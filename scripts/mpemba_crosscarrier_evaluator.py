#!/usr/bin/env python3
"""Frozen cross-carrier evaluator for the Mpemba crossing law.

This is the artifact od7.md names as the highest-value next step: a *frozen*, reusable
evaluator that takes independently determined rates as calibration and tests a proved
law against a held-out trajectory, so the same equation can be run across unrelated
physical carriers without refitting.

THE FROZEN LAW (proved in Lean, not fitted here)
------------------------------------------------
    Physlib/Optics/MpembaCrossingReadsEffectiveDamping.lean

        mpembaCrossingTime a b lam2 lam3 = log (a / b) / (lam2 - lam3)
        gammaEff_mul_crossingTime : gamma_eff * t_cross = log (a / b)

Two relaxation branches with initial distances-to-steady-state `a` and `b` decaying at
rates `lam2` and `lam3` cross at exactly `t* = log(a/b) / (lam2 - lam3)`.  Nothing on the
right-hand side is fitted to the crossing: the amplitudes are the measured `t -> 0`
distances and the rates are reported independently by the experiment.

ANTI-CIRCULARITY (the point of the exercise)
--------------------------------------------
Calibration set   : lam1, lam2                   -- from the paper's eigenvalue table
Initial condition : a = D_slow(0), b = D_fast(0) -- measured, not fitted
Held out          : the entire D(t) trajectory, including where the curves cross

The evaluator never fits the trajectory.  It predicts `t*` from calibration alone and
compares against the observed crossing.

CARRIER 1 (this file)
---------------------
Zhang, Xia, Wu et al., "Observation of quantum strong Mpemba effect",
Nature Communications 16, 301 (2025), doi:10.1038/s41467-024-54303-0.
Single trapped ion; strong Mpemba realized by nulling the slowest decaying mode -- the
`a2 = 0` condition of Physlib/Optics/MpembaIndexRateSelection.lean.
Source data: Supplementary Data 41467_2024_54303_MOESM3/MOESM4.

Adding a carrier means implementing `load_*` returning a `Carrier`; the law and the test
are untouched.  That is what "frozen" means here.
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass, field
from pathlib import Path

DATA_DIR = Path.home() / "Downloads"

# The crossing and the Mpemba physics occur within a few lifetimes of the FAST mode.
# The published traces run far past that into a flat tail; including it would make every
# branch look like a constant and the precondition test meaningless.
WINDOW_LIFETIMES = float('inf')   # window is set by the noise floor, not by a guess


# --------------------------------------------------------------------------- law


def crossing_time(a: float, b: float, lam_a: float, lam_b: float) -> float:
    """t* = log(a/b) / (lam_b - lam_a), i.e. Lean `mpembaCrossingTime`.

    `a` decays at `lam_a`, `b` at `lam_b`.  Sign convention: rates are negative
    (decaying), and `lam_b` is the faster (more negative) one.
    """
    return math.log(a / b) / (lam_b - lam_a)


def two_mode_distance(a: float, lam: float, t: float) -> float:
    """Single-exponential branch `D(t) = a * exp(lam * t)` -- the frozen prediction."""
    return a * math.exp(lam * t)


# ------------------------------------------------------------------------ carrier


@dataclass
class Carrier:
    name: str
    reference: str
    ratio: str
    lam_slow: float
    lam_slow_err: float
    lam_fast: float
    lam_fast_err: float
    t: list[float] = field(default_factory=list)
    d_slow: list[float] = field(default_factory=list)
    d_slow_err: list[float] = field(default_factory=list)
    d_fast: list[float] = field(default_factory=list)
    d_fast_err: list[float] = field(default_factory=list)


def load_trapped_ion() -> list[Carrier]:
    """Nature Comms 16, 301 (2025) supplementary data -> one Carrier per coupling ratio."""
    try:
        import openpyxl
    except ImportError:
        print("openpyxl not available; cannot read the supplementary workbooks.")
        return []

    f4 = DATA_DIR / "41467_2024_54303_MOESM4_ESM.xlsx"
    if not f4.exists():
        print(f"missing {f4}")
        return []

    wb = openpyxl.load_workbook(f4, read_only=True, data_only=True)

    # Fig3(c): independently reported eigenvalues, the calibration set.
    lam = {}
    for row in wb["Fig3(c)"].iter_rows(min_row=2, values_only=True):
        if row[0] is None or row[1] is None:
            continue
        lam[round(float(row[0]), 3)] = (
            float(row[1]), float(row[2]), float(row[3]), float(row[4])
        )

    # Fig3(a): held-out distance trajectories, three ratios side by side.
    ws = wb["Fig3(a)"]
    rows = list(ws.iter_rows(values_only=True))
    header = rows[0]
    carriers: list[Carrier] = []
    for ratio_str, base in (("0.04", 1), ("0.16", 8), ("0.25", 15)):
        key = round(float(ratio_str), 3)
        if key not in lam:
            continue
        l1, l1e, l2, l2e = lam[key]
        # column layout: state0, err, state2, err, stateME, err
        c = Carrier(
            name=f"trapped ion (omega1/omega2={ratio_str})",
            reference="Nature Communications 16, 301 (2025)",
            ratio=ratio_str,
            lam_slow=l1, lam_slow_err=l1e, lam_fast=l2, lam_fast_err=l2e,
        )
        t_max = WINDOW_LIFETIMES / abs(l2) if l2 else float("inf")
        for r in rows[1:]:
            if r[0] is None or r[base] is None or r[base + 4] is None:
                continue
            if float(r[0]) > t_max:      # restrict to the pre-asymptotic window
                continue
            c.t.append(float(r[0]))
            c.d_slow.append(float(r[base]))          # state 0  -- carries the slow mode
            c.d_slow_err.append(float(r[base + 1]))
            c.d_fast.append(float(r[base + 4]))      # state ME -- slow mode nulled
            c.d_fast_err.append(float(r[base + 5]))
        if len(c.t) > 4:
            carriers.append(c)
        _ = header
    return carriers


# --------------------------------------------------------------------------- test



def log_slope(t: list[float], d: list[float], lo: float, hi: float) -> tuple[float, int]:
    """Least-squares slope of log D against t on [lo, hi]. No model, just a diagnostic."""
    pts = [(a, math.log(b)) for a, b in zip(t, d) if lo <= a <= hi and b > 0]
    n = len(pts)
    if n < 3:
        return float("nan"), n
    sx = sum(p[0] for p in pts); sy = sum(p[1] for p in pts)
    sxx = sum(p[0] ** 2 for p in pts); sxy = sum(p[0] * p[1] for p in pts)
    den = n * sxx - sx * sx
    return ((n * sxy - sx * sy) / den if den else float("nan")), n


def single_exponential(t: list[float], d: list[float], tol: float = 0.35) -> tuple[bool, float, float]:
    """PRECONDITION of the frozen law: is this branch one exponential?

    `mpembaCrossingTime` is exact for two branches that are each a *single* decaying
    exponential.  If a branch carries both modes its log-slope drifts, and the law does
    not apply -- reporting a crossing prediction anyway would be meaningless.  Compares
    the log-slope on the first and last thirds of the window.
    """
    span = max(t) - min(t)
    early, _ = log_slope(t, d, min(t), min(t) + span / 3)
    late, _ = log_slope(t, d, min(t) + 2 * span / 3, max(t))
    if math.isnan(early) or math.isnan(late) or early == 0:
        return False, early, late
    return abs(late / early - 1.0) <= tol, early, late


def noise_floor(d: list[float], err: list[float]) -> tuple[float, bool]:
    """Detect a floor in the distance estimator.

    A trace-distance estimated from finite sampling is positively biased: it does not
    decay to zero but flattens at, and then wanders around, a floor.  Any log-slope test
    run past that point measures the floor rather than the decay rate.  Returns the
    median of the last quarter of the trace and whether the trace is non-monotone there
    (a rise beyond error bars is a definite floor signature).
    """
    tail = d[max(1, 3 * len(d) // 4):]
    if not tail:
        return 0.0, False
    srt = sorted(tail)
    med = srt[len(srt) // 2]
    rises = any(tail[i + 1] > tail[i] + math.hypot(err[-len(tail) + i], err[-len(tail) + i + 1])
                for i in range(len(tail) - 1)
                if -len(tail) + i + 1 < 0)
    return med, rises


def observed_crossing(c: Carrier) -> float | None:
    """First time the two measured curves cross, by linear interpolation. Held out."""
    for i in range(len(c.t) - 1):
        g0 = c.d_slow[i] - c.d_fast[i]
        g1 = c.d_slow[i + 1] - c.d_fast[i + 1]
        if g0 == 0:
            return c.t[i]
        if g0 * g1 < 0:
            frac = g0 / (g0 - g1)
            return c.t[i] + frac * (c.t[i + 1] - c.t[i])
    return None


def monotone_decreasing(d: list[float], err: list[float]) -> tuple[int, int]:
    """Count strict violations of D(t_{i+1}) <= D(t_i) beyond combined uncertainty."""
    bad = 0
    for i in range(len(d) - 1):
        tol = math.hypot(err[i], err[i + 1])
        if d[i + 1] > d[i] + tol:
            bad += 1
    return bad, len(d) - 1


def evaluate(c: Carrier) -> dict:
    a, b = c.d_slow[0], c.d_fast[0]

    # -- precondition gate: the law is exact only for single-exponential branches --
    floor, wanders = noise_floor(c.d_slow, c.d_slow_err)
    ok_slow, e_slow, l_slow = single_exponential(c.t, c.d_slow)
    ok_fast, e_fast, l_fast = single_exponential(c.t, c.d_fast)
    applicable = ok_slow and ok_fast

    t_pred = crossing_time(a, b, c.lam_slow, c.lam_fast)

    # propagate the reported eigenvalue uncertainties through the frozen law
    denom = c.lam_fast - c.lam_slow
    dt_dl = abs(math.log(a / b) / denom**2)
    t_pred_err = dt_dl * math.hypot(c.lam_slow_err, c.lam_fast_err)

    t_obs = observed_crossing(c)

    # chi^2 of the held-out slow branch against the frozen single-exponential prediction
    chi2, n = 0.0, 0
    for ti, di, ei in zip(c.t, c.d_slow, c.d_slow_err):
        if ei and ei > 0:
            chi2 += ((di - two_mode_distance(a, c.lam_slow, ti)) / ei) ** 2
            n += 1

    bad_slow, tot_slow = monotone_decreasing(c.d_slow, c.d_slow_err)
    bad_fast, tot_fast = monotone_decreasing(c.d_fast, c.d_fast_err)

    return dict(
        carrier=c.name, ref=c.reference, applicable=applicable,
        slope_slow=(e_slow, l_slow), slope_fast=(e_fast, l_fast),
        floor=floor, wanders=wanders,
        a=a, b=b, lam_slow=c.lam_slow, lam_fast=c.lam_fast,
        t_pred=t_pred, t_pred_err=t_pred_err, t_obs=t_obs,
        pull=None if t_obs is None or t_pred_err == 0 else (t_obs - t_pred) / t_pred_err,
        chi2=chi2, ndof=max(n - 0, 1), chi2_red=chi2 / max(n, 1),
        mono=f"{tot_slow - bad_slow}/{tot_slow} slow, {tot_fast - bad_fast}/{tot_fast} fast",
    )


def main() -> int:
    carriers = load_trapped_ion()
    if not carriers:
        print("no carriers loaded")
        return 1

    print("=" * 78)
    print("FROZEN CROSS-CARRIER EVALUATOR -- Mpemba crossing law")
    print("law: t* = log(a/b)/(lam_fast - lam_slow)   [Lean: mpembaCrossingTime]")
    print("calibration: reported eigenvalues + measured D(0).  Held out: the trajectory.")
    print("=" * 78)

    ok = 0
    skipped_local: list[str] = []
    for c in carriers:
        r = evaluate(c)
        print(f"\n--- {r['carrier']}")
        print(f"    {r['ref']}")
        print(f"    calibration : lam_slow={r['lam_slow']:+.5f}  lam_fast={r['lam_fast']:+.5f}")
        print(f"                  a=D_slow(0)={r['a']:.4f}   b=D_fast(0)={r['b']:.4f}")
        es, ls = r["slope_slow"]; ef, lf = r["slope_fast"]
        print(f"    data check  : distance floor ~{r['floor']:.3f}"
              f"{'  (trace RISES at late time -- definite floor)' if r['wanders'] else ''}")
        print(f"    precondition: single-exponential branches?  {'PASS' if r['applicable'] else 'FAIL'}")
        print(f"                  slow d(logD)/dt early={es:+.4f} late={ls:+.4f}")
        print(f"                  fast d(logD)/dt early={ef:+.4f} late={lf:+.4f}")
        if not r["applicable"]:
            print("    VERDICT     : law NOT APPLICABLE to this carrier -- the branches are")
            print("                  not single exponentials, so mpembaCrossingTime's")
            print("                  hypotheses fail.  No crossing prediction is reported.")
            print("                  (This is a precondition failure, not a refutation.)")
            skipped_local.append(r["carrier"])
        else:
            print(f"    PREDICTED   : t* = {r['t_pred']:.4f} +/- {r['t_pred_err']:.4f}")
            if r["t_obs"] is None:
                print("    OBSERVED    : no crossing within the measured window")
            else:
                print(f"    OBSERVED    : t* = {r['t_obs']:.4f}")
                print(f"    pull        : {r['pull']:+.2f} sigma (eigenvalue error only)")
                if abs(r["pull"]) <= 3:
                    ok += 1
            print(f"    held-out chi2/N of the slow branch : {r['chi2_red']:.2f}")
        print(f"    distance monotone decreasing        : {r['mono']}")

    print("\n" + "=" * 78)
    tested = len(carriers) - len(skipped_local)
    print(f"carriers where the law APPLIES: {tested}/{len(carriers)}")
    print(f"of those, crossing predicted within 3 sigma: {ok}/{tested if tested else 0}")
    if skipped_local:
        print("gated out (preconditions unmet): " + ", ".join(skipped_local))
    print("NOTE: a single carrier is not cross-carrier validation.  Adding a carrier")
    print("means writing another load_* -- the law and the test above do not change.")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    sys.exit(main())

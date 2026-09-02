#!/usr/bin/env python3
"""Deferred-moire vibrometer: the Saveljev et al. 2023 experiment, virtually.

Saveljev-Son-Lee-Heo, "Non-contact measurement of vibrations using deferred
moire patterns", Adv. Mech. Eng. 15(4) 2023, 10.1177/16878132221143885:
a grid attached to a vibrating rod is videoed; each frame is later multiplied
by a computer-generated reference grid ("deferred"); the moire fringe phase
magnifies the rod displacement mu = 1/|1 - T2/T1| times (Eqs. 3-5), giving a
self-calibrated sub-pixel vibrometer.  Their finding: a broken rod moves the
frequency by only 7% (4.68 -> 4.36 Hz) but DOUBLES the decay lifetime
(2.8-4.4 s -> 7.3-9.2 s) -- the decay rate is the pre-failure indicator.

This script replays the experiment end-to-end through the Lean-mirror routes
(moirePeriod, moireMagnification, route_deferred_displacement) and quantifies
the formalized thesis (envelope_is_frequency_blind + envelope_separates_decay):
the amplitude envelope reads Re(lambda) = -Gamma and only that.

  [1] EXTERNAL WELD: mirror moirePeriod (Eq. 3) vs the independent
      moire-optics-lab estimate_moire_period at zero twist.
  [2] VIRTUAL EXPERIMENT: damped rod u(t) = A e^{-Gamma t} cos(2 pi f0 t) with
      the paper's measured (f0, lifetime) for unbroken/broken; grid 8.9 mm at
      13 px/mm (their setup); reference grid chosen for mu ~ 9; per-frame
      lock-in demodulation at the moire wavenumber recovers u(t); FFT peak ->
      f0, log-regression on envelope maxima -> Gamma.  5% pixel noise, 30 FPS.
  [3] SUB-PIXEL: the recovered tail displacement is below one pixel.
  [4] VERDICT: frequency contrast vs lifetime contrast, broken vs unbroken.
  [5] STRUCTURAL GRAVIMETER: Eq. 6 squared times the self-weight sag cancels
      every beam parameter -- f0^2 delta = (pi^2/32) g
      (cantilever_selfweight_gravimeter).  Three beams of different material
      and size, each measured for frequency (dynamic) and sag (static fringe
      shift), all recover the same hidden g via route_structural_g.

Run:  python3 scripts/deferred_moire_vibrometer.py
"""
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import physlib_mpemba as plm

# paper's rod measurements (Section "Comparative tests with/without cracks")
CASES = {
    "unbroken": {"f0": 4.68, "tau": 3.6},   # Hz, s (lifetime = 1/Gamma, 2.8-4.4 s)
    "broken":   {"f0": 4.36, "tau": 8.2},   # 7.3-9.2 s
}
PX_PER_MM = 13.0                            # "we had 13 pixels/mm"
T2 = 8.9e-3                                 # attached grid period, m ("grid 8.9 mm")
T1 = 10.0e-3                                # deferred computer-generated reference, m
A0 = 3.0e-3                                 # initial amplitude, m (paper: 0.5-5 mm)
FPS, DURATION = 30.0, 30.0
NOISE = 0.05
rng = np.random.default_rng(23)


def measure_case(f0, tau, noisy=True, fps=FPS, duration=DURATION, a0=A0):
    """Video frames of grid+rod -> deferred moire -> u(t) -> (f0, Gamma)."""
    k1, k2 = 2 * np.pi / T1, 2 * np.pi / T2
    kM = k2 - k1                                        # moire wavenumber (>0 here)
    mu = plm.moireMagnification(T1, T2)
    span = 0.30                                          # m of grid in view (A5-ish)
    x = np.arange(0, span, 1e-3 / PX_PER_MM)
    t = np.arange(0, duration, 1 / fps)
    u_true = a0 * np.exp(-t / tau) * np.cos(2 * np.pi * f0 * t)

    u_meas = np.empty_like(t)
    # Hann-windowed lock-in: only ~4 moire periods fit the view, so the DC and
    # carrier terms leak into the moire bin unless windowed out
    demod = np.hanning(len(x)) * np.exp(-1j * kM * x)
    for i, ui in enumerate(u_true):
        frame = (1 + np.cos(k2 * (x - ui))) * (1 + np.cos(k1 * x))
        if noisy:
            frame = frame + NOISE * rng.standard_normal(len(x))
        # lock-in at the moire wavenumber: the cross term cos(kM x - k2 u)
        # demodulates to e^{-i k2 u} -- the phase is the magnified displacement
        # kM * x_M with x_M = mu*u (route_deferred_displacement)
        z = np.sum((frame - frame.mean()) * demod)
        u_meas[i] = -np.angle(z) / k2
    # fringe-displacement view of the same data (Eq. 5): x_M = mu * u
    xM_peak = plm.route_deferred_displacement(k1, k2, np.max(np.abs(u_meas)))

    # frequency: FFT peak with parabolic interpolation
    W = np.abs(np.fft.rfft(u_meas * np.hanning(len(t)))) ** 2
    fax = np.fft.rfftfreq(len(t), 1 / fps)
    i0 = int(np.argmax(W[1:])) + 1
    y0, y1, y2 = np.log(W[i0 - 1]), np.log(W[i0]), np.log(W[i0 + 1])
    f_meas = fax[i0] + 0.5 * (y0 - y2) / (y0 - 2 * y1 + y2) * (fax[1] - fax[0])

    # decay: exponential regression on envelope maxima (the paper's method)
    imax = [i for i in range(1, len(t) - 1)
            if u_meas[i] > u_meas[i - 1] and u_meas[i] > u_meas[i + 1] and u_meas[i] > 0]
    tm, am = t[imax], u_meas[imax]
    keep = am > 0.02 * np.max(am)
    slope = np.polyfit(tm[keep], np.log(am[keep]), 1)[0]
    return f_meas, -1 / slope, mu, abs(xM_peak), u_meas, u_true, t


def static_sag(delta, noisy=True, scale=1.0):
    """Sag from the fringe-phase difference of an unloaded and a loaded frame.
    Wrapped to one grid period; scale > 1 uses a coarser grid pair (periods
    scale*T1, scale*T2), extending the wrap-free range by the same factor."""
    T1s, T2s = scale * T1, scale * T2
    k1, k2 = 2 * np.pi / T1s, 2 * np.pi / T2s
    kM = k2 - k1
    x = np.arange(0, 0.30 * scale, 1e-3 / PX_PER_MM * scale)
    demod = np.hanning(len(x)) * np.exp(-1j * kM * x)

    def phase(u):
        frame = (1 + np.cos(k2 * (x - u))) * (1 + np.cos(k1 * x))
        if noisy:
            frame = frame + NOISE * rng.standard_normal(len(x))
        z = np.sum((frame - frame.mean()) * demod)
        return -np.angle(z)

    dphi = np.angle(np.exp(1j * (phase(delta) - phase(0.0))))
    return dphi / k2


def main():
    plm.selfcheck()
    print("[GATE] physlib_mpemba mirror passes all Lean theorem identities\n")

    # [1] external weld: Eq. 3 vs moire-optics-lab at zero twist
    try:
        import moire_physics as mp
        worst = max(abs(mp.estimate_moire_period(a, b, 0.0) / plm.moirePeriod(a, b) - 1)
                    for a, b in [(8.9, 10.0), (60.0, 70.0), (40.0, 41.0)])
        print(f"[1] moire-optics-lab estimate_moire_period(0 deg) vs Lean moirePeriod "
              f"(Eq. 3, 3 cases): max rel dev = {worst:.2e}")
    except ImportError:
        print("[1] moire-optics-lab not installed -- external weld skipped")

    mu = plm.moireMagnification(T1, T2)
    TM = plm.moirePeriod(T1, T2)
    print(f"\n[2] grids: attached {T2 * 1e3:.1f} mm, reference {T1 * 1e3:.1f} mm -> "
          f"moire period {TM * 1e3:.1f} mm, magnification {mu:.2f}x "
          f"(pixel = {1 / PX_PER_MM:.3f} mm)")

    results = {}
    for name, c in CASES.items():
        f_m, tau_m, _, xM, u_m, u_t, t = measure_case(c["f0"], c["tau"])
        results[name] = (f_m, tau_m)
        rms = np.sqrt(np.mean((u_m - u_t) ** 2))
        print(f"    {name:9s}: f = {f_m:.3f} Hz (true {c['f0']}), "
              f"lifetime = {tau_m:.2f} s (true {c['tau']}); "
              f"u(t) RMS error {rms * 1e6:.1f} um; peak fringe shift {xM * 1e3:.1f} mm")

    # [3] sub-pixel: tail amplitude under one pixel, still tracked
    f_m, tau_m, _, _, u_m, u_t, t = measure_case(**{"f0": 4.68, "tau": 3.6})
    late = t > 20.0
    tail_true = np.max(np.abs(u_t[late]))
    tail_err = np.sqrt(np.mean((u_m[late] - u_t[late]) ** 2))
    px = 1e-3 / PX_PER_MM
    print(f"\n[3] sub-pixel: tail amplitude {tail_true * 1e3:.4f} mm < pixel "
          f"{px * 1e3:.3f} mm, tracked to {tail_err * 1e6:.2f} um RMS "
          f"(magnification {mu:.1f}x is why -- deferred_subpixel_magnification)")

    # [4] the formalized thesis
    fu, tu = results["unbroken"]
    fb, tb = results["broken"]
    print(f"\n[4] contrasts (broken vs unbroken):")
    print(f"    frequency: {fu:.2f} -> {fb:.2f} Hz  ({(1 - fb / fu) * 100:.1f}% fall)")
    print(f"    lifetime : {tu:.2f} -> {tb:.2f} s   ({tb / tu:.2f}x rise)")
    # [5] structural gravimeter: three beams, one g
    G_TRUE = 9.81
    beams = [                                  # E (Pa), b x h (m), L (m), rho (kg/m3)
        ("plastic 10x10mm", 3.0e9, 0.010, 0.010, 0.50, 1200.0),
        ("aluminium 5x5mm", 69.0e9, 0.005, 0.005, 0.60, 2700.0),
        ("steel 3x3mm", 200.0e9, 0.003, 0.003, 0.45, 7850.0),
    ]
    print(f"\n[5] structural gravimeter (hidden g = {G_TRUE}): f0^2 delta = (pi^2/32) g,")
    print("    every beam parameter cancels (cantilever_selfweight_gravimeter):")
    for name, E, b, h, L, rho in beams:
        I = b * h ** 3 / 12
        lmass = rho * b * h
        f0 = plm.beamFundamentalFrequency(E, I, lmass, L)
        delta = lmass * G_TRUE * L ** 4 / (8 * E * I)         # hidden-g truth
        f_m, _, _, _, _, _, _ = measure_case(f0, 2.0, fps=120.0, duration=10.0, a0=1e-3)
        d_m = static_sag(delta)
        g_rec = plm.route_structural_g(f_m, d_m)
        print(f"    {name:16s}: f = {f_m:6.2f} Hz, sag = {d_m * 1e3:5.2f} mm "
              f"-> g = {g_rec:.3f}")
    gs = np.array([plm.route_structural_g(
        measure_case(28.68, 2.0, fps=120.0, duration=10.0, a0=1e-3)[0],
        static_sag(3.68e-3)) for _ in range(40)])
    print(f"    Monte Carlo (plastic beam, 40 runs, {NOISE * 100:.0f}% pixel noise): "
          f"g = {gs.mean():.3f} +/- {gs.std():.3f}")

    # [6] two-frequency absolute order: sag beyond the single-grid wrap limit
    delta_big = 31.0e-3                                  # m, >> T2/2 = 4.45 mm
    Rbig = G_TRUE / (8 * delta_big)
    f0_big = np.pi / 2 * np.sqrt(Rbig)
    fine = static_sag(delta_big)                         # wrapped: integer lost
    coarse = static_sag(delta_big, scale=10.0)           # M = 10: rough but absolute
    d_abs = plm.route_two_frequency_unwrap(fine, coarse, T2)
    f_m6, _, _, _, _, _, _ = measure_case(f0_big, 2.5, fps=60.0, duration=15.0, a0=1e-3)
    g6 = plm.route_structural_g(f_m6, d_abs)
    print(f"\n[6] two-frequency absolute order (Ibrahim-Takasaki, M = 10):")
    print(f"    true sag {delta_big * 1e3:.1f} mm > wrap limit {T2 / 2 * 1e3:.2f} mm; "
          f"fine grid reads {fine * 1e3:.2f} mm (order lost)")
    print(f"    coarse grid reads {coarse * 1e3:.2f} mm (absolute, rough) -> combined "
          f"{d_abs * 1e3:.3f} mm")
    print(f"    floppy beam f0 = {f_m6:.2f} Hz -> g = {g6:.3f}  "
          f"(range x10, fine precision kept)")

    print("\nVERDICT: the envelope observable ||e^{lambda t}|| = e^{-Gamma t} is frequency-blind")
    print("(envelope_is_frequency_blind) yet strictly decay-separating (envelope_separates_decay):")
    print("the deferred moire pattern reads the entropic sector Re(lambda) directly, and the decay")
    print("rate -- not the 7% frequency shift -- is the pre-failure indicator, as measured.")


if __name__ == "__main__":
    main()

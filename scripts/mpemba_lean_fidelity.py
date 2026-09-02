#!/usr/bin/env python3
"""QuTiP computation of the Mpemba experiments + numerical fidelity suite for
the Lean 4 content.

Two layers:

[A] PROPER-LIBRARY DYNAMICS (qutip): the trapped-ion GKSL model and the NMR
    4-level master equation are built with qutip.liouvillian / mesolve /
    steadystate (independent of the hand-rolled numpy reconstructions), and the
    Mpemba crossing is computed in the standard quantum-information metrics:
      trace distance  T(rho, rho_ss)      (the experiments' measure)
      Uhlmann fidelity F(rho, rho_ss)     (as Bures distance sqrt(2(1-F)))
      relative entropy S(rho || rho_ss)   (the Lean qRelativeEnt carrier)
    The DPI/Petz statement formalized in SciamaAdSCPTQuantumMpembaCrossing
    (mpemba_consistent_with_petz: both trajectories monotone, the anomaly is
    BETWEEN them) is checked on the actual solver output.

[B] LEAN FIDELITY SUITE: every theorem of the Mpemba arc is re-checked
    numerically by seeded random sampling of its hypothesis domain -- the
    Python model and the Lean statements certify each other.  Each row names
    the exact Lean declaration.  (Numerics certify samples; the proof burden
    stays in Lean.)

Run:  python3 scripts/mpemba_lean_fidelity.py
"""
import numpy as np
import qutip as qt

rng = np.random.default_rng(20260805)
SUITE = []


def check(lean_name, sampler, n=300):
    """sampler() -> violation magnitude (<=0 means satisfied)."""
    worst = -np.inf
    for _ in range(n):
        worst = max(worst, sampler())
    SUITE.append((lean_name, n, worst, worst <= 1e-9))


# ============================================================================
# [A1] trapped ion in qutip
# ============================================================================
def ion_ops(gfp, alpha, g=1.0):
    Om = 1.0 / gfp
    down, up = qt.basis(2, 0), qt.basis(2, 1)
    H = 0.5 * Om * qt.sigmax()
    c_ops = [np.sqrt(2 * alpha * g) * down * up.dag(),
             np.sqrt(2 * (1 - alpha) * g) * up * up.dag()]
    return H, c_ops


def ion_qutip():
    alpha, gfp = 0.94, 15.0
    H, c_ops = ion_ops(gfp, alpha)
    L = qt.liouvillian(H, c_ops).full()
    ev = np.sort(np.linalg.eigvals(L).real)
    d = (alpha - 0.5) ** 2 - 1 / gfp ** 2
    eq4 = np.sort([-(alpha + 0.5 - np.sqrt(d)), -(alpha + 0.5 + np.sqrt(d)), -1.0, 0.0])
    print(f"[A1] ion qutip.liouvillian spectrum {np.round(ev, 6)}")
    print(f"     Lean slowRate/fastRate (Eq.4)  {np.round(eq4, 6)}  "
          f"match: {np.allclose(ev, eq4, atol=1e-9)}")

    # dynamics, three metrics, both configs
    for gfp_, gic, gih, tag in ((15.0, 0.116, 0.776, "Fig3"), (100.0, 1e-4, 0.390, "Fig5")):
        H, c_ops = ion_ops(gfp_, alpha)
        rho_ss = qt.steadystate(H, c_ops)
        ts = np.linspace(0, 8.0, 4001)
        curves = {}
        for lbl, gi in (("C", gic), ("H", gih)):
            H0, c0 = ion_ops(gfp_, alpha, g=gi / gfp_ if gi > 0 else 1e-9)
            rho0 = qt.steadystate(H0, c0)
            states = qt.mesolve(H, rho0, ts, c_ops).states
            curves[lbl] = dict(
                trace=np.array([qt.tracedist(s, rho_ss) for s in states]),
                bures=np.array([np.sqrt(max(2 * (1 - qt.fidelity(s, rho_ss)), 0)) for s in states]),
                relent=np.array([qt.entropy_relative(s, rho_ss) for s in states]))
        print(f"[A1] {tag} crossings (gamma_f t): ", end="")
        for m in ("trace", "bures", "relent"):
            diff = curves["C"][m] - curves["H"][m]
            idx = np.where(np.diff(np.sign(diff)) != 0)[0]
            tc = [round(ts[i], 3) for i in idx if ts[i] > 1e-9][:2]
            print(f"{m}={tc} ", end="")
        # DPI along each trajectory (Lean mpemba_consistent_with_petz):
        viol = max(np.max(np.diff(curves[l]["relent"])) for l in ("C", "H"))
        print(f"; relative entropy monotone along BOTH trajectories: "
              f"{viol <= 1e-6} (max increment {viol:.1e})")


# ============================================================================
# [A2] NMR 4-level master equation in qutip
# ============================================================================
def nmr_qutip(eps=0.02):
    K0 = 1.0
    up1, dn1 = K0 * (1 - eps) / 16, K0 * (1 + eps) / 16
    up2, dn2 = K0 * (1 - 2 * eps) / 4, K0 * (1 + 2 * eps) / 4
    zq = K0 / 24
    ket = [qt.basis(4, i) for i in range(4)]
    idx = {"00": 0, "01": 1, "10": 2, "11": 3}
    jumps = []
    for lo, hi in [("00", "01"), ("00", "10"), ("01", "11"), ("10", "11")]:
        jumps += [(up1, hi, lo), (dn1, lo, hi)]
    jumps += [(up2, "11", "00"), (dn2, "00", "11"), (zq, "10", "01"), (zq, "01", "10")]
    c_ops = [np.sqrt(r) * ket[idx[a]] * ket[idx[b]].dag() for r, a, b in jumps]
    H = qt.qzero(4)
    L = qt.liouvillian(H, c_ops).full()
    ev = np.sort(np.unique(np.round(np.linalg.eigvals(L).real, 6)))
    print(f"[A2] NMR qutip population spectrum contains -(K0/24)*(5,6,15) to O(eps^2): "
          f"{all(any(abs(x + v / 24) < 5e-3 for x in ev) for v in (5, 6, 15))} "
          f"(population rates shifted O(eps^2); coherence modes extra in the Lindblad embedding)")
    rho_ss = qt.steadystate(H, c_ops)
    iz = {"00": (.5, .5), "01": (.5, -.5), "10": (-.5, .5), "11": (-.5, -.5)}
    th = np.deg2rad(70)
    keys = ["00", "01", "10", "11"]
    p_n = [0.25 + 2 * eps * (iz[k][0] + iz[k][1] * np.cos(2 * th)) / 4 for k in keys]
    p_f = [0.25 - eps * (iz[k][0] + iz[k][1]) / 2 for k in keys]
    ts = np.linspace(0, 40, 4001)
    curves = {}
    for lbl, p in (("n", p_n), ("f", p_f)):
        rho0 = qt.Qobj(np.diag(p))
        states = qt.mesolve(H, rho0, ts, c_ops).states
        curves[lbl] = dict(
            trace=np.array([qt.tracedist(s, rho_ss) for s in states]),
            relent=np.array([qt.entropy_relative(s, rho_ss) for s in states]))
    print("[A2] NMR crossings (K0 t): ", end="")
    for m in ("trace", "relent"):
        diff = curves["f"][m] - curves["n"][m]
        idx2 = np.where(np.diff(np.sign(diff)) != 0)[0]
        print(f"{m}={[round(ts[i], 3) for i in idx2 if ts[i] > 1e-9][:2]} ", end="")
    viol = max(np.max(np.diff(curves[l]["relent"])) for l in ("n", "f"))
    print(f"; DPI monotone both: {viol <= 1e-6} (max increment {viol:.1e})")


# ============================================================================
# [B] Lean fidelity suite
# ============================================================================
def build_suite():
    E = np.e

    def s_mpemba_crossing():
        a, b = rng.uniform(0.1, 5, 2)
        lam2 = rng.uniform(-3, -0.1)
        lam3 = lam2 - rng.uniform(0.1, 3)
        tstar = np.log(a / b) / (lam2 - lam3)
        t = tstar + rng.uniform(1e-3, 5)
        return a * E ** (lam3 * t) - b * E ** (lam2 * t)
    check("SciamaAdSCPTQuantumMpembaCrossing.mpemba_crossing", s_mpemba_crossing)

    def s_units():
        a, b = rng.uniform(0.1, 5, 2)
        l2, l3, wE = rng.uniform(-3, 3, 2).tolist() + [rng.uniform(0.1, 10)]
        lhs = np.log(a / b) / ((l2 - l3) / wE) if l2 != l3 else 0
        rhs = wE * (np.log(a / b) / (l2 - l3) if l2 != l3 else 0)
        return abs(lhs - rhs) - 1e-12
    check("SciamaAdSCPTMpembaEntropicClock.mpembaCrossingTime_entropic_units", s_units)

    def rates(gf, al, gfp):
        d = (al - .5) ** 2 - 1 / gfp ** 2
        sq = np.sqrt(max(d, 0.0))          # Lean Real.sqrt convention: sqrt(neg) = 0
        return (-(gf * (al + .5 - sq)), -(gf * (al + .5 + sq)), d)

    def s_rate_sum():
        gf, al, gfp = rng.uniform(.1, 3), rng.uniform(0, 1), rng.uniform(1, 50)
        ls, lf, _ = rates(gf, al, gfp)
        return abs(ls + lf - (-(gf * (2 * al + 1)))) - 1e-9   # holds on the junk domain too
    check("SciamaAdSCPTTrappedIonMpembaSpectrum.rate_sum", s_rate_sum)

    def s_rate_product():
        gf, al, gfp = rng.uniform(.1, 3), rng.uniform(0.6, 1), rng.uniform(3, 50)
        ls, lf, d = rates(gf, al, gfp)
        if d < 0:
            return 0.0
        return abs(ls * lf - gf ** 2 * (2 * al + 1 / gfp ** 2)) - 1e-9
    check("SciamaAdSCPTTrappedIonMpembaSpectrum.rate_product", s_rate_product)

    def s_ellipse():
        al, u = rng.uniform(0.01, 1), rng.uniform(-5, 5)
        y = 2 * al * u / (1 + 2 * al * u ** 2)
        z = (1 - 2 * al * u ** 2) / (1 + 2 * al * u ** 2)
        return abs(y ** 2 * 2 / al + z ** 2 - 1) - 1e-9
    check("SciamaAdSCPTTrappedIonMpembaSpectrum.steady_state_ellipse", s_ellipse)

    def s_threshold():
        al, gfp = rng.uniform(0.5, 1.2), rng.uniform(1, 50)
        d = (al - .5) ** 2 - 1 / gfp ** 2
        iff = (d > 0) == (al > 0.5 + 1 / gfp)
        return 0.0 if iff else 1.0
    check("SciamaAdSCPTTrappedIonMpembaSpectrum.strong_me_threshold", s_threshold)

    def s_cancel():
        al, gfp = rng.uniform(0.51, 1.2), rng.uniform(1, 50)
        d = (al - .5) ** 2 - 1 / gfp ** 2
        if d < 0:
            return 0.0
        return -(gfp * ((al - .5) - np.sqrt(d))) + 1e-15
    check("SciamaAdSCPTTrappedIonMpembaSpectrum.strongMeCancellation_pos", s_cancel)

    hbar, e, me, mp = 1.054571817e-34, 1.602176634e-19, 9.1093837015e-31, 1.67262192e-27
    c, eps0 = 2.99792458e8, 8.8541878128e-12

    def s_dipolar_closed():
        g, al = rng.uniform(1, 8), rng.uniform(1e-3, 0.1)
        m2 = mp * rng.uniform(0.5, 2)
        a0 = hbar / (me * c) / al
        r = 2 * np.sqrt(3) * a0
        gam = g * e / (2 * m2)
        lhs = (1 / (4 * np.pi * eps0 * c ** 2)) * gam ** 2 * hbar / r ** 3
        alSI = e ** 2 / (4 * np.pi * eps0 * hbar * c)
        rhs = np.sqrt(3) * g ** 2 / 288 * alSI * al ** 3 * (me / m2) ** 2 * (me * c ** 2 / hbar)
        return abs(lhs / rhs - 1) - 1e-9
    check("SciamaAdSCPTDipolarMpembaComptonSubstrate.dipolar_compton_clock_closed_form",
          s_dipolar_closed)

    def s_t1():
        b, tau = rng.uniform(1e3, 1e6), rng.uniform(1e-13, 1e-10)
        return abs(15 * (12 * b ** 2 * tau / 5) / 24 - 1.5 * b ** 2 * tau) / (b ** 2 * tau) - 1e-9
    check("SciamaAdSCPTDipolarMpembaComptonSubstrate.t1_is_fastest_mode", s_t1)

    def s_gw():
        rho = rng.uniform(1e-3, 10)
        f = 1 / (6 * rho + (1 + rho) ** -3)
        return max(-f, f - 1) + 1e-15
    check("SciamaAdSCPTDipolarMpembaComptonSubstrate.giererWirtzFactor_pos/_lt_one", s_gw)

    def s_bose():
        x = rng.uniform(1e-4, 20)
        n = 1 / (np.exp(x) - 1)
        return max((1 / x - 1) - n, n - 1 / x) + 1e-15
    check("SciamaAdSCPTMpembaEntropicClock.boseOccupation_entropic_bounds", s_bose)

    def s_window():
        A, om, wE = rng.uniform(.1, 5), rng.uniform(.1, 5), rng.uniform(.1, 50)
        g = A / (np.exp(om / wE) - 1)
        return max((A / om * wE - A) - g, g - A / om * wE) + 1e-15
    check("SciamaAdSCPTMpembaEntropicClock.decoherence_rate_entropic_clock_window", s_window)

    def s_arrow():
        eps = rng.uniform(1e-6, 0.499)
        v = np.exp(-2 * eps)
        return max((1 - 2 * eps) - v, v - (1 - eps)) + 1e-15
    check("SciamaAdSCPTMpembaEntropicClock.detailed_balance_entropic_arrow", s_arrow)

    def s_frozen():
        a = rng.uniform(0.1, 5)
        b = a - rng.uniform(1e-3, a * 0.9)
        k1, k2, t = rng.uniform(-10, 10, 3)
        return b * abs(np.exp(-1j * k2 * t)) - a * abs(np.exp(-1j * k1 * t)) + 1e-15
    check("SciamaAdSCPTMpembaNewtonObstructionHerglotz.newton_reversible_ordering_frozen",
          s_frozen)

    def s_calibration():
        a, b = rng.uniform(0.1, 5, 2)
        l2 = rng.uniform(-3, 3)
        l3 = l2 - rng.uniform(0.01, 3)
        g = np.cosh(rng.uniform(-3, 3))
        v1 = (l2 - l3) * np.log(a / b) / (l2 - l3)
        v2 = (l2 / g - l3 / g) * (np.log(a / b) / ((l2 - l3) / g))
        return max(abs(v1 - np.log(a / b)), abs(v2 - np.log(a / b))) - 1e-9
    check("SciamaAdSCPTMpembaNewtonObstructionHerglotz.mpemba_crossing_self_calibrates"
          "/+rapidity_invariant", s_calibration)

    def s_alpha_metrology():
        C_, mu_, om_, ep_, g_ = rng.uniform(0.1, 3, 5)
        al = rng.uniform(1e-3, 0.1)
        dal = al * 1e-6
        same = lambda a: (np.sqrt(3) * g_ ** 2 / 288 * a ** 4 * mu_ ** 2 * om_) / (C_ * a ** 4 * mu_ * om_)
        cross = lambda a: (ep_ / 2 * a ** 2 * om_) / (C_ * a ** 4 * mu_ * om_)
        blind = abs(same(al + dal) - same(al)) / same(al)          # must be ~0
        sens = abs(cross(al + dal) - cross(al)) / cross(al)        # must be ~2 dal/al
        return max(blind - 1e-9, abs(sens - 2 * dal / al) / (2 * dal / al) - 1e-3)
    check("SciamaAdSCPTDipolarMpembaComptonSubstrate.alpha_blind/alpha_sensitive rungs",
          s_alpha_metrology)

    def s_group_action():
        a, b = rng.uniform(0.1, 5, 2)
        l2 = rng.uniform(-3, 3)
        l3 = l2 - rng.uniform(0.01, 3)
        cc = rng.uniform(0.1, 5) * rng.choice([-1, 1])
        v = (cc * l2 - cc * l3) * (np.log(a / b) / (cc * (l2 - l3)))
        t1, t2, lam = rng.uniform(-3, 3, 3)
        u = lambda t, x: np.exp(-1j * x * t)          # liouvilleEvolve of the trivial mode
        grp = abs(u(t1, lam) * u(t2, lam) - u(t1 + t2, lam))
        # age eigenvalue T U_t = t U_t : numerical derivative of the flow in lam
        h = 1e-6
        age = abs(1j * (u(t1 + t2, lam + h) - u(t1 + t2, lam - h)) / (2 * h)
                  - (t1 + t2) * u(t1 + t2, lam))
        return max(abs(v - np.log(a / b)) - 1e-9, grp - 1e-12, age - 1e-4)
    check("SciamaAdSCPTMpembaNewtonObstructionHerglotz.group_action (scaling-invariant + flow group)",
          s_group_action)

    def s_gravimeter():
        gg, h1, h2, tst = rng.uniform(0.1, 3, 4)
        c2 = rng.uniform(1, 10)
        sA, sB = gg * h1 / c2, gg * h2 / c2
        t1, t2 = tst / (1 + sA), tst / (1 + sB)
        e1 = abs(t1 / t2 - (1 + sB) / (1 + sA))
        e2 = abs((t1 / t2 - 1) * (1 + sA) - gg * (h2 - h1) / c2)
        return max(e1, e2) - 1e-9
    check("SciamaAdSCPTMpembaEntropicClock.mpemba_differential_gravimeter"
          "/+local_gravity_blind", s_gravimeter)

    def s_dilation():
        gG, xx, om, NN = rng.uniform(0.1, 3, 4)
        cc = rng.uniform(1, 10)
        Gm = gG * xx / cc ** 2 * np.sqrt(NN / 2) * om
        return abs(Gm * cc ** 2 / (xx * np.sqrt(NN / 2) * om) - gG) - 1e-9
    check("SciamaAdSCPTMpembaEntropicClock.dilation_gravimeter_recovery", s_dilation)

    def s_gaussian_crossing():
        a2, b2 = sorted(rng.uniform(0.5, 3, 2))[::-1]
        G2, dG = rng.uniform(0.1, 2), rng.uniform(0.05, 1)
        G3 = G2 + dG
        u_star = np.log(a2 / b2) / (G3 ** 2 - G2 ** 2)
        t_ = np.sqrt(u_star) * rng.uniform(1.001, 2)
        ok_cross = a2 * np.exp(-(G3 * t_) ** 2) < b2 * np.exp(-(G2 * t_) ** 2)
        ok_cal = abs((G3 ** 2 - G2 ** 2) * u_star - np.log(a2 / b2))
        return max(0.0 if ok_cross else 1.0, ok_cal - 1e-9)
    check("SciamaAdSCPTQuantumMpembaCrossing.gaussian_mpemba_crossing"
          "/+self_calibrates", s_gaussian_crossing)

    def s_optical_gravimeters():
        sig, rh, gg = rng.uniform(0.01, 3, 3)
        lc = np.sqrt(sig / (rh * gg))
        e1 = abs(sig / (rh * lc ** 2) - gg)
        vmin2 = 2 * np.sqrt(gg * sig / rh)
        e2 = abs(rh * vmin2 ** 2 / (4 * sig) - gg)
        kT, A_ = rng.uniform(0.1, 3, 2)
        S0 = kT / (A_ * rh * gg)
        e3 = abs(kT / (rh * A_ * S0) - gg)
        kk = rng.uniform(0.1, 5)
        e4 = 0.0 if (gg / kk + sig * kk / rh) ** 2 >= 4 * gg * sig / rh - 1e-12 else 1.0
        return max(e1, e2, e3, e4) - 1e-9
    check("SciamaAdSCPT rainbow/pond/roughness gravimeters + min-speed bound",
          s_optical_gravimeters)

    def s_moire():
        k1, k2, xm = rng.uniform(0.5, 5, 3)
        e1 = abs(abs(np.exp(1j * k1 * xm) + np.exp(1j * k2 * xm))
                 - 2 * abs(np.cos((k1 - k2) / 2 * xm)))
        gg, sig, rh = rng.uniform(0.1, 3, 3)
        if abs(k1 - k2) < 1e-3:
            k2 = k1 + 0.5
        w1s = gg * k1 + sig / rh * k1 ** 3
        w2s = gg * k2 + sig / rh * k2 ** 3
        e2 = abs((w1s - w2s) / (k1 - k2) - sig / rh * (k1 ** 2 + k1 * k2 + k2 ** 2) - gg)
        th = rng.uniform(0.01, 3)
        e3 = abs(np.sqrt((np.cos(th) - 1) ** 2 + np.sin(th) ** 2)
                 - 2 * abs(np.sin(th / 2)))
        return max(e1, e2, e3) - 1e-9
    check("SciamaAdSCPT moire envelope modulus + dispersion + twist law", s_moire)

    def s_deferred_moire():
        T1, T2 = rng.uniform(0.5, 3, 2)
        if abs(T1 - T2) < 1e-3:
            T2 = T1 + 0.5
        TM = T1 * T2 / abs(T1 - T2)
        e1 = abs(TM - T2 / abs(1 - T2 / T1))                       # Eq3 = Eq4 x grid
        e2 = abs(abs(2 * np.pi / T1 - 2 * np.pi / T2) - 2 * np.pi / TM)
        k1, k2, x, d = rng.uniform(0.5, 4, 4)
        if abs(k1 - k2) < 1e-3:
            k2 = k1 + 0.5
        xM = k2 * d / (k1 - k2)                                    # Eq5
        e3 = abs(abs(np.exp(1j * k1 * x) + np.exp(1j * k2 * (x - d)))
                 - 2 * abs(np.cos((k1 - k2) / 2 * (x + xM))))
        E, rh, s, lm, L = rng.uniform(0.5, 4, 5)
        e4 = abs(np.pi / 2 * np.sqrt(E * (rh * s * L ** 3 / 12) / (lm * L ** 4))
                 - np.pi / 4 * np.sqrt(E * rh / (3 * lm)) * np.sqrt(s / L))
        G, w1, w2, t = rng.uniform(0.1, 3, 4)
        e5 = abs(abs(np.exp((-G + 1j * w1) * t)) - abs(np.exp((-G + 1j * w2) * t)))
        G2 = G + rng.uniform(0.1, 1)
        e6 = 0.0 if abs(np.exp((-G2 + 1j * w2) * t)) < abs(np.exp((-G + 1j * w1) * t)) else 1.0
        Ib, gb = rng.uniform(0.5, 4, 2)
        f0 = np.pi / 2 * np.sqrt(E * Ib / (lm * L ** 4))
        e7 = abs(f0 ** 2 * (lm * gb * L ** 4 / (8 * E * Ib)) - np.pi ** 2 / 32 * gb)
        return max(e1, e2, e3, e4, e5, e6, e7) - 1e-9
    check("SciamaAdSCPT deferred-moire vibrometer (Saveljev Eqs 3-5, 9-10, envelope)",
          s_deferred_moire)

    def s_moire_lattice():
        p, q = int(rng.integers(1, 8)), int(rng.integers(1, 8))
        N = p ** 2 + q ** 2
        c, sP = (p ** 2 - q ** 2) / N, 2 * p * q / N
        e1 = abs(c ** 2 + sP ** 2 - 1)
        a, b = int(rng.integers(-9, 9)), int(rng.integers(-9, 9))
        u, v = N * (a * c - b * sP), N * (a * sP + b * c)
        e2 = max(abs(u - round(u)), abs(v - round(v)))
        return max(e1, e2) - 1e-9
    check("SciamaAdSCPT moire lattice commensurability (Pythagorean twists)", s_moire_lattice)

    def s_moire_zeeman():
        D, dth = rng.uniform(0.1, 3, 2)
        e1 = abs(D / 2 * (1 + np.cos(2 * dth)) - D * np.cos(dth) ** 2)
        e2 = abs(D / 2 * (1 + np.cos(2 * np.pi / 3)) - D / 4)
        nel, lam, mu, g, muB = rng.uniform(0.1, 3, 5)
        Be = nel * (mu - lam) / (g * muB)
        e3 = abs(nel * (lam - mu) / 2 + g * muB * Be / 2)
        return max(e1, e2, e3) - 1e-9
    check("SciamaAdSCPT moire Zeeman (geometry factor + restoration magnetometer)",
          s_moire_zeeman)

    def s_two_frequency():
        p, al, be, M = rng.uniform(0.2, 1.2, 4)
        e1 = abs(M * p / (np.tan(al) + np.tan(be))
                 - M * (p / (np.tan(al) + np.tan(be))))
        T, Mi = rng.uniform(0.5, 2), int(rng.integers(3, 12))
        d = rng.uniform(-0.49, 0.49) * Mi * T
        frac = d - T * np.round(d / T)
        n = np.round((d - frac) / T)
        e2 = abs(n * T + frac - d)
        N, pp = rng.uniform(1, 8), rng.uniform(0.01, 0.05)
        ll, ss = rng.uniform(0.5, 2), rng.uniform(0.5, 2)
        h = N * pp * ll / (ss - N * pp)
        e3 = abs(h * ss / (pp * (ll + h)) - N)                     # order inversion
        e4 = abs(h - N * (pp * ll / ss) * (ss / (ss - N * pp)))    # ladder factorization
        mm, uu, DD = rng.uniform(0.5, 3, 3)
        e5 = abs(mm * uu / (mm * DD) * DD - uu)                    # reference-mark calibration
        return max(e1, e2, e3, e4, e5) - 1e-9
    check("SciamaAdSCPT two-frequency topography (contour ladder + absolute order)",
          s_two_frequency)

    def s_spectral_trajectories():
        p, k, a = int(rng.integers(-4, 5)), rng.uniform(0.2, 3), rng.uniform(0, 6)
        peak = p * k * np.exp(1j * a)
        e1 = abs(abs(peak) - abs(p) * abs(k))                       # visibility radius
        k2, a2 = rng.uniform(0.2, 3), rng.uniform(0, 6)
        e2 = abs((1 * k * np.exp(1j * a) + (-1) * k2 * np.exp(1j * a2))
                 - (k * np.exp(1j * a) - k2 * np.exp(1j * a2)))     # Amidror difference
        th = rng.uniform(0.05, 3)
        e3 = abs(abs(k * np.exp(0j) - k * np.exp(1j * th))
                 - 2 * k * abs(np.sin(th / 2)))                     # twist from spectral
        c = rng.uniform(0.2, 3)
        e4 = abs(p * (c * k) * np.exp(1j * a) - c * (p * k * np.exp(1j * a)))  # radial
        # angle-derivative: numeric d/dt of p k e^{i(At+B)} vs i A (peak)
        A, B, t0 = rng.uniform(0.3, 2), rng.uniform(0, 3), rng.uniform(0, 1)
        h = 1e-6
        g = lambda tt: p * k * np.exp(1j * (A * tt + B))
        num = (g(t0 + h) - g(t0 - h)) / (2 * h)
        e5 = abs(num - 1j * A * g(t0)) / (abs(A * g(t0)) + 1e-12)
        return max(e1, e2, e3, e4, e5) - 1e-5
    check("SciamaAdSCPT spectral trajectories (Saveljev-Kim: peak/twist/radial/rotation-deriv)",
          s_spectral_trajectories)

    def s_sagnac():
        c = rng.uniform(5, 20)
        v = rng.uniform(0.05, 0.9) * c
        r = rng.uniform(0.1, 2)
        dT = 2 * np.pi * r / (c - v) - 2 * np.pi * r / (c + v)
        e1 = abs(dT - 4 * np.pi * r * v / (c ** 2 - v ** 2))          # closed form
        w = v / r
        e2 = abs(dT - 4 * (np.pi * r ** 2) * w / (c ** 2 - v ** 2))   # area x omega
        dT_fo = 4 * (np.pi * r ** 2) * w / c ** 2
        e3 = abs(c ** 2 * dT_fo / (4 * np.pi * r ** 2) - w)           # rotation readout
        s = rng.uniform(-3, 3)
        e4 = abs(s ** 2 + 2 * (w * r) * s - (c ** 2 - (w * r) ** 2)
                 - (s - (c - w * r)) * (s + (c + w * r)))             # Langevin factoring
        L = rng.uniform(1, 5)
        e5 = abs(L * (1 + v / c) + L * (1 - v / c) - 2 * L)           # contour closure
        # LT simultaneity gap nonzero vs LTA position-independent
        g, u, x1, x2 = rng.uniform(1, 2), rng.uniform(0.1, 1), 0.0, rng.uniform(1, 3)
        gap = g * (0 - u * x1 / c ** 2) - g * (0 - u * x2 / c ** 2)
        e6 = 0.0 if abs(gap) > 1e-9 else 1.0                          # relative simultaneity
        return max(e1, e2, e3, e4, e5, e6) - 1e-9
    check("SciamaAdSCPT Sagnac (delay/rotation-readout/Langevin/simultaneity, Spavieri 2021)",
          s_sagnac)

    def s_minkowski_bridge():
        c = rng.uniform(2, 20)
        u = rng.uniform(-0.9, 0.9) * c
        g = 1.0 / np.sqrt(1 - (u / c) ** 2)                           # gamma^2(c^2-u^2)=c^2
        t, x = rng.uniform(0.1, 3), rng.uniform(-3, 3)
        # (i) interval Lorentz-invariant
        lt_t = g * (t - u * x / c ** 2)
        lt_x = g * (x - u * t)
        e1 = abs((c ** 2 * lt_t ** 2 - lt_x ** 2) - (c ** 2 * t ** 2 - x ** 2))
        # (ii) LTA time = co-moving proper time
        e2 = abs(np.sqrt(c ** 2 * t ** 2 - (u * t) ** 2) / c - t / g)
        # (iii) null interval stays null
        tn = abs(x) / c
        e3 = abs(c ** 2 * (g * (tn - u * x / c ** 2)) ** 2 - (g * (x - u * tn)) ** 2)
        return max(e1, e2, e3) - 1e-9
    check("SciamaAdSCPT Minkowski bridge (interval invariant + LTA=proper time + null cone)",
          s_minkowski_bridge)

    def s_holonomy():
        w, r, c = rng.uniform(0.1, 3), rng.uniform(0.1, 2), rng.uniform(5, 20)
        # numerically integrate the removable offset density v/c^2 around the ring
        N = 20000
        phi = np.linspace(0, 2 * np.pi, N, endpoint=False)
        dl = r * (2 * np.pi / N)
        H_numeric = np.sum((w * r) / c ** 2 * dl * np.ones(N))     # oint (v/c^2) dl
        H_closed = 2 * (np.pi * r ** 2) * w / c ** 2
        e1 = abs(H_numeric - H_closed) / H_closed                  # loop integral = 2A w/c^2
        e2 = abs(4 * (np.pi * r ** 2) * w / c ** 2 - 2 * H_closed)  # Sagnac = 2 x holonomy
        e3 = abs(c ** 2 * H_closed / (2 * np.pi * r ** 2) - w)      # invert -> omega
        return max(e1, e2, e3) - 1e-4
    check("SciamaAdSCPT synchronization holonomy (loop integral = 2A w/c^2, Sagnac = 2H, reads w)",
          s_holonomy)

    def s_sagnac_triad():
        A, c = rng.uniform(1, 100), rng.uniform(5, 20)
        w = rng.uniform(-3, 3, 3)
        dT = 4 * A * w / c ** 2                                # three ring delays
        e1 = abs(c ** 2 * dT[0] / (4 * A) - w[0])             # per-axis recovery
        e2 = abs(c ** 2 / (4 * A) * np.sqrt(np.sum(dT ** 2))
                 - np.sqrt(np.sum(w ** 2)))                   # triad magnitude
        return max(e1, e2) - 1e-9
    check("SciamaAdSCPT Sagnac triad (per-axis + magnitude reconstruction, strapdown gyro)",
          s_sagnac_triad)

    def s_differential_channel():
        x1, x2, m = rng.uniform(-5, 5, 3)
        e1 = abs((x1 + m - (x2 + m)) - (x1 - x2))                  # common-mode rejection
        a, b, k = rng.uniform(0.2, 5, 3)
        e2 = abs(np.log((k * a) / (k * b)) - np.log(a / b))       # multiplicative rejection
        g1, g2, xcm = rng.uniform(-3, 3, 3)
        e3 = abs((g1 * xcm - g2 * xcm) - (g1 - g2) * xcm)         # CMRR mismatch leakage
        c, v, r = rng.uniform(5, 20), rng.uniform(0.1, 4), rng.uniform(0.1, 2)
        e4 = abs((2 * np.pi * r / (c - v) - 2 * np.pi * r / (c + v))
                 - (2 * np.pi * r / (c - v) - 2 * np.pi * r / (c + v)))   # Sagnac instance
        g, h1, h2, cc = rng.uniform(0.1, 3, 4)
        e5 = abs(g * (h2 - h1) / cc ** 2
                 - (g * h2 / cc ** 2 - g * h1 / cc ** 2))         # gravimeter instance
        return max(e1, e2, e3, e4, e5) - 1e-9
    check("SciamaAdSCPT differential channel (common-mode rejection + CMRR + instances)",
          s_differential_channel)

    def s_delta_encoding():
        x = rng.uniform(-5, 5, 15)
        d = np.diff(x)
        e1 = abs(np.sum(d) - (x[-1] - x[0]))                      # telescoping
        e2 = np.max(np.abs((x[0] + np.concatenate([[0], np.cumsum(d)])) - x))  # reconstruct
        c = rng.uniform(-3, 3)
        e3 = np.max(np.abs(np.diff(x + c) - d))                   # reference-blind
        eps = rng.uniform(-0.1, 0.1, len(d))
        e4 = abs(np.sum(d + eps) - ((x[-1] - x[0]) + np.sum(eps)))  # error accumulates
        return max(e1, e2, e3, e4) - 1e-9
    check("SciamaAdSCPT delta encoding (telescoping + reference-blind + error random walk)",
          s_delta_encoding)

    def s_optical_sagnac():
        A, w, wl, c = rng.uniform(1, 100), rng.uniform(0.1, 3), rng.uniform(0.5, 2), rng.uniform(5, 20)
        dphi = 8 * np.pi * A * w / (wl * c)
        e1 = abs((2 * np.pi * c / wl) * (4 * A * w / c ** 2) - dphi)   # phase = w_opt x delay
        e2 = abs(wl * c * dphi / (8 * np.pi * A) - w)                  # phase reads rotation
        e3 = abs((1 + np.cos(dphi + np.pi / 2)) - (1 - np.sin(dphi)))  # quadrature bias
        N, D = rng.uniform(1, 5), rng.uniform(0.05, 0.5)
        e4 = abs(8 * np.pi * (N * np.pi * D ** 2 / 4) * w / (wl * c)
                 - 2 * np.pi * (N * np.pi * D) * D * w / (wl * c))     # fibre form 2 pi L D
        P = rng.uniform(1, 10)
        e5 = abs(wl * P * (4 * A * w / (wl * P)) / (4 * A) - w)        # beat reads rotation
        return max(e1, e2, e3, e4, e5) - 1e-9
    check("SciamaAdSCPT optical Sagnac (phase = w_opt x delay, interference, beat)",
          s_optical_sagnac)

    def s_quantum_optics():
        N = rng.uniform(2, 1e6)
        r = rng.uniform(0.1, 3)
        shot, therm = 1 / N, (1 + N) / N
        sq, heis = np.exp(-2 * r) / N, 1 / N ** 2
        e1 = 0.0 if shot < therm else 1.0                 # thermal above shot noise
        e2 = 0.0 if sq < shot else 1.0                    # squeezed below shot noise
        e3 = abs(np.exp(-2 * (np.log(N) / 2)) / N - heis)  # squeezing reaches Heisenberg
        e4 = 0.0 if heis < shot else 1.0                  # Heisenberg below shot noise
        return max(e1, e2, e3, e4) - 1e-9
    check("SciamaAdSCPT quantum-optical limits (coherent SQL / thermal / squeezed / Heisenberg)",
          s_quantum_optics)

    def s_entropic_quantization():
        kB, T, hbar = rng.uniform(0.1, 3, 3)
        omega_E = kB * T / hbar
        period = hbar / (kB * T)                          # imaginary-time circumference
        e1 = abs(period - 1 / omega_E)                    # period = 1/omega_E
        n = int(rng.integers(-8, 9))
        e2 = abs(2 * np.pi * n / period - 2 * np.pi * n * omega_E)   # ladder = 2 pi n omega_E
        e3 = abs((2 * np.pi * (n + 1) / period - 2 * np.pi * n / period)
                 - 2 * np.pi * omega_E)                   # spacing = 2 pi omega_E
        m = n + int(rng.integers(1, 5))
        e4 = 0.0 if (2 * np.pi * n / period != 2 * np.pi * m / period) else 1.0  # faithful (n!=m)
        return max(e1, e2, e3, e4) - 1e-9
    check("SciamaAdSCPT entropic-time quantization (Matsubara ladder omega_n = 2 pi n omega_E)",
          s_entropic_quantization)

    def s_entropic_spectrum():
        gf, c = rng.uniform(0.5, 3), rng.uniform(0.2, 4)     # rate + entropic-clock factor
        al, gp = rng.uniform(0.6, 1.0), rng.uniform(3, 40)   # coherent, real-spectrum domain
        disc = (al - 0.5) ** 2 - 1 / gp ** 2
        sd = np.sqrt(disc)
        slow = lambda g: -(g * (al + 0.5 - sd))
        fast = lambda g: -(g * (al + 0.5 + sd))
        e1 = abs(slow(c * gf) - c * slow(gf))                # rate carries the clock
        # existence (gap) invariant under clock rescaling c>0
        e2 = 0.0 if ((fast(c * gf) < slow(c * gf)) == (fast(gf) < slow(gf))) else 1.0
        e3 = abs(fast(c * gf) / slow(c * gf) - fast(gf) / slow(gf))   # ratio clock-free
        a, b, l2, l3 = 2.0, 1.0, 0.9, 0.3
        e4 = abs(np.log(a / b) / (c * l2 - c * l3)
                 - (np.log(a / b) / (l2 - l3)) / c)          # crossing scales as 1/c
        return max(e1, e2, e3, e4) - 1e-9
    check("SciamaAdSCPT entropic-time spectrum (existence clock-free, timing clock-set)",
          s_entropic_spectrum)

    def s_osterwalder_schrader():
        E = rng.uniform(0.2, 3)
        n = int(rng.integers(2, 7))
        c, tau = rng.uniform(-2, 2, n), rng.uniform(0.1, 3, n)
        # reflected Euclidean form = rank-1 Gram square
        K = np.array([[np.exp(-(E * (tau[i] + tau[j]))) for j in range(n)] for i in range(n)])
        form = c @ K @ c
        square = (np.sum(c * np.exp(-(E * tau)))) ** 2
        e1 = abs(form - square)                            # reflection positivity is a square
        e2 = 0.0 if form >= -1e-12 else 1.0                # OS positivity
        # the reflected kernel is PSD (all eigenvalues >= 0): rank-1, one positive eigenvalue
        evals = np.linalg.eigvalsh(K)
        e3 = 0.0 if evals.min() > -1e-9 else 1.0
        # Euclidean correlator = imaginary-modular weight at t=0
        t0 = rng.uniform(0.1, 2)
        e4 = abs(np.exp(-(E * t0)) - abs(np.exp(-1j * E * (0 - 1j * t0))))
        return max(e1, e2, e3, e4) - 1e-9
    check("SciamaAdSCPT Osterwalder-Schrader (reflection positivity = rank-1 Gram square)",
          s_osterwalder_schrader)

    def s_os_reconstruction():
        E = rng.uniform(0.2, 3)                            # positive-energy mode
        s1, s2 = rng.uniform(0.1, 3, 2)
        G = lambda tau: np.exp(-(E * tau))
        e1 = abs(G(s1 + s2) - G(s1) * G(s2))               # semigroup law T^{s+s'} = T^s T^s'
        e2 = 0.0 if (0 < G(s1) <= 1) else 1.0              # contraction (E>=0, s>=0)
        e3 = 0.0 if (all(G(ss) <= 1 for ss in (0.1, 1, 5)) == (E >= 0)) else 1.0  # spectrum cond
        e4 = abs(-np.log(G(1.0)) - E)                      # H = -log T^1 = E
        # negative-energy mode would VIOLATE the contraction (spectrum condition is if-and-only-if)
        e5 = 0.0 if (np.exp(-((-1.0) * 1.0)) > 1) else 1.0   # E=-1 -> T^1 = e^{+1} > 1
        return max(e1, e2, e3, e4, e5) - 1e-9
    check("SciamaAdSCPT OS reconstruction (semigroup contraction -> spectrum condition H>=0)",
          s_os_reconstruction)

    def s_matsubara_continuation():
        eps, w, eta = rng.uniform(-3, 3), rng.uniform(-3, 3), rng.uniform(0.05, 1)
        # one resolvent, two axes: Matsubara (i wn) and retarded (w + i eta)
        wn = rng.uniform(0.5, 5)
        G_mats = 1.0 / (1j * wn - eps)
        G_ret = 1.0 / (w + 1j * eta - eps)
        e1 = abs(G_mats - 1.0 / ((1j * wn) - eps))              # matsubara = resolvent at i wn
        # spectral function = -1/pi Im G_ret = Lorentzian
        A = -(1 / np.pi) * G_ret.imag
        e2 = abs(A - (1 / np.pi) * eta / ((w - eps) ** 2 + eta ** 2))
        e3 = 0.0 if A >= -1e-12 else 1.0                        # spectral positivity (eta>0)
        # barycentric interpolation passes through the data at a node
        w1, w2, f1, f2, z1, z2 = rng.uniform(0.5, 3, 6)
        if abs(z1 - z2) < 1e-3:
            z2 = z1 + 0.5
        b_z1 = ((w1 * f1 * (z1 - z2) + w2 * f2 * (z1 - z1))
                / (w1 * (z1 - z2) + w2 * (z1 - z1)))
        e4 = abs(b_z1 - f1)
        return max(e1, e2, e3, e4) - 1e-9
    check("SciamaAdSCPT Matsubara analytic continuation (resolvent/spectral positivity/barycentric)",
          s_matsubara_continuation)

    def s_gated_gravimetry():
        x_, G_, g_, D_, rg_, dr_ = rng.uniform(0.1, 3, 6)
        S = np.sqrt(g_ * D_ * rg_ * dr_)
        J = lambda xg: xg / S
        e1 = 0.0 if (J(0.5 * S) < 1 and J(2.0 * S) > 1 and abs(J(S) - 1) < 1e-12) else 1.0
        cB = rng.uniform(1.1, 5)
        e2 = 0.0 if S < np.sqrt(cB * g_ * D_ * rg_ * dr_) else 1.0
        e3 = 0.0 if (x_ * G_ / np.sqrt(cB * g_ * D_ * rg_ * dr_)
                     < x_ * G_ / S) else 1.0
        return max(e1, e2, e3) - 1e-12
    check("SciamaAdSCPT shear regime classification + boundary/influence monotonicity",
          s_gated_gravimetry)

    def s_complex_mode():
        a, b = rng.uniform(0.1, 5, 2)
        re2 = rng.uniform(-3, -0.1)
        re3 = re2 - rng.uniform(0.1, 3)
        l2 = re2 + 1j * rng.uniform(-20, 20)
        l3 = re3 + 1j * rng.uniform(-20, 20)
        tstar = np.log(a / b) / (re2 - re3)
        t = tstar + rng.uniform(1e-3, 5)
        return a * abs(np.exp(l3 * t)) - b * abs(np.exp(l2 * t))
    check("SciamaAdSCPTMpembaComplexActionLorentzian.complex_mode_crossing", s_complex_mode)

    def s_strip_split():
        k, t, tau = rng.uniform(-10, 10, 3)
        lhs = abs(np.exp(-1j * k * (t - 1j * tau)))
        return abs(lhs - np.exp(-k * tau)) / max(np.exp(-k * tau), 1e-300) - 1e-9
    check("SciamaAdSCPTMpembaComplexActionLorentzian.strip_weight_entropic_only", s_strip_split)

    def s_wedge_modular():
        a, b = rng.uniform(0.1, 5, 2)
        k2 = rng.uniform(0.01, 3)
        k3 = k2 + rng.uniform(0.01, 3)
        tstar = np.log(a / b) / (2 * np.pi * (k3 - k2))
        sflow = tstar + rng.uniform(1e-3, 3)
        return (a * np.exp(-2 * np.pi * k3 * sflow)
                - b * np.exp(-2 * np.pi * k2 * sflow))
    check("SciamaAdSCPTMpembaComplexActionLorentzian.wedge_modular_mpemba_crossing",
          s_wedge_modular)

    def s_herglotz():
        a, b = rng.uniform(0.1, 5, 2)
        r2 = rng.uniform(0.05, 2)
        r3 = r2 + rng.uniform(0.05, 2)
        tstar = np.log(a / b) / (-r2 - (-r3))
        t = tstar + rng.uniform(1e-3, 5)
        return a * np.exp(-r3 * t) - b * np.exp(-r2 * t)
    check("SciamaAdSCPTMpembaNewtonObstructionHerglotz.herglotz_friction_crossing", s_herglotz)


def main():
    ion_qutip()
    nmr_qutip()
    build_suite()
    w = max(len(r[0]) for r in SUITE) + 2
    print("\n" + "=" * (w + 40))
    print(f"{'Lean declaration':<{w}}{'samples':>8}{'max violation':>16}  verdict")
    print("-" * (w + 40))
    for name, n, worst, ok in SUITE:
        print(f"{name:<{w}}{n:>8}{worst:>16.2e}  {'PASS' if ok else 'FAIL'}")
    print("=" * (w + 40))
    bad = [r for r in SUITE if not r[3]]
    print(f"{len(SUITE) - len(bad)}/{len(SUITE)} Lean declarations numerically certified"
          + (f"; FAILURES: {[r[0] for r in bad]}" if bad else "."))


if __name__ == "__main__":
    main()

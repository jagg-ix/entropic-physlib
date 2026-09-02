#!/usr/bin/env python3
"""Numerical computation of the complex-action / Lorentzian-conversion /
Bisognano-Wichmann layer of the Mpemba chain (the content of the Lean module
SciamaAdSCPTMpembaComplexActionLorentzian), on the actual experimental models.

[1] COMPLEX SPECTRUM & THE LORENTZIAN<->ENTROPIC BIFURCATION: the trapped-ion
    Liouvillian's eigenvalues vs gamma' -- below the bifurcation
    gamma_b' = 1/|alpha - 1/2| the y-z modes are a complex pair (underdamped:
    Lorentzian oscillation present, EQUAL real parts -> no Mpemba gap); above
    it they are real (pure entropic decay, gap opens).  The Mpemba effect
    exists exactly where the Lorentzian component dies.
[2] COMPLEX-MODE CROSSING computed on the real system: in the underdamped
    regime the oscillating y-z mode still crosses the real x-mode at the t*
    computed from real parts alone (Lean complex_mode_crossing).
[3] THE STRIP / WICK ROTATION: the continued weight e^{lambda z} on
    z = t - i tau: Re(lambda z) = Re(lambda) t + Im(lambda) tau -- Lorentzian
    time couples to the entropic rate component and entropic time to the
    oscillatory component (roles exchange across the strip); for the pure
    reversible generator e^{-i kappa z} the modulus is e^{-kappa tau} exactly
    (Lean strip_weight_entropic_only).  complexBoost strip anchors
    Lambda(i pi) = -1, Lambda(i pi/2) = i J computed via scipy expm.
[4] MODULAR / KMS (Wichmann-related, computed): the modular Hamiltonian
    K = -log rho_ss of the ion steady state, its modular spectrum, the
    numerically verified KMS identity F(s-i) = Tr(rho sigma_s(B) A) for the
    modular flow sigma_s(B) = rho^{is} B rho^{-is}, and the Mpemba crossing of
    two modular weights of the COMPUTED spectrum under modular flow
    (Lean wedge_modular_mpemba_crossing).

Run:  python3 scripts/mpemba_complex_action_lorentzian.py
"""
import numpy as np
from scipy.linalg import expm
import qutip as qt

ALPHA = 0.94


def ion_ops(gfp, alpha, g=1.0):
    down, up = qt.basis(2, 0), qt.basis(2, 1)
    H = 0.5 * (1.0 / gfp) * qt.sigmax()
    return H, [np.sqrt(2 * alpha * g) * down * up.dag(),
               np.sqrt(2 * (1 - alpha) * g) * up * up.dag()]


def yz_modes(gfp):
    """The two y-z Bloch-sector eigenvalues of the ion Liouvillian."""
    H, c = ion_ops(gfp, ALPHA)
    ev = np.linalg.eigvals(qt.liouvillian(H, c).full())
    ev = np.array(sorted(ev, key=lambda z: z.real))
    ev = ev[np.abs(ev) > 1e-9]                      # drop steady mode
    ix = int(np.argmin(np.abs(ev - (-1.0))))        # x-mode is exactly -gamma_f
    return np.delete(ev, ix)


def section1():
    gb = 1 / abs(ALPHA - 0.5)
    print(f"[1] bifurcation predicted gamma_b' = 1/|alpha-1/2| = {gb:.4f}")
    print(f"    {'gamma_f':>8} {'Re lam_-':>10} {'Re lam_+':>10} {'Im lam':>10} {'Re-gap':>9}  regime")
    for gfp in (1.0, 1.5, 2.0, 2.2727, 2.5, 5.0, 15.0):
        m = yz_modes(gfp)
        gap = abs(m[0].real - m[1].real)
        osc = max(abs(m[0].imag), abs(m[1].imag))
        reg = "LORENTZIAN (underdamped, no Mpemba gap)" if osc > 1e-6 else "ENTROPIC (overdamped, gap open)"
        print(f"    {gfp:>8.4f} {m[0].real:>10.4f} {m[1].real:>10.4f} {osc:>10.4f} {gap:>9.4f}  {reg}")
    print("    -> the Mpemba gap opens exactly where the Lorentzian (oscillatory) component dies.")


def section2():
    gfp = 1.5                                   # underdamped regime
    m = yz_modes(gfp)
    lam_yz = m[0]                               # complex mode, Re = -(alpha+1/2)
    lam_x = -1.0 + 0j                           # x-mode, real
    a, b = 1.0, 0.35                            # amplitudes: oscillating mode starts larger
    tstar = np.log(a / b) / (lam_x.real - lam_yz.real)
    ts = np.linspace(0, 3 * tstar, 20001)
    fa = a * np.abs(np.exp(lam_yz * ts))
    fb = b * np.abs(np.exp(lam_x * ts))
    idx = np.where(np.diff(np.sign(fa - fb)) != 0)[0]
    tc = ts[idx[0]] if len(idx) else np.nan
    print(f"\n[2] complex-mode crossing at gamma_f'={gfp} (underdamped): "
          f"lam_yz = {lam_yz:.4f} (oscillating), lam_x = {lam_x.real:.1f}")
    print(f"    predicted t* from Re parts alone = {tstar:.4f} ; computed modulus crossing = {tc:.4f} "
          f"(match: {abs(tc - tstar) < 2e-3})")


def section3():
    # strip landscape for a complex mode: Re(lambda z) = Re lam * t + Im lam * tau
    lam = yz_modes(1.5)[0]
    rngT, rngTau = np.linspace(-2, 2, 41), np.linspace(0, 2, 21)
    worst = 0.0
    for t in rngT:
        for tau in rngTau:
            z = t - 1j * tau
            lhs = abs(np.exp(lam * z))
            rhs = np.exp(lam.real * t + lam.imag * tau)
            worst = max(worst, abs(lhs - rhs) / rhs)
    print(f"\n[3] strip landscape |e^(lam z)| = e^(Re lam * t + Im lam * tau): max rel dev = {worst:.1e}")
    print("    -> under Wick rotation the roles exchange: entropic time couples to the OSCILLATORY part.")
    kappa = 0.7
    worst2 = max(abs(abs(np.exp(-1j * kappa * (t - 1j * tau))) - np.exp(-kappa * tau))
                 for t in rngT for tau in rngTau)
    print(f"    pure reversible generator: |e^(-i k(t - i tau))| = e^(-k tau): max dev = {worst2:.1e} "
          f"(Lean strip_weight_entropic_only)")
    # complexBoost strip anchors via scipy expm: Lambda(z) = expm(z * offdiag(1,1))
    Kb = np.array([[0, 1], [1, 0]], dtype=complex)
    edge = expm(1j * np.pi * Kb)
    half = expm(1j * np.pi / 2 * Kb)
    print(f"    expm strip anchors: Lambda(i pi) = -1: {np.allclose(edge, -np.eye(2), atol=1e-12)} ; "
          f"Lambda(i pi/2) = i J: {np.allclose(half, 1j * Kb, atol=1e-12)}")


def section4():
    gfp = 15.0
    H, c = ion_ops(gfp, ALPHA)
    rho = qt.steadystate(H, c).full()
    p, U = np.linalg.eigh(rho)
    kap = -np.log(p)                                        # modular energies
    print(f"\n[4] modular structure of the computed steady state (gamma_f'={gfp}):")
    print(f"    spectrum p = {np.round(p, 5)} ; modular energies kappa = {np.round(kap, 4)}")
    print(f"    BW ladder Delta = p_1/p_2 = {p[0] / p[1]:.5f} = e^-(k1-k2) = {np.exp(-(kap[0] - kap[1])):.5f}")

    def mpow(rho, w):                                       # rho^w for complex w
        return U @ np.diag(p.astype(complex) ** w) @ U.conj().T
    A = np.array([[0, 1], [1, 0]], dtype=complex)           # sigma_x
    B = np.array([[0, -1j], [1j, 0]])                       # sigma_y
    worst = 0.0
    for s in (-0.7, 0.0, 0.4, 1.3):
        sigB = mpow(rho, 1j * s) @ B @ mpow(rho, -1j * s)
        sigB_shift = mpow(rho, 1j * (s - 1j)) @ B @ mpow(rho, -1j * (s - 1j))
        lhs = np.trace(rho @ A @ sigB_shift)                # F(s - i)
        rhs = np.trace(rho @ sigB @ A)                      # G(s)
        worst = max(worst, abs(lhs - rhs) / max(abs(lhs), abs(rhs), 1e-30))
    print(f"    KMS identity F(s-i) = Tr(rho sigma_s(B) A): max rel dev over s = {worst:.1e}  "
          f"(Tomita-Takesaki flow of the computed state; sigma_s(B) = rho^is B rho^-is)")

    # Mpemba crossing of two modular weights of the COMPUTED spectrum under modular flow
    k2, k3 = sorted(kap)                                    # k2 < k3
    a, b = 1.0, 0.4
    sstar = np.log(a / b) / ((k3 - k2))                     # rates -k under flow e^{-k s}
    ss = np.linspace(0, 3 * sstar, 20001)
    fa, fb = a * np.exp(-k3 * ss), b * np.exp(-k2 * ss)
    idx = np.where(np.diff(np.sign(fa - fb)) != 0)[0]
    sc = ss[idx[0]] if len(idx) else np.nan
    print(f"    IMAGINARY-modular-time (Euclidean) Mpemba crossing of the computed ladder: "
          f"predicted s* = {sstar:.4f}, computed = {sc:.4f} (match: {abs(sc - sstar) < 2e-3})")
    print("    (Lean wedge_modular_mpemba_crossing; real modular flow is unitary and FREEZES the")
    print("     ordering -- real_modular_ordering_frozen: entropic time is not the Tomita-Takesaki flow)")


if __name__ == "__main__":
    section1()
    section2()
    section3()
    section4()

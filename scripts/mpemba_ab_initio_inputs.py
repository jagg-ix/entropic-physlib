#!/usr/bin/env python3
"""Ab initio computation of the Mpemba first-principles inputs.

Replaces the scaling-law estimates and literature lookups of
validate_mpemba_experiments.py with proper calculations:

  [QED]   Exact hydrogenic bound-state spontaneous emission: the 2p->1s rate
          from the analytic Coulomb eigenfunctions (radial integral by
          quadrature, reduced-mass corrected) and the QED emission formula
          A = w^3 e^2 R^2 / (9 pi eps0 hbar c^3).  No estimated matrix
          element anywhere -- this validates the E1 operator machinery
          exactly; the Sr+ rungs of the alpha ladder differ from it only by
          many-electron matrix elements (declared out of scope; lattice-level
          atomic many-body theory would supply them).
  [QCHEM] Hartree-Fock SCF geometry of ethylene (pyscf, D2h, Nelder-Mead on
          (r_CC, r_CH, HCH)): the geminal H-H distance r_HH = 2 r_CH sin(HCH/2)
          solved from the molecular Coulomb Hamiltonian -- fundamental
          constants + basis set only, no tabulated geometry.  The vinylidene
          CH2= fragment of 2-chloroacrylonitrile is taken transferable
          (standard sp2 transferability; declared).
  [QCD]   SU(6) spin-flavor quark model for the proton g-factor: the
          color-singlet three-quark structure the repo's QCD arc
          (ColorSingletBaryon) formalizes gives mu_p = (4 mu_u - mu_d)/3;
          with constituent mass m_q = m_p/3 this is mu_p = 3 mu_N (g_p = 6),
          and the mass-independent sharp prediction mu_p/mu_n = -3/2.
          (Percent-level g_p needs lattice QCD; cited, not run here.)

The chain then re-derives the NMR T1 with every input computed:
g_p from QCD structure, r_HH from SCF, tau_c from Gierer-Wirtz/SED.

Run:  python3 scripts/mpemba_ab_initio_inputs.py
"""
import numpy as np

hbar = 1.054571817e-34
e = 1.602176634e-19
me = 9.1093837015e-31
mp = 1.67262192e-27
c = 2.99792458e8
eps0 = 8.8541878128e-12
kB = 1.380649e-23
alpha = e ** 2 / (4 * np.pi * eps0 * hbar * c)

ROWS = []


def row(label, model, ref, refsrc, note=""):
    dev = abs(model - ref) / abs(ref) * 100
    ROWS.append((label, model, ref, dev, refsrc, note))
    return model


# ============================================================================
# [QED] exact hydrogenic 2p -> 1s
# ============================================================================
def qed_lyman_alpha():
    mu = me * mp / (me + mp)                      # reduced mass (proper bound state)
    a0 = hbar / (mu * c * alpha)
    r = np.linspace(1e-4, 60, 400001) * a0
    R10 = 2 * a0 ** -1.5 * np.exp(-r / a0)
    R21 = (1 / (2 * np.sqrt(6))) * a0 ** -1.5 * (r / a0) * np.exp(-r / (2 * a0))
    n10 = np.trapezoid(R10 ** 2 * r ** 2, r)      # normalization checks (must be 1)
    n21 = np.trapezoid(R21 ** 2 * r ** 2, r)
    R = np.trapezoid(R10 * r * R21 * r ** 2, r)   # radial matrix element <1s|r|2p>
    w = (3 / 8) * alpha ** 2 * (mu * c ** 2 / hbar)   # Lyman-alpha frequency
    A = w ** 3 * e ** 2 * R ** 2 / (9 * np.pi * eps0 * hbar * c ** 3)
    print(f"[QED] norms: <1s|1s>={n10:.6f} <2p|2p>={n21:.6f} ; R = {R / a0:.6f} a0 "
          f"(analytic 2^7 sqrt6/3^5 = {128 * np.sqrt(6) / 243:.6f})")
    row("QED H 2p->1s rate A21 (s^-1)", A, 6.2649e8, "NIST ASD",
        "exact Coulomb eigenfunctions; no fitted or estimated matrix element")
    return A


# ============================================================================
# [QCHEM] ethylene HF geometry -> geminal H-H distance
# ============================================================================
def qchem_ethylene(basis):
    from pyscf import gto, scf
    from scipy.optimize import minimize

    def energy(p):
        rcc, rch, hch = p
        h = np.deg2rad(hch) / 2
        d = rcc / 2
        atoms = [("C", (0, 0, d)), ("C", (0, 0, -d))]
        for sz, sy in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
            atoms.append(("H", (0, sy * rch * np.sin(h), sz * (d + rch * np.cos(h)))))
        mol = gto.M(atom=atoms, basis=basis, unit="Angstrom", verbose=0)
        return scf.RHF(mol).kernel()

    res = minimize(energy, x0=np.array([1.33, 1.08, 117.0]), method="Nelder-Mead",
                   options=dict(xatol=1e-4, fatol=1e-9, maxiter=400))
    rcc, rch, hch = res.x
    rhh = 2 * rch * np.sin(np.deg2rad(hch) / 2)
    print(f"[QCHEM] HF/{basis}: E = {res.fun:.6f} Ha ; r_CC = {rcc:.4f} A, "
          f"r_CH = {rch:.4f} A, HCH = {hch:.2f} deg -> r_HH = {rhh:.4f} A")
    return rhh


# ============================================================================
# [QCD] SU(6) quark model
# ============================================================================
def qcd_su6():
    m_q = mp / 3                                   # constituent quark mass
    mu_N = e * hbar / (2 * mp)
    mu_u = (2 / 3) * e * hbar / (2 * m_q)          # = 2 mu_N
    mu_d = (-1 / 3) * e * hbar / (2 * m_q)         # = -mu_N
    mu_p = (4 * mu_u - mu_d) / 3
    mu_n = (4 * mu_d - mu_u) / 3
    g_p = 2 * mu_p / mu_N
    row("QCD SU(6) proton g-factor", g_p, 5.5856946893, "CODATA",
        "color-singlet 3-quark spin-flavor state, m_q = m_p/3; lattice QCD for %-level")
    row("QCD SU(6) mu_p/mu_n", mu_p / mu_n, -1.45989806, "CODATA",
        "mass-independent SU(6) prediction -3/2")
    return g_p


# ============================================================================
# chain: NMR T1 with computed inputs
# ============================================================================
def nmr_t1(g, r_hh, eta=2.0e-3, T=295.0, aM=2.66e-10, aS=2.56e-10):
    gam = g * e / (2 * mp)
    b = (1 / (4 * np.pi * eps0 * c ** 2)) * gam ** 2 * hbar / (r_hh * 1e-10) ** 3
    rho = aS / aM
    f = 1.0 / (6 * rho + (1 + rho) ** -3)
    tau = f * 4 * np.pi * eta * aM ** 3 / (3 * kB * T)
    K0 = 12 * b ** 2 * tau / 5
    return 24 / (15 * K0), b, tau


def main():
    qed_lyman_alpha()

    try:
        rhh = qchem_ethylene("6-31g(d)")
    except Exception as ex:
        print(f"[QCHEM] 6-31g(d) failed ({ex}); falling back to sto-3g")
        rhh = qchem_ethylene("sto-3g")
    row("QCHEM ethylene geminal r_HH (A)", rhh, 1.847, "microwave r0 structure",
        "solved from the molecular Coulomb Hamiltonian (HF SCF)")

    g_su6 = qcd_su6()

    for label, g, r in (("NMR T1: QCD g_p + QCHEM r_HH", g_su6, rhh),
                        ("NMR T1: CODATA g_p + QCHEM r_HH", 5.5856946893, rhh)):
        T1, b, tau = nmr_t1(g, r)
        row(label + " (s)", T1, 5.7, "Chatterjee 2509.13451",
            f"b/2pi = {b / 2 / np.pi / 1e3:.1f} kHz, tau_c = {tau * 1e12:.2f} ps")

    # ------------------------------------------------------------------
    # [ENTROPIC TIME] temperature enters only as the tick rate k_B T / hbar
    # (Lean: SciamaAdSCPTMpembaEntropicClock)
    # ------------------------------------------------------------------
    T = 295.0
    omega_E = kB * T / hbar
    om0 = 5.5856946893 * e / (2 * mp) * 11.7          # NMR Larmor
    eps_c = om0 / (2 * omega_E)
    exact = np.exp(-2 * eps_c)
    print(f"\n[ENTROPIC TIME] omega_E = k_B T/hbar = {omega_E:.4e} /s at T = {T} K")
    print(f"  NMR polarization = clock ratio: eps = om0/(2 omega_E) = {eps_c:.3e}")
    print(f"  detailed-balance bracket: 1-2eps = {1 - 2 * eps_c:.9f} < e^(-2eps) = {exact:.9f}"
          f" < 1-eps = {1 - eps_c:.9f}  (gap O(eps^2) = {abs(exact - (1 - 2 * eps_c)):.1e})")
    T1_qcd, b_qcd, tau_qcd = nmr_t1(g_su6, rhh)
    K0 = 24 / (15 * T1_qcd)
    print(f"  NMR rates per entropic tick: K0/omega_E = {K0 / omega_E:.3e} ; "
          f"crossing tau* = omega_E * t* = {omega_E * 1.962 / K0:.3e} entropic ticks")
    print(f"  ION temperature map (gamma proportional to omega_E): T_i/T_f = gamma_i'/gamma_f' ; "
          f"T_SME/T_f = 0.0762/15 = {0.0762 / 15:.2e}")
    print("  hotter = the entropic clock ticks faster: the Mpemba dial diagram is a temperature diagram.")

    # ------------------------------------------------------------------
    # [GRAVIMETER] Mpemba gravimetry (Lean: mpemba_differential_gravimeter)
    # ------------------------------------------------------------------
    c_ = 2.99792458e8
    tstar = 6.78                                     # NMR two-mode crossing (s)
    print("\n[GRAVIMETER] two equal-proper-physics stations, one common clock:")
    print("  locally BLIND (equivalence principle: calibration point is scaling-invariant);")
    print("  differentially sharp: g dh/c^2 = (t1/t2 - 1)(1 + g h1/c^2), all RHS measured.")
    for name, GM, R in (("Earth", 3.986e14, 6.371e6), ("Mars", 4.283e13, 3.390e6),
                        ("Jupiter", 1.267e17, 6.991e7)):
        phi = GM / (R * c_ ** 2)
        print(f"  {name:8} surface GM/Rc^2 = {phi:.2e} ; crossing shift vs infinity = "
              f"{phi * tstar:.2e} s of t* = {tstar} s")
    per_m = 9.81 / c_ ** 2
    print(f"  Earth per metre: gh/c^2 = {per_m:.2e}/m -> Delta t* = {per_m * tstar:.1e} s/m")
    print("  VERDICT: exact in principle; sensitivity needs sigma(t*)/t* ~ Phi/c^2 "
          "(optical-clock territory).")
    print("  The conceptual gain is systematics: self-calibration needs no unit at either station.")
    # -- the entropic-time gravimeter that IS practical: dilation decoherence (Pikovski) --
    omega_E295 = kB * 295.0 / hbar
    print("\n[GRAVIMETER-ENTROPIC] time-dilation decoherence: Gamma = (g x/c^2) sqrt(N/2) omega_E")
    for name, N_, x_ in (("gram, 1 um", 1e23, 1e-6), ("microgram, 1 um", 1e17, 1e-6),
                         ("nanogram, 10 um", 1e14, 1e-5)):
        Gam = 9.81 * x_ / c_ ** 2 * np.sqrt(N_ / 2) * omega_E295
        print(f"  {name:16}: Gamma = {Gam:.3g} /s  (tau_dec = {1/Gam:.3g} s)")
    print("  g recovered as c^2 Gamma/(x sqrt(N/2) omega_E): delta g/g = delta Gamma/Gamma "
          "(~percent) -- RATE not timing;")
    print("  ratio version: same apparatus on two planets -> Gamma1/Gamma2 = g1/g2, "
          "unit- and calibration-free;")
    print("  decay SHAPE is Gaussian (crossing at (G3^2-G2^2) t*^2 = log(a/b), squared-time "
          "calibration);")
    print("  planets scale linearly: Gamma(Mars)/Gamma(Earth) = 0.38, Jupiter = 2.53.")
    print("  HONESTY: the rates assume the superposition EXISTS; today's records "
          "(~2.5e4 amu molecules,")
    for name, N_, x_ in (("25 kDa molecule, 0.1 um", 2.5e3, 1e-7),
                         ("MAQRO-class 1e10 atoms, 0.1 um", 1e10, 1e-7)):
        Gam = 9.81 * x_ / c_ ** 2 * np.sqrt(N_ / 2) * omega_E295
        print(f"    {name:28}: Gamma = {Gam:.2g} /s -- not yet measurable)")
    print("  the gram/1um regime is the mesoscopic-superposition frontier "
          "(same as gravitational-decoherence tests).")
    # -- optical gravimetry: rainbow / pond / thermal roughness --
    print("\n[GRAVIMETER-OPTICAL] no apparatus: capillary optics read g")
    for name, sig_, rho_, g_ in (("Earth rain (water)", 0.072, 1000.0, 9.81),
                                 ("Mars (water)", 0.072, 1000.0, 3.71),
                                 ("Titan (methane rain)", 0.017, 450.0, 1.352)):
        lc_ = np.sqrt(sig_ / (rho_ * g_))
        cmin = (4 * g_ * sig_ / rho_) ** 0.25
        print(f"  {name:20}: l_c = {lc_ * 1e3:.2f} mm (drop-flattening scale in the bow) ; "
              f"c_min = {cmin * 100:.1f} cm/s (slowest ripples)")
    print("  inversions: g = sigma/(rho l_c^2) [rainbow] ; g = rho c_min^4/(4 sigma) [pond] ;")
    print("  g = kB T/(rho A S0) [thermal surface roughness -- the entropic clock's equipartition,")
    print("  gravity as infrared cutoff: A(rho g + sigma k^2) S(k) = hbar omega_E].")
    print("  MOIRE readout: |e^{ik1x}+e^{ik2x}| = 2|cos(Dk x/2)| -- the envelope reads ONLY the")
    print("  difference, magnified by k/Dk; first null at Dk*x = pi (unit-free, pi = the log(a/b)")
    print("  of interference); dispersion difference-quotient (w1^2-w2^2)/(k1-k2) = g exactly on")
    print("  the gravity branch: mm ripples read as cm-scale moire fringes -> pond gravimetry at")
    print("  moire magnification ~ k/Dk ~ 10-100.")
    # classical-channel boundary (Mudawar ISS/FBCE flight anchor)
    D_t, rho_gv, drho_ = 7.24e-3, 14.0, 1569.0        # nPFH geometry/properties
    print("\n[CLASSICAL BOUNDARY] shear-vs-buoyancy (FBCE nPFH, D = 7.24 mm): J_g = xG/sqrt(g D rho_g drho)")
    for name, g_ in (("Earth", 9.81), ("Mars", 3.71), ("Moon", 1.62)):
        xG = np.sqrt(g_ * D_t * rho_gv * drho_)
        print(f"  {name:6}: gravity-blind for xG > {xG:.0f} kg/m^2s  (boundary scales as sqrt g)")
    print("  flight anchor: orientation spread ~35% at G=97 -> ~5% at G=194; g-free correlations")
    print("  transfer to mu-g at 7.1% MAE, g-dependent forms fail at up to 100% -- the classical")
    print("  validity condition for the equal-proper-physics hypothesis, measured.")

    w = max(len(r_[0]) for r_ in ROWS) + 2
    print("\n" + "=" * 104)
    print(f"{'quantity':<{w}}{'computed':>14}{'reference':>14}{'dev':>8}  reference source")
    print("-" * 104)
    for label, model, ref, dev, refsrc, note in ROWS:
        print(f"{label:<{w}}{model:>14.5g}{ref:>14.5g}{dev:>7.1f}%  {refsrc}")
        if note:
            print(f"{'':<{w}}  {note}")
    print("=" * 104)
    print("""Scope: Sr+ many-electron matrix elements (for the ion experiment's E1/E2 rungs)
need atomic many-body theory; percent-level g_p needs lattice QCD; both cited.
The QED rung is validated EXACTLY on hydrogen, the geometry is solved by SCF,
and g_p is derived from the SU(6) color-singlet structure -- no scaling-law
guesses remain in the NMR chain.""")


if __name__ == "__main__":
    main()

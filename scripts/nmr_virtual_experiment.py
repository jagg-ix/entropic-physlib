#!/usr/bin/env python3
"""Ab initio virtual NMR Mpemba experiment (Chatterjee et al., arXiv:2509.13451).

Models the experiment end-to-end in Python, each input from its proper theory:

  [QCHEM]  HF geometry optimization (pyscf + geomeTRIC) of the ACTUAL molecule,
           2-chloroacrylonitrile (CAN), gives the geminal H-H distance; the
           molecular volumes of CAN and DMSO are integrated from the SCF
           electron density (0.001 e/bohr^3 isodensity, Bader convention) --
           no tabulated geometry, no Bondi table.
  [QCD]    proton g-factor from the SU(6) color-singlet three-quark structure
           (g_p = 6; CODATA comparison run) -- the repo's ColorSingletBaryon
           content; percent-level needs lattice QCD (cited).
  [QED]    dipolar coupling b = (mu0/4pi) gamma_p^2 hbar / r^3 with
           gamma_p = g_p e/(2 m_p); Larmor omega0 = gamma_p B0; polarization
           eps = hbar omega0/(2 kB T) (the entropic-clock ratio).
  [BATH]   Gierer-Wirtz microviscosity x Stokes-Einstein-Debye from the
           COMPUTED radii; solvent viscosity eta(DMSO) is the one literature
           input (declared).
  [DYNAMICS] qutip mesolve of the dipolar-relaxation master equation in SI
           seconds: the experimental protocol (rho_n(theta) after PFG
           dephasing, and the unitarily prepared rho_f), trace-distance curves,
           the crossing, T1 from the simulated far-state decay.

Declared, not computed: eta(DMSO) (solvent hydrodynamics), the {5,6,15}/24
Redfield ladder (the paper's dipolar-relaxation result, standard theory), and
the chemical-shift difference Delta (does not enter the rate ladder; HF GIAO
error would exceed the 0.18 ppm target).

Run:  python3 scripts/nmr_virtual_experiment.py     (few minutes: 2 geomopts)
"""
import os
import sys
import numpy as np
import qutip as qt

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import physlib_mpemba as plm                     # the Lean-mirror library
from pyscf import gto, scf
from pyscf.dft import numint
from pyscf.geomopt.geometric_solver import optimize as geom_opt

hbar = 1.054571817e-34
e = 1.602176634e-19
mp = 1.67262192e-27
kB = 1.380649e-23
c = 2.99792458e8
eps0 = 8.8541878128e-12
BOHR = 0.529177210903

CAN_GUESS = """
C1  0.000  0.000  0.000
C2  1.330  0.000  0.000
H  -0.560  0.930  0.000
H  -0.560 -0.930  0.000
Cl  2.180  1.500  0.000
C3  2.100 -1.230  0.000
N   2.750 -2.230  0.000
"""
DMSO_GUESS = """
S   0.000  0.000  0.000
O   0.000  0.000  1.490
C1  1.640  0.000 -0.640
C2 -1.640  0.000 -0.640
H   2.190  0.890 -0.390
H   2.190 -0.890 -0.390
H   2.000  0.000 -1.660
H  -2.190  0.890 -0.390
H  -2.190 -0.890 -0.390
H  -2.000  0.000 -1.660
"""


def optimize_molecule(name, atom, basis="6-31g"):
    mol = gto.M(atom=atom, basis=basis, verbose=0)
    mf = scf.RHF(mol)
    mol_eq = geom_opt(mf, maxsteps=120)
    mf_eq = scf.RHF(mol_eq)
    E = mf_eq.kernel()
    print(f"[QCHEM] {name}: HF/{basis} optimized, E = {E:.6f} Ha")
    return mol_eq, mf_eq


def density_volume(mol, mf, iso=0.001, spacing=0.20):
    """Molecular volume (A^3) inside the iso e/bohr^3 density surface."""
    dm = mf.make_rdm1()
    xyz = mol.atom_coords()                                  # bohr
    lo, hi = xyz.min(axis=0) - 6.0, xyz.max(axis=0) + 6.0    # bohr margins
    axes = [np.arange(lo[k], hi[k], spacing / BOHR) for k in range(3)]
    G = np.stack(np.meshgrid(*axes, indexing="ij"), axis=-1).reshape(-1, 3)
    nvox = 0
    for chunk in np.array_split(G, max(1, len(G) // 200000)):
        ao = numint.eval_ao(mol, chunk)
        rho = numint.eval_rho(mol, ao, dm)
        nvox += int(np.count_nonzero(rho > iso))
    V = nvox * (spacing / BOHR) ** 3 * BOHR ** 3             # A^3
    a = (3 * V / (4 * np.pi)) ** (1 / 3)
    return V, a


def main():
    plm.selfcheck()                              # theorem-conformance gate
    print("[GATE] physlib_mpemba mirror passes all Lean theorem identities")
    # ---------------- QCHEM ----------------
    can, mf_can = optimize_molecule("2-chloroacrylonitrile", CAN_GUESS)
    xyz = can.atom_coords() * BOHR
    hs = [i for i in range(can.natm) if can.atom_symbol(i) == "H"]
    r_hh = np.linalg.norm(xyz[hs[0]] - xyz[hs[1]])
    V_can, a_can = density_volume(can, mf_can)
    dmso, mf_dmso = optimize_molecule("DMSO", DMSO_GUESS)
    V_dmso, a_dmso = density_volume(dmso, mf_dmso)
    print(f"[QCHEM] CAN geminal r_HH = {r_hh:.4f} A ; V = {V_can:.1f} A^3 -> a = {a_can:.2f} A")
    print(f"[QCHEM] DMSO V = {V_dmso:.1f} A^3 -> a = {a_dmso:.2f} A")
    me = 9.1093837015e-31
    alphaSI = e ** 2 / (4 * np.pi * eps0 * hbar * c)
    r_sub = plm.sp2GeminalDistance(plm.bohrRadius(me, c, hbar, alphaSI)) * 1e10
    print(f"[SUBSTRATE] sp2GeminalDistance(bohrRadius) = {r_sub:.4f} A "
          f"(QChem actual molecule: {r_hh:.4f} A)")

    # ---------------- BATH ----------------
    eta, T = 2.0e-3, 295.0                                   # eta: declared literature input
    rho_r = a_dmso / a_can
    tau_c = plm.bathCorrelationTime(rho_r, eta, a_can * 1e-10, kB * T)
    print(f"[BATH] bathCorrelationTime = giererWirtzFactor x stokesEinsteinDebye: "
          f"f = {plm.giererWirtzFactor(rho_r):.4f} ; tau_c = {tau_c * 1e12:.2f} ps")

    # ---------------- QCD + QED + DYNAMICS ----------------
    B0 = 11.7
    results = {}
    for tag, g_p in (("SU(6) QCD", 6.0), ("CODATA", 5.5856946893)):
        gam = plm.gyromagneticRatio(g_p, e, mp)
        b = plm.dipolarCoupling(eps0, c, gam, hbar, r_hh * 1e-10)
        om0 = gam * B0
        eps = plm.route_polarization(om0, kB, T, hbar)   # polarization_is_clock_ratio
        K0 = plm.dipolarRate(b, tau_c)
        # jump operators of the dipolar ladder (paper's Redfield result, cited)
        ket = [qt.basis(4, i) for i in range(4)]
        idx = {"00": 0, "01": 1, "10": 2, "11": 3}
        jumps = []
        for lo, hi in [("00", "01"), ("00", "10"), ("01", "11"), ("10", "11")]:
            jumps += [(K0 * (1 - eps) / 16, hi, lo), (K0 * (1 + eps) / 16, lo, hi)]
        jumps += [(K0 * (1 - 2 * eps) / 4, "11", "00"), (K0 * (1 + 2 * eps) / 4, "00", "11"),
                  (K0 / 24, "10", "01"), (K0 / 24, "01", "10")]
        c_ops = [np.sqrt(r) * ket[idx[x]] * ket[idx[y]].dag() for r, x, y in jumps]
        H = qt.qzero(4)
        rho_ss = qt.steadystate(H, c_ops)
        iz = {"00": (.5, .5), "01": (.5, -.5), "10": (-.5, .5), "11": (-.5, -.5)}
        th = np.deg2rad(70)
        keys = ["00", "01", "10", "11"]
        p_n = [0.25 + 2 * eps * (iz[k][0] + iz[k][1] * np.cos(2 * th)) / 4 for k in keys]
        p_f = [0.25 - eps * (iz[k][0] + iz[k][1]) / 2 for k in keys]
        ts = np.linspace(0, 30.0, 3001)                       # SI seconds, the paper's window
        D = {}
        for lbl, p in (("n", p_n), ("f", p_f)):
            states = qt.mesolve(H, qt.Qobj(np.diag(p)), ts, c_ops,
                                options={"atol": 1e-13, "rtol": 1e-11}).states
            D[lbl] = np.array([qt.tracedist(s, rho_ss) for s in states])
        diff = D["f"] - D["n"]
        ic = np.where(np.diff(np.sign(diff)) != 0)[0]
        t_cross = ts[ic[0]] if len(ic) else np.nan
        # T1 through the theorem (t1_is_fastest_mode), mesolve fit as cross-check
        T1_theorem = plm.route_T1(b, tau_c)
        mask = D["f"] > D["f"][0] * 1e-3
        slope = np.polyfit(ts[mask], np.log(D["f"][mask]), 1)[0]
        # mode amplitudes by eigendecomposition; crossing via dipolar_mpemba_crossing
        W = np.zeros((4, 4))
        for r_, x, y in jumps:
            W[idx[x], idx[y]] += r_
        for j in range(4):
            W[j, j] -= W[:, j].sum()
        w_, Vm = np.linalg.eig(W)
        Vi = np.linalg.inv(Vm)
        p_th = np.real(Vm[:, np.argmax(w_.real)]).copy()
        p_th /= p_th.sum()

        def amp(p0, target):
            cvec = Vi @ (np.array(p0) - p_th)
            n_ = int(np.argmin(np.abs(w_.real - target)))
            return np.abs((Vm[:, n_] * cvec[n_]).real).sum() / 2
        a_far = amp(p_f, -15 * K0 / 24)                  # far state, fast mode
        b_near = amp(p_n, -5 * K0 / 24)                  # near state, slow mode
        t_2mode = plm.route_dipolar_crossing_time(a_far, b_near, K0)
        results[tag] = (b, eps, K0, T1_theorem, t_cross, om0, t_2mode)
        print(f"[DYN {tag:9}] b/2pi = {b / 2 / np.pi / 1e3:.2f} kHz ; K0 = {K0:.4f}/s ; "
              f"T1(route_T1) = {T1_theorem:.2f} s (mesolve fit {-1 / slope:.2f}) ; "
              f"two-mode t* = {t_2mode:.2f} s ; crossing full = {t_cross:.2f} s ; eps = {eps:.2e}")

    # ---------------- comparison ----------------
    print("\n" + "=" * 88)
    print(f"{'observable':<34}{'SU(6) QCD':>14}{'CODATA g_p':>14}{'measured':>14}  source")
    print("-" * 88)
    rows = [("geminal r_HH (A)", f"{r_hh:.3f}", "", "~1.85", "sp2 geometry lit."),
            ("Larmor freq (MHz)", f"{results['SU(6) QCD'][5] / 2 / np.pi / 1e6:.0f}",
             f"{results['CODATA'][5] / 2 / np.pi / 1e6:.0f}", "500.02", "paper"),
            ("polarization eps", f"{results['SU(6) QCD'][1]:.1e}",
             f"{results['CODATA'][1]:.1e}", "~1e-5", "paper (order)"),
            ("T1 (s)", f"{results['SU(6) QCD'][3]:.2f}",
             f"{results['CODATA'][3]:.2f}", "5.7", "paper"),
            ("crossing, full curve (s)", f"{results['SU(6) QCD'][4]:.2f}",
             f"{results['CODATA'][4]:.2f}", "(early, unresolved)", "model"),
            ("crossing, two-mode t* (s)", f"{results['SU(6) QCD'][6]:.2f}",
             f"{results['CODATA'][6]:.2f}", "~5-12 (fig)", "paper Fig 3a")]
    for r in rows:
        print(f"{r[0]:<34}{r[1]:>14}{r[2]:>14}{r[3]:>14}  {r[4]}")
    print("=" * 88)
    print("Inputs: CODATA constants, SU(6)/CODATA g_p, HF geometry + density volumes "
          "(computed), eta(DMSO) literature.  Nothing fitted to the NMR data.")


if __name__ == "__main__":
    main()

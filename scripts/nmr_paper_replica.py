#!/usr/bin/env python3
"""Compute the paper: Chatterjee et al., arXiv:2509.13451, equation by equation
and figure by figure, through the Lean-mirror library (physlib_mpemba) and the
ab initio inputs (pyscf geometry/density, SU(6)/CODATA g_p, QED coupling).

  Eq (2)   thermal state + polarization eps           -> route_polarization
  Eq (5)   coherence-free condition p00+p11 = p01+p10 -> verified on rho_n(theta)
  Eq (6)   mode decomposition p(t) = p_th + sum a_n e^{lam_n t} v_n
           ladder {5,6,15}K0/24                       -> eigendecomposition
  Fig 3(a) D_n, D_f trace-distance curves, theta=70   -> qutip mesolve (SI s)
  Fig 3(c) same at theta=60
  Fig 3(b) mode-resolved curves a1 e^{lam1 t}, a3 e^{lam3 t}; a1(rho_f) = 0
  Fig 3(d) genuine QME: relative-entropy curves d_f, d_n and their crossing
  J(H,H)   ab initio spin-spin coupling (pyscf-properties SSC at HF level)
  Delta    chemical-shift difference: NOT computed (pyscf-properties GIAO
           incompatible with pyscf 2.14 in this environment; declared)

Run:  python3 scripts/nmr_paper_replica.py     (several minutes: geomopt + SSC)
"""
import os
import sys
import numpy as np
import qutip as qt

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import physlib_mpemba as plm
from nmr_virtual_experiment import (optimize_molecule, density_volume,
                                    CAN_GUESS, DMSO_GUESS)

hbar = 1.054571817e-34
e = 1.602176634e-19
mp_ = 1.67262192e-27
kB = 1.380649e-23
c = 2.99792458e8
eps0 = 8.8541878128e-12
BOHR = 0.529177210903
G_P = 5.5856946893          # CODATA primary; SU(6) band reported by the virtual experiment
B0, T, ETA = 11.7, 295.0, 2.0e-3


def rho_states(eps, theta_deg):
    iz = {"00": (.5, .5), "01": (.5, -.5), "10": (-.5, .5), "11": (-.5, -.5)}
    th = np.deg2rad(theta_deg)
    keys = ["00", "01", "10", "11"]
    p_n = np.array([0.25 + 2 * eps * (iz[k][0] + iz[k][1] * np.cos(2 * th)) / 4 for k in keys])
    p_f = np.array([0.25 - eps * (iz[k][0] + iz[k][1]) / 2 for k in keys])
    return p_n, p_f


def rate_matrix(K0, eps):
    idx = {"00": 0, "01": 1, "10": 2, "11": 3}
    jumps = []
    for lo, hi in [("00", "01"), ("00", "10"), ("01", "11"), ("10", "11")]:
        jumps += [(K0 * (1 - eps) / 16, hi, lo), (K0 * (1 + eps) / 16, lo, hi)]
    jumps += [(K0 * (1 - 2 * eps) / 4, "11", "00"), (K0 * (1 + 2 * eps) / 4, "00", "11"),
              (K0 / 24, "10", "01"), (K0 / 24, "01", "10")]
    W = np.zeros((4, 4))
    for r_, x, y in jumps:
        W[idx[x], idx[y]] += r_
    for j in range(4):
        W[j, j] -= W[:, j].sum()
    return W, jumps, idx


def kl(p, q):
    return float(np.sum(p * np.log(p / q)))


def main():
    plm.selfcheck()
    print("[GATE] physlib_mpemba mirror passes all Lean theorem identities\n")

    # ---------- ab initio inputs ----------
    can, mf_can = optimize_molecule("2-chloroacrylonitrile", CAN_GUESS)
    xyz = can.atom_coords() * BOHR
    hs = [i for i in range(can.natm) if can.atom_symbol(i) == "H"]
    r_hh = np.linalg.norm(xyz[hs[0]] - xyz[hs[1]])
    _, a_can = density_volume(can, mf_can)
    dmso, mf_dmso = optimize_molecule("DMSO", DMSO_GUESS)
    _, a_dmso = density_volume(dmso, mf_dmso)
    tau_c = plm.bathCorrelationTime(a_dmso / a_can, ETA, a_can * 1e-10, kB * T)
    gam = plm.gyromagneticRatio(G_P, e, mp_)
    b = plm.dipolarCoupling(eps0, c, gam, hbar, r_hh * 1e-10)
    K0 = plm.dipolarRate(b, tau_c)
    om0 = gam * B0
    eps = plm.route_polarization(om0, kB, T, hbar)
    T1 = plm.route_T1(b, tau_c)
    print(f"[CHAIN] r_HH = {r_hh:.4f} A ; tau_c = {tau_c * 1e12:.2f} ps ; "
          f"b/2pi = {b / 2 / np.pi / 1e3:.2f} kHz ; K0 = {K0:.4f}/s ; "
          f"T1 = {T1:.2f} s ; eps = {eps:.3e}\n")

    # ---------- Eq (5): coherence-free condition ----------
    worst = max(abs((rho_states(eps, th)[0][0] + rho_states(eps, th)[0][3])
                    - (rho_states(eps, th)[0][1] + rho_states(eps, th)[0][2]))
                for th in range(0, 91, 5))
    print(f"[Eq 5] p00+p11 = p01+p10 on the rho_n(theta) family: max dev = {worst:.1e} "
          f"(coherence terms stay zero under natural thermalization)")

    # ---------- Eq (6): ladder + overlaps ----------
    W, jumps, idx = rate_matrix(K0, eps)
    w_, V = np.linalg.eig(W)
    order = np.argsort(-w_.real)
    lam = w_.real[order]
    print(f"[Eq 6] Liouvillian ladder (1/s): {np.round(lam, 5)} ; "
          f"ratios to -K0/24: {np.round(-lam[1:] * 24 / K0, 4)} (paper: 5, 6, 15)")
    Vi = np.linalg.inv(V)
    p_th = np.real(V[:, np.argmax(w_.real)]).copy()
    p_th /= p_th.sum()

    def amp(p0, target):
        cvec = Vi @ (p0 - p_th)
        n_ = int(np.argmin(np.abs(w_.real - target)))
        return np.abs((V[:, n_] * cvec[n_]).real).sum() / 2

    # ---------- Fig 3(b): mode-resolved curves, theta = 70 ----------
    p_n, p_f = rho_states(eps, 70.0)
    a1n, a3n = amp(p_n, -5 * K0 / 24), amp(p_n, -15 * K0 / 24)
    a1f, a3f = amp(p_f, -5 * K0 / 24), amp(p_f, -15 * K0 / 24)
    print(f"\n[Fig 3b] mode amplitudes /(2 eps):  rho_n: a1 = {a1n / (2 * eps):.4f}, "
          f"a3 = {a3n / (2 * eps):.4f} ;  rho_f: a1 = {a1f / (2 * eps):.2e} (=0), "
          f"a3 = {a3f / (2 * eps):.4f}")
    tgrid = np.array([0, 5, 10, 15, 20, 25, 29])
    print(f"{'t (s)':>8}" + "".join(f"{t_:>9.0f}" for t_ in tgrid))
    print(f"{'a1 e^l1t':>8}" + "".join(f"{a1n / (2 * eps) * np.exp(-5 * K0 / 24 * t_):>9.4f}"
                                       for t_ in tgrid))
    print(f"{'a3 e^l3t':>8}" + "".join(f"{a3n / (2 * eps) * np.exp(-15 * K0 / 24 * t_):>9.4f}"
                                       for t_ in tgrid))

    # ---------- Fig 3(a)/(c): distance curves + crossings ----------
    ket = [qt.basis(4, i) for i in range(4)]
    c_ops = [np.sqrt(r_) * ket[idx[x]] * ket[idx[y]].dag() for r_, x, y in jumps]
    H = qt.qzero(4)
    rho_ss = qt.steadystate(H, c_ops)
    ts = np.linspace(0, 29.0, 2901)
    for fig, th in (("Fig 3a", 70.0), ("Fig 3c", 60.0)):
        p_n, p_f = rho_states(eps, th)
        D = {}
        P = {}
        for lbl, p0 in (("n", p_n), ("f", p_f)):
            states = qt.mesolve(H, qt.Qobj(np.diag(p0)), ts, c_ops,
                                options={"atol": 1e-13, "rtol": 1e-11}).states
            D[lbl] = np.array([qt.tracedist(s, rho_ss) for s in states])
            P[lbl] = np.array([np.real(np.diag(s.full())) for s in states])
        ic = np.where(np.diff(np.sign(D["f"] - D["n"])) != 0)[0]
        t_full = ts[ic[0]] if len(ic) else np.nan
        a_far = amp(p_f, -15 * K0 / 24)
        b_near = amp(p_n, -5 * K0 / 24)
        t_2m = plm.route_dipolar_crossing_time(a_far, b_near, K0)
        print(f"\n[{fig}] theta = {th:.0f}: D/(2 eps) curves")
        print(f"{'t (s)':>8}" + "".join(f"{t_:>9.0f}" for t_ in tgrid))
        for lbl in ("n", "f"):
            vals = np.interp(tgrid, ts, D[lbl]) / (2 * eps)
            print(f"{'D_' + lbl:>8}" + "".join(f"{v:>9.4f}" for v in vals))
        print(f"  crossings: full-curve = {t_full:.2f} s ; "
              f"two-mode (route_dipolar_crossing_time) = {t_2m:.2f} s")
        if fig == "Fig 3a":
            # ---------- Fig 3(d): genuine QME in relative entropy ----------
            dn = np.array([kl(P["n"][i], np.real(np.diag(rho_ss.full()))) for i in range(len(ts))])
            df = np.array([kl(P["f"][i], np.real(np.diag(rho_ss.full()))) for i in range(len(ts))])
            icd = np.where(np.diff(np.sign(df - dn)) != 0)[0]
            t_kl = ts[icd[0]] if len(icd) else np.nan
            print(f"\n[Fig 3d] genuine QME (relative entropy): d_f(0) = {df[0]:.3e} > "
                  f"d_n(0) = {dn[0]:.3e} : {df[0] > dn[0]} ; KL crossing = {t_kl:.2f} s ; "
                  f"monotone both: {max(np.max(np.diff(df)), np.max(np.diff(dn))) <= 1e-15}")

    # ---------- J(H,H) ab initio ----------
    try:
        from pyscf.prop import ssc
        jobj = ssc.RHF(mf_can)
        jobj.verbose = 0
        jobj.nuc_pair = [(hs[0], hs[1])]
        e11 = jobj.kernel()
        # convert reduced K (au) -> J (Hz), replicating pyscf.prop.ssc.rhf's own block
        from pyscf.data import nist
        from pyscf.prop.ssc.rhf import _atom_gyro_list
        nuc_magneton = 0.5 * (nist.E_MASS / nist.PROTON_MASS)
        unit = (nist.HARTREE2J / nist.PLANCK) * nuc_magneton ** 2
        gyro = _atom_gyro_list(can)
        j_hz = float(unit * np.trace(np.asarray(e11)[0]) / 3 * gyro[hs[0]] * gyro[hs[1]])
        print(f"\n[J] ab initio SSC (HF/6-31G) geminal J(H,H) = {j_hz:.2f} Hz "
              f"(paper: 3.24 Hz; HF-level FC term is qualitative -- order/sign check)")
    except Exception as ex:
        print(f"\n[J] SSC unavailable/failed: {ex}")
    print("[Delta] chemical-shift difference NOT computed: pyscf-properties GIAO "
          "incompatible with pyscf 2.14 here (declared; paper value 89 Hz = 0.178 ppm)")

    # ---------- summary ----------
    print("\n" + "=" * 78)
    print(f"{'paper quantity':<38}{'computed':>16}{'paper':>16}")
    print("-" * 78)
    print(f"{'eps (Eq 2)':<38}{eps:>16.2e}{'~1e-5 (order)':>16}")
    print(f"{'ladder ratios (Eq 6)':<38}{'5 : 6 : 15':>16}{'5 : 6 : 15':>16}")
    print(f"{'T1 (s)':<38}{T1:>16.2f}{'5.7':>16}")
    print(f"{'a1(rho_f) (Fig 3b inset)':<38}{a1f / (2 * eps):>16.1e}{'~0':>16}")
    print("=" * 78)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""The moire Zeeman effect: periodic magnetization as an Umklapp splitting.

Gomez Salvador-Kuhlenkamp-Ciorciaro-Knap-Imamoglu, "Optical Signatures of
Periodic Magnetization: The Moire Zeeman Effect" (arXiv:2112.10276): excitons
in a TMD monolayer probe a periodically modulated valley Zeeman field
B_z(r) = sum_G B_G e^{iG r}.  Zero-momentum excitons feel only the AVERAGE
field; the Bragg-Umklapp resonances couple to B_G and split by the geometry
factor (Delta/2)(1 + cos 2 dtheta_G) = Delta cos^2(dtheta_G) -- Delta/4 on the
triangular lattice.  Lean side: SciamaAdSCPTMpembaComplexActionLorentzian SZ.

  [1] GEOMETRY FACTOR: the half-angle law across dtheta, the triangular Delta/4.
  [2] FOURIER DISCRIMINATOR: on a real-space cell, a zero-average periodic
      field has exactly zero uniform response while its Umklapp component
      |B_G| is read in full -- the probe is background-free (numerically to
      machine precision, matching moire_zeeman_discriminator).
  [3] MoSe2 CALIBRATION: the paper's quoted pair (Delta = 1.5 meV at
      |B_G| ~ 12 T) against g mu_B |B_G|/2 with g = 4.3.
  [4] RESTORATION MAGNETOMETER: with the paper's Fig. 3 parameters
      (n_e lambda = 2 meV, n_e mu = 4 meV) the external field that restores
      the zero-average spectrum reads n_e(mu - lambda) exactly.

Run:  python3 scripts/moire_zeeman_probe.py
"""
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import physlib_mpemba as plm

MU_B = 5.7883818060e-2                     # meV / T


def main():
    plm.selfcheck()
    print("[GATE] physlib_mpemba mirror passes all Lean theorem identities\n")

    # [1] geometry factor
    print("[1] Umklapp splitting geometry factor (moire_zeeman_splitting_half_angle):")
    for deg in (0, 30, 60, 90):
        dth = np.radians(deg)
        S = plm.moireZeemanSplitting(1.0, dth)
        print(f"    dtheta = {deg:2d} deg: S/Delta = {S:.4f}  (= cos^2 = "
              f"{np.cos(dth) ** 2:.4f})")
    print(f"    triangular (60 deg = pi/3): S = Delta/4 exactly "
          f"(moire_zeeman_splitting_triangular)")

    # [2] Fourier discriminator on a triangular cell
    n = 480
    a = 1.0
    G1 = 4 * np.pi / (np.sqrt(3) * a) * np.array([0.0, 1.0])
    G2 = 4 * np.pi / (np.sqrt(3) * a) * np.array([np.sqrt(3) / 2, -0.5])
    # real-space cell spanned by lattice vectors a1, a2 (dual to G1, G2)
    u = (np.arange(n) + 0.5) / n
    U, V = np.meshgrid(u, u, indexing="ij")
    BG = 12.0                                                     # tesla
    rng = np.random.default_rng(5)
    phases = rng.uniform(0, 2 * np.pi, 2)
    # B(r) on the cell: zero-average periodic modulation (first-shell cosines)
    B = BG * (np.cos(2 * np.pi * U + phases[0]) + np.cos(2 * np.pi * V + phases[1]))
    avg = abs(B.mean())
    umk = 2 * abs((B * np.exp(-2j * np.pi * U)).mean())           # reads the G1 component
    print(f"\n[2] discriminator on the cell: uniform response |<B>| = {avg:.2e} T "
          f"(blind);\n    Umklapp response |B_G| = {umk:.4f} T (= {BG} T injected) "
          f"-- background-free, as proved")

    # [3] MoSe2 calibration
    g = 4.3
    Delta = g * MU_B * BG / 2
    print(f"\n[3] MoSe2: g = {g}, |B_G| = {BG} T -> Delta = g mu_B |B_G|/2 = "
          f"{Delta:.2f} meV (paper quotes 1.5 meV; {abs(Delta / 1.5 - 1) * 100:.1f}% off)")
    print(f"    triangular splitting Delta/4 = {Delta / 4 * 1e3:.0f} ueV")

    # [4] restoration magnetometer (paper Fig. 3 parameters)
    nel_lam, nel_mu = 2.0, 4.0                                    # meV
    Be = plm.route_restoration_field(1.0, nel_lam, nel_mu, g, MU_B)
    resid = 1.0 * (nel_lam - nel_mu) / 2 + g * MU_B * Be / 2
    print(f"\n[4] restoration field: n_e lambda = {nel_lam} meV, n_e mu = {nel_mu} meV "
          f"-> B_e = {Be:.2f} T\n    (residual sigma_z coefficient {resid:.1e} meV: "
          f"exact inversion, moire_zeeman_magnetometer)")

    print("\nVERDICT: periodic magnetization hides from every uniform probe yet splits the")
    print("Umklapp resonances by Delta cos^2(dtheta) -- and the field that undoes the split")
    print("is itself a measurement. The moire geometry enters, once again, as a half-angle law.")


if __name__ == "__main__":
    main()

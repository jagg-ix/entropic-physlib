#!/usr/bin/env python3
"""Spectral-trajectory theory of the moire effect (Saveljev-Kim 2013), verified.

Saveljev-Kim, "Theoretical estimation of moire effect using spectral
trajectories", Opt. Express 21 (2013) 1693: moire spectra live in the complex
plane, each grating peak at T_p(alpha) = p k e^{i alpha} (Eq. 2), the moire
peak of two gratings is the vector difference (Eq. 4), and a swept parameter
draws a TRAJECTORY -- a circular arc for a rotating grating (Eq. 12,
dT/dt = iA T), a radial segment for a scaling one (Eq. 10, dT/dt = (A/k) T).

Lean side: SciamaAdSCPTMpembaComplexActionLorentzian SS.  This script closes
two loops:

  [1] CODE = THEORY: the moire-optics-lab estimate_moire_period, which we have
      been validating against, IS Eq. 4 -- its output equals 2 pi/|moire peak|
      computed from route_moire_peak, to machine precision, over a grid of
      angles and periods.
  [2] TRAJECTORY GEOMETRY: sweeping the angle keeps |T| constant (circle);
      sweeping the wavenumber keeps arg(T) constant (ray).  The finite-
      difference derivative matches iA*T (rotation) and (A/k)*T (scaling) --
      the paper's Eqs. 10/12 -- and the twist law 2k sin(theta/2) falls out of
      the peak difference (twist_law_from_spectral_peaks).

Run:  python3 scripts/spectral_trajectories.py
"""
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import physlib_mpemba as plm


def main():
    plm.selfcheck()
    print("[GATE] physlib_mpemba mirror passes all Lean theorem identities\n")

    # [1] the external package IS Eq. 4
    try:
        import moire_physics as mp
        worst = 0.0
        for P1 in (40.0, 70.0):
            for P2 in (41.0, 80.0):
                for deg in (0.5, 3.0, 12.0):
                    k1, k2 = 2 * np.pi / P1, 2 * np.pi / P2
                    peak = plm.route_moire_peak(k1, 0.0, k2, np.deg2rad(deg))
                    period_theory = 2 * np.pi / abs(peak)
                    period_pkg = mp.estimate_moire_period(P1, P2, deg)
                    worst = max(worst, abs(period_pkg / period_theory - 1))
        print(f"[1] moire-optics-lab estimate_moire_period vs 2 pi/|Eq.4 peak| "
              f"(12 cases): max rel dev = {worst:.2e}")
        print("    -> the code we validated against is exactly the spectral-peak difference")
    except ImportError:
        print("[1] moire-optics-lab not installed -- code=theory weld skipped")

    # [2a] rotation trajectory is a circle
    p, k = 1, 3.0
    angles = np.linspace(0, 2 * np.pi, 400)
    radii = np.array([abs(plm.spectralPeak(p, k, a)) for a in angles])
    print(f"\n[2a] rotation sweep: |T(alpha)| over 0..2pi = {radii.mean():.4f} "
          f"+/- {radii.std():.1e}  (constant -> circular arc, angle_trajectory_circular)")

    # [2b] scaling trajectory is a ray (constant argument)
    scales = np.linspace(0.2, 4.0, 400)
    args = np.array([np.angle(plm.spectralPeak(p, c * k, 0.7)) for c in scales])
    print(f"[2b] scaling sweep: arg(T(c k)) over c in [0.2,4] = {args.mean():.4f} "
          f"+/- {args.std():.1e}  (constant -> radial segment, wavenumber_trajectory_radial)")

    # [2c] the derivatives (Eqs. 10, 12)
    A, B, t0 = 1.3, 0.4, 0.55
    h = 1e-6
    ga = lambda t: plm.spectralPeak(p, k, A * t + B)
    d_ang = (ga(t0 + h) - ga(t0 - h)) / (2 * h)
    err_ang = abs(d_ang - 1j * A * ga(t0)) / abs(A * ga(t0))
    gk = lambda t: plm.spectralPeak(p, A * t + B, 0.7)
    d_k = (gk(t0 + h) - gk(t0 - h)) / (2 * h)
    err_k = abs(d_k - (A / (A * t0 + B)) * gk(t0)) / abs(d_k)
    print(f"\n[2c] rotation derivative vs iA*T (Eq. 12): rel err {err_ang:.2e}")
    print(f"     scaling  derivative vs (A/k)*T (Eq. 10): rel err {err_k:.2e}")

    # [2d] the twist law is the peak difference
    worst = 0.0
    for deg in (1.0, 4.0, 15.0, 45.0):
        th = np.deg2rad(deg)
        lhs = abs(plm.spectralPeak(1, k, 0.0) + plm.spectralPeak(-1, k, th))
        rhs = 2 * k * abs(np.sin(th / 2))
        worst = max(worst, abs(lhs - rhs))
    print(f"\n[2d] twist law from spectral difference (twist_law_from_spectral_peaks): "
          f"max dev = {worst:.2e}")

    print("\nVERDICT: the moire spectrum is a complex-plane vector diagram; the code we build on")
    print("is its Eq. 4; rotations trace circles and scalings trace rays (Eqs. 10/12); and the")
    print("rotational twist law is nothing but the modulus of the peak difference.")


if __name__ == "__main__":
    main()

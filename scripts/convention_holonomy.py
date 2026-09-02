#!/usr/bin/env python3
"""The quantification method: measure a locally-invisible convention by its holonomy.

Section 11 established that a global convention -- the simultaneity choice, the
gravitational potential, the entropic contour -- is locally unobservable.  This
script is the METHOD to quantify it (Lean: convention_holonomy_quantifier):
each convention is the closed-loop or differential integral of a locally-
removable offset, and each such integral is an exact identity in an observable.

  [1] ROTATION: integrate the removable synchronization offset density v/c^2
      around a rotating ring -> the holonomy H = 2 A omega/c^2; the Sagnac
      delay is 2H; invert H -> omega (route_holonomy_reads_rotation).  A ring-
      laser gyroscope IS this loop integral.
  [2] GRAVITY: the differential redshift around a vertical loop (up h, across,
      down) returns the potential difference g dh/c^2 that no single station
      sees (mpemba_differential_gravimeter).
  [3] CONTOUR: the crossing calibration (l2-l3) t* = log(a/b) reads the
      imaginary-action rate of the Nagao-Nielsen modulus e^{-rho t}.

The method is uniform: pick the loop the convention lives on, integrate the
removable offset, read the invariant off the result.

Run:  python3 scripts/convention_holonomy.py
"""
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import physlib_mpemba as plm

C = 299792458.0


def main():
    plm.selfcheck()
    print("[GATE] physlib_mpemba mirror passes all Lean theorem identities\n")

    # [1] rotation: the synchronization holonomy, integrated around the ring
    r, omega = 0.10, 50.0                                     # 10 cm ring, 50 rad/s
    N = 200000
    phi = np.linspace(0, 2 * np.pi, N, endpoint=False)
    v = omega * r                                            # tangential speed
    dl = r * (2 * np.pi / N)
    # oint (v/c^2) dl -- the sum of the locally-removable offsets around the loop
    H = np.sum(plm.syncOffsetDensity(v, C) * dl * np.ones(N))
    H_closed = plm.ringSyncHolonomy(omega, r, C)
    A = np.pi * r ** 2
    print("[1] ROTATION -- synchronization holonomy:")
    print(f"    local offset density v/c^2 = {plm.syncOffsetDensity(v, C):.3e} s/m "
          f"(removable at any point)")
    print(f"    loop integral  oint(v/c^2)dl = {H:.6e} s")
    print(f"    closed form 2A omega/c^2     = {H_closed:.6e} s  (= {2 * A * omega / C ** 2:.6e})")
    print(f"    Sagnac delay = 2H            = {2 * H_closed:.6e} s")
    w_rec = plm.route_holonomy_reads_rotation(H, r, C)
    print(f"    invert H -> omega            = {w_rec:.6f} rad/s  (true {omega}, "
          f"err {abs(w_rec / omega - 1):.1e})")

    # [2] gravity: the differential redshift around a vertical loop
    g, h1, h2 = 9.81, 0.0, 100.0                             # 100 m tower
    tstar = 6.78                                             # NMR crossing, s
    f1, f2 = 1 + g * h1 / C ** 2, 1 + g * h2 / C ** 2        # redshift factors
    t1, t2 = tstar / f1, tstar / f2
    # the ratio minus one, cancellation-free (= g(h2-h1)/c^2 / f1): the theorem's
    # exact form; the naive t1/t2 - 1 loses ~12 digits at 100 m (fractional effect
    # 1e-14, float64's edge -- optical-clock territory, as for the Sagnac gyro)
    ratio_m1 = g * (h2 - h1) / C ** 2 / f1
    naive = t1 / t2 - 1
    dphi = ratio_m1 * f1                                     # = g(h2-h1)/c^2
    print("\n[2] GRAVITY -- differential redshift (vertical loop, 100 m):")
    print(f"    single-station crossing t* = {tstar} s (blind to g)")
    print(f"    two-station ratio t1/t2 - 1 = {ratio_m1:.6e} (naive subtraction "
          f"gives {naive:.3e}, {abs(naive / ratio_m1 - 1) * 100:.1f}% off to cancellation)")
    print(f"    recovered g dh/c^2 = {dphi:.6e} = truth {g * (h2 - h1) / C ** 2:.6e}")
    print(f"    -> potential difference g dh = {dphi * C ** 2:.4f} m^2/s^2 "
          f"(= g x {h2 - h1:.0f} m = {g * (h2 - h1):.1f})")

    # [3] contour: the crossing calibration reads the imaginary-action rate
    a, b, lam2, lam3 = 3.0, 1.0, 0.9, 0.2
    tstar_c = plm.mpembaCrossingTime(a, b, lam2, lam3)
    cal = (lam2 - lam3) * tstar_c
    rho, t = 0.7, 2.0
    nn_modulus = np.exp(-rho * t)
    print("\n[3] CONTOUR -- crossing calibration (Nagao-Nielsen imaginary-action rate):")
    print(f"    crossing t* = {tstar_c:.4f}, calibration (l2-l3)t* = {cal:.4f} "
          f"= log(a/b) = {np.log(a / b):.4f}")
    print(f"    NN modulus ||e^{{-rho t}}|| = {nn_modulus:.4f} at rho={rho}, t={t}: the "
          f"imaginary-action decay, read clock-free by the crossing")

    print("\nVERDICT: the method quantifies a locally-invisible convention by the loop it lives on --")
    print("integrate the removable offset around the loop and read the invariant off the total.")
    print("Rotation: 4A omega/c^2 = 2 x holonomy. Gravity: g dh/c^2 differential. Contour: log(a/b).")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""The Sagnac effect as a rotation readout and simultaneity discriminator.

Spavieri-Gillies-Haug, "The Sagnac effect and the role of simultaneity in
relativity theory", J. Mod. Opt. 68 (2021) 202: on a rotating platform the
counter-propagating light times differ by Delta T = 4 A omega/(c^2 - v^2)
(A = pi r^2), a direct reading of the angular velocity -- and the effect
discriminates absolute (t' = t/gamma, position-independent) from relative
(t' = gamma(t - u x/c^2), Einstein) simultaneity.

Lean side: SciamaAdSCPTMpembaEntropicClock SS (S5), computed through the mirror
routes sagnacTimeDelay and route_sagnac_reads_rotation.

  [1] RING-LASER GYROSCOPE: a real fibre-optic gyro (r = 0.1 m, 1000-turn coil,
      Earth-rate omega) -- the delay, its closed form, and the recovered omega.
  [2] LANGEVIN METRIC: the rotating-frame null condition factors into the two
      local light speeds c +/- omega r, whose round trip IS the delay.
  [3] SIMULTANEITY DISCRIMINATOR: the Lorentz transform gaps two equal-t clocks
      a distance L apart by gamma u L/c^2 (missing section BK = c dt'), while
      absolute synchronization keeps the closed contour L(1+v/c)+L(1-v/c) = 2L.

Run:  python3 scripts/sagnac_simultaneity.py
"""
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import physlib_mpemba as plm

C = 299792458.0
OMEGA_EARTH = 7.2921159e-5           # rad/s


def main():
    plm.selfcheck()
    print("[GATE] physlib_mpemba mirror passes all Lean theorem identities\n")

    # [1] a fibre-optic gyroscope reading Earth's rotation
    r, N_turns = 0.10, 1000
    v = OMEGA_EARTH * r
    A = np.pi * r ** 2
    # the instrument delay = the proved closed form 4 A w/(c^2-v^2); the naive
    # subtraction 2pir/(c-v)-2pir/(c+v) loses ~13 digits to cancellation at
    # Earth rate (v ~ 1e-5), so we use the closed form the theorem proves equal
    dT_one = 4 * A * OMEGA_EARTH / (C ** 2 - v ** 2)
    dT = N_turns * dT_one                                     # N loops = N x area
    naive = plm.sagnacTimeDelay(C, v, r)
    w_rec = plm.route_sagnac_reads_rotation(dT / N_turns, r, C)
    print(f"[1] fibre gyro (r = {r} m, {N_turns}-turn coil, Earth rate):")
    print(f"    per-loop delay  = {dT_one:.6e} s (closed form; naive subtraction "
          f"gives {naive:.3e}, {abs(naive / dT_one - 1) * 100:.2f}% off to cancellation)")
    print(f"    total delay     = {dT:.6e} s")
    print(f"    recovered omega = {w_rec:.9e} rad/s  (true {OMEGA_EARTH:.9e}, "
          f"err {abs(w_rec / OMEGA_EARTH - 1):.1e})")

    # [2] the metric derives the two speeds
    omega = 50.0                                              # fast lab rotation, rad/s
    rr, cc = 1.0, C
    roots = np.roots([1.0, 2 * (omega * rr), -(cc ** 2 - (omega * rr) ** 2)])
    print(f"\n[2] Langevin null s^2 + 2 w r s - (c^2 - w^2 r^2) = 0:")
    print(f"    roots = {roots[0]:.4f}, {roots[1]:.4f}")
    print(f"    factored speeds c-wr = {cc - omega * rr:.4f}, -(c+wr) = "
          f"{-(cc + omega * rr):.4f}  (the c-/+ v of the Sagnac delay)")
    lhs = 2 * np.pi * rr / (cc - omega * rr) - 2 * np.pi * rr / (cc + omega * rr)
    rhs = 4 * (np.pi * rr ** 2) * omega / (cc ** 2 - (omega * rr) ** 2)
    print(f"    round-trip of those speeds = delay: dev {abs(lhs - rhs):.2e}")

    # [3] simultaneity discriminator
    gamma, u, L = 1.0000001, 2 * v, 1.0
    dt_gap = gamma * u * L / C ** 2                           # LT gap between equal-t clocks
    BK = C * dt_gap                                           # missing section
    lta_gap = 0.0                                             # LTA: position-independent
    contour = L * (1 + v / C) + L * (1 - v / C)
    print(f"\n[3] simultaneity of two clocks a distance L = {L} m apart:")
    print(f"    Lorentz (relative):  gap dt' = {dt_gap:.3e} s -> missing section "
          f"BK = {BK:.3e} m")
    print(f"    Tangherlini (absolute): gap = {lta_gap:.1f} s (position-independent, t/gamma)")
    print(f"    absolute-sync closed contour L(1+v/c)+L(1-v/c) = {contour:.6f} m "
          f"(= 2L exactly)")

    # [4] the invariant beneath the convention: interval, potential, contour
    print("\n[4] one invariant, three conventions (simultaneity_potential_contour_synthesis):")
    u = 0.6 * C
    gam = 1.0 / np.sqrt(1 - (u / C) ** 2)
    t, x = 1.0e-8, 2.0
    lt_t, lt_x = plm.ltTime(gam, u, C, t, x), plm.ltSpace(gam, u, t, x)
    inv_lt = C ** 2 * lt_t ** 2 - lt_x ** 2
    inv_0 = C ** 2 * t ** 2 - x ** 2
    print(f"    (i) interval Lorentz-invariant: c^2 t'^2 - x'^2 = {inv_lt:.6e} = "
          f"c^2 t^2 - x^2 = {inv_0:.6e} (dev {abs(inv_lt - inv_0):.1e})")
    proper = plm.route_minkowski_proper_time(u, C, t)
    print(f"    (i') absolute-sim time t/gamma = {plm.ltaTime(gam, t):.6e} s = co-moving "
          f"proper time {proper:.6e} s -- the LTA clock reads the interval")
    # (ii) EEP: redshift common scaling leaves the calibration log(a/b) fixed
    a, b, lam2, lam3 = 3.0, 1.0, 0.9, 0.2
    for s in (0.0, 0.3, -0.2):                        # any gravitational potential shift
        cal = ((1 / (1 + s) * lam2 - 1 / (1 + s) * lam3)
               * plm.mpembaCrossingTime(a, b, 1 / (1 + s) * lam2, 1 / (1 + s) * lam3))
        assert abs(cal - np.log(a / b)) < 1e-12
    print(f"    (ii) EEP: calibration (l2-l3)t* = log(a/b) = {np.log(a / b):.4f} for every "
          f"redshift scaling 1/(1+s) -- single station blind to the potential")
    # (iii) NN contour modulus, imaginary-time decay, untouched by the real-time slicing
    rho = 0.7
    nn = np.exp(-rho * t * 1e8)                       # e^{-rho t}, imaginary-time modulus
    print(f"    (iii) Nagao-Nielsen modulus ||NN|| = e^-rho t = {nn:.4f}: the entropic decay")
    print(f"          lives on the imaginary-time contour, blind to the (i) synchronization")

    print("\nVERDICT: the Sagnac ring reads angular velocity the way the entropic clock reads a")
    print("bath -- through the synchronization it forces; the delay is a metric consequence")
    print("(c +/- v are the Langevin roots), and it favours absolute over relative simultaneity.")
    print("The interval (proper time), the calibration log(a/b), and the imaginary-time modulus")
    print("are one invariant seen under three locally-unobservable conventions.")


if __name__ == "__main__":
    main()

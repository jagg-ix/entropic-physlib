#!/usr/bin/env python3
"""The differential-channel signal model: the arc's observables as USB-style deltas.

Every recovery in this arc is a two-input difference in which the shared part
cancels -- the structure a USB / LVDS / RS-485 pair uses to carry data as
V+ - V- and reject common-mode noise.  The convention that is locally
unobservable (S11) is the common-mode; the differential channel rejects it and
the difference is the data.

Lean side: SciamaAdSCPTMpembaNewtonObstructionHerglotz S13, computed through the
mirror routes differentialChannel / logDifferentialChannel / route_mismatch_leakage.

  [1] COMMON-MODE REJECTION: carry a physical signal (a Sagnac rotation rate) on
      a two-wire differential pair, inject a large shared drift + noise on BOTH
      lines, and show the difference recovers the signal untouched.
  [2] CMRR: introduce a gain mismatch between the two channels; the common-mode
      now leaks into the output proportionally to the mismatch -- quantified in dB,
      exactly the common-mode rejection ratio of a real differential receiver.
  [3] THE FOUR INSTANCES: Sagnac delay, moire beat, self-calibration, and the
      differential gravimeter, each written as one differential-channel node,
      with the common-mode it rejects named.

Run:  python3 scripts/differential_signal_model.py
"""
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import physlib_mpemba as plm

C = 299792458.0
rng = np.random.default_rng(5)


def main():
    plm.selfcheck()
    print("[GATE] physlib_mpemba mirror passes all Lean theorem identities\n")

    # [1] carry a Sagnac rotation rate over a differential pair with common-mode junk
    N = 4000
    A_eff, r = 5.0e3, 0.05
    omega = 3.0 + 0.5 * np.sin(np.linspace(0, 6, N))          # the signal: a varying rate
    # encode as the two counter-propagating flight-time excursions (the differential lines):
    # line+ carries +dT/2, line- carries -dT/2 about a huge common-mode round-trip time
    dT = 4 * A_eff * omega / C ** 2
    T_roundtrip = 2 * np.pi * r / C                           # common-mode (~1 ns), shared
    drift = 50e-9 * np.cumsum(rng.standard_normal(N)) / np.sqrt(N)   # slow shared drift
    noise = 20e-9 * rng.standard_normal(N)                    # shared pickup noise
    line_plus = T_roundtrip / 2 + dT / 2 + drift + noise      # both lines see the same
    line_minus = T_roundtrip / 2 - dT / 2 + drift + noise     # common-mode junk
    recovered_dT = plm.differentialChannel(line_plus, line_minus)   # D+ - D-
    omega_rec = plm.route_ring_delay_omega(recovered_dT, A_eff, C)
    cm_amplitude = np.std(drift + noise)
    print("[1] common-mode rejection (Sagnac rate on a differential pair):")
    print(f"    common-mode junk on both lines: {cm_amplitude * 1e9:.1f} ns "
          f"(>> signal dT ~ {np.abs(dT).max() * 1e12:.2f} ps)")
    print(f"    differential output recovers omega to "
          f"{np.abs(omega_rec - omega).max():.1e} rad/s -- junk fully rejected")

    # [2] CMRR: mismatch the two channel gains
    print("\n[2] CMRR (channel gain mismatch leaks the common-mode):")
    print("    mismatch eps     CMRR (dB)     leaked rate error")
    xcm = cm_amplitude                                        # representative common-mode level
    for eps in (1e-2, 1e-4, 1e-6):
        # line gains 1 and 1+eps; common-mode leakage = (g1-g2) xcm = -eps xcm
        leak = plm.route_mismatch_leakage(1.0, 1.0 + eps, xcm)
        cmrr_db = 20 * np.log10(1.0 / eps)                    # diff gain 1 / common gain eps
        leak_omega = plm.route_ring_delay_omega(abs(leak), A_eff, C)
        print(f"    {eps:.0e}        {cmrr_db:6.1f}        {leak_omega:.3e} rad/s")
    print("    -> perfectly matched channels (eps=0) reject the common-mode exactly "
          "(infinite CMRR)")

    # [3] the four instances as one node each
    print("\n[3] the arc's observables as differential-channel nodes:")
    c, v, rr = 10.0, 2.0, 1.0
    sag = plm.differentialChannel(2 * np.pi * rr / (c - v), 2 * np.pi * rr / (c + v))
    print(f"    Sagnac delay   D(2pir/(c-v), 2pir/(c+v)) = {sag:.4f}   "
          f"[common-mode: round-trip time]")
    k1, k2 = 105.0, 100.0
    print(f"    moire beat     D(k1, k2) = {plm.differentialChannel(k1, k2):.1f} rad/m   "
          f"[common-mode: carrier {(k1 + k2) / 2:.1f}]")
    a, b = 3.0, 1.0
    print(f"    self-calib     D_log(a, b) = log(a/b) = {plm.logDifferentialChannel(a, b):.4f}   "
          f"[common-mode: absolute anchor nu0 (multiplicative)]")
    g, h1, h2 = 9.81, 0.0, 100.0
    grav = plm.differentialChannel(g * h2 / C ** 2, g * h1 / C ** 2)
    print(f"    gravimeter     D(g h2/c^2, g h1/c^2) = {grav:.3e}   "
          f"[common-mode: proper crossing t*]")

    print("\nVERDICT: the convention that is locally unobservable is the common-mode; a differential")
    print("channel rejects it and the difference is the data -- Sagnac ΔT, moire Δk, self-calibration")
    print("log(a/b), the redshift Δ(gh/c²). Matched channels reject perfectly; mismatch sets the CMRR.")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Quantizing entropic time: the Matsubara ladder set by temperature.

Entropic time is imaginary modular (Euclidean) time -- and the KMS condition makes
it COMPACT: periodic with circumference hbar/(kB T) = 1/omega_E (the Connes-Rovelli
thermal time, one entropic tick).  A compact time coordinate quantizes like an
angle: its conjugate spectrum is DISCRETE, the Matsubara ladder

    omega_n = 2 pi n / period = 2 pi n * omega_E,   n in Z, omega_E = kB T/hbar

integer multiples of the entropic clock rate.  Lean side:
SciamaAdSCPTMpembaEntropicClock S10 (built on the repo's MatsubaraThermalOscillator).

  [1] THE QUANTUM: the entropic-time period and level spacing at real temperatures;
      the ladder omega_n through the Lean-mirror route.
  [2] TEMPERATURE SETS THE QUANTUM: hotter -> coarser ladder (spacing ~ T), the
      Planckian time hbar/(kB T) as the tick.
  [3] DISCRETENESS: the spectrum is a rigid, faithful copy of Z (no degeneracy).

Run:  python3 scripts/entropic_time_quantization.py
"""
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import physlib_mpemba as plm

KB = 1.380649e-23        # J/K
HBAR = 1.054571817e-34   # J s


def main():
    plm.selfcheck()
    print("[GATE] physlib_mpemba mirror passes all Lean theorem identities\n")

    # [1] the quantum of entropic time at real temperatures
    print("[1] the entropic-time quantum (period = hbar/kB T = 1/omega_E, one tick):")
    for T, name in ((300.0, "room 300 K"), (4.2, "liquid He 4.2 K"), (0.01, "dilution 10 mK")):
        omega_E = KB * T / HBAR
        period = plm.entropicTimePeriod(KB, T, HBAR)
        spacing = 2 * np.pi * omega_E
        print(f"    {name:16s}: omega_E = {omega_E:.3e} rad/s, tick = {period * 1e15:.2f} fs, "
              f"ladder spacing 2 pi omega_E = {spacing:.3e} rad/s")
    print(f"    (room-temperature tick hbar/kB T = 25 fs is the Planckian dissipation time)")

    # the ladder omega_n = 2 pi n omega_E through the mirror
    T = 300.0
    period = plm.entropicTimePeriod(KB, T, HBAR)
    print(f"\n    Matsubara ladder at 300 K (omega_n = 2 pi n omega_E):")
    for n in (-2, -1, 0, 1, 2):
        wn = plm.matsubaraFreqBoson(period, n)
        wn_route = plm.route_entropic_ladder(KB, T, HBAR, n)
        print(f"      n = {n:+d}: omega_n = {wn:+.3e} rad/s  (route {wn_route:+.3e}, "
              f"dev {abs(wn - wn_route):.1e})")

    # [2] temperature sets the quantum: spacing scales linearly with T
    print("\n[2] temperature sets the quantum (spacing 2 pi omega_E ~ T):")
    Ts = np.array([100.0, 200.0, 400.0])
    spacings = 2 * np.pi * KB * Ts / HBAR
    for Ti, si in zip(Ts, spacings):
        print(f"    T = {Ti:5.0f} K -> spacing {si:.3e} rad/s")
    print(f"    ratio spacing(400K)/spacing(100K) = {spacings[-1] / spacings[0]:.1f} "
          f"= T ratio {Ts[-1] / Ts[0]:.1f}  (hotter = coarser ladder)")

    # [3] discreteness: the spectrum is a faithful copy of Z
    ns = np.arange(-50, 51)
    freqs = plm.matsubaraFreqBoson(period, ns)
    unique = len(np.unique(np.round(freqs, 6)))
    print(f"\n[3] discreteness: 101 integer modes -> {unique} distinct frequencies "
          f"(faithful copy of Z, no degeneracy); zero mode omega_0 = "
          f"{plm.matsubaraFreqBoson(period, 0):.1e} (static/DC)")

    print("\nVERDICT: entropic time is quantized -- imaginary modular time is compact (KMS-periodic,")
    print("period hbar/kB T), so its conjugate is the discrete Matsubara ladder omega_n = 2 pi n omega_E,")
    print("spaced by 2 pi omega_E and set by temperature. The Pauli obstruction is evaded by compactness;")
    print("the MPC age operator (i[L,T]=I on the real-line Liouvillian) is the continuous dual.")


if __name__ == "__main__":
    main()

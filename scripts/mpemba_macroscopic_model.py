#!/usr/bin/env python3
"""The macroscopic Mpemba effect: Newton's law of cooling vs the Herglotz crossing.

Predicts what a real cooling experiment measures -- hot vs warm water in a freezer --
under two models, and shows where the Mpemba effect ("hot freezes first") appears:

  NEWTON (the null model): a single relaxation rate, dT/dt = -k(T-T_env).
    Theorem newton_single_mode_no_crossing: one rate preserves ordering for all
    time -- the hotter sample stays hotter and freezes LATER. No Mpemba, ever.

  HERGLOTZ (the dissipative model): the cooling rate is a contact friction rho
    that the initial state sets -- a hotter sample drives stronger evaporation and
    convection and holds less dissolved gas, so it relaxes on a FASTER mode.  Two
    frictions rho_warm < rho_hot cross (theorem herglotz_friction_crossing): the
    hot distance-to-equilibrium overtakes the warm one at
    t* = log(a/b)/(rho_hot-rho_warm) [mirror mpembaCrossingTime], and the hot
    sample freezes first when rho_hot/rho_warm exceeds a threshold.

The crossing is read in ENTROPIC TIME (ticks of omega_E = kB T/hbar, S10 Matsubara
quantization -- invariant of the lab clock), as a MISRA age (the monotone internal
time = accumulated friction), and priced as HERGLOTZ imaginary action S_I = hbar rho t
(the Nagao-Nielsen modulus e^{-rho t}).  This is not the quantum Mpemba effect -- it is
the original macroscopic one, modelled through the arc's dissipative framework and
contrasted with Newtonian physics.

Run:  python3 scripts/mpemba_macroscopic_model.py
"""
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import physlib_mpemba as plm

KB, HBAR = 1.380649e-23, 1.054571817e-34
T_ENV = -18.0            # freezer, deg C
T_FREEZE = 0.0           # freezing threshold, deg C
T_HOT, T_WARM = 99.0, 35.0
GAP = T_FREEZE - T_ENV   # distance-to-equilibrium at freezing = 18


def main():
    plm.selfcheck()
    print("[GATE] physlib_mpemba mirror passes all Lean theorem identities\n")

    # --- NEWTON: single rate, no crossing (newton_single_mode_no_crossing) ---
    k = 0.040                                   # per minute, one rate for both samples
    print("[NEWTON] single relaxation rate k = 0.040 /min (dT/dt = -k(T-T_env)):")
    for T0, name in ((T_HOT, "hot 99C"), (T_WARM, "warm 35C")):
        tf = plm.route_freeze_time(T0, T_ENV, T_FREEZE, k)
        print(f"    {name:9s}: reaches 0 C at {tf:.1f} min")
    tf_hot = plm.route_freeze_time(T_HOT, T_ENV, T_FREEZE, k)
    tf_warm = plm.route_freeze_time(T_WARM, T_ENV, T_FREEZE, k)
    print(f"    -> warm freezes first ({tf_warm:.1f} < {tf_hot:.1f} min); ordering never "
          f"crosses. Newton predicts NO Mpemba.")

    # --- HERGLOTZ: friction set by initial temperature -> crossing ---
    rho_warm, rho_hot = 0.035, 0.075            # /min; hot drives faster relaxation
    a, b = T_HOT - T_ENV, T_WARM - T_ENV        # distances-to-equilibrium: 117, 53
    tstar = plm.mpembaCrossingTime(a, b, -rho_warm, -rho_hot)   # = log(a/b)/(rho_hot-rho_warm)
    print(f"\n[HERGLOTZ] two frictions rho_warm = {rho_warm}, rho_hot = {rho_hot} /min "
          f"(ratio {rho_hot / rho_warm:.2f}):")
    print(f"    distance-to-equilibrium crossing (herglotz_friction_crossing): "
          f"t* = {tstar:.1f} min")
    hf = plm.route_freeze_time(T_HOT, T_ENV, T_FREEZE, rho_hot)
    wf = plm.route_freeze_time(T_WARM, T_ENV, T_FREEZE, rho_warm)
    print(f"    hot 99C reaches 0 C at {hf:.1f} min; warm 35C at {wf:.1f} min")
    verdict = "HOT FREEZES FIRST -- the Mpemba effect" if hf < wf else "warm first (no Mpemba)"
    print(f"    -> {verdict} (crossing at t* = {tstar:.1f} min precedes freezing)")

    # --- the crossing in ENTROPIC TIME (S10), MISRA age, HERGLOTZ imaginary action ---
    T_cross = T_ENV + a * np.exp(-rho_hot * tstar)    # temperature at the crossing, deg C
    omega_E = KB * (T_cross + 273.15) / HBAR          # entropic clock rate at that temperature
    period = plm.entropicTimePeriod(KB, T_cross + 273.15, HBAR)
    ticks = omega_E * (tstar * 60.0)                  # entropic ticks in t* (t* in seconds)
    efolds = rho_hot * tstar                          # dimensionless rho*t (min*/min): the e-fold count
    print(f"\n[ENTROPIC / MISRA / HERGLOTZ] the crossing, read three ways:")
    print(f"    entropic clock at crossing T = {T_cross:.1f} C: omega_E = {omega_E:.2e} rad/s, "
          f"tick = {period * 1e15:.1f} fs")
    print(f"    crossing time in entropic ticks: omega_E t* = {ticks:.2e} "
          f"(macroscopic t* = {tstar * 60:.0f} s is ~1e17 entropic ticks, clock-invariant)")
    print(f"    Misra age = Herglotz imaginary action S_I/hbar = e-fold count = rho_hot t* "
          f"= {efolds:.3f}")
    print(f"    (one dimensionless internal time, three names); NN modulus e^-(rho t*) "
          f"= {np.exp(-efolds):.3f}")

    # --- the Mpemba window: which initial hot temperatures freeze first ---
    print(f"\n[WINDOW] hot-freezes-first window (warm fixed at 35C, rho_hot/rho_warm = "
          f"{rho_hot / rho_warm:.2f}):")
    hot_temps = np.arange(40, 100, 5.0)
    first = []
    for Th in hot_temps:
        # friction grows with initial temperature (phenomenological: evaporation/convection)
        rho_h = rho_warm * (1 + (rho_hot / rho_warm - 1) * (Th - T_WARM) / (T_HOT - T_WARM))
        hf_i = plm.route_freeze_time(Th, T_ENV, T_FREEZE, rho_h)
        first.append(hf_i < wf)
    window = hot_temps[np.array(first)]
    if len(window):
        print(f"    Mpemba (hot freezes before warm) for hot T0 in "
              f"[{window.min():.0f}, {window.max():.0f}] C -- Newton predicts this window is EMPTY")
    threshold = np.log(a / GAP) / np.log(b / GAP)
    print(f"    onset condition: rho_hot/rho_warm > log((T_hot-T_env)/gap)/log((T_warm-T_env)/gap) "
          f"= {threshold:.2f}")

    # --- ENTROPIC-TIME RE-EVALUATION: existence is clock-free, timing is clock-set ---
    print("\n[ENTROPIC-TIME] the same crossing across temperatures (omega_E = kB T/hbar):")
    print("    T (K)   omega_E (rad/s)   lab t* (min)   entropic ticks   gap exists?")
    # the spectral geometry (rate RATIO) is fixed; only the overall rate scales with omega_E ~ T
    ratio = rho_hot / rho_warm                        # dimensionless spectral gap, clock-free
    for Tk in (250.0, 300.0, 350.0):
        oE = KB * Tk / HBAR
        # rates measured in lab time scale with the entropic clock (rho ~ omega_E ~ T)
        scale = Tk / 300.0
        rw_T, rh_T = rho_warm * scale, rho_hot * scale
        tstar_T = plm.mpembaCrossingTime(a, b, -rw_T, -rh_T)   # lab-frame crossing time
        ticks_T = oE * (tstar_T * 60.0)                        # entropic-tick count
        gap = (rh_T > rw_T)                                    # existence: the gap
        print(f"    {Tk:5.0f}   {oE:.3e}     {tstar_T:8.2f}     {ticks_T:.3e}   {gap}")
    print(f"    -> lab t* scales as 1/T (faster clock, sooner crossing); the entropic-tick")
    print(f"       count moves with omega_E, but the GAP RATIO {ratio:.2f} (existence) is T-invariant.")
    print(f"    -> WHETHER hot freezes first is clock-free spectral geometry (ratio > {threshold:.2f});")
    print(f"       WHEN it happens is set by the entropic clock omega_E ~ T (rates_split_scaling_invariant).")

    # --- LORENTZ / BISOGNANO-WICHMANN reading: the clock factor is a boost e^eta ---
    print("\n[WICHMANN] the entropic clock is the wedge modular flow (= Lorentz boost); rescaling")
    print("    omega_E is a boost of rapidity eta (Doppler shift of the Unruh temperature):")
    k2, k3 = 0.30, 0.55                                # two Rindler/boost energies (kappa)
    s0 = plm.mpembaCrossingTime(a, b, -(2 * np.pi * k2), -(2 * np.pi * k3))  # imag-modular crossing
    print("    rapidity eta   boost e^eta   modular s*   e-folds 2 pi k3 s* (imaginary action)")
    for eta in (-0.5, 0.0, 0.5, 1.0):
        eh = np.exp(eta)
        s_eta = plm.mpembaCrossingTime(a, b, eh * -(2 * np.pi * k2), eh * -(2 * np.pi * k3))
        efolds = (eh * (2 * np.pi * k3)) * s_eta       # rate blueshift x dilated modular time
        gap = (k3 > k2)                                # existence, boost-invariant
        print(f"    {eta:+.1f}          {eh:.3f}       {s_eta:8.3f}     {efolds:.4f}  (gap: {gap})")
    print(f"    -> s* dilates with rapidity (imaginary modular time), the gap is boost-invariant,")
    print(f"       and the e-fold count 2 pi k3 s* = {2 * np.pi * k3 * s0:.4f} is the LORENTZ INVARIANT")
    print(f"       (rate blueshifts e^eta, modular time dilates e^-eta -- exact compensation).")

    print("\nVERDICT: Newton's single-rate cooling can never make hot freeze first (ordering frozen,")
    print("newton_single_mode_no_crossing). The Herglotz two-friction model -- friction set by the")
    print("initial state -- crosses at t* = log(a/b)/(rho_hot-rho_warm) and predicts a definite")
    print("hot-freezes-first window; the crossing is ~1e17 entropic ticks, a Misra age, an imaginary")
    print("action. The macroscopic measurement discriminates the two (macroscopic_mpemba_vs_newton).")


if __name__ == "__main__":
    main()

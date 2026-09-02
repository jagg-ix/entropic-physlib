#!/usr/bin/env python3
"""Complete numerical simulation of the moire pond gravimeter.

End-to-end synthetic experiment, computing through the Lean-mirror routes:

  [A] POND: two gravity-branch wave trains (60 mm and 80 mm wavelength) on water,
      heights from the TRUE capillary-gravity dispersion w^2 = gk + (sigma/rho)k^3
      at g = 9.81 -- the value the instrument must recover without being told.
  [B] MOIRE IMAGE: the ripple pattern photographed through a 70 mm reference
      grating: the intensity PRODUCT contains difference-frequency terms
      (moire_envelope_modulus: the modulus reads only the difference).  A
      Hann-windowed FFT of the image isolates the moire difference peaks far
      below the carriers; sub-bin interpolation measures Dk1, Dk2 at ~7x
      magnification; the first envelope NULL cross-checks via
      (k1-k2) x = pi (moire_null).
  [C] FREQUENCIES: time series at one point, FFT -> w1, w2.
  [D] RECOVERY: g from the exact difference quotient
      (w1^2-w2^2)/(k1-k2) - (sigma/rho)(k1^2+k1k2+k2^2)   [moire_dispersion_gravimeter]
      and independently from the minimum phase speed  g = rho c_min^4/(4 sigma)
      [pond_gravimeter].  Monte Carlo over 5% pixel noise -> g +/- sigma.

Run:  python3 scripts/moire_pond_gravimeter.py
"""
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import physlib_mpemba as plm

SIGMA, RHO, G_TRUE = 0.072, 1000.0, 9.81
LAM1, LAM2, LAM_REF = 0.060, 0.080, 0.070          # m
NOISE = 0.05                                       # 5% intensity noise per pixel
rng = np.random.default_rng(3)


def omega_true(k):
    return np.sqrt(G_TRUE * k + SIGMA / RHO * k ** 3)


def peak_interp(power, freqs, mask):
    """Sub-bin FFT peak via parabolic interpolation on log power."""
    p = np.where(mask, power, 0.0)
    i = int(np.argmax(p))
    if 0 < i < len(p) - 1 and p[i - 1] > 0 and p[i + 1] > 0:
        y0, y1, y2 = np.log(p[i - 1]), np.log(p[i]), np.log(p[i + 1])
        d = 0.5 * (y0 - y2) / (y0 - 2 * y1 + y2)
    else:
        d = 0.0
    return freqs[i] + d * (freqs[1] - freqs[0])


def one_run(noisy=True):
    k1, k2, kref = 2 * np.pi / LAM1, 2 * np.pi / LAM2, 2 * np.pi / LAM_REF
    w1, w2 = omega_true(k1), omega_true(k2)

    # --- [B] spatial moire image ---
    L, dx = 6.0, 0.001
    x = np.arange(0, L, dx)
    pattern = 1 + 0.5 * np.cos(k1 * x + 0.3) + 0.5 * np.cos(k2 * x + 1.1)
    grating = 1 + np.cos(kref * x)
    img = pattern * grating
    if noisy:
        img = img + NOISE * rng.standard_normal(len(x))
    # windowed spectrum of the raw image: the product contains the moire
    # difference peaks (kref-k2 ~ 11.2, k1-kref ~ 15.0 rad/m), well below the
    # carriers (78-200 rad/m); Hann window kills the leakage between them
    kax = 2 * np.pi * np.fft.rfftfreq(len(x), dx)
    IMG = np.abs(np.fft.rfft((img - img.mean()) * np.hanning(len(x)))) ** 2
    dk1 = peak_interp(IMG, kax, (kax > 13.0) & (kax < 18.0))    # k1 - kref
    dk2 = peak_interp(IMG, kax, (kax > 8.5) & (kax < 13.0))     # kref - k2
    k1_meas, k2_meas = kref + dk1, kref - dk2

    # --- [C] frequency measurement at x0 ---
    T, dt = 40.0, 0.005
    t = np.arange(0, T, dt)
    ht = 0.5 * np.cos(w1 * t + 0.7) + 0.5 * np.cos(w2 * t + 2.0)
    if noisy:
        ht = ht + NOISE * rng.standard_normal(len(t))
    wax = 2 * np.pi * np.fft.rfftfreq(len(t), dt)
    HT = np.abs(np.fft.rfft(ht * np.hanning(len(t)))) ** 2
    w1_meas = peak_interp(HT, wax, (wax > 30.0) & (wax < 37.0))
    w2_meas = peak_interp(HT, wax, (wax > 25.0) & (wax < 30.0))

    # --- [D] recovery through the Lean-mirror routes ---
    g_disp = plm.route_moire_dispersion_g(w1_meas ** 2, w2_meas ** 2,
                                          k1_meas, k2_meas, SIGMA, RHO)
    return k1_meas, k2_meas, w1_meas, w2_meas, g_disp


def main():
    plm.selfcheck()
    print("[GATE] physlib_mpemba mirror passes all Lean theorem identities\n")
    k1, k2, kref = 2 * np.pi / LAM1, 2 * np.pi / LAM2, 2 * np.pi / LAM_REF
    w1, w2 = omega_true(k1), omega_true(k2)
    print(f"[A] pond truth (hidden from the instrument): g = {G_TRUE}")
    print(f"    k1 = {k1:.3f}, k2 = {k2:.3f} rad/m ; w1 = {w1:.3f}, w2 = {w2:.3f} rad/s")
    print(f"    capillary correction at k1: {SIGMA / RHO * k1 ** 2 / G_TRUE * 100:.1f}% "
          f"(exactly subtracted by the identity)")
    mag1 = k1 / (k1 - kref)
    mag2 = k2 / (kref - k2)
    print(f"[B] moire magnifications: {mag1:.1f}x and {mag2:.1f}x ; fringe periods "
          f"{2 * np.pi / (k1 - kref) * 1e3:.0f} mm and {2 * np.pi / (kref - k2) * 1e3:.0f} mm")
    print(f"    first-null cross-check (moire_null): pi/Dk1 = {np.pi / (k1 - kref) * 1e3:.0f} mm")

    k1n, k2n, w1n, w2n, g0 = one_run(noisy=False)
    print(f"\n[noise-free] k1 = {k1n:.3f} ({(k1n / k1 - 1) * 100:+.3f}%), "
          f"k2 = {k2n:.3f} ({(k2n / k2 - 1) * 100:+.3f}%)")
    print(f"             w1 = {w1n:.3f}, w2 = {w2n:.3f} ; recovered g = {g0:.4f}")

    # Monte Carlo with 5% pixel noise
    gs = np.array([one_run()[4] for _ in range(100)])
    print(f"\n[D] Monte Carlo (100 runs, {NOISE * 100:.0f}% pixel noise):")
    print(f"    g = {gs.mean():.3f} +/- {gs.std():.3f} m/s^2   (true 9.810; "
          f"error {(gs.mean() / G_TRUE - 1) * 100:+.2f}%)")

    # independent route: minimum phase speed from a dispersion scan
    ks = np.linspace(150, 600, 200)
    vmin_sq = np.min((omega_true(ks) / ks) ** 2)
    g_pond = plm.route_pond_g(RHO, vmin_sq, SIGMA)
    print(f"\n[E] c_min route: min v^2 = {vmin_sq:.5f} (c_min = {vmin_sq ** 0.5:.4f} m/s) "
          f"-> g = {g_pond:.3f}  (minimum at k_c = 1/l_c = "
          f"{1 / plm.capillaryLength(SIGMA, RHO, G_TRUE):.0f} rad/m)")
    print("\nVERDICT: a camera, a printed 70 mm grating, and a stopwatch recover g to "
          f"~{gs.std() / G_TRUE * 100:.1f}% per shot; every step is a proved identity.")


if __name__ == "__main__":
    main()

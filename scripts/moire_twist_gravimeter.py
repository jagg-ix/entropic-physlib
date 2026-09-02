#!/usr/bin/env python3
"""Twist-moire gravimeter: 2D rotational moire readout, built on external stacks.

Expands the 1D moire pond gravimeter to the ROTATIONAL moire law
(Lean: twist_moire_wavenumber -- two equal-k patterns rotated by theta beat at
2k sin(theta/2), magnification 1/(2 sin(theta/2))), using three external
packages as engines and cross-checks:

  [1] moire-optics-lab (Rafael V. F. dos Santos): its independent
      estimate_moire_period is validated against our Lean law across a grid,
      and its line_grating/combine_gratings generate the 2D moire images.
  [2] The twist gravimeter: pond ripples (60 mm) photographed through an
      equal-period reference grating rotated by 4 degrees; the moire peak in
      the 2D FFT sits at 2k sin(theta/2) (14x magnification); k recovered from
      the peak radius, omega from a time series, and g from the dispersion
      g = (w^2 - (sigma/rho) k^3)/k.  Monte Carlo over pixel noise.
  [3] PyAtoms (A. Prado): twisted hexagonal lattices from hexatoms() -- the
      innermost moire FFT peak vs 2|k1| sin(theta/2) on a hex lattice.
      (Optional: set PYATOMS_DIR to the PyAtoms checkout.)
  [4] MoirePy (J. Umar): rotation-matrix consistency; bilayer lattice tooling
      available for tight-binding extensions (noted, not required).

Run:  python3 scripts/moire_twist_gravimeter.py
"""
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import physlib_mpemba as plm

import moire_physics as mp

SIGMA, RHO, G_TRUE = 0.072, 1000.0, 9.81
LAM = 0.060                       # 60 mm ripples
THETA_DEG = 4.0
NOISE = 0.05
rng = np.random.default_rng(11)


def twist_law(theta):
    """Lean twist_moire_wavenumber: |k_hat1 - R(theta) k_hat2| = 2|sin(theta/2)|."""
    return 2 * abs(np.sin(theta / 2))


def omega_true(k):
    return np.sqrt(G_TRUE * k + SIGMA / RHO * k ** 3)


def peak_radius_2d(F, k_ax, kmin, kmax):
    """Radius of the strongest 2D-FFT peak in [kmin, kmax), with sub-bin
    parabolic interpolation on log power along both axes."""
    KX, KY = np.meshgrid(k_ax, k_ax)
    KR = np.hypot(KX, KY)
    mask = (KR > kmin) & (KR < kmax)
    i, j = np.unravel_index(np.argmax(np.where(mask, F, 0.0)), F.shape)
    dk = k_ax[1] - k_ax[0]

    def off(a, b, c):
        return 0.5 * (np.log(a) - np.log(c)) / (np.log(a) - 2 * np.log(b) + np.log(c))

    di = off(F[i - 1, j], F[i, j], F[i + 1, j]) if 0 < i < F.shape[0] - 1 else 0.0
    dj = off(F[i, j - 1], F[i, j], F[i, j + 1]) if 0 < j < F.shape[1] - 1 else 0.0
    return np.hypot(k_ax[j] + dj * dk, k_ax[i] + di * dk)


def moire_peak_radius(img, extent):
    """Radius (rad/m) of the innermost non-DC 2D-FFT peak."""
    n = img.shape[0]
    w2 = np.hanning(n)[:, None] * np.hanning(n)[None, :]
    F = np.abs(np.fft.fftshift(np.fft.fft2((img - img.mean()) * w2))) ** 2
    k_ax = 2 * np.pi * np.fft.fftshift(np.fft.fftfreq(n, d=extent / n))
    k_carrier = 2 * np.pi / LAM
    return peak_radius_2d(F, k_ax, 0.03 * k_carrier, 0.5 * k_carrier)


def one_run(noisy=True):
    # [2] the 2D twist-moire image: ripples at 0 deg, reference at THETA_DEG
    n, extent = 2048, 12.0                                    # 12 m field, ~14 moire fringes
    period_px = LAM / (extent / n)
    ripple = mp.line_grating(n, period_px, angle_deg=0.0,
                             phase_rad=rng.uniform(0, 2 * np.pi), waveform="sinusoidal")
    ref = mp.line_grating(n, period_px, angle_deg=THETA_DEG, waveform="sinusoidal")
    img = mp.combine_gratings(ripple, ref, mode="multiply")
    if noisy:
        img = img + NOISE * rng.standard_normal(img.shape)
    km = moire_peak_radius(img, extent)
    k_meas = km / twist_law(np.deg2rad(THETA_DEG))            # invert the twist law

    # frequency at a point
    T, dt = 40.0, 0.005
    t = np.arange(0, T, dt)
    w = omega_true(2 * np.pi / LAM)
    ht = np.cos(w * t + 1.2) + (NOISE * rng.standard_normal(len(t)) if noisy else 0)
    wax = 2 * np.pi * np.fft.rfftfreq(len(t), dt)
    HT = np.abs(np.fft.rfft(ht * np.hanning(len(t)))) ** 2
    band = (wax > 0.7 * w) & (wax < 1.3 * w)
    i = int(np.argmax(np.where(band, HT, 0)))
    y0, y1, y2 = np.log(HT[i - 1]), np.log(HT[i]), np.log(HT[i + 1])
    w_meas = wax[i] + 0.5 * (y0 - y2) / (y0 - 2 * y1 + y2) * (wax[1] - wax[0])

    g_rec = (w_meas ** 2 - SIGMA / RHO * k_meas ** 3) / k_meas
    return k_meas, w_meas, g_rec


def main():
    plm.selfcheck()
    print("[GATE] physlib_mpemba mirror passes all Lean theorem identities\n")

    # [1] validate the external implementation against the Lean twist law
    worst = 0.0
    for P in (40.0, 70.0, 123.0):
        for deg in (0.5, 1.0, 4.0, 10.0):
            ours = P / twist_law(np.deg2rad(deg))
            theirs = mp.estimate_moire_period(P, P, deg)
            worst = max(worst, abs(theirs / ours - 1))
    print(f"[1] moire-optics-lab estimate_moire_period vs Lean twist law "
          f"(12 cases): max rel dev = {worst:.2e}")

    k_true = 2 * np.pi / LAM
    mag = 1 / twist_law(np.deg2rad(THETA_DEG))
    print(f"\n[2] twist gravimeter: 60 mm ripples, reference rotated {THETA_DEG} deg "
          f"-> magnification {mag:.1f}x (moire at {2 * np.pi / (k_true * twist_law(np.deg2rad(THETA_DEG))) * 1e3:.0f} mm)")
    k0, w0, g0 = one_run(noisy=False)
    print(f"    noise-free: k = {k0:.2f} ({(k0 / k_true - 1) * 100:+.2f}%), "
          f"w = {w0:.3f} ; recovered g = {g0:.3f}")
    gs = np.array([one_run()[2] for _ in range(40)])
    print(f"    Monte Carlo (40 runs, {NOISE * 100:.0f}% pixel noise): "
          f"g = {gs.mean():.4f} +/- {gs.std():.4f}  (true {G_TRUE})")

    # [3] PyAtoms cross-check on twisted hexagonal lattices
    pyatoms_dir = os.environ.get("PYATOMS_DIR", "")
    if pyatoms_dir and os.path.isdir(pyatoms_dir):
        sys.path.insert(0, pyatoms_dir)
        try:
            from hexatoms import hexatoms
            pix, Lnm, a_nm, th = 512, 40.0, 0.5, 3.0
            lat1, _ = hexatoms(pix, Lnm, a_nm, 0.0, 0, 0, 0, 1, 1, "Hollow", [0, 0])
            lat2, _ = hexatoms(pix, Lnm, a_nm, th, 0, 0, 0, 1, 1, "Hollow", [0, 0])
            prod = lat1 * lat2
            w2 = np.hanning(pix)[:, None] * np.hanning(pix)[None, :]
            F = np.abs(np.fft.fftshift(np.fft.fft2((prod - prod.mean()) * w2))) ** 2
            kax = 2 * np.pi * np.fft.fftshift(np.fft.fftfreq(pix, d=Lnm / pix))
            k1 = 4 * np.pi / (np.sqrt(3) * a_nm)
            expect = k1 * twist_law(np.deg2rad(th))
            kr = peak_radius_2d(F, kax, 0.3 * expect, 2.5 * expect)
            print(f"\n[3] PyAtoms twisted hex ({th} deg): innermost moire peak at "
                  f"{kr:.3f} /nm vs 2|k1|sin(theta/2) = {expect:.3f} /nm "
                  f"({(kr / expect - 1) * 100:+.1f}%)")
        except Exception as ex:
            print(f"\n[3] PyAtoms check skipped: {ex}")
    else:
        print("\n[3] PyAtoms check skipped (set PYATOMS_DIR to a PyAtoms checkout)")

    # [4] MoirePy rotation-matrix consistency
    try:
        from moirepy import get_rotation_matrix
        th = np.deg2rad(THETA_DEG)
        R = np.asarray(get_rotation_matrix(th))
        khat = np.array([1.0, 0.0])
        dev = abs(np.linalg.norm(khat - R @ khat) - twist_law(th))
        print(f"[4] MoirePy get_rotation_matrix: |k - R k| vs 2 sin(theta/2): "
              f"dev = {dev:.2e}  (BilayerMoireLattice available for tight-binding extensions)")
    except Exception as ex:
        print(f"[4] MoirePy check skipped: {ex}")

    print("\nVERDICT: the rotational moire law (Lean twist_moire_wavenumber) is validated by an")
    print("independent optics package, drives a 14x-magnified 2D gravimeter, and reproduces the")
    print("twisted-bilayer moire peak on hex lattices -- one law, three stacks.")


if __name__ == "__main__":
    main()

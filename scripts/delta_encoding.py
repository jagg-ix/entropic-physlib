#!/usr/bin/env python3
"""Delta encoding: the difference is the data, in time -- and it closes the gyro loop.

The temporal twin of the differential channel (differential_signal_model.py):
transmit x_n - x_{n-1}, not the raw sample, as USB framing / delta-sigma / video
codecs / incremental encoders do.  The reference is rejected, the deltas
telescope to the absolute change, and per-delta errors accumulate as a random
walk -- which IS the strapdown gyroscope's attitude drift.

Lean side: SciamaAdSCPTMpembaNewtonObstructionHerglotz S14, via the mirror routes
deltaEncode / route_delta_reconstruct.

  [1] TELESCOPING + REFERENCE-BLINDNESS: encode a signal as deltas, shift the
      whole stream, show the deltas are unchanged and reconstruct exactly from
      one reference sample (a keyframe).
  [2] ERROR RANDOM WALK: noisy deltas -> reconstruction error = sum of errors,
      growing as sqrt(n) -- the same law as the Sagnac-gyroscope attitude drift.
  [3] KEYFRAME RESYNC: periodically re-inject a reference (video keyframe, USB
      SOF, IMU-vs-GPS update) to bound the accumulating drift.

Run:  python3 scripts/delta_encoding.py
"""
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import physlib_mpemba as plm

rng = np.random.default_rng(5)


def main():
    plm.selfcheck()
    print("[GATE] physlib_mpemba mirror passes all Lean theorem identities\n")

    # [1] telescoping + reference-blindness
    N = 200
    t = np.linspace(0, 4 * np.pi, N)
    x = 3 * np.sin(t) + 0.5 * t                              # the raw stream
    d = plm.deltaEncode(x)
    shift = 1000.0                                           # a huge absolute reference
    d_shifted = plm.deltaEncode(x + shift)
    recon = plm.route_delta_reconstruct(x[0], d)
    print("[1] telescoping reconstruction + reference-blindness:")
    print(f"    stream spans {x.min():.2f}..{x.max():.2f}; sum of {N - 1} deltas = "
          f"{np.sum(d):.4f} = x_N - x_0 = {x[-1] - x[0]:.4f}")
    print(f"    add reference {shift:.0f} to whole stream -> deltas change by "
          f"{np.max(np.abs(d_shifted - d)):.1e} (rejected)")
    print(f"    reconstruct from x_0 + cumsum(deltas): max error {np.max(np.abs(recon - x)):.1e}")

    # [2] error accumulates as a random walk (the gyro drift law)
    print("\n[2] per-delta error -> random-walk reconstruction drift "
          "(delta_error_accumulates):")
    sigma = 0.02
    for n in (25, 100, 400, 1600):
        finals = []
        for _ in range(400):
            eps = sigma * rng.standard_normal(n)
            finals.append(np.sum(eps))                       # reconstruction error at step n
        pred = sigma * np.sqrt(n)
        print(f"    n = {n:4d}: drift std = {np.std(finals):.3f}  "
              f"(sqrt(n) law: sigma*sqrt(n) = {pred:.3f})")
    print("    -> the same sqrt(n) growth as the Sagnac-gyroscope attitude random walk")

    # [3] keyframe resync bounds the drift
    print("\n[3] keyframe resync bounds the drift (video/USB/IMU-GPS):")
    n_total, sigma = 4000, 0.02
    for period in (0, 200, 50):
        drifts = []
        for _ in range(200):
            err = 0.0
            peak = 0.0
            for i in range(n_total):
                err += sigma * rng.standard_normal()         # accumulate delta error
                if period and (i + 1) % period == 0:
                    err = 0.0                                # reference re-injected
                peak = max(peak, abs(err))
            drifts.append(peak)
        label = "no resync" if period == 0 else f"every {period} samples"
        span = period if period else n_total
        print(f"    {label:18s}: peak drift {np.mean(drifts):.3f}  "
              f"(per-interval RMS sigma*sqrt(span) = {sigma * np.sqrt(span):.3f}; "
              f"peak over intervals is a few x that)")

    print("\nVERDICT: delta encoding transmits the change and rejects the reference; the deltas")
    print("telescope back to the absolute stream given one keyframe, and their errors random-walk")
    print("as sqrt(n) -- the gyroscope's drift law. A periodic reference bounds it, as every real")
    print("delta-encoded system (video keyframes, USB SOF, GPS-aided inertial nav) does.")


if __name__ == "__main__":
    main()

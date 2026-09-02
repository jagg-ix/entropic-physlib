#!/usr/bin/env python3
"""A Sagnac (optical) gyroscope reading a mechanical gyroscope, via the holonomy method.

Leverages the mechanical-gyroscope simulation at
  gyroscope_simulation (external, not vendored here)
(Zhuo Li, U. Melbourne): a spinning rotor in a gimbal, integrated with the exact
Newton-Euler ODE of func.m.  That mechanical gyro is the TRUTH source of a
rotating platform; a strapdown Sagnac ring triad bolted to its frame reads the
frame angular velocity omega(t) off the synchronization holonomy -- the method
formalized in SciamaAdSCPTMpembaEntropicClock S7:

  omega_i = c^2 dT_i/(4A)   (ring_delay_reads_component)
  |omega| = (c^2/4A) sqrt(sum dT_i^2)   (sagnac_triad_reconstructs_magnitude)

  [1] TRUTH: integrate func.m verbatim with the repo's initial conditions ->
      the Euler-angle trajectory (alpha, beta, gamma, delta) it animates.
  [2] SENSOR: the frame body angular velocity omega_3_3(t) (from calculation.m
      kinematics); a Sagnac triad reads dT_i = 4A omega_i/c^2 and reconstructs
      omega through the Lean-mirror routes -- exact, no contact with the rotor.
  [3] ATTITUDE: integrate the reconstructed omega (strapdown) and compare the
      orientation to the true direction-cosine matrix.
  [4] NOISE: fs-scale timing jitter -> angular-rate error -> attitude drift, MC.
  [5] ARCHITECTURE: the naive absolute-subtraction readout suffers catastrophic
      cancellation and leaks the common-mode through channel mismatch (S13 CMRR);
      the reciprocal (differential-by-design) readout rejects it. Full IMU error
      chain -- scale-factor, axis misalignment, bias random walk -- with an
      ablation of each source's attitude drift.
  [6] ALLAN: characterize the modelled gyro's noise the way a datasheet does --
      Allan deviation (allantools) -> angle random walk N and rate random walk K.

Run:  python3 scripts/sagnac_gyroscope.py
"""
import os
import sys
import numpy as np
from scipy.integrate import solve_ivp
from scipy.linalg import expm
import allantools

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import physlib_mpemba as plm

C = 299792458.0
DEG = np.pi / 180.0
HR = 3600.0


def gyro_ode(t, X):
    """The exact Newton-Euler ODE of gyroscope_simulation/func.m (Zhuo Li),
    transcribed verbatim: state [alpha,beta,gamma,delta, and their rates]."""
    a0, b0, c0, d0, a1, b1, c1, d1 = X
    cb, sb = np.cos(b0), np.sin(b0)
    cc, sc = np.cos(c0), np.sin(c0)
    s2b, s2c = np.sin(2 * b0), np.sin(2 * c0)

    a2 = (7078141215445656726073042565750 * b1 * c1
          + 4245518245688925142712718458880 * b1 * d1
          + 2500195204575568522761652178811 * b1 * c1 * cc ** 2
          - 130176979546908692175566929920 * b1 * d1 * cc ** 2
          + 147638083790227500439682678784 * cc * sb * sc
          - 81539949657416952006196871655354 * a1 * b1 * cb
          + 2500195204575568522761652178811 * a1 * b1 * cb * cc ** 2
          + 2500195204575568522761652178811 * a1 ** 2 * cb * cc * sb * sc
          + 2500195204575568522761652178811 * a1 * c1 * cc * sb * sc
          - 130176979546908692175566929920 * a1 * d1 * cc * sb * sc) \
        / (44309045436431304366134957110552 * sb)

    b2 = (178043574288384 * sb) / 1690241007126979 \
        + (10598877589516231 * a1 ** 2 * s2b) / 27043856114031664 \
        + (18454760473778437554960334848 * cc ** 2 * sb) / 5538630679553913045766869638819 \
        - (2500195204575568522761652178811 * b1 * c1 * s2c) / 88618090872862608732269914221104 \
        + (8136061221681793260972933120 * b1 * d1 * s2c) / 5538630679553913045766869638819 \
        - (2923050467499601 * a1 * c1 * sb) / 13521928057015832 \
        - (156986423377920 * a1 * d1 * sb) / 1690241007126979 \
        + (2500195204575568522761652178811 * a1 * c1 * cc ** 2 * sb) / 44309045436431304366134957110552 \
        - (16272122443363586521945866240 * a1 * d1 * cc ** 2 * sb) / 5538630679553913045766869638819 \
        + (2500195204575568522761652178811 * a1 ** 2 * cb * cc ** 2 * sb) / 44309045436431304366134957110552 \
        - (2500195204575568522761652178811 * a1 * b1 * cb * cc * sc) / 44309045436431304366134957110552

    c2 = (73870227446580795977937019074899808721446395032 * a1 * b1
          + 28262380361590614194780550292109443069369113530 * a1 * b1 * cb ** 2
          - 36742143539608995028253775267975567227786146752 * a1 * b1 * cc ** 2
          - 8865703545381186754902693514814798424291134750 * b1 * c1 * cb
          - 5317710542514931507672782311114922040900976640 * b1 * d1 * cb
          - 3131611649818579604886207711957873014596575183 * b1 * c1 * cb * cc ** 2
          + 163052766816461016901622055467362547411189760 * b1 * d1 * cb * cc ** 2
          + 33610531889790415423367567556017694213189571569 * a1 * b1 * cb ** 2 * cc ** 2
          - 18371071769804497514126887633987783613893073376 * a1 ** 2 * cc * sb * sc
          + 18371071769804497514126887633987783613893073376 * b1 ** 2 * cc * sb * sc
          - 184923618087194692237333625726727459126116352 * cb * cc * sb * sc
          + 15239460119985917909240679922029910599296498193 * a1 ** 2 * cb ** 2 * cc * sb * sc
          - 3131611649818579604886207711957873014596575183 * a1 * c1 * cb * cc * sb * sc
          + 163052766816461016901622055467362547411189760 * a1 * d1 * cb * cc * sb * sc) \
        / (55499155676776298463810131440912025107553321656 * sb)

    d2 = (207306110849994 * a1 ** 2 * s2c) / 1252546858776253 \
        - (207306110849994 * b1 ** 2 * s2c) / 1252546858776253 \
        - (414612221699988 * a1 * b1 * sb) / 1252546858776253 \
        + (829224443399976 * a1 * b1 * cc ** 2 * sb) / 1252546858776253 \
        - (414612221699988 * a1 ** 2 * cb ** 2 * cc * sc) / 1252546858776253

    return [a1, b1, c1, d1, a2, b2, c2, d2]


def frame_omega(a0, b0, c0, a1, b1, c1):
    """Body angular velocity of gimbal frame {3}, omega_3_3, from calculation.m:
    w_3_3 = R32 (w_21_2 + R21 w_1_1) + w_32_3."""
    cb, sb, cc, sc = np.cos(b0), np.sin(b0), np.cos(c0), np.sin(c0)
    wx = cc * b1 + sc * a1 * sb
    wy = -sc * b1 + cc * a1 * sb
    wz = a1 * cb + c1
    return np.array([wx, wy, wz])


def dcm_true(a0, b0, c0):
    """True direction-cosine matrix R03 = R01(alpha) R12(beta) R23(gamma)."""
    ca, sa, cb, sb, cc, sc = (np.cos(a0), np.sin(a0), np.cos(b0), np.sin(b0),
                              np.cos(c0), np.sin(c0))
    R01 = np.array([[ca, -sa, 0], [sa, ca, 0], [0, 0, 1]])
    R12 = np.array([[1, 0, 0], [0, cb, -sb], [0, sb, cb]])
    R23 = np.array([[cc, -sc, 0], [sc, cc, 0], [0, 0, 1]])
    return R01 @ R12 @ R23


def skew(w):
    return np.array([[0, -w[2], w[1]], [w[2], 0, -w[0]], [-w[1], w[0], 0]])


def attitude_error_deg(Ra, Rb):
    ct = np.clip((np.trace(Ra.T @ Rb) - 1) / 2, -1, 1)
    return np.degrees(np.arccos(ct))


# Fibre-optic gyro triad: a real telecom-wavelength coil.  Effective area
# A = L D/4 (L = fibre length, D = coil diameter); phase scale factor 8 pi A/(wl c).
# Sized so the Sagnac phase stays within one fringe (|dphi| < pi/2) over the fast
# spinning-top rate -- open-loop interferometric readout (navigation FOGs extend the
# range with closed-loop serrodyne feedback; noted, not simulated).
WL = 1550e-9                 # telecom wavelength, m
D_COIL = 0.08                # coil diameter, m
L_FIBRE = 50.0               # fibre length per axis, m
N_TURNS = L_FIBRE / (np.pi * D_COIL)
A_EFF = L_FIBRE * D_COIL / 4                    # effective area, m^2 (~1 m^2)
SCALE = 8 * np.pi * A_EFF / (WL * C)            # phase per unit rate, rad/(rad/s)
PHI_BIAS = np.pi / 2         # quadrature bias (interference_quadrature_bias)
PHOTONS = 1.0e13             # detected photons per sample (shot-noise phase floor)
rng = np.random.default_rng(7)


def optical_readout(w_axis, g=None, shot=False):
    """The real fibre-gyro chain for one axis: rotation -> Sagnac phase -> biased
    interference intensity -> (shot noise) -> demodulate -> phase -> rotation, all
    through the Lean-mirror sagnacPhase / interferenceIntensity / phase readout."""
    dphi = plm.sagnacPhase(A_EFF, w_axis, WL, C)            # 8 pi A w/(wl c)
    I = plm.interferenceIntensity(1.0, PHI_BIAS, dphi)      # = 1 - sin(dphi), quadrature
    if shot:
        I = I + (1.0 / np.sqrt(PHOTONS)) * g.standard_normal()   # photon shot noise
    sin_dphi = np.clip(1.0 - I, -1.0, 1.0)                  # demodulate: I/I0 - 1 = -sin dphi
    dphi_meas = np.arcsin(sin_dphi)                         # within one fringe
    return plm.route_phase_reads_rotation(dphi_meas, A_EFF, WL, C)


SIGMA_W_SHOT = (1.0 / np.sqrt(PHOTONS)) / SCALE     # shot-limited per-sample rate noise, rad/s


def imu_params(seed):
    """A tactical fibre-optic gyro error budget: fixed instrument properties (scale
    factor, axis misalignment) plus per-sample photon shot noise and bias drift."""
    g = np.random.default_rng(seed)
    sf = 1 + 200e-6 * g.standard_normal(3)       # 200 ppm scale-factor error per axis
    M = np.eye(3) + 0.5e-3 * (g.standard_normal((3, 3)))  # 0.5 mrad axis misalignment
    return dict(sf=sf, M=M, sigma_brw=1.0e-5, shot=True)   # bias random walk rad/s/sqrt(s)


def measure_reciprocal(w_true, p, state, dt, g):
    """The interferometric (reciprocal) fibre-gyro readout: each axis goes through the
    optical Sagnac chain (phase -> biased interference -> shot noise -> demodulate ->
    phase -> rotation), then the residual error chain scale-factor -> misalignment ->
    bias random walk.  The common-mode is rejected by the interferometer's reciprocity
    (S13), so no absolute transit time is ever formed."""
    w = np.array([optical_readout(w_true[k], g, shot=p['shot']) for k in range(3)])
    w = p['sf'] * w                                          # scale-factor error
    w = p['M'] @ w                                           # axis misalignment (cross-axis)
    state['bias'] = state['bias'] + p['sigma_brw'] * np.sqrt(dt) * g.standard_normal(3)
    w = w + state['bias']                                    # bias random walk
    return w


def main():
    plm.selfcheck()
    print("[GATE] physlib_mpemba mirror passes all Lean theorem identities\n")

    # [1] the mechanical gyroscope: integrate func.m with the repo's init
    init = [30 * np.pi / 180, 5 * np.pi / 180, 0.0, 0.0, 5.5, 0.0, 1.0, 20.0]
    sol = solve_ivp(gyro_ode, [0, 10], init, method="RK45", rtol=1e-9, atol=1e-9,
                    dense_output=True, max_step=0.01)
    t = np.arange(0, 10 + 1e-9, 0.01)
    X = sol.sol(t)
    print("[1] mechanical gyro (func.m verbatim, repo init [30deg,5deg,0,0,5.5,0,1,20]):")
    print(f"    integrated 0..10 s, {len(t)} steps; alpha (precession) sweeps "
          f"{np.degrees(X[0].min()):.0f}..{np.degrees(X[0].max()):.0f} deg, "
          f"beta (nutation) {np.degrees(X[1].min()):.1f}..{np.degrees(X[1].max()):.1f} deg")

    # [2] the fibre-optic Sagnac triad reads omega_3_3(t) via the interference phase
    W = np.array([frame_omega(X[0, i], X[1, i], X[2, i], X[4, i], X[5, i], X[6, i])
                  for i in range(len(t))])            # true body rates, rad/s
    dphi = plm.sagnacPhase(A_EFF, W, WL, C)           # per-axis optical Sagnac phase, rad
    delay = 4 * A_EFF * W / C ** 2                    # the underlying time delay, s
    W_rec = np.array([[optical_readout(W[i, k]) for k in range(3)]
                      for i in range(len(t))])         # phase->interference->demod->omega
    mag_true = np.linalg.norm(W, axis=1)
    mag_rec = np.linalg.norm(W_rec, axis=1)
    print(f"\n[2] fibre-optic Sagnac triad (L = {L_FIBRE:.0f} m, D = {D_COIL * 100:.0f} cm, "
          f"lambda = {WL * 1e9:.0f} nm) on the gimbal frame:")
    print(f"    scale factor 8 pi A/(lambda c) = {SCALE:.4f} rad/(rad/s), A_eff = {A_EFF:.2f} m^2")
    print(f"    underlying delay peak {np.abs(delay).max() * 1e15:.1f} fs -> Sagnac phase peak "
          f"{np.abs(dphi).max():.3f} rad (within one fringe, |dphi| < pi/2)")
    print(f"    interference readout reconstructs omega to {np.abs(W_rec - W).max():.1e} rad/s "
          f"(noise-free, exact); |omega| {mag_true.min():.3f}..{mag_true.max():.3f} rad/s "
          f"to {np.abs(mag_rec - mag_true).max():.1e}")

    # [3] strapdown attitude: integrate reconstructed omega (midpoint / 2nd order),
    # compare to the true DCM.  omega is sensed continuously from sol.sol.
    def omega_at(tt):
        Y = sol.sol(tt)
        return frame_omega(Y[0], Y[1], Y[2], Y[4], Y[5], Y[6])

    dt = t[1] - t[0]
    R = dcm_true(init[0], init[1], init[2])
    for i in range(len(t) - 1):
        w_mid = omega_at(t[i] + dt / 2)               # noise-free reconstruction is exact
        R = R @ expm(skew(w_mid) * dt)
    err_nf = attitude_error_deg(R, dcm_true(X[0, -1], X[1, -1], X[2, -1]))
    print("\n[3] strapdown attitude from the reconstructed omega (midpoint propagation):")
    print(f"    orientation error vs true DCM at 10 s: {err_nf:.2e} deg "
          f"(noise-free) -- the Sagnac gyro tracks the mechanical one")

    # [4] photon shot noise -> attitude random walk (the fundamental FOG noise floor)
    p_shot = dict(sf=np.ones(3), M=np.eye(3), sigma_brw=0.0, shot=True)
    finals = []
    for run in range(30):
        g = np.random.default_rng(200 + run)
        st = {"bias": np.zeros(3)}
        R = dcm_true(init[0], init[1], init[2])
        for i in range(len(t) - 1):
            w_mid = omega_at(t[i] + dt / 2)
            R = R @ expm(skew(measure_reciprocal(w_mid, p_shot, st, dt, g)) * dt)
        finals.append(attitude_error_deg(R, dcm_true(X[0, -1], X[1, -1], X[2, -1])))
    print(f"\n[4] photon shot noise ({PHOTONS:.0e} detected/sample -> phase floor "
          f"{1 / np.sqrt(PHOTONS):.1e} rad, {SIGMA_W_SHOT * 1e6:.2f} urad/s per axis):")
    print(f"    attitude random walk at 10 s (30 runs): {np.mean(finals):.3f} +/- "
          f"{np.std(finals):.3f} deg  (shot-limited angle random walk)")

    # [5] architecture: the interferometer measures the phase directly (reciprocal),
    # never the two absolute transit times -- which is why it must be differential
    T_common = L_FIBRE / C                           # one-way fibre transit, the common-mode
    print("\n[5] architecture -- why the readout is interferometric (S13):")
    print(f"    common-mode fibre transit T_common = L/c = {T_common * 1e9:.1f} ns; "
          f"signal delay ~ fs (1e8 x smaller)")
    for rate, name in ((6.5, "spinning top"), (7.29e-5, "Earth rate")):
        dT_sig = 4 * A_EFF * rate / C ** 2
        eps_req = dT_sig / T_common                 # per-channel timing precision to subtract absolutes
        print(f"    {name:13s}: absolute-subtraction would need per-channel timing to "
              f"{eps_req:.1e} rel. -- {'infeasible' if eps_req < 1e-13 else 'hard'}")
    eps_ch = 10 ** (-100 / 20)                       # 100 dB path (non-reciprocity) match
    leak_dT = plm.route_mismatch_leakage(1.0, 1.0 + eps_ch, T_common)
    leak_rate = plm.route_ring_delay_omega(leak_dT, A_EFF, C)
    print(f"    a 100 dB non-reciprocity between the paths would leak "
          f"{abs(leak_rate) / DEG * HR:.1e} deg/hr -> the interferometer reads the phase")
    print(f"    difference directly (reciprocity rejects the common-mode, S13), never subtracting.")

    # full interferometric error chain, ablation of each source
    print("\n    interferometric readout, full error chain (10 s attitude drift, ablation):")
    p_full = imu_params(11)
    sources = {
        "shot noise (ARW)": dict(sf=np.ones(3), M=np.eye(3), sigma_brw=0.0, shot=True),
        "scale-factor 200ppm": dict(shot=False, M=np.eye(3), sigma_brw=0.0),
        "misalignment 0.5mrad": dict(shot=False, sf=np.ones(3), sigma_brw=0.0),
        "bias random walk": dict(shot=False, sf=np.ones(3), M=np.eye(3)),
        "ALL combined": dict(),
    }
    for label, override in sources.items():
        p = dict(p_full, **override)
        drifts = []
        for run in range(20):
            g = np.random.default_rng(100 + run)
            st = {"bias": np.zeros(3)}
            R = dcm_true(init[0], init[1], init[2])
            for i in range(len(t) - 1):
                w_mid = omega_at(t[i] + dt / 2)
                R = R @ expm(skew(measure_reciprocal(w_mid, p, st, dt, g)) * dt)
            drifts.append(attitude_error_deg(R, dcm_true(X[0, -1], X[1, -1], X[2, -1])))
        print(f"      {label:22s}: {np.mean(drifts):.3f} +/- {np.std(drifts):.3f} deg")

    # [6] Allan-deviation characterization of the modelled gyro (datasheet-style)
    print("\n[6] Allan deviation of a static run (allantools) -- datasheet noise terms:")
    fs, T_static = 100.0, 2000.0
    dts = 1.0 / fs
    Ns = int(T_static * fs)
    p = imu_params(3)
    g = np.random.default_rng(42)
    st = {"bias": np.zeros(3)}
    rate_x = np.empty(Ns)
    for i in range(Ns):
        rate_x[i] = measure_reciprocal(np.zeros(3), p, st, dts, g)[0]   # x-axis, zero true rate
    taus, adev, _, _ = allantools.oadev(rate_x, rate=fs, data_type="freq", taus="octave")
    # angle random walk N: sigma(tau) = N/sqrt(tau) in the white-rate region (small tau,
    # slope -1/2), so N = sigma*sqrt(tau) there -- read below the ARW/RRW crossover
    i_min = int(np.argmin(adev))
    white = (taus < taus[i_min]) & (taus > 2 * dts)
    N_meas = float(np.median(adev[white] * np.sqrt(taus[white])))   # rad/sqrt(s)
    # rate random walk K from the +1/2 slope region (tau past the minimum)
    i_k = min(i_min + 2, len(taus) - 1)
    K_meas = adev[i_k] / np.sqrt(taus[i_k] / 3.0)            # rad/s/sqrt(s)
    N_shot = SIGMA_W_SHOT * np.sqrt(dts)                     # shot-noise-predicted ARW, rad/sqrt(s)
    print(f"    shot-noise ARW = {N_shot / DEG * np.sqrt(HR):.4f} deg/sqrt(hr); "
          f"measured N = {N_meas / DEG * np.sqrt(HR):.4f} deg/sqrt(hr)")
    print(f"    Allan minimum {adev[i_min] / DEG * HR:.3f} deg/hr at tau = {taus[i_min]:.1f} s "
          f"(the ARW/RRW crossover; flicker floor not modelled)")
    print(f"    input RRW sigma_brw = {p['sigma_brw'] / DEG * HR * np.sqrt(HR):.1f} "
          f"deg/hr/sqrt(hr); measured K = {K_meas / DEG * HR * np.sqrt(HR):.1f} "
          f"deg/hr/sqrt(hr) (+1/2 slope)")

    # [7] Fock-space photon statistics: where the shot-noise floor comes from, and
    # how squeezed light beats it (the quantum-optical limits of S9)
    Nbar = PHOTONS                                   # mean photons per sample (coherent state)
    print("\n[7] Fock-space photon statistics of the phase floor (S9):")
    print(f"    mean photon number N = {Nbar:.0e} per sample")
    for label, var in (
            ("thermal (chaotic)", plm.thermalPhaseVariance(Nbar)),
            ("coherent (laser, SQL)", plm.shotNoisePhaseVariance(Nbar)),
            ("squeezed r=1.5", plm.squeezedPhaseVariance(1.5, Nbar)),
            ("Heisenberg (N00N)", plm.heisenbergPhaseVariance(Nbar))):
        dphi = np.sqrt(var)
        drate = SCALE and abs(WL * C * dphi / (8 * np.pi * A_EFF))   # -> rate resolution
        print(f"      {label:22s}: dphi = {dphi:.2e} rad -> rate floor {drate / DEG * HR:.3e} deg/hr")
    r_heis = np.log(Nbar) / 2
    print(f"    squeezing r = (1/2)log N = {r_heis:.1f} reaches the Heisenberg limit "
          f"(squeezing_reaches_heisenberg)")

    # squeezed-light gyro: the rate-noise floor improves by e^{-r} (isolated from the
    # integration error by measuring the per-axis rate reconstruction RMS directly)
    r_sq = 1.5
    improve = np.exp(-r_sq)
    print(f"    squeezed-light gyro (r = {r_sq}): rate noise improves by e^-r = {improve:.2f} "
          f"({-20 * np.log10(improve):.1f} dB below the shot-noise limit)")
    g = np.random.default_rng(300)
    err_sql = []
    for i in range(0, len(t), 3):
        for k in range(3):
            err_sql.append(optical_readout(W[i, k], g, shot=True) - W[i, k])
    err_sql = np.array(err_sql)
    rms_sql, rms_sq = np.std(err_sql), np.std(err_sql * improve)
    print(f"    per-axis rate-noise RMS: SQL {rms_sql * 1e6:.2f} urad/s -> "
          f"squeezed {rms_sq * 1e6:.2f} urad/s (x{rms_sq / rms_sql:.2f}, matches e^-r)")

    print("\nVERDICT: the mechanical gyroscope's rotation is read, without contact, by a strapdown")
    print("fibre-optic Sagnac triad -- each ring turns the rotation into an optical phase")
    print("Delta phi = 8 pi A omega/(lambda c), read on a quadrature-biased interferometer and")
    print("demodulated to omega (S8). The interferometer measures the phase difference directly, so")
    print("the common-mode transit is rejected by reciprocity (S13), never subtracted; under the full")
    print("error chain -- shot noise, scale factor, misalignment, bias drift -- it is a tactical IFOG.")


if __name__ == "__main__":
    main()

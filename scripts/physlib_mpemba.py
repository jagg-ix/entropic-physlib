#!/usr/bin/env python3
"""Faithful Python mirror of the Lean 4 Mpemba-arc definitions and theorem routes.

Every function mirrors EXACTLY one Lean `def` (same name, same argument order,
same formula) or implements a computation path licensed by a named Lean theorem
(`route_*` functions).  Scripts must compute through these mirrors -- never
through inline re-derivations -- so the Python pipeline follows the formal
content.  `selfcheck()` verifies the theorem identities numerically.

Lean sources (Physlib/QuantumMechanics/ComplexAction/Lorentz/ unless noted):
  SciamaAdSCPTQuantumMpembaCrossing.lean
  SciamaAdSCPTTrappedIonMpembaSpectrum.lean
  SciamaAdSCPTDipolarMpembaComptonSubstrate.lean
  SciamaAdSCPTMpembaEntropicClock.lean
  SciamaAdSCPTMpembaComplexActionLorentzian.lean
  SciamaAdSCPTMadelungNavierStokesTerms.lean / SciamaAdSCPTNavierStokesHerglotzHolographicG.lean
  ComptonClock/FrequencyTrinity.lean ; Particles/CasimirLengthHierarchy.lean
  ElectroweakYangMillsThermodynamics.lean ; Optics/TemporalDoubleSlit.lean
"""
import numpy as np

# ---------------------------------------------------------------------------
# Lean defs, mirrored one-to-one
# ---------------------------------------------------------------------------


def mpembaCrossingTime(a, b, lam2, lam3):
    """def mpembaCrossingTime (a b lam2 lam3 : ℝ) := Real.log (a/b) / (lam2 - lam3)"""
    return np.log(a / b) / (lam2 - lam3)


def quantumKinematicViscosity(hbar, m):
    """def quantumKinematicViscosity (ℏ m : ℝ) := ℏ / (2 * m)   [MadelungNavierStokesTerms]"""
    return hbar / (2 * m)


def viscousLength(nu, c):
    """def viscousLength (ν c : ℝ) := 2 * ν / c   [NavierStokesHerglotzHolographicG]"""
    return 2 * nu / c


def comptonWavelength(m, c, hbar):
    """def comptonWavelength (m c ħ : ℝ) := ħ / (m * c)   [ComptonClock/FrequencyTrinity]"""
    return hbar / (m * c)


def comptonFrequency(m, c, hbar):
    """def comptonFrequency (m c ħ : ℝ) := m * c^2 / ħ   [ComptonClock/FrequencyTrinity]"""
    return m * c ** 2 / hbar


def bohrRadius(m, c, hbar, alpha):
    """def bohrRadius (m c ħ α : ℝ) := comptonWavelength m c ħ / α   [CasimirLengthHierarchy]"""
    return comptonWavelength(m, c, hbar) / alpha


def fineStructureConstant(q):
    """def fineStructureConstant (q : ℝ) := q^2 / (4π)   [ElectroweakYangMillsThermodynamics]"""
    return q ** 2 / (4 * np.pi)


def gyromagneticRatio(g, e, m):
    """def gyromagneticRatio (g e m : ℝ) := g * e / (2 * m)   [DipolarMpembaComptonSubstrate]"""
    return g * e / (2 * m)


def dipolarCoupling(eps0, c, gamma, hbar, r):
    """def dipolarCoupling (ε₀ c γ ℏ r : ℝ) := 1/(4π ε₀ c²) * γ² * ℏ / r³"""
    return 1 / (4 * np.pi * eps0 * c ** 2) * gamma ** 2 * hbar / r ** 3


def dipolarRate(b, tau):
    """def dipolarRate (b τ : ℝ) := 12 * b² * τ / 5   [DipolarMpembaComptonSubstrate]"""
    return 12 * b ** 2 * tau / 5


def sp2GeminalDistance(a0):
    """def sp2GeminalDistance (a₀ : ℝ) := 2 * √3 * a₀   [DipolarMpembaComptonSubstrate]"""
    return 2 * np.sqrt(3) * a0


def stokesEinsteinDebye(eta, a, kBT):
    """def stokesEinsteinDebye (η a kBT : ℝ) := 4π η a³ / (3 kBT)"""
    return 4 * np.pi * eta * a ** 3 / (3 * kBT)


def giererWirtzFactor(rho):
    """def giererWirtzFactor (ρ : ℝ) := 1 / (6ρ + (1+ρ)⁻³)"""
    return 1 / (6 * rho + (1 + rho) ** -3)


def bathCorrelationTime(rho, eta, a, kBT):
    """def bathCorrelationTime (ρ η a kBT : ℝ) := giererWirtzFactor ρ * stokesEinsteinDebye η a kBT"""
    return giererWirtzFactor(rho) * stokesEinsteinDebye(eta, a, kBT)


def thermalEntropicRate(kB, T, hbar):
    """def thermalEntropicRate (kB T ℏ : ℝ) := kB * T / ℏ   [Optics/TemporalDoubleSlit]"""
    return kB * T / hbar


def boseEinstein(beta, omega):
    """def boseEinstein (β ω : ℝ) := 1 / (exp(β ω) − 1)   [SciamaFluctuationDissipation]"""
    return 1 / (np.exp(beta * omega) - 1)


def hyperfineClockRate(C, alpha, mu, omC):
    """def hyperfineClockRate (C α μ ωC : ℝ) := C * α⁴ * μ * ωC   [DipolarMpembaComptonSubstrate]"""
    return C * alpha ** 4 * mu * omC


def opticalClockRate(eps, alpha, omC):
    """def opticalClockRate (ε α ωC : ℝ) := ε/2 * α² * ωC   [DipolarMpembaComptonSubstrate]"""
    return eps / 2 * alpha ** 2 * omC


def realizedClockRate(nu0, sh):
    """def realizedClockRate (ν₀ sh : ℝ) := ν₀ * (1 + sh)   [MpembaEntropicClock]"""
    return nu0 * (1 + sh)


def spectralDiscriminant(alpha, gfp):
    """def spectralDiscriminant (α gf' : ℝ) := (α − ½)² − 1/gf'²   [TrappedIonMpembaSpectrum]"""
    return (alpha - 0.5) ** 2 - 1 / gfp ** 2


def _sqrtL(x):
    """Lean Real.sqrt convention: sqrt of a negative is 0."""
    return np.sqrt(max(x, 0.0))


def slowRate(gf, alpha, gfp):
    """def slowRate (γf α gf' : ℝ) := −(γf (α + ½ − √disc))"""
    return -(gf * (alpha + 0.5 - _sqrtL(spectralDiscriminant(alpha, gfp))))


def fastRate(gf, alpha, gfp):
    """def fastRate (γf α gf' : ℝ) := −(γf (α + ½ + √disc))"""
    return -(gf * (alpha + 0.5 + _sqrtL(spectralDiscriminant(alpha, gfp))))


def strongMeCancellation(alpha, gfp):
    """def strongMeCancellation (α gf' : ℝ) := gf' ((α − ½) − √disc)"""
    return gfp * ((alpha - 0.5) - _sqrtL(spectralDiscriminant(alpha, gfp)))


# ---------------------------------------------------------------------------
# Theorem routes: computations licensed by named Lean theorems
# ---------------------------------------------------------------------------


def route_T1(b, tau):
    """theorem t1_is_fastest_mode: 15·dipolarRate b τ/24 = (3/2)b²τ = 1/T₁.
    T₁ computed through the theorem, not fitted."""
    return 1 / (15 * dipolarRate(b, tau) / 24)


def route_dipolar_crossing_time(a, b_amp, K0):
    """theorem dipolar_mpemba_crossing: crossing at
    mpembaCrossingTime a b (−5K₀/24) (−15K₀/24)."""
    return mpembaCrossingTime(a, b_amp, -(5 * K0 / 24), -(15 * K0 / 24))


def route_b_closed_form(g, alphaSI, alpha_geom, me, m, c, hbar):
    """theorem dipolar_compton_clock_closed_form:
    dipolarCoupling at r = sp2GeminalDistance (bohrRadius mₑ c ℏ α)
      = √3 g²/288 · α_SI · α³ · (mₑ/m)² · comptonFrequency mₑ c ℏ."""
    return (np.sqrt(3) * g ** 2 / 288 * alphaSI * alpha_geom ** 3
            * (me / m) ** 2 * comptonFrequency(me, c, hbar))


def route_polarization(omega0, kB, T, hbar):
    """theorem polarization_is_clock_ratio: ε = ω₀ / (2·thermalEntropicRate kB T ℏ)."""
    return omega0 / (2 * thermalEntropicRate(kB, T, hbar))


def route_gamma_window(A, omega0, omegaE):
    """theorem decoherence_rate_entropic_clock_window:
    (A/ω₀)ω_E − A < γ = A·n̄ < (A/ω₀)ω_E."""
    return (A / omega0 * omegaE - A, A / omega0 * omegaE)


def route_crossing_entropic_ticks(a, b, lam2, lam3, omegaE):
    """theorem mpembaCrossingTime_entropic_units: τ* = ω_E · t*."""
    return omegaE * mpembaCrossingTime(a, b, lam2, lam3)


def route_trapped_ion_crossing_time(a, b, gf, alpha, gfp):
    """theorem trapped_ion_crossing: crossing at
    mpembaCrossingTime a b (slowRate γf α gf') (fastRate γf α gf')."""
    return mpembaCrossingTime(a, b, slowRate(gf, alpha, gfp), fastRate(gf, alpha, gfp))


def route_efold_calibration(a, b, lam2, lam3):
    """theorem mpemba_crossing_self_calibrates: (lam2-lam3)*t* = log(a/b) --
    the crossing occurs at a fixed differential e-fold count; clock-free calibration."""
    return (lam2 - lam3) * mpembaCrossingTime(a, b, lam2, lam3)


def dilationDecoherenceRate(g, x, c, omegaE, N):
    """def dilationDecoherenceRate (g x c ωE N : ℝ) := g*x/c² * √(N/2) * ωE   [MpembaEntropicClock]"""
    return g * x / c ** 2 * np.sqrt(N / 2) * omegaE


def route_dilation_g(Gamma, x, c, omegaE, N):
    """theorem dilation_gravimeter_recovery: g = Γ·c²/(x·√(N/2)·ω_E)."""
    return Gamma * c ** 2 / (x * np.sqrt(N / 2) * omegaE)


def capillaryLength(sigma, rho, g):
    """def capillaryLength (σ ρ g : ℝ) := √(σ/(ρg))   [MpembaNewtonObstructionHerglotz]"""
    return np.sqrt(sigma / (rho * g))


def bondNumber(g, rho, r, sigma):
    """def bondNumber (g ρ r σ : ℝ) := gρr²/σ"""
    return g * rho * r ** 2 / sigma


def route_rainbow_g(sigma, rho, lc):
    """theorem rainbow_gravimeter: g = σ/(ρ·ℓ_c²)."""
    return sigma / (rho * lc ** 2)


def route_pond_g(rho, vmin_sq, sigma):
    """theorem pond_gravimeter: g = ρ·v_min²/(4σ)  (v_min = c_min²)."""
    return rho * vmin_sq ** 2 / (4 * sigma)


def thermalRoughness(kBT, rho, g, sigma, k, A):
    """def thermalRoughness := k_BT/(A(ρg+σk²))   [MpembaEntropicClock]"""
    return kBT / (A * (rho * g + sigma * k ** 2))


def route_roughness_g(kBT, rho, A, S0):
    """theorem roughness_gravimeter: g = k_BT/(ρ·A·S₀)."""
    return kBT / (rho * A * S0)


def moireEnvelope(k1, k2, x):
    """theorem moire_envelope_modulus: |e^{ik1 x} + e^{ik2 x}| = 2|cos((k1-k2)x/2)| --
    the modulus depends only on the difference."""
    return 2 * abs(np.cos((k1 - k2) / 2 * x))


def twistMoireWavenumber(k, theta):
    """theorem twist_moire_wavenumber: sqrt((cos t - 1)^2 + sin^2 t) = 2|sin(t/2)| --
    equal-wavenumber patterns rotated by theta beat at 2 k sin(theta/2)."""
    return 2 * k * abs(np.sin(theta / 2))


def route_twist_magnification(theta):
    """corollary of twist_moire_wavenumber: moire magnification 1/(2 sin(theta/2))."""
    return 1 / (2 * abs(np.sin(theta / 2)))


def route_moire_dispersion_g(w1sq, w2sq, k1, k2, sigma, rho):
    """theorem moire_dispersion_gravimeter:
    (w1^2-w2^2)/(k1-k2) = g + (sigma/rho)(k1^2+k1 k2+k2^2) -> solve for g."""
    return (w1sq - w2sq) / (k1 - k2) - sigma / rho * (k1 ** 2 + k1 * k2 + k2 ** 2)


def moirePeriod(T1, T2):
    """def moirePeriod := T1*T2/|T1-T2|   [Saveljev et al. 2023 Eq. 3]"""
    return T1 * T2 / abs(T1 - T2)


def moireMagnification(T1, T2):
    """def moireMagnification := 1/|1 - T2/T1|   [Saveljev et al. 2023 Eq. 4]"""
    return 1 / abs(1 - T2 / T1)


def beamFundamentalFrequency(E, I, lm, L):
    """def beamFundamentalFrequency := (pi/2) sqrt(E I/(lm L^4))   [Eq. 6, McConnell]"""
    return np.pi / 2 * np.sqrt(E * I / (lm * L ** 4))


def route_deferred_displacement(k1, k2, d):
    """theorem deferred_moire_displacement (Eq. 5): grid displacement d moves the moire
    envelope by x_M = k2 d/(k1-k2) = mu*d -- the phase-magnification law."""
    return k2 * d / (k1 - k2)


def route_beam_rod_frequency(E, rho, s, lm, L):
    """theorem beam_frequency_rod_form (Eqs. 9-10): f0 = (pi/4) sqrt(E rho/(3 lm)) sqrt(s/L)."""
    return np.pi / 4 * np.sqrt(E * rho / (3 * lm)) * np.sqrt(s / L)


def route_structural_g(f0, delta):
    """theorem structural_gravimeter_recovery: g = 32 f0^2 delta/pi^2 -- frequency and
    self-weight sag of any beam compute g with every material parameter cancelling."""
    return 32 * f0 ** 2 * delta / np.pi ** 2


def pythagoreanCos(p, q):
    """def pythagoreanCos := (p^2-q^2)/(p^2+q^2)   [photonic moire lattices]"""
    return (p ** 2 - q ** 2) / (p ** 2 + q ** 2)


def pythagoreanSin(p, q):
    """def pythagoreanSin := 2pq/(p^2+q^2)"""
    return 2 * p * q / (p ** 2 + q ** 2)


def moireZeemanSplitting(D, dth):
    """def moireZeemanSplitting := (D/2)(1 + cos 2 dtheta)   [moire Zeeman, 2112.10276]"""
    return D / 2 * (1 + np.cos(2 * dth))


def route_restoration_field(nel, lam, mu, g, muB):
    """theorem moire_zeeman_magnetometer: B_e = n_e (mu - lam)/(g muB) restores the
    zero-average spectrum -- reading the interaction asymmetry exactly."""
    return nel * (mu - lam) / (g * muB)


def shadowContourInterval(p, alpha, beta):
    """def shadowContourInterval := p/(tan alpha + tan beta)   [Ibrahim-Takasaki 1985]"""
    return p / (np.tan(alpha) + np.tan(beta))


def route_two_frequency_unwrap(frac_fine, d_coarse, T):
    """theorem two_frequency_unambiguous_range: within one coarse interval M T the
    height is unique, so the coarse reading supplies the integer the wrapped fine
    phase lost: d = n T + frac with n = round((d_coarse - frac)/T)."""
    n = np.round((d_coarse - frac_fine) / T)
    return n * T + frac_fine


def takasakiFringeHeight(N, p, l, s):
    """def takasakiFringeHeight := N p l/(s - N p)   [Ibrahim-Takasaki 1985; nonlinear ladder]"""
    return N * p * l / (s - N * p)


def route_takasaki_order(h, p, l, s):
    """theorem takasaki_order_inversion: N = h s/(p (l + h))."""
    return h * s / (p * (l + h))


def obliqueShadowShift(h, alpha):
    """def obliqueShadowShift := h tan(alpha)."""
    return h * np.tan(alpha)


def spectralPeak(p, k, alpha):
    """def spectralPeak := p k e^{i alpha}   [Saveljev-Kim 2013 Eq. 2, complex plane]"""
    return p * k * np.exp(1j * alpha)


def route_moire_peak(k1, a1, k2, a2):
    """theorem moire_wavevector_difference: first combinational peak = k1 e^{i a1} - k2 e^{i a2}
    (Amidror k_M = k1 - k2 as complex subtraction; = moire-optics-lab's general beat)."""
    return k1 * np.exp(1j * a1) - k2 * np.exp(1j * a2)


def sagnacTimeDelay(c, v, r):
    """def sagnacTimeDelay := 2 pi r/(c-v) - 2 pi r/(c+v)   [Spavieri 2021 Eq. 2]"""
    return 2 * np.pi * r / (c - v) - 2 * np.pi * r / (c + v)


def route_sagnac_reads_rotation(dT, r, c):
    """theorem sagnac_first_order_reads_rotation: omega = c^2 dT/(4 pi r^2) -- a Sagnac
    ring measures angular velocity as a simultaneity observable (gyroscope)."""
    return c ** 2 * dT / (4 * np.pi * r ** 2)


def ltTime(gamma, u, c, t, x):
    """def ltTime := gamma (t - u x/c^2)   [Lorentz, relative simultaneity]"""
    return gamma * (t - u * x / c ** 2)


def ltSpace(gamma, u, t, x):
    """def ltSpace := gamma (x - u t)"""
    return gamma * (x - u * t)


def ltaTime(gamma, t):
    """def ltaTime := t/gamma   [Tangherlini-Selleri, absolute simultaneity = proper time]"""
    return t / gamma


def route_minkowski_proper_time(u, c, t):
    """theorem lta_time_is_minkowski_proper_time: sqrt(c^2 t^2 - (u t)^2)/c = t/gamma --
    the absolute-simultaneity time IS the co-moving clock's Minkowski proper time."""
    return np.sqrt(c ** 2 * t ** 2 - (u * t) ** 2) / c


def syncOffsetDensity(u, c):
    """def syncOffsetDensity := u/c^2   [removable local synchronization offset per length]"""
    return u / c ** 2


def ringSyncHolonomy(omega, r, c):
    """def ringSyncHolonomy := (omega r/c^2)(2 pi r) = 2 A omega/c^2 -- the loop integral
    of the offset density, the measurable residue of the synchronization convention."""
    return omega * r / c ** 2 * (2 * np.pi * r)


def route_holonomy_reads_rotation(H, r, c):
    """theorem holonomy_reads_rotation: omega = c^2 H/(2 pi r^2) -- quantify the rotation
    by integrating the removable offset around the loop."""
    return c ** 2 * H / (2 * np.pi * r ** 2)


def route_ring_delay_omega(dT, A, c):
    """theorem ring_delay_reads_component: omega_n = c^2 dT/(4 A) -- one Sagnac ring
    reads the projection of the rotation onto its normal (strapdown gyroscope axis)."""
    return c ** 2 * dT / (4 * A)


def route_triad_magnitude(dT1, dT2, dT3, A, c):
    """theorem sagnac_triad_reconstructs_magnitude: (c^2/4A) sqrt(dT1^2+dT2^2+dT3^2)
    = |omega| -- three orthogonal rings reconstruct the angular-velocity magnitude."""
    return c ** 2 / (4 * A) * np.sqrt(dT1 ** 2 + dT2 ** 2 + dT3 ** 2)


def differentialChannel(x1, x2):
    """def differentialChannel := x1 - x2   [the USB D+ - D- differential node]"""
    return x1 - x2


def logDifferentialChannel(a, b):
    """def logDifferentialChannel := log(a/b)   [multiplicative common-mode rejected]"""
    return np.log(a / b)


def route_mismatch_leakage(g1, g2, xcm):
    """theorem differential_mismatch_leakage: D(g1 xcm, g2 xcm) = (g1-g2) xcm --
    common-mode leaks through mismatched channels (finite CMRR)."""
    return (g1 - g2) * xcm


def deltaEncode(x):
    """def deltaEncode: d_n = x_{n+1} - x_n   [temporal delta encoding, USB/video]"""
    return np.diff(x)


def route_delta_reconstruct(x0, deltas):
    """theorem delta_needs_reference: x_n = x_0 + sum_{i<n} d_i -- reconstruct the
    absolute stream from the deltas plus one reference sample (keyframe)."""
    return x0 + np.concatenate([[0.0], np.cumsum(deltas)])


def sagnacPhase(A, omega, wl, c):
    """def sagnacPhase := 8 pi A omega/(wl c) -- the optical Sagnac phase shift
    (fibre gyro: A = N pi D^2/4, so Delta phi = 2 pi L D omega/(wl c))."""
    return 8 * np.pi * A * omega / (wl * c)


def route_phase_reads_rotation(dphi, A, wl, c):
    """theorem sagnac_phase_reads_rotation: omega = wl c dphi/(8 pi A) -- the
    fibre-optic gyroscope readout, from the interferometric Sagnac phase."""
    return wl * c * dphi / (8 * np.pi * A)


def interferenceIntensity(I0, phi_b, dphi):
    """def interferenceIntensity := I0 (1 + cos(dphi + phi_b)) -- the recombined
    counter-propagating beams; phi_b = pi/2 quadrature bias linearizes the readout."""
    return I0 * (1 + np.cos(dphi + phi_b))


def sagnacBeatFrequency(A, omega, wl, P):
    """def sagnacBeatFrequency := 4 A omega/(wl P) -- ring-laser-gyro beat frequency."""
    return 4 * A * omega / (wl * P)


def route_beat_reads_rotation(df, A, wl, P):
    """theorem beat_reads_rotation: omega = wl P df/(4 A) -- ring-laser-gyro readout."""
    return wl * P * df / (4 * A)


def shotNoisePhaseVariance(Nbar):
    """def shotNoisePhaseVariance := 1/Nbar -- coherent-state standard quantum limit."""
    return 1 / Nbar


def thermalPhaseVariance(Nbar):
    """def thermalPhaseVariance := (1+Nbar)/Nbar -- thermal light, super-Poissonian."""
    return (1 + Nbar) / Nbar


def squeezedPhaseVariance(r, Nbar):
    """def squeezedPhaseVariance := e^{-2r}/Nbar -- squeezing beats the shot-noise limit."""
    return np.exp(-(2 * r)) / Nbar


def heisenbergPhaseVariance(Nbar):
    """def heisenbergPhaseVariance := 1/Nbar^2 -- the Heisenberg (N00N) limit."""
    return 1 / Nbar ** 2


def entropicTimePeriod(kB, T, hbar):
    """def entropicTimePeriod := hbar/(kB T) = 1/omega_E -- imaginary-time (KMS) circle
    circumference, one entropic tick (Connes-Rovelli thermal time)."""
    return hbar / (kB * T)


def matsubaraFreqBoson(beta, n):
    """def matsubaraFreqBoson := 2 pi n/beta -- the discrete Matsubara ladder."""
    return 2 * np.pi * n / beta


def route_entropic_ladder(kB, T, hbar, n):
    """theorem entropic_matsubara_ladder: omega_n = 2 pi n omega_E -- entropic time
    quantized in integer multiples of the entropic clock rate omega_E = kB T/hbar."""
    return 2 * np.pi * n * (kB * T / hbar)


def newtonCooling(T0, T_env, k, t):
    """Newton's law of cooling T(t) = T_env + (T0-T_env)e^{-kt} (single mode);
    theorem newton_single_mode_no_crossing: one rate preserves ordering, no crossing."""
    return T_env + (T0 - T_env) * np.exp(-k * t)


def route_freeze_time(T0, T_env, T_freeze, rho):
    """time for the distance-to-equilibrium D=T-T_env to relax to the freezing gap
    (T_freeze-T_env) at friction rho: t = log((T0-T_env)/(T_freeze-T_env))/rho."""
    return np.log((T0 - T_env) / (T_freeze - T_env)) / rho


def euclideanTwoPoint(E, tau):
    """def euclideanTwoPoint := e^{-E tau} -- the Euclidean two-point function / the
    imaginary-modular weight (Osterwalder-Schrader)."""
    return np.exp(-(E * tau))


def route_os_reflected_form(c, tau, E):
    """theorem os_reflected_form_is_square: sum_ij c_i c_j e^{-E(tau_i+tau_j)}
    = (sum_i c_i e^{-E tau_i})^2 -- OS reflection positivity as a rank-1 Gram square."""
    return (np.sum(np.asarray(c) * np.exp(-(E * np.asarray(tau))))) ** 2


def route_os_hamiltonian(E):
    """theorem os_reconstructed_hamiltonian_is_energy: H = -log(T^1) = E -- the OS
    reconstruction recovers the mode energy as the semigroup generator."""
    return -np.log(euclideanTwoPoint(E, 1.0))


def matsubaraGreen(eps, wn):
    """def matsubaraGreen := 1/(i wn - eps)  [Huang-Yue 2024; single pole]"""
    return 1.0 / (1j * wn - eps)


def retardedGreen(eps, w, eta):
    """def retardedGreen := 1/(w + i eta - eps)  -- analytic continuation i wn -> w + i eta"""
    return 1.0 / (w + 1j * eta - eps)


def route_spectral_lorentzian(eps, w, eta):
    """theorem spectral_function_lorentzian: A(w) = -(1/pi) Im G_ret = (1/pi) eta/((w-eps)^2+eta^2)."""
    return (1 / np.pi) * (eta / ((w - eps) ** 2 + eta ** 2))


def dimensionlessVaporVelocity(x, G, g, D, rho_g, drho):
    """def dimensionlessVaporVelocity := xG/sqrt(g D rho_g drho)   [MpembaNewtonObstructionHerglotz]"""
    return x * G / np.sqrt(g * D * rho_g * drho)


def route_gaussian_crossing_t(a, b, G2, G3):
    """theorem gaussian_mpemba_crossing / gaussian_crossing_self_calibrates:
    crossing at t^2 = mpembaCrossingTime a b (-G2^2) (-G3^2); (G3^2-G2^2) t*^2 = log(a/b)."""
    return np.sqrt(mpembaCrossingTime(a, b, -G2 ** 2, -G3 ** 2))


def route_gravimeter_recovery(t1, t2, s1):
    """theorem mpemba_differential_gravimeter (ii): g(h2-h1)/c^2 = (t1/t2 - 1)(1+s1)
    with s1 = g h1/c^2 -- recovers the potential difference from two coordinate-timed
    crossings of equal-proper-physics stations."""
    return (t1 / t2 - 1) * (1 + s1)


def route_wedge_modular_crossing_time(a, b, k2, k3):
    """theorem wedge_modular_mpemba_crossing: crossing at
    mpembaCrossingTime a b (−2πκ₂) (−2πκ₃)."""
    return mpembaCrossingTime(a, b, -(2 * np.pi * k2), -(2 * np.pi * k3))


# ---------------------------------------------------------------------------
# selfcheck: the theorem identities, verified on the mirrors
# ---------------------------------------------------------------------------


def selfcheck(verbose=False):
    rng = np.random.default_rng(7)
    checks = []

    def ck(name, ok):
        checks.append((name, bool(ok)))

    for _ in range(50):
        hbar, m, c = rng.uniform(0.1, 3, 3)
        ck("viscousLength_quantum_eq_compton",
           np.isclose(viscousLength(quantumKinematicViscosity(hbar, m), c),
                      comptonWavelength(m, c, hbar)))
        b, tau = rng.uniform(0.1, 3, 2)
        ck("t1_is_fastest_mode",
           np.isclose(15 * dipolarRate(b, tau) / 24, 1.5 * b ** 2 * tau))
        eps0, r, g, e, me = rng.uniform(0.1, 3, 5)
        aSI = e ** 2 / (4 * np.pi * eps0 * hbar * c)
        ag = rng.uniform(0.01, 0.2)
        r_geom = sp2GeminalDistance(bohrRadius(me, c, hbar, ag))
        ck("dipolar_compton_clock_closed_form",
           np.isclose(dipolarCoupling(eps0, c, gyromagneticRatio(g, e, m), hbar, r_geom),
                      route_b_closed_form(g, aSI, ag, me, m, c, hbar)))
        ck("dipolar_from_alpha_compton",
           np.isclose(dipolarCoupling(eps0, c, gyromagneticRatio(g, e, m), hbar, r),
                      g ** 2 / 4 * aSI * comptonWavelength(m, c, hbar) ** 2 * c / r ** 3))
        gf, al, gfp = rng.uniform(0.1, 3), rng.uniform(0.55, 1.0), rng.uniform(3, 40)
        ck("rate_sum", np.isclose(slowRate(gf, al, gfp) + fastRate(gf, al, gfp),
                                  -(gf * (2 * al + 1))))
        if spectralDiscriminant(al, gfp) >= 0:      # rate_product hypothesis hd
            ck("rate_product", np.isclose(slowRate(gf, al, gfp) * fastRate(gf, al, gfp),
                                          gf ** 2 * (2 * al + 1 / gfp ** 2)))
        rho = rng.uniform(0.01, 5)
        ck("giererWirtzFactor_pos/_lt_one", 0 < giererWirtzFactor(rho) < 1)
        ck("bathCorrelation_below_stick",
           bathCorrelationTime(rho, 1.0, 1.0, 1.0) < stokesEinsteinDebye(1.0, 1.0, 1.0))
        a_, b_, l2, l3, wE = rng.uniform(0.1, 3, 5)
        l3 = l2 - abs(l3) - 0.01
        ck("mpembaCrossingTime_entropic_units",
           np.isclose(mpembaCrossingTime(a_, b_, l2 / wE, l3 / wE),
                      route_crossing_entropic_ticks(a_, b_, l2, l3, wE)))
        x = rng.uniform(0.01, 10)
        ck("boseOccupation_entropic_bounds",
           1 / x - 1 < boseEinstein(1.0, x) < 1 / x)
        th, kt = rng.uniform(0.01, 3, 2)
        ck("twist_moire_wavenumber",
           np.isclose(kt * np.sqrt((np.cos(th) - 1) ** 2 + np.sin(th) ** 2),
                      twistMoireWavenumber(kt, th)))
        T1, T2 = rng.uniform(0.5, 3, 2)
        if abs(T1 - T2) < 1e-3:
            T2 = T1 + 0.5
        ck("moire_period_is_magnified_grid",
           np.isclose(moirePeriod(T1, T2), moireMagnification(T1, T2) * T2))
        ck("moire_period_from_wavenumbers",
           np.isclose(abs(2 * np.pi / T1 - 2 * np.pi / T2),
                      2 * np.pi / moirePeriod(T1, T2)))
        kk1, kk2, xx, dd = rng.uniform(0.5, 4, 4)
        if abs(kk1 - kk2) < 1e-3:
            kk2 = kk1 + 0.5
        ck("deferred_moire_displacement",
           np.isclose(abs(np.exp(1j * kk1 * xx) + np.exp(1j * kk2 * (xx - dd))),
                      2 * abs(np.cos((kk1 - kk2) / 2
                                     * (xx + route_deferred_displacement(kk1, kk2, dd))))))
        Eb, rb, sb, lmb, Lb = rng.uniform(0.5, 4, 5)
        ck("beam_frequency_rod_form",
           np.isclose(beamFundamentalFrequency(Eb, rb * sb * Lb ** 3 / 12, lmb, Lb),
                      route_beam_rod_frequency(Eb, rb, sb, lmb, Lb)))
        cb = rng.uniform(0.5, 3)
        ck("crack_factors_cancel",
           np.isclose(np.sqrt(cb * sb / (cb * Lb)), np.sqrt(sb / Lb)))
        Ib, gb = rng.uniform(0.5, 4, 2)
        f0b = beamFundamentalFrequency(Eb, Ib, lmb, Lb)
        db = lmb * gb * Lb ** 4 / (8 * Eb * Ib)
        ck("cantilever_selfweight_gravimeter",
           np.isclose(f0b ** 2 * db, np.pi ** 2 / 32 * gb))
        ck("structural_gravimeter_recovery",
           np.isclose(route_structural_g(f0b, db), gb))
        pp, qq = rng.integers(1, 7), rng.integers(1, 7)
        cP, sP = pythagoreanCos(pp, qq), pythagoreanSin(pp, qq)
        ck("pythagorean_twist_on_circle", np.isclose(cP ** 2 + sP ** 2, 1.0))
        aa, bb = rng.integers(-9, 9), rng.integers(-9, 9)
        NP = pp ** 2 + qq ** 2
        ck("pythagorean_twist_commensurate",
           np.isclose(NP * (aa * cP - bb * sP), round(NP * (aa * cP - bb * sP)))
           and np.isclose(NP * (aa * sP + bb * cP), round(NP * (aa * sP + bb * cP))))
        Dz, dth = rng.uniform(0.1, 3, 2)
        ck("moire_zeeman_splitting_half_angle",
           np.isclose(moireZeemanSplitting(Dz, dth), Dz * np.cos(dth) ** 2))
        ck("moire_zeeman_splitting_triangular",
           np.isclose(moireZeemanSplitting(Dz, np.pi / 3), Dz / 4))
        nz, lz, mz, gz, muz = rng.uniform(0.1, 3, 5)
        Bz = route_restoration_field(nz, lz, mz, gz, muz)
        ck("moire_zeeman_magnetometer",
           np.isclose(nz * (lz - mz) / 2 + gz * muz * Bz / 2, 0.0))
        pt, at_, bt, Mt = rng.uniform(0.2, 1.2, 4)
        ck("decorated_contour_ladder",
           np.isclose(shadowContourInterval(Mt * pt, at_, bt),
                      Mt * shadowContourInterval(pt, at_, bt)))
        Tt, Mi = rng.uniform(0.5, 2), rng.integers(3, 12)
        dt_ = rng.uniform(-0.49, 0.49) * Mi * Tt
        frac = dt_ - Tt * np.round(dt_ / Tt)
        ck("two_frequency_unambiguous_range",
           np.isclose(route_two_frequency_unwrap(frac, dt_ + 0.2 * Tt
                                                 * rng.uniform(-1, 1), Tt), dt_))
        Nk, pk = rng.uniform(1, 8), rng.uniform(0.01, 0.05)
        lk, sk = rng.uniform(0.5, 2), rng.uniform(0.5, 2)
        hk_ = takasakiFringeHeight(Nk, pk, lk, sk)
        ck("takasaki_step_formula",
           np.isclose(takasakiFringeHeight(Nk + 1, pk, lk, sk) - hk_,
                      pk * lk * sk / ((sk - (Nk + 1) * pk) * (sk - Nk * pk))))
        ck("takasaki_order_inversion",
           np.isclose(route_takasaki_order(hk_, pk, lk, sk), Nk))
        ck("moire_envelope_sign_blind",
           np.isclose(abs(np.exp(1j * 1.3 * hk_) + np.exp(1j * 0.7 * hk_)),
                      abs(np.exp(1j * 1.3 * -hk_) + np.exp(1j * 0.7 * -hk_))))
        alk = rng.uniform(0.2, 1.2)
        ck("shadow_fringe_height",
           np.isclose(obliqueShadowShift(Nk * pk / np.tan(alk), alk), Nk * pk))
        Nf = rng.integers(-8, 8)
        ck("fringe_order_parity",
           np.isclose(np.cos(Nf * np.pi) ** 2, 1.0)
           and np.isclose(np.cos((Nf + 0.5) * np.pi), 0.0))
        pk_, kk_, a1_, a2_ = rng.integers(-4, 5), rng.uniform(0.2, 3), \
            rng.uniform(0, 6), rng.uniform(0, 6)
        ck("spectral_peak_modulus",
           np.isclose(abs(spectralPeak(pk_, kk_, a1_)), abs(pk_) * abs(kk_)))
        ck("moire_wavevector_difference",
           np.isclose(spectralPeak(1, kk_, a1_) + spectralPeak(-1, kk_ * 1.3, a2_),
                      route_moire_peak(kk_, a1_, kk_ * 1.3, a2_)))
        thw = rng.uniform(0.05, 3)
        ck("twist_law_from_spectral_peaks",
           np.isclose(abs(spectralPeak(1, kk_, 0.0) + spectralPeak(-1, kk_, thw)),
                      2 * kk_ * abs(np.sin(thw / 2))))
        cc = rng.uniform(0.2, 3)
        ck("wavenumber_trajectory_radial",
           np.isclose(spectralPeak(pk_, cc * kk_, a1_), cc * spectralPeak(pk_, kk_, a1_)))
        cs, rs = rng.uniform(5, 20), rng.uniform(0.1, 2)
        vs = rng.uniform(0.05, 0.9) * cs
        ck("sagnac_time_delay_closed",
           np.isclose(sagnacTimeDelay(cs, vs, rs),
                      4 * np.pi * rs * vs / (cs ** 2 - vs ** 2)))
        ws = vs / rs
        dT_fo = 4 * (np.pi * rs ** 2) * ws / cs ** 2
        ck("sagnac_first_order_reads_rotation",
           np.isclose(route_sagnac_reads_rotation(dT_fo, rs, cs), ws))
        ss = rng.uniform(-3, 3)
        ck("langevin_null_factorization",
           np.isclose(ss ** 2 + 2 * (ws * rs) * ss - (cs ** 2 - (ws * rs) ** 2),
                      (ss - (cs - ws * rs)) * (ss + (cs + ws * rs))))
        us = rng.uniform(-0.9, 0.9) * cs
        gam = 1.0 / np.sqrt(1 - (us / cs) ** 2)              # gamma^2 (c^2-u^2) = c^2
        xs, tsg = rng.uniform(-3, 3), rng.uniform(0.1, 3)
        ck("minkowski_interval_lorentz_invariant",
           np.isclose(cs ** 2 * ltTime(gam, us, cs, tsg, xs) ** 2
                      - ltSpace(gam, us, tsg, xs) ** 2,
                      cs ** 2 * tsg ** 2 - xs ** 2))
        ck("lta_time_is_minkowski_proper_time",
           np.isclose(route_minkowski_proper_time(us, cs, tsg), ltaTime(gam, tsg)))
        ck("ring_sync_holonomy_area",
           np.isclose(ringSyncHolonomy(ws, rs, cs),
                      2 * (np.pi * rs ** 2) * ws / cs ** 2))
        ck("sagnac_delay_first_order_twice_holonomy",
           np.isclose(4 * (np.pi * rs ** 2) * ws / cs ** 2,
                      2 * ringSyncHolonomy(ws, rs, cs)))
        Hh = 2 * (np.pi * rs ** 2) * ws / cs ** 2
        ck("holonomy_reads_rotation",
           np.isclose(route_holonomy_reads_rotation(Hh, rs, cs), ws))
        Aa = rng.uniform(1, 100)
        w1, w2, w3 = rng.uniform(-3, 3, 3)
        d1, d2, d3 = (4 * Aa * w1 / cs ** 2, 4 * Aa * w2 / cs ** 2, 4 * Aa * w3 / cs ** 2)
        ck("ring_delay_reads_component",
           np.isclose(route_ring_delay_omega(d1, Aa, cs), w1))
        ck("sagnac_triad_reconstructs_magnitude",
           np.isclose(route_triad_magnitude(d1, d2, d3, Aa, cs),
                      np.sqrt(w1 ** 2 + w2 ** 2 + w3 ** 2)))
        xx1, xx2, mm = rng.uniform(-5, 5, 3)
        ck("differential_common_mode_rejection",
           np.isclose(differentialChannel(xx1 + mm, xx2 + mm),
                      differentialChannel(xx1, xx2)))
        aa, bb, kk = rng.uniform(0.2, 5, 3)
        ck("log_differential_scale_rejection",
           np.isclose(logDifferentialChannel(kk * aa, kk * bb),
                      logDifferentialChannel(aa, bb)))
        gg1, gg2, xcm = rng.uniform(-3, 3, 3)
        ck("differential_mismatch_leakage",
           np.isclose(differentialChannel(gg1 * xcm, gg2 * xcm),
                      route_mismatch_leakage(gg1, gg2, xcm)))
        xseq = rng.uniform(-5, 5, 12)
        ck("delta_telescoping_reconstruction",
           np.isclose(np.sum(deltaEncode(xseq)), xseq[-1] - xseq[0]))
        ck("delta_needs_reference",
           np.allclose(route_delta_reconstruct(xseq[0], deltaEncode(xseq)), xseq))
        cshift = rng.uniform(-3, 3)
        ck("delta_reference_blind",
           np.allclose(deltaEncode(xseq + cshift), deltaEncode(xseq)))
        Ap, wp, cp = rng.uniform(1, 100), rng.uniform(0.5, 2), rng.uniform(5, 20)
        wlp = rng.uniform(0.5, 2)
        ck("sagnac_phase_from_delay",
           np.isclose((2 * np.pi * cp / wlp) * (4 * Ap * wp / cp ** 2),
                      sagnacPhase(Ap, wp, wlp, cp)))
        dphi = sagnacPhase(Ap, wp, wlp, cp)
        ck("sagnac_phase_reads_rotation",
           np.isclose(route_phase_reads_rotation(dphi, Ap, wlp, cp), wp))
        ck("interference_quadrature_bias",
           np.isclose(interferenceIntensity(1.0, np.pi / 2, dphi), 1.0 - np.sin(dphi)))
        Pp = rng.uniform(1, 10)
        df = sagnacBeatFrequency(Ap, wp, wlp, Pp)
        ck("beat_reads_rotation",
           np.isclose(route_beat_reads_rotation(df, Ap, wlp, Pp), wp))
        Nb = rng.uniform(2, 1e6)
        rq = rng.uniform(0.1, 3)
        ck("thermal_above_shot_noise",
           shotNoisePhaseVariance(Nb) < thermalPhaseVariance(Nb))
        ck("squeezed_below_shot_noise",
           squeezedPhaseVariance(rq, Nb) < shotNoisePhaseVariance(Nb))
        ck("squeezing_reaches_heisenberg",
           np.isclose(squeezedPhaseVariance(np.log(Nb) / 2, Nb),
                      heisenbergPhaseVariance(Nb)))
        ck("heisenberg_below_shot_noise",
           heisenbergPhaseVariance(Nb) < shotNoisePhaseVariance(Nb))
        kBv, Tv, hbv = rng.uniform(0.1, 3, 3)
        nn = int(rng.integers(-5, 6))
        period = entropicTimePeriod(kBv, Tv, hbv)
        ck("entropic_time_period_is_inverse_rate",
           np.isclose(period, 1 / (kBv * Tv / hbv)))
        ck("entropic_matsubara_ladder",
           np.isclose(matsubaraFreqBoson(period, nn),
                      route_entropic_ladder(kBv, Tv, hbv, nn)))
        ck("entropic_level_spacing",
           np.isclose(matsubaraFreqBoson(period, nn + 1) - matsubaraFreqBoson(period, nn),
                      2 * np.pi * (kBv * Tv / hbv)))
        av, bv2, kk2, tt2 = rng.uniform(0.5, 3, 4)
        bv2 = av - abs(bv2) - 0.01                            # ensure b < a
        ck("newton_single_mode_no_crossing",
           bv2 * np.exp(-kk2 * tt2) < av * np.exp(-kk2 * tt2))
        gf_, cc_ = rng.uniform(0.5, 3), rng.uniform(0.2, 4)   # rate + entropic-clock factor
        al_, gp_ = rng.uniform(0.55, 1.0), rng.uniform(3, 40)
        ck("slowRate_scaling",
           np.isclose(slowRate(cc_ * gf_, al_, gp_), cc_ * slowRate(gf_, al_, gp_)))
        if spectralDiscriminant(al_, gp_) >= 0:              # real-spectrum domain
            ck("spectral_gap_ratio_entropic_invariant",
               np.isclose(fastRate(cc_ * gf_, al_, gp_) / slowRate(cc_ * gf_, al_, gp_),
                          fastRate(gf_, al_, gp_) / slowRate(gf_, al_, gp_)))
        l2_, l3_ = rng.uniform(0.1, 3), rng.uniform(0.1, 3)
        ac_, bc_ = rng.uniform(1.5, 3), rng.uniform(0.5, 1.4)   # positive a > b > 0
        if abs(l2_ - l3_) > 1e-3:
            ck("mpemba_crossing_scales_inversely",
               np.isclose(mpembaCrossingTime(ac_, bc_, cc_ * l2_, cc_ * l3_),
                          mpembaCrossingTime(ac_, bc_, l2_, l3_) / cc_))
        # Osterwalder-Schrader reflection positivity (rank-1 Gram square)
        Eos = rng.uniform(0.2, 3)
        n_os = rng.integers(2, 6)
        c_os, tau_os = rng.uniform(-2, 2, n_os), rng.uniform(0.1, 3, n_os)
        form = sum(c_os[i] * c_os[j] * np.exp(-(Eos * (tau_os[i] + tau_os[j])))
                   for i in range(n_os) for j in range(n_os))
        ck("os_reflected_form_is_square",
           np.isclose(form, route_os_reflected_form(c_os, tau_os, Eos)))
        ck("os_reflection_positive", form >= -1e-9)
        s1, s2 = rng.uniform(0.1, 3, 2)
        ck("os_semigroup_property",
           np.isclose(euclideanTwoPoint(Eos, s1 + s2),
                      euclideanTwoPoint(Eos, s1) * euclideanTwoPoint(Eos, s2)))
        ck("os_semigroup_contraction",                     # E>=0, s>=0 -> 0 < T^s <= 1
           0 < euclideanTwoPoint(Eos, s1) <= 1)
        ck("os_spectrum_condition",                        # contraction all s>=0  <->  E>=0
           (all(euclideanTwoPoint(Eos, ss) <= 1 for ss in (0.1, 1.0, 5.0))) == (Eos >= 0))
        ck("os_reconstructed_hamiltonian_is_energy",
           np.isclose(route_os_hamiltonian(Eos), Eos))
        eps_m, w_m, eta_m = rng.uniform(-3, 3), rng.uniform(-3, 3), rng.uniform(0.05, 1)
        ck("spectral_function_lorentzian",
           np.isclose(-(1 / np.pi) * retardedGreen(eps_m, w_m, eta_m).imag,
                      route_spectral_lorentzian(eps_m, w_m, eta_m)))
        ck("spectral_positivity", route_spectral_lorentzian(eps_m, w_m, eta_m) >= -1e-12)
        w1b, w2b, f1b, f2b, z1b, z2b = rng.uniform(0.5, 3, 6)
        if abs(z1b - z2b) > 1e-3:
            ck("barycentric_interpolates",
               np.isclose((w1b * f1b * (z1b - z2b) + w2b * f2b * (z1b - z1b))
                          / (w1b * (z1b - z2b) + w2b * (z1b - z1b)), f1b))
        eta = rng.uniform(-2, 2)
        eh = np.exp(eta)                                        # boost factor c = e^eta
        k2_, k3_ = rng.uniform(0.1, 2), rng.uniform(0.1, 2)
        if abs(k2_ - k3_) > 1e-3:
            base = mpembaCrossingTime(ac_, bc_, -(2 * np.pi * k2_), -(2 * np.pi * k3_))
            ck("wedge_crossing_boost_dilation",
               np.isclose(mpembaCrossingTime(ac_, bc_, eh * -(2 * np.pi * k2_),
                                             eh * -(2 * np.pi * k3_)), base / eh))
            ck("wedge_imaginary_action_boost_invariant",   # e-fold count is boost-invariant
               np.isclose((eh * (2 * np.pi * k3_))
                          * mpembaCrossingTime(ac_, bc_, eh * -(2 * np.pi * k2_),
                                               eh * -(2 * np.pi * k3_)),
                          (2 * np.pi * k3_) * base))
    bad = [n for n, ok in checks if not ok]
    if verbose or bad:
        names = sorted({n for n, _ in checks})
        for n in names:
            oks = [ok for m_, ok in checks if m_ == n]
            print(f"  selfcheck {n}: {'PASS' if all(oks) else 'FAIL'} ({len(oks)} samples)")
    assert not bad, f"mirror violates Lean theorems: {set(bad)}"
    return True


if __name__ == "__main__":
    selfcheck(verbose=True)
    print("physlib_mpemba mirror: all theorem identities hold.")

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.KoopmanQuantization
public import Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov
public import Physlib.ClassicalMechanics.HopfBifurcationNormalForm
public import Physlib.Gravity.Canonical.ProblemOfTime
public import Physlib.QuantumMechanics.OneDimension.HarmonicOscillator.TISE
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Physlib.Meta.AxiomWhitelistCheck
meta import Zil

/-!
# The quantized cyclic automaton and its discrete energy spectrum

The simple periodic automaton of G. 't Hooft, *The Cellular Automaton
Interpretation of Quantum Mechanics* (arXiv:1405.1548, the cogwheel model of
its chapter 2): `N` ontological states permuted cyclically,
`|n⟩ → |n + 1 mod N⟩` (Eq. Nevolv), quantized here through the general
Koopman lift of `Physlib.QuantumMechanics.KoopmanQuantization`:

* **The Fourier modes diagonalize the step** (Eqs. Hstates, Hstatesevolve):
  the discrete Fourier mode `χ_k(n) = e^(2πikn/N)` - built from the standard
  additive character of `ZMod N` - is an eigenvector of the quantized shift
  with eigenphase `e^(-2πik/N)` (`koopman_cyclicShift_fourierMode`,
  `cyclicShift_eigenphase`): the energy spectrum `2πk/N` of the periodic
  automaton (Eq. Hamiltonperiodic), defined modulo the `2π` periodicity and
  the constant offset `δE` noted in the source.
* **Exact recurrence**: the shift has exact period `N`
  (`cyclicShift_iterate_period`) - the explicit form of the finite Poincare
  recurrence of `Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov` -
  and, for `N > 1`, moves every ontological state
  (`cyclicShift_fixed_free`).
* **Stationarity without fixed points**: the constant (zero-momentum) mode is
  a normalizable stationary state - it satisfies the Page-Wootters timeless
  constraint of the quantized automaton (`zero_mode_isPhysical`) - although
  the dynamics is fixed-point free. On finite orbits the infinite-orbit
  exclusion of `KoopmanQuantization.stationary_vanishes_on_infinite_orbit`
  does not apply: normalizable time-independent Schrodinger solutions exist
  exactly because the classical dynamics recurs. Together with the
  infinite-orbit case this completes the recurrence dichotomy at the quantum
  level.
* **Composite automata**: the Chinese remainder equivalence intertwines the
  period-`m * n` automaton with the product of coprime period-`m` and
  period-`n` automata (`chineseRemainder_intertwines`), and the product
  recurs with the product period (`prod_shift_period`) - two coprime
  cogwheels are one cogwheel, the building block of the source's generic
  finite deterministic time-reversible model.

**Honest boundary.** The eigenphase statements are per-mode identities of the
step unitary; the Hamiltonian itself (the operator `H` with `U = e^(-iH)`,
its `[0, 2π)` branch choice, the ontological-basis matrix elements and the
`tan` resummation of the source) is not constructed, and no continuum limit
is taken. The Zeeman-atom reading is the source's interpretation, not a
formalized claim.
-/

set_option autoImplicit false

open Real
open scoped ENNReal

@[expose] public section

namespace Physlib.QuantumMechanics.CyclicAutomatonSpectrum

open Physlib.QuantumMechanics.KoopmanQuantization
open Physlib.ClassicalMechanics.HopfBifurcationNormalForm

variable (N : ℕ) [NeZero N]

/-- **The simple periodic automaton** ('t Hooft Eq. Nevolv): the cyclic shift
`n ↦ n + 1` on `N` ontological states. -/
def cyclicShift : ZMod N ≃ ZMod N where
  toFun n := n + 1
  invFun n := n - 1
  left_inv n := by ring
  right_inv n := by ring

/-- Every amplitude on a finite state space is square-summable. -/
lemma memℓp_of_fintype (f : ZMod N → ℂ) : Memℓp f 2 :=
  memℓp_gen (hasSum_fintype _).summable

/-- **The discrete Fourier mode** ('t Hooft Eq. Hstates, unnormalized):
`χ_k(n) = e^(2πikn/N)`, built from the standard additive character of
`ZMod N`. -/
noncomputable def fourierMode (k : ZMod N) : lp (fun _ : ZMod N => ℂ) 2 :=
  ⟨fun n => ZMod.stdAddChar (k * n), memℓp_of_fintype N _⟩

@[simp] lemma fourierMode_apply (k n : ZMod N) :
    (fourierMode N k : ZMod N → ℂ) n = ZMod.stdAddChar (k * n) := rfl

/-- **The Fourier modes diagonalize the quantized cyclic automaton**
('t Hooft Eq. Hstatesevolve): one step multiplies the `k`-th mode by the
eigenphase `stdAddChar (-k) = e^(-2πik/N)`. -/
@[zil_level bridge_theorem]
theorem koopman_cyclicShift_fourierMode (k : ZMod N) :
    koopman (cyclicShift N) (fourierMode N k)
      = ZMod.stdAddChar (-k) • fourierMode N k := by
  apply lp.ext
  funext n
  simp only [koopman_apply, fourierMode_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul]
  have hsymm : (cyclicShift N).symm n = n - 1 := rfl
  rw [hsymm]
  rw [show k * (n - 1) = -k + k * n from by ring]
  exact AddChar.map_add_eq_mul _ _ _

/-- **The eigenphase in closed form** ('t Hooft Eq. Hamiltonperiodic): the
`k`-th mode evolves by `e^(-2πik/N)` per step - the energy spectrum `2πk/N`
of the periodic automaton, defined modulo `2π` and a constant offset. -/
@[zil_level physical_theorem]
theorem cyclicShift_eigenphase (k : ℤ) :
    ZMod.stdAddChar (-(k : ZMod N))
      = Complex.exp (2 * π * Complex.I * (-k) / N) := by
  rw [show (-(k : ZMod N)) = (((-k : ℤ) : ZMod N)) from by push_cast; ring]
  rw [ZMod.stdAddChar_coe]
  push_cast
  ring_nf

/-- **The iterate of the cyclic shift in closed form**: `j` steps translate
by `j` - the automaton's internal clock reading. -/
@[zil_level physical_theorem]
theorem cyclicShift_iterate (j : ℕ) (x : ZMod N) :
    (⇑(cyclicShift N))^[j] x = x + j := by
  induction j with
  | zero => simp
  | succ l ih =>
      rw [Function.iterate_succ_apply', ih,
        show ∀ y : ZMod N, cyclicShift N y = y + 1 from fun _ => rfl]
      push_cast
      ring

/-- **Exact recurrence**: the cyclic automaton returns after exactly `N`
steps - the explicit period of the finite Poincare recurrence. -/
@[zil_level bridge_theorem]
theorem cyclicShift_iterate_period (x : ZMod N) :
    (⇑(cyclicShift N))^[N] x = x := by
  rw [cyclicShift_iterate, ZMod.natCast_self, add_zero]

/-- For `N > 1` the cyclic shift moves every ontological state. -/
@[zil_level physical_theorem]
theorem cyclicShift_fixed_free (hN : 1 < N) (x : ZMod N) :
    cyclicShift N x ≠ x := by
  haveI : Fact (1 < N) := ⟨hN⟩
  show x + 1 ≠ x
  intro h
  have h1 : (1 : ZMod N) = 0 := by
    have h2 : x + 1 = x + 0 := by rw [add_zero]; exact h
    exact add_left_cancel h2
  exact one_ne_zero h1

/-- **The zero mode is stationary**: the constant Fourier mode is fixed by
the quantized shift - a normalizable stationary state on a dynamics that
(for `N > 1`) moves every ontological state. -/
@[zil_level physical_theorem]
theorem zero_mode_stationary :
    koopman (cyclicShift N) (fourierMode N 0) = fourierMode N 0 := by
  have h := koopman_cyclicShift_fourierMode N 0
  rw [neg_zero] at h
  rw [h, AddChar.map_zero_eq_one, one_smul]

/-- **The timeless sector of a recurrent automaton is nontrivial without
fixed points**: the constant mode satisfies the Page-Wootters constraint of
the quantized cyclic automaton. On finite orbits the infinite-orbit exclusion
does not apply - normalizable time-independent Schrodinger solutions exist
exactly because the classical dynamics recurs. -/
@[zil_level bridge_theorem]
theorem zero_mode_isPhysical :
    (koopmanTimelessConstraint (cyclicShift N)).IsPhysical (fourierMode N 0) :=
  (isPhysical_iff_fixed _ _).mpr (zero_mode_stationary N)

/-- **The quantized cyclic automaton, assembled**: Fourier modes diagonalize
the step with eigenphases `e^(-2πik/N)`, the automaton recurs with exact
period `N`, moves every state for `N > 1`, and its timeless sector contains
the constant mode - discrete spectrum, exact recurrence, and stationarity
without fixed points. -/
@[zil_level bridge_theorem]
theorem cyclic_automaton_spectrum (hN : 1 < N) :
    (∀ k : ZMod N, koopman (cyclicShift N) (fourierMode N k)
        = ZMod.stdAddChar (-k) • fourierMode N k)
    ∧ (∀ x : ZMod N, (⇑(cyclicShift N))^[N] x = x)
    ∧ (∀ x : ZMod N, cyclicShift N x ≠ x)
    ∧ (koopmanTimelessConstraint (cyclicShift N)).IsPhysical (fourierMode N 0) :=
  ⟨koopman_cyclicShift_fourierMode N, cyclicShift_iterate_period N,
   cyclicShift_fixed_free N hN, zero_mode_isPhysical N⟩

/-! ## The cyclic automaton as a bundled unitary on `ℓ²` -/

/-- The unitary state step is the **Koopman operator** of the cyclic label
shift — the reversible classical permutation quantized to a surjective linear
isometry on `ℓ²`, bundled from the general `koopmanStateStep`. -/
noncomputable def cyclicStateStep :
    lp (fun _ : ZMod N => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ZMod N => ℂ) 2 :=
  koopmanStateStep (cyclicShift N)

/-- The state step is exactly pullback by the inverse cyclic label shift — the
defining Koopman action. -/
@[simp, zil_level structural] theorem cyclicStateStep_apply
    (ψ : lp (fun _ : ZMod N => ℂ) 2) (i : ZMod N) :
    cyclicStateStep N ψ i = ψ ((cyclicShift N).symm i) :=
  rfl

/-- The label shift by an arbitrary residue. -/
def labelShift (a : ZMod N) : ZMod N ≃ ZMod N where
  toFun i := i + a
  invFun i := i - a
  left_inv i := by ring
  right_inv i := by ring

/-- The state step shifted by an arbitrary residue — a distinct presentation
of the cyclic dynamics for every generator choice. -/
noncomputable def shiftStateStep (a : ZMod N) :
    lp (fun _ : ZMod N => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ZMod N => ℂ) 2 :=
  koopmanStateStep (labelShift N a)

/-- **The shifted presentations are genuinely distinct**: for `a ≠ 1` the
shifted step is a different unitary from the standard cyclic step. -/
@[zil_level physical_theorem]
theorem shiftStateStep_ne {a : ZMod N} (ha : a ≠ 1) :
    shiftStateStep N a ≠ cyclicStateStep N := by
  intro heq
  have h1 : shiftStateStep N a (lp.single 2 (0 : ZMod N) 1) =
      lp.single 2 a 1 := by
    show koopman (labelShift N a) (lp.single 2 (0 : ZMod N) 1) = _
    rw [koopman_single]
    congr 1
    show (0 : ZMod N) + a = a
    ring
  have h2 : cyclicStateStep N (lp.single 2 (0 : ZMod N) 1) =
      lp.single 2 (1 : ZMod N) 1 := by
    show koopman (cyclicShift N) (lp.single 2 (0 : ZMod N) 1) = _
    rw [koopman_single]
    congr 1
    show (0 : ZMod N) + 1 = 1
    ring
  have hsingle : (lp.single 2 a (1 : ℂ) : lp (fun _ : ZMod N => ℂ) 2) =
      lp.single 2 (1 : ZMod N) (1 : ℂ) := by
    rw [← h1, ← h2, heq]
  have hval : ((lp.single 2 a (1 : ℂ) : lp (fun _ : ZMod N => ℂ) 2) : ZMod N → ℂ) a
      = ((lp.single 2 (1 : ZMod N) (1 : ℂ) : lp (fun _ : ZMod N => ℂ) 2) : ZMod N → ℂ) a := by
    rw [hsingle]
  rw [lp.coeFn_single, lp.coeFn_single, Pi.single_apply, Pi.single_apply,
    if_pos rfl, if_neg ha] at hval
  exact one_ne_zero hval

/-! ## Composite automata: coprime periods combine by the Chinese remainder
theorem ('t Hooft's generic finite deterministic time-reversible model) -/

section Composite

variable (m n : ℕ) [NeZero m] [NeZero n]

/-- **Coprime cyclic automata combine into one**: the Chinese remainder ring
equivalence intertwines the single period-`m * n` automaton with the product
of the period-`m` and period-`n` automata - two coprime cogwheels are one
cogwheel, the building block of the generic finite reversible model. -/
@[zil_level bridge_theorem]
theorem chineseRemainder_intertwines (h : Nat.Coprime m n) (x : ZMod (m * n)) :
    ZMod.chineseRemainder h (cyclicShift (m * n) x)
      = Prod.map (⇑(cyclicShift m)) (⇑(cyclicShift n))
          (ZMod.chineseRemainder h x) := by
  have hx : cyclicShift (m * n) x = x + 1 := rfl
  rw [hx, map_add, map_one]
  rfl

/-- **The product automaton recurs with period `m * n`**: componentwise, the
period-`m` wheel absorbs `m * n` steps and so does the period-`n` wheel. -/
@[zil_level physical_theorem]
theorem prod_shift_period (x : ZMod m × ZMod n) :
    (Prod.map (⇑(cyclicShift m)) (⇑(cyclicShift n)))^[m * n] x = x := by
  rw [Prod.map_iterate]
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · show (⇑(cyclicShift m))^[m * n] x.1 = x.1
    rw [cyclicShift_iterate]
    have hz : ((m * n : ℕ) : ZMod m) = 0 := by
      push_cast
      rw [ZMod.natCast_self, zero_mul]
    rw [hz, add_zero]
  · show (⇑(cyclicShift n))^[m * n] x.2 = x.2
    rw [cyclicShift_iterate]
    have hz : ((m * n : ℕ) : ZMod n) = 0 := by
      push_cast
      rw [ZMod.natCast_self, mul_zero]
    rw [hz, add_zero]

end Composite

/-! ## The continuum limit of the clock evolution: the Schrodinger phase at
the automaton's ticks, and the vanishing-tick limit ('t Hooft's route from
the periodic automaton to the harmonic rotator) -/

/-- **The `j`-step eigenphase**: iterating the quantized shift multiplies the
`k`-th mode by the `j`-th power of its eigenphase - the discrete clock
equation solved in closed form. -/
@[zil_level physical_theorem]
theorem koopman_iterate_fourierMode (k : ZMod N) (j : ℕ) :
    (koopman (cyclicShift N))^[j] (fourierMode N k)
      = (ZMod.stdAddChar (-k)) ^ j • fourierMode N k := by
  induction j with
  | zero => simp
  | succ l ih =>
      rw [Function.iterate_succ_apply', ih]
      have hsmul : koopman (cyclicShift N)
          ((ZMod.stdAddChar (-k)) ^ l • fourierMode N k)
            = (ZMod.stdAddChar (-k)) ^ l •
                koopman (cyclicShift N) (fourierMode N k) :=
        map_smul (koopmanLinear (cyclicShift N)) _ _
      rw [hsmul, koopman_cyclicShift_fourierMode, smul_smul, ← pow_succ]

/-- **The discrete clock equals the continuous Schrodinger phase at every
tick**: with energy `E_k = 2πk/(N δt)` (the spectrum of Eq. Hamiltonperiodic
at time step `δt`) and tick time `t_j = j δt`, the `j`-step automaton phase
is exactly `e^(-i E_k t_j)`. The quantum model is mathematically equivalent
to the deterministic automaton at all integer multiples of the time step. -/
@[zil_level bridge_theorem]
theorem discrete_clock_eq_continuous (k j : ℤ) (δt : ℝ) (hδ : δt ≠ 0) :
    ZMod.stdAddChar ((-(j * k) : ℤ) : ZMod N)
      = Complex.exp
          (-(Complex.I) * ((2 * π * k / (N * δt)) * (j * δt))) := by
  rw [ZMod.stdAddChar_coe]
  congr 1
  have hN : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hδ' : ((δt : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ
  push_cast
  field_simp

/-- **The vanishing-tick limit**: for fixed energy and time, the
stroboscopic phase at the automaton's ticks `δt ⌊t/δt⌋` converges to the
continuous Schrodinger phase `e^(-iEt)` as the tick vanishes - the
continuum limit of the clock evolution. -/
@[zil_level bridge_theorem]
theorem tendsto_strobe_phase (E t : ℝ) :
    Filter.Tendsto
      (fun δt : ℝ =>
        Complex.exp (-(Complex.I) * E * ((δt * ⌊t / δt⌋ : ℝ) : ℂ)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Complex.exp (-(Complex.I) * E * (t : ℂ)))) := by
  have hfloor : Filter.Tendsto (fun δt : ℝ => δt * ⌊t / δt⌋)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds t) := by
    have hupper : ∀ δt ∈ Set.Ioi (0 : ℝ), δt * ⌊t / δt⌋ ≤ t := by
      intro δt hδ
      have hne : δt ≠ 0 := ne_of_gt hδ
      have h1 : ((⌊t / δt⌋ : ℝ)) ≤ t / δt := Int.floor_le _
      calc δt * ⌊t / δt⌋ ≤ δt * (t / δt) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt hδ)
        _ = t := by field_simp
    have hlower : ∀ δt ∈ Set.Ioi (0 : ℝ), t - δt ≤ δt * ⌊t / δt⌋ := by
      intro δt hδ
      have hne : δt ≠ 0 := ne_of_gt hδ
      have h1 : t / δt - 1 < ⌊t / δt⌋ := Int.sub_one_lt_floor _
      have h2 : δt * (t / δt - 1) < δt * ⌊t / δt⌋ :=
        mul_lt_mul_of_pos_left h1 hδ
      have h3 : δt * (t / δt - 1) = t - δt := by
        field_simp
      linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun δt : ℝ => t - δt) (h := fun _ : ℝ => t) ?_ ?_ ?_ ?_
    · have h : Filter.Tendsto (fun δt : ℝ => t - δt)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (t - 0)) :=
        Filter.Tendsto.sub tendsto_const_nhds
          (Filter.tendsto_id.mono_left nhdsWithin_le_nhds)
      simpa using h
    · exact tendsto_const_nhds
    · exact Filter.eventually_iff_exists_mem.mpr
        ⟨Set.Ioi 0, self_mem_nhdsWithin, hlower⟩
    · exact Filter.eventually_iff_exists_mem.mpr
        ⟨Set.Ioi 0, self_mem_nhdsWithin, hupper⟩
  have hinner : Filter.Tendsto
      (fun δt : ℝ => -(Complex.I) * E * ((δt * ⌊t / δt⌋ : ℝ) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(Complex.I) * E * (t : ℂ))) := by
    have hcast := (Complex.continuous_ofReal.tendsto t).comp hfloor
    exact hcast.const_mul (-(Complex.I) * (E : ℂ))
  exact (Complex.continuous_exp.tendsto _).comp hinner

/-! ## The stroboscopic conjugacy: from the Hopf clock to the automaton

The chain closing the clock story across modules: the attractor born at the
Hopf bifurcation is the uniform rotation
(`HopfBifurcationNormalForm.hopfField_on_cycle`); sampling the rotation at
its commensurate tick lands on the primitive `N`-th root of unity; and on the
roots of unity the sampled rotation is exactly the cyclic automaton. -/

/-- **The stroboscopic embedding** of the automaton states onto the `N`-th
roots of unity. -/
noncomputable def strobeMap (n : ZMod N) : ℂ := ZMod.stdAddChar n

/-- The stroboscopic embedding is injective - distinct ontological states
land on distinct roots of unity. -/
theorem strobeMap_injective : Function.Injective (strobeMap N) :=
  ZMod.injective_stdAddChar

/-- **The automaton is the sampled rotation**: through the stroboscopic
embedding, one automaton step is multiplication by the primitive root of
unity - rotation by `2π/N` on the unit circle. -/
@[zil_level bridge_theorem]
theorem strobe_conjugacy (n : ZMod N) :
    strobeMap N (cyclicShift N n)
      = ZMod.stdAddChar (1 : ZMod N) * strobeMap N n := by
  unfold strobeMap
  rw [show cyclicShift N n = n + 1 from rfl, AddChar.map_add_eq_mul, mul_comm]

/-- **The continuous clock tick lands on the primitive root**: for rotation
frequency `ω ≠ 0`, one tick of duration `2π/(Nω)` advances the phase by
exactly `e^(2πi/N)`. -/
@[zil_level physical_theorem]
theorem rotation_tick_eq_primitive_root (ω : ℝ) (hω : ω ≠ 0) :
    Complex.exp (Complex.I * ω * (2 * π / (N * ω)))
      = ZMod.stdAddChar (((1 : ℤ) : ZMod N)) := by
  rw [ZMod.stdAddChar_coe]
  congr 1
  have hN : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hω' : ((ω : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hω
  push_cast
  field_simp

/-- **The clock chain, assembled**: the Hopf attractor is the uniform
rotation on its cycle, the rotation's commensurate tick is the primitive root
of unity, the sampled rotation on the roots of unity is exactly the cyclic
automaton, and the embedding is injective - the bifurcation-born clock
strobes to the automaton whose quantization carries the discrete spectrum
and the timeless (Wheeler-DeWitt) constraint structure shared with the
canonical-gravity problem of time. -/
@[zil_level bridge_theorem]
theorem hopf_cycle_strobe_automaton (μ ω : ℝ) (hω : ω ≠ 0) :
    (∀ p : ℝ × ℝ, p.1 ^ 2 + p.2 ^ 2 = μ → hopfField μ ω p = rotationField ω p)
    ∧ Complex.exp (Complex.I * ω * (2 * π / (N * ω)))
        = ZMod.stdAddChar (((1 : ℤ) : ZMod N))
    ∧ (∀ n : ZMod N, strobeMap N (cyclicShift N n)
        = ZMod.stdAddChar (1 : ZMod N) * strobeMap N n)
    ∧ Function.Injective (strobeMap N) :=
  ⟨fun _ h => hopfField_on_cycle h,
   rotation_tick_eq_primitive_root N ω hω,
   strobe_conjugacy N,
   strobeMap_injective N⟩

/-! ## The ontological-basis Hamiltonian kernel (Eq. hammatrixelements) -/

/-- **Character orthogonality on the states**: summing the standard character
along a multiple of the states gives `N` on the trivial multiple and zero
otherwise - the discrete Fourier orthogonality behind the kernel algebra. -/
@[zil_level physical_theorem]
theorem sum_stdAddChar_mul (c : ZMod N) :
    ∑ n : ZMod N, ZMod.stdAddChar (c * n) = if c = 0 then (N : ℂ) else 0 := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    rw [if_pos rfl]
    simp [zero_mul, AddChar.map_zero_eq_one, Finset.sum_const,
      Finset.card_univ, ZMod.card]
  · rw [if_neg hc]
    have hψ : (ZMod.stdAddChar (N := N)).mulShift c ≠ 0 := by
      intro h0
      exact (ZMod.isPrimitive_stdAddChar N) hc
        (h0.trans (by ext a; rfl))
    have hsum := AddChar.sum_eq_zero_iff_ne_zero.mpr hψ
    calc ∑ n : ZMod N, ZMod.stdAddChar (c * n)
        = ∑ n : ZMod N, (ZMod.stdAddChar (N := N)).mulShift c n := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [AddChar.mulShift_apply]
      _ = 0 := hsum

/-- Conjugation inverts the standard character. -/
theorem stdAddChar_conj (j : ZMod N) :
    (starRingEnd ℂ) (ZMod.stdAddChar j) = ZMod.stdAddChar (-j) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
    AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

/-- **The Hamiltonian kernel in the ontological basis** ('t Hooft
Eq. hammatrixelements): `H(m, n) = (2π/N²) ∑ₖ k·e^(2πik(m-n)/N)`, each mode
weighted by its energy. Summing over all residues coincides with the
source's `k = 1, …, N-1` range, the zero mode carrying zero weight. -/
noncomputable def hamiltonianKernel (m n : ZMod N) : ℂ :=
  (2 * (π : ℂ) / (N : ℂ) ^ 2) *
    ∑ k : ZMod N, (k.val : ℂ) * ZMod.stdAddChar (k * (m - n))

/-- **The kernel is hermitian**: conjugation swaps the arguments - the
Hamiltonian matrix elements form a self-adjoint array. -/
@[zil_level physical_theorem]
theorem hamiltonianKernel_hermitian (m n : ZMod N) :
    (starRingEnd ℂ) (hamiltonianKernel N m n) = hamiltonianKernel N n m := by
  unfold hamiltonianKernel
  rw [map_mul, map_sum]
  congr 1
  · rw [map_div₀, map_mul, map_ofNat, map_pow, map_natCast,
      Complex.conj_ofReal]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    congr 1
    · rw [map_natCast]
    · rw [stdAddChar_conj]
      congr 1
      ring

/-- **The kernel reproduces the spectrum** (Eqs. hammatrixelements and
Hamiltonperiodic): applied to the `l`-th Fourier character, the
ontological-basis kernel returns energy `2πl/N` times the character at the
apex - including the ground state `l = 0`, whose separate correction in the
source is covered uniformly by the kernel form. -/
@[zil_level bridge_theorem]
theorem hamiltonianKernel_fourierMode (l m : ZMod N) :
    ∑ n : ZMod N, hamiltonianKernel N m n * ZMod.stdAddChar (l * n)
      = (2 * (π : ℂ) * (l.val : ℂ) / (N : ℂ)) * ZMod.stdAddChar (l * m) := by
  have hN : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hstep : ∀ n : ZMod N, hamiltonianKernel N m n * ZMod.stdAddChar (l * n)
      = (2 * (π : ℂ) / (N : ℂ) ^ 2) *
          ∑ k : ZMod N, (k.val : ℂ) *
            (ZMod.stdAddChar (k * m) * ZMod.stdAddChar ((l - k) * n)) := by
    intro n
    unfold hamiltonianKernel
    rw [mul_assoc]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc]
    congr 1
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc ∑ n : ZMod N, hamiltonianKernel N m n * ZMod.stdAddChar (l * n)
      = ∑ n : ZMod N, (2 * (π : ℂ) / (N : ℂ) ^ 2) *
          ∑ k : ZMod N, (k.val : ℂ) *
            (ZMod.stdAddChar (k * m) * ZMod.stdAddChar ((l - k) * n)) :=
        Finset.sum_congr rfl fun n _ => hstep n
    _ = (2 * (π : ℂ) / (N : ℂ) ^ 2) *
          ∑ n : ZMod N, ∑ k : ZMod N, (k.val : ℂ) *
            (ZMod.stdAddChar (k * m) * ZMod.stdAddChar ((l - k) * n)) :=
        (Finset.mul_sum _ _ _).symm
    _ = (2 * (π : ℂ) / (N : ℂ) ^ 2) *
          ∑ k : ZMod N, (k.val : ℂ) * ZMod.stdAddChar (k * m) *
            ∑ n : ZMod N, ZMod.stdAddChar ((l - k) * n) := by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        ring
    _ = (2 * (π : ℂ) / (N : ℂ) ^ 2) *
          ((l.val : ℂ) * ZMod.stdAddChar (l * m) * (N : ℂ)) := by
        congr 1
        calc ∑ k : ZMod N, (k.val : ℂ) * ZMod.stdAddChar (k * m) *
              ∑ n : ZMod N, ZMod.stdAddChar ((l - k) * n)
            = ∑ k : ZMod N, (k.val : ℂ) * ZMod.stdAddChar (k * m) *
                (if l = k then (N : ℂ) else 0) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [sum_stdAddChar_mul]
              simp only [sub_eq_zero]
          _ = (l.val : ℂ) * ZMod.stdAddChar (l * m) * (N : ℂ) := by
              simp only [mul_ite, mul_zero]
              rw [Finset.sum_ite_eq]
              simp
    _ = (2 * (π : ℂ) * (l.val : ℂ) / (N : ℂ)) * ZMod.stdAddChar (l * m) := by
        field_simp

/-! ## The Hamiltonian operator: branch, resummation, and the oscillator
ladder -/

/-- The kernel action on amplitudes. -/
noncomputable def hamiltonianAct (ψ : lp (fun _ : ZMod N => ℂ) 2) :
    lp (fun _ : ZMod N => ℂ) 2 :=
  ⟨fun m => ∑ n : ZMod N, hamiltonianKernel N m n * ψ n,
    memℓp_of_fintype N _⟩

@[simp] lemma hamiltonianAct_apply (ψ : lp (fun _ : ZMod N => ℂ) 2)
    (m : ZMod N) : (hamiltonianAct N ψ : ZMod N → ℂ) m
      = ∑ n : ZMod N, hamiltonianKernel N m n * ψ n := rfl

/-- **The Hamiltonian as an operator on the amplitude space**: the kernel
operator `(Hψ)(m) = ∑ₙ H(m,n) ψ(n)`, the source's Hamiltonian promoted from
matrix elements to a linear operator. -/
noncomputable def hamiltonianOp :
    lp (fun _ : ZMod N => ℂ) 2 →ₗ[ℂ] lp (fun _ : ZMod N => ℂ) 2 where
  toFun := hamiltonianAct N
  map_add' ψ φ := by
    apply lp.ext
    funext m
    simp only [hamiltonianAct_apply, lp.coeFn_add, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
  map_smul' c ψ := by
    apply lp.ext
    funext m
    simp only [hamiltonianAct_apply, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring

@[simp] lemma hamiltonianOp_apply (ψ : lp (fun _ : ZMod N => ℂ) 2) :
    hamiltonianOp N ψ = hamiltonianAct N ψ := rfl

/-- **The operator eigenvalue equation**: the Fourier mode is an eigenvector
of the Hamiltonian operator with eigenvalue `2πl/N`. -/
@[zil_level bridge_theorem]
theorem hamiltonianOp_fourierMode (l : ZMod N) :
    hamiltonianOp N (fourierMode N l)
      = (2 * (π : ℂ) * (l.val : ℂ) / (N : ℂ)) • fourierMode N l := by
  apply lp.ext
  funext m
  simp only [hamiltonianOp_apply, hamiltonianAct_apply, fourierMode_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  exact hamiltonianKernel_fourierMode N l m

/-- **The operator is symmetric** on the amplitude space - self-adjointness
of the finite Hamiltonian, from hermiticity of its kernel. -/
@[zil_level physical_theorem]
theorem hamiltonianOp_symmetric (ψ φ : lp (fun _ : ZMod N => ℂ) 2) :
    inner ℂ (hamiltonianOp N ψ) φ = inner ℂ ψ (hamiltonianOp N φ) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, tsum_fintype, tsum_fintype]
  simp only [hamiltonianOp_apply, hamiltonianAct_apply, RCLike.inner_apply]
  have key : ∀ m n : ZMod N,
      φ m * (starRingEnd ℂ) (hamiltonianKernel N m n * ψ n)
        = hamiltonianKernel N n m * φ m * (starRingEnd ℂ) (ψ n) := by
    intro m n
    rw [map_mul, hamiltonianKernel_hermitian]
    ring
  calc ∑ m : ZMod N,
        φ m * (starRingEnd ℂ) (∑ n : ZMod N, hamiltonianKernel N m n * ψ n)
      = ∑ m : ZMod N, ∑ n : ZMod N,
          φ m * (starRingEnd ℂ) (hamiltonianKernel N m n * ψ n) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_sum, Finset.mul_sum]
    _ = ∑ m : ZMod N, ∑ n : ZMod N,
          hamiltonianKernel N n m * φ m * (starRingEnd ℂ) (ψ n) :=
        Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun n _ => key m n
    _ = ∑ n : ZMod N, ∑ m : ZMod N,
          hamiltonianKernel N n m * φ m * (starRingEnd ℂ) (ψ n) :=
        Finset.sum_comm
    _ = ∑ n : ZMod N,
          (∑ m : ZMod N, hamiltonianKernel N n m * φ m) *
            (starRingEnd ℂ) (ψ n) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.sum_mul]

/-- **The branch choice**: every eigenvalue of the Hamiltonian lies in
`[0, 2π)` - the source's restriction of the periodic Hamiltonian to its
principal branch, realized by the spectrum itself. -/
@[zil_level physical_theorem]
theorem hamiltonianOp_eigenvalue_mem_Ico (l : ZMod N) :
    (2 * π * (l.val : ℝ) / N) ∈ Set.Ico 0 (2 * π) := by
  rw [Set.mem_Ico]
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  constructor
  · positivity
  · rw [div_lt_iff₀ hN]
    have hval : ((l.val : ℝ)) < N := by exact_mod_cast ZMod.val_lt l
    calc 2 * π * (l.val : ℝ) < 2 * π * N :=
          mul_lt_mul_of_pos_left hval (by positivity)
      _ = 2 * π * N := rfl

/-- **The step unitary is the exponential of the Hamiltonian on the
eigenbasis**: the eigenphase of the quantized shift is `e^(-iE)` at the
operator eigenvalue `E = 2πk/N` - the per-mode form of `U = e^(-iH)`. -/
@[zil_level bridge_theorem]
theorem eigenphase_eq_exp_neg_energy (k : ZMod N) :
    ZMod.stdAddChar (-k)
      = Complex.exp (-(Complex.I) * (2 * π * (k.val : ℝ) / N)) := by
  have hk : (-k : ZMod N) = (((-(k.val : ℤ)) : ℤ) : ZMod N) := by
    push_cast [ZMod.natCast_zmod_val]
    rfl
  rw [hk, ZMod.stdAddChar_coe]
  congr 1
  have hN : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

/-- The weighted geometric sum identity behind the resummation. -/
lemma weighted_geom_sum_mul (ζ : ℂ) (n : ℕ) :
    (ζ - 1) * ∑ j ∈ Finset.range n, (j : ℂ) * ζ ^ j
      = ((n : ℂ) - 1) * ζ ^ n - (∑ j ∈ Finset.range n, ζ ^ j) + 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (f := fun j => ζ ^ j)]
      push_cast
      ring_nf
      ring_nf at ih
      linear_combination ih

/-- Sums over the states are sums over the residue range. -/
lemma sum_reindex (f : ℕ → ℂ) :
    ∑ k : ZMod N, f k.val = ∑ j ∈ Finset.range N, f j := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  exact Fin.sum_univ_eq_sum_range (fun j => f j) (M + 1)

/-- The character at a multiple is the power of the character. -/
lemma stdAddChar_mul_eq_pow (d k : ZMod N) :
    ZMod.stdAddChar (k * d) = ZMod.stdAddChar d ^ k.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val (a := k)]
  rw [← AddChar.mulShift_apply, AddChar.mulShift_spec']

/-- The character is an `N`-th root of unity. -/
lemma stdAddChar_pow_card (d : ZMod N) :
    ZMod.stdAddChar d ^ N = 1 := by
  rw [← AddChar.mulShift_spec', AddChar.mulShift_apply, ZMod.natCast_self,
    zero_mul, AddChar.map_zero_eq_one]

/-- **The resolvent resummation** (the closed form behind Eq. NHam): at a
nonzero relative position the energy-weighted character sum closes in
resolvent form, `(ζ - 1) · S = N`. -/
@[zil_level physical_theorem]
theorem energy_sum_resolvent {d : ZMod N} (hd : d ≠ 0) :
    (ZMod.stdAddChar d - 1) *
      ∑ k : ZMod N, (k.val : ℂ) * ZMod.stdAddChar (k * d) = (N : ℂ) := by
  have hpow : ∑ k : ZMod N, (k.val : ℂ) * ZMod.stdAddChar (k * d)
      = ∑ j ∈ Finset.range N, (j : ℂ) * ZMod.stdAddChar d ^ j := by
    rw [← sum_reindex N (fun j => (j : ℂ) * ZMod.stdAddChar d ^ j)]
    exact Finset.sum_congr rfl fun k _ => by rw [stdAddChar_mul_eq_pow]
  have hG : ∑ j ∈ Finset.range N, ZMod.stdAddChar d ^ j = 0 := by
    rw [← sum_reindex N (fun j => ZMod.stdAddChar d ^ j)]
    calc ∑ k : ZMod N, ZMod.stdAddChar d ^ k.val
        = ∑ k : ZMod N, ZMod.stdAddChar (d * k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← stdAddChar_mul_eq_pow]
          congr 1
          ring
      _ = 0 := by
          rw [sum_stdAddChar_mul, if_neg hd]
  rw [hpow, weighted_geom_sum_mul, stdAddChar_pow_card, hG]
  ring

/-- **The diagonal resummation** (the constant term of Eq. NHam): twice the
energy-weighted sum at coincident sites is `N(N-1)`. -/
@[zil_level physical_theorem]
theorem energy_sum_diagonal :
    (2 : ℂ) * ∑ k : ZMod N, ((k.val : ℂ)) = (N : ℂ) * ((N : ℂ) - 1) := by
  rw [sum_reindex N (fun j => (j : ℂ))]
  have h1 : (1 : ℕ) ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have h := congrArg (fun t : ℕ => (t : ℂ)) (Finset.sum_range_id_mul_two N)
  push_cast [Nat.cast_sub h1] at h
  linear_combination h

/-- The half-angle factorization of `e^(iθ) - 1`. -/
lemma exp_mul_I_sub_one (θ : ℝ) :
    Complex.exp ((θ : ℝ) * Complex.I) - 1
      = Complex.exp (((θ / 2 : ℝ)) * Complex.I)
          * (2 * Complex.I * ((Real.sin (θ / 2) : ℝ) : ℂ)) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  have hcos := Real.cos_two_mul (θ / 2)
  have hsin := Real.sin_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ from by ring] at hcos hsin
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, hcos, hsin]
  have hpy : ((Real.cos (θ / 2) : ℂ)) ^ 2 + ((Real.sin (θ / 2) : ℂ)) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (θ / 2)
  have hC : Complex.cos ((θ : ℂ) / 2) = ((Real.cos (θ / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cos]
    norm_cast
  have hS : Complex.sin ((θ : ℂ) / 2) = ((Real.sin (θ / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sin]
    norm_cast
  push_cast
  rw [hC, hS]
  linear_combination (2 : ℂ) * hpy +
    (-(2 : ℂ) * ((Real.sin (θ / 2) : ℝ) : ℂ) ^ 2) * Complex.I_sq

/-! ## The oscillator ladder: the continuum clock with the half-quantum
offset -/

open QuantumMechanics.OneDimension in
/-- **The oscillator ladder has the rotator spacing**: adjacent levels differ
by the constant quantum `ℏω` - the equally spaced spectrum of a periodic
clock, the operator-level shadow of the automaton spacing `2π/N` per step. -/
@[zil_level bridge_theorem]
theorem oscillator_ladder_spacing (Q : HarmonicOscillator) (n : ℕ) :
    HarmonicOscillator.eigenValue Q (n + 1) - HarmonicOscillator.eigenValue Q n
      = Constants.ℏ * Q.ω := by
  unfold HarmonicOscillator.eigenValue
  push_cast
  ring

open QuantumMechanics.OneDimension in
/-- **The oscillator is the rotator ladder with the half-quantum offset**:
`E_n = n·ℏω + ℏω/2` - the clock spectrum shifted by the constant
`δE = ℏω/2`, exactly the energy-offset freedom of the periodic automaton. -/
@[zil_level bridge_theorem]
theorem oscillator_eq_ladder_plus_offset (Q : HarmonicOscillator) (n : ℕ) :
    HarmonicOscillator.eigenValue Q n
      = (n : ℝ) * (Constants.ℏ * Q.ω) + (Constants.ℏ * Q.ω) / 2 := by
  unfold HarmonicOscillator.eigenValue
  ring

open QuantumMechanics.OneDimension in
/-- **Anti-periodicity at the classical period**: the half-quantum offset
makes every oscillator eigenphase return to `-1` after one classical period -
the Maslov half-shift separating the oscillator from the plain rotator
clock. -/
@[zil_level bridge_theorem]
theorem oscillator_antiperiodic (Q : HarmonicOscillator) (n : ℕ)
    (h : Constants.ℏ * Q.ω ≠ 0) :
    Complex.exp (-(Complex.I) * (HarmonicOscillator.eigenValue Q n : ℝ)
        * ((2 * π / (Constants.ℏ * Q.ω) : ℝ))) = -1 := by
  have harg : -(Complex.I) * ((HarmonicOscillator.eigenValue Q n : ℝ) : ℂ)
      * (((2 * π / (Constants.ℏ * Q.ω) : ℝ)) : ℂ)
      = ((-(n : ℤ) : ℤ) : ℂ) * (2 * π * Complex.I) + -(π * Complex.I) := by
    unfold HarmonicOscillator.eigenValue
    have hℏ : ((Constants.ℏ : ℝ)) ≠ 0 := left_ne_zero_of_mul h
    have hω : Q.ω ≠ 0 := right_ne_zero_of_mul h
    have hℏ' : (((Constants.ℏ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℏ
    have hω' : ((Q.ω : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω
    push_cast
    field_simp
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul,
    Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

end Physlib.QuantumMechanics.CyclicAutomatonSpectrum

end

open Physlib.QuantumMechanics.CyclicAutomatonSpectrum in
#physlib_axiom_clean_all [
  cyclicStateStep_apply,
  shiftStateStep_ne,
  koopman_cyclicShift_fourierMode,
  cyclicShift_eigenphase,
  cyclicShift_iterate,
  cyclicShift_iterate_period,
  cyclicShift_fixed_free,
  zero_mode_stationary,
  zero_mode_isPhysical,
  cyclic_automaton_spectrum,
  chineseRemainder_intertwines,
  prod_shift_period,
  koopman_iterate_fourierMode,
  discrete_clock_eq_continuous,
  tendsto_strobe_phase,
  strobeMap_injective,
  strobe_conjugacy,
  rotation_tick_eq_primitive_root,
  hopf_cycle_strobe_automaton,
  sum_stdAddChar_mul,
  stdAddChar_conj,
  hamiltonianKernel_hermitian,
  hamiltonianKernel_fourierMode,
  hamiltonianOp_fourierMode,
  hamiltonianOp_symmetric,
  hamiltonianOp_eigenvalue_mem_Ico,
  eigenphase_eq_exp_neg_energy,
  weighted_geom_sum_mul,
  sum_reindex,
  stdAddChar_mul_eq_pow,
  stdAddChar_pow_card,
  energy_sum_resolvent,
  energy_sum_diagonal,
  exp_mul_I_sub_one,
  oscillator_ladder_spacing,
  oscillator_eq_ladder_plus_offset,
  oscillator_antiperiodic ]

open Physlib.QuantumMechanics.CyclicAutomatonSpectrum in
#physlib_non_vacuous_all [
  shiftStateStep_ne,
  koopman_cyclicShift_fourierMode,
  cyclicShift_eigenphase,
  cyclicShift_iterate,
  cyclicShift_iterate_period,
  cyclicShift_fixed_free,
  zero_mode_stationary,
  zero_mode_isPhysical,
  cyclic_automaton_spectrum,
  chineseRemainder_intertwines,
  prod_shift_period,
  koopman_iterate_fourierMode,
  discrete_clock_eq_continuous,
  tendsto_strobe_phase,
  strobeMap_injective,
  strobe_conjugacy,
  rotation_tick_eq_primitive_root,
  hopf_cycle_strobe_automaton,
  sum_stdAddChar_mul,
  stdAddChar_conj,
  hamiltonianKernel_hermitian,
  hamiltonianKernel_fourierMode,
  hamiltonianOp_fourierMode,
  hamiltonianOp_symmetric,
  hamiltonianOp_eigenvalue_mem_Ico,
  eigenphase_eq_exp_neg_energy,
  weighted_geom_sum_mul,
  sum_reindex,
  stdAddChar_mul_eq_pow,
  stdAddChar_pow_card,
  energy_sum_resolvent,
  energy_sum_diagonal,
  exp_mul_I_sub_one,
  oscillator_ladder_spacing,
  oscillator_eq_ladder_plus_offset,
  oscillator_antiperiodic ]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.koopman_cyclicShift_fourierMode where
  formalizes @ "claim:the-discrete-fourier-modes-diagonalize-the-quantized-cyclic-automaton",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548",
  supported_by @ "lean:Physlib.QuantumMechanics.KoopmanQuantization.koopman"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.cyclicShift_eigenphase where
  formalizes @ "claim:the-cyclic-automaton-energy-spectrum-is-two-pi-k-over-n-per-step",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548",
  caveat @ "claim:energies-are-defined-modulo-two-pi-and-a-constant-offset-the-hamiltonian-operator-itself-is-not-constructed"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.cyclicShift_iterate_period where
  formalizes @ "claim:the-cyclic-automaton-recurs-with-exact-period-n",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.bijective_global_period"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.zero_mode_isPhysical where
  formalizes @ "claim:finite-period-dynamics-carries-normalizable-stationary-states-without-fixed-points",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.KoopmanQuantization.stationary_vanishes_on_infinite_orbit",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.HamiltonianConstraint",
  caveat @ "claim:this-is-the-finite-orbit-complement-of-the-infinite-orbit-exclusion-not-a-full-spectral-decomposition"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.cyclic_automaton_spectrum where
  formalizes @ "claim:the-simple-periodic-automaton-quantizes-to-a-discrete-spectrum-with-exact-recurrence",
  epistemic_status @ "conditional-model",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548",
  supported_by @ "paper:page-wootters-1983-evolution-without-evolution-dynamics-described-by-stationary-observables",
  caveat @ "claim:the-hamiltonian-operator-its-branch-choice-and-the-continuum-limit-are-not-constructed"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.chineseRemainder_intertwines where
  formalizes @ "claim:coprime-cyclic-automata-combine-into-one-by-the-chinese-remainder-equivalence",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548",
  supported_by @ "lean:ZMod.chineseRemainder"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.prod_shift_period where
  formalizes @ "claim:the-product-of-coprime-cyclic-automata-recurs-with-the-product-period",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.koopman_iterate_fourierMode where
  formalizes @ "claim:the-discrete-clock-equation-solves-in-closed-form-with-powered-eigenphases",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.discrete_clock_eq_continuous where
  formalizes @ "claim:the-quantum-evolution-equals-the-deterministic-automaton-at-every-integer-tick",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548",
  caveat @ "claim:per-mode-phase-identity-at-ticks-the-hamiltonian-operator-is-not-constructed"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.tendsto_strobe_phase where
  formalizes @ "claim:the-stroboscopic-clock-phase-converges-to-the-continuous-schrodinger-phase-as-the-tick-vanishes",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548",
  caveat @ "claim:phase-level-continuum-limit-for-fixed-energy-no-operator-convergence-or-harmonic-oscillator-construction"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.strobe_conjugacy where
  formalizes @ "claim:the-cyclic-automaton-is-the-stroboscopic-sampling-of-the-uniform-rotation-on-the-roots-of-unity",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.ClassicalMechanics.HopfBifurcationNormalForm.rotationField",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.rotation_tick_eq_primitive_root where
  formalizes @ "claim:the-continuous-clock-tick-lands-on-the-primitive-root-of-unity",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.ClassicalMechanics.HopfBifurcationNormalForm.hopfField_on_cycle"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.hopf_cycle_strobe_automaton where
  formalizes @ "claim:the-bifurcation-born-clock-strobes-to-the-cyclic-automaton-closing-the-clock-chain",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.ClassicalMechanics.HopfBifurcationNormalForm.hopfField_on_cycle",
  supported_by @ "lean:Physlib.Gravity.Canonical.KucharWDWSplit",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548",
  caveat @ "claim:the-gravity-link-is-the-shared-timeless-constraint-structure-of-the-problem-of-time-not-a-derivation-of-gravitational-dynamics"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.sum_stdAddChar_mul where
  formalizes @ "claim:character-orthogonality-sums-to-the-state-count-on-the-trivial-multiple-and-vanishes-otherwise",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:ZMod.isPrimitive_stdAddChar"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.hamiltonianKernel_hermitian where
  formalizes @ "claim:the-ontological-basis-hamiltonian-kernel-is-hermitian",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.hamiltonianKernel_fourierMode where
  formalizes @ "claim:the-ontological-basis-hamiltonian-kernel-reproduces-the-two-pi-k-over-n-spectrum-including-the-ground-state",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548",
  caveat @ "claim:kernel-level-matrix-elements-the-operator-on-the-amplitude-space-and-the-tan-resummed-form-are-not-constructed"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.hamiltonianOp_fourierMode where
  formalizes @ "claim:the-hamiltonian-operator-on-the-amplitude-space-has-the-fourier-modes-as-eigenvectors",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.hamiltonianOp_symmetric where
  formalizes @ "claim:the-hamiltonian-operator-is-symmetric-on-the-amplitude-space",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:lp.inner_eq_tsum"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.hamiltonianOp_eigenvalue_mem_Ico where
  formalizes @ "claim:the-hamiltonian-spectrum-realizes-the-zero-to-two-pi-principal-branch",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.eigenphase_eq_exp_neg_energy where
  formalizes @ "claim:the-step-unitary-is-the-exponential-of-the-hamiltonian-on-the-eigenbasis",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548",
  caveat @ "claim:per-mode-form-the-operator-exponential-identity-is-not-taken"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.energy_sum_resolvent where
  formalizes @ "claim:the-energy-weighted-character-sum-closes-in-resolvent-form-the-resummation-behind-the-cotangent-hamiltonian",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548",
  caveat @ "claim:resolvent-and-half-angle-factorization-proved-the-cotangent-presentation-is-not-assembled"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.oscillator_ladder_spacing where
  formalizes @ "claim:the-oscillator-ladder-has-the-constant-rotator-spacing",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:QuantumMechanics.OneDimension.HarmonicOscillator.eigenValue"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.oscillator_eq_ladder_plus_offset where
  formalizes @ "claim:the-oscillator-spectrum-is-the-clock-ladder-shifted-by-the-half-quantum-offset",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:QuantumMechanics.OneDimension.HarmonicOscillator.eigenValue",
  supported_by @ "paper:hooft-2014-the-cellular-automaton-interpretation-of-quantum-mechanics-1405-1548"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.oscillator_antiperiodic where
  formalizes @ "claim:every-oscillator-eigenphase-returns-to-minus-one-after-one-classical-period",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:QuantumMechanics.OneDimension.HarmonicOscillator.eigenValue",
  caveat @ "claim:the-maslov-half-shift-reading-is-standard-only-the-phase-identity-is-proved"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.cyclicStateStep_apply where
  formalizes @ "claim:the-finite-cyclic-step-is-the-koopman-operator-of-the-basis-cycle",
  supported_by @ "lean:Physlib.QuantumMechanics.KoopmanQuantization.koopman",
  supported_by @ "lean:Physlib.QuantumMechanics.KoopmanQuantization.koopman_norm_eq",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:a-finite-cyclic-age-is-zmod-valued-and-not-a-monotone-real-clock"

zil attach Physlib.QuantumMechanics.CyclicAutomatonSpectrum.shiftStateStep_ne where
  formalizes @ "claim:the-unit-shifted-cyclic-state-steps-are-genuinely-distinct-unitaries",
  supported_by @ "lean:Physlib.QuantumMechanics.KoopmanQuantization.koopman_single"

zil_file_contract physlib.cyclicAutomatonSpectrum where
  promises "The quantized simple periodic automaton: the cyclic shift on N ontological states lifts through the general Koopman quantization to a bundled surjective linear isometry cyclicStateStep on l2, its arbitrary-residue shifted presentations are genuinely distinct unitaries, the discrete Fourier modes built from the standard additive character diagonalize the step with eigenphases e to the minus two pi i k over N - the discrete energy spectrum - the automaton recurs with exact period N and moves every state for N above one, the constant mode satisfies the Page-Wootters timeless constraint, coprime automata combine by the Chinese remainder equivalence, the discrete clock equation solves in closed form and equals the continuous Schrodinger phase at every tick with the stroboscopic phase converging as the tick vanishes, and the bifurcation-born uniform clock strobes onto the automaton through the injective roots-of-unity embedding - closing the clock chain against the Hopf normal form and the canonical problem-of-time constraint structure."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.KoopmanQuantization.koopman",
    "lean:Physlib.QuantumMechanics.KoopmanQuantization.koopmanStateStep",
    "lean:Physlib.QuantumMechanics.KoopmanQuantization.koopmanTimelessConstraint",
    "lean:ZMod.stdAddChar", "lean:AddChar.map_add_eq_mul",
    "lean:Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.bijective_global_period",
    "lean:Physlib.ClassicalMechanics.HopfBifurcationNormalForm.hopfField_on_cycle",
    "lean:Physlib.Gravity.Canonical.KucharWDWSplit"]
  forbids_substitutes ["the operator identity U equals the exponential of minus i H beyond the per-mode eigenphase form",
    "the cotangent presentation of the resolvent resummation - the resolvent identity and the half-angle factorization are provided",
    "the oscillator position-space eigenfunctions or ladder-operator algebra beyond the eigenvalue spacing and offset",
    "an operator-level continuum limit or harmonic-oscillator construction beyond the phase-level tick agreement and vanishing-tick convergence",
    "the Zeeman-atom identification as a formalized claim",
    "Fourier completeness or orthogonality relations beyond the per-mode eigenphase identities",
    "a derivation of gravitational dynamics: the problem-of-time link is the shared timeless constraint structure"]
  witnessed_by [
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.cyclicStateStep_apply,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.shiftStateStep_ne,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.koopman_cyclicShift_fourierMode,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.cyclicShift_eigenphase,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.cyclicShift_iterate,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.cyclicShift_iterate_period,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.cyclicShift_fixed_free,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.zero_mode_stationary,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.zero_mode_isPhysical,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.cyclic_automaton_spectrum,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.chineseRemainder_intertwines,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.prod_shift_period,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.koopman_iterate_fourierMode,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.discrete_clock_eq_continuous,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.tendsto_strobe_phase,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.strobe_conjugacy,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.rotation_tick_eq_primitive_root,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.hopf_cycle_strobe_automaton,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.sum_stdAddChar_mul,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.hamiltonianKernel_hermitian,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.hamiltonianKernel_fourierMode,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.hamiltonianOp_fourierMode,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.hamiltonianOp_symmetric,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.hamiltonianOp_eigenvalue_mem_Ico,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.eigenphase_eq_exp_neg_energy,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.energy_sum_resolvent,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.energy_sum_diagonal,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.oscillator_ladder_spacing,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.oscillator_eq_ladder_plus_offset,
    Physlib.QuantumMechanics.CyclicAutomatonSpectrum.oscillator_antiperiodic ]

/- ZIL-END -/

#zil_formalization_lint physlib.cyclicAutomatonSpectrum

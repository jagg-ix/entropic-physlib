/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates
public import Physlib.QuantumMechanics.Foundations.RelativeStateConventionality
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumDarwinism
meta import Zil

/-!
# Quantum Darwinism realized in the Everett–Deutsch relative-state machinery (Zurek × Kuypers–Deutsch)

Upgrades `SciamaAdSCPTMeasurementCommunicationDarwinism`: the communication reading of quantum Darwinism is
here **welded to the repo's Everett and Deutsch content** at the density-matrix level.  The identifications are
exact, not analogies:

* **Zurek's branching state (2107.03378 Eq. 1)** `α|↑⟩|ε_↑ε_↑…⟩ + β|↓⟩|ε_↓ε_↓…⟩` **is** the Everett correlated
  ket `MinimalModalOnticDynamics.correlatedKet Ψ χ` (`vec p = Ψ p.1 · χ p.1 p.2`), and his perfect-record
  condition `⟨F_↑|F_↓⟩ = 0` **is** the orthogonality hypothesis `horth`.
* **Zurek's decohered record state (Eq. 4)** `ρ_SF = |α|²|↑⟩⟨↑|⊗|F_↑⟩⟨F_↑| + |β|²…` **is**
  `traceRight_correlatedKet_orthonormal`: orthogonal environmental records force the reduced state diagonal
  with Born entries.
* **Zurek's c-not model of Darwinism** (`N` target qubits imprinted by the control) **is** the Kuypers–Deutsch
  `cnotRecord`/`binaryMemory` machinery of `EverettHeisenbergRelativeStates`.

* `pointer_record_weight_three_faces` — the pointer-record weight in **three derived faces** at once: the
  reduced-density diagonal entry is the Born weight `|Ψ_m|²` (records, Everett); that weight is the fixed point
  of the Deutsch decision-theoretic functional (`deutsch_born_unequal` — **derived**, not postulated); and it is
  the modulus² of the entropic `historyWeight` (`born_diagonal_eq_historyWeight`) — the same imaginary-action
  sector as the arc's decoherence/confinement weights.
* `redundant_register_descriptor` — the observer's memory descriptor of the `N`-fold c-not-imprinted register
  (all records showing the same outcome, Zurek's redundancy) in closed form:
  `binaryMemoryDescriptor (const s) = coeff(s)·(2ⁿ − 1)` — the `N`-record memory of an agreeing environment.
* `darwinism_register_objective` — the register is accurate (`cnotRecord_isAccurate`), exponentially large
  (`2ⁿ` configurations), and carries redundancy `R = N` (`perfectCopy_redundancy_eq`) — Zurek's "quantum spam",
  in the Kuypers–Deutsch record machinery.
* `darwinism_everett_deutsch_synthesis` — the capstone: the three-face weight, the accurate redundant register,
  and **no primitive collapse anywhere** (`everettHeisenberg_excludes_primitive_collapse`) — Zurek's "linearity
  assures that all the branches persist: collapse to one outcome is not in the cards", as a theorem.

Honest scope: the record orthogonality (`horth`) is a hypothesis (perfect records), not derived from dynamics;
the Deutsch face carries the standard decision-theoretic continuity/rationality hypotheses; the register model
is the finite c-not chain.  Everything else is exact reuse of the Foundations machinery.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDarwinismEverettDeutschRecords

open Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates
open Physlib.QuantumMechanics.Foundations.UnitaryDecoherentMeasurement
open Physlib.QuantumMechanics.Foundations.RelativeStateConventionality
open Physlib.QuantumMechanics.Foundations.MinimalModalOnticDynamics
open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumDarwinism
open ComplexConjugate

/-! ## §1. The pointer-record weight in three derived faces -/

/-- **[The pointer-record weight, three faces at once]** — for Zurek's branching state (`correlatedKet Ψ χ`)
with orthogonal environmental records (Eq. 4, `⟨F_m|F_{m'}⟩ = 0`): **(i)** the reduced-density diagonal entry is
the Born weight `|Ψ_m|²` (the record face — Everett relative states); **(ii)** that weight is the fixed point of
the Deutsch decision-theoretic functional (the derived-Born face — `deutsch_born_unequal`, not a postulate); and
**(iii)** it equals `|historyWeight|²` with imaginary action `−log|Ψ_m|²` (the entropic/complex-action face —
the same imaginary-action sector as the arc's decoherence and confinement weights). -/
theorem pointer_record_weight_three_faces
    {dS dE : Type*} [Fintype dS] [Fintype dE] [DecidableEq dS] [DecidableEq dE]
    (Ψ : Ket dS) (χ : dS → Ket dE)
    (horth : ∀ m₁ m₂, m₁ ≠ m₂ → ∑ e, χ m₁ e * conj (χ m₂ e) = 0)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hrat : ∀ (k n : ℕ), 0 < n → k ≤ n → f ((k : ℝ) / (n : ℝ)) = (k : ℝ) / (n : ℝ))
    (m : dS) (hm : Ψ m ≠ 0) (S_R ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    ((MState.pure (correlatedKet Ψ χ)).traceRight).m m m = (Complex.normSq (Ψ m) : ℂ)
      ∧ f (Complex.normSq (Ψ m)) = Complex.normSq (Ψ m)
      ∧ ((MState.pure (correlatedKet Ψ χ)).traceRight).m m m
          = (Complex.normSq (historyWeight S_R (-Real.log (Complex.normSq (Ψ m))) ℏ) : ℂ) := by
  refine ⟨?_, deutsch_born_unequal Ψ f hf hrat m,
    born_diagonal_eq_historyWeight Ψ χ horth m hm S_R ℏ hℏ⟩
  rw [traceRight_correlatedKet_orthonormal Ψ χ horth]
  simp

/-! ## §2. The redundant record register (Zurek's c-not model = Kuypers–Deutsch records) -/

/-- **[The N-record memory of an agreeing environment, in closed form]**
`binaryMemoryDescriptor (const s) = coeff(s)·(2ⁿ − 1)`.  Zurek's redundancy: all `N` c-not-imprinted
environment records show the *same* outcome `s`; the Kuypers–Deutsch binary-memory descriptor of that
agreeing register evaluates in closed form (geometric sum). -/
theorem redundant_register_descriptor (n : ℕ) (s : SpinOutcome) :
    binaryMemoryDescriptor (fun _ : Fin n => s)
      = spinProjectorCoefficient .minus s * (2 ^ n - 1) := by
  unfold binaryMemoryDescriptor
  rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun i => (2 : ℝ) ^ i),
    geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1) n, show ((2 : ℝ) - 1) = 1 by norm_num, div_one]
  ring

/-- **[The Darwinism register is accurate, exponentially large, and `R = N` redundant]** — every c-not record is
accurate (`pointerValue = systemValue`), the `N`-qubit register has `2ⁿ` configurations, and `N` perfect copies
give redundancy `R = N` (`SciamaAdSCPTQuantumDarwinism`): Zurek's "quantum spam" in the Kuypers–Deutsch record
machinery. -/
theorem darwinism_register_objective (n : ℕ) (s : SpinOutcome) :
    (cnotRecord s).IsAccurate
      ∧ Fintype.card (Fin n → SpinOutcome) = 2 ^ n
      ∧ perfectCopyRedundancy (n : ℝ) = (n : ℝ) :=
  ⟨cnotRecord_isAccurate s, spinOutcome_register_card n, perfectCopy_redundancy_eq _⟩

/-! ## §3. The capstone: Darwinism in Everett–Deutsch, no collapse anywhere -/

/-- **[Quantum Darwinism realized in Everett–Deutsch, collapse-free]** — the three-face pointer-record weight
(§1), the accurate exponential register (§2), and **no step is a primitive collapse**
(`everettHeisenberg_excludes_primitive_collapse`): Zurek's "linearity assures that all the branches persist:
collapse to one outcome is not in the cards", as a theorem over the four measurement steps. -/
theorem darwinism_everett_deutsch_synthesis
    {dS dE : Type*} [Fintype dS] [Fintype dE] [DecidableEq dS] [DecidableEq dE]
    (Ψ : Ket dS) (χ : dS → Ket dE)
    (horth : ∀ m₁ m₂, m₁ ≠ m₂ → ∑ e, χ m₁ e * conj (χ m₂ e) = 0)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hrat : ∀ (k n : ℕ), 0 < n → k ≤ n → f ((k : ℝ) / (n : ℝ)) = (k : ℝ) / (n : ℝ))
    (m : dS) (hm : Ψ m ≠ 0) (S_R ℏ : ℝ) (hℏ : ℏ ≠ 0) (s : SpinOutcome) :
    (((MState.pure (correlatedKet Ψ χ)).traceRight).m m m = (Complex.normSq (Ψ m) : ℂ)
        ∧ f (Complex.normSq (Ψ m)) = Complex.normSq (Ψ m)
        ∧ ((MState.pure (correlatedKet Ψ χ)).traceRight).m m m
            = (Complex.normSq (historyWeight S_R (-Real.log (Complex.normSq (Ψ m))) ℏ) : ℂ))
      ∧ (cnotRecord s).IsAccurate
      ∧ (¬ IsPrimitiveCollapse .unitaryInteraction
          ∧ ¬ IsPrimitiveCollapse .environmentalDecoherence
          ∧ ¬ IsPrimitiveCollapse .lindbladReducedDynamics
          ∧ ¬ IsPrimitiveCollapse .bornWeightedConditioning) :=
  ⟨pointer_record_weight_three_faces Ψ χ horth f hf hrat m hm S_R ℏ hℏ,
    cnotRecord_isAccurate s,
    everettHeisenberg_excludes_primitive_collapse⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDarwinismEverettDeutschRecords

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDarwinismEverettDeutschRecords.pointer_record_weight_three_faces where
  formalizes @ "claim:the-quantum-darwinism-pointer-record-weight-is-simultaneously-the-orthogonal-record-born-diagonal-the-deutsch-decision-theoretic-fixed-point-and-the-entropic-history-weight-modulus",
  supported_by @ "paper:zurek-2021-emergence-of-the-classical-from-within-the-quantum-universe",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.MinimalModalOnticDynamics.traceRight_correlatedKet_orthonormal",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.deutsch_born_unequal",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.MinimalModalOnticDynamics.born_diagonal_eq_historyWeight",
  caveat @ "epistemic:perfect-record-orthogonality-is-a-hypothesis-not-derived-from-dynamics"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDarwinismEverettDeutschRecords.redundant_register_descriptor where
  formalizes @ "claim:the-n-fold-cnot-imprinted-agreeing-environment-register-has-closed-form-binary-memory-descriptor-two-to-the-n-minus-one-times-the-outcome-coefficient",
  supported_by @ "paper:zurek-2021-emergence-of-the-classical-from-within-the-quantum-universe",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates.binaryMemoryDescriptor_eq_natCast",
  caveat @ "epistemic:finite-cnot-chain-register-model-with-perfect-copies"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDarwinismEverettDeutschRecords.darwinism_everett_deutsch_synthesis where
  formalizes @ "claim:quantum-darwinism-is-realized-in-the-everett-deutsch-relative-state-machinery-with-no-primitive-collapse-step",
  requires @ "claim:the-quantum-darwinism-pointer-record-weight-is-simultaneously-the-orthogonal-record-born-diagonal-the-deutsch-decision-theoretic-fixed-point-and-the-entropic-history-weight-modulus",
  supported_by @ "paper:zurek-2021-emergence-of-the-classical-from-within-the-quantum-universe",
  supported_by @ "paper:kuypers-deutsch-2021-everettian-relative-states-in-the-heisenberg-picture",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates.everettHeisenberg_excludes_primitive_collapse",
  caveat @ "epistemic:records-and-register-are-finite-models-the-objectivity-scope-is-the-formalized-redundancy-not-full-open-system-dynamics"

/- ZIL-END -/

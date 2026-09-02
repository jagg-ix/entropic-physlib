/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Thermodynamics.ComputationLandauer
public import Mathlib.Computability.Halting
meta import Zil

/-!
# No constructor decides the halting problem — the computability obstruction

The impossibility face of thermodynamics-from-computability: a physical device implementing a task
whose success would decide the halting set cannot exist, because any computably-driven finite
channel induces a computable decision procedure, and the halting set is undecidable (Turing;
Mathlib's `ComputablePred.halting_problem`). This module states it on the repo's own constructor
carrier — the deterministic channel `computationKernel` of `ComputationLandauer`, the same kernel
whose erasure steps carry the Landauer cost:

* **§A the decision-map form.** No computable `f : Code → Bool` decides halting-on-empty-input; no
  computable total driver `f : ℕ → ℕ` decides it on encodings by hitting `1`.
* **§B the constructor form.** No `computationKernel f` with computable driver decides halting by
  placing its output mass on the register value `1` — the physical-channel statement: the kernel
  applied to an encoded machine has `κ(⟨e⟩){1} = 1` exactly on halting `e` for *no* computable `f`.

The weld to thermodynamics: `ComputationLandauer` justifies its per-step irreversibility flags by
exactly this obstruction — whether a computation "will halt" (and hence whether its history can be
uncomputed for free) is not decidable by any physical constructor of the model, so reversibility is
*declared per step*, never inferred. This module makes that justification a theorem.

What is **not** claimed: impossibility for oracle-equipped or infinite devices, any bound on
*partial* deciders, or a physical-Church-Turing principle — the statements quantify over computable
total drivers of the model's kernels.

## References

* A. M. Turing, *On computable numbers* (1936). D. Deutsch, constructor-theoretic impossibility as
  inspiration (not assumed). Mathlib: `ComputablePred.halting_problem` (Rice's theorem route),
  M. Carneiro's `Nat.Partrec.Code`.
* Repo carriers: `Thermodynamics.ComputationLandauer.computationKernel`, the Landauer erasure-step
  family.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open Physlib.Thermodynamics.ComputationLandauer

@[expose] public section

namespace Physlib.Thermodynamics.ComputationHaltingImpossibility

/-! ## A. The decision-map form -/

/-- **[No computable map decides halting]** there is no computable `f : Code → Bool` with
`f c = true` exactly when machine `c` halts on empty input — Mathlib's halting theorem in the
decision-map form used by the constructor statements below. -/
theorem no_computable_decider_halting :
    ¬ ∃ f : Nat.Partrec.Code → Bool, Computable f ∧
        ∀ c : Nat.Partrec.Code, (f c = true ↔ (c.eval 0).Dom) := by
  rintro ⟨f, hf, hiff⟩
  refine ComputablePred.halting_problem 0 ?_
  rw [ComputablePred.computable_iff]
  exact ⟨f, hf, funext fun c => propext (hiff c).symm⟩

/-- **[No computable total driver decides halting on encodings]** no computable `f : ℕ → ℕ` has
`f ⟨c⟩ = 1` exactly on the halting codes: a total numeric driver — the data of a
`computationKernel` — cannot carry a halting decision. -/
theorem no_computable_natDriver_decides_halting :
    ¬ ∃ f : ℕ → ℕ, Computable f ∧
        ∀ c : Nat.Partrec.Code, (f (Encodable.encode c) = 1 ↔ (c.eval 0).Dom) := by
  rintro ⟨f, hf, hiff⟩
  refine no_computable_decider_halting
    ⟨fun c => f (Encodable.encode c) == 1, ?_, fun c => ?_⟩
  · exact Primrec.beq.to_comp.comp (hf.comp Computable.encode) (Computable.const 1)
  · simpa using hiff c

/-! ## B. The constructor form: the kernel cannot decide halting -/

/-- **[The kernel's mass on `{1}`]** `κ_f(n){1} = 1 ↔ f n = 1`: the deterministic computation
channel places full mass on the register value `1` exactly when its driver outputs `1`. -/
lemma computationKernel_singleton_one (f : ℕ → ℕ) (n : ℕ) :
    computationKernel f n {1} = 1 ↔ f n = 1 := by
  unfold computationKernel
  rw [Kernel.deterministic_apply, Measure.dirac_apply' _ (measurableSet_singleton 1)]
  constructor
  · intro h
    by_contra hne
    rw [Set.indicator_of_notMem (by simpa using hne)] at h
    exact zero_ne_one h
  · intro h
    rw [Set.indicator_of_mem (by simpa using h)]
    rfl

/-- **[No constructor decides the halting problem]** there is no computable total driver `f` whose
computation channel `computationKernel f` — the same deterministic kernel whose erasure steps carry
the Landauer cost — places its output mass on the register value `1` exactly on the halting codes.
The physical-channel form of undecidability: a task whose implementation would decide halting is
impossible for the model's constructors, which is why `ComputationLandauer` *declares*
per-step reversibility instead of inferring it. -/
theorem no_computationKernel_decides_halting :
    ¬ ∃ f : ℕ → ℕ, Computable f ∧
        ∀ c : Nat.Partrec.Code,
          (computationKernel f (Encodable.encode c) {1} = 1 ↔ (c.eval 0).Dom) := by
  rintro ⟨f, hf, hiff⟩
  exact no_computable_natDriver_decides_halting
    ⟨f, hf, fun c => (computationKernel_singleton_one f (Encodable.encode c)).symm.trans (hiff c)⟩

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil_theorem_intent no_computationKernel_decides_halting where
  at_level bridge_theorem
  must_mention [computationKernel]

zil attach no_computable_decider_halting where
  formalizes @ "claim:halting-set-has-no-computable-decision-map",
  supported_by @ "paper:turing-1936",
  supported_by @ "paper:carneiro-2019",
  caveat @ "claim:mathlib-halting-theorem-reshaped-to-decision-map-form"

zil attach no_computationKernel_decides_halting where
  formalizes @ "claim:no-computation-kernel-constructor-decides-halting",
  requires @ "claim:halting-set-has-no-computable-decision-map",
  requires @ "assumption:computable-total-driver",
  supported_by @ "paper:turing-1936",
  supported_by @ "paper:bennett-1973",
  caveat @ "claim:model-constructors-only-no-physical-church-turing-principle"

zil_file_contract physlib.computationHaltingImpossibility where
  promises "The computability obstruction on the repo's constructor carrier: no computable decision map decides the halting set, no computable total numeric driver decides it on encodings, the deterministic computation kernel places mass one on the register value one exactly when its driver outputs one, and therefore no computationKernel with computable driver decides halting by its output mass — the impossibility face of thermodynamics-from-computability, and the formal justification for ComputationLandauer declaring per-step reversibility rather than inferring it."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Thermodynamics.ComputationLandauer.computationKernel",
    "lean:ComputablePred.halting_problem",
    "lean:Nat.Partrec.Code"]
  forbids_substitutes ["a physical Church-Turing principle claimed from model-level impossibility",
    "impossibility for oracle-equipped or infinite devices",
    "bounds on partial or probabilistic deciders, which are not treated"]
  witnessed_by [no_computable_decider_halting, no_computable_natDriver_decides_halting,
    computationKernel_singleton_one, no_computationKernel_decides_halting]

/- ZIL-END -/

end Physlib.Thermodynamics.ComputationHaltingImpossibility

end

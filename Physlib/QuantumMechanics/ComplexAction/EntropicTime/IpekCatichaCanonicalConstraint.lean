/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsCanonicalRepresentation

meta import Zil

/-!
# Linking the Ipek–Caticha super-Hamiltonian constraint to the entropic-dynamics canonical constraint

Connects the Ipek–Caticha matter–gravity super-Hamiltonian constraint (`IpekCatichaMatterGravityConstraint`) with the
repository's entropic-dynamics **canonical constraint** (`EntropicDynamicsCanonicalRepresentation`, Ipek–Abedi–Caticha
Eqs. 38, 66, 67). The Ipek–Caticha constraint `H^G_⊥ + ℋ = 0` is exactly the ED canonical constraint
`H = π_geom + H̃` with the gravitational super-Hamiltonian as the geometric momentum `π_geom` and the Klein–Gordon
matter energy as the ensemble Hamiltonian `H̃`:

* the **Ipek–Caticha constraint is the ED canonical constraint** — `H^G_⊥ + ℋ = canonicalConstraint(H^G_⊥, ℋ)`
  (`ipekCaticha_constraint_is_canonicalConstraint`), the gravitational super-Hamiltonian playing `π_geom`, the
  Klein–Gordon matter playing `H̃`;
* the **constraint fixes the geometric momentum** `H = 0 ⟺ H^G_⊥ = −ℋ` (`ipekCaticha_hamiltonian_constraint`,
  reusing the ED `hamiltonian_constraint`) — the Wheeler–DeWitt-type relation `π_geom = −H̃`, the gravitational
  momentum equal to minus the matter ensemble Hamiltonian;
* the **flat Klein–Gordon matter is the ED ensemble Hamiltonian** `ℋ|_{g=δ} = H̃_⊥|_{ρ=1, Q=0}`
  (`kgMatter_flat_eq_eHamiltonian`) — the Ipek–Caticha Klein–Gordon density (Eq. 100a) is the classical part of the
  ED ensemble Hamiltonian (Eq. 66);
* the **ED ensemble Hamiltonian is the Klein–Gordon matter plus the quantum potential** `H̃ = ℋ + Q`
  (`eHamiltonian_is_kgMatter_plus_quantum`) — the Fisher/Bohm quantum potential `Q = edQuantumPotential` is exactly
  what the Ipek–Caticha classical Klein–Gordon energy is missing to be the *quantum* ensemble Hamiltonian.

So the two constraint formulations are one: the Ipek–Caticha gravitational super-Hamiltonian is the ED geometric
momentum, its Klein–Gordon matter is the classical part of the ED ensemble Hamiltonian, and the Fisher/Bohm quantum
potential completes it — the coupled-gravity constraint `H^G_⊥ + ℋ = 0` on the entropic-dynamics canonical hub.

* **§A — the constraint identification** (`ipekCaticha_constraint_is_canonicalConstraint`,
  `ipekCaticha_hamiltonian_constraint`).
* **§B — matter density and the quantum potential** (`kgMatter_flat_eq_eHamiltonian`,
  `eHamiltonian_is_kgMatter_plus_quantum`).

**Honest layering.** The constraint identity, the Wheeler–DeWitt momentum relation, the flat matter/ensemble
equality, and the quantum-potential completion are exact algebra, reusing `canonicalConstraint`,
`hamiltonian_constraint`, `eHamiltonianDensity`, `edQuantumPotential`, `gravSuperHamiltonian`, and `kgMatterDensity`.


## References

* S. Ipek, A. Caticha, arXiv:2006.05036 (Eqs. 66, 100a); S. Ipek, M. Abedi, A. Caticha, arXiv:1803.07493
  (Eqs. 38, 66, 67). Repo carriers: `EntropicTime.EntropicDynamicsCanonicalRepresentation` (`canonicalConstraint`,
  `eHamiltonianDensity`, `edQuantumPotential`), `EntropicTime.IpekCatichaMatterGravityConstraint`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsCanonicalRepresentation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCanonicalConstraint


/-- **[The Ipek–Caticha constraint is the ED canonical constraint] `H^G_⊥ + ℋ = canonicalConstraint(H^G_⊥, ℋ)`.**
The gravitational super-Hamiltonian is the geometric momentum `π_geom` and the Klein–Gordon matter energy is the
ensemble Hamiltonian `H̃` of the ED canonical constraint (Ipek–Abedi–Caticha Eq. 38). -/
lemma ipekCaticha_constraint_is_canonicalConstraint (κ sqrtg R sqrtg' ginv π gradchi V : ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) :
    gravSuperHamiltonian κ sqrtg R M + kgMatterDensity sqrtg' ginv π gradchi V
      = canonicalConstraint (gravSuperHamiltonian κ sqrtg R M)
          (kgMatterDensity sqrtg' ginv π gradchi V) := rfl

/-- **[The constraint fixes the geometric momentum] `H = 0 ⟺ H^G_⊥ = −ℋ`.** Imposing the Ipek–Caticha
super-Hamiltonian constraint — as the ED canonical constraint — means the gravitational super-Hamiltonian equals
minus the Klein–Gordon matter ensemble Hamiltonian: the Wheeler–DeWitt-type relation `π_geom = −H̃`, reusing the ED
`hamiltonian_constraint`. -/
lemma ipekCaticha_hamiltonian_constraint (κ sqrtg R sqrtg' ginv π gradchi V : ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) :
    canonicalConstraint (gravSuperHamiltonian κ sqrtg R M)
        (kgMatterDensity sqrtg' ginv π gradchi V) = 0
      ↔ gravSuperHamiltonian κ sqrtg R M = -kgMatterDensity sqrtg' ginv π gradchi V :=
  hamiltonian_constraint _ _


/-- **[The flat Klein–Gordon matter is the ED ensemble Hamiltonian] `ℋ|_{g=δ} = H̃_⊥|_{ρ=1, Q=0}`.** At the flat
metric and unit probability, the Ipek–Caticha Klein–Gordon energy density (Eq. 100a) is the classical part of the
entropic-dynamics ensemble Hamiltonian (Eq. 66): kinetic + gradient + potential. -/
lemma kgMatter_flat_eq_eHamiltonian (dΦ dχ V : ℝ) :
    kgMatterDensity 1 1 dΦ dχ V = eHamiltonianDensity 1 dΦ dχ V 0 := by
  unfold kgMatterDensity eHamiltonianDensity
  ring

/-- **[The ED ensemble Hamiltonian is Klein–Gordon matter plus the quantum potential] `H̃ = ℋ + Q`.** The
entropic-dynamics ensemble Hamiltonian (at unit probability) is the Ipek–Caticha classical Klein–Gordon energy plus
the Fisher/Bohm quantum potential `Q = edQuantumPotential` — the quantum potential is exactly what makes the
Klein–Gordon matter the *quantum* ensemble Hamiltonian. -/
lemma eHamiltonian_is_kgMatter_plus_quantum (dΦ dχ V lam dρ : ℝ) :
    eHamiltonianDensity 1 dΦ dχ V (edQuantumPotential lam 1 dρ)
      = kgMatterDensity 1 1 dΦ dχ V + edQuantumPotential lam 1 dρ := by
  unfold eHamiltonianDensity kgMatterDensity
  ring

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCanonicalConstraint

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCanonicalConstraint.ipekCaticha_hamiltonian_constraint where
  formalizes @ "claim:imposing-the-coupled-gravity-super-hamiltonian-constraint-forces-the-gravitational-super-hamiltonian-to-equal-minus-the-klein-gordon-matter-energy-the-wheeler-dewitt-relation-pi-geom-equals-minus-h-tilde",
  supported_by @ "paper:ipek-caticha-entropic-dynamics-quantum-gravity-functional-schrodinger-constraints"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCanonicalConstraint.eHamiltonian_is_kgMatter_plus_quantum where
  formalizes @ "claim:the-entropic-dynamics-ensemble-hamiltonian-is-exactly-the-classical-klein-gordon-matter-energy-plus-the-fisher-bohm-quantum-potential"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCanonicalConstraint.kgMatter_flat_eq_eHamiltonian where
  formalizes @ "claim:in-the-flat-unit-probability-limit-the-ipek-caticha-klein-gordon-energy-density-coincides-with-the-classical-part-of-the-entropic-dynamics-ensemble-hamiltonian"

zil_file_contract physlib.ipekCatichaCanonicalConstraint where
  promises "The Ipek-Caticha super-Hamiltonian constraint as the entropic-dynamics canonical constraint. Imposing the coupled-gravity constraint forces the gravitational super-Hamiltonian to equal minus the Klein-Gordon matter energy -- the Wheeler-DeWitt relation pi_geom = -H_tilde (ipekCaticha_hamiltonian_constraint). The entropic-dynamics ensemble Hamiltonian is exactly the classical Klein-Gordon matter energy plus the Fisher/Bohm quantum potential (eHamiltonian_is_kgMatter_plus_quantum), coinciding with the Klein-Gordon energy density in the flat unit-probability limit (kgMatter_flat_eq_eHamiltonian)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsCanonicalRepresentation.canonicalConstraint",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsCanonicalRepresentation.eHamiltonianDensity",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint.gravSuperHamiltonian",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint.kgMatterDensity"]
  forbids_substitutes ["the full functional-derivative / smearing structure of the Wheeler-DeWitt equation and the operator ordering of the quantum constraint, which are the cited canonical-quantum-gravity infrastructure",
    "any claim that the Wheeler-DeWitt equation is solved; only the algebraic constraint relation between the gravitational and matter super-Hamiltonians is carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCanonicalConstraint.ipekCaticha_hamiltonian_constraint,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCanonicalConstraint.eHamiltonian_is_kgMatter_plus_quantum,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCanonicalConstraint.kgMatter_flat_eq_eHamiltonian]

/- ZIL-END -/

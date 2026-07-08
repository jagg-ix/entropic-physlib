/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingComplexStructureSchrodinger

/-!
# The functional Schrödinger equation of coupled-gravity entropic dynamics (Ipek–Caticha §10)

Formalizes the structure of the Ipek–Caticha functional Schrödinger equation (arXiv:2006.05036, Eqs. 105–108),

`i ∂_t Ψ = ∫ dx (N_x Ĥ_⊥x + N^i_x Ĥ_ix) Ψ`,

the emergence of quantum evolution from the entropic dynamics: the wave functional `Ψ` evolves under the smeared
Hamiltonian generator built from the lapse `N` times the **normal** (super-Hamiltonian) operator `Ĥ_⊥` and the
shift `N^i` times the **tangential** (super-momentum) operator `Ĥ_i`. At the operator level (single mode `ℂ`) the
smeared generator is `𝓗(N, N^i) = N·Ĥ_⊥ + N^i·Ĥ_i`, and the two essential structural facts are:

* the **smeared generator acts as `N·Ĥ_⊥ + N^i·Ĥ_i`** (`smearedSchrodinger_apply`) — the normal/tangential split of
 Eq. 108: lapse times the super-Hamiltonian plus shift times the super-momentum;
* the **generator is `ℂ`-linear, so the flow superposes** (`smearedSchrodinger_superposition`) — for *fixed*
 operators `Ĥ_⊥, Ĥ_i` (fixed background metric) the functional Schrödinger equation is linear, reusing the
 Hamilton–Killing `schrodinger_superposition`; this is exactly the superposition that the state-sourced metric
 (`IpekCatichaSuperpositionViolation`) destroys;
* the **generator is linear in the lapse and shift** (`smearedSchrodinger_add_deformation`) — `𝓗` depends linearly
 on the deformation `(N, N^i)`, the freedom of foliation: any choice of lapse and shift picks a slicing of
 space-time, and the generator combines them linearly.

So the coupled-gravity entropic dynamics has functional Schrödinger form `i∂_tΨ = 𝓗(N,N^i)Ψ` with the smeared
generator the lapse-weighted super-Hamiltonian plus shift-weighted super-momentum, `ℂ`-linear (superposition) for a
fixed background and linear in the foliation choice — the linear Schrödinger flow whose superposition is broken only
once the metric in `Ĥ_⊥` is sourced by `Ψ`.

* **§A — the smeared functional Schrödinger generator** (`smearedSchrodingerGenerator`,
 `smearedSchrodinger_apply`).
* **§B — linearity: superposition and foliation freedom** (`smearedSchrodinger_superposition`,
 `smearedSchrodinger_add_deformation`).

The normal/tangential split, the `ℂ`-linearity of the flow, and the linearity in the
lapse/shift are exact algebra on `ℂ`-linear operators, reusing `schrodinger_superposition`. The functional
derivatives `Ĥ_⊥ = −(1/2√g)δ²/δχ² + …`, the Poisson-bracket derivation (Eqs. 105–107), and the field-theoretic
smearing are the referenced content. The state-dependence of `Ĥ_⊥` (the nonlinearity) is in
`IpekCatichaSuperpositionViolation`. No new axioms.

## References

* S. Ipek, A. Caticha, arXiv:2006.05036 (Eqs. 105–108). Repo structure:
 `EntropicTime.HamiltonKillingComplexStructureSchrodinger` (`schrodinger_superposition`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingComplexStructureSchrodinger

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger

/-! ## §A — the smeared functional Schrödinger generator -/

/-- **The smeared functional Schrödinger generator** `𝓗(N, N^i) = N·Ĥ_⊥ + N^i·Ĥ_i` (Ipek–Caticha Eq. 108) — the
lapse `N` times the normal super-Hamiltonian operator `Ĥ_⊥` plus the shift `N^i` times the tangential super-momentum
operator `Ĥ_i`, the `ℂ`-linear generator of the functional Schrödinger evolution `i∂_tΨ = 𝓗Ψ`. -/
noncomputable def smearedSchrodingerGenerator (N Ni : ℝ) (Hperp Hi : ℂ →ₗ[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ :=
  (N : ℂ) • Hperp + (Ni : ℂ) • Hi

/-- **[The generator acts as `N·Ĥ_⊥ + N^i·Ĥ_i`].** The normal/tangential split of the functional Schrödinger
generator (Eq. 108): lapse times the super-Hamiltonian applied to `Ψ` plus shift times the super-momentum. -/
theorem smearedSchrodinger_apply (N Ni : ℝ) (Hperp Hi : ℂ →ₗ[ℂ] ℂ) (ψ : ℂ) :
    smearedSchrodingerGenerator N Ni Hperp Hi ψ = (N : ℂ) * Hperp ψ + (Ni : ℂ) * Hi ψ := by
  simp only [smearedSchrodingerGenerator, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

/-! ## §B — linearity: superposition and foliation freedom -/

/-- **[The functional Schrödinger flow superposes] `𝓗(c₁ψ₁ + c₂ψ₂) = c₁𝓗ψ₁ + c₂𝓗ψ₂`.** For fixed operators
`Ĥ_⊥, Ĥ_i` (fixed background metric) the smeared generator is `ℂ`-linear, so the functional Schrödinger flow
superposes — reusing the Hamilton–Killing `schrodinger_superposition`. This linearity is exactly what the
state-sourced metric of coupled gravity destroys. -/
theorem smearedSchrodinger_superposition (N Ni : ℝ) (Hperp Hi : ℂ →ₗ[ℂ] ℂ) (c₁ c₂ ψ₁ ψ₂ : ℂ) :
    smearedSchrodingerGenerator N Ni Hperp Hi (c₁ • ψ₁ + c₂ • ψ₂)
      = c₁ • smearedSchrodingerGenerator N Ni Hperp Hi ψ₁
        + c₂ • smearedSchrodingerGenerator N Ni Hperp Hi ψ₂ :=
  schrodinger_superposition (smearedSchrodingerGenerator N Ni Hperp Hi) c₁ c₂ ψ₁ ψ₂

/-- **[The generator is linear in the lapse and shift] `𝓗(N₁+N₂, N^i₁+N^i₂) = 𝓗(N₁,N^i₁) + 𝓗(N₂,N^i₂)`.** The
smeared generator depends linearly on the deformation `(N, N^i)` — the freedom of foliation: lapse and shift
combine linearly to select a slicing of space-time. -/
theorem smearedSchrodinger_add_deformation (N₁ N₂ Ni₁ Ni₂ : ℝ) (Hperp Hi : ℂ →ₗ[ℂ] ℂ) :
    smearedSchrodingerGenerator (N₁ + N₂) (Ni₁ + Ni₂) Hperp Hi
      = smearedSchrodingerGenerator N₁ Ni₁ Hperp Hi + smearedSchrodingerGenerator N₂ Ni₂ Hperp Hi := by
  unfold smearedSchrodingerGenerator
  push_cast
  module

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger

end

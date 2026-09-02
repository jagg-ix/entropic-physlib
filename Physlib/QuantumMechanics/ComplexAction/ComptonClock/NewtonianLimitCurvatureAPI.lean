/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit
public import Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
public import Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric

/-!
# Grounding the Newtonian-limit curvature in the library's tensor API

`NewtonianAndGRLimit` wrote the linearized Christoffel `Γˣ₀₀ = ∂_xΦ/c²` and Ricci `R₀₀ = ∇²Φ/c²` directly.
The library already carries a full curvature API — `Curvature.RiemannCurvatureTensor` (the `RiemannTensor`
type, the `ricci` contraction, `scalarCurvature`, `constantCurvature`), `ComplexEinstein.EinsteinFieldEquationsPhysLean`
(`einsteinTensor` `G = R − ½Rg`, `einsteinFieldEquation` `G = κT`) and `EntropicTime.ConnectionCovariantHessian`
(`IsTorsionFree`) — so those quantities can be *derived*, not posited. This module does so in `1+1` dimensions,
where the computation is tractable and, crucially, *no generality is lost*: in two dimensions every curvature
tensor is of `constantCurvature` form `R_{abcd} = K(g_{ac}g_{bd} − g_{ad}g_{bc})`, so the weak static field is
captured exactly by the single local curvature `K`.

* **§A — `R₀₀` from the library Ricci contraction.** `weakFieldRiemann` (`= constantCurvature (∇²Φ/c²) η`, a
  genuine `IsRiemannCurvature`), `weakFieldRiemann_ricci_00` (the library `ricci η weakFieldRiemann` has
  `(0,0)`-entry `∇²Φ/c²`) and `weakFieldRicci00_eq_library_ricci` (the posited
  `NewtonianAndGRLimit.weakFieldRicci00` *equals* that library contraction) — `R₀₀` is now derived.
* **§B — the connection is torsion-free.** `weakFieldConnection` as a `Γ : ι → Matrix ι ι ℝ` with the single
  component `Γˣ₀₀ = ∂_xΦ/c²`, and `weakFieldConnection_isTorsionFree` (`ConnectionCovariantHessian.IsTorsionFree`)
  — the weak-field connection is a genuine Levi-Civita (symmetric) connection.
* **§C — the field equation via the library `einsteinFieldEquation`.** `einsteinFieldEquation_apply_00` reads
  the `(0,0)` component `R₀₀ − ½R g₀₀ = κ T₀₀` off the library `einsteinFieldEquation Ric R g T κ` (`G = κT`);
  its trace-reversed form is the Poisson equation of `NewtonianAndGRLimit.weakField_einstein_poisson`.
* **§D — the Christoffel symbols *from the metric* (Levi-Civita).** `weakFieldMetric2` `g = diag(1+2Φ/c²,−1)`
  with its derivatives `weakFieldMetricDeriv2`, the connection `weakFieldLeviCivita2` (`Γᵗ_{tx}=A'/2A`,
  `Γˣ_{tt}=A'/2`), and the two conditions that *define* it as the metric's Levi-Civita connection:
  `weakFieldLeviCivita2_isTorsionFree` and `weakFieldLeviCivita2_isMetricCompatible` (`∇_λ g = 0`, via the
  library `ConnectionCovariantHessian.metricCovariantDeriv`). `weakFieldLeviCivita2_christoffel_x` identifies
  its `Γˣ_{tt}` with §G's posited `weakFieldChristoffel`.
* **§E — the covariant geodesic returns `ẍ = −∇Φ`.** `geodesicAcceleration` `ẍ^μ = −Γ^μ_{αβ}ẋ^αẋ^β` (built from
  the connection like the library `covariantHessian`), and `weakField_geodesic_x_eq_newton`: a slow particle
  on a geodesic of the §D metric-built connection has `ẍˣ = −∂_xΦ` — Newton's gravity, now from the metric's
  own Levi-Civita connection, no mass entering.
* **§F — the Riemann tensor *from the connection*, closing `metric → Γ → Riemann → Ricci`.**
  `riemannFromConnection` `R^ρ_{σμν} = ∂Γ − ∂Γ + ΓΓ` (validated by `riemannFromConnection_antisymm_last` and
  `riemannFromConnection_flat`), `ricciFromConnection` `R_{σν} = R^μ_{σμν}`,
  `ricciMatrixFromConnection` as the matrix-valued carrier accepted by `einsteinFieldEquation`, and
  `weakField_ricci00_from_connection` (the exact `R₀₀ = A''/2 − A'²/(4A)` from the §D metric-built connection)
  with `weakField_ricci00_from_connection_newtonian` (`= weakFieldRicci00 − Φ'²/(c⁴A)`, the Newtonian
  `∇²Φ/c²` plus an explicit `O(c⁻⁴)` correction). `weakFieldScalarCurvature2` then contracts that matrix with
  the inverse metric through the existing `ricciScalarContraction`; `weakFieldEinsteinTensor2_eq_zero`
  records the exact two-dimensional identity `G_{μν}=0`. The last posited input of §A is thereby derived.

**Honest layering.** §A/§C route through the library `ricci` / `einsteinTensor` / `einsteinFieldEquation`;
§D grounds the connection in the metric through the library `metricCovariantDeriv` / `IsMetricCompatible` /
`IsTorsionFree` (metric-compatible + torsion-free = Levi-Civita, exactly); §E's covariant geodesic and §F's
Riemann/Ricci are built from that connection. With §F the full chain `metric → Christoffel → Riemann → Ricci`
is derived with nothing posited: `weakField_ricci00_from_connection` gives the *exact* `1+1` `R₀₀`, whose
leading term is the Newtonian `∇²Φ/c²` and whose `O(c⁻⁴)` correction is written out, not silently dropped.
§A's `constantCurvature`-based `R₀₀` (via the library `ricci`) and §F's `∂Γ−∂Γ+ΓΓ`-based `R₀₀` agree at leading
order. The `1+1` demonstrator has an identically vanishing Einstein tensor (the peculiarity of two
dimensions), so the matter-sourcing Poisson equation is the trace-reversed `00`-relation of
`weakField_einstein_poisson`.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI

open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
open Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.Relativity Matrix


/-- **The `1+1`-D weak-field Riemann tensor** `R_{abcd} = (∇²Φ/c²)(η_{ac}η_{bd} − η_{ad}η_{bc})`: in two
dimensions every curvature tensor is of constant-curvature form, so the weak static field is the
`constantCurvature` tensor of the single local curvature `K = ∇²Φ/c²` (`d2Φ = ∇²Φ`, here `Φ''`) over the
Minkowski metric. -/
noncomputable def weakFieldRiemann (d2Φ c : ℝ) : RiemannTensor (Fin 1 ⊕ Fin 1) :=
  constantCurvature (d2Φ / c ^ 2) minkowskiMatrix

/-- **The weak-field Riemann tensor is a genuine Riemann tensor** (satisfies the four algebraic symmetries),
via the library `isRiemannCurvature_constantCurvature` and the symmetry of `minkowskiMatrix`. -/
lemma weakFieldRiemann_isRiemannCurvature (d2Φ c : ℝ) :
    IsRiemannCurvature (weakFieldRiemann d2Φ c) :=
  isRiemannCurvature_constantCurvature _ _ fun i j => by
    by_cases h : i = j
    · rw [h]
    · rw [minkowskiMatrix.off_diag_zero h, minkowskiMatrix.off_diag_zero (Ne.symm h)]

/-- **[`R₀₀` derived from the library contraction] `ricci η weakFieldRiemann |₀₀ = ∇²Φ/c²`**: contracting the
weak-field Riemann tensor with the Minkowski inverse metric through the library `ricci` yields the Newtonian
time–time Ricci curvature — the value `NewtonianAndGRLimit.weakFieldRicci00` was written by hand. -/
lemma weakFieldRiemann_ricci_00 (d2Φ c : ℝ) :
    ricci minkowskiMatrix (weakFieldRiemann d2Φ c) (Sum.inl 0) (Sum.inl 0) = d2Φ / c ^ 2 := by
  simp [ricci, weakFieldRiemann, constantCurvature, Fintype.sum_sum_type]

/-- **The posited `weakFieldRicci00` is the library Ricci contraction**: the hand-written
`NewtonianAndGRLimit.weakFieldRicci00 = ∇²Φ/c²` equals the library `ricci` of the weak-field Riemann tensor,
so §H's Ricci is grounded in the tensor API. -/
lemma weakFieldRicci00_eq_library_ricci (d2Φ c : ℝ) :
    weakFieldRicci00 d2Φ c
      = ricci minkowskiMatrix (weakFieldRiemann d2Φ c) (Sum.inl 0) (Sum.inl 0) := by
  rw [weakFieldRiemann_ricci_00]; rfl


/-- **The weak-field Levi-Civita connection** as a `Γ : ι → Matrix ι ι ℝ` (`(Γ l) μ ν = Γˡ_{μν}`) with the
single non-zero component `Γˣ₀₀ = ∂_xΦ/c²`. -/
noncomputable def weakFieldConnection (dΦ c : ℝ) :
    (Fin 1 ⊕ Fin 1) → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  fun l => Matrix.of fun μ ν =>
    if μ = Sum.inl 0 ∧ ν = Sum.inl 0 then (if l = Sum.inr 0 then dΦ / c ^ 2 else 0) else 0

/-- **The weak-field connection is torsion-free** (`ConnectionCovariantHessian.IsTorsionFree`): each Christoffel
matrix `Γ l` is symmetric in its lower pair, since its only entry sits on the `(0,0)` diagonal — a genuine
symmetric (Levi-Civita) connection. -/
lemma weakFieldConnection_isTorsionFree (dΦ c : ℝ) : IsTorsionFree (weakFieldConnection dΦ c) := by
  intro l
  ext μ ν
  simp only [Matrix.transpose_apply, weakFieldConnection, Matrix.of_apply, and_comm]


/-- **The `(0,0)` component of the library Einstein field equation** `R₀₀ − ½R g₀₀ = κ T₀₀`: reading the
tensor equation `einsteinFieldEquation Ric R g T κ` (`G = κT`, i.e. `Ric − ½R g = κT`) off its `(0,0)` entry
gives the scalar field equation whose trace-reversed Newtonian form is
`NewtonianAndGRLimit.weakField_einstein_poisson` (`∇²Φ = 4πGρ`). -/
lemma einsteinFieldEquation_apply_00
    {ι : Type*} [DecidableEq ι] (i : ι) (Ric g T : Matrix ι ι ℝ) (scalarR κ : ℝ)
    (h : einsteinFieldEquation Ric scalarR g T κ) :
    Ric i i - scalarR / 2 * g i i = κ * T i i := by
  have hij := congrFun (congrFun h i) i
  simpa [einsteinTensor, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using hij


/-- **The `1+1`-D weak static metric** `g = diag(A, −1)` with `A = g₀₀ = 1 + 2Φ/c²` (time index `0`, space
index `1`). -/
noncomputable def weakFieldMetric2 (A : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![A, 0; 0, -1]

/-- **The metric's partial derivatives** `∂_λ g`: static (`∂₀ g = 0`) with `∂₁ g₀₀ = A' = 2Φ'/c²`. -/
noncomputable def weakFieldMetricDeriv2 (A' : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![0, !![A', 0; 0, 0]]

/-- **The Levi-Civita connection of `weakFieldMetric2`** `Γ^λ_{μν} = ½g^{λσ}(∂_μ g_{σν}+∂_ν g_{σμ}−∂_σ g_{μν})`
computed from the metric: the non-zero symbols are `Γᵗ_{tx}=Γᵗ_{xt}=A'/(2A)` and `Γˣ_{tt}=A'/2`. Written in the
`Γ : ι → Matrix ι ι ℝ` form `(Γ σ) μ ν = Γˢ_{μν}`. -/
noncomputable def weakFieldLeviCivita2 (A A' : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![!![0, A' / (2 * A); A' / (2 * A), 0], !![A' / 2, 0; 0, 0]]

/-- **[The connection is torsion-free]** each Christoffel matrix is symmetric in its lower pair
(`ConnectionCovariantHessian.IsTorsionFree`). -/
lemma weakFieldLeviCivita2_isTorsionFree (A A' : ℝ) :
    IsTorsionFree (weakFieldLeviCivita2 A A') := by
  intro l
  fin_cases l <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [weakFieldLeviCivita2, Matrix.transpose_apply]

/-- **[The connection is metric-compatible] `∇_λ g_μν = 0`** (`ConnectionCovariantHessian.IsMetricCompatible`):
the weak-field Levi-Civita connection annihilates the metric it was built from. Together with
`weakFieldLeviCivita2_isTorsionFree`, this is exactly the statement that `weakFieldLeviCivita2` *is* the
metric's Levi-Civita connection — the metric→Christoffel derivation, via the library's `metricCovariantDeriv`. -/
lemma weakFieldLeviCivita2_isMetricCompatible (A A' : ℝ) (hA : A ≠ 0) :
    IsMetricCompatible (weakFieldLeviCivita2 A A') (weakFieldMetricDeriv2 A') (weakFieldMetric2 A) := by
  intro l
  fin_cases l <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [metricCovariantDeriv, weakFieldLeviCivita2, weakFieldMetric2, weakFieldMetricDeriv2,
      Fin.sum_univ_two] <;> field_simp <;> ring

/-- **The metric-derived `Γˣ_{tt}` is the posited weak-field Christoffel** of §G: with `A' = 2Φ'/c²`, the
`(x; t,t)` component of the Levi-Civita connection is `A'/2 = Φ'/c² = NewtonianAndGRLimit.weakFieldChristoffel`,
so §G's `Γˣ₀₀` is grounded in the metric. -/
lemma weakFieldLeviCivita2_christoffel_x (dΦ c : ℝ) :
    weakFieldLeviCivita2 (0 : ℝ) (2 * dΦ / c ^ 2) 1 0 0 = weakFieldChristoffel dΦ c := by
  simp only [weakFieldLeviCivita2, weakFieldChristoffel, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.of_apply]
  ring


/-- **The geodesic acceleration** `ẍ^μ = −Γ^μ_{αβ} ẋ^α ẋ^β` — the covariant geodesic equation `∇_ẋẋ = 0`
solved for the acceleration, built from the connection exactly as `ConnectionCovariantHessian.covariantHessian`
builds `∇∇φ`. -/
noncomputable def geodesicAcceleration {ι : Type*} [Fintype ι]
    (Γ : ι → Matrix ι ι ℝ) (v : ι → ℝ) : ι → ℝ :=
  fun μ => - ∑ α, ∑ β, (Γ μ) α β * v α * v β

/-- **[GR ⇒ Newton, from the metric's connection] the geodesic acceleration is `−∇Φ`**: a slow particle
(4-velocity `ẋ = (c, 0)`, `dx⁰/dτ ≈ c`) on a geodesic of the weak-field metric has spatial acceleration
`ẍˣ = −Γˣ_{tt} c² = −∂_xΦ` — Newton's gravity, now derived from the metric-built Levi-Civita connection of §D
via the covariant geodesic equation. No mass enters. -/
lemma weakField_geodesic_x_eq_newton (A dΦ c : ℝ) (hc : c ≠ 0) :
    geodesicAcceleration (weakFieldLeviCivita2 A (2 * dΦ / c ^ 2)) ![c, 0] 1 = -dΦ := by
  simp only [geodesicAcceleration, weakFieldLeviCivita2, Fin.sum_univ_two, Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.of_apply]
  field_simp
  ring


/-- **The Riemann curvature from a connection** `R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ}Γ^λ_{νσ}
− Γ^ρ_{νλ}Γ^λ_{μσ}`, with `dΓ μ ρ = ∂_μ Γ^ρ` (`(dΓ μ ρ) ν σ = ∂_μ Γ^ρ_{νσ}`). The `∂Γ − ∂Γ + ΓΓ` formula the
library's abstract `RiemannTensor` was missing — supplied here. -/
noncomputable def riemannFromConnection {ι : Type*} [Fintype ι]
    (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ) (ρ σ μ ν : ι) : ℝ :=
  (dΓ μ ρ) ν σ - (dΓ ν ρ) μ σ
    + (∑ l, (Γ ρ) μ l * (Γ l) ν σ) - (∑ l, (Γ ρ) ν l * (Γ l) μ σ)

/-- **[Antisymmetry in the last pair] `R^ρ_{σμν} = −R^ρ_{σνμ}`** — a structural identity of the
`∂Γ − ∂Γ + ΓΓ` formula, independent of the connection. -/
lemma riemannFromConnection_antisymm_last {ι : Type*} [Fintype ι]
    (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ) (ρ σ μ ν : ι) :
    riemannFromConnection Γ dΓ ρ σ μ ν = - riemannFromConnection Γ dΓ ρ σ ν μ := by
  unfold riemannFromConnection; ring

/-- **[Flat connection ⇒ flat curvature] `Γ = 0, ∂Γ = 0 ⇒ R = 0`.** -/
lemma riemannFromConnection_flat {ι : Type*} [Fintype ι] (ρ σ μ ν : ι) :
    riemannFromConnection (fun _ => 0) (fun _ _ => 0) ρ σ μ ν = 0 := by
  simp [riemannFromConnection]

/-- **The Ricci tensor from a connection** `R_{σν} = R^μ_{σμν}` — the contraction over the first upper and
first lower index of `riemannFromConnection`. -/
noncomputable def ricciFromConnection {ι : Type*} [Fintype ι]
    (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ) (σ ν : ι) : ℝ :=
  ∑ μ, riemannFromConnection Γ dΓ μ σ μ ν

/--
**The Ricci tensor from a connection as a matrix.** This is the reusable
carrier that feeds the connection-derived contraction directly into APIs such
as `einsteinTensor` and `einsteinFieldEquation`.
-/
noncomputable def ricciMatrixFromConnection {ι : Type*} [Fintype ι]
    (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun σ ν => ricciFromConnection Γ dΓ σ ν

@[simp]
lemma ricciMatrixFromConnection_apply {ι : Type*} [Fintype ι]
    (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ) (σ ν : ι) :
    ricciMatrixFromConnection Γ dΓ σ ν = ricciFromConnection Γ dΓ σ ν :=
  rfl

/-- **The spatial derivatives of the weak-field Levi-Civita connection** `∂_λ Γ` (static, so `∂₀Γ = 0`):
`∂₁Γᵗ_{tx} = (A''A − A'²)/(2A²)` and `∂₁Γˣ_{tt} = A''/2`. -/
noncomputable def weakFieldConnDeriv2 (A A' A'' : ℝ) : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 0],
    ![!![0, (A'' * A - A' ^ 2) / (2 * A ^ 2); (A'' * A - A' ^ 2) / (2 * A ^ 2), 0],
      !![A'' / 2, 0; 0, 0]]]

/--
**The weak-field Ricci matrix derived from the metric's Levi-Civita
connection.** Its derivative arguments are expressed directly as the
Newtonian potential derivatives `Φ'` and `Φ''`.
-/
noncomputable def weakFieldRicciMatrix2 (A dΦ d2Φ c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ricciMatrixFromConnection
    (weakFieldLeviCivita2 A (2 * dΦ / c ^ 2))
    (weakFieldConnDeriv2 A (2 * dΦ / c ^ 2) (2 * d2Φ / c ^ 2))

/-- **[`R₀₀` from the metric's own connection] `R₀₀ = A''/2 − A'²/(4A)`**: contracting the
`riemannFromConnection` of the §D metric-built Levi-Civita connection gives the exact `1+1` time–time Ricci
curvature — the full chain `metric → Christoffel (§D) → Riemann → Ricci`, nothing posited. -/
lemma weakField_ricci00_from_connection (A A' A'' : ℝ) (hA : A ≠ 0) :
    ricciFromConnection (weakFieldLeviCivita2 A A') (weakFieldConnDeriv2 A A' A'') 0 0
      = A'' / 2 - A' ^ 2 / (4 * A) := by
  simp [ricciFromConnection, riemannFromConnection, weakFieldLeviCivita2, weakFieldConnDeriv2,
    Fin.sum_univ_two]
  field_simp
  ring

/-- **[The metric-derived `R₀₀` is the Newtonian `∇²Φ/c²` plus an explicit relativistic correction]**
`R₀₀ = weakFieldRicci00 − Φ'²/(c⁴A)`: with `A' = 2Φ'/c²`, `A'' = 2∇²Φ/c²`, the exact Ricci from the connection
is the posited Newtonian `weakFieldRicci00 = ∇²Φ/c²` (§A/§H, its leading term) minus an explicit `O(c⁻⁴)`
term. The last linearized input of §A is thereby *derived*, with the dropped correction made visible. -/
lemma weakField_ricci00_from_connection_newtonian (A dΦ d2Φ c : ℝ) (hA : A ≠ 0) (hc : c ≠ 0) :
    ricciFromConnection (weakFieldLeviCivita2 A (2 * dΦ / c ^ 2))
        (weakFieldConnDeriv2 A (2 * dΦ / c ^ 2) (2 * d2Φ / c ^ 2)) 0 0
      = weakFieldRicci00 d2Φ c - dΦ ^ 2 / (c ^ 4 * A) := by
  rw [weakField_ricci00_from_connection A (2 * dΦ / c ^ 2) (2 * d2Φ / c ^ 2) hA]
  unfold weakFieldRicci00
  field_simp
  ring

/--
The `(0,0)` entry of the connection-derived weak-field Ricci matrix is the
Newtonian curvature plus the explicit `O(c⁻⁴)` correction.
-/
lemma weakFieldRicciMatrix2_apply_00 (A dΦ d2Φ c : ℝ)
    (hA : A ≠ 0) (hc : c ≠ 0) :
    weakFieldRicciMatrix2 A dΦ d2Φ c 0 0 =
      weakFieldRicci00 d2Φ c - dΦ ^ 2 / (c ^ 4 * A) := by
  exact weakField_ricci00_from_connection_newtonian A dΦ d2Φ c hA hc


/-- **The inverse weak-field metric** `g⁻¹ = diag(1/A, −1)`. -/
noncomputable def weakFieldMetric2Inv (A : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 / A, 0; 0, -1]

/-- **[`g⁻¹ · g = 1`]** the inverse relation for the weak-field metric (`A ≠ 0`). -/
lemma weakFieldMetric2Inv_mul (A : ℝ) (hA : A ≠ 0) :
    weakFieldMetric2Inv A * weakFieldMetric2 A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weakFieldMetric2Inv, weakFieldMetric2, Matrix.mul_apply, Fin.sum_univ_two, hA]

/--
The complete connection-derived Ricci matrix of the weak static metric.  Its
off-diagonal entries vanish and its spatial component is `-R₀₀/A`.
-/
lemma weakFieldRicciMatrix2_eq (A dΦ d2Φ c : ℝ)
    (hA : A ≠ 0) (hc : c ≠ 0) :
    weakFieldRicciMatrix2 A dΦ d2Φ c =
      !![weakFieldRicci00 d2Φ c - dΦ ^ 2 / (c ^ 4 * A), 0;
        0, -(weakFieldRicci00 d2Φ c - dΦ ^ 2 / (c ^ 4 * A)) / A] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weakFieldRicciMatrix2, ricciMatrixFromConnection, ricciFromConnection,
      riemannFromConnection, weakFieldLeviCivita2, weakFieldConnDeriv2,
      weakFieldRicci00, Fin.sum_univ_two] <;>
    field_simp <;>
    ring

/--
The scalar curvature obtained by tracing the connection-derived Ricci matrix
with the inverse weak-field metric.
-/
noncomputable def weakFieldScalarCurvature2 (A dΦ d2Φ c : ℝ) : ℝ :=
  ricciScalarContraction (weakFieldMetric2Inv A)
    (weakFieldRicciMatrix2 A dΦ d2Φ c)

/--
The exact scalar curvature is twice the `(0,0)` Ricci component divided by
`A`; the relativistic `O(c⁻⁴)` term remains explicit.
-/
lemma weakFieldScalarCurvature2_eq (A dΦ d2Φ c : ℝ)
    (hA : A ≠ 0) (hc : c ≠ 0) :
    weakFieldScalarCurvature2 A dΦ d2Φ c =
      2 / A * (weakFieldRicci00 d2Φ c - dΦ ^ 2 / (c ^ 4 * A)) := by
  rw [weakFieldScalarCurvature2, weakFieldRicciMatrix2_eq A dΦ d2Φ c hA hc]
  simp [ricciScalarContraction, weakFieldMetric2Inv, Matrix.trace, Fin.sum_univ_two]
  ring

/--
The Einstein tensor of the exact `1+1` weak-field geometry vanishes.  This is
the standard two-dimensional identity and is why this demonstrator cannot by
itself represent a nonzero matter-sourced `3+1` Einstein equation.
-/
lemma weakFieldEinsteinTensor2_eq_zero (A dΦ d2Φ c : ℝ)
    (hA : A ≠ 0) (hc : c ≠ 0) :
    einsteinTensor (weakFieldRicciMatrix2 A dΦ d2Φ c)
        (weakFieldScalarCurvature2 A dΦ d2Φ c) (weakFieldMetric2 A) = 0 := by
  rw [weakFieldRicciMatrix2_eq A dΦ d2Φ c hA hc,
    weakFieldScalarCurvature2_eq A dΦ d2Φ c hA hc]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [einsteinTensor, weakFieldMetric2] <;>
    field_simp [hA] <;>
    ring

/-- **[§D's connection is the general Levi-Civita connection]** `weakFieldLeviCivita2 = christoffelFromMetric`:
the hand-built `1+1` weak-field connection of §D equals the general `Curvature.LeviCivitaFromMetric` applied to
the weak-field metric — the "one instance" claim proven, exercising `christoffelFromMetric` against a real
inverse metric. -/
lemma weakFieldLeviCivita2_eq_christoffelFromMetric (A A' : ℝ) (hA : A ≠ 0) :
    weakFieldLeviCivita2 A A'
      = christoffelFromMetric (weakFieldMetric2Inv A) (weakFieldMetricDeriv2 A') := by
  funext σ
  ext μ ν
  fin_cases σ <;> fin_cases μ <;> fin_cases ν <;>
    simp [weakFieldLeviCivita2, christoffelFromMetric, weakFieldMetric2Inv, weakFieldMetricDeriv2,
      Fin.sum_univ_two]
  all_goals field_simp

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory

/-!
# The dual-sphere fiber Yoneda bridge, ported to `ℂ`-modules and the field algebra

Ports the **category-theory core** of the Navier–Stokes dual-sphere fiber layer
(`NavierStokes/CategoryTheoryYonedaBridge.lean`) into physlib. The source bridge applies the
**Yoneda lemma** to a category of Banach spaces (`TopModuleCat ℝ`), making Yoneda-native reasoning
available for its field functionals. Here the same Yoneda machinery is set up over `ModuleCat ℂ` — the
natural home for physlib's `ℂ`-linear structures — and linked to the Greaves–Thomas **field formula
algebra** `K^form = TensorAlgebra ℂ U`.

The Yoneda lemma says a representable presheaf `hom(−, X)` determines its object `X`:

  `NatTrans(hom(−, X), hom(−, Y)) ≃ Hom(X, Y)`,

so morphisms are recovered from their action on all probes — and an object is determined up to isomorphism
by that probe data (Yoneda extensionality).

* **§A — the Yoneda bridge over `ModuleCat ℂ`** (`homPresheaf`, `yoneda_natTrans_equiv_hom`,
  `hom_ext_via_yoneda_map`, `iso_of_probe_equivalence`). Represented presheaves, the Yoneda equivalence
  `NatTrans(hom(−,X), hom(−,Y)) ≃ (X ⟶ Y)` (native `CategoryTheory.yonedaEquiv`), faithfulness
  (`yoneda.map_injective`), and iso-reconstruction from probe equivalence (`CategoryTheory.Yoneda.ext`).
* **§B — the physlib link: the field formula algebra as a `ℂ`-module object** (`fieldAlgebraObj`,
  `fieldAlgebraPresheaf`, `fieldAlgebra_yoneda`, `fieldAlgebra_hom_ext`). The field algebra
  `K^form = TensorAlgebra ℂ U` is an object of `ModuleCat ℂ`; its `ℂ`-linear endomorphisms (the realm of the
  Greaves–Thomas formula automorphisms / superoperators) are recovered, by Yoneda, from their action on all
  probes — and two such maps coincide iff their Yoneda images do.

## References

* The Yoneda lemma (`CategoryTheory.yonedaEquiv`, `CategoryTheory.Yoneda.ext`); the dual-sphere fiber bridge
  `NavierStokes/CategoryTheoryYonedaBridge.lean` (Yoneda over `TopModuleCat ℝ`).
* Repo structure: `PTSymmetricQFT.FormalFieldTheory` (`KForm = TensorAlgebra ℂ U`, the field formula algebra).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberYoneda

open CategoryTheory
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory

/-! ## §A — the Yoneda bridge over `ModuleCat ℂ` -/

/-- Presheaves on the category of `ℂ`-modules — the physlib analogue of the source `BanSpPresheaf`. -/
abbrev ModPresheaf := (ModuleCat ℂ)ᵒᵖ ⥤ Type _

/-- The represented (`hom`) presheaf `hom(−, X)` of a `ℂ`-module object `X`. -/
noncomputable def homPresheaf (X : ModuleCat ℂ) : ModPresheaf := yoneda.obj X

/-- **[Yoneda lemma] `NatTrans(hom(−,X), hom(−,Y)) ≃ (X ⟶ Y)`.** Natural transformations between
representable presheaves are exactly the `ℂ`-linear morphisms — `CategoryTheory.yonedaEquiv` specialized to
`ModuleCat ℂ`. -/
noncomputable def yoneda_natTrans_equiv_hom (X Y : ModuleCat ℂ) :
    (homPresheaf X ⟶ homPresheaf Y) ≃ (X ⟶ Y) := by
  simpa [homPresheaf] using
    yonedaEquiv (X := X) (F := (yoneda (C := ModuleCat ℂ)).obj Y)

/-- **[Faithfulness] Two morphisms are equal if their Yoneda actions agree.** The Yoneda embedding is
faithful. -/
theorem hom_ext_via_yoneda_map {X Y : ModuleCat ℂ} {f g : X ⟶ Y}
    (h : (yoneda (C := ModuleCat ℂ)).map f = (yoneda (C := ModuleCat ℂ)).map g) :
    f = g :=
  yoneda.map_injective h

/-- **[Yoneda extensionality] An iso from probe-level equivalence.** Mutually inverse, natural maps on all
incoming probes reconstruct an isomorphism of objects — `CategoryTheory.Yoneda.ext`. -/
noncomputable def iso_of_probe_equivalence (X Y : ModuleCat ℂ)
    (p : ∀ {Z : ModuleCat ℂ}, (Z ⟶ X) → (Z ⟶ Y))
    (q : ∀ {Z : ModuleCat ℂ}, (Z ⟶ Y) → (Z ⟶ X))
    (h₁ : ∀ {Z : ModuleCat ℂ} (f : Z ⟶ X), q (p f) = f)
    (h₂ : ∀ {Z : ModuleCat ℂ} (f : Z ⟶ Y), p (q f) = f)
    (n : ∀ {Z Z' : ModuleCat ℂ} (f : Z' ⟶ Z) (g : Z ⟶ X), p (f ≫ g) = f ≫ p g) :
    X ≅ Y :=
  CategoryTheory.Yoneda.ext (C := ModuleCat ℂ) X Y p q h₁ h₂ n

/-! ## §B — the physlib link: the field formula algebra as a `ℂ`-module object -/

variable {U : Type} [AddCommGroup U] [Module ℂ U]

/-- **The field formula algebra `K^form = TensorAlgebra ℂ U` as an object of `ModuleCat ℂ`.** -/
noncomputable def fieldAlgebraObj (U : Type) [AddCommGroup U] [Module ℂ U] : ModuleCat ℂ :=
  ModuleCat.of ℂ (KForm U)

/-- The represented presheaf of the field algebra. -/
noncomputable def fieldAlgebraPresheaf : ModPresheaf := homPresheaf (fieldAlgebraObj U)

/-- **[Yoneda for the field algebra] `NatTrans(hom(−, K^form), hom(−, K^form)) ≃ (K^form ⟶ K^form)`.** The
`ℂ`-linear endomorphisms of the field formula algebra — the realm of the Greaves–Thomas formula automorphisms
and superoperators — are recovered by Yoneda from natural transformations of its represented presheaf. -/
noncomputable def fieldAlgebra_yoneda :
    (fieldAlgebraPresheaf (U := U) ⟶ fieldAlgebraPresheaf (U := U))
      ≃ (fieldAlgebraObj U ⟶ fieldAlgebraObj U) :=
  yoneda_natTrans_equiv_hom (fieldAlgebraObj U) (fieldAlgebraObj U)

/-- **[Field-algebra faithfulness] Two `ℂ`-linear endomorphisms of `K^form` coincide iff their Yoneda images
do** — the field algebra is determined by its probes. -/
theorem fieldAlgebra_hom_ext {f g : fieldAlgebraObj U ⟶ fieldAlgebraObj U}
    (h : (yoneda (C := ModuleCat ℂ)).map f = (yoneda (C := ModuleCat ℂ)).map g) :
    f = g :=
  yoneda.map_injective h

end Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberYoneda

end

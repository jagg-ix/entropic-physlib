/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability
public import Physlib.QuantumMechanics.ComplexAction.Particles.ShellFillingStability
public import Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers
public import Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics
public import Physlib.QuantumMechanics.ComplexAction.ExchangeStatisticsSpectrum
meta import Zil

/-!
# The isotope-stability tower: neutron register, β-decay valley, island, pairing, collectivity, spin-orbit magic, spin statistics

The neutron-degree-of-freedom side of the nuclear-stability model, in seven namespaces (each formerly its own
module), all downstream of `NuclearValleyOfStability` and the shell-filling combinatorics:

* **Part I — `NuclearIsotopeStability`.** The two-register information of a nuclide
  (`isotopeMicrostates = 2^(Z+N)`, `isotope_information`: the mass number *is* the information content in
  bits), doubly-magic closures on the `N = Z` diagonal (`diagonal_doubly_magic`, `helium4/oxygen16/calcium40`),
  and the stable-neutron line `stableNeutronNumber = Z + (a_C/ε)(Z−½)` proved to be the exact inverse of the
  isobaric β-valley (`stableNeutronNumber_consistent`), neutron-rich (`stable_neutron_excess`) and growing
  (`stableNeutronNumber_strictMono`).
* **Part II — `NuclearBetaDecayValley`.** The β-decay structure of an isobaric chain from strict convexity of
  the mass parabola: `mass_lt_of_closer` (the valley shape), `betaStable` with the decay directions
  (`not_betaStable_of_lighter_upper`/`_lower`), and Mattauch's isobar rule as the exact-degeneracy condition
  `adjacent_betaStable_degenerate`.
* **Part III — `NuclearStabilityIsland`.** The isolated doubly-magic closure beyond the fission cliff:
  `hoMagic_strictMono`, the pure-oscillator island `(112, 168)` (`island_doubly_magic`, `island_neutron_rich`,
  `island_in_superheavy`), and its isolation (`sea_of_instability`, `island_isolated`).
* **Part IV — `NuclearPairingParity`.** Odd-even pairing *derived* from spin-doublet filling: the unpaired
  count `Z%2 + N%2` and the four parity classes (§A, pure combinatorics), the pairing energy `d · unpaired`
  (§B), and the even-A/odd-A split behind Mattauch's rule (`evenEven_lighter`, `oddA_adjacent_pairing_eq`).
* **Part V — `NuclearValenceCollectivity`.** Valence nucleons as the shell distance
  (`valenceNucleons = shellDistance (oscillatorDegeneracy k) q`): zero at magic closures (spherical), maximal
  at mid-shell (`collectivity_max_at_midshell` — deformation peaks between closures), particle-hole symmetric
  (`nuclear_valence_particle_hole`) — the combinatorial core of the Casten `N_pN_n` picture.
* **Part VI — `NuclearSpinOrbitMagic`.** The observed magic numbers `2, 8, 20, 28, 50, 82, 126, 184` from the
  Mayer–Jensen spin-orbit intruder mechanism: `spinOrbit_conserves` (`(2l+2) + 2l = 2(2l+1)`),
  `shell_minus_intruder`, `socMagic_values`, `first_three_match_hoMagic`, `spin_orbit_shifts_at_28`, and the
  corrected superheavy island `soc_island` (`(126, 184)`).
* **Part VII — `IsotopeNuclearSpinStatistics`.** Isotope statistics from the composite twist `(−1)^A`:
  `nucleus_boson`/`nucleus_fermion`, the concrete isotopes (`carbon12_boson`, `carbon13_fermion`,
  `oxygen16_boson`, `deuteron_boson`), and even-even ⇒ fully paired ⇒ `I = 0`
  (`evenEven_fully_paired`) — the chain isotopy → pairing → nuclear spin → exchange statistics that feeds the
  `¹²C₆₀` molecular selection rules.

**Honest layering.** The register information, the doubly-magic diagonal, the stable-`N` inversion, the valley
convexity consequences, the pairing combinatorics, the valence/shell-distance identities, the spin-orbit state
counting, and the composite exchange phase are all exact/derived. The physical parameters (`ε`, `a_C`, the
pair-binding scale `d`) are physical scales, not fits; the Mayer–Jensen intruder *ordering* is encoded (in
`socGap`) and its magic numbers then derived; "even-even ⇒ `I = 0`" is the pairing ground-state rule grounded
on `unpaired = 0`. Detailed deformation energetics and level coupling are not modelled.

## References

* Isotopes, neutron shell closures, doubly-magic nuclei; J. Mattauch (1934), the isobar rule; the predicted
  superheavy island (`Z ≈ 114–126`, `N ≈ 184`); M. G. Mayer, O. Haxel, J. H. D. Jensen, H. E. Suess (1949),
  the shell model with spin-orbit coupling; composite spin-statistics of nucleons. Built on
  `Particles.NuclearValleyOfStability` (both its namespaces), `Particles.ShellInformationLadder`,
  `Particles.ShellFillingStability`, `Particles.ShellFillingParticleHole`,
  `Particles.AtomicSubshellQuantumNumbers`, `Particles.HadronSpinStatistics`, and
  `ComplexAction.ExchangeStatisticsSpectrum`.


-/

set_option autoImplicit false

@[expose] public section

/-! ## Part I — isotopy: the neutron register, doubly-magic closures, the stable-`N` line -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.NuclearIsotopeStability

open Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability
open Physlib.QuantumMechanics.ComplexAction.Particles.NuclearBetaStabilityLine


/-- The **occupation microstates of a nuclide** `(Z, N)`: protons and neutrons fill separate Pauli registers, so
`2^Z · 2^N` configurations. -/
def isotopeMicrostates (Z N : ℕ) : ℕ := 2 ^ Z * 2 ^ N

/-- **A nuclide's register is `2^A`** `isotopeMicrostates Z N = 2^(Z+N)`: the two shell registers combine into
one of `A = Z + N` bits. -/
lemma isotopeMicrostates_eq (Z N : ℕ) : isotopeMicrostates Z N = 2 ^ (Z + N) := by
  rw [isotopeMicrostates, ← pow_add]

/-- **The mass number is the information content** `log₂(isotopeMicrostates) = Z + N = A`: each nucleon is one
occupation bit, so a nuclide stores `A` bits. -/
lemma isotope_information (Z N : ℕ) : Nat.log 2 (isotopeMicrostates Z N) = Z + N := by
  rw [isotopeMicrostates_eq, Nat.log_pow (by norm_num)]

/-- **Each added neutron doubles the register** — the isotope information strictly increases with neutron
number at fixed `Z`. -/
lemma isotope_register_strictMono_in_N (Z : ℕ) :
    StrictMono (fun N => isotopeMicrostates Z N) := by
  intro a b hab
  simp only [isotopeMicrostates_eq]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)


/-- A nucleon number is **magic** when it is an oscillator shell closure `hoMagic k`. -/
def IsMagic (n : ℕ) : Prop := ∃ k, hoMagic k = n

/-- A nuclide is **doubly magic** when both its proton and neutron numbers are shell closures. -/
def IsDoublyMagic (Z N : ℕ) : Prop := IsMagic Z ∧ IsMagic N

/-- **Every oscillator closure gives an `N = Z` doubly-magic nuclide** — neutrons fill the same ladder as
protons, so the diagonal `(hoMagic k, hoMagic k)` is doubly magic for all `k`. -/
lemma diagonal_doubly_magic (k : ℕ) : IsDoublyMagic (hoMagic k) (hoMagic k) :=
  ⟨⟨k, rfl⟩, ⟨k, rfl⟩⟩

/-- **Helium-4 is doubly magic** `(Z, N) = (2, 2)` — the `k = 0` oscillator closure. -/
lemma helium4_doubly_magic : IsDoublyMagic 2 2 := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩

/-- **Oxygen-16 is doubly magic** `(8, 8)` — the `k = 1` closure. -/
lemma oxygen16_doubly_magic : IsDoublyMagic 8 8 := ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩

/-- **Calcium-40 is doubly magic** `(20, 20)` — the `k = 2` closure. -/
lemma calcium40_doubly_magic : IsDoublyMagic 20 20 := ⟨⟨2, by decide⟩, ⟨2, by decide⟩⟩


/-- The **stable neutron number** of element `Z` — the neutron count of its most stable isotope,
`N* = Z + (a_C/ε)(Z − ½)`. Derived below as the exact inverse of the isobaric β-stability line. -/
noncomputable def stableNeutronNumber (ε aC Z : ℝ) : ℝ := Z + (aC / ε) * (Z - 1 / 2)

/-- **The stable-neutron line inverts the β-valley** `betaStableCharge (Z + N*) = Z`: the neutron number
`stableNeutronNumber` is exactly the value that puts element `Z` on the isobaric line of stability. -/
lemma stableNeutronNumber_consistent (ε aC Z : ℝ) (hε : 0 < ε) (hC : 0 < aC) :
    betaStableCharge ε aC (Z + stableNeutronNumber ε aC Z) = Z := by
  have hε' : ε ≠ 0 := ne_of_gt hε
  have hd : (2 : ℝ) * ε + aC ≠ 0 := by positivity
  unfold betaStableCharge stableCharge massLinear massCurvature stableNeutronNumber
  rw [neg_neg]
  field_simp
  ring

/-- **Stable isotopes are neutron-rich** `Z < N*` (for `Z > ½`): the most stable isotope of any element beyond
the lightest carries more neutrons than protons. -/
lemma stable_neutron_excess (ε aC Z : ℝ) (hε : 0 < ε) (hC : 0 < aC) (hZ : 1 / 2 < Z) :
    Z < stableNeutronNumber ε aC Z := by
  unfold stableNeutronNumber
  have h : 0 < aC / ε * (Z - 1 / 2) := mul_pos (by positivity) (by linarith)
  linarith

/-- **The stable neutron number grows with `Z`** — heavier elements sit at progressively higher neutron numbers
(the valley bends toward neutron excess). -/
lemma stableNeutronNumber_strictMono (ε aC : ℝ) (hε : 0 < ε) (hC : 0 < aC) :
    StrictMono (stableNeutronNumber ε aC) := by
  intro a b hab
  unfold stableNeutronNumber
  have h : 0 < aC / ε := by positivity
  nlinarith [mul_pos h (show (0 : ℝ) < b - a by linarith)]

end Physlib.QuantumMechanics.ComplexAction.Particles.NuclearIsotopeStability

/-! ## Part II — the β-decay valley and Mattauch's isobar rule, from parabola convexity -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.NuclearBetaDecayValley

open Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability


/-- **The isobar closer to `Z*` is lighter** — if `Z₁` is nearer the stability charge than `Z₂` (in squared
distance) then `M(Z₁) < M(Z₂)`. The mass rises with distance from the valley bottom (strict convexity). -/
lemma mass_lt_of_closer (c₀ c₁ c₂ Z₁ Z₂ : ℝ) (hc : 0 < c₂)
    (h : (Z₁ - stableCharge c₁ c₂) ^ 2 < (Z₂ - stableCharge c₁ c₂) ^ 2) :
    isobaricMass c₀ c₁ c₂ Z₁ < isobaricMass c₀ c₁ c₂ Z₂ := by
  have k1 := mass_sub_min c₀ c₁ c₂ (ne_of_gt hc) Z₁
  have k2 := mass_sub_min c₀ c₁ c₂ (ne_of_gt hc) Z₂
  have hs := mul_lt_mul_of_pos_left h hc
  linarith


/-- A nuclide (charge `Z`, fixed `A`) is **β-stable** when it is no heavier than either isobaric neighbour: it
cannot lower its mass by `β⁻` (`Z → Z+1`) or `β⁺`/EC (`Z → Z−1`). -/
def betaStable (c₀ c₁ c₂ Z : ℝ) : Prop :=
  isobaricMass c₀ c₁ c₂ Z ≤ isobaricMass c₀ c₁ c₂ (Z - 1) ∧
  isobaricMass c₀ c₁ c₂ Z ≤ isobaricMass c₀ c₁ c₂ (Z + 1)

/-- **A lighter `Z+1` neighbour makes `Z` unstable** — the isobar `β⁻`-decays upward toward `Z*`. -/
lemma not_betaStable_of_lighter_upper (c₀ c₁ c₂ Z : ℝ)
    (h : isobaricMass c₀ c₁ c₂ (Z + 1) < isobaricMass c₀ c₁ c₂ Z) :
    ¬ betaStable c₀ c₁ c₂ Z := fun hs => absurd hs.2 (not_le.mpr h)

/-- **A lighter `Z−1` neighbour makes `Z` unstable** — the isobar `β⁺`/EC-decays downward toward `Z*`. -/
lemma not_betaStable_of_lighter_lower (c₀ c₁ c₂ Z : ℝ)
    (h : isobaricMass c₀ c₁ c₂ (Z - 1) < isobaricMass c₀ c₁ c₂ Z) :
    ¬ betaStable c₀ c₁ c₂ Z := fun hs => absurd hs.1 (not_le.mpr h)


/-- **Mattauch's rule** — two *adjacent* isobars `Z` and `Z+1` can both be β-stable only if their masses are
exactly equal `M(Z) = M(Z+1)`. Since the odd-even pairing term generically lifts this degeneracy, adjacent
isobars are not both stable. -/
lemma adjacent_betaStable_degenerate (c₀ c₁ c₂ Z : ℝ)
    (hZ : betaStable c₀ c₁ c₂ Z) (hZ1 : betaStable c₀ c₁ c₂ (Z + 1)) :
    isobaricMass c₀ c₁ c₂ Z = isobaricMass c₀ c₁ c₂ (Z + 1) := by
  have h1 := hZ.2
  have h2 := hZ1.1
  rw [add_sub_cancel_right] at h2
  linarith

end Physlib.QuantumMechanics.ComplexAction.Particles.NuclearBetaDecayValley

/-! ## Part III — the island of stability: an isolated doubly-magic closure beyond the fission cliff -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.NuclearStabilityIsland

open Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability
open Physlib.QuantumMechanics.ComplexAction.Particles.NuclearIsotopeStability
open Physlib.QuantumMechanics.ComplexAction.Particles.ShellFillingStability


/-- **The oscillator magic-number ladder is strictly increasing** — each shell closure exceeds the last
(`hoMagic k = closureCount oscillatorDegeneracy (k+1)`, from `ShellFillingStability`). -/
lemma hoMagic_strictMono : StrictMono hoMagic := by
  intro a b hab
  rw [← nuclear_closure_eq_hoMagic, ← nuclear_closure_eq_hoMagic]
  exact nuclear_shells_strictMono (by omega)

/-- **The island proton number** `hoMagic 5 = 112` — the next proton shell closure after lead. -/
lemma island_protonNumber : hoMagic 5 = 112 := by decide

/-- **The island neutron number** `hoMagic 6 = 168` — the next neutron shell closure. -/
lemma island_neutronNumber : hoMagic 6 = 168 := by decide


/-- **The `(112, 168)` nuclide is doubly magic** — both a proton and a neutron shell closure: the model's
superheavy island of stability. -/
lemma island_doubly_magic : IsDoublyMagic (hoMagic 5) (hoMagic 6) := ⟨⟨5, rfl⟩, ⟨6, rfl⟩⟩

/-- **The island is neutron-rich** `Z = 112 < 168 = N` — consistent with the derived neutron-excess line
(`NuclearBetaStabilityLine.stable_is_neutron_rich`). -/
lemma island_neutron_rich : hoMagic 5 < hoMagic 6 := hoMagic_strictMono (by omega)

/-- **The island lies in the superheavy region** `100 < 112` — well beyond the fission mainland. -/
lemma island_in_superheavy : 100 < hoMagic 5 := by rw [island_protonNumber]; omega


/-- **The sea of instability** — no shell closure lies strictly between `hoMagic 4` (`= 70`) and the island
`hoMagic 5` (`= 112`): the superheavy region below the island has no stabilizing closure. -/
lemma sea_of_instability (n : ℕ) (h1 : hoMagic 4 < n) (h2 : n < hoMagic 5) : ¬ IsMagic n := by
  rintro ⟨k, rfl⟩
  have h4 : 4 < k := hoMagic_strictMono.lt_iff_lt.mp h1
  have h5 : k < 5 := hoMagic_strictMono.lt_iff_lt.mp h2
  omega

/-- **The island is isolated** — the *only* shell closure in the window `(hoMagic 4, hoMagic 6) = (70, 168)` is
the island `hoMagic 5 = 112`: a single stability node surrounded by the sea of instability. -/
lemma island_isolated (n : ℕ) (h1 : hoMagic 4 < n) (h2 : n < hoMagic 6) (hm : IsMagic n) :
    n = hoMagic 5 := by
  obtain ⟨k, rfl⟩ := hm
  have h4 : 4 < k := hoMagic_strictMono.lt_iff_lt.mp h1
  have h6 : k < 6 := hoMagic_strictMono.lt_iff_lt.mp h2
  have hk5 : k = 5 := by omega
  rw [hk5]

end Physlib.QuantumMechanics.ComplexAction.Particles.NuclearStabilityIsland

/-! ## Part IV — odd-even pairing from spin-doublet filling: the even-A / odd-A split -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.NuclearPairingParity

open Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability


/-- The number of **unpaired nucleons** `Z%2 + N%2`: each spatial orbital holds a spin-doublet pair, so a like-
nucleon species contributes an unpaired nucleon exactly when its count is odd. -/
def unpaired (Z N : ℕ) : ℕ := Z % 2 + N % 2

/-- **At most two unpaired nucleons** — one proton and/or one neutron. -/
lemma unpaired_le_two (Z N : ℕ) : unpaired Z N ≤ 2 := by unfold unpaired; omega

/-- **Even-even nuclides are fully paired** `unpaired = 0`. -/
lemma evenEven_unpaired_zero (Z N : ℕ) (h : Z % 2 = 0 ∧ N % 2 = 0) : unpaired Z N = 0 := by
  unfold unpaired; omega

/-- **Odd-odd nuclides have two unpaired nucleons** `unpaired = 2`. -/
lemma oddOdd_unpaired_two (Z N : ℕ) (h : Z % 2 = 1 ∧ N % 2 = 1) : unpaired Z N = 2 := by
  unfold unpaired; omega

/-- **Even mass number ⟺ same parity** `(Z+N) even ↔ Z%2 = N%2` — even-`A` nuclides are even-even or odd-odd. -/
lemma massNumber_even_iff_same_parity (Z N : ℕ) : (Z + N) % 2 = 0 ↔ Z % 2 = N % 2 := by omega

/-- **Odd mass number ⟹ exactly one unpaired nucleon** — an odd-`A` nuclide is even-odd or odd-even. -/
lemma oddA_unpaired_one (Z N : ℕ) (h : (Z + N) % 2 = 1) : unpaired Z N = 1 := by
  unfold unpaired; omega


/-- The **pairing energy** `d · (unpaired count)` — the cost of unpaired nucleons, with `d > 0` the pair-binding
energy scale (a physical parameter). -/
noncomputable def pairingEnergy (d : ℝ) (Z N : ℕ) : ℝ := d * (unpaired Z N : ℝ)

/-- **An even-even nuclide has zero pairing energy.** -/
lemma pairingEnergy_evenEven (d : ℝ) (Z N : ℕ) (h : Z % 2 = 0 ∧ N % 2 = 0) :
    pairingEnergy d Z N = 0 := by
  unfold pairingEnergy; rw [evenEven_unpaired_zero Z N h]; simp

/-- **An odd-odd nuclide has pairing energy `2d`.** -/
lemma pairingEnergy_oddOdd (d : ℝ) (Z N : ℕ) (h : Z % 2 = 1 ∧ N % 2 = 1) :
    pairingEnergy d Z N = 2 * d := by
  unfold pairingEnergy; rw [oddOdd_unpaired_two Z N h]; push_cast; ring

/-- **Even-even sits below odd-odd** `0 < 2d`: the fully-paired nuclide has strictly lower pairing energy. -/
lemma evenEven_below_oddOdd (d : ℝ) (hd : 0 < d) (Z₁ N₁ Z₂ N₂ : ℕ)
    (he : Z₁ % 2 = 0 ∧ N₁ % 2 = 0) (ho : Z₂ % 2 = 1 ∧ N₂ % 2 = 1) :
    pairingEnergy d Z₁ N₁ < pairingEnergy d Z₂ N₂ := by
  rw [pairingEnergy_evenEven d Z₁ N₁ he, pairingEnergy_oddOdd d Z₂ N₂ ho]; linarith


/-- The **total nuclide mass**: the isobaric parabola plus the pairing energy. -/
noncomputable def nuclideMass (c₀ c₁ c₂ d : ℝ) (Z N : ℕ) : ℝ :=
  isobaricMass c₀ c₁ c₂ (Z : ℝ) + pairingEnergy d Z N

/-- **Even-even is favoured** — of two isobars at equal parabola height, the even-even nuclide is lighter (by
`2d`) than the odd-odd one. So even-`A` chains carry their even-even members on a lower effective parabola,
allowing several stable isobars. -/
lemma evenEven_lighter (c₀ c₁ c₂ d : ℝ) (hd : 0 < d) (Z₁ N₁ Z₂ N₂ : ℕ)
    (he : Z₁ % 2 = 0 ∧ N₁ % 2 = 0) (ho : Z₂ % 2 = 1 ∧ N₂ % 2 = 1)
    (hpar : isobaricMass c₀ c₁ c₂ (Z₁ : ℝ) = isobaricMass c₀ c₁ c₂ (Z₂ : ℝ)) :
    nuclideMass c₀ c₁ c₂ d Z₁ N₁ < nuclideMass c₀ c₁ c₂ d Z₂ N₂ := by
  unfold nuclideMass
  have := evenEven_below_oddOdd d hd Z₁ N₁ Z₂ N₂ he ho
  linarith

/-- **Odd-`A` chains have uniform pairing** — adjacent isobars `(Z, N)` and `(Z+1, N−1)` of an odd-`A` chain
carry the *same* pairing energy (both have one unpaired nucleon), so pairing cancels between neighbours and the
strict-convex parabola alone selects a single stable isobar. -/
lemma oddA_adjacent_pairing_eq (d : ℝ) (Z N : ℕ) (hA : (Z + N) % 2 = 1) (hN : 1 ≤ N) :
    pairingEnergy d Z N = pairingEnergy d (Z + 1) (N - 1) := by
  unfold pairingEnergy unpaired
  have h : Z % 2 + N % 2 = (Z + 1) % 2 + (N - 1) % 2 := by omega
  rw [h]

end Physlib.QuantumMechanics.ComplexAction.Particles.NuclearPairingParity

/-! ## Part V — valence nucleons and nuclear collectivity, from the shell distance -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValenceCollectivity

open Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability
open Physlib.QuantumMechanics.ComplexAction.Particles.ShellFillingParticleHole


/-- The **valence nucleons** of a shell `k` with occupancy `q` — particles or holes, whichever is fewer:
`shellDistance (oscillatorDegeneracy k) q`. -/
def valenceNucleons (k q : ℕ) : ℕ := shellDistance (oscillatorDegeneracy k) q

/-- **A just-closed shell has no valence nucleons** `valenceNucleons k 0 = 0` — a spherical magic nucleus. -/
lemma valence_closed_zero (k : ℕ) : valenceNucleons k 0 = 0 :=
  shellDistance_closed_zero _ 0 (Or.inl rfl)

/-- **A fully-filled shell has no valence nucleons** — the next magic closure, also spherical. -/
lemma valence_full_zero (k : ℕ) : valenceNucleons k (oscillatorDegeneracy k) = 0 :=
  shellDistance_closed_zero _ _ (Or.inr rfl)

/-- **The valence count is at most half the shell** `2 · valenceNucleons ≤ oscillatorDegeneracy k`. -/
lemma valence_le_half (k q : ℕ) (h : q ≤ oscillatorDegeneracy k) :
    2 * valenceNucleons k q ≤ oscillatorDegeneracy k :=
  shellDistance_le_half _ q h


/-- **Every nuclear shell has an even capacity** `Even (oscillatorDegeneracy k)` — `(k+1)(k+2)` is a product of
consecutive integers. -/
lemma oscillatorDegeneracy_even (k : ℕ) : Even (oscillatorDegeneracy k) := by
  unfold oscillatorDegeneracy
  exact Nat.even_mul_succ_self (k + 1)

/-- **The mid-shell occupancy has the maximal valence** `valenceNucleons k (C/2) = C/2`. -/
lemma midshell_valence (k : ℕ) :
    valenceNucleons k (oscillatorDegeneracy k / 2) = oscillatorDegeneracy k / 2 := by
  obtain ⟨m, hm⟩ := oscillatorDegeneracy_even k
  unfold valenceNucleons shellDistance
  omega

/-- **Collectivity peaks at mid-shell** — no occupancy has more valence nucleons than the half-filled shell, so
deformation is maximal between the magic closures. -/
lemma collectivity_max_at_midshell (k q : ℕ) (h : q ≤ oscillatorDegeneracy k) :
    valenceNucleons k q ≤ valenceNucleons k (oscillatorDegeneracy k / 2) := by
  rw [midshell_valence]
  have := valence_le_half k q h
  unfold valenceNucleons at *
  omega


/-- **Nuclear valence is particle-hole symmetric** — a shell with `q` nucleons and one with `C − q` (holes)
have the same valence count, hence the same collectivity. -/
lemma nuclear_valence_particle_hole (k q : ℕ) (h : q ≤ oscillatorDegeneracy k) :
    valenceNucleons k q = valenceNucleons k (oscillatorDegeneracy k - q) :=
  shellDistance_particle_hole _ q h

end Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValenceCollectivity

/-! ## Part VI — the spin-orbit magic numbers: `2, 8, 20, 28, 50, 82, 126, 184` -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.NuclearSpinOrbitMagic

open Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability
open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers

open Finset


/-- The **`j = l + ½` level degeneracy** `2j+1 = 2l+2` — the intruder (energy-lowered) level. -/
def jUpDeg (l : ℕ) : ℕ := 2 * l + 2

/-- The **`j = l − ½` level degeneracy** `2j+1 = 2l`. -/
def jDownDeg (l : ℕ) : ℕ := 2 * l

/-- **Spin-orbit splitting conserves states** `(2l+2) + 2l = 2(2l+1)` — the two `j`-levels partition the full
`l` capacity. -/
lemma spinOrbit_conserves (l : ℕ) : jUpDeg l + jDownDeg l = capacityOfAngularMomentum l := by
  unfold jUpDeg jDownDeg capacityOfAngularMomentum; omega


/-- The **intruder-level degeneracy** of oscillator shell `N` — its highest orbital `l = N` with `j = N + ½`,
degeneracy `2N + 2`. -/
def intruderDeg (N : ℕ) : ℕ := 2 * N + 2

/-- The **shell remainder** after removing the intruder — `N(N+1)`. -/
def leftoverDeg (N : ℕ) : ℕ := N * (N + 1)

/-- **A shell minus its intruder is `N(N+1)`** `oscillatorDegeneracy N − intruderDeg N = N(N+1)` — the intruder
drops down, leaving this remainder in the original shell. -/
lemma shell_minus_intruder (N : ℕ) :
    oscillatorDegeneracy N - intruderDeg N = leftoverDeg N := by
  unfold oscillatorDegeneracy intruderDeg leftoverDeg; ring_nf; omega


/-- The **spin-orbit shell gap** at closure `k`: the pure oscillator shells for `k ≤ 2`, the bare intruder at
`k = 3`, and `leftover(k−1) + intruder(k)` beyond (the previous shell's remainder plus the new intruder). -/
def socGap (k : ℕ) : ℕ :=
  if k ≤ 2 then oscillatorDegeneracy k
  else if k = 3 then intruderDeg 3
  else leftoverDeg (k - 1) + intruderDeg k

/-- The **spin-orbit magic number** — the cumulative shell gaps. -/
def socMagic (k : ℕ) : ℕ := ∑ i ∈ range (k + 1), socGap i

/-- **The spin-orbit magic numbers** `2, 8, 20, 28, 50, 82, 126, 184` — the experimentally observed nuclear
shell closures. -/
lemma socMagic_values :
    socMagic 0 = 2 ∧ socMagic 1 = 8 ∧ socMagic 2 = 20 ∧ socMagic 3 = 28 ∧ socMagic 4 = 50
      ∧ socMagic 5 = 82 ∧ socMagic 6 = 126 ∧ socMagic 7 = 184 := by decide

/-- **The first three magic numbers agree with the pure oscillator** `2, 8, 20` — spin-orbit does not shift the
closures through `l = 2`. -/
lemma first_three_match_hoMagic :
    socMagic 0 = hoMagic 0 ∧ socMagic 1 = hoMagic 1 ∧ socMagic 2 = hoMagic 2 := by decide

/-- **Spin-orbit shifts the fourth closure** `socMagic 3 = 28 ≠ 40 = hoMagic 3` — the `1f₇⁄₂` intruder creates
the new magic number `28`, absent from the pure oscillator. -/
lemma spin_orbit_shifts_at_28 : socMagic 3 = 28 ∧ hoMagic 3 = 40 ∧ socMagic 3 ≠ hoMagic 3 := by decide


/-- **The corrected superheavy island is `(126, 184)`** — both `socMagic 6 = 126` and `socMagic 7 = 184` are
spin-orbit magic, so the doubly-magic superheavy nucleus is `Z ≈ 126, N = 184`, the spin-orbit correction of
the pure-oscillator `(112, 168)` island (`NuclearStabilityIsland`). -/
lemma soc_island : socMagic 6 = 126 ∧ socMagic 7 = 184 := by decide

end Physlib.QuantumMechanics.ComplexAction.Particles.NuclearSpinOrbitMagic

/-! ## Part VII — isotope spin statistics from nucleon pairing: `A` even ⇒ boson, `A` odd ⇒ fermion -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.IsotopeNuclearSpinStatistics

open Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics
open Physlib.QuantumMechanics.ComplexAction.Particles.NuclearPairingParity
open Physlib.QuantumMechanics.ComplexAction.ExchangeStatisticsSpectrum


/-- The **exchange phase of a nucleus** `(Z, N)` — the composite twist of its `A = Z + N` spin-½ nucleons,
`(−1)^A`. -/
noncomputable def nucleusExchange (Z N : ℕ) : ℂ := compositeTwist (Z + N)

/-- **An even-`A` nucleus is a boson** — `A` even ⇒ exchange phase `+1`. -/
lemma nucleus_boson (Z N : ℕ) (h : Even (Z + N)) : IsBosonic (nucleusExchange Z N) := by
  unfold IsBosonic nucleusExchange
  rw [compositeTwist_eq, h.neg_one_pow]

/-- **An odd-`A` nucleus is a fermion** — `A` odd ⇒ exchange phase `−1`. -/
lemma nucleus_fermion (Z N : ℕ) (h : Odd (Z + N)) : IsFermionic (nucleusExchange Z N) := by
  unfold IsFermionic nucleusExchange
  rw [compositeTwist_eq, h.neg_one_pow]


/-- **`¹²C` is a boson** — `A = 12` (even-even). -/
lemma carbon12_boson : IsBosonic (nucleusExchange 6 6) := nucleus_boson 6 6 (by decide)

/-- **`¹³C` is a fermion** — `A = 13` (odd). -/
lemma carbon13_fermion : IsFermionic (nucleusExchange 6 7) := nucleus_fermion 6 7 (by decide)

/-- **`¹⁶O` is a boson** — `A = 16` (even-even, `I = 0`). -/
lemma oxygen16_boson : IsBosonic (nucleusExchange 8 8) := nucleus_boson 8 8 (by decide)

/-- **The deuteron is a boson** — `A = 2` (odd-odd, `I = 1`). -/
lemma deuteron_boson : IsBosonic (nucleusExchange 1 1) := nucleus_boson 1 1 (by decide)


/-- **An even-even nucleus is fully paired** `unpaired = 0` — every proton and neutron has a partner, so the
ground-state spin is `0` and there is a single (`I = 0`) nuclear-spin state: the symmetric spin function
underlying the `¹²C₆₀` Bose–Einstein selection rule. -/
lemma evenEven_fully_paired (Z N : ℕ) (h : Z % 2 = 0 ∧ N % 2 = 0) : unpaired Z N = 0 :=
  evenEven_unpaired_zero Z N h

/-- **`¹²C` is fully paired** `unpaired 6 6 = 0` — the even-even carbon-12 nucleus has spin `0`. -/
lemma carbon12_fully_paired : unpaired 6 6 = 0 := by decide

end Physlib.QuantumMechanics.ComplexAction.Particles.IsotopeNuclearSpinStatistics

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.NuclearIsotopeStability.stableNeutronNumber_consistent where
  formalizes @ "claim:the-stable-neutron-line-is-the-exact-inverse-of-the-isobaric-beta-valley",
  supported_by @ "paper:mattauch-1934-isobar-rule"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.NuclearBetaDecayValley.adjacent_betaStable_degenerate where
  formalizes @ "claim:mattauch-rule-adjacent-isobars-are-both-stable-only-under-exact-mass-degeneracy",
  requires @ "claim:the-stable-neutron-line-is-the-exact-inverse-of-the-isobaric-beta-valley",
  supported_by @ "paper:mattauch-1934-isobar-rule"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.NuclearSpinOrbitMagic.socMagic_values where
  formalizes @ "claim:the-spin-orbit-intruder-mechanism-derives-the-observed-magic-numbers-two-eight-twenty-twenty-eight-fifty-eighty-two-one-twenty-six-one-eighty-four",
  supported_by @ "paper:mayer-jensen-1949-nuclear-shell-model",
  caveat @ "claim:the-mayer-jensen-intruder-ordering-is-encoded-and-the-numbers-then-derived"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.IsotopeNuclearSpinStatistics.nucleus_boson where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics.compositeTwist_eq",
  formalizes @ "claim:an-even-mass-nucleus-is-a-boson-via-the-composite-twist-minus-one-to-the-A",
  requires @ "claim:mattauch-rule-adjacent-isobars-are-both-stable-only-under-exact-mass-degeneracy"

zil_file_contract physlib.nuclearIsotopeStability where
  promises "The isotope-stability tower: the stable-neutron line is the exact inverse of the beta valley, Mattauch's rule requires exact mass degeneracy for adjacent co-stability, the spin-orbit intruder mechanism derives the observed magic numbers through one-eighty-four, and an even-mass nucleus is a boson via the composite twist."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.NuclearIsotopeStability.stableNeutronNumber",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.NuclearSpinOrbitMagic.socMagic",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.IsotopeNuclearSpinStatistics.nucleusExchange"]
  forbids_substitutes ["a derivation of the Mayer-Jensen intruder ordering, which is encoded",
    "the detailed level coupling behind the even-even I equals zero ground state"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.NuclearIsotopeStability.stableNeutronNumber_consistent,
    Physlib.QuantumMechanics.ComplexAction.Particles.NuclearBetaDecayValley.adjacent_betaStable_degenerate,
    Physlib.QuantumMechanics.ComplexAction.Particles.NuclearSpinOrbitMagic.socMagic_values,
    Physlib.QuantumMechanics.ComplexAction.Particles.IsotopeNuclearSpinStatistics.nucleus_boson]

/- ZIL-END -/

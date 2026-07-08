/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Thermodynamics.EntropicInformationRate
public import Physlib.Thermodynamics.BekensteinJacobsonEntropicBits
public import Physlib.Thermodynamics.Landauer

/-!
# Information-channel stress from entropy, KL, and mutual-information throughput

This module extracts the theorem-level kernel from the signal-integrity
reading in `/Users/macbookpro/Downloads/tau/gemdec22-2025.md` around line
58174:

* stress is not a new primitive physical force;
* it is the load of an information rate against an available channel capacity;
* KL divergence and mutual information enter as entropy-production payloads,
  measured in nats and converted to bits by `landauerInfoRate`.

The load-bearing definition is

```text
load := informationRateBits / capacityBitsPerTime
slack := capacityBitsPerTime - informationRateBits
```

and the main theorems prove the exact equivalences:

```text
within capacity  ↔  load ≤ 1  ↔  slack ≥ 0
critical stress  ↔  load = 1  ↔  slack = 0
over capacity    ↔  load > 1  ↔  slack < 0
```

No particle-decay, impedance-mismatch, or coding-theory analogy is assumed.
Concrete physics enters only when another module supplies an entropy/KL/mutual
information rate and a capacity.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics.InformationChannelStress

open Physlib.Thermodynamics
open Physlib.Thermodynamics.Landauer

/-! ## Channel load and slack -/

/-- A real information channel with a strictly positive bit-rate capacity and a
non-negative transmitted information rate.  Both fields are measured in bits per
unit time. -/
structure InformationChannel where
  /-- Channel capacity, in bits per unit time. -/
  capacityBitsPerTime : ℝ
  /-- transmitted information rate, in bits per unit time. -/
  informationRateBits : ℝ
  /-- Capacity is strictly positive. -/
  capacity_pos : 0 < capacityBitsPerTime
  /-- The transmitted information rate is non-negative. -/
  rate_nonneg : 0 ≤ informationRateBits

/-- Channel load: the fraction of available capacity used by the transmitted information rate. -/
def channelLoad (χ : InformationChannel) : ℝ :=
  χ.informationRateBits / χ.capacityBitsPerTime

/-- Capacity slack: the unused bit-rate capacity. -/
def capacitySlack (χ : InformationChannel) : ℝ :=
  χ.capacityBitsPerTime - χ.informationRateBits

/-- The channel is operating within its capacity. -/
def WithinCapacity (χ : InformationChannel) : Prop :=
  χ.informationRateBits ≤ χ.capacityBitsPerTime

/-- Strictly below capacity. -/
def LowStress (χ : InformationChannel) : Prop :=
  χ.informationRateBits < χ.capacityBitsPerTime

/-- Exactly at capacity. -/
def CriticalStress (χ : InformationChannel) : Prop :=
  χ.informationRateBits = χ.capacityBitsPerTime

/-- Above capacity. -/
def OverCapacity (χ : InformationChannel) : Prop :=
  χ.capacityBitsPerTime < χ.informationRateBits

@[simp] theorem channelLoad_nonneg (χ : InformationChannel) :
    0 ≤ channelLoad χ := by
  unfold channelLoad
  exact div_nonneg χ.rate_nonneg χ.capacity_pos.le

/-- Operating within capacity is exactly the condition `load ≤ 1`. -/
theorem withinCapacity_iff_load_le_one (χ : InformationChannel) :
    WithinCapacity χ ↔ channelLoad χ ≤ 1 := by
  unfold WithinCapacity channelLoad
  constructor
  · intro h
    rw [div_le_iff₀ χ.capacity_pos]
    simpa [one_mul] using h
  · intro h
    rw [div_le_iff₀ χ.capacity_pos] at h
    simpa [one_mul] using h

/-- Strictly sub-capacity operation is exactly `load < 1`. -/
theorem lowStress_iff_load_lt_one (χ : InformationChannel) :
    LowStress χ ↔ channelLoad χ < 1 := by
  unfold LowStress channelLoad
  constructor
  · intro h
    rw [div_lt_iff₀ χ.capacity_pos]
    simpa [one_mul] using h
  · intro h
    rw [div_lt_iff₀ χ.capacity_pos] at h
    simpa [one_mul] using h

/-- Critical stress is exactly `load = 1`. -/
theorem criticalStress_iff_load_eq_one (χ : InformationChannel) :
    CriticalStress χ ↔ channelLoad χ = 1 := by
  unfold CriticalStress channelLoad
  constructor
  · intro h
    rw [h]
    exact div_self (ne_of_gt χ.capacity_pos)
  · intro h
    have hcap_ne : χ.capacityBitsPerTime ≠ 0 := ne_of_gt χ.capacity_pos
    field_simp [hcap_ne] at h
    simpa using h

/-- Above-capacity operation is exactly `load > 1`. -/
theorem overCapacity_iff_load_gt_one (χ : InformationChannel) :
    OverCapacity χ ↔ 1 < channelLoad χ := by
  unfold OverCapacity channelLoad
  constructor
  · intro h
    rw [lt_div_iff₀ χ.capacity_pos]
    simpa [one_mul] using h
  · intro h
    rw [lt_div_iff₀ χ.capacity_pos] at h
    simpa [one_mul] using h

/-- Operating within capacity is exactly non-negative slack. -/
theorem slack_nonneg_iff_withinCapacity (χ : InformationChannel) :
    0 ≤ capacitySlack χ ↔ WithinCapacity χ := by
  unfold capacitySlack WithinCapacity
  constructor <;> intro h <;> linarith

/-- Critical stress is exactly zero slack. -/
theorem criticalStress_iff_slack_eq_zero (χ : InformationChannel) :
    CriticalStress χ ↔ capacitySlack χ = 0 := by
  unfold CriticalStress capacitySlack
  constructor <;> intro h <;> linarith

/-- Above-capacity operation is exactly negative slack. -/
theorem overCapacity_iff_slack_neg (χ : InformationChannel) :
    OverCapacity χ ↔ capacitySlack χ < 0 := by
  unfold OverCapacity capacitySlack
  constructor <;> intro h <;> linarith

/-- Slack is capacity times the remaining unloaded fraction. -/
theorem slack_eq_capacity_mul_one_sub_load (χ : InformationChannel) :
    capacitySlack χ = χ.capacityBitsPerTime * (1 - channelLoad χ) := by
  unfold capacitySlack channelLoad
  have hcap_ne : χ.capacityBitsPerTime ≠ 0 := ne_of_gt χ.capacity_pos
  field_simp [hcap_ne]

/-! ## KL and mutual-information throughput -/

/-- KL-divergence production rate, measured in nats per unit time. -/
abbrev KullbackLeiblerRate : Type := ℝ

/-- Mutual-information production/throughput rate, measured in nats per unit
time.  Mutual information is a KL divergence of a joint state from the product
of its marginals, so the same nat-rate conversion applies. -/
abbrev MutualInformationRate : Type := ℝ

/-- KL-divergence throughput converted from nats/time to bits/time. -/
def klInformationRateBits (Ddot : KullbackLeiblerRate) : ℝ :=
  landauerInfoRate Ddot

/-- Mutual-information throughput converted from nats/time to bits/time. -/
def mutualInformationRateBits (Idot : MutualInformationRate) : ℝ :=
  landauerInfoRate Idot

@[simp] theorem klInformationRateBits_eq (Ddot : KullbackLeiblerRate) :
    klInformationRateBits Ddot = Ddot / Real.log 2 := rfl

@[simp] theorem mutualInformationRateBits_eq (Idot : MutualInformationRate) :
    mutualInformationRateBits Idot = Idot / Real.log 2 := rfl

/-- Non-negative KL production gives non-negative bit throughput. -/
theorem klInformationRateBits_nonneg {Ddot : KullbackLeiblerRate}
    (hD : 0 ≤ Ddot) :
    0 ≤ klInformationRateBits Ddot := by
  unfold klInformationRateBits landauerInfoRate
  exact div_nonneg hD (le_of_lt Physlib.Thermodynamics.log_two_pos)

/-- Non-negative mutual-information production gives non-negative bit
throughput. -/
theorem mutualInformationRateBits_nonneg {Idot : MutualInformationRate}
    (hI : 0 ≤ Idot) :
    0 ≤ mutualInformationRateBits Idot := by
  unfold mutualInformationRateBits landauerInfoRate
  exact div_nonneg hI (le_of_lt Physlib.Thermodynamics.log_two_pos)

/-- KL throughput as a channel. -/
def channelFromKLRate
    (capacityBitsPerTime : ℝ) (Ddot : KullbackLeiblerRate)
    (hC : 0 < capacityBitsPerTime) (hD : 0 ≤ Ddot) :
    InformationChannel where
  capacityBitsPerTime := capacityBitsPerTime
  informationRateBits := klInformationRateBits Ddot
  capacity_pos := hC
  rate_nonneg := klInformationRateBits_nonneg hD

/-- Mutual-information throughput as a channel. -/
def channelFromMutualInformationRate
    (capacityBitsPerTime : ℝ) (Idot : MutualInformationRate)
    (hC : 0 < capacityBitsPerTime) (hI : 0 ≤ Idot) :
    InformationChannel where
  capacityBitsPerTime := capacityBitsPerTime
  informationRateBits := mutualInformationRateBits Idot
  capacity_pos := hC
  rate_nonneg := mutualInformationRateBits_nonneg hI

/-- KL bit throughput is within capacity iff the KL nat-rate is below
`capacity · log 2`. -/
theorem klInformationRateBits_le_capacity_iff
    (capacityBitsPerTime : ℝ) (Ddot : KullbackLeiblerRate) :
    klInformationRateBits Ddot ≤ capacityBitsPerTime
      ↔ Ddot ≤ capacityBitsPerTime * Real.log 2 := by
  unfold klInformationRateBits landauerInfoRate
  rw [div_le_iff₀ Physlib.Thermodynamics.log_two_pos]

/-- Mutual-information bit throughput is within capacity iff the mutual
information nat-rate is below `capacity · log 2`. -/
theorem mutualInformationRateBits_le_capacity_iff
    (capacityBitsPerTime : ℝ) (Idot : MutualInformationRate) :
    mutualInformationRateBits Idot ≤ capacityBitsPerTime
      ↔ Idot ≤ capacityBitsPerTime * Real.log 2 := by
  unfold mutualInformationRateBits landauerInfoRate
  rw [div_le_iff₀ Physlib.Thermodynamics.log_two_pos]

/-- The KL channel is within capacity exactly when its nat-rate satisfies the
converted Shannon/Landauer capacity bound. -/
theorem klChannel_withinCapacity_iff_natsRate_le
    (capacityBitsPerTime : ℝ) (Ddot : KullbackLeiblerRate)
    (hC : 0 < capacityBitsPerTime) (hD : 0 ≤ Ddot) :
    WithinCapacity (channelFromKLRate capacityBitsPerTime Ddot hC hD)
      ↔ Ddot ≤ capacityBitsPerTime * Real.log 2 := by
  unfold WithinCapacity channelFromKLRate
  exact klInformationRateBits_le_capacity_iff capacityBitsPerTime Ddot

/-- The mutual-information channel is within capacity exactly when its
nat-rate satisfies the converted Shannon/Landauer capacity bound. -/
theorem mutualChannel_withinCapacity_iff_natsRate_le
    (capacityBitsPerTime : ℝ) (Idot : MutualInformationRate)
    (hC : 0 < capacityBitsPerTime) (hI : 0 ≤ Idot) :
    WithinCapacity
        (channelFromMutualInformationRate capacityBitsPerTime Idot hC hI)
      ↔ Idot ≤ capacityBitsPerTime * Real.log 2 := by
  unfold WithinCapacity channelFromMutualInformationRate
  exact mutualInformationRateBits_le_capacity_iff capacityBitsPerTime Idot

/-- KL channel load in nats/time form. -/
theorem klChannel_load_eq_natsRate_div_capacity_log
    (capacityBitsPerTime : ℝ) (Ddot : KullbackLeiblerRate)
    (hC : 0 < capacityBitsPerTime) (hD : 0 ≤ Ddot) :
    channelLoad (channelFromKLRate capacityBitsPerTime Ddot hC hD)
      = Ddot / (capacityBitsPerTime * Real.log 2) := by
  unfold channelLoad channelFromKLRate klInformationRateBits landauerInfoRate
  have hC_ne : capacityBitsPerTime ≠ 0 := ne_of_gt hC
  have hlog_ne : Real.log 2 ≠ 0 := ne_of_gt Physlib.Thermodynamics.log_two_pos
  field_simp [hC_ne, hlog_ne]

/-- Mutual-information channel load in nats/time form. -/
theorem mutualChannel_load_eq_natsRate_div_capacity_log
    (capacityBitsPerTime : ℝ) (Idot : MutualInformationRate)
    (hC : 0 < capacityBitsPerTime) (hI : 0 ≤ Idot) :
    channelLoad
        (channelFromMutualInformationRate capacityBitsPerTime Idot hC hI)
      = Idot / (capacityBitsPerTime * Real.log 2) := by
  unfold channelLoad channelFromMutualInformationRate mutualInformationRateBits landauerInfoRate
  have hC_ne : capacityBitsPerTime ≠ 0 := ne_of_gt hC
  have hlog_ne : Real.log 2 ≠ 0 := ne_of_gt Physlib.Thermodynamics.log_two_pos
  field_simp [hC_ne, hlog_ne]

/-! ## Complex-action and Bekenstein capacity hooks -/

/-- Complex-action information rate in bits/time, using the existing
`complexActionBits` conversion on an imaginary-action rate. -/
def complexActionInformationRateBits (hbar SIdot : ℝ) : ℝ :=
  complexActionBits hbar SIdot

/-- Complex-action bit-rate equals the Landauer conversion of the
complex-action nat-rate. -/
theorem complexActionInformationRateBits_eq_landauerInfoRate_nats
    (hbar SIdot : ℝ) :
    complexActionInformationRateBits hbar SIdot
      = landauerInfoRate (complexActionNats hbar SIdot) := by
  unfold complexActionInformationRateBits landauerInfoRate
  rw [complexActionBits_eq_nats_div_log2]

/-- Bekenstein bit capacity per unit time. -/
def bekensteinBitsPerTime (A ℓP Δt : ℝ) : ℝ :=
  bekensteinBits A ℓP / Δt

/-- Positive area, non-zero Planck length, and positive time window give a
positive Bekenstein bit-rate capacity. -/
theorem bekensteinBitsPerTime_pos
    {A ℓP Δt : ℝ} (hA : 0 < A) (hℓP : ℓP ≠ 0) (hΔt : 0 < Δt) :
    0 < bekensteinBitsPerTime A ℓP Δt := by
  unfold bekensteinBitsPerTime bekensteinBits
  apply div_pos
  · apply div_pos hA
    apply mul_pos
    · apply mul_pos
      · norm_num
      · exact sq_pos_of_ne_zero hℓP
    · exact Physlib.Thermodynamics.log_two_pos
  · exact hΔt

/-- KL throughput bounded by a Bekenstein channel capacity, written in nats/time
so the capacity conversion is explicit. -/
theorem klWithinBekensteinCapacity_iff_natsRate_le
    {A ℓP Δt : ℝ} (hA : 0 < A) (hℓP : ℓP ≠ 0) (hΔt : 0 < Δt)
    (Ddot : KullbackLeiblerRate) (hD : 0 ≤ Ddot) :
    WithinCapacity
        (channelFromKLRate (bekensteinBitsPerTime A ℓP Δt) Ddot
          (bekensteinBitsPerTime_pos hA hℓP hΔt) hD)
      ↔ Ddot ≤ bekensteinBitsPerTime A ℓP Δt * Real.log 2 := by
  exact klChannel_withinCapacity_iff_natsRate_le
    (bekensteinBitsPerTime A ℓP Δt) Ddot
    (bekensteinBitsPerTime_pos hA hℓP hΔt) hD

end Physlib.Thermodynamics.InformationChannelStress

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Entropic-time formalization — overview, empirical anchoring,
and methodology trail

This module is **documentation only**: no definitions, no
theorems. It exists to give a reader the full context for the
entropic-time / Bender-complex-energy formalization that lives
across five physlib files. Without this context the individual
theorems are correct but disconnected from the experimental
papers and methodology choices that motivated them.

## 1. What the formalization covers

The Bender-Brody-Hook 2008 identity bridges three views of a
non-Hermitian decay:

 `dS_I/dt = −Im E`, `Γ = 2 · dS_I/dt`, `τ = ℏ / Γ`.

That is, the entropy-production rate `Ṡ_I`, the resonance width
`Γ`, and the lifetime `τ` are inter-convertible via algebraic
relations and the constant `ℏ`. This relation lives in
`Physlib.QuantumMechanics.ComplexAction.BenderIdentity`.

Around this algebraic core, the library adds:

* the Euclidean–Lorentzian crossover (KMS state ↔ thermal rate),
 in `Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KMS`;

* the Pendry-2021 photon-number-conservation theorem in
 `Physlib.QuantumMechanics.ComplexAction.PendryPhotonConservation`;

* a six-timescale taxonomy (envelope, coherence, population,
 Gamow, Drude, avalanche) together with three candidate
 identification predicates and the Pendry-2024
 effective-damping decomposition, in
 `Physlib.Optics.MaterialTimescales`;

* a concrete experimental instance — pump-modulated indium tin
 oxide at the epsilon-near-zero wavelength, anchored against
 three published measurements — in
 `Physlib.Optics.ITOAvalancheCase`.

## 2. The papers

The formalization is anchored to seven publications. Each is
cited in the individual modules; here is the complete chain at
a glance.

* **Bender, Boettcher (1998)** — PT-symmetric Hamiltonians can
 have real spectra. Establishes the framework in which
 non-Hermitian dynamics can be physically sensible.

* **Bender, Brody, Hook (2008)** — Complex-action / complex-
 energy translation. This is the *algebraic content* the
 library formalises in BenderIdentity.lean.

* **Pendry (2021)** — Photon-number conservation in PT-symmetric
 time-dependent media. Identifies a **conservation law**
 (photon count) stronger than energy in the right regime.
 Formalised in PendryPhotonConservation.lean.

* **Tirole et al. (2022)** — Temporal double-slit interference
 in pump-modulated ITO. Reports a 1–10 fs rise time of the
 reflectivity, "unexplained by theory" at publication.

* **Galiffi et al. (2024)** — Coherent perfect absorption and
 parametric amplification in the same ITO platform. Provides
 ellipsometric Drude scattering rate `γ_Drude = 0.13 fs⁻¹`
 and Floquet eigenmode observation `Im[ω]/Ω ≈ ±0.1`.

* **Pendry (2024)** — Auger-avalanche model: pump field
 accelerates background electrons, when each reaches the
 band gap an Auger process cascades, giving exponential
 electron-density growth `n(t) = n_0 · exp(β t)` with
 `β = E·e / √(U_G·m)`. Effective Drude damping becomes
 `γ_eff = γ_Drude − β` (his eq. 6); above threshold this is
 *negative*, recovering Bender's complex-energy gain mode
 from microscopic physics.

* **Oue, Pendry, Silveirinha (2024)** — Stable-to-unstable
 transition in quantum friction. A *third* physical
 mechanism for the Bender gain mode (alongside PT-symmetric
 time gratings and the Auger avalanche): two metallic plates
 in shear motion at velocity `±v/2`, the Doppler-shifted
 Drude permittivity becomes negative-imaginary for
 short-wavelength modes (`|k_x|·v/2 > ω`), creating a gain
 regime. Critical velocity `v̄_cr ≈ −2/log(γ̄)` (their
 eq. 15). Theoretical; no direct experimental measurement.
 Formalised as a second concrete instance in
 `QuantumFrictionCase.lean`.

## 3. Lean module chain

```
BenderIdentity algebraic identity + decay law (§G)
 + complex energy (§H)
 │
 ├──> ThermoFieldDynamics.KMS Euclidean modular ↔ Lorentzian thermal
 │
 └──> PendryPhotonConservation
 IsPendryEvolution → photon conservation
 (Maxwell-derivation gap named)

MaterialTimescales six named timescales (Env, T₂, T₁, Gamow,
 Drude, Avalanche)
 three identification Props
 Pendry effective-damping decomposition
 IsGainMode / IsDecayMode / IsAtThreshold
 with iff theorems

ITOAvalancheCase concrete numerical instances:
 - galiffiLowPumpDecomposition (DECAY)
 - tiroleThresholdDecomposition (BOUNDARY)
 - tiroleDecomposition (GAIN)
 - galiffiHighPumpDecomposition (EXTREME GAIN)
 each with a proved regime theorem.
```

## 4. Methodology — three candidate identifications

The framework is intentionally non-committal about *which*
physical timescale plays the role of the Bender lifetime in any
given experiment. Three candidate identifications are recorded
explicitly as Props in MaterialTimescales:

 (A) `IsLiteralRiseTimeIdentification`:
 `τ_Gamow = τ_envelope`. Naive reading of complex-action/entropic-time paper
 text that identifies the entropic timescale with the
 pump-pulse rise time `τ_rise` from Tirole 2022.

 (B) `IsMediumDephasingIdentification`:
 `τ_Gamow = T_2`. The natural identification for an open
 quantum system probed by interferometry: the Bender Γ is
 the dephasing rate of the medium.

 (C) `IsAvalancheIdentification`:
 `τ_Gamow = τ_β` (Pendry 2024). The avalanche switching
 time `τ_β = √(U_G·m)/(E·e)` — pump-field-dependent,
 microscopically derived from Auger dynamics.

Each is an **empirical hypothesis**, not a theorem. Downstream
code stating "the Bender Γ for this system is X" must attach
the relevant Prop and accept the responsibility of justifying
it from data.

## 5. What the experimental anchoring shows

For the ITO/ENZ class of experiments (Tirole 2022, Galiffi 2024),
the methodology trail across our analysis can be summarised as:

 (a) **Identification (A) — literal rise time — looked
 initially attractive** because Tirole's τ_rise ≈ 7 fs
 and Galiffi's τ_Drude ≈ 7.7 fs agree to ~10 %. This
 suggested they were the same physical quantity.

 (b) **Identification (A) is, however, not the empirically
 supported one.** Tirole's spectrum-envelope fit and
 Galiffi's ellipsometry MEASURE DIFFERENT THINGS that
 only numerically coincide at the threshold pump
 intensity Pendry 2024 identifies. Away from threshold
 (e.g. at Galiffi's I_pump = 18 GW/cm²), τ_Drude stays
 fixed at 7.7 fs while τ_β slows to 11.2 fs.

 (c) **Identification (B) — medium dephasing T_2 — was
 briefly considered** when a Bender-Drude exponential
 failed to fit Galiffi's V(I_pump) curve. An apparent
 fit to T_2 ≈ 0.57 ps emerged from a 2-level QuTiP toy.

 (d) **Identification (B) does not survive scrutiny either.**
 The 2-level QuTiP fit was extracting the visibility of
 a single underlying fringe pattern repeatedly (six
 Extended_Fig_3d model curves at fixed slit separation
 share the same fringes by construction). The supposed
 T_2 ≈ 0.57 ps value was an artifact of the wrong data
 axis.

 (e) **Identification (C) — Pendry-2024 avalanche — is the
 supported one.** At Tirole's working pump
 I_pump = 124 GW/cm²:

 γ_Drude (Galiffi) = 1.30 × 10¹⁴ s⁻¹
 β (Pendry) = 2.34 × 10¹⁴ s⁻¹
 γ_eff (Pendry §6) = −1.04 × 10¹⁴ s⁻¹ (negative)

 Negative `γ_eff` is the Bender complex-energy gain
 mode, consistent with Galiffi's experimental observation
 of parametric amplification up to 2600 %. This is the
 `tirole_is_gain_mode` theorem in ITOAvalancheCase.

The library records Props (A), (B), (C) all explicitly,
because future experiments may live in different regimes. The
ITO-specific evidence for (C) at Tirole's pump intensity is the
only currently-anchored instantiation.

## 6. Visibility observables: the photon-conservation regime

A separate question is what governs the *fringe visibility*
observable measured in either experiment. Naive expectation
would be a Bender-decay exponential `V(x) = V_max · exp(−Γ·x)`,
but this fits neither Tirole's nor Galiffi's data:

* Tirole's six rise-time-labelled spectra in Extended_Fig_3d
 are theoretical model curves at fixed slit separation, not
 independent measurements at six physical rise times. No
 V-vs-τ_rise sweep is available in the published data.

* Galiffi's V(I_pump) curve from Fig 5b is non-monotonic
 (drops to 0.72 at I_pump = 294 GW/cm², recovers to 0.80 at
 589 GW/cm²) and is attributed by the authors to classical-EM
 spectral redshift of the Signal vs Phase-Conjugated Ancilla,
 not to quantum decoherence.

Both observables live in **Pendry's photon-conservation
regime**. Per Pendry 2021, in a PT-symmetric time-dependent
medium the time evolution preserves photon number — visibility
loss in such experiments is governed by spectral overlap of
Floquet eigenmodes, a unitary photon-conserving redistribution
that has nothing to do with the Bender Γ that governs
amplitude decay of an unstable state.

The library makes this distinction explicit:

* `IsPhotonConservationRegime` (MaterialTimescales §E) flags
 systems in Pendry's regime;
* `pendry_photon_conservation` (PendryPhotonConservation §C)
 proves that under any `IsPendryEvolution` evolution, the
 photon number is invariant;
* Failure of a Bender-decay fit on Pendry-regime data is **not**
 a refutation of the Bender identity; it indicates a
 model-class mismatch (the wrong conservation law).

## 7. What is formalized vs what is a hypothesis

**Formalized in Lean (proved by ordinary tactics):**

* algebraic Bender identity §A–§F (BenderIdentity);
* Bender exponential decay law `exp(−t/τ)` §G;
* QIF lifetime ↔ `1/e` time bridge §G;
* complex-energy projections §H;
* KMS Euclidean–Lorentzian inversion `β·λ_th = 1`;
* photon-conservation theorem given `IsPendryEvolution`;
* gain ↔ decay ↔ threshold characterisations for any
 `EffectiveDampingDecomposition`;
* literal-rise-time refutation lemma (algebraic);
* four concrete ITO regime instances with proved regime
 theorems.

**Represented as Props (empirical inputs, not theorems):**

* `IsLiteralRiseTimeIdentification`,
 `IsMediumDephasingIdentification`,
 `IsAvalancheIdentification` — per-experiment mappings;
* `IsPlanckianSaturation`, `IsSubPlanckian` — KMS regime flags;
* `IsPhotonConservationRegime` — Pendry-regime flag (opaque
 `True` structure);
* `IsPendryEvolution` — Maxwell+PT-symmetric Pendry-2021
 hypothesis (the Maxwell derivation is out of scope).

**Open in physlib (acknowledged):**

* Source-free Maxwell formalisation;
* Bloch / Floquet decomposition framework;
* Transfer-matrix construction;
* Operator-exp `exp(−iHt/ℏ)` for non-Hermitian generators;
* Tomita-Takesaki modular-flow infrastructure.

The first three would supply a witness for `IsPendryEvolution`
directly. The fourth would lift §G's scalar decay law to a
full state-evolution theorem. None are blocking the current
claims; all are natural follow-up work.

## 8. Cross-paper anchoring at a glance

For ITO at the ENZ wavelength `λ_ENZ = 1196 nm`:

| Quantity | Value | Source |
| -------------- | ----------------- | ----------------------------------- |
| `λ_p` | 597 nm | Galiffi 2024 Methods Sec. 1 |
| `ε_∞` | 4.08 | Galiffi 2024 Methods Sec. 1 |
| `γ_Drude` | 0.13 fs⁻¹ | Galiffi 2024 (ellipsometry) |
| `τ_Drude` | 7.7 fs | `= 1 / γ_Drude` |
| `U_G` | 3 eV | Pendry 2024 Eq. 9 (band gap) |
| `β_inst` | 0.002 cm²/GW | Galiffi 2024 (instantaneous Kerr) |
| `β_slow` | −0.0003 cm²/GW | Galiffi 2024 (slow plasma redshift) |
| Threshold I | 38.3 GW/cm² | computed; Pendry stated ≈ 50 GW/cm² |
| τ_rise (Tirole)| ≈ 7 fs | Tirole 2022 envelope fit |
| τ_β at 124 GW | 4.27 fs | Pendry 2024 Eq. 3 |
| γ_eff at 124 GW| −1.04 × 10¹⁴ s⁻¹ | Pendry 2024 Eq. 6 |

The `ITOAvalancheCase` module instantiates these values
explicitly and proves the gain-mode conclusion at I_pump = 124
GW/cm² as `tirole_is_gain_mode`.

## 9. Methodology lesson

The most important methodology lesson from the analysis trail
is: **distinguish three layers when reporting a model-vs-data
discrepancy**:

* the theory (here: Bender's algebraic complex-energy
 framework, which is signature-agnostic and untouched by any
 specific experiment);
* the operational identification (here: which physical
 timescale plays the role of the Bender lifetime — three
 candidates above);
* the experimental data (here: which observable is being
 measured, and what conservation law governs it).

A failure at the data-vs-model interface refutes the
identification or the choice of observable, NOT the theory.
The Props in MaterialTimescales make this discipline explicit
in Lean: every claim that "for this system, the Bender Γ is X"
must attach an identification Prop, separable from the
algebraic Bender identity itself.

## 10. References (with DOIs / arXiv)

* Bender, C. M. and Boettcher, S. (1998), *Real spectra in
 non-Hermitian Hamiltonians having `PT` symmetry*,
 Phys. Rev. Lett. **80** (24), 5243.
 DOI: [10.1103/PhysRevLett.80.5243](https://doi.org/10.1103/PhysRevLett.80.5243).

* Bender, C. M., Brody, D. C. and Hook, D. W. (2008), *Quantum
 effects in classical systems having complex energy*,
 J. Phys. A **41** (35), 352003.
 DOI: [10.1088/1751-8113/41/35/352003](https://doi.org/10.1088/1751-8113/41/35/352003).
 arXiv: [0804.4169](https://arxiv.org/abs/0804.4169).

* Pendry, J. B. (2021), *Photon number conservation in time
 dependent systems*, Optics Express **29** (25), 41587.
 arXiv: [2209.11576](https://arxiv.org/abs/2209.11576).

* Tirole, R. et al. (2023), *Double-slit time diffraction at
 optical frequencies*, Nature Physics **19** (7), 999.
 DOI: [10.1038/s41567-023-01993-w](https://doi.org/10.1038/s41567-023-01993-w).

* Galiffi, E. et al. (2024), *Optical coherent perfect
 absorption and amplification in a time-varying medium*,
 arXiv: [2410.16426](https://arxiv.org/abs/2410.16426).

* Pendry, J. B. (2024), *An avalanche model for femtosecond
 optical response*, arXiv: [2407.08391](https://arxiv.org/abs/2407.08391).

## 11. How to read this library

If you have a specific question:

* "What does the algebraic Bender identity actually say?"
 → `BenderIdentity` §A–§F (algebra), §G (decay law),
 §H (complex energy).

* "How does Euclidean modular time relate to Lorentzian
 observables?"
 → `ThermoFieldDynamics.KMS`.

* "When does Pendry's photon-conservation theorem apply?"
 → `PendryPhotonConservation`.

* "Which timescale is the Bender Γ for my experiment?"
 → `MaterialTimescales` §A taxonomy, §B–§C–§F three
 candidate identifications (Props).

* "Is my system in the gain mode or the decay mode?"
 → `MaterialTimescales` §F `IsGainMode` / `IsDecayMode` /
 `IsAtThreshold` iff theorems, given a candidate
 `EffectiveDampingDecomposition` for your system.

* "How does this all play out for ITO at ENZ?"
 → `ITOAvalancheCase` — four concrete pump-intensity regime
 instances with proved regime theorems.

If you want to extend the library to a new experiment, the
recipe is:

1. Build an `EffectiveDampingDecomposition` with your
 `γ_Drude`, `β`, and the derived `γ_eff` (parallel
 `tiroleDecomposition` in `ITOAvalancheCase`).
2. Prove the rate inequality (`γ_Drude < β` or vice versa) by
 `norm_num` or `linarith`.
3. Apply the appropriate iff theorem from
 `MaterialTimescales` §F to derive `IsGainMode` /
 `IsDecayMode` / `IsAtThreshold`.
4. Add a docstring explaining where your rate values came
 from (which measurement, what conditions, what assumptions)
 — exactly as `ITOAvalancheCase` does for the Tirole-Galiffi
 chain.

That's the full library workflow.

## 12. Known gap: non-ITO experimental anchoring

As of this writing, **all empirical anchoring in physlib uses
the same ITO film** (or nominally-identical ITO films across
the Tirole 2022 / Galiffi 2024 / Harwood 2024 chain). The
`EffectiveDampingDecomposition` structure is material-agnostic
— it records only positive real rates — but the FRAMEWORK'S
EXPERIMENTAL BREADTH is currently narrow.

Extending to a non-ITO instance would require a paper that
provides:

* **`γ_Drude`** for the material — typically from linear-
 response ellipsometry at the relevant frequency. In Galiffi
 2024 this is `0.13 fs⁻¹` for ITO at the ENZ wavelength.

* **A pump-induced rise time at a stated pump intensity** —
 to cross-check against the Pendry 2024 avalanche formula
 `β = E·e/√(U_G·m)` (with `E` derived from `I_pump`).

* **The material's band gap `U_G` and effective mass `m`** —
 the Pendry formula's only material-specific inputs beyond
 `γ_Drude`.

Candidate non-ITO materials with reported ENZ behaviour
include AZO (aluminum-doped zinc oxide), CdO (cadmium oxide),
and various transparent conducting oxides; pump-modulated
ENZ measurements on these systems exist but specific
`γ_Drude` ellipsometry + `τ_rise` pump-probe values would
need to be located in the literature to anchor a Lean instance.

This module **does not invent rate values** for non-ITO
materials — that would defeat the purpose of empirical
anchoring. The status is: framework is general,
empirical instances are currently ITO-only. A future
contributor with the relevant rate measurements (or a
dedicated literature scan) can add a non-ITO instance
following the recipe in §11.

## 13. Architectural layering: rate level here, operator level
external

The KMS bridge `ThermoFieldDynamics.KMS.lean` works at the **rate level** —
it has `planckianPeriod β` and `thermalRate λ_th` with the
proved identity `β · λ_th = 1`. It does **not** include the
operator-level **Tomita-Takesaki modular automorphism**
`σ_t`, the modular operator `Δ`, or Tomita's theorem
`(Δ^{it})* = Δ^{−it}`.

That operator-level content is the published mathematical
construction of Tomita 1970 and the Connes-Rovelli 1994
thermal-time hypothesis. A formal Lean development of these
theorems exists in a separate codebase outside physlib's
dependency surface (no import dependency from here). The
relevant material:

* The modular operator `Δ` and the proved unitarity
 `(Δ^{it})* = Δ^{−it}` (Tomita 1970).
* The KMS strip width `Δs_KMS(t) = 1/γ_I(t)` and the
 identification of the strip width with the entropic proper
 time `τ_ent` (Connes-Rovelli 1994 + downstream extensions).
* Further consumers with modular-thermal certificates,
 modular group laws, reduced modular channels,
 Matsubara-AQFT equivalence, relative-entropy/modular
 bridges, discrete-event modular flow, entropic coercivity
 from modular Hamiltonians, and Page-Wootters / Wheeler-
 DeWitt / path-integral modular-flow integrations.

The split is intentional: physlib stays material-agnostic and
rate-level so it can be imported by any downstream theory;
the operator-algebra content lives externally with proper
citation to the published origin. `ThermoFieldDynamics.KMS.lean §F`
provides the **hook** (`IsModularFlow` `Prop` structure) by
which any external operator-algebra construction can connect
its modular flow back to the rate-level KMS bridge in physlib
without taking a build-time dependency on the external code.

**External-origin disclaimer.** Physlib's lakefile depends
only on Mathlib + doc-gen4. All references in this section
to "external codebases" denote separately maintained Lean
developments that physlib does not import. Every cross-
codebase mention is conceptual, citing a published origin
(Takesaki 1970, Connes-Rovelli 1994, …) — never an implicit
dependency.

## 14. Seven routes to `τ_ent` across the stack

`τ_ent` (entropic proper time) is identified or constructed in
*seven* distinct ways across the entropic-time codebase, each
with its own structure hypothesis or proved structural lemma:

| Route | Module | structure / theorem |
|-------|--------|-------------------|
| **Bender lifetime** `τ = ℏ/Γ` | `BenderIdentity` §F | `lifetimeFromRate`, `rate_lifetime_inverse` |
| **KMS thermal time** `β = ℏ/(k_B·T)` | `ThermoFieldDynamics.KMS` §A | `planckianPeriod`, `β·λ_th = 1` |
| **ETH information density** `τ_ent_canon = β_I·I/ℏ` | physlib `RouteConvergence` §E (D'Alessio et al. 2016) | `ETHInformationScale.canonicalTau` |
| **Variational rate functional** `τ_ent(E) = S_eff(E)` | external (no physlib dependency) | published in complex-action/entropic-time literature |
| **Connes-Rovelli thermal Hamiltonian** `H_th = −ln ρ = S_I/ℏ = τ_ent` | published Connes-Rovelli 1994; external Lean (no dependency) | scalar shadow in `RouteConvergence` §N |
| **Pendry avalanche-corrected damping** `γ_eff = γ_Drude − β` | physlib `MaterialTimescales` §F + `ITOAvalancheCase` | five concrete ITO instances |
| **OPS Doppler shear gain** | physlib `QuantumFrictionCase` | subcritical / supercritical instances |
| **Page-Wootters clock-conditional time** `t = clock reading` | published Page-Wootters 1983; scalar representative in physlib `RouteConvergence` §J | `PageWoottersScale.systemPhase` |
| **Lindblad dephasing time** `τ_ent(t) = Γ·t = −log γ(t)` | physlib `Lindblad/` + published Lindblad 1976 / Spohn 1978 | `gklsEntropicRate`, `gklsEntropicRate_nonneg` |

The nine routes share the same exponential structure
`exp(−τ_ent·rate)` at the visibility / decay level (see
`VisibilityDecayFraction` for the algebraic identification at
the rate level). Each structure has an explicit Prop
hypothesis that, when supplied with concrete inputs, gives a
specific numerical `τ_ent` for the system at hand.

## 15. Status of the convergence question

A formal "convergence theorem" — stating that under matching
structure hypotheses, all seven routes yield the same `τ_ent` —
was not a single Lean theorem at the time §15 was originally
authored. Since then, physlib's `RouteConvergence` module
(commits A.1–A.5 on this branch) records five routes' worth
of convergence and `Closure.lean` assembles the unified
statement on Phase-D corpus instances. The piecewise structure-
level identifications listed below remain accurate and are
the ingredients of the assembled theorems:

* Bender ↔ KMS: at Planckian saturation, `λ_th = 1/τ_Gamow`
 (`ThermoFieldDynamics.KMS.IsPlanckianSaturation`).
* Bender ↔ Pendry: `gamma_eff = γ_Drude − β` (`MaterialTimescales`
 `EffectiveDampingDecomposition`); five ITO instances anchor
 this empirically.
* KMS ↔ ETH information density: `β = ℏ/(k_B·T)` and
 `τ_ent_canon = β_I·I/ℏ` agree if `β_I = β` and `I = k_B·T·t/ℏ`
 (structure-level).
* ETH ↔ thermal Hamiltonian: published Connes-Rovelli 1994
 identification `H_th = −ln ρ = S_I/ℏ = τ_ent` (an external
 Lean development records this theorem; no dependency from
 physlib).
* OPS Doppler ↔ Pendry: both use the same
 `EffectiveDampingDecomposition` structure (`MaterialTimescales`
 §F), with `β` taking different physical interpretations
 (avalanche rate for Pendry; Doppler-induced growth for OPS).

* Page-Wootters ↔ Matsubara: a published Page-Wootters /
 Matsubara identity (an external Lean codebase formalises it;
 no dependency from physlib) proves `−phaseS·ℏ = β·ℏ·E_S` at
 the imaginary-time evaluation point and extends to
 `−phaseS·ℏ = S_I` under a single-mode hypothesis.

* Page-Wootters ↔ KMS modular flow: a published Wheeler-DeWitt
 + Matsubara + modular-strip-width identification (external
 Lean codebase, no dependency from physlib) proves
 `path_integral = modular_flow_action` and
 `modular_flow_period = inverse_dissipation_rate`.

* Page-Wootters dissipative extension ↔ Lindblad dephasing: a
 published identification (external Lean codebase, no
 dependency from physlib) proves `|amp|² = exp(−S_I/ℏ)` for
 `S_I ≥ 0`; the standard Lindblad form `γ(t) = exp(−Γ·t)`
 gives `τ_ent(t) = Γ·t`. Under the structure identification
 `S_I = ℏ·Γ·t`, the two exponentials coincide:
 `exp(−S_I/ℏ) = exp(−Γ·t) = γ(t)²`, and the dissipative
 reduction at `S_I = 0` coincides with the Lindblad reduction
 at `Γ = 0` (zero dephasing rate ⇒ unitary evolution).

* Lindblad GKLS rate ↔ QIF entropic rate: physlib's
 `GKLSEntropicRate` defines `gklsEntropicRate L ρ :=
 Σ_j Tr(L_j^† · L_j · ρ).re` and the `gklsImaginaryHamiltonian
 L ℏ := (ℏ/2) · Σ_j L_j^† · L_j` ; the docstring states the
 intended bridge `gklsEntropicRate = entropicRateOfDensity
 (gklsImaginaryHamiltonian L ℏ) ℏ ρ`. That specific bridge
 theorem is named in the file's docstring but not yet proved
 as a Lean statement in the file (it is the natural
 follow-up); what is proved is the rate's non-negativity
 (`gklsEntropicRate_nonneg`).

A unified "convergence" theorem stating that *all nine
routes* give the same `τ_ent` would bundle these piecewise
identifications into a single structure and prove the
transitive closure. That bundling is a follow-up project,
not yet executed.

What *can* be stated with the current code:

* `τ_ent` is a **well-defined object across all seven routes**
 in the sense that each route's structure provides its own
 `τ_ent` value plus a Prop hypothesis identifying it with
 some other quantity.

* The **empirical anchoring** of `τ_ent` for the ENZ / ITO
 experimental class is established through the Pendry route
 with five concrete instances (`ITOAvalancheCase`, sessions
 10-23 of the smoke log).

* The **algebraic convergence** of the visibility-decay
 exponential `exp(−λ_ent·S)` across the Bender, ETH, and
 Pendry routes is established by the algebraic identity
 proved in `VisibilityDecayFraction` plus the cross-references
 in §14 above.

## 16. The main theorem in plain language

Lean checks formal validity, not physical content. Before
adding more framework it is worth writing down, in plain
language, the small main theorem the library actually proves
about `τ_ent`, and assessing what it says.

**Definition.** `τ_ent` in physlib is the *Bender lifetime*,

 `τ_ent := ℏ / (2 · Ṡ_I)`,

where `ℏ` is Planck's constant and `Ṡ_I` is the rate of
imaginary-action accumulation. This is `lifetimeFromRate` in
`BenderIdentity` §A.

**Assumptions.**

 A. `ℏ > 0` (Planck's constant is positive).
 B. `Ṡ_I > 0` (entropy-production rate is positive).
 C. The state `ψ` has definite complex energy
 `E = E_R − i · ℏ · Ṡ_I / 2` (a single Gamow eigenstate).

**Conclusion — exactly what the proved theorems give.**

 1. **Positivity**: `τ_ent > 0`.
 Lean: `BenderIdentity.lifetime_pos`.

 2. **Inverse relation**: `τ_ent · Γ = ℏ` where `Γ = 2 · Ṡ_I`
 is the resonance width.
 Lean: `BenderIdentity.lifetime_mul_width`.

 3. **Exponential decay law**: `|ψ(t)|² / |ψ(0)|² = exp(−t/τ_ent)`,
 strictly monotone-decreasing in `t`.
 Lean: `BenderIdentity.benderDecayFraction_strictAnti`.

 4. **One-over-e time**: at `t = τ_ent`, the squared modulus
 has dropped to `exp(−1) ≈ 0.368`.
 Lean: `BenderIdentity.qifLifetime_decayFraction_eq_inv_e`.

**Does this say "time is quantized"?**

No. The four conclusions are properties of the algebraic
structure of complex energies in non-Hermitian quantum
mechanics. Each conclusion is consistent with `τ_ent` being
any positive real number.

The library contains **no theorem** stating that

* `τ_ent` takes values in a discrete set, or
* a time observable has a discrete spectrum, or
* any physical process has a minimum time-step.

The phrase "time is quantized" is **not** what the proved
theorems show.

**What the conclusions actually say (described modestly).**

The Bender lifetime `τ_ent` is a positive real number with
units of time, satisfying:

* the standard inverse relation with the resonance width
 (the Γ-τ duality `Γ τ = ℏ`);
* strictly monotone exponential decay of the squared modulus;
* the standard `1/e`-time characterisation of the operational
 notion of "lifetime".

This is the exponential-decay structure of an unstable
resonance in non-Hermitian quantum mechanics. It is a valid
and self-contained result, and naming it that way is the
description.

**Structural content beyond the scalar `τ_ent` algebra.**

The four conclusions (1)–(4) are at the scalar level
(`τ_ent : ℝ`). At the **operator level**, physlib records
substantially more: the Nagao-Nielsen complex-Hamiltonian
decomposition

 `H_C := H_R − i · H_I`,
 non-Hermitian Schrödinger: `iℏ ∂_t ψ = H_C ψ`,
 norm-squared decay: `d‖ψ‖²/dt = −(2/ℏ)·⟨H_I⟩`

is in `Physlib.QuantumMechanics.FiniteTarget.\
NagaoNielsenSchrodinger`, with the following proved theorems:

 5. **Reduction to standard QM at `H_I = 0`**: the
 non-Hermitian Schrödinger equation collapses to the
 standard Hermitian one when `H_I = 0`.
 Lean: `nonHermitian_schrodinger_at_H_I_zero`,
 `complexHamiltonian_at_H_I_zero`.

 6. **Norm-decay sign**: under `H_I ≥ 0` and `ℏ > 0`, the
 norm-squared decay rate is non-positive (norm
 non-increasing — contractive evolution).
 Lean: `norm_decay_rate_nonpos`.

 7. **TISE via Mazur-Ulam chain**: under `H_I.IsPositive`,
 zero local entropy-production rate
 `H_I.reApplyInnerSelf ψ = 0`, and an `H_R`-eigenvector
 hypothesis `H_R ψ = E·ψ`, the full complex Hamiltonian
 satisfies `H_C ψ = E·ψ` (time-independent Schrödinger
 equation for the full complex generator).
 Lean: `tise_via_mazur_ulam_chain_from_zero_entropy_rate`.

 8. **Entropic proper time vanishes ⇒ unitary evolution**:
 when the entropic proper time
 `(entropicProperTime ρ ρ).toReal = 0` (Frozen-LRF, `ρ = σ`),
 `H_I = 0` and the evolution reduces to standard unitary
 QM.
 Lean: `entropic_proper_time_self_implies_unitary`.

 9. **Frame-change invariance of the entropic rate**: under
 a Quantum Inertial Frame change, the entropic rate of a
 state is invariant.
 Lean: `entropicRate_invariant` in
 `QuantumInertialFrame.lean`.

 10. **Page-Wootters Schrödinger reduction**: when
 `τ_ent = 0` (equivalently `S_I = 0`, `Z = 1`), the full
 Page-Wootters / Matsubara / modular-flow tower collapses
 coherently to the bare Schrödinger phase
 `phaseS = −E_S·t/ℏ` of an `H_S` eigenstate, the
 path-integral imaginary action vanishes, and the modular
 strip width at the evaluation point is zero.
 External Lean development (no physlib dependency):
 a `schrodinger_reduction_under_no_clock_evolution`
 theorem in the published Page-Wootters / Wheeler-DeWitt
 literature (Page-Wootters 1983; Giovannetti et al. 2015).

 11. **Lindblad reduction at zero dephasing rate**: when
 `Γ = 0` (no decoherence), the dephasing factor
 `γ(t) = exp(−Γ·t)` is identically `1`, the induced
 entropic time `τ_ent_Lindblad(t) = −log γ(t) = Γ·t`
 vanishes, and the Lindblad evolution reduces to the
 unitary Schrödinger evolution. The arrow-of-time
 content of `τ_ent_Lindblad` accumulates only under
 strictly positive `Γ`.
 External Lean development (no physlib dependency):
 a `tauEnt_lindblad_arrow_requires_positive_Γ` theorem
 composes the published Lindblad 1976 / Spohn 1978
 content.

 Under the structure identification `S_I = ℏ·Γ·t`,
 the Page-Wootters reduction (10) and the Lindblad reduction
 (11) are the same statement at different parametrisations:
 `τ_ent = 0 ⇔ S_I = 0 ⇔ Γ·t = 0 ⇔ Γ = 0` (at fixed nonzero
 `t`). Both collapse to the bare Schrödinger evolution.

 The Page-Wootters Schrödinger phase identity at the
 eigenvalue level, `phaseS(t) = −E_S·t/ℏ`, is **the same
 algebraic identity** as the `BenderIdentity` §I
 `benderPhase E_R t ℏ := −(E_R·t)/ℏ` under the identification
 `E_R = E_S`. Page-Wootters derives this from the
 Wheeler-DeWitt constraint plus conditional-state extraction
 `|ψ_S(t)⟩ := ⟨t|_C|Ψ⟩` (PW3); §I derives it from the polar
 decomposition of the Bender complex energy `E = E_R − iℏṠ_I/2`.
 Same scalar identity, two independent derivations.

**What this adds to the claim about `τ_ent`.**

Theorems (5)–(9) say something the scalar conclusions (1)–(4)
do not: the framework `H_C = H_R − i·H_I` is not just one
choice among many — it is the structural form that any
contractive non-Hermitian evolution takes (Mazur-Ulam +
Cueto-Avellaneda-Peralta 2018; the decomposition itself is a
cited theorem from the operator-algebra literature, and its
finite-dimensional consequences are proved here). Standard
unitary QM is the reduction at `H_I = 0`, not a separate
formalism.

This is a **structural preference within the class of
contractive evolutions**: alternative non-Hermitian models
that do not decompose as `H_R − i·H_I` with `H_R` Hermitian and
`H_I` positive Hermitian are not different theories at this
class — they simply do not exist within the contractive class,
by Mazur-Ulam.

**Empirical content beyond the algebra.**

Physlib does *not* prove that `τ_ent` matches any specific
experimental observable from first principles. That matching
is supplied by **structure hypotheses** (per-experiment `Prop`s)
in `MaterialTimescales` §B/§C/§F and realised in
`ITOAvalancheCase` (five ITO instances anchored to Galiffi 2024
ellipsometry + Pendry 2024 avalanche formula).

The proof structure in each ITO instance is:

 given the rate inputs `γ_Drude` (from Galiffi) and `β` (from
 Pendry's formula at a stated pump intensity), the regime
 classification `IsGainMode` / `IsDecayMode` / `IsAtThreshold`
 follows from the abstract iff-theorems in
 `MaterialTimescales` §F.

So the Lean instances **classify** the regime correctly given
the rate inputs; they do **not** derive the rate inputs from
first principles. The empirical consistency between the
framework's regime predictions and Tirole / Galiffi / Harwood
observations is documented in the smoke log (sessions 10, 13,
23), not as Lean theorems. Consistency at the smoke-log level
is not derivation.

**summary (corrected).**

What physlib proves at the **scalar level** (1)–(4): the
algebraic structure of unstable-state decay in non-Hermitian
QM — positivity, the `Γ τ = ℏ` inverse-rate relation, monotone
exponential decay, `1/e`-time characterisation.

What physlib proves at the **operator level** (5)–(9): the
Nagao-Nielsen `H_C = H_R − i·H_I` decomposition reduces to
standard unitary QM at `H_I = 0`; norm-decay non-positivity
under positive `H_I`; TISE recovery via the Mazur-Ulam chain;
entropic-proper-time vanishing implies unitary evolution;
frame-change invariance of the entropic rate.

What physlib **does not** prove: time quantization, a unique
`τ_ent` value derived from first principles for a specific
material, or that any specific experimental observable
(Tirole rise time, Galiffi visibility, Harwood diffraction
pattern) is uniquely a consequence of the framework rather
than a phenomenological match.

The framework's **structural preference** within the
contractive non-Hermitian class is established by the
Mazur-Ulam citation chain plus the proved reduction theorems
(5)–(11). Outside that class — e.g., expanding evolutions or
non-contractive dynamics — the Mazur-Ulam decomposition does
not apply and the framework's preferred status is not claimed.

**Page-Wootters operational definition of `τ_ent`.**

The published Page-Wootters mechanism (Page-Wootters 1983;
Giovannetti-Lloyd-Maccone 2015; an external Lean development
formalises the quantum-clock structure and the WDW
path-integral / modular-flow spine, with no physlib import
dependency) provides an **independent operational route** to
`τ_ent`: it emerges from
the clock-reading `t` of a clock subsystem entangled with the
rest of the universe under the Wheeler-DeWitt global
constraint `(H_C + H_S)|Ψ⟩ = 0`. Under this mechanism, the
state of the system conditional on the clock reading is

 `|ψ_S(t)⟩ := ⟨t|_C|Ψ⟩`,

and the system evolves by the Schrödinger equation
`iℏ ∂_t|ψ_S(t)⟩ = H_S|ψ_S(t)⟩` derived from PW2 + PW3.

The entropic-proper-time identification at the imaginary-time
evaluation point `t = β·ℏ` is the proved theorem
`pageWootters_thermal_eval_identity`:

 `−phaseS · ℏ = β · ℏ · E_S`.

Combined with the Matsubara/Luttinger-Ward identification
`S_I = ℏ·β·Ω` and the single-mode hypothesis `E_S = Ω`, this
gives `−phaseS·ℏ = S_I`, which is one of the central
imaginary-time-action identifications.

What PW adds beyond the Bender + KMS routes:
* a **mechanistic** statement of where the clock time comes
 from (clock-system entanglement under WDW), not just a
 consistency identity;
* a **single proved reduction theorem**
 (`schrodinger_reduction_under_no_clock_evolution`)
 showing that the entire PW + Matsubara + modular-flow tower
 collapses coherently to standard Schrödinger at `τ_ent = 0`,
 complementing the (5)–(9) reductions above.

What PW does **not** add:
* a derivation of a specific numerical `τ_ent` for a specific
 experimental system (same caveat as the other routes);
* an operator-level construction of the clock projector
 `⟨t|_C` (the PW structure is magnitude-level only, with the
 clock projector left abstract — same scope caveat as
 `IsModularFlow` and `IsPendryEvolution`).
-/

namespace Physlib.Optics.EntropicTimeOverview

/-- Module marker.  This module is documentation only; the
declaration is here so `lake build` has something to verify.
The substantive content is the module-level docstring above. -/
def _overview : Unit := ()

end Physlib.Optics.EntropicTimeOverview

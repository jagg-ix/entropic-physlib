# De Broglie's 1924 thesis under the information-dimension lens

**Source**: *On the Theory of Quanta* — Louis de Broglie, doctoral thesis (Ann. de Phys.
1925), A. F. Kracklauer translation (2004), 81 pp.  **Evaluated against**: the
repository's formalized apparatus as of 2026-08-30 — the Compton-clock / frequency
trinity, the temperature and frequency groupoids, the path-integral nat ledger
(`PathIntegralBitProcessing`), the holographic–Landauer bridge, and the Planck
calibration of the Gaussian–Fisher coupling.  46 modules in the tree carry de Broglie's
name; this document says precisely which of the thesis's claims survive as kernel-checked
theorems, which are re-graded by the information dimension, and what the thesis was
missing that the `[I]` machinery supplies.

## 1. What survives as exact theorems (kernel-checked)

| Thesis claim | Where | Formal survivor |
|---|---|---|
| The internal clock `hν₀ = m₀c²` (Eq. 1.1.5, "the basis of our theory") | Ch. 1.1 | `FrequencyTrinity.comptonFrequency = mc²/ℏ`; tick count `fujiwaraComptonTickCount = mc²τ/(2πℏ)` — action over `h`, exactly de Broglie's clock counting |
| The two frequencies: dilated clock `ν₁ = ν₀/γ` vs. energy frequency `ν = γν₀` (Eqs. 1.1.6–7) and the **theorem of phase harmony** reconciling them | Ch. 1.1 | `deBroglie_eq_gamma_compton : ω_dB(γmc²) = γ·ω_C` — the boost law, the algebraic core of phase harmony, proven; the trinity module's Compton/de Broglie/Zitterbewegung structure is the thesis's Ch. 1 made exact |
| Bohr–Sommerfeld stability = wave resonance (integer phase per orbit) | Ch. 3 | the tick count makes "resonance" *countable*: an orbit is stationary iff the clock advances an integer number of ticks — the repository's stationary/isometric split (below) explains **why** such states are stable |
| Statistical mechanics by cell counting, `S = k log P` | Ch. 7.1 | the ancestor of `comptonCellBits` (`Nλ² = A`) and `entropicNatCount = S/k_B`; his phase-space cells are the direct forebears of the Compton–Fisher cell |
| The de Broglie carriers as *hub* of the modern welds | Chs. 1, 7 | `deBroglieTemperature`/`deBroglieFrequency` are the general-`E` hub of the temperature octagon and frequency pentagon: `hawking_eq_deBroglieTemperature_iff`, `deBroglie_eq_gibbonsHawkingSI_iff`, `gravity_eq_deBroglieTemperature_iff`, the Compton instances — every one a closed groupoid edge |

The thesis's two central mathematical claims — the clock postulate and phase harmony —
survive *verbatim* as exact identities.  Nothing in it is contradicted by the formal
apparatus.

## 2. What the information dimension re-grades

The sharpest thing the `[I]` machinery says about this thesis is **which half of physics
it is**:

* **De Broglie's mechanics is the zero-nat sector.**  `Physlib.Meta.PathIntegralBitGate`
  §3 certifies the Fujiwara/Compton tick count *information-neutral*: it is `k_B`-free and
  stays dimensionless under the Brillouin price.  The thesis's periodic phenomenon,
  phase waves, and Maupertuis–Fermat unification (Ch. 2) are exactly the *reversible*
  half of the path integral — and by the Feynman–Kac Landauer dichotomy
  (`dampedHeat_isometric ⟺ landauerCount = 0`), reversible means **zero bits erased**.
  Clock ticks are not nats.  De Broglie's electron computes for free.
* **This re-grading explains his Chapter 3.**  Why don't Bohr orbits radiate?  In the
  formal split: a stationary (resonant, integer-tick) state is isometric, and isometric
  evolution has Landauer count zero — no entropy production, no decoherence, nothing to
  pay.  The stability de Broglie derived from resonance is, in the modern ledger,
  *informational* stability: the orbit processes no nats, so there is no dissipation
  channel.  His resonance condition and the repository's dichotomy are two descriptions
  of the same zero.
* **His Chapter 7 holds the other half — unpriced.**  `S = k log P` with cell counting is
  the nat ledger *avant la lettre*: under the repository's **default** binder typing
  (`k_B : E Θ⁻¹ I⁻¹`, the Brillouin price — a convention Brillouin introduced three
  decades after this thesis), his `S/k` is exactly the `[I]`-dimensional
  `entropicNatCount`.  The thesis contains both halves of the modern picture — the
  kinematic clock (Ch. 1) and the counting statistics (Ch. 7) — but has no bridge
  between them, because the bridge *is* the information charge of `k_B`, which did not
  exist in 1924.

## 3. What the thesis was missing, now supplied

The modern chain builds gravity out of de Broglie's own objects plus exactly two
ingredients he lacked:

1. **The price**: one nat per cell (`k_B`'s `I⁻¹`; the Brillouin convention the binder
   table now carries by default).  With it, his Ch. 7 cells become bits and his `S/k`
   becomes `[I]`.
2. **The calibration**: *which* cell.  The Gaussian–Fisher chain takes the Compton cell
   `λ_C²` of his Ch. 1 clock, prices it at one bit, and the Planck calibration
   (`existsUnique_calibration`) proves the gravitational cell is uniquely the Planck
   area — `G = ħcσ₀⁴` is equivalent to one bit per `ℓ_P²`, the width is pinned at
   `inferenceMass = m_P`, and per-system widths are refuted by coupling injectivity.

With those two additions, his clock's cells tile the holographic screen
(`tiledBits_eq_holographicBits`), the tiled response *is* Newton's law
(`tiledScreen_gravitationalResponse`), the horizon count is Bekenstein's, and the screen
temperature is Hawking's (`GaussianFisherHorizonConsistency`).  In that precise sense the
1924 thesis supplies the kinematic scaffolding of the entire information-dimension
program: **de Broglie's clock, priced and calibrated, is the gravitational bit.**

## 4. Verdict

* **Accuracy**: the thesis's formalizable core (clock postulate, phase harmony, boost
  law, resonance quantization, cell statistics) survives complete and exact; 46 modules
  carry its objects, and its temperature/frequency carriers sit at the hub of every
  closed groupoid in the repository.
* **Epistemic placement**: it is a theory of the reversible, information-neutral half of
  quantum dynamics — certified as such by the tick-neutrality gate, not merely asserted.
  Its own Ch. 7 contains the seed of the other half, unpriced.
* **The one sentence**: de Broglie postulated the clock and counted the cells; Brillouin
  priced them; Verlinde moved them; the Fisher calibration pinned them at the Planck
  area — and each step of that sentence is now a kernel-checked theorem, with the
  thesis's steps the only ones old enough to have been conjecture.

## 5. Additional leverage extracted (2026-08-30, second pass)

A follow-up inspection found two quantitative results of the thesis with **no formal
counterpart** in the library; both are now theorems in
`ComptonClock/DeBroglieDispersionComptonAnchor.lean`:

* **The dispersion theorems (Ch. 1.2).**  De Broglie's "ultimately very useful" theorem —
  the group velocity `dω/dk` of the phase wave equals the particle velocity `βc` — is
  proved from actual `HasDerivAt` derivatives of `ω(β) = ω₀/√(1−β²)` and
  `k(β) = ω₀β/(c√(1−β²))` (`groupVelocity_eq_particleVelocity`), with the phase velocity
  `c/β` and the duality `V·U = c²` alongside, and the Compton clock's mass-additivity as
  the simplest exact form of his Ch. 4 two-clock problem.
* **The Compton anchor (Ch. 6.3, Eq. 6.3.4).**  The Compton–Debye shift
  `Δλ = (2πℏ/mc)(1−cos θ)`, in de Broglie's own clock-normalized form
  `λ₀·2α sin²(θ/2)` with `α = ν₀/ν_C`.  The leverage is that the right-angle shift *is*
  the non-reduced Compton wavelength (`comptonShift_right_angle`), so **the holographic
  bit cell is an experimentally measured length**: the cell area is `(Δλ(π/2)/2π)²`
  (`cellArea_eq_shift_sq`) and the gravitational-response bit density is
  `(2π/Δλ(π/2))²` at the inference mass (`comptonBitDensity_eq_inv_shift_sq`).  Compton's
  1923 X-ray experiment thereby anchors one end of the holographic Newton chain, the
  measured `G` anchors the other, and the Planck calibration is the unique bridge —
  giving the `G = ħcσ₀⁴` program a second, independent empirical interface.

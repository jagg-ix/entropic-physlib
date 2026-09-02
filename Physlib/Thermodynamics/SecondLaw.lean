/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Thermodynamics.SecondLaw.SergiOperatorTimeFree

/-!
# Second law and the entropic-time arrow as a derived side effect

This module formalises the thesis that **entropic time is not a cause but
a side effect of entropy increase**. It corresponds to
`AbstractWitnessContracts.ThermodynamicsLean` (Clausius/Lieb–Yngvason second law)
and `EntropyIncreaseAlongWorldlineBridge` (Paper 2 §5, "entropic-time arrow along
worldlines").

## The thesis, made precise

Along a worldline the **imaginary action / entropy production** `S_I(t)` is the
primary, load-bearing quantity; the **entropic proper time** is *defined* from it,

  `τ_ent(t) := S_I(t)/ℏ`.

The arrow of time `dτ_ent ≥ 0` is therefore a **consequence** of entropy increase
`S_I(t₁) ≤ S_I(t₂)`, never an independent input. We make the asymmetry explicit:

* every theorem about `τ_ent` is *derived from* a property of `S_I`
  (`tau_ent_monotone`, `tau_ent_nonneg_along_worldline`, …);
* `time_order_iff_entropy_order` proves the time order is **exactly** the entropy
  order — `τ_ent(t₁) ≤ τ_ent(t₂) ↔ S_I(t₁) ≤ S_I(t₂)` — so `τ_ent` carries no
  ordering information beyond `S_I`: it is a strictly monotone *readout* of
  accumulated entropy, i.e. a side effect.

## Second law

`clausiusEntropy k_B T T₀ = k_B·log(T/T₀)` is monotone increasing in `T`
(`clausiusEntropy_monotone`) — the canonical second-law statement on
Lieb–Yngvason states. `ofClausiusProfile` shows a monotone temperature history
**instantiates** an entropic-time arrow: the thermodynamic second law is one
source of the `S_I` monotonicity that the time arrow rides on.

## Link to physlib's relative-entropy time

`ofStateWorldline` builds the arrow carrier from a genuine state trajectory
`ρ : ℝ → MState d` with `S_I(t) = ℏ·D(ρ(t)‖ρ(0))`, so that
`τ_ent(t) = (entropicProperTime (ρ t) (ρ 0)).toReal`
(`ofStateWorldline_tau_ent_eq_relativeEntropy`). The entropic clock is literally
the accumulated quantum relative entropy — the side effect of state divergence.


## References

- **Lindblad 1976** — *On the generators of quantum dynamical semigroups*
- **Spohn 1978** — *Entropy production for quantum dynamical semigroups*
- **Araki 1976** — *Relative Hamiltonian for faithful normal states of a von Neumann algebra*
- **Clausius 1865** — *Über verschiedene für die Anwendung bequeme Formen der Hauptgleichungen*
- **Zhang 2008** — *Topology and Information Conservation in the Second Law of Thermodynamics*
- **Sergi & Giaquinta 2016** — *Linear Quantum Entropy and Non-Hermitian Hamiltonians*, Entropy 18(12), 451 (entropic-physlib-inventory/entropy-v18-i12_20260602.bib) — primary source for the Sergi spine (Phase D / D₂ / D₃ / E / F).
- **Sergi & Ferrario 2001** — *Non-Hamiltonian Equations of Motion with a Conserved Energy*, Phys. Rev. E 64, 056125 (entropic-physlib-inventory/entropy-v18-i12_20260602.bib) — classical analogue: antisymmetric B + κ-compressibility arrow (`NonHamiltonianFlow`, `NonHamiltonianMeasureBridge`).
-/

# Physlib — the entropic-dynamics spine (Quantum Mechanics → General Relativity)

A clean, self-contained Lean 4 / Mathlib formalization of the **entropic-dynamics reconstruction of physics**:
how the mathematical formalism of quantum mechanics — and its bridge to general relativity — emerges from
probability theory and information geometry.

Unlike the full research library, this repository depends **only on Mathlib** (no heavyweight particle-physics
infrastructure) and is authored as a coherent narrative spine:

1. **Information geometry** — the statistical simplex and the Fisher–Rao metric.
2. **Probability metrics** — the Cramér and 1-Wasserstein distances as `Lᵖ` distances between CDFs.
3. **Entropic dynamics** — the Fokker–Planck probability flow, the Wasserstein gradient flow of the free energy,
   free energy as relative entropy (the `H`-theorem), and the Gibbs equilibrium.
4. **Hamilton–Killing → quantum mechanics** — the Kähler geometry of the statistical cotangent bundle
   (symplectic + metric + complex structure), the phase-shift gauge that makes states rays, the Born rule, and the
   Schrödinger equation as a Hamilton–Killing flow.
5. **Quantum mechanics → general relativity** — the complex-Einstein / entropic-gravity link and the
   clock → Newton → general-relativity chain.

## Build

```bash
lake exe cache get   # fetch prebuilt Mathlib
lake build
```

Toolchain: `leanprover/lean4:v4.30.0`, Mathlib `v4.30.0`. No new axioms; `sorry`-free.

## License

Apache 2.0 — see [LICENSE](LICENSE).

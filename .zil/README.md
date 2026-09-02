# Physlib ZIL formalization targets

This directory contains local orchestration metadata. It does not add axioms,
definitions, or proofs to Physlib, and ZIL status is not theorem truth.

## Entropic-spine accountability

The principal integration is `Physlib.Meta.EntropicSpineZil`, together with its
imported `Physlib.Meta.MultiNormSection4PaperZil` companion. They are optional
development/CI modules: production roots do not need to import them, and they
create no theorem aliases or scientific definitions. Together they classify
and contract sixty-three central layers:

| Layer | ZIL level | Kernel witness |
| --- | --- | --- |
| probability metric | `structural` | `wasserstein1Distance_triangle` |
| free energy / relative entropy | `toy_model` | `freeEnergy_ge_gibbs` |
| wave-function reconstruction | `algebraic` | `edWaveFunction_modulus_sq` |
| irreversible lifetime | `bridge_theorem` | `qifLifetime_decayFraction_eq_inv_e` |
| frozen recovery | `bridge_theorem` | `frozen_limit_recovers_standard_physics` |
| GR/Newton convergence | `bridge_theorem` | `entropicNewtonConstant_converges` |
| holographic G / clocks / contours / EFE | `bridge_theorem` | `holographicNewton_comptonNagaoLeviCivita_staticPoissonField_chain` |
| damped heat / Stokes resolvent | `bridge_theorem` | `stokesModeLaplaceResolvent_one_eq_euclideanPropagator` |
| finite Fourier Stokes energy | `bridge_theorem` | `dampedStokesEvolution_kineticEnergy_hasDerivAt` |
| Fourier Sobolev dissipation cascade | `bridge_theorem` | `dampedStokesEvolution_sobolevDissipationCascade` |
| integrated Fourier dissipation cascade | `bridge_theorem` | `dampedStokesEvolution_integratedSobolevDissipationCascade` |
| discrete/continuous Fourier budget bridge | `bridge_theorem` | `dampedStokesEvolution_discreteBkm_converges_to_certifiedBudget` |
| fixed-resolution Fourier budget certificate | `bridge_theorem` | `dampedStokesEvolution_discreteBkm_le_certifiedBudget` |
| tolerance-driven Fourier resolution selection | `bridge_theorem` | `dampedStokesEvolution_exists_resolution_for_bkm_tolerance` |
| finite Schrödinger initial-data recovery | `bridge_theorem` | `finiteSchrodinger_initialRecovery_and_sampledEnergy` |
| Euclidean `L²` free Schrödinger evolution | `bridge_theorem` | `euclideanL2_freeSchrodinger_unitaryStronglyContinuous` |
| Schrödinger paraboloid affine self-similarity | `structural` | `schrodingerParaboloid_affineSelfSimilarity` |
| Schrödinger parabolic phase rescaling | `structural` | `schrodingerPhase_parabolicRescaling_chain` |
| Euclidean Sobolev hierarchy / rough frequency localization | `bridge_theorem` | `euclideanSobolev_hierarchy_freeEvolution_annularLocalization` |
| finite Euclidean Littlewood--Paley orthogonality | `bridge_theorem` | `finiteLittlewoodPaley_orthogonality_bessel` |
| standard-matrix multi-norm geometry | `structural` | `standardMultiNorm_dilationGauge_geometry` |
| multi-norm dominance / marked blocks | `structural` | `strictDominance_markedBlock_structure` |
| multi-norm marked partitions / cones | `structural` | `strictDominance_induces_unique_markedCone` |
| explicit marked-cone coordinates / `τ_S` | `structural` | `markedCone_explicitCoordinate_characterization` |
| minimal dotted set `D(t)` | `structural` | `minimalMarkedPartition_dottedSet_characterization` |
| nonnegative cone coverage / `Γ(D)` partition | `structural` | `nonnegativePoint_markedCone_and_uniqueDottedRegion` |
| exact Proposition 3.5 characterization of `Γ(D)` | `structural` | `dottedRegion_eq_markedConeUnion_inter_strictDottedLocus` |
| maximal lattice scales / finite dyadic tubes | `structural` | `maximalDottedScale_finiteTube_geometry` |
| wall-robust maximal floor profile | `structural` | `isMaximalDottedScale_iff_maximalFloorProfile` |
| unique maximal apices / tube coverage / disjoint interiors | `structural` | `uniqueMaximalApex_coverage_disjointInteriors` |
| maximal-apex proximity / intersecting-tube bound | `structural` | `maximalScale_proximity_and_intersectingTube_bound` |
| principal-cone density / meet proximity (Lemma 3.8(ii--iii)) | `structural` | `principalCone_density_and_maximalMeet_proximity` |
| constructed maximal-tube coloring / local overlap | `structural` | `constructedTubeColoring_and_finiteLocalOverlap` |
| exact frequency blocks / dyadic coordinate shells | `structural` | `frequencyBlock_eq_coordinateDyadicShell` |
| frequency-block gauge comparison | `structural` | `frequencyBlock_blockGauge_comparison` |
| smooth cutoffs subordinate to exact blocks | `structural` | `smoothBlockCutoff_subordinate_frequencyBlock` |
| coloring of padded smooth supports | `structural` | `smoothTubeColor_fiber_pairwiseDisjoint` |
| finite pointwise smooth square bound | `structural` | `finiteSmoothMultiplierSquareBound` |
| global low/high frequency coverage | `structural` | `fullFrequencyCover_and_cutoff_one` |
| finite normalized smooth partition | `structural` | `finiteNormalizedPartition_of_coversAt` |
| finite reproducing and square identities | `structural` | `finiteMultiNorm_reproducing_square_support` |
| global neighborhood local finiteness | `structural` | `globalSmoothCover_locallyFinite` |
| native global smooth partition of unity | `structural` | `globalSmoothPartitionOfUnity_spec` |
| global pointwise-finite reproducing identities | `structural` | `globalMultiNorm_reproducing_square_finiteSupport` |
| complex multi-norm amplitude / Born resolution | `structural` | `globalMultiNorm_complexReproducing_bornResolution` |
| multi-norm Schrödinger localization | `bridge_theorem` | `multiNorm_schrodingerLocalization_bridge` |
| multi-norm Schrödinger decoherence | `bridge_theorem` | `multiNorm_schrodingerDecoherence_bridge` |
| finite-overlap Euclidean Littlewood--Paley energy | `bridge_theorem` | `finiteDyadicOverlapLittlewoodPaley_constructedColoring_bessel` |
| Section 4 dyadic Schwartz kernels / cancellation | `structural` | `dyadicSchwartzKernel_cancellation_telescope` |
| Section 4 tempered-distribution Calderón identity | `bridge_theorem` | `dyadicDetailDistribution_tendsto_delta` |
| Section 4 physical convolution / multi-norm multiplier bridge | `bridge_theorem` | `physicalCalderon_reconstruction_multiNormMultiplier_bridge` |
| Lemma 4.1 multi-index moment/derivative interface | `structural` | `arbitraryMultiIndex_moment_derivative_decomposition` |
| Lemma 4.2 certified dual families | `bridge_theorem` | `dualCalderon_arbitraryCancellation_support_partial_full` |
| Proposition 4.3 full-index tensor partial identities | `bridge_theorem` | `fullMultiIndex_tensorProduct_calderon_family` |
| Lemma 4.2 Rychkov formulas (4.2)--(4.3) | `bridge_theorem` | `rychkov_partial_kernel_identity` |
| Lemma 4.2 Rychkov approximation Fourier support | `structural` | `fourier_rychkovDualApproximation_support` |
| Lemma 4.2 Rychkov detail Fourier support | `structural` | `fourier_rychkovDualDetail_support` |
| Lemma 4.2 final approximation spatial formula | `structural` | `dualApproximationConvolution_eq_spatialPolynomial` |
| Lemma 4.2 tilded detail spatial formula | `structural` | `rychkovDualDetail_succ_eq_spatialPolynomial` |
| Lemma 4.2 constructed compact spatial support | `bridge_theorem` | `rychkov_constructed_spatial_compactSupport` |
| Lemma 4.2 approximation-to-full-limit bridge | `bridge_theorem` | `tendsto_rychkovDualCalderon_of_approximation` |
| Lemma 4.2 constructed final approximation limit | `bridge_theorem` | `tendsto_rychkovDualApproximation_delta` |
| Lemma 4.2 unconditional full detail-series limit | `bridge_theorem` | `tendsto_rychkovDualCalderon_delta` |
| Lemma 4.2 arbitrary cancellation and uniform spatial dilate | `bridge_theorem` | `constructedRychkovDual_cancellation_uniformSpatialSupport` |
| Lemma 4.2 unscaled relative normalization and dyadic scaling | `bridge_theorem` | `constructedRychkovDual_normalization_scaling` |
| Proposition 4.3 paper-tube index partition | `structural` | `existsUnique_paperTubeIndex` |
| Proposition 4.3 tempered-distribution regrouping | `bridge_theorem` | `hasSum_paperGroupedDualDetailDistribution_delta` |
| aggregate spine | `bridge_theorem` | all preceding witnesses plus the Schwarzschild chain |

Build and run the complete local contract graph with:

```bash
lake build Physlib.Meta.EntropicSpineZil
```

The module ends in `#zil_formalization_lint_all`; therefore the build fails if
any `satisfied` contract loses a required declaration, a theorem statement no
longer mentions its promised objects, or the strongest classified witness falls
below the advertised level.

Export the complete accountability graph without an external service:

```bash
lake exe zil-scan \
  Physlib.Meta.EntropicSpineZil \
  /tmp/entropic-spine.zilevents.json \
  --no-cache --force
```

The batch contains `formalization_contracts`, `theorem_intents`, and
`declaration_attachments` for the imported kernel witnesses. Important
prohibitions are data, not merely prose: no time-quantization claim, no
promotion of pointwise Gibbs algebra to an integrated empirical H-theorem, no
measurement-derived `G`, and no dynamical entanglement-to-horizon dilation.
The finite Schrödinger contract also prevents the finite pure-point recovery
theorem from being presented as the Du--Zhang Euclidean almost-everywhere
Carleson theorem or as a Sobolev/maximal-estimate result.
The Euclidean upgrade uses Mathlib's Plancherel isometry to construct the
actual `L²(ℝⁿ)` Fourier multiplier, bundle each time slice as a complex-linear
isometric automorphism, and prove strong `L²` recovery. Its contract records
that this still does not imply pointwise or almost-everywhere convergence.
The next two layers implement the paper's parabolic-rescaling mechanism: the
explicit ambient affine shear/dilation is bijective on the frequency
paraboloid, and the real Schrödinger phase and complex oscillatory kernel obey
the exact centre-phase factorization under the dual space--time rescaling.
These are geometric and algebraic identities; the full rescaled propagator
formula still requires Fourier dilation, Jacobian, and support-transport
lemmas.
The next layer implements the Bessel-potential definition of `H^s(ℝⁿ)`,
proves `H⁰ = L²` at the norm level and the monotone Sobolev hierarchy, and
constructs the paper's rough annular Fourier projection as an idempotent
contraction commuting with free evolution. It does not claim the dyadic
Littlewood--Paley square-function equivalence or a Schrödinger maximal bound.
The finite Littlewood--Paley layer then reuses those projections: pairwise
disjoint rough annuli give orthogonal physical-space components, an exact
finite Pythagorean identity, the sharp `L²` Bessel bound, and covariance under
free Schrödinger evolution. The cited multi-norm paper motivates the spectral
support geometry, but the contract explicitly withholds its smooth
finite-overlap theory, `L¹` square-function equivalence, local `h¹_E` space,
Calderón reproducing formula, and atomic characterization.
The next twenty-one layers formalize more of that paper's reusable substrate. The
standard-matrix module defines the physical and frequency anisotropic
dilations on arbitrary normed coordinate blocks, proves their multiplicative
laws, proves exact degree-one homogeneity of the corresponding gauges, and
proves that all those gauges share the same unit ball. The dominance module
then formalizes the logarithmic frequency gauges and the paper's dominance
transfer principle: a coordinate dominant in any gauge dominates its own
gauge. Strict dominants are unique, and any supplied strict-dominance owner
map is idempotent, so its fibers carry canonical marked elements. The marked-
cone module packages those fibers as actual marked partitions, defines the
closed and strict cones `Γ_S`, identifies the principal cone, and proves that
a supplied strict-dominance assignment induces the unique strict marked cone
containing the point. The coordinate module then defines the finite minima
`τ_S(p,q)`, proves their positivity and diagonal normalization, and proves the
paper's exact two-family inequality characterization of `Γ_S`. The minimal-
dotted-set module implements the marked-block merge used in Lemma 3.4, chooses
a containing cone with the fewest marks, proves strict separation of distinct
minimal marks, and proves that its canonical `D(t)` is contained in the marks
of every other containing cone. The coverage module removes the remaining
existence premise: finite maxima select dominant owners, nonnegativity makes
the owner map idempotent even on tie walls, and every point of the nonnegative
orthant therefore admits a containing marked cone. It defines the canonical
regions `Γ(D)` and proves that each nonnegative point has a unique region
index. The next module proves Proposition 3.5 exactly: for nonempty `D`,
`Γ(D)` is the intersection of the union of marked cones with marks `D` and
the strict positive separation locus on `D`. The dyadic module then defines
maximal lattice scales, the finite downward index tube `𝕋_L`, and its
continuous cell union `T_L`, proving finiteness and the greatest-apex property.
The maximal-floor module then proves the wall-robust lattice criterion:
maximality is equivalent to the floor profile in every containing marked cone
with the same dotted set. This corrects the printed strict pairwise `τ_S`
clause, which is stronger than maximality on tie walls under the stated
standard-matrix axioms. The unique-apex and tube-partition modules construct
the apex, prove independence from the chosen containing cone, prove unique
maximal-apex assignment for every lattice point in a nonempty canonical
region, identify each continuous tube with an explicit closed product box,
prove regionwise coverage, and prove genuine topological interiors of distinct
nonempty-region maximal tubes are disjoint. The empty dotted region's origin
case is handled in the subsequent density module. The proximity module proves
the Lemma 3.8(i) unit cone-thickening and Lemma 3.8(iv) uniform apex-distance
bound for intersecting tubes. The density module completes Lemma 3.8(ii--iii):
every nonnegative principal-cone point lies a matrix-uniform logarithmic
sup-distance from a maximal lattice apex, and the coordinatewise meet of two
maximal apices lies within distance one of another maximal apex. The coloring
module combines the overlap bound with coordinate residues modulo a
matrix-determined integer. Same-colored intersecting maximal tubes are equal,
so every color fiber is disjoint and the number of maximal tubes through a
point is bounded by the finite color cardinality. The frequency-block module then
implements the positive binary logarithmic norm map and proves that each
`B_L = π⁻¹(T_L)` is exactly the rough product of dyadic coordinate balls and
dotted annuli. The block-gauge module proves the anisotropic physical-gauge
outer estimate and a valid reverse inclusion using floor-normalized coordinate
gauges. It explicitly withholds the printed single-constant inner inclusion on
floor tie walls, where its upper and lower requirements can conflict. The new
smooth-cutoff module reuses Mathlib's bundled `ContDiffBump` to construct a
`C∞`, `[0,1]`-valued cutoff equal to one on every exact rough frequency block,
with support in an explicit half-scale padded shell. A second, padding-aware
residue coloring proves that equal-color smooth supports are disjoint, and a
third module bounds every finite pointwise square sum by the finite color
cardinality. The completed index module then adjoins the paper's unique
low-frequency block `(D,L)=(∅,0)` and proves global frequency coverage with a
unit cutoff at every point. On any finite subfamily covering the point under
consideration, the quadratic normalization denominator is positive, the
normalized symbols are `C∞` on its nonvanishing domain and sum to one, and the
resulting multiplier and square-analysis pieces satisfy exact finite
reproducing identities while retaining support subordination. The global
local-finiteness module then proves neighborhood-level local finiteness by
reducing every support meeting a bounded ball to a finite bounded-apex family.
This makes the infinite quadratic normalization globally positive and `C∞`;
it is bundled as Mathlib's native `SmoothPartitionOfUnity`. The final global
module proves exact `finsum` multiplier reconstruction and square-analysis
identities and exposes the canonical finite carrier at every frequency.
The Section 4 layer now supplies genuine normalized Schwartz kernels,
positive-level cancellation, finite telescoping, convergence of detail partial
sums to the Dirac tempered distribution, and pointwise physical-space
convolution reconstruction. Lemma 4.1's finite arbitrary multi-index derivative
language reuses Mathlib's iterated line derivatives and support theorem. Lemma
4.2 now has actual tilded kernels constructed with Mathlib's bundled Fourier
inverse and temperate-growth multiplier API. The finite polynomial identities
in formulas (4.2)--(4.3) and every partial convolutional Calderón identity are
proved from Mathlib's geometric-sum lemmas. Pointwise multiplier support now
proves that the constructed approximation retains the original Fourier
carrier and every positive detail lies in the union of its two adjacent
carriers. Fourier scaling, normalization, a uniform polynomial bound, and
dominated convergence now prove the constructed final approximation limit.
The exact finite identity then proves the full detail-series limit. Fourier
vanishing is converted to arbitrary coordinate-moment cancellation through
Mathlib's Fourier-derivative theorem, and the physical convolution formulas
put both dual families in the explicit common carrier `(4M+1)K`. Fourier-
conjugate dilation/undilation recovers the paper's unscaled templates, proves
both relative Schwartz-seminorm estimates against the approximation family,
and constructs the complete dual family without an analytic premise.
Proposition 4.3's finite coordinatewise-box tensor
identities are proved over the actual index type `Fin n → ℕ` using Physlib's
existing continuous `SchwartzMap.productTensor`.

The completed maximal-tube index from Section 3 is now proved to partition
`ℕ^n`, including the distinguished zero low block. Finite sums and
unconditional infinite sums can be regrouped by those exact finite fibers.
The distribution-valued theorem applies this regrouping directly to the
tensor dual kernels without assuming a nonexistent completeness instance for
tempered distributions.

The unconditional analytic construction of the Lemma 4.1 Hadamard mechanism
from moment cancellation remains an explicit premise. For Lemma 4.2, exact
finite physical-space convolution formulas, qualitative compact spatial
support, Fourier support, arbitrary multi-index cancellation, the uniform
explicit support dilate, the final approximation limit, and the full
detail-series limit and the paper-faithful relative seminorm normalization are
now proved for the constructed Rychkov kernels. The implementation normalizes
the unscaled families before applying the external dyadic dilation and uses
the original approximation templates as the reference for both dual families.
For Proposition 4.3 the exact `\mathcal L` regrouping is proved,
while convergence of the raw `ℕ^n` tensor series to the Dirac distribution
remains the premise of the distributional regrouping theorem. Proposition 4.4,
anisotropic seminorm estimates, and the Hardy-space results remain
unconstructed.
The complex extension now reconstructs complex Fourier amplitudes and resolves
their pointwise Born weight on the same canonical finite carrier. Its
one-block Euclidean `L²` realization is a contractive smooth frequency
localization commuting with free Schrödinger evolution, while the abstract
branch commutes with the existing complex-linear Ipek--Caticha functional
generator. Feeding those branches to the existing rank-one
Sorkin--Johnston/Dowker--Halliwell kernel gives an exact decoherence diagonal
resolution and invariance of the full kernel under the free Schrödinger phase.
These results do not construct the paper's product-space inverse-Fourier
Calderón family, a coarse-graining event lattice, or environmental decoherence.
The finite-overlap Euclidean module retains its generic certificate-based
theorem, but the standard dyadic capstone now constructs a parity coloring
internally, proves its color fibers spectrally disjoint, and obtains
`∑ᵢ ‖Pᵢf‖² ≤ 2 ‖f‖²` without an external coloring premise. This dyadic radial
coloring is separate from the paper-specific multi-norm smooth-support coloring;
The pointwise-finite global frequency reproducing sum, finite full-index tensor
identities, paper-tube partition, and distributional regrouping are now proved.
Discharging the remaining Hadamard/analytic estimates and the raw tensor
`HasSum`, then proving the `L¹`/Hardy-space estimates, remain open.

## Holographic G → clock → contour → Levi-Civita → EFE

The production theorem
`HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_einstein_chain`
composes the strongest existing carriers without duplicating their definitions
or proofs:

1. `G = A c³/(ℏN)` and `κ_G = 8πG/c⁴` on the entropic screen
   `r = λ_C log K`;
2. the moving de Broglie clock
   `ω_dB(E) = cosh(θ) ω_C` for the same mass;
3. the Nagao–Nielsen mass-shell coordinate and its convergence condition;
4. the derived contour angle `ϑ(θ) = arctan(tanh θ)`, its exact match with the
   `p/(E/c)` slope, the positive ray representation
   `E/c + ip = exp(iϑ(θ)) r(θ)` with `r(θ) > 0`, its proof of
   `|ϑ(θ)| < π/4`, and complex-delta normalization on that permitted ray;
5. the exact `1+1` metric-derived Levi-Civita connection, complete
   `weakFieldRicciMatrix2`, and `weakFieldScalarCurvature2`, retaining the
   explicit `O(c⁻⁴)` correction and proving that its Einstein tensor vanishes;
6. the sourced linearized `Fin 4` upgrade in `WeakFieldEinstein3Plus1`: the
   Newtonian-gauge metric perturbation, its metric-derived `Γ¹₀₀ = Φ'/c²`, a
   connection-derived `R₀₀ = Φ''/c²`, the isotropic first-order Ricci/scalar
   carriers, and `G^(1) = diag(2Φ''/c²,0,0,0)`;
7. the equivalence between the full linearized rest-dust Einstein matrix
   equation and `Φ'' = 4πGρ`, plus the complex equation when the independent
   imaginary-sector relation `Λ = κ_G S` is supplied.
8. the full static `Φ(x,y,z)` upgrade: three metric-derived acceleration
   symbols `Γⁱ₀₀ = ∂ᵢΦ/c²`, equality of the complete compact Christoffel array
   with `christoffelFromMetric`, a symmetric spatial Hessian derivative of that
   metric-derived connection, all sixteen Ricci components contracted from
   `∂Γ-∂Γ`, cancellation of mixed Hessian entries,
   `R_μν^(1) = (∇²Φ/c²) I₄`, and real/complex field equations governed by
   `∇²Φ = 4πGρ`.
9. `StaticPotentialJet3`, the downstream API that packages the potential value,
   `Fin 3` gradient, symmetric `3×3` Hessian, and Laplacian into one object.
   Its adapters select the same metric derivative, metric-derived connection,
   connection derivative, Ricci, scalar, Einstein tensor, Poisson predicate,
   and complex field equation without passing loose Cartesian scalars.
10. `StaticPotentialJet3.ofFunctionAt`, the analytic constructor from a genuine
    `C²` potential `Φ : (Fin 3 → ℝ) → ℝ`. Its Cartesian gradient and Hessian
    come from the first and iterated second Fréchet derivatives, Hessian
    symmetry follows from Schwarz's theorem, and the analytic capstone exposes
    the pointwise Laplacian while reusing the typed-jet geometry.
11. `StaticPoissonField3`, which stores one Newton coupling, one global `C²`
    potential, one density field, and Poisson's equation at every point. The
    strongest capstone uses the same stored `G` for the screen count and source
    law, proves the clock/contour facts once, and supplies the metric-derived
    connection, connection-derived Ricci tensor, and real/complex linearized
    EFE carriers throughout space.
12. `homogeneousDensityPoissonField3`, the explicit non-vacuum example
    `Φ=(2πGρ/3)(x₀²+x₁²+x₂²)`. Lean computes its gradient and Hessian, proves
    `∇²Φ=4πGρ`, and instantiates the pointwise metric/connection/Ricci/EFE
    family. ZIL records that this whole-space quadratic model is neither an
    isolated finite-mass source nor an asymptotically flat nonlinear solution.
13. `StaticPoissonHodgeStar3`, the oriented Euclidean spatial-form layer. It
    reuses the repository Levi-Civita tensor to define `⋆ : Ω¹ → Ω²` and its
    normalized inverse, proves `d⋆dΦ = ∇²Φ`, rewrites Poisson's equation as the
    sourced Hodge-flux identity, and links that same pointwise source to the
    static linearized Einstein equation.
14. `StaticHodgeScreenBits`, the homogeneous local-to-screen closure. It
    defines the enclosed constant-density ball mass, proves that the radial
    derivative of the quadratic potential is `GM(R)/R²`, and computes the
    constant-normal-component spherical Hodge flux as `4πG M(R)`. The capstone
    then reuses the one screen bit count for that boundary acceleration, the
    Nagao–Nielsen horizon modulus, the area-per-bit Einstein coupling, and the
    pointwise static linearized Einstein equation. This is explicitly a
    homogeneous spherical specialization, not a general Stokes theorem.
15. `IsolatedNewtonHodgeSphereFlux`, the isolated-source upgrade. It defines
    an actual Bochner surface integral over the repository unit-sphere measure,
    proves that the inverse-square exterior field has flux `4πGM` through
    every centered sphere, and independently reuses the distributional
    fundamental solution to prove
    `Δᵈ(-GM/r) = (4πGM) • δ₀`. The capstone identifies the surface-flux
    coefficient with the Dirac-source coefficient and carries that result into
    the same boundary bit-count, Nagao–Nielsen modulus, and area-per-bit
    Einstein-coupling chain. It remains an origin-centered, distributional
    linearized carrier—not a general arbitrary-surface Stokes theorem, a
    smooth rest-dust source, or an exact nonlinear Einstein point-mass result.
16. The translation-covariant isolated-source upgrade. The general `Space`
    API now proves that distributional Laplacians commute with translations
    and that translating a Dirac delta translates its support. Reusing those
    lemmas, the isolated Newton carrier moves from the origin to any source
    point `x₀`, proves flux `4πGM` through every positive-radius round sphere
    centered at `x₀`, and proves
    `Δᵈ Φₓ₀ = (4πGM) • δₓ₀`. Its capstone retains the same bit-count and
    entropic-screen identities. This is single-source translation covariance,
    not a multi-source superposition theorem or an arbitrary-domain result.
17. `FiniteNewtonPointSources`, the first genuine multi-source carrier. It
    defines a finite point-mass distribution `ρ = ∑ᵢ Mᵢδₓᵢ` and the matching
    superposed inverse-radius potential. Linearity proves both
    `ΔᵈΦ = ∑ᵢ (4πGMᵢ)δₓᵢ` and the factored law `ΔᵈΦ = (4πG)ρ`.
    The complete source and potential configurations are covariant under a
    common translation. Its screen bridge uses only the total mass `∑ᵢMᵢ`;
    it deliberately does not assert that the chosen screen encloses the
    sources or that its flux equals the total Dirac coefficient.
18. `FiniteNewtonPointSourcesEinstein00`, the distribution-valued static
    linearized Einstein `00` bridge. It reuses the smooth connection-derived
    normalization `G₀₀^(1) = 2∇²Φ/c²`, continues that scalar coefficient to
    distributions, proves equivalence with `ΔᵈΦ = (4πG)ρ` for `c ≠ 0`, and
    instantiates it for the finite Dirac-source potential before entering the
    total-mass entropic-screen chain. It does not construct a full
    distribution-valued curvature tensor or claim a nonlinear multi-body
    Einstein solution.
19. `FiniteNewtonPointSourceResolvedFlux`, the first actual finite-source flux
    decomposition. Each source receives its own positive-radius round sphere
    centered at that source, and the existing translated isolated-source
    integral proves its flux is `4πGMᵢ`. Summing gives
    `4πG∑ᵢMᵢ`, while the distributional Laplacian is rewritten as the Dirac
    sum weighted by those measured fluxes. This is source-resolved flux, not
    total-field flux through one enclosing screen; cross-source flux terms
    still require an off-center Gauss-law or spherical divergence theorem.
20. `FiniteNewtonEnclosingSphereFlux`, the one-screen composition layer. It
    defines the actual pointwise finite superposition, proves every off-boundary
    single-source screen integrand is continuous and integrable, and proves the
    total-field flux through one round screen is exactly the sum of the actual
    off-center source fluxes. The remaining analytic solid-angle identity is
    represented by the explicit proposition `NewtonSphereFluxLaw3`; the
    enclosing-screen `4πG∑ᵢMᵢ` and Einstein/entropic capstones take a proof of
    that proposition as an argument. ZIL therefore records both the completed
    unconditional decomposition and the still-conditional analytic step.

Build the scientific theorem and its optional ZIL contract with:

```bash
lake build \
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravityField \
  Physlib.Meta.HolographicNewtonClockContourGravityZil
```

Export the contract, theorem intent, assumptions, provenance, and caveats:

```bash
lake exe zil-scan \
  Physlib.Meta.HolographicNewtonClockContourGravityZil \
  /tmp/holographic-newton-clock-gravity.zilevents.json \
  --no-cache --force
```

The ZIL contract intentionally rejects stronger readings: it does not claim a
numerical prediction of `G`, derive the EFE from clock or contour algebra,
discard the exact connection-curvature correction, identify every mass-shell
point with a unique admissible integration contour, or conflate the
Levi-Civita connection with Levi-Civita's gravitational/inertial tensor.  The
explicit metric/Ricci/scalar carrier is a `1+1` weak-field demonstrator, not a
claimed sourced construction.  The first separate `Fin 4` carrier remains the
plane-symmetric specialization.  The stronger static `Fin 4` carrier admits a
general Cartesian spatial Hessian and proves the three-coordinate Laplacian,
but it is still linearized and static—not an exact nonlinear or spherical
solution.  ZIL checks these boundaries in the separate `geometry2`,
`geometry4Linearized`, `geometry4StaticSpatial`, and `geometry4StaticJet`
contracts, plus `geometry4StaticC2Potential` and
`geometry4StaticPoissonField` and the `homogeneousDensityExample`, and records the
new `geometry4StaticHodge`, `homogeneousHodgeScreen`, and
`isolatedNewtonSphereFlux`, `isolatedNewtonTranslatedSphereFlux`, and
`finiteNewtonPointSources`, `finiteNewtonPointSourcesEinstein00`, and
`finiteNewtonPointSourceResolvedFlux` and
`finiteNewtonEnclosingSphereFlux` contracts.
The first explicitly limits `d⋆dΦ` to the oriented Cartesian Euclidean spatial
slice; the second limits its screen flux to the constant-density radial model;
the third records the actual origin-centered sphere integral plus the
distributional inverse-radius source; and the fourth moves that construction
to an arbitrary source point while forbidding promotion to arbitrary surfaces,
multiple-source systems, smooth matter, or an exact nonlinear Einstein point
source. The imaginary complex-Einstein sector remains an explicit assumption
rather than a consequence of Poisson's equation.

From the sibling `zil-lang-jrg` repository, select and verify the current target:

```bash
./bin/zil formalization-next ../physlib-epl-v430/.zil/formalization.zc
./bin/zil formalization-check \
  ../physlib-epl-v430/.zil/formalization.zc \
  entropic_newton_constant_convergence \
  ../physlib-epl-v430
```

The legacy `.zc` worklist now mirrors eighty-one selected kernel witnesses and marks
them proved. Lean compilation remains necessary, and the human author remains
responsible for confirming that statements and documentation express the
intended physics, as required by `AI-POLICY.md`.

The Schwarzschild target contracts the complete typed one-bit horizon chain:

```bash
./bin/zil formalization-check \
  ../physlib-epl-v430/.zil/formalization.zc \
  schwarzschild_one_bit_entire_chain \
  ../physlib-epl-v430
```

Its Lean theorem proves the mathematical chain. Native ZIL metadata provides a
stable claim identity, dependency and paper provenance, an explicit
non-dynamical-interpretation caveat, and elaboration-time `no_sorry`/link
validation. ZIL does not reinterpret the shared factor `2` as a physical
entanglement-driven horizon dilation.

The same module now carries a native formalization-accountability contract
derived from `zil6.md`. Its principal witness is classified
`bridge_theorem`; the theorem intent checks that the elaborated statement
actually mentions the Barletta radius, Schwarzschild radius/area, sphere area,
both entropy representations, scale distance, and the diagonal `SL(2,ℂ)`
dilation. The file contract lists those required Lean declarations and records
the prohibited generalized-mass and dynamical-dilation substitutes.

Ordinary elaboration runs:

```lean
#zil_formalization_lint physlib.schwarzschildHorizonScaleMobius
```

The module fails to elaborate if its `satisfied` promise loses a required
object, lacks a sufficiently classified theorem witness, or the theorem
statement ceases to contain one of its declared objects.

For a fast metadata-only inspection export of the seven selected Schwarzschild
claims:

```bash
lake exe zil-scan \
  Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius \
  /tmp/schwarzschild-selected.zilevents.json \
  --export-selected
```

The first invocation loads exported Lean module data; subsequent invocations
reuse an artifact-keyed cache while the compiled `.olean` remains unchanged.
Omit `--export-selected` when producing the complete batch consumed by
`zil-lang-jrg import-lean-events`. Scanner batches now also include
`formalization_contracts`, `theorem_intents`, and per-declaration `zil_level`.

All current native ZIL fragments in Physlib are enclosed by exact standalone
`/- ZIL-BEGIN -/` and `/- ZIL-END -/` markers. This includes the general
`Physlib.Meta.Zil` integration and the Schwarzschild claim graph. The portable
Schwarzschild `@zil` description remains outside the removable regions. Check
the marker contracts with:

```bash
lake exe zil-source-filter check Physlib/Meta/Zil.lean

lake exe zil-source-filter check \
  Physlib/QuantumMechanics/ComplexAction/Curvature/SchwarzschildHorizonScaleMobius.lean
```

Generate a line-preserving production version without native ZIL imports,
attributes, validation commands, attachments, or rules:

```bash
lake exe zil-source-filter strip \
  Physlib/QuantumMechanics/ComplexAction/Curvature/SchwarzschildHorizonScaleMobius.lean \
  /tmp/SchwarzschildHorizonScaleMobius.production.lean

lake env lean /tmp/SchwarzschildHorizonScaleMobius.production.lean
```

Use `keep` instead of `strip` to remove only the marker comments while retaining
all native ZIL behavior.

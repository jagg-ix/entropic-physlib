# Continuum weak-coupling reduction status

## Scope

This layer connects the existing one-level spectral rate

```text
gamma = 2 pi g^2 J(omega_0)
```

to a typed continuum-reduction contract and now instantiates that contract for
an exactly solvable Gaussian spectral collision reservoir.  The result is a
concrete Davies-scale convergence theorem for this repeated-interaction model;
it is not the general fixed-Hamiltonian thermodynamic-bath Davies theorem.

The implementation separates three analytic obligations that were previously
compressed into one phrase: “Born--Markov/secular approximation.”

## Target 1 — bath-correlation transform

`BathCorrelationTransformCertificate` records:

- a continuum correlation `C : R -> C`;
- the transition frequency `omega_0`;
- integrability of `exp(i omega_0 t) C(t)` on `[0,infinity)`;
- the one-sided transform

  ```text
  C_hat(omega_0) = integral_[0,infinity) exp(i omega_0 t) C(t) dt;
  ```

- a positive spectral weight satisfying

  ```text
  Re C_hat(omega_0) = 2 pi J(omega_0);
  ```

- finite-window approximants;
- an explicit truncation-error function; and
- convergence of that error to zero.

The theorem

```text
goldenRuleGamma_eq_coupling_mul_transform_re
```

then gives

```text
gamma = g^2 Re C_hat(omega_0).
```

The certificate is a precise target for concrete Ohmic, Lorentzian, KMS, or
other bath models. It does not invent a correlation transform from a declared
spectral number.

## Target 2 — Volterra memory to Markov generator

`VolterraMarkovApproximation` distinguishes:

1. the exact nonlocal memory term;
2. a finite-memory-window term; and
3. the local Markov replacement.

The two errors are:

```text
tailError
stateReplacementError
```

and the proved composition is

```text
norm(memoryTerm - markovTerm)
  <= tailError + stateReplacementError.
```

This prevents one “Markov approximation” premise from hiding two different
analytic requirements:

- decay/mixing of the bath correlation tail; and
- regularity or slow variation of the reduced state over the correlation time.

When both certified errors vanish, exact equality with the local term follows.

## Target 3 — secular projection and final LDDL bound

For a finite family of Bohr frequencies, the exact projection is

```text
P_sec A(i,j) = A(i,j)  if omega_i = omega_j
             = 0       otherwise.
```

The implementation proves:

- resonant coefficients are retained;
- nonresonant coefficients are removed;
- every coefficient decomposes into secular plus nonsecular parts; and
- `P_sec` is idempotent.

`FiniteFrequencySecularCertificate` records a quantitative finite-time average
and its pointwise error relative to this projection.

Finally, `OneLevelWeakCouplingReductionCertificate` composes:

```text
exact reduced field
  -> Markov field          memoryError
  -> secular field         secularError
  -> LDDL field            exact identification
```

and proves

```text
norm(F_exact(n) - F_LDDL(n))
  <= memoryError(n) + secularError(n).
```

Zero errors imply exact equality.

## Concrete Gaussian unitary-bath instantiation

`GaussianContinuumBath` uses Mathlib's Gaussian probability measure on the
continuum energy line.  It now instantiates the repository's reusable
arbitrary-measure diagonal Schrödinger construction, so its spectral evolution

```text
U(t) psi(omega) = exp(-i t omega) psi(omega)
```

is a bundled complex-linear unitary `C0` group on the genuine Hilbert space
`L2(R, gaussianReal omega_0 (2 pi); C)`.  It has proved identity, composition,
inverse, exact `L2` norm preservation, and strong continuity at every real
time.  The normalized constant vacuum vector has norm one, and
`vacuum_matrixCoefficient` identifies its actual Hilbert-space matrix
coefficient with the Gaussian characteristic function.  Consequently the
correlation is not a supplied number: `correlation_eq_vacuum_matrixCoefficient`
and `correlation_eq_spectralIntegral` identify it with the fixed bath group's
vacuum correlation and its continuum spectral integral.  The Gaussian
characteristic-function theorem then proves

```text
exp(i omega_0 t) C(t) = 4 pi J exp(-pi t^2)
integral_[0,infinity) exp(i omega_0 t) C(t) dt = 2 pi J.
```

The finite-window transform is the genuine interval integral, and
`truncationError_tendsto_zero` proves its actual norm error tends to zero.

`exactReductionCertificate` inhabits the generic memory/secular interface for
the exactly solvable collision reservoir by choosing the three reduced fields
to coincide, hence both errors are definitionally zero.  This is the exact
collision-model specialization, not a derivation that arbitrary Volterra-bath
errors vanish.  The
microscopic channel is the repository's Stinespring unitary on the system plus
two fresh bath qubits.  Preparing the bath and tracing it out is proved equal to
the channel at macroscopic time `lambda^2 t`.  Therefore

```text
Phi_reduced(lambda, s / lambda^2) = Phi_LDDL(s)       (lambda != 0),
```

which yields convergence in the bundled CPTP-channel topology and exact channel
equality uniformly on every finite macroscopic interval.  The limit is the
existing genuine CPTP `C0` semigroup, and its right infinitesimal generator is
the explicit one-level loss/gain GKSL matrix operator.

## What is now shown

The repository now has explicit formal surfaces for:

- the continuum one-sided correlation transform;
- the transformation from its real on-shell value to `gamma`;
- separate memory-tail and delayed-state errors;
- exact finite-frequency secular projection;
- finite-time averaging-error interfaces; and
- additive end-to-end error against the one-level LDDL vector field.
- a concrete continuum spectral measure and unitary phase group;
- a bundled complex-linear unitary `C0` group on the spectral `L2` carrier;
- a normalized vacuum whose matrix coefficient is the bath correlation;
- evaluated correlation transform and actual finite-window convergence;
- a zero-error instantiation of the generic reduction certificate;
- a microscopic unitary Stinespring collision reservoir;
- Davies-scale convergence of its reduced channel;
- CPTP and strong-continuity of the limiting semigroup; and
- exact identification of the limiting loss/gain GKSL generator.

## What remains open

The free persistent bath is now concrete: multiplication by energy on the
Gaussian spectral `L2` space generates the fixed unitary `C0` group and its
vacuum correlation is evaluated.  The remaining stronger target must couple
that bath to the system through one microscopic Hamiltonian `H_0 + lambda V`.
It still needs a self-adjoint coupled operator on a common domain, KMS data for
the same interacting bath state, thermodynamic/continuum limiting control, and
a proof that its reduced dynamics converges to the collision-model semigroup.
Those coupled-limit obligations are not silently inferred from either the free
bath group or Stinespring purification.

Physical calibration, observed transition/environment identity, and a frozen
held-out benchmark remain external evidence obligations.

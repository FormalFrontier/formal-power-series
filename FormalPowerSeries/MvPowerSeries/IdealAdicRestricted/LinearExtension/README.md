# Polynomial linear operators on restricted series

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LinearExtension`.
For any variable type `σ`, commutative ring `R`, ideal `I : Ideal R` and
`[IsAdicComplete I R]`, every `R`-linear polynomial endomorphism
`F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R` has a canonical `R`-linear
extension to the existing restricted subring:

```lean
MvPowerSeries.restrictedLinearExtension I F :
  MvPowerSeries.adicallyRestrictedSubring (σ := σ) I →ₗ[R]
    MvPowerSeries.adicallyRestrictedSubring (σ := σ) I
```

Completeness is required for **the coefficient ring**, not separately for the
restricted-series ring. No finite-variable, finite-generation, domain,
regularity, valuation, nontriviality or proper-ideal assumption is needed.
The existing `adicallyRestrictedAlgebra I` supplies the scalar action; this
module introduces no competing scalar instance.

## Finite levels and extension laws

`polynomialLinearMapMod I n F` is an `R ⧸ I ^ n`-linear endomorphism of
`MvPolynomial σ (R ⧸ I ^ n)`. It combines the **finite** monomial expansion
against the corresponding reduced images under `F`.
`polynomialLinearMapMod_map` commutes with polynomial reduction, and
`polynomialLinearMapMod_factorPow` commutes with transitions `m ≤ n`.

For a restricted series `f`, the defining equation holds at **every** level:

```lean
MvPowerSeries.adicReduction I n (MvPowerSeries.restrictedLinearExtension I F f) =
  MvPowerSeries.polynomialLinearMapMod I n F (MvPowerSeries.adicReduction I n f)
```

This is `adicReduction_restrictedLinearExtension`.
`restrictedLinearExtension_polynomial` gives agreement with `F` on
`polynomialToRestricted I p`; `restrictedLinearExtension_preserves_ker`
preserves each coefficientwise `RingHom.ker (adicReduction I n)`.
`restrictedLinearExtension_unique` identifies an `R`-linear competitor **only
when both** polynomial agreement and preservation of all these reduction
kernels are supplied. Polynomial agreement alone does not imply uniqueness.
The kernel is not claimed to equal the intrinsic restricted-series submodule
`I ^ n • ⊤` for arbitrary ideals.

The construction transports compatible finite quotient polynomials through
the existing `adicPolynomialLevelEquiv` and
`adicallyRestrictedEquivAdicCompletion` to the existing restricted subring.
Finite polynomial reductions at all levels are essential, especially with
infinitely many variables. It does not define a new completion or claim
intrinsic restricted-ring completeness.

The [ordinary-import client](../../../../Tests/MvPowerSeries/IdealAdicRestricted/LinearExtension.lean)
checks addition, scalar multiplication, finite-level and polynomial laws,
kernel preservation, uniqueness, identity, level zero, empty variables,
the zero ideal and the zero ring `ZMod 1`.

## Reproduction and provenance

Use the repository's pinned `lean-toolchain` (Lean `v4.34.0-rc2`) and complete
`lake-manifest.json` (sole direct mathlib revision
`83abb3e776bdefcbc447a1e44d0debe4010039e5`). From the repository root,
fetch the matching precompiled mathlib cache **successfully before building**:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake build FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LinearExtension
LEAN_NUM_THREADS=2 lake build Tests.MvPowerSeries.IdealAdicRestricted.LinearExtension
lake build FormalPowerSeries Tests
```

At the earlier 2026-09-30 pre-check preparation snapshot, these reproduction
commands did **not** establish a destination build or audit. Subsequently,
original configured run 1473 on exact destination commit
`ea3901676c230babd4af405c3e8d4f089ae7cbc8` built both aggregate roots
in **13.8 seconds (1,958 Lake jobs)** and passed the complete transitive
standard-three axiom audit, including private/generated declarations. Its
**219-second** end-to-end CI window includes setup, auditing and artifacts;
see the [root README build and cost guidance](../../../../README.md#build-and-use)
for measured command times and explicitly unvalidated planning estimates. No
peak RAM or disk use was measured. Fresh independent destination contribution
review and the original checks preceded Anchor's code acceptance and main
integration; a separate consolidated release review, protected promotion and
verified GitHub publication remain to be arranged. No source-coverage
decision follows.

The original fixed-basis/completion design was developed by Formal Frontier
worker-a Hive Task `hive-request-96f6d32357a1f51f399a39913faeab788ed93acc`
(UID `3738ef8a-fc35-419e-9c6f-c22f984f7d4c`); the producer and private client
were implemented by worker-b Task
`hive-request-e1010a8901a682edc7a851fb5f7395aac3fd7689`
(UID `a104d42c-a577-4aa3-ba24-1a757364d1c9`). This transfer into
`FormalPowerSeries` is by a separate worker-b execution; it reuses the existing
[completion](../InverseLimit/README.md) and
[linear quotient](../LinearQuotient/README.md) APIs and mathlib's native
polynomial and adic-completion interfaces. Original development and changed
destination checks are distinct. Original Formal Frontier files are licensed
under Apache-2.0; mathlib is an Apache-2.0 dependency. Authors: Formal
Frontier Agents.

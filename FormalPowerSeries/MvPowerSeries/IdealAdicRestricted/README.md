# Ideal-adically restricted multivariate power series

SPDX-License-Identifier: Apache-2.0

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted` to work with the
coefficientwise ideal-adically restricted subring of the **native**
`MvPowerSeries σ R`. For any `σ : Type*`, `R : Type*`, `[CommRing R]`, and
`I : Ideal R`, the predicate `MvPowerSeries.IsAdicallyRestricted I f` means

```lean
∀ k : ℕ, {m : σ →₀ ℕ | MvPowerSeries.coeff m f ∉ I ^ k}.Finite
```

No norm, finite variable type, finite generation, proper ideal, completeness,
domain, separatedness, or assumption on `k` is required. The corresponding
`MvPowerSeries.adicallyRestrictedSubring I` is the intersection of the preimages
of the **native** polynomial-inclusion subrings under quotient coefficient maps;
`mem_adicallyRestrictedSubring` identifies its carrier with the displayed
predicate.

## Polynomial reduction

- `finite_exception_iff_map_mem_poly_range I k f` equates the finite exception
  set with membership of the quotient series in the range of
  `MvPolynomial.coeToMvPowerSeries.ringHom`.
- `isAdicallyRestricted_iff_map_mem_poly_range I f` states that equivalence at
  every ideal-power level.
- `adicReduction I k` is a surjective **ring homomorphism** from the restricted
  subring to `MvPolynomial σ (R ⧸ I ^ k)`;
  `adicReduction_surjective I k` lifts any polynomial over the quotient.
- `adicReduction_coe I k f` embeds its output into the native quotient power
  series and identifies it with `MvPowerSeries.map (Ideal.Quotient.mk (I ^ k)) f`.
  `coeff_adicReduction I k f m` computes the coefficient as
  `Ideal.Quotient.mk (I ^ k) (MvPowerSeries.coeff m f)`.
- `map_polynomial_coe`, `isAdicallyRestricted_polynomial`, and the native
  polynomial inclusion `polynomialToRestricted I` show how to construct
  restricted elements from polynomials; `polynomialToRestricted_coe` and
  `adicReduction_polynomial` identify their actual reductions with native
  `MvPolynomial.map`.

For example, with `I : Ideal ℤ`, `k : ℕ`, and
`f : MvPowerSeries.adicallyRestrictedSubring (σ := Fin 2) I`:

```lean
def residue (I : Ideal ℤ) (k : ℕ)
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := Fin 2) I) :
    MvPolynomial (Fin 2) (ℤ ⧸ I ^ k) :=
  MvPowerSeries.adicReduction I k f

example (I : Ideal ℤ) (k : ℕ)
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := Fin 2) I)
    (m : Fin 2 →₀ ℕ) :
    (residue I k f).coeff m =
      Ideal.Quotient.mk (I ^ k) (MvPowerSeries.coeff m f) :=
  MvPowerSeries.coeff_adicReduction I k f m
```

The ordinary-import client in
[`Tests/MvPowerSeries/IdealAdicRestricted.lean`](../../../Tests/MvPowerSeries/IdealAdicRestricted.lean) additionally
tests polynomial lifts and the cases `k = 0` (zero quotient), `I = ⊤` (every
series), `I = ⊥` (polynomial example), and `σ = Fin 0` (every series). Nothing
requires a nonzero quotient or a positive number of variables.

With **finitely many variables**, the separate [degree-cutoff guide](DegreeDecay/README.md)
characterizes restrictedness by an ideal-adic cutoff in total degree; its
[ordinary-import client](../../../Tests/MvPowerSeries/IdealAdicRestricted/DegreeDecay.lean)
proves the infinite-variable converse false. When `I.FG` also holds, the
[finite-generation kernel guide](FinitelyGeneratedKernel/README.md) identifies
the kernel of every `adicReduction I k` with the algebraic ideal generated
by restricted constants from `I ^ k`, including `k = 0`. Its
[client](../../../Tests/MvPowerSeries/IdealAdicRestricted/FinitelyGeneratedKernel.lean)
checks the finite decomposition and degenerate/nonregular cases. Neither
restriction is imposed on this base module or the separate regular-principal
kernel result.

## Ideal change, residue and first-variable regrouping

The [ideal-change guide](IdealChange/README.md) describes restriction along
`I ≤ J` and surjective finite-polynomial reduction modulo `J`. The
[residue guide](ValuationResidue/README.md) specializes it to the maximal
ideal of a local ring. The [first-variable guide](FirstVariableRegrouping/README.md)
describes restricted coefficient slices, polynomial embeddings and `Fin`
reindexing, without asserting surjectivity onto all iterated power series.

## Reproduction and scope

From the repository root, use the pinned Lean `v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, and `lake-manifest.json`:

```sh
lake exe cache get
lake build FormalPowerSeries.MvPowerSeries.IdealAdicRestricted
lake build Tests.MvPowerSeries.IdealAdicRestricted
```

Both modules enable `warningAsError` and are imported by the
`FormalPowerSeries` and `Tests` roots, respectively. The companion
[degree cutoff](DegreeDecay/README.md),
[finitely generated kernel](FinitelyGeneratedKernel/README.md),
[regular-principal kernel](PrincipalKernel/README.md),
[scalar-linear quotient](LinearQuotient/README.md) and
[coefficient-complete inverse-limit](InverseLimit/README.md) modules extend the
API; the principal quotient and inverse-limit equivalences have additional
hypotheses, while scalar-linear reduction works for any ideal. This base module
by itself does **not** assert arbitrary-ideal
internal kernels, norm/radius-weighted `MvPowerSeries.IsRestricted`, variable-adic
completion, total-degree cutoffs, preparation/division, general coefficient-map
naturality, or source-specific correspondence and coverage.

For separate theorems under stronger valuation/adic assumptions, see the
[content, leading-term and division guide](RestrictedDivision/README.md) and
[conditional primitive ideal-generation guide](PrimitiveStandardBasis/README.md).
The public [cofinal module-filtration comparison](../../AdicCompletion/README.md)
is independently importable and works for arbitrary modules.

## Provenance

The definitions and proofs use native mathlib polynomial/power-series rings,
their coefficient maps, truncation, inclusion and quotient-ring operations;
they do not reimplement those structures. Native `MvPowerSeries.Basic` and
`MvPowerSeries.Trunc` credit Johan Commelin and Kenny Lau;
`MvPolynomial.Basic`/`Eval` credit Johannes Hölzl, Johan Commelin and Mario
Carneiro; `Ideal.Quotient.Defs` credits Kenny Lau, Chris Hughes, Mario
Carneiro and Anne Baanen. Native mathlib remains separately authored work.

Formal Frontier AI contributors developed the restricted-series definition,
proofs, client and guide, later adapted here as a source-independent native
series API. This does not newly prove the native mathlib results or assert
source-specific coverage. See [repository metadata](../../../formalization.yaml)
for sources, license and contributors.

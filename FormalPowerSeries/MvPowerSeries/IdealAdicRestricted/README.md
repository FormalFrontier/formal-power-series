# Ideal-adically restricted multivariate power series

SPDX-License-Identifier: Apache-2.0

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted` for series that
become polynomials under a specified family of coefficient homomorphisms,
and for their ideal-adic specialization. Variables, coefficients, reduction
indices and target coefficients may inhabit four independent universes.

## Polynomiality under coefficient maps

For commutative semirings `C` and `Q i` and any family `q : ∀ i, C →+* Q i`,
`MvPowerSeries.polynomialReductionSubalgebra σ q` is the `C`-subalgebra of
`MvPowerSeries σ C` with carrier

```lean
∀ i, MvPowerSeries.map (q i) f ∈
  Set.range (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := Q i))
```

Equivalently, each set `{m | q i (MvPowerSeries.coeff m f) ≠ 0}` is finite.
No algebra structures on `Q i`, compatibility or surjectivity of `q`, finite
variable type, or inhabited index type are needed. The ambient and subtype
algebra structures are the usual coefficient algebra structures.

- `mem_polynomialReductionSubalgebra` and
  `mem_polynomialReductionSubalgebra_iff_finite_support` characterize membership;
  `polynomialReductionSubalgebra.ext` compares ambient coefficients, and
  `polynomialReductionSubalgebra.coe_algebraMap` identifies coefficient constants.
- `map_polynomial_coe` works over commutative semirings.
  `polynomialToReductionSubalgebra σ q` codomain-restricts the stock polynomial
  algebra inclusion; its `_coe` and `val_comp_polynomialToReductionSubalgebra`
  laws identify the ambient map.
- `polynomialReduction σ q i` is a semiring homomorphism to
  `MvPolynomial σ (Q i)`. Its `_coe`, `coeff_polynomialReduction`, `_polynomial`
  and `_algebraMap` laws compute series, coefficients, polynomials and constants.
  It is surjective when the single row `q i` is surjective.
- `polynomialReduction_jointly_injective_iff` characterizes when all row reductions
  determine a restricted series: exactly when the coefficient homomorphisms jointly
  determine coefficients.
- `polynomialReduction_transition` commutes with a specified
  `t : Q j →+* Q i` provided `t.comp (q j) = q i`; no transitions are presumed.
- For maps into ambient series whose reduced coefficient supports are finite,
  use `AlgHom.codRestrict`; `polynomialReductionSubalgebra.val_comp_codRestrict`
  gives its factorization equation with the subalgebra inclusion.

The boundary laws are mathematical characterizations: an empty reduction-index
type gives the whole algebra (`polynomialReductionSubalgebra_eq_top`), while one
identity row gives exactly the polynomial-inclusion subalgebra
(`polynomialReductionSubalgebra_id`). For that row, reduction and polynomial
inclusion are mutual inverses, by `polynomialReduction_id_polynomial` and
`polynomialToReductionSubalgebra_id_reduction`.

## Ideal-adic specialization

For any `σ : Type*`, `R : Type*`, `[CommRing R]`, and `I : Ideal R`,
the predicate `MvPowerSeries.IsAdicallyRestricted I f` means

```lean
∀ k : ℕ, {m : σ →₀ ℕ | MvPowerSeries.coeff m f ∉ I ^ k}.Finite
```

No norm, finite variable type, finite generation, proper ideal, completeness,
domain, separatedness, or assumption on `k` is required. The corresponding
`MvPowerSeries.adicallyRestrictedSubring I` is the underlying subring of
`polynomialReductionSubalgebra σ (fun k => Ideal.Quotient.mk (I ^ k))`.
The public equality `polynomialReductionSubalgebra_toSubring` identifies these
bundled structures; `mem_adicallyRestrictedSubring` identifies the carrier
with the displayed predicate. The polynomial inclusion and reductions below
specialize the same family construction, without a second support or
polynomial-selection implementation.

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
[`FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted.lean`](../../../FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted.lean) additionally
tests polynomial lifts and the cases `k = 0` (zero quotient), `I = ⊤` (every
series), `I = ⊥` (polynomial example), and `σ = Fin 0` (every series). Nothing
requires a nonzero quotient or a positive number of variables.

With **finitely many variables**, the separate [degree-cutoff guide](DegreeDecay/README.md)
characterizes restrictedness by an ideal-adic cutoff in total degree; its
[ordinary-import client](../../../FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/DegreeDecay.lean)
proves the infinite-variable converse false. When `I.FG` also holds, the
[finite-generation kernel guide](FinitelyGeneratedKernel/README.md) identifies
the kernel of every `adicReduction I k` with the algebraic ideal generated
by restricted constants from `I ^ k`, including `k = 0`. Its
[client](../../../FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/FinitelyGeneratedKernel.lean)
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

## Singleton division, quotient units and preparation

The [singleton division guide](SingletonDivision/README.md) separates the
Hausdorff leading-product and uniqueness laws from primitive existence, which
additionally requires completeness, a nonzero parameter and radical equality.
The [first-variable division guide](FirstVariableDivision/README.md) explains
the scalar-top residue criterion and finite-polynomial remainder, including
degree zero. The [quotient-unit guide](FirstVariableUnit/README.md) records
polynomial-residue unit reflection and the criterion for a supplied division
of `X₀^d` by a divisor with regrouped residue degree `d` and nonzero scalar
top, with actual remainder supported below `d`. Radical equality and
completeness reflect the computed quotient residue to a unit. The
[preparation guide](FirstVariablePreparation/README.md) combines these laws:
over a commutative valuation domain, for a restricted divisor with regrouped
maximal-ideal residue degree `d` and
nonzero scalar coefficient at `d`, a nonzero principal-adic parameter in the
maximal ideal, radical equality and completeness, it constructs a restricted
unit and a unique monic polynomial of degree `d`, including `d = 0` and
`n = 0`. Its [client](../../../FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/FirstVariablePreparation.lean)
uses uniqueness without assuming a competing multiplier is a unit.

## Reproduction and scope

From the repository root, use the pinned Lean `v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, and `lake-manifest.json`:

```sh
lake exe cache get
lake build FormalPowerSeries.MvPowerSeries.IdealAdicRestricted
lake build FormalPowerSeriesTests.MvPowerSeries.IdealAdicRestricted
```

Both modules enable `warningAsError` and are imported by the
`FormalPowerSeries` and `FormalPowerSeriesTests` roots, respectively. The companion
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
series API. The coefficient-homomorphism family construction generalizes that
same restricted-series core, retaining its ideal-adic specialization.
This does not newly prove the native mathlib results or assert
source-specific coverage. See [repository metadata](../../../formalization.yaml)
for sources, license and contributors.

<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- Authors: Formal Frontier Agents -->

# Content, leading terms and restricted division

Import individual `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.*`
modules below, or import `FormalPowerSeries` for the entire family. These are
coefficientwise **ideal-adically restricted** native multivariate power series,
not norm/radius-weighted series. The variable type may be empty or infinite.
The [base guide](../README.md) defines restrictedness and polynomial reduction;
the [API index](../../../../API.md) lists the main signatures.

## Coefficients and intrinsic leading terms

- `Content`: over `[PreValuationRing R]` and `[IsHausdorff I R]`,
  `MvPowerSeries.IsAdicallyRestricted.exists_span_range_eq_span_coeff`
  finds an actual coefficient generating the coefficient-content ideal of a
  restricted series. No completeness or principal ideal is required.
- `SelectedFactor`: if a selected coefficient generates that content ideal,
  `MvPowerSeries.IsAdicallyRestricted.exists_selected_coeff_factor` factors
  the series by the selected coefficient, with a restricted factor whose
  selected coefficient is one. Regularity of the coefficient is not assumed.
- `LeadingTerm`: over a valuation domain with separated principal filtration,
  `MvPowerSeries.restrictedContentIndex` and `restrictedResidue` choose a
  content factor and its polynomial reduction in `R ⧸ m`.
  `MonomialOrder.restrictedLeadingExponent` is independent of this choice;
  `restrictedLeadingTerm` and `restrictedLeadingTermIdeal` instead use
  **actual coefficients in `R`**. A nonzero series need not have nonzero
  reduction modulo `m`; normalization is essential.
- `MonicParameter`: for a finite primitive family over a valuation domain,
  `MvPowerSeries.exists_common_monic_parameter` chooses a common principal
  parameter at which normalized reductions have the required monic degrees.
  The hypotheses include a nonzero original parameter in the maximal ideal
  whose radical is that maximal ideal.

## Polynomial division and adic correction

- `PolynomialDivision` extends the fixed `R`-linear polynomial remainder and
  quotient operators to restricted series over `[IsAdicComplete I R]`, using
  the already supplied `restrictedLinearExtension`. With a finite divisor
  family and unit polynomial leading coefficients, it supplies a decomposition
  and actual coefficientwise remainder-cone laws. The **polynomial** linear
  division algorithm comes from the pinned `MultivariatePolynomials.LinearDivision`.
- `RestrictedGeometricInverse` inverts an `R`-linear endomorphism raising the
  coefficientwise reduction kernel by one level, using coefficient-adic
  completeness and existing inverse-limit/linear-quotient APIs. It does not
  identify these kernels with arbitrary intrinsic restricted-ring ideal powers.
- `PerturbedDivision` corrects division when finite restricted divisors agree
  with the polynomial divisors at first reduction; it reuses the existing
  `KernelFiltration` law and the geometric inverse.
- `MonicDivision` obtains an existential division by finite restricted
  divisors whose first reductions are monic. Polynomial monic lifting is
  provided by the pinned `MultivariatePolynomials.MonicLift`.

Neither quotient nor remainder is claimed unique. `Cofinal` transports
`IsAdicallyRestricted` for the *same underlying series* between ideals with
`I ≤ J` and `J ^ N ≤ I` for positive `N`; it does not identify the two
restricted subrings. The separately importable
[`AdicCompletion.Cofinal`](../../../AdicCompletion/README.md) supplies public
Hausdorff, precompleteness and completeness comparisons for arbitrary modules.
`ValuationNormalizedDivision` combines these comparisons with a common
parameter to give `MonomialOrder.exists_restricted_primitive_division`:
over a valuation domain, a nonzero parameter `a` in the maximal ideal with
`radical (span {a}) = m`, completeness at `span {a}`, and a finite primitive
family of restricted divisors, it produces restricted quotients and a remainder
whose **R-valued** coefficients vanish on the leading cones. Its conclusion is
existential and imposes no finite-variable condition. The independent
[`PrimitiveStandardBasis` guide](../PrimitiveStandardBasis/README.md)
describes the additional leading-term-ideal premise needed for ideal generation.

All ten ordinary-import clients live under
`Tests/MvPowerSeries/IdealAdicRestricted/`; the cofinal comparisons, empty
family and empty-variable cases are exercised there. The old
`LinearExtension` and `KernelFiltration` clients remain in place.

## Attribution and scope

Formal Frontier AI contributors originally developed these separate content,
factorization, leading-term, polynomial and adic-correction, normalized-division
and ideal-generation proofs; their mathematical contributions are retained
through module relocation. The polynomial algorithms are original work of the
separately licensed MultivariatePolynomials library, and the foundational
polynomial, valuation, ideal and completion APIs remain separately authored
mathlib work. These modules assert neither preparation nor standard-basis
existence, unique division, or formal coverage of a source.

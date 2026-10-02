<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- Authors: Formal Frontier Agents -->

# Conditional ideal generation by primitive restricted series

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.PrimitiveStandardBasis`.
Let `R` be a valuation domain, `σ` any variable type, and `a : R` a nonzero
element of `IsLocalRing.maximalIdeal R` with
`(Ideal.span {a}).radical = IsLocalRing.maximalIdeal R` and
`[IsAdicComplete (Ideal.span {a}) R]`. Write `T` for
`MvPowerSeries.adicallyRestrictedSubring (σ := σ) (Ideal.span {a})`.

For `J : Ideal T` and a finite (possibly empty) family `g : ι → T` of
**primitive** elements of `J` (their actual coefficient-content ideals are
`⊤`), `MonomialOrder.ideal_eq_span_of_primitive_standardBasis` has the
essential *additional* premise in `MvPolynomial σ R`:

```lean
μ.restrictedLeadingTermIdeal a ham J =
  Ideal.span (Set.range (fun i => μ.restrictedLeadingTerm a ham (g i)))
```

It concludes `J = Ideal.span (Set.range g)`. These are intrinsic leading
terms with coefficients in **`R`**, not leading terms of a residue-field
polynomial; the normalized residue is used to detect the leading exponent.
No finite-variable or nonempty-family assumption is introduced. There is no
claim that a family satisfying the leading-term-ideal equality exists, and
no uniqueness of quotient or remainder or preparation theorem.

The proof uses the intrinsic leading exponent and primitive leading-unit
lemmas from `LeadingTerm`; it converts the polynomial leading-term ideal into
a monomial ideal. Mathlib's `MvPolynomial.mem_ideal_span_monomial_image`
locates a componentwise divisor cone. `ValuationNormalizedDivision` then
gives a restricted remainder with zero **actual** coefficients on those
cones; a nonzero remainder in `J` would have a nonzero leading coefficient
in one of the cones. Thus the remainder is zero. See the
[`Tests` client](../../../../Tests/MvPowerSeries/IdealAdicRestricted/PrimitiveStandardBasis.lean)
and the [division guide](../RestrictedDivision/README.md).

The formal statement and proof are standalone mathematical library content;
source-specific correspondence and coverage are separate matters.

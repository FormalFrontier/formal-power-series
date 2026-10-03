# First-variable restricted division

Import [FirstVariableDivision](../FirstVariableDivision.lean); see the
[ordinary-import client](../../../../FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/FirstVariableDivision.lean)
for degree-zero and empty-tail cases. The lexicographic scalar-top lemma comes
from the published `MultivariatePolynomials.FirstVariableLex` library; this
module uses its `Finsupp.cons_zero_le_cons_iff` directly.

For `Fin (n + 1)` variables over a valuation domain `V`, write
`I = Ideal.span {a}` and `k = V ⧸ IsLocalRing.maximalIdeal V`. Assume that
`a ≠ 0`, `a` lies in the maximal ideal, `I.radical` equals that ideal,
`[IsAdicComplete I V]`, and the actual coefficients of the restricted divisor
`f` generate `⊤`. Let `F` be its `k`-polynomial residue regrouped in the
first variable. Suppose `F.natDegree = d` and `F.coeff d = C c` with `c ≠ 0`.

- `restrictedLeadingExponent_lex_eq_cons_of_scalar_top` identifies the
  intrinsic maximum-lex exponent of `f` as `(0 : Fin n →₀ ℕ).cons d`.
- `existsUnique_firstVariable_division_of_leadingExponent` turns a specified
  leading exponent into a unique quotient `q` and polynomial remainder `P`
  for every dividend `h`, with
  `h = q * f + polynomialRestrictedFinFirst I n P` and
  `P.degree < (d : WithBot ℕ)`.
- `existsUnique_firstVariable_division_of_scalar_top` obtains that exponent
  from the scalar-top hypothesis; `exists_firstVariable_monomial_division_of_scalar_top`
  specializes the dividend to the distinguished monomial and spells out the
  actual remainder-coefficient vanishing condition.

The assertions include `d = 0` and `n = 0`. The degree bound uses `WithBot`
so the zero polynomial is an admissible remainder at degree zero. Existence
uses primitive singleton restricted division and the finite-polynomial image
characterization of **actual** remainder support. Division alone does not
assert an invertible quotient or preparation; the
[preparation guide](../FirstVariablePreparation/README.md) combines it with
the quotient-unit law. Developed by Formal Frontier Agents under Apache-2.0.

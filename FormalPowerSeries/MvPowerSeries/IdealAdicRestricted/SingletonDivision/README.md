# Intrinsic leading products and singleton division

Import [SingletonDivision](../SingletonDivision.lean). Its generic product law
is in [LeadingTerm/Product](../LeadingTerm/Product.lean); the
[ordinary-import client](../../../../FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/SingletonDivision.lean)
exercises products, uniqueness and existence, including empty variable types.

Let `R` be a commutative valuation domain, `σ` an arbitrary variable type,
`μ : MonomialOrder σ`, and `a` a member of the maximal ideal. Assuming
`[IsHausdorff (Ideal.span {a}) R]`:

- `MonomialOrder.restrictedLeadingExponent_mul_of_ne_zero` gives a nonzero
  product of nonzero restricted series and additivity of its intrinsic
  **normalized-residue exponent**, not a multiplication law for actual leading
  coefficients.
- `MonomialOrder.restricted_singleton_division_unique` proves that two pairs
  satisfying `f = q * g + r` and `f = q' * g + r'`, for `g ≠ 0`, coincide if
  every **actual** remainder coefficient on the componentwise cone above the
  intrinsic leading exponent of `g` vanishes. Neither result needs a primitive
  divisor or adic completeness, and `a` may be zero.

`MonomialOrder.existsUnique_restricted_primitive_singleton_division` also
supplies existence for a divisor whose actual coefficients generate the unit
ideal. It requires `a ≠ 0`, radical equality of `(a)` with the maximal ideal,
and `(a)`-adic completeness in addition to the conditions above; it specializes
the finite-family primitive division theorem. No existence for a nonprimitive
divisor follows. Nonprimitive divisors still satisfy the standalone uniqueness
theorem whenever the two supported remainder equations are supplied.

The arguments reuse coefficient-content factorization, polynomial residue and
the finite-family restricted division theorem. Developed by Formal Frontier
Agents under Apache-2.0.

# First-variable preparation of restricted power series

## Headline results

[`MvPowerSeries.existsUnique_firstVariable_preparation_of_scalar_top`](../FirstVariablePreparation.lean) prepares
an adically restricted series over a commutative valuation domain as a unit
times a monic polynomial in its first variable. Its residue polynomial must
have degree `d` and a nonzero scalar coefficient at `d`. That coefficient
implies the actual coefficients generate the unit ideal. The principal adic
parameter is nonzero, lies in the maximal ideal, generates an ideal whose
radical is the maximal ideal, and the base ring is complete for that
principal ideal.

[`MvPowerSeries.existsUnique_firstVariable_preparation_of_scalar_top_of_primitive`](../FirstVariablePreparation.lean)
retains the explicit actual-coefficient primitivity hypothesis for direct use
with primitive division; the headline theorem derives it from the scalar
coefficient.

The monic polynomial has **exact degree** `d`, including `d = 0` and with zero
remaining variables. The equation uses the concrete finite-variable embedding
`polynomialRestrictedFinFirst`. The quotient and polynomial are jointly
unique among all competing monic polynomials of exact degree `d`; the
competitor's quotient need not be assumed a unit.

## Proof and usage

Apply `existsUnique_firstVariable_division_of_scalar_top` to the embedded
monomial `X ^ d`. If its remainder is `R`, the preparation polynomial is
`X ^ d - R`. The strict degree bound on `R` makes the difference monic of
degree `d`; actual coefficientwise support of the embedded remainder allows
`isUnit_quotient_of_restrictedFinFirst_division` to detect the unit quotient.
For any competing monic polynomial of degree `d`, its difference from `X ^ d`
has degree below `d`. It gives a second division of the same monomial by the
same series; uniqueness of division identifies both components.

Import
`FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.FirstVariablePreparation`.
The [ordinary-import examples](../../../../FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/FirstVariablePreparation.lean)
instantiate monomial divisors `X ^ d`, recover the pair `(1, X ^ d)` and
apply whole-pair uniqueness to arbitrary competitors, including degree zero
and no remaining variables.

This is preparation of **globally adically restricted series**, controlled by
the **maximum** first-variable degree of their residue polynomial. Ordinary
formal power-series Weierstrass preparation based on the **minimum** order of
the reduction does not supply this statement or its restricted-polynomial
remainder. Nonzero adic parameter is essential for the invoked restricted
division theorem. For a nonfield valuation domain and a nonzero nonunit `t`,
the zero-parameter ring of restricted one-variable series is a polynomial
ring: `1 + t X` has constant residue `1`, but no monic degree-zero
preparation since it has no polynomial inverse. Thus the zero-parameter
boundary is not covered.

# Local-ring polynomial residue

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.ValuationResidue`.
See the [module](../ValuationResidue.lean) and its
[client](../../../../FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/ValuationResidue.lean).

For a commutative local ring `R` and `a ∈ IsLocalRing.maximalIdeal R`,
`restrictedResidueHom a ham` takes a series restricted for `Ideal.span {a}`
to a polynomial over the residue quotient. Its coefficient formula reduces
each series coefficient modulo the maximal ideal. The homomorphism is
surjective: any quotient polynomial lifts coefficientwise to a polynomial
in the restricted subring.

If `R` is a valuation domain, `restrictedResidueHom_apply` identifies this
map with `restrictedResidue`; the zero, one, addition, multiplication, and
polynomial laws follow. Restricted units map to units. Unit reflection is
not claimed. Local-ring construction requires neither valuation nor
completeness, finite variables, or a nonzero parameter.

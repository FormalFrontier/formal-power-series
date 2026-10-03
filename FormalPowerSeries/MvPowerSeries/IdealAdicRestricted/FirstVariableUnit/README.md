# Units of conditional first-variable quotients

Import [FirstVariableUnit](../FirstVariableUnit.lean); the
[ordinary-import client](../../../../FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/FirstVariableUnit.lean)
exercises the unit criterion and the actual-support hypothesis. Generic
residue reflection is in [UnitDetection/Residue](../UnitDetection/Residue.lean).

For a commutative local ring `R` and `a` in its maximal ideal,
`isUnit_of_isUnit_restrictedResidueHom` reflects a unit of the polynomial
residue to a unit of the `(a)`-restricted subring when
`(Ideal.span {a}).radical` equals the maximal ideal and `R` is `(a)`-adically
complete. `isUnit_of_isUnit_restrictedResidue` is the valuation-domain
specialization. Neither needs finitely many variables.

`finSuccEquiv_restrictedResidueHom_polynomialRestrictedFinFirst` commutes
polynomial embedding in the first variable with coefficientwise reduction.
`restrictedResidueHom_quotient_of_restrictedFinFirst_division` starts from an
**already supplied** division equation for `X ^ d` by `f` with quotient `q`
and an actual remainder whose coefficients vanish at first exponents at least
`d`. If the regrouped polynomial residue of `f` has degree `d` and scalar
top coefficient `C c`, `c ≠ 0`, then the polynomial residue of `q` is
`C (c⁻¹)`. This calculation needs neither completeness nor a radical
assumption. `isUnit_quotient_of_restrictedFinFirst_divisionHom` adds those
assumptions to infer `IsUnit q`; its valuation-domain wrappers use the genuine
valuation residue. The statements include `d = 0` and `n = 0`.

The actual-support condition is essential: a unit divisor can divide the
degree-zero monomial with quotient zero and remainder one, but this quotient
is not a unit. These conditional laws do **not** construct division or
preparation; the [preparation guide](../FirstVariablePreparation/README.md)
combines them with division and its uniqueness. Developed by Formal Frontier
Agents under Apache-2.0.

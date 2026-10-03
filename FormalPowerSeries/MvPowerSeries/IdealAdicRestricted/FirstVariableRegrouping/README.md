# Restricted first-variable regrouping

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.FirstVariableRegrouping.Fin`.
See [coefficient regrouping](../FirstVariableRegrouping.lean),
[renaming](../Rename.lean), the [Fin bridge](Fin.lean), and the
[client](../../../../FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/FirstVariableRegrouping.lean).

For `I : Ideal R`, let `S` be the restricted subring in variables `τ` and
`T` the restricted subring in variables `Option τ`. The additive map
`restrictedFirstCoeff I n : T →+ S` extracts the coefficient at the
distinguished-variable exponent `n`. It is generally not multiplicative.
The injective ring map `restrictedFirstRegroup I : T →+* PowerSeries S`
assembles these slices and agrees with raw `optionEquivLeft` after forgetting
the coefficient restriction. It need not be surjective: independently
restricted slices need not have globally finite exceptional support.

`polynomialRestrictedFirst I : Polynomial S →+* T` embeds finite
polynomials in the distinguished variable; regrouping its image yields
the original polynomial. `restrictedFirst_actual_support_iff` characterizes
its unique bounded-degree representation by vanishing of coefficients at
all exponents above the bound, including degree zero and the zero ring.

`restrictedRenameEquiv I e` transports restricted series across a variable
bijection. For `Fin (n + 1)`, `restrictedFinSuccEquiv I n` converts to
`Option (Fin n)` variables. The resulting coefficient, regrouping, polynomial
and bounded-support laws work when `n = 0`; no equivalence between all
iterated restricted series and restricted series is asserted.

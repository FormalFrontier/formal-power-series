<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- Authors: Formal Frontier Agents -->

# Cofinal ideal-adic filtrations of modules

Import `FormalPowerSeries.AdicCompletion.Cofinal`. For **any** commutative ring
`R`, additive commutative group `M` with `[Module R M]`, ideals `I ≤ J`, and
`N : ℕ` with `1 ≤ N` and `J ^ N ≤ I`, the global public theorems
`isHausdorff_iff_of_cofinal`, `isPrecomplete_iff_of_cofinal` and
`isAdicComplete_iff_of_cofinal` compare the corresponding predicates for
`I` and `J` on `M`. They assume neither finite generation nor Noetherianity.

The inclusions `I ^ n • ⊤ ≤ J ^ n • ⊤` and
`J ^ (N * n) • ⊤ ≤ I ^ n • ⊤` give both directions: reindex a Cauchy
sequence by `N * n` when necessary, and transfer the levelwise congruences.
This is a generic, separately importable support leaf, not a theorem only
about multivariate series or an order-ideal completion. For the distinct
restrictedness comparison of *series* see
[`MvPowerSeries.IdealAdicRestricted.Cofinal`](../MvPowerSeries/IdealAdicRestricted/Cofinal.lean).

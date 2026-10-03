# Units of ideal-adically restricted power series

SPDX-License-Identifier: Apache-2.0

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.UnitDetection`.
For any variable type `σ`, commutative ring `R`, ideal `I : Ideal R`, and
`[IsAdicComplete I R]`, let
`T := MvPowerSeries.adicallyRestrictedSubring (σ := σ) I`. The following
results detect units **inside `T`**, not merely inside the unrestricted
power-series ring:

| Use | Declaration in `MvPowerSeries` |
| --- | --- |
| A restricted series is a unit iff its first polynomial reduction is a unit | `isUnit_adicallyRestricted_iff_adicReduction_one I f` |
| Equivalently, the constant coefficient modulo `I` is a unit and every nonconstant coefficient modulo `I` is nilpotent | `isUnit_adicallyRestricted_iff_coeff_mod_ideal I f` |
| A coefficient is a unit iff its image in `R ⧸ I` is a unit | `isUnit_iff_quotient_of_isAdicComplete I r` |
| Equivalently, the actual constant coefficient is a unit and all nonconstant coefficients belong to `I.radical` | `isUnit_adicallyRestricted_iff_coeff_radical I f` |

In particular, the first criterion uses `adicReduction I 1 f` in
`MvPolynomial σ (R ⧸ I ^ 1)`, whereas the coefficient criteria use the
quotient by `I`; the proof transports these via `I ^ 1 = I`.
No finite-variable, finite-generation, domain, nontriviality, valuation or
intrinsic restricted-ring ideal-power assumption is needed.

The converse lifts an inverse polynomial using `adicReduction_surjective`.
The resulting error `1 - f*g` raises the coefficientwise reduction
filtration by `adicReduction_mul_eq_zero`; `restrictedGeometricInverse`
then yields an inverse **in `T`**. The scalar unit criterion uses adic
completeness and the Jacobson-radical criterion.

The [ordinary-import client](../../../../Tests/MvPowerSeries/IdealAdicRestricted/UnitDetection.lean)
exercises arbitrary ideals and variable types, empty and infinite variables,
the zero ideal and the zero ring. Its `ZMod 4` example demonstrates an
existing polynomial-unit inclusion with a nonzero nilpotent linear
coefficient; it does **not** exercise the coefficient criterion in
that nonvacuous case. The direct mod-`I` criterion client uses empty variables.

These results provide no incomplete-base Jacobson-radical criterion, preparation
theorem, norm/radius restriction or source-specific coverage. Formal Frontier
AI contributors developed the criteria, their formal proofs, client and guide;
mathlib's polynomial-unit and adic-completeness results retain their
respective authorship and license.

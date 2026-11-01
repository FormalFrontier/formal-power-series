<!-- SPDX-License-Identifier: Apache-2.0 -->

# Restricted series and polynomial adic completion

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.InverseLimit`.
Let `R` be any commutative ring, `I : Ideal R`, and `σ` any variable type,
in a universe independent of `R`. Write

- `S = MvPolynomial σ R`, `J = I.map (algebraMap R S)`;
- `A = AdicCompletion I R`, `B = AdicCompletion J S`;
- `q n = (AdicCompletion.evalₐ I n).toRingHom`.

Then `MvPolynomial.adicCompletionEquiv σ I` identifies `B` with
`MvPowerSeries.polynomialReductionSubalgebra σ q` as `A`-algebras.
The target consists of series whose coefficientwise image under **each original
quotient evaluation** is a polynomial, equivalently has finite coefficient
support. The finite support may depend on the precision.

No finite-generation, Noetherian, completeness, separation, proper-ideal,
nontriviality or finite-variable hypothesis is imposed. In particular, this
condition is not replaced by restriction for powers of the image ideal in `A`.
No intrinsic completeness assertion for `A` or `B` is made.

## Scalar structures

The source has its stock ring structure and the exact named algebra
`AdicCompletion.extendedAlgebra I`. Its algebra map is completion of the
original coefficient map `R → S`. This is an opt-in value, not a global
instance. To write source algebra-map expressions, use a limited section:

```lean
universe u v

section
attribute [local instance] AdicCompletion.extendedAlgebra

example {R : Type u} [CommRing R] (σ : Type v) (I : Ideal R)
    (a : AdicCompletion I R) :
    (MvPolynomial.adicCompletionEquiv σ I
      (algebraMap (AdicCompletion I R)
        (AdicCompletion (I.map (algebraMap R (MvPolynomial σ R)))
          (MvPolynomial σ R)) a)).val = MvPowerSeries.C a :=
  MvPolynomial.adicCompletionEquiv_algebraMap I a
end
```

The target retains its ordinary coefficient-`A` subalgebra structure.
Importing the module does not register the named source algebra globally or
replace any pre-existing coefficient algebra on other completions.

## Coefficients and reductions

For a completed polynomial `x`, `coeff_adicCompletionEquiv I x d` states
that its degree-`d` series coefficient is

```lean
AdicCompletion.map I (MvPolynomial.lcoeff R d)
  (AdicCompletion.restrictScalarsEquiv I (MvPolynomial σ R) x)
```

The underlying linear equivalence is the canonical restriction-of-scalars
comparison, completion of the polynomial coefficient linear equivalence, and
the **whole** `AdicCompletion.dfinsuppEquiv`. Identifying its restricted product
with the target series subalgebra only normalizes equal-ideal quotients.
Its inverse is reused, not reconstructed from another compatible-row carrier.
The producer's completed scalar compatibility supplies linearity over `A`.

- `adicPolynomialLevelEquiv I n` identifies `S ⧸ J ^ n` with
  `MvPolynomial σ (R ⧸ I ^ n)`. It uses Mathlib's polynomial quotient
  equivalence and `Ideal.map_pow`.
- `adicPolynomialLevelEquiv_mk I n p` reduces the original coefficients of `p`.
- `adicPolynomialLevelEquiv_factorPow I hmn x` and
  `adicReduction_factorPow I hmn f` commute with the quotient-power transitions.
- `MvPolynomial.polynomialReduction_adicCompletionEquiv I n x` identifies
  the target finite reduction with
  `adicPolynomialLevelEquiv I n (AdicCompletion.evalₐ J n x)`.
- `MvPolynomial.adicCompletionEquiv_symm_eval` characterizes the inverse
  at every quotient precision; `adicCompletionEquiv_symm_coeff` characterizes
  all its completed coefficient projections. The usual `AlgEquiv` inverse
  laws apply without unfolding the implementation.
- `MvPolynomial.adicCompletionEquiv_of I p` sends an original polynomial
  representative to its usual power series after coefficientwise completion.
- `MvPolynomial.adicCompletionEquiv_symm_polynomial I p` identifies the inverse
  on polynomials over `A` with stock `MvPolynomial.aeval` at the completed
  original variables, using the exact named source algebra.
- `MvPolynomial.adicCompletionEquiv_algebraMap I a` sends the completed
  coefficient map to the power-series constant `C a`.

All level laws include `n = 0`, whose quotient is the zero ring. The reduced
polynomial support is then empty. Multiplication is verified through all these
ring-hom reductions and joint injectivity of the original coefficient evaluations,
not through intrinsic completeness of the completed coefficient ring.

## Complete original coefficients

With `[IsAdicComplete I R]`, the original public ring equivalence remains

```lean
MvPowerSeries.adicallyRestrictedEquivAdicCompletion (σ := σ) I :
  MvPowerSeries.adicallyRestrictedSubring (σ := σ) I ≃+*
    AdicCompletion
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
      (MvPolynomial σ R)
```

It is coefficientwise transport by `AdicCompletion.ofAlgEquiv I`, followed
by the inverse of `MvPolynomial.adicCompletionEquiv σ I`.
`AdicCompletion.mk_ofAlgEquiv_symm` identifies its raw coefficient reductions
with ideal-power reductions. Thus there is only one underlying coefficient
completion comparison.

`MvPowerSeries.adicCompletionEquiv_adicallyRestrictedEquivAdicCompletion`
expresses this agreement on ambient series. The original forward and inverse
`_eval`, `_symm_eval`, and `_polynomial` laws are unchanged, as are the
completeness-free polynomial level API and its transition laws. Existing
linear-extension applications continue to use the original ring equivalence.

The [ordinary-import client](../../../../FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/InverseLimit.lean)
uses the inverse on a scalar-variable polynomial with an arbitrary completed
coefficient, without original-coefficient completeness. It also retains the
finite-level and polynomial checks for arbitrary, empty and infinite variable
types, zero precision, and complete coefficient rings with zero divisors.

## Build and scope

The root `lake-manifest.json` pins Mathlib, AdicModules and the shared polynomial
and coherent-module dependencies. With the pinned Lean toolchain:

```sh
lake exe cache get
lake build FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.InverseLimit
lake build FormalPowerSeriesTests.MvPowerSeries.IdealAdicRestricted.InverseLimit
```

Both modules are reached from the default library and test roots. The equivalences
do not assert general coefficient base change, arbitrary series renaming,
norm/radius-weighted or variable-adic restriction, intrinsic restricted-ring
completeness, preparation or division. Source-specific correspondence is outside
this independent library.

## Provenance

Mathlib supplies polynomial quotient transport, coefficient linear equivalences,
adic completion, the completion functor, completed scalar actions and
`AdicCompletion.ofAlgEquiv`. AdicModules supplies its full dependent-direct-sum
completion comparison and inverse, restriction of scalars and the completed
coefficient map with its named algebra. The polynomial-reduction subalgebra and
finite reductions are the existing construction of this library. Mathlib and
AdicModules retain their authorship and licenses; see [credits](../../../../CREDITS.md).
The restricted-series foundation, original complete-coefficient application,
and completed-coefficient generalization were developed by distinct Formal
Frontier AI contributors. No source-specific coverage is claimed.

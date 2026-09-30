<!-- SPDX-License-Identifier: Apache-2.0 -->

# Restricted series and polynomial adic completion

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.InverseLimit`.
For an arbitrary variable type `σ`, a commutative ring `R`, an ideal
`I : Ideal R`, and `[IsAdicComplete I R]`, the canonical ring equivalence

```lean
MvPowerSeries.adicallyRestrictedEquivAdicCompletion (σ := σ) I :
  MvPowerSeries.adicallyRestrictedSubring (σ := σ) I ≃+*
    AdicCompletion
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
      (MvPolynomial σ R)
```

identifies coefficientwise restricted series with the **native** completion of
polynomials at the coefficient-generated ideal. `IsAdicComplete` means both
precompleteness and Hausdorffness for the coefficient ring; no finite-generation,
Noetherian, domain, nontriviality, proper-ideal, finite-variable or countability
condition is imposed. This result is canonical **as characterized by the laws
below**; it does not assert base-change naturality.

## Exact level laws

- `adicPolynomialLevelEquiv I n` identifies the quotient of polynomials by
  `(I.map MvPolynomial.C) ^ n` with polynomials over `R ⧸ I ^ n`; it composes
  the inverse of the native `MvPolynomial.quotientEquivQuotientMvPolynomial`
  with quotient transport across `Ideal.map_pow`.
- `adicPolynomialLevelEquiv_mk I n p` sends the quotient class of `p` to
  `MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) p`.
- `adicPolynomialLevelEquiv_factorPow I hmn x` states the square for the
  **actual** `Ideal.Quotient.factorPow` transitions, at any `m ≤ n`.
- `adicReduction_factorPow I hmn f` commutes finite reductions with
  `MvPolynomial.map (Ideal.Quotient.factorPow I hmn)`.
- `adicallyRestrictedEquivAdicCompletion_eval I n f` identifies the forward
  completion evaluation, after `adicPolynomialLevelEquiv`, **exactly** with
  `MvPowerSeries.adicReduction I n f`.
- `adicallyRestrictedEquivAdicCompletion_symm_eval I n x` identifies the
  finite reduction of the inverse image with the same native evaluation.
- `adicallyRestrictedEquivAdicCompletion_polynomial I p` sends
  `polynomialToRestricted I p` to `AdicCompletion.of _ _ p`.

The inverse reconstructs each coefficient from a compatible native coefficient
completion, using `AdicCompletion.ofAlgEquiv I` and its inverse. At **each
fixed** level the finite exceptional set of *monomial indices* is precisely
the support of the resulting quotient polynomial. Those supports need not
admit a uniform finite bound across levels. Native `evalₐ` handles quotients
by `I ^ n • ⊤`; the proof transports them explicitly to quotients by `I ^ n`.
The transition and representative laws hold at `n = 0` as well: the level-zero
quotient is the zero ring.

For example, the following works even if `σ` is infinite:

```lean
example {σ R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (p : MvPolynomial σ R) :
    MvPowerSeries.adicallyRestrictedEquivAdicCompletion I
        (MvPowerSeries.polynomialToRestricted I p) =
      AdicCompletion.of
        (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R) p :=
  MvPowerSeries.adicallyRestrictedEquivAdicCompletion_polynomial I p
```

The [ordinary-import client](../../../../Tests/MvPowerSeries/IdealAdicRestricted/InverseLimit.lean)
tests both evaluation directions, polynomial
representatives, identity and composition of level transitions, level zero,
empty and infinite variable types, and the bottom-ideal complete ring
`ZMod 6` (whose nonzero classes `2` and `3` multiply to zero). For `I = ⊤`,
coefficient completeness forces a subsingleton ring; the client tests the
zero ring `ZMod 1`, not a nonexistent complete nonzero-ring instance.

## Reproduction and scope

From the repository root with pinned `lake-manifest.json`, Lean `v4.34.0-rc2`
and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`:

```sh
lake exe cache get
lake build FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.InverseLimit
lake build Tests.MvPowerSeries.IdealAdicRestricted.InverseLimit
```

Fetch the matching precompiled mathlib cache **before** either build. Both
modules set `warningAsError` and are imported by the `FormalPowerSeries` and
`Tests` roots, respectively. This equivalence makes no assertion of
arbitrary-ideal internal restricted kernels, restricted-subring adic or
topological completeness, completion completeness at non-finitely-generated
ideals, base-change functoriality, variable-adic equivalence, preparation or
division. Source-specific correspondence is outside this independent library.

## Provenance

The construction reuses native mathlib `Ideal.map_pow`, quotient transports,
`MvPolynomial.quotientEquivQuotientMvPolynomial`, `AdicCompletion.liftRingHom`,
`AdicCompletion.ofAlgEquiv`, `AdicCompletion.ext_evalₐ`, and the earlier
restricted-series finite-reduction API; it introduces no competing quotient or
inverse-limit framework. Native mathlib retains its authorship and license.
The underlying restricted-series API and this inverse-limit proof, client
and guide were developed by distinct Formal Frontier AI contributors in the
shared incubator. This relocation preserves their proof work and does not
claim new proofs of the native mathlib results, a newly established source
correspondence or whole-source coverage. Anchor is responsible for the
restricted-series contribution; see [repository metadata](../../../../formalization.yaml)
for license and source context.

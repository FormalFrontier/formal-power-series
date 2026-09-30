# Restricted multivariate series: linear polynomial quotients

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LinearQuotient`.
For `σ : Type*`, `[CommRing R]` and `I : Ideal R`, this module uses the
**existing** subring subtype
`MvPowerSeries.adicallyRestrictedSubring (σ := σ) I`. It neither constructs a
new carrier nor changes what ideal-adically restricted means: modulo each
`I ^ k`, all but finitely many *monomial-indexed* coefficients vanish.

## Public interface

- `MvPowerSeries.adicallyRestrictedAlgebra I` gives the subtype its `Algebra R`
  structure using `(polynomialToRestricted I).comp MvPolynomial.C`. This is the
  only new global scalar structure; no second `SMul` or `Module` is separately
  registered. `algebraMap_adicallyRestricted_coe`,
  `coe_smul_adicallyRestricted` and `coeff_smul_adicallyRestricted` identify
  its constants and scalar action with the native ambient constant series and
  coefficientwise action.
- `algebraAdicReduction I k` is an `R`-algebra homomorphism whose underlying
  ring homomorphism is the existing `adicReduction I k`.
  `linearAdicReduction I k` is its `AlgHom.toLinearMap`; the simp lemmas
  `linearAdicReduction_apply` and `coeff_linearAdicReduction` give its
  original value and coefficient law. `linearAdicReduction_surjective` applies
  for **every** ideal, variable type and natural-number level, including zero.
- For `a : R` and `ha : IsRegular a`, put `I := Ideal.span ({a} : Set R)`.
  `principalAdicConstant_mul_eq_smul a k f` identifies multiplication by
  the accepted restricted constant `a ^ k` with the `R`-scalar action;
  `ker_linearAdicReduction_principal a ha k` states the actual **R-submodule**
  equality `LinearMap.ker (linearAdicReduction I k) = I ^ k • ⊤`.
- `principalLinearQuotientEquiv a ha k` is the **R-linear equivalence**
  `S ⧸ (I ^ k • (⊤ : Submodule R S)) ≃ₗ[R] MvPolynomial σ (R ⧸ I ^ k)`,
  where `S := adicallyRestrictedSubring (σ := σ) I`.
  `principalLinearQuotientEquiv_mk` computes the image of a representative
  `Submodule.Quotient.mk f` as `adicReduction I k f`.
- For integer coefficients, `intLinearAdicReduction I k` bundles the same
  `adicReduction I k` via `RingHom.toAddMonoidHom.toIntLinearMap`, using the
  **native default integer module** on both sides. Its `apply`, `coeff` and
  `surjective` lemmas work for every integer ideal and every level.
  `ker_intLinearAdicReduction_principal a ha k` identifies its native
  `Submodule ℤ S` kernel with `I ^ k • ⊤`, and
  `principalIntLinearQuotientEquiv a ha k` is the corresponding native
  `S ⧸ (I ^ k • ⊤) ≃ₗ[ℤ] MvPolynomial σ (ℤ ⧸ I ^ k)`.
  `principalIntLinearQuotientEquiv_mk` computes representatives by the
  unchanged `adicReduction`. `principalAdicConstant_mul_eq_int_smul` relates
  the principal constant directly to native integer scalar multiplication.

These signatures require only `[CommRing R]`; regularity is needed only for
the principal kernel and quotient. `Ideal.span {a}` is an ideal **of `R`**;
`I ^ k • ⊤` is a submodule **of the restricted-series subtype**. The accepted
`ker_adicReduction_principal` instead computes a ring ideal of that subtype;
the new proof bridges those statements rather than identifying their types.
It uses the accepted restricted-division witness, whose quotient stays *inside*
`S`, `Ideal.span_singleton_pow`, `Submodule.ideal_span_singleton_smul`, and
`Submodule.mem_smul_pointwise_iff_exists`. The final equivalence composes
native `Submodule.quotEquivOfEq` and
`LinearMap.quotKerEquivOfSurjective`, not a ring quotient.

The canonical integer result is a separate public endpoint because the generic
`Algebra.toModule` instance and the native `AddCommGroup.toIntModule` instance
agree on scalar values but are not definitionally the same inside dependent
submodule and quotient types. Its short kernel proof reuses the accepted ring
kernel and division witness, recasting only the submodule-membership bridge
under the native action. It does not replace the generic proof or the carrier.

For example, the following declarations select the native submodule and quotient
**before** using the compatibility equivalence, without any client instance override:

```lean
import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LinearQuotient
open MvPowerSeries
open scoped Pointwise

private abbrev fourIdeal : Ideal ℤ := Ideal.span ({(4 : ℤ)} : Set ℤ)
private noncomputable abbrev fourSubmodule (k : ℕ) :
    Submodule ℤ (adicallyRestrictedSubring (σ := Fin 2) fourIdeal) :=
  fourIdeal ^ k • ⊤
private abbrev fourQuotient (k : ℕ) :=
  adicallyRestrictedSubring (σ := Fin 2) fourIdeal ⧸ fourSubmodule k
private theorem fourRegular : IsRegular (4 : ℤ) :=
  IsRegular.of_ne_zero (by decide)

example (k : ℕ) :
    LinearMap.ker (intLinearAdicReduction (σ := Fin 2) fourIdeal k) =
      fourSubmodule k :=
  ker_intLinearAdicReduction_principal 4 fourRegular k

example (f : adicallyRestrictedSubring (σ := Fin 2) fourIdeal) :
    principalIntLinearQuotientEquiv (σ := Fin 2) 4 fourRegular 2
      ((Submodule.Quotient.mk f) : fourQuotient 2) = adicReduction fourIdeal 2 f :=
  principalIntLinearQuotientEquiv_mk 4 fourRegular 2 f
```

The ordinary-import client
`Tests.MvPowerSeries.IdealAdicRestricted.LinearQuotient`
exercises arbitrary `I`, `R`, `σ`, `k`, and scalar/coefficient laws; `σ = Unit`
without any sequence transport; native integer kernel and quotient
representatives at levels `0`, `1`, `2` with regular nonunit `4 : ℤ`;
native scalar/coefficient action and a native typed quotient equivalence; and
the unchanged generic level `2` case for regular nonunit
`(2, 1) : ℤ × ℤ` (a ring with zero divisors). The original `218ecb61` client
used a private priority-2000 `Algebra.toModule` override and did **not** test
this default-client case. The accepted corrected donor removed that override;
the original failed-client logs and independent REQUEST_CHANGES verdict remain
historical evidence, not passing default-client checks.

The target is linear over `R`, not automatically bundled as linear over
`R ⧸ I ^ k`. In particular `R ⧸ I` is not generally the residue ring at
levels `k > 1`. No domain, PID, nonunit, finite residue, Noetherian,
finite-variable, positive-level or nontrivial-ring assumption is implicit.
The result covers units and the degenerate quotient. No sequence equivalence,
inverse limit, completeness, countability or nonfreeness theorem is asserted;
pointwise multiplication of sequences is not power-series convolution.

## Build and use

From this repository root, the pinned `lean-toolchain` is Lean
`v4.34.0-rc2` and `lake-manifest.json` pins mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. Fetch the matching
mathlib cache before building the new producer and ordinary-import client,
then build both aggregate roots:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake build +FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LinearQuotient +Tests.MvPowerSeries.IdealAdicRestricted.LinearQuotient
lake build FormalPowerSeries Tests
```

Both transferred modules enable `warningAsError` and are included in the
respective `FormalPowerSeries` and `Tests` roots. A dependent pinned Lake
project can import the producer directly or the `FormalPowerSeries` root;
the [API](../../../../API.md#scalar-linear-reduction-and-principal-quotients)
locates the full library interface. These commands describe reproduction,
not checks performed on this transfer. New destination build and complete
transitive axiom evidence, independent review, maintainer acceptance and
reviewed release remain pending.
That pending statement records transfer preparation earlier on 2026-09-30.
Original configured run 1343 on exact destination commit
`41aa9fa6a4244ba200fe3cdadf9ee9e4113f6540` passed a cache-first
both-root build and complete private-inclusive transitive axiom audit with
only `propext`, `Classical.choice` and `Quot.sound`. A fresh independent
reviewer approved the full destination transfer; Prism accepted its code and
integrated it into `main` on 2026-09-30 at 09:32:45 UTC. These commands remain
reproduction instructions, not a claim of a new release-candidate build.
At preparation of this release snapshot on 2026-09-30, separate release
review, protected promotion and verified GitHub publication were still
pending. Code acceptance alone does not establish those later steps or
source coverage.

## Provenance and credit

These source-independent definitions and proofs build on the existing
[restricted carrier](../README.md) and
[regular-principal division and ring kernel](../PrincipalKernel/README.md)
and native mathlib algebra, ideal, submodule and first-isomorphism APIs;
they do not re-prove or relicense those upstream contributions. Anchor is
responsible for the carrier and principal-kernel transfer. The original
linear-bridge plan was produced by a Formal Frontier worker-a contributor.
A distinct worker-a contributor authored the initial linear producer,
ordinary client and guide; an independent worker-b reviewer found the
native-default `ℤ`-module mismatch. Another worker-a contributor repaired
that mismatch with a separate integer endpoint and corrected client;
a worker-b independently approved that repair. The corrected modules were
registered by a further worker-a contributor, independently reviewed by
worker-b at the assembled candidate and accepted in the incubator in
September 2026. This destination transfer is authored by a different
worker-b execution; Prism corrected its client's destination namespace before
destination review. Its own independent review and checks are pending.
The preceding pending statement records the earlier 2026-09-30
transfer-preparation state. The corrected destination commit received the
original both-root check and fresh independent review before Prism's code
acceptance and 09:32:45 UTC integration on 2026-09-30; neither those checks
nor that acceptance constitute release approval or source coverage.

The isolated 2026-09-29 repair guide referred to a **26-package** unregistered
incubator candidate and described its checks as preliminary. Those are
historical origin facts: the registered donor is accepted at the frozen
incubator revision, whereas this destination has nine manifest
packages and adds the two roots' mapped modules without an incubator
requirement. Historical donor proof evidence is not new destination evidence.
This library makes no source-specific formalization or coverage claim.
SPDX-License-Identifier: Apache-2.0; Authors: Formal Frontier Agents.

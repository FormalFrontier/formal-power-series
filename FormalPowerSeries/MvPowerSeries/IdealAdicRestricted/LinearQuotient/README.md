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
  the restricted constant `a ^ k` with the `R`-scalar action;
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
`I ^ k • ⊤` is a submodule **of the restricted-series subtype**. The
`ker_adicReduction_principal` instead computes a ring ideal of that subtype;
the proof bridges those statements rather than identifying their types.
It uses the restricted-division witness, whose quotient stays *inside*
`S`, `Ideal.span_singleton_pow`, `Submodule.ideal_span_singleton_smul`, and
`Submodule.mem_smul_pointwise_iff_exists`. The final equivalence composes
native `Submodule.quotEquivOfEq` and
`LinearMap.quotKerEquivOfSurjective`, not a ring quotient.

The canonical integer result is a separate public endpoint because the generic
`Algebra.toModule` instance and the native `AddCommGroup.toIntModule` instance
agree on scalar values but are not definitionally the same inside dependent
submodule and quotient types. Its short kernel proof reuses the ring
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
`(2, 1) : ℤ × ℤ` (a ring with zero divisors). The client uses the native
default integer module without a priority override.

The target is linear over `R`, not automatically bundled as linear over
`R ⧸ I ^ k`. In particular `R ⧸ I` is not generally the residue ring at
levels `k > 1`. No domain, PID, nonunit, finite residue, Noetherian,
finite-variable, positive-level or nontrivial-ring assumption is implicit.
The result covers units and the degenerate quotient. No sequence equivalence,
inverse limit, completeness, countability or nonfreeness theorem is asserted;
pointwise multiplication of sequences is not power-series convolution.

## Build and use

From the repository root, `lean-toolchain` pins Lean `v4.34.0-rc2` and
`lake-manifest.json` pins mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`.
Fetch its precompiled cache successfully before either build:

```sh
lake exe cache get
lake build FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LinearQuotient \
  Tests.MvPowerSeries.IdealAdicRestricted.LinearQuotient
lake build FormalPowerSeries Tests
```

Both modules enable `warningAsError` and are included in the two roots.
A dependent pinned Lake project can import this producer or the root;
[API.md](../../../../API.md#scalar-linear-reduction-and-principal-quotients)
locates the full interface. See the [root build guidance](../../../../README.md#build-and-use)
for cache-first setup and selective-module build instructions.

## Provenance and credit

These source-independent definitions and proofs build on the
[restricted carrier](../README.md),
[regular-principal division and ring kernel](../PrincipalKernel/README.md)
and native mathlib algebra, ideal, submodule and first-isomorphism APIs.
Formal Frontier AI contributors authored the linear-bridge design, original
producer, ordinary-import client and guide; a separate contribution repaired
the native-default `ℤ`-module mismatch with the integer endpoint. Later
contributors adapted and assembled the modules here, including Prism's
client namespace correction. Relocation does not erase original authorship
or transfer credit for mathlib's native methods. Original project files are
Apache-2.0 (Authors: Formal Frontier Agents); mathlib remains separately
licensed. This library makes no source-specific coverage claim.

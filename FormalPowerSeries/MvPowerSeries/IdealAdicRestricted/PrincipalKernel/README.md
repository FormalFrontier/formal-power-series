# Regular-principal kernels for restricted power-series reduction

SPDX-License-Identifier: Apache-2.0

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.PrincipalKernel`.
Let `σ : Type*`, `[CommRing R]`, `a : R`, `ha : IsRegular a`,
`I = Ideal.span ({a} : Set R)`, and `k : ℕ`. The existing
`MvPowerSeries.adicallyRestrictedSubring (σ := σ) I` consists of full series
`f` for which the set of **monomial indices**

```lean
{m : σ →₀ ℕ | MvPowerSeries.coeff m f ∉ I ^ l}
```

is finite for every `l : ℕ`. This is not a finiteness assertion about the set
of distinct coefficient values. Its existing `adicReduction I k` is a
surjective ring homomorphism to `MvPolynomial σ (R ⧸ I ^ k)`.

## Kernel and quotient witness

`principalAdicConstant (σ := σ) a k` is the element of the *restricted
subring* obtained by including `MvPolynomial.C (a ^ k)`. The new API is:

```lean
-- In namespace MvPowerSeries, with {σ R : Type*} [CommRing R]:
theorem exists_restricted_principal_quotient (a : R) (ha : IsRegular a)
    (k : ℕ) (f : adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R)))
    (hf : ∀ m : σ →₀ ℕ,
      coeff m (f : MvPowerSeries σ R) ∈ (Ideal.span ({a} : Set R)) ^ k) :
    ∃ g : adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R)),
      f = principalAdicConstant (σ := σ) a k * g

theorem ker_adicReduction_principal (a : R) (ha : IsRegular a) (k : ℕ) :
    RingHom.ker (adicReduction (σ := σ) (Ideal.span ({a} : Set R)) k) =
      Ideal.span ({principalAdicConstant (σ := σ) a k} :
        Set (adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R))))
```

Here `I` abbreviates `Ideal.span ({a} : Set R)`. The first
result produces `g` **inside the restricted subring**, not just an ambient
power-series quotient. At level `l`, the proof identifies the exceptional
monomial-index set of `g` as a subset of the finite exceptional set of `f` at
level `k + l`. It uses regularity of `a ^ k` for cancellation, even when a
coefficient is zero. The second result identifies the kernel of the *existing*
polynomial-valued map via its public coefficient formula and proves both ideal
inclusions inside the restricted subring.

For example, the integer case can directly invoke the witness:

```lean
example (a : ℤ) (ha : IsRegular a) (k : ℕ)
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := Fin 2)
      (Ideal.span ({a} : Set ℤ)))
    (hf : ∀ m : Fin 2 →₀ ℕ,
      MvPowerSeries.coeff m (f : MvPowerSeries (Fin 2) ℤ) ∈
        (Ideal.span ({a} : Set ℤ)) ^ k) :
    ∃ g : MvPowerSeries.adicallyRestrictedSubring (σ := Fin 2)
      (Ideal.span ({a} : Set ℤ)),
      f = MvPowerSeries.principalAdicConstant a k * g :=
  MvPowerSeries.exists_restricted_principal_quotient a ha k f hf
```

For the quotient by this principal ideal, rewrite with
`ker_adicReduction_principal` and then apply native
`RingHom.quotientKerEquivOfSurjective` to
`adicReduction_surjective I k`. Its native
`RingHom.quotientKerEquivOfSurjective_apply_mk` says the image of the
representative `[f]` is exactly `adicReduction I k f`. This avoids a redundant
first-isomorphism implementation; the ordinary-import private client tests the
quotient and representative law.

The statements hold for `k = 0`, units, zero coefficient rings (including a
regular zero), empty or infinite variable types, and regular nonunits in rings
with zero divisors, such as `(2, 1) : ℤ × ℤ`. They do not assert regularity of
zero in a nontrivial ring. No domain, `Nontrivial`, Noetherian, completeness,
finite-variable, proper-ideal, or positive-level assumption is imposed. No
arbitrary-ideal kernel, coefficient-map naturality, preparation/division, new
topology, or source-specific coverage is claimed here. The separate
[inverse-limit module](../InverseLimit/README.md) assumes coefficient adic
completeness rather than regularity of a generator.

## Reproduction and status

Use the repository's pinned Lean `v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, and unchanged ordered Lake
manifest. Fetch the matching mathlib cache **before** building:

```sh
lake exe cache get
lake build FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.PrincipalKernel \
  Tests.MvPowerSeries.IdealAdicRestricted.PrincipalKernel
```

Both modules enable `warningAsError`; the corresponding private client is
[`Tests/MvPowerSeries/IdealAdicRestricted/PrincipalKernel.lean`](../../../../Tests/MvPowerSeries/IdealAdicRestricted/PrincipalKernel.lean).
The `FormalPowerSeries` and `Tests` roots import the producer and client.

## Provenance

The preceding finite-reduction API and this regular-principal proof were
developed by distinct Formal Frontier AI contributors in the shared incubator.
This transfer preserves their mathematical work. Native mathlib supplies
`Ideal.span_singleton_pow`,
`Ideal.mem_span_singleton'`, `IsRegular.pow`, `MvPowerSeries.coeff_C_mul`,
`Ideal.Quotient.eq_zero_iff_mem`, and the native first-isomorphism theorem;
their respective native authors retain their credit. The original AI-developed
proof, ordinary-import client and guide are not newly proved by their relocation.
See [repository metadata](../../../../formalization.yaml) for license and
source context; no source-specific correspondence is asserted here.

# Finitely generated restricted-series reduction kernels

SPDX-License-Identifier: Apache-2.0

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.FinitelyGeneratedKernel`
(or `FormalPowerSeries`). For `[CommRing R]`, `[Finite σ]`, `I : Ideal R`,
`hI : I.FG` and **every** `k : ℕ`, the public theorem
`MvPowerSeries.ker_adicReduction_fg I hI k` identifies the kernel as

```lean
RingHom.ker (MvPowerSeries.adicReduction (σ := σ) I k) =
  Ideal.map ((MvPowerSeries.polynomialToRestricted (σ := σ) I).comp MvPolynomial.C)
    (I ^ k)
```

This is an **algebraic ideal inside**
`MvPowerSeries.adicallyRestrictedSubring (σ := σ) I`, not an ambient-series
ideal or its topological closure. Reduction lands surjectively in
`MvPolynomial σ (R ⧸ I ^ k)`; the supporting public theorem
`MvPowerSeries.exists_restricted_fg_decomposition I hI k f hf` takes a
restricted `f` with all coefficients in `I ^ k` and returns finite constants
`v j ∈ I ^ k` and restricted `g j` such that

```lean
f = ∑ j, MvPowerSeries.polynomialToRestricted I (MvPolynomial.C (v j)) * g j
```

For example, the kernel identification turns a zero reduction into an
*intrinsic* algebraic ideal membership:

```lean
example {σ R : Type*} [CommRing R] [Finite σ]
    (I : Ideal R) (hI : I.FG) (k : ℕ)
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I)
    (hf : MvPowerSeries.adicReduction I k f = 0) :
    f ∈ Ideal.map ((MvPowerSeries.polynomialToRestricted I).comp MvPolynomial.C)
      (I ^ k) := by
  rw [← MvPowerSeries.ker_adicReduction_fg I hI k]
  exact (RingHom.mem_ker).2 hf
```

The proof chooses a finite spanning family of `I ^ k`. At each monomial
index it decomposes the coefficient into those constants times coefficients
in a bounded ideal power. Finite-variable bounded-degree finiteness and the
original restrictedness ensure that the assembled coefficient series remain
restricted, without cancelling any generator. No completeness, separation,
Noetherianity, domain, valuation, regularity, `Nontrivial`, proper-ideal,
positive-level or nonempty-variable assumption is needed. The
[ordinary-import client](../../../../Tests/MvPowerSeries/IdealAdicRestricted/FinitelyGeneratedKernel.lean)
checks finite decomposition, ideal membership, a quotient-ring equivalence,
`k = 0`, zero/top ideals, empty variables, the zero ring and the nonregular
`2 : ZMod 4` case. Its quotient equivalence is a private client, not an
additional public API. The separate [regular-principal kernel](../PrincipalKernel/README.md)
works even for infinite variables; neither result replaces the other. There
is no general division, normal form, completion-exactness or preparation
assertion here.

From the repository root, keep the pinned `lean-toolchain` and manifest;
fetch the matching precompiled mathlib cache successfully before building:

```sh
lake exe cache get
lake build FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.FinitelyGeneratedKernel
lake build Tests.MvPowerSeries.IdealAdicRestricted.FinitelyGeneratedKernel
```

Both modules enable `warningAsError`; the [repository README](../../../../README.md#build-and-use)
has unvalidated time/memory/disk planning estimates for the library, not
measurements for these new leaves or proof that an 8 GiB machine suffices.
The finite ideal-smul/span, `Nat.findGreatest`, `Ideal.FG.pow` and
bounded-degree tools are native mathlib APIs. Different Formal Frontier
contributors wrote and independently reviewed the original mathematical
argument, implemented its Lean theorem and ordinary-import clients, and
later transferred the accepted code to this source-independent library.
That attribution does not imply source-specific coverage.

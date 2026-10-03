# Degree cutoffs for restricted multivariate series

SPDX-License-Identifier: Apache-2.0

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.DegreeDecay` (or
`FormalPowerSeries`). For `[CommRing R]`, `[Finite σ]`, `I : Ideal R` and
`f : MvPowerSeries σ R`, the public theorem
`MvPowerSeries.isAdicallyRestricted_iff_degree_cutoff I f` states

```lean
MvPowerSeries.IsAdicallyRestricted I f ↔
  ∀ k : ℕ, ∃ d : ℕ, ∀ m : σ →₀ ℕ,
    d ≤ m.degree → MvPowerSeries.coeff m f ∈ I ^ k
```

The cutoff may depend on `k`; `m.degree` is the sum of monomial exponents.
Restrictedness means **finitely many exceptional indices** at each level, not
finitely many distinct coefficient values. The proof bounds the degrees of the
finite exceptional set for the forward implication, without using finite `σ`.
The converse uses finite `σ` to make the set of bounded-degree indices finite;
the forward helper is private and not an arbitrary-variable public theorem.

```lean
example {σ R : Type*} [CommRing R] [Finite σ]
    (I : Ideal R) (f : MvPowerSeries σ R)
    (hf : MvPowerSeries.IsAdicallyRestricted I f) :
    ∀ k : ℕ, ∃ d : ℕ, ∀ m : σ →₀ ℕ,
      d ≤ m.degree → MvPowerSeries.coeff m f ∈ I ^ k :=
  (MvPowerSeries.isAdicallyRestricted_iff_degree_cutoff I f).mp hf
```

No domain, valuation, norm, Noetherianity, completeness, proper-ideal,
nonzero-ring, nonempty-variable or positive-level hypothesis is needed.
The [ordinary-import client](../../../../Tests/MvPowerSeries/IdealAdicRestricted/DegreeDecay.lean)
checks both directions, `k = 0`, empty variables, the top ideal and polynomials.
It also contains a **formal counterexample** to the converse for infinite `σ`:
over `ℤ` at the zero ideal, the series with coefficient one at every variable
monomial and zero elsewhere has cutoff `d = 2` at every level but infinitely
many exceptional degree-one indices. Do not use the equivalence without
`[Finite σ]`.

From the repository root, use `lean-toolchain` and the pinned manifest; first
fetch the matching precompiled mathlib cache successfully, then build:

```sh
lake exe cache get
lake build FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.DegreeDecay
lake build Tests.MvPowerSeries.IdealAdicRestricted.DegreeDecay
```

These modules use `warningAsError`. The repository [README](../../../../README.md#build-and-use)
gives cache-first build guidance and selective-module reproduction instructions.
The argument uses mathlib's native `Finsupp.degree` and
`Finsupp.finite_of_degree_lt` (whose contributors include Antoine
Chambert-Loir and María Inés de Frutos-Fernández), not copied proofs.
Formal Frontier contributors developed the finite-variable criterion and the
separate infinite-variable regression; a later contributor moved them into
this source-independent API. This does not assert source coverage.

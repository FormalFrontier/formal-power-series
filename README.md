# Formal power series

A Lean library with two independent families: the **weighted negative logarithmic
derivative** of native single-variable power-series units over an arbitrary
commutative ring `R`, and coefficientwise **ideal-adically restricted native
multivariate power series**:

```lean
PowerSeries.negXLogDeriv (f : (PowerSeries R)ˣ) =
  -PowerSeries.X * PowerSeries.derivative (f : PowerSeries R) *
    ((f⁻¹ : (PowerSeries R)ˣ) : PowerSeries R)
```

The multivariate family works with finite exceptional *monomial indices* at
each ideal power, not a finite set of coefficient values. Its basic construction
allows arbitrary variable types and ideals; stronger hypotheses are stated
separately for internal principal division and coefficient completeness. Under
`[IsAdicComplete I R]`, **every `R`-linear polynomial endomorphism extends
to an `R`-linear operator on restricted series**, with finite-level equations
and a uniqueness theorem requiring both polynomial agreement and preservation
of every coefficientwise reduction kernel. Neither family imports or
mathematically depends on the other.

## Headline results

### Weighted unit derivative

- **Products become sums, naturally in the coefficient ring.** Over any
  commutative ring, `PowerSeries.negXLogDeriv` takes multiplication of native
  units to addition, inverses to negatives and integer powers to integer
  multiples. It commutes with arbitrary coefficient-ring homomorphisms, also
  between different universes, and bundles as a homomorphism from the unit
  group written additively. For a supplied unit `f`, the equation
  `g * f = -X * f'` characterizes `g = negXLogDeriv f` without normalizing its
  constant coefficient. See the [definition](FormalPowerSeries/UnitLogDerivative.lean#L27),
  [laws](FormalPowerSeries/UnitLogDerivative.lean#L39),
  [naturality](FormalPowerSeries/UnitLogDerivative.lean#L81) and
  [characterization](FormalPowerSeries/UnitLogDerivative.lean#L98).
- **Integral coefficient formulas.** A finite convolution identity works for
  every native unit, including nonnormalized ones. If the constant coefficient
  is one, a **forward** recurrence determines each next coefficient of the
  weighted derivative from the coefficients of `f` and preceding derivative
  coefficients, without division by positive integers. Thus torsion and zero
  rings are allowed; this does not reconstruct `f` from its derivative. See
  [convolution](FormalPowerSeries/UnitLogDerivative.lean#L115) and
  [recurrence](FormalPowerSeries/UnitLogDerivative.lean#L124).
- **Linear factors and finite signed products.** `oneSubCXUnit a` represents
  `1 - C a * X` for every `a`; its inverse has coefficient `a^n` in degree
  `n`, and its weighted derivative has coefficient `a^(n+1)` in degree `n+1`.
  The product and integer-power laws yield a signed power-sum formula for
  finite products of these factors, including inverse factors and the empty
  family. The [signed-product example](Tests/UnitLogDerivative.lean#L127) is a
  client in the `Tests` root, not a theorem splitting arbitrary units. See the
  [factor](FormalPowerSeries/UnitLogDerivative.lean#L139) and
  [coefficient formula](FormalPowerSeries/UnitLogDerivative.lean#L160).

This is weighted by **negative `X`**, not an unweighted analytic logarithmic
derivative or a formal logarithm. Constant units lie in its kernel; under
`[CharP R p]` for any natural `p`, so do `p`-th powers. Even a normalized
nonidentity unit can lie in the kernel, as the
[characteristic-two client](Tests/UnitLogDerivative.lean#L96) shows.
For `a_n = coeff n f` and `b_n = coeff n (negXLogDeriv f)`, the unnormalized
identity is `∑ (i,j) ∈ antidiagonal (n+1), b_i * a_j = -(a_(n+1) * (n+1))`.
**Only if** `a_0 = 1`, the forward recurrence is
`b_(n+1) + ∑ i ∈ range n, a_(i+1) * b_(n-i) = -(a_(n+1) * (n+1))`.
See [API.md](API.md) for the conventions; the pin-specific `derivative_map`
helper remains private, not a separate derivative API. There is no lambda/Witt
structure, splitting extension or Adams operation here.

### Ideal-adically restricted multivariate series

- **Finite-index reduction.** For any variable type `σ`, commutative ring
  `R` and ideal `I`, `IsAdicallyRestricted I f` requires that at each `k : ℕ`,
  only finitely many monomial indices have coefficients outside `I ^ k`.
  A polynomial-range characterization yields a restricted subring and a
  **surjective** ring homomorphism
  `adicReduction I k : _ →+* MvPolynomial σ (R ⧸ I ^ k)`, including at `k = 0`.
  See the [predicate](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted.lean#L25),
  [polynomial characterization](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted.lean#L67),
  [reduction](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted.lean#L133)
  and [finite-reduction guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/README.md).
- **Regular-principal internal kernel.** When `I = Ideal.span {a}` and
  `ha : IsRegular a`, coefficientwise division by `a ^ k` constructs the
  quotient *inside the restricted subring*. The kernel of `adicReduction I k`
  is the ideal generated there by the restricted constant `a ^ k`. This is
  not arbitrary-ideal internal division. See the
  [division theorem](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/PrincipalKernel.lean#L38),
  [kernel theorem](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/PrincipalKernel.lean#L82)
  and [kernel guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/PrincipalKernel/README.md).
- **Scalar-linear polynomial quotients.** The existing restricted subring has
  an `R`-algebra structure, and reduction to `MvPolynomial σ (R ⧸ I ^ k)` is
  surjective and `R`-linear for every ideal, variable type and level, including
  `k = 0`. For a regular principal generator `a`, its **submodule** kernel is
  `I ^ k • ⊤`, yielding an `R`-linear equivalence from the corresponding
  module quotient; it is not a ring-quotient equivalence. A separate native
  integer endpoint supports default `ℤ`-module quotient types without a
  priority override. See the [linear quotient module](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/LinearQuotient.lean),
  [guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/LinearQuotient/README.md)
  and [ordinary-import client](Tests/MvPowerSeries/IdealAdicRestricted/LinearQuotient.lean).
- **Polynomial adic-completion equivalence.** With actual coefficient
  completeness `[IsAdicComplete I R]`,
  `adicallyRestrictedEquivAdicCompletion I` is a ring equivalence between
  the restricted subring and native
  `AdicCompletion (I.map MvPolynomial.C) (MvPolynomial σ R)`. It preserves
  finite-level evaluation and polynomial inclusion. Neither finite variables
  nor finite generation of `I` is assumed; completeness of arbitrary
  non-finitely-generated polynomial completions is **not** asserted. See the
  [equivalence](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/InverseLimit.lean#L270),
  [evaluation](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/InverseLimit.lean#L280)
  and [completion guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/InverseLimit/README.md).

- **Generic linear extension.** Over `[CommRing R]` and `[IsAdicComplete I R]`,
  `restrictedLinearExtension I F` extends any polynomial `R`-linear endomorphism
  `F`, for arbitrary variable type and ideal. The quotient-polynomial operator
  commutes with reductions and level transitions; the extension preserves
  each coefficientwise reduction kernel and agrees on polynomials. Its
  uniqueness assumes **both** polynomial agreement and all-level kernel
  preservation. Finite polynomial levels keep its output restricted; no
  finite-variable, Noetherian, domain, nontriviality, intrinsic arbitrary-ideal
  kernel, or intrinsic restricted-ring completeness claim is added. See the
  [producer](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/LinearExtension.lean),
  [guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/LinearExtension/README.md)
  and [ordinary-import client](Tests/MvPowerSeries/IdealAdicRestricted/LinearExtension.lean).

The latter five results concern coefficient-adic series, not norm/radius or
variable-adic restrictions, general base change, general preparation or
arbitrary-ideal division. The two mathematical families remain independent.

## Build and use

Install `elan` and Git; `lean-toolchain` pins Lean
`leanprover/lean4:v4.34.0-rc2`, and the sole direct dependency is mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. From the repository root:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake build FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LinearExtension
LEAN_NUM_THREADS=2 lake build Tests.MvPowerSeries.IdealAdicRestricted.LinearExtension
lake build FormalPowerSeries Tests
lake build
```

The first command fetches the matching mathlib cache; the literal default
`lake build` includes the public library and all `Tests/` examples.
`LEAN_NUM_THREADS=2` limits Lean's own threads in the two selective commands;
it is **not** a global bound on concurrent Lake jobs. Historical
**unit-derivative-only** initial module/default builds on the author's
September 2026 environment processed 1,743/1,777 Lake jobs on a matching
warm cache. These are job counts for the earlier graph, **not** measurements
of the later carrier/completion graph, time or peak memory. For the prior
23-file graph, the original September 2026 strict `lean-ci` run on pinned
Lean/mathlib fetched the matching mathlib cache in **39.5 seconds**, verified
its cached Mathlib build in **6.5 seconds**, then completed
`lake build FormalPowerSeries Tests` in **10.8 seconds (1,954 Lake jobs)**.
These are command wall times from that CI runner, not isolated compiler timings
or local-machine benchmarks. The complete CI run took **2 minutes 46 seconds**
including setup, build, transitive axiom checks and artifact handling; it is
not the build command's duration. No peak RAM or disk use was measured. That
historical run predates the scalar-linear quotient and generic linear-extension
transfers and does not check either changed destination graph.

For the **current 29-file graph**, the original 2026-09-30 configured strict
CI run on the pinned Lean/mathlib inputs fetched the matching mathlib cache
(**8,892 decompressed files**) in **39.5 seconds**, verified the cached
Mathlib build in **6.3 seconds**, and completed
`lake build FormalPowerSeries Tests` in **13.8 seconds (1,958 Lake jobs)**.
These are command wall times on that CI runner, not isolated compiler timings
or desktop predictions. The **3 minutes 39 seconds** end-to-end CI run
additionally includes setup, the complete
private-inclusive transitive axiom audit and artifact handling. Compared with
the older 1,954-job run, the graph now includes both the quotient and extension
producer/client pairs and has four more Lake jobs. This comparison does not
isolate extension cost; job count alone does not measure memory demand or
general rebuild latency. Neither run measured peak RAM or disk consumption.

For planning on a typical 4-core Linux machine using this pinned graph and a
matching precompiled mathlib cache (not building mathlib from source), allow
roughly **10–50 minutes** for initial toolchain/cache setup plus the full
library-and-tests build, and **1–15 minutes** for a small library/test rebuild
with dependencies already cached. Provision approximately **16 GiB RAM and
20 GiB free disk**, with more headroom for concurrent work. These are
conservative **unvalidated planning estimates**, updated for the two-module
increment from earlier graph guidance; they are neither measured peaks nor
guaranteed sufficient limits. CPU, bandwidth, cache state and competing jobs
can change both time and resources. Fetch the matching cache before building.

Import `FormalPowerSeries` from a dependent Lake project (declare and pin this
repository and its dependencies there), or selectively import
`FormalPowerSeries.UnitLogDerivative`,
`FormalPowerSeries.MvPowerSeries.IdealAdicRestricted`,
`FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.PrincipalKernel`,
`FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LinearQuotient`, or
`FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.InverseLimit`, or
`FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LinearExtension`. The
`Tests` root imports independent [unit](Tests/UnitLogDerivative.lean),
[finite-reduction](Tests/MvPowerSeries/IdealAdicRestricted.lean),
[kernel](Tests/MvPowerSeries/IdealAdicRestricted/PrincipalKernel.lean),
[linear-quotient](Tests/MvPowerSeries/IdealAdicRestricted/LinearQuotient.lean),
[completion](Tests/MvPowerSeries/IdealAdicRestricted/InverseLimit.lean) and
[linear-extension](Tests/MvPowerSeries/IdealAdicRestricted/LinearExtension.lean)
clients. The unit client contains this example:

```lean
theorem signedExample {T : Type*} [CommRing T]
    (a : T) (n : ℕ) :
    PowerSeries.coeff (n + 1)
      (PowerSeries.negXLogDeriv (PowerSeries.oneSubCXUnit a)) = a ^ (n + 1) :=
  PowerSeries.coeff_succ_negXLogDeriv_oneSubCXUnit a n
```

See [API.md](API.md) for both public families' names, hypotheses, coefficient
conventions and guide links.

## Provenance and rights

The integral formula is related to Charles A. Weibel, *The K-book: An
Introduction to Algebraic K-theory* (2013), Section II.4 and Exercise 4.6;
this small library does **not** claim to formalize the whole section or book.
Prism developed the original derivative proof expression in a checked source
experiment in
`source-weibel-k-book` at commit `6453001fbf58cbca909037650832071c594568a6`
(accepted source main `a2857276cc6bac20a65c77306e58f077d985fa93`).
Formal Frontier's `formalization-worker-a` adapted the proofs into this
source-independent module-system API and added the standalone client and
original documentation. Folio prepared the derivative headline explanations
for this combined README; that documentation work does not replace Prism's
proof authorship or `formalization-worker-a`'s adaptation credit. The derivative
module retains the originating proof structure and code expression, rather than
attributing them to mathlib. We use mathlib's
`PowerSeries.derivative`, `invOneSubPow`, `rescale`, coefficient algebra and
ordinary tactics as dependencies, not copied mathlib declarations or proofs.
The independent restricted-series base, regular-principal and inverse-limit
proofs, ordinary-import clients and guides were developed by Formal Frontier
AI contributors in the shared incubator and transferred without changing their
public mathematical declarations. Their distinct original authors and the
transfer author are recorded in the private owning provenance; the
[three guides](API.md#ideal-adically-restricted-multivariate-series) credit
the native mathlib APIs and their authors. Anchor is responsible for the
restricted-series contribution; Prism retains derivative maintenance and shared
library responsibility. Original Formal Frontier files are licensed under
Apache-2.0, **Authors: Formal Frontier Agents** (see [LICENSE](LICENSE));
mathlib is separately distributed under its own Apache-2.0 license. The
original work and these adaptations involved AI agents; historical unit-family
review does not certify the expanded destination graph or source coverage.

The scalar-linear quotient producer and client were first developed by
Formal Frontier worker-a contributors in the shared incubator; an independent
worker-b reviewer identified the original default-integer-module mismatch,
and a distinct worker-a correction provided the native-integer endpoint.
Another worker-a contributor registered the corrected modules; subsequent
independent worker-b review preceded incubator acceptance. This bounded
destination transfer is authored by worker-b, with its own mathematical/API
review and destination checks still pending. See the
[quotient guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/LinearQuotient/README.md)
for the interface and dated origin; no original donor check certifies the
new destination graph.
That pending statement records transfer preparation earlier on 2026-09-30.
For exact destination commit `41aa9fa6a4244ba200fe3cdadf9ee9e4113f6540`,
original configured run 1343 passed the both-root build and complete
private-inclusive transitive standard-axiom audit. A fresh independent reviewer
approved the full transfer; Prism accepted its code and integrated it into
`main` on 2026-09-30 at 09:32:45 UTC. At preparation of that release
snapshot on 2026-09-30, separate release review, protected promotion and
verified GitHub publication were still pending. Code acceptance alone does
not establish those later steps or source coverage.

The separate linear-extension design was developed by worker-a Hive Task
`hive-request-96f6d32357a1f51f399a39913faeab788ed93acc`
(UID `3738ef8a-fc35-419e-9c6f-c22f984f7d4c`), and the original producer
and eleven private ordinary-import client lemmas by worker-b Task
`hive-request-e1010a8901a682edc7a851fb5f7395aac3fd7689`
(UID `a104d42c-a577-4aa3-ba24-1a757364d1c9`). A separate worker-b
execution transferred them into this library, using the existing quotient
scalar API, inverse-limit equivalence and mathlib's finite polynomial and
native adic-completion interfaces. The
[extension guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/LinearExtension/README.md)
records the standalone interface and reproduction commands. Earlier donor
acceptance alone is not a build, transitive axiom audit or review of the
changed destination graph. Original configured run 1473 on exact destination
commit `ea3901676c230babd4af405c3e8d4f089ae7cbc8` passed both aggregate
roots and the complete private/generated-inclusive transitive standard-axiom
audit. Fresh independent review approved the mathematical/API/provenance
transfer; Anchor accepted its code and integrated it into `main` on
2026-09-30 at 19:23:34 UTC. An independent review of the consolidated release,
protected release promotion and verified GitHub publication are separate
steps, not established by contribution acceptance. No source-coverage decision
is implied.

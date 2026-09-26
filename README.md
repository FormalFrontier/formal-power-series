# Formal power series

A Lean library for the **weighted negative logarithmic derivative** of native
power-series units over an arbitrary commutative ring `R`:

```lean
PowerSeries.negXLogDeriv (f : (PowerSeries R)ˣ) =
  -PowerSeries.X * PowerSeries.derivative (f : PowerSeries R) *
    ((f⁻¹ : (PowerSeries R)ˣ) : PowerSeries R)
```

It takes multiplication of units to addition of series, commutes with coefficient
ring maps (also between different universes), and has integral finite convolution
and normalized recurrence formulas. The native unit `oneSubCXUnit a` represents
`1 - C a * X`; its inverse and weighted-derivative coefficients are explicit.
No division by positive integers or hypothesis excluding torsion/zero rings is
required. This library does not construct formal logarithms, lambda- or
Witt-ring structures, splitting extensions or Adams operations. In positive
characteristic this map need not be injective.

## Build and use

Install `elan` and Git; `lean-toolchain` pins Lean
`leanprover/lean4:v4.34.0-rc2`, and the sole direct dependency is mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. From the repository root:

```sh
lake exe cache get
lake build
```

The first command fetches the matching mathlib cache; the literal default
`lake build` includes the public library and all `Tests/` examples. On a
matching warm cache, the measured initial module/default builds on the
author's September 2026 environment processed 1,743/1,777 Lake jobs;
these are job counts, not time or peak-memory measurements.

For capacity planning on a typical 4-core Linux development machine, budget
roughly **16 GiB RAM and 20 GiB free disk** for the pinned toolchain, dependencies,
matching mathlib cache and build outputs. An **unbenchmarked estimate** is
10–30 minutes for initial toolchain/cache setup and the default build, or
1–5 minutes for a small library/test rebuild with dependencies already cached.
These are planning allowances, not measured minima or performance guarantees;
download bandwidth, CPU speed and competing jobs can change them substantially.
The published author evidence records successful builds and job counts, not
elapsed-time, peak-memory or disk-use benchmarks. Fetch the cache before
building; these estimates do not cover rebuilding mathlib from source.

Import `FormalPowerSeries` from a dependent Lake project (declare and pin this
repository and its dependencies there). A build-checked example in
`Tests/UnitLogDerivative.lean`, which imports this public root, is:

```lean
theorem signedExample {T : Type*} [CommRing T]
    (a : T) (n : ℕ) :
    PowerSeries.coeff (n + 1)
      (PowerSeries.negXLogDeriv (PowerSeries.oneSubCXUnit a)) = a ^ (n + 1) :=
  PowerSeries.coeff_succ_negXLogDeriv_oneSubCXUnit a n
```

See [API.md](API.md) for names, hypotheses, coefficient conventions and examples.

## Provenance and rights

The integral formula is related to Charles A. Weibel, *The K-book: An
Introduction to Algebraic K-theory* (2013), Section II.4 and Exercise 4.6;
this small library does **not** claim to formalize the whole section or book.
Prism developed the original checked source experiment in
`source-weibel-k-book` at commit `6453001fbf58cbca909037650832071c594568a6`
(accepted source main `a2857276cc6bac20a65c77306e58f077d985fa93`).
Formal Frontier's `formalization-worker-a` adapted the proofs into this
source-independent module-system API and added the standalone client and
documentation. The module retains the originating proof structure and code
expression, rather than attributing them to mathlib. We use mathlib's
`PowerSeries.derivative`, `invOneSubPow`, `rescale`, coefficient algebra and
ordinary tactics as dependencies, not copied mathlib declarations or proofs.
Original repository files are released under Apache-2.0 (see `LICENSE`);
mathlib is separately distributed under its own Apache-2.0 license.
Both the original experiment and this adaptation involved AI agents, with
human/agent independent review tracked separately from authorship.

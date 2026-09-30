# Coefficientwise kernel products for restricted power series

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.KernelFiltration` (or
the umbrella `FormalPowerSeries`). For any variable type `σ`, `[CommRing R]`
and ideal `I : Ideal R`, write
`T := MvPowerSeries.adicallyRestrictedSubring (σ := σ) I` and
`ρ n := MvPowerSeries.adicReduction I n : T →+* MvPolynomial σ (R ⧸ I ^ n)`.
No finite-variable, finite-generation, Noetherian, completeness, separatedness,
proper-ideal or nontriviality hypothesis is needed.

## Product and finite-sum laws

- `MvPowerSeries.coeff_mul_mem_ideal_mul_ideal`: if the coefficients of arbitrary
  multivariate series `f` and `g` belong to arbitrary ideals `J` and `K`,
  respectively, every coefficient of `f * g` belongs to `J * K`.
- `MvPowerSeries.adicReduction_mul_eq_zero`: if `ρ n a = 0` and `ρ k b = 0`
  for `a b : T`, then `ρ (n + k) (a * b) = 0`.
- `MvPowerSeries.adicReduction_sum_mul_eq_zero`: the same conclusion for a
  finite sum `∑ i ∈ s, a i * b i` when every `a i` and `b i` lies in the
  respective fixed-level kernel.
- `MvPowerSeries.adicReduction_sum_mul_eq_zero_succ`: the finite-sum law with
  the second factors at level one, giving `ρ (n + 1)` of the sum equal to zero.

The kernels here are **coefficientwise**: vanishing of `ρ n` means that every
coefficient lies in `I ^ n`. This does not identify a kernel with an intrinsic
power of an ideal of `T`. The product laws include level zero, empty families,
empty variables, bottom/top ideals and zero rings. They do not construct a
geometric inverse or division operator and do not depend on the completion,
linear-extension or quotient modules. See the
[ordinary-import client](../../../../Tests/MvPowerSeries/IdealAdicRestricted/KernelFiltration.lean)
for eleven private usage examples.

## Reproduction and provenance

Use the repository's `lean-toolchain` (Lean `v4.34.0-rc2`) and complete
`lake-manifest.json` (sole direct dependency: mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`). From the project root,
first fetch the matching precompiled mathlib cache successfully:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake build FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.KernelFiltration
LEAN_NUM_THREADS=2 lake build Tests.MvPowerSeries.IdealAdicRestricted.KernelFiltration
lake build FormalPowerSeries Tests
```

The original coefficientwise proof and eleven client examples were written
by Formal Frontier AI contributors; this library adapts them to the
restricted-series base without changing their mathematical arguments. The
antidiagonal method adapts Jz Pan's one-variable proof in mathlib's
`Mathlib.RingTheory.PowerSeries.CoeffMulMem` (2025, Apache-2.0), explicitly
credited in the Lean producer. The use of that method does not assert original
authorship of mathlib's lemma. Original Formal Frontier code is Apache-2.0
(Authors: Formal Frontier Agents); mathlib is a separate Apache-2.0
dependency. These results do not establish source-specific coverage.

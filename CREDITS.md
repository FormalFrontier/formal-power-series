# Sources, contributors and rights

The integral unit formulas are related to Charles A. Weibel, *The K-book:
An Introduction to Algebraic K-theory* (2013), Section II.4 and Exercise
4.6. The rational Artin–Hasse exponential is described by I. B. Fesenko and
S. V. Vostokov, *Local Fields and Their Extensions*, second edition (2002),
Chapter I, (9.1); its coefficient-integrality assertion is proved here by the
standard Dieudonné–Dwork method using Mathlib's p-adic divided powers, rather
than by the book's Euler-product argument.
Kazuhiro Fujiwara and Fumiharu Kato, *Foundations of Rigid Geometry I*, provide
background for coefficientwise restricted series. These references do not
imply formal coverage of the sources.

The original weighted unit logarithmic derivative formalization and its earlier
boundary examples were contributed by the Formal Frontier project. Formal Frontier
AI contributors adapted and extended these formalizations and examples for this
library and wrote examples and documentation.

The restricted-series contributions include the carrier construction, principal
kernel, completion, scalar-linear quotient, linear extension and coefficientwise
kernel-filtration proofs; content, selected factorization, actual leading terms,
normalized division, cofinal comparison and conditional primitive ideal generation;
the finite-variable degree criterion, its infinite-variable counterexample and
the finite-generation kernel argument; and the restricted-subring unit criteria.
This collective credit distinguishes the mathematical arguments from their Lean
formalizations and ordinary-import examples. Further contributions include the
intrinsic leading-product, singleton and first-variable division, residue
reflection, conditional quotient-unit and first-variable preparation arguments,
formalizations and clients. These results reuse the restricted-series foundation
and polynomial lexicographic API.

The antidiagonal coefficient-product method adapts Jz Pan's 2025 mathlib
`PowerSeries.CoeffMulMem` argument,
Apache-2.0, as credited in the [kernel-filtration formalization](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/KernelFiltration.lean).
The upstream copyright, license and author notices are retained for this
adaptation, together with a separate description of the project's multivariate
coefficient-ideal and restricted-series kernel-product modifications in that
file.

The completed-coefficient polynomial comparison reuses the entire AdicModules
completion-of-dependent-direct-sums equivalence and inverse, its canonical
restriction-of-scalars comparison, and its named completed coefficient algebra.
Mathlib supplies the coefficient linear equivalences and completion functor,
including the completion and completed scalar formalizations of Judith Ludwig,
Christian Merten and Jiedong Jiang. The complete-original-coefficient comparison
is a coefficient transport of this same equivalence, using the existing
polynomial-reduction API of this library.
Native mathlib polynomial, power-series, ideal, quotient and completion APIs
retain their respective authors and license; using these methods is not a
claim to their original proofs.

The completed polynomial maps reuse AdicModules' `AdicCompletion.mapRingHom`
and Mathlib's polynomial coefficient maps and renaming. The restricted-series
coefficient and arbitrary variable maps over completed coefficients are
constructed independently of the polynomial-completion comparison: coefficient
change restricts Mathlib's coefficientwise map, while renaming completes a
finite direct-sum pushforward using the whole AdicModules
completion/restricted-product equivalence. Their forward and inverse naturality
with the comparison is proved rather than used to define them; see the
[naturality module](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/Naturality.lean).

Original project files carry **SPDX-License-Identifier: Apache-2.0** and
**Authors: Formal Frontier Agents**; see the complete [LICENSE](LICENSE).
mathlib is separately licensed under Apache-2.0. The project used AI agents
for formalization and documentation. These credits do not assert formal
coverage of these mathematical sources.

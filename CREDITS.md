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
imply formal coverage of the sources. Prism authored the original weighted
unit logarithmic derivative formalization and its earlier boundary examples.
Formal Frontier AI contributors adapted and extended these formalizations and
examples for this library, added further examples and wrote the guides.
Folio contributed the derivative headlines and documentation. Distinct Formal
Frontier contributors developed the restricted carrier, principal kernel,
completion, scalar-linear quotient, linear extension and coefficientwise
kernel-filtration proofs; other contributors developed content, selected
factorization, actual leading terms, normalized division, cofinal comparison
and conditional primitive ideal generation. Contributors to the finite-variable
degree criterion, its infinite-variable counterexample and the finite-generation
kernel argument were distinct from those who formalized these results and wrote
their ordinary-import clients. Further contributors developed and formalized
the restricted-subring unit criteria and wrote their ordinary-import client.
Formal Frontier AI contributors also developed the intrinsic leading-product,
singleton and first-variable division, residue reflection, conditional
quotient-unit and first-variable preparation arguments and their
ordinary-import clients; these results reuse the published restricted-series
foundation and polynomial lexicographic API.
The antidiagonal coefficient-product method adapts Jz Pan's 2025 mathlib
`PowerSeries.CoeffMulMem` argument,
Apache-2.0, as credited in the [kernel-filtration formalization](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/KernelFiltration.lean).
The upstream copyright, license and author notices are retained for this
adaptation, together with a separate description of the project's multivariate
coefficient-ideal and restricted-series kernel-product modifications in that
file. These notices and the modification description also accompany earlier
published versions of the kernel-filtration development, its documentation
and examples.
Native mathlib polynomial, power-series, ideal, quotient and completion APIs
retain their respective authors and license; using these methods is not a
claim to their original proofs.

Original project files carry **SPDX-License-Identifier: Apache-2.0** and
**Authors: Formal Frontier Agents**; see the complete [LICENSE](LICENSE).
mathlib is separately licensed under Apache-2.0. The project used AI agents
for formalization and documentation. These credits do not assert formal
coverage of these mathematical sources.

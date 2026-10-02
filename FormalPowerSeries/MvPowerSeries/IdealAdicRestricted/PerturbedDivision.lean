/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.KernelFiltration
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.PolynomialDivision
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.RestrictedGeometricInverse

@[expose] public section

/-!
# Division by finite perturbations of polynomial divisors

Finite polynomial division and the coefficientwise kernel product law give a
linear error operator for restricted divisors agreeing with the polynomial
divisors modulo the first ideal power. Its geometric inverse corrects both
quotient coordinates and remainder inside the restricted subring.
-/

set_option warningAsError true

namespace MonomialOrder

variable {σ ι R : Type*} [CommRing R] [Fintype ι]
variable (I : Ideal R) [IsAdicComplete I R]
variable (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
variable (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
variable (g : ι → MvPowerSeries.adicallyRestrictedSubring (σ := σ) I)

/-- The difference between fixed polynomial division and multiplication by
the actual restricted divisors, as an `R`-linear endomorphism. -/
noncomputable def restrictedDivisionError :
    Module.End R (MvPowerSeries.adicallyRestrictedSubring (σ := σ) I) where
  toFun x := ∑ i, restrictedDivisionQuotient I m b hb x i *
    (MvPowerSeries.polynomialToRestricted I (b i) - g i)
  map_add' x y := by
    simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [map_smul, Pi.smul_apply, smul_mul_assoc, Finset.smul_sum]
    rfl

/-- Level-one agreement makes the finite error operator strictly raise every
coefficientwise kernel; this is derived rather than required of the caller. -/
theorem restrictedDivisionError_raises
    (hg : ∀ i, MvPowerSeries.adicReduction I 1
        (MvPowerSeries.polynomialToRestricted I (b i)) =
      MvPowerSeries.adicReduction I 1 (g i))
    (n : ℕ) (x : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I)
    (hx : MvPowerSeries.adicReduction I n x = 0) :
    MvPowerSeries.adicReduction I (n + 1)
      (restrictedDivisionError I m b hb g x) = 0 := by
  change MvPowerSeries.adicReduction I (n + 1)
    (∑ i, restrictedDivisionQuotient I m b hb x i *
      (MvPowerSeries.polynomialToRestricted I (b i) - g i)) = 0
  apply MvPowerSeries.adicReduction_sum_mul_eq_zero_succ I Finset.univ
  · intro i _
    exact restrictedDivisionQuotient_preserves_ker I m b hb n x hx i
  · intro i _
    simpa only [map_sub, sub_eq_zero] using hg i

/-- Quotient coordinates for a finite family of restricted divisors, corrected
by the geometric inverse of the polynomial-division error. -/
noncomputable def restrictedPerturbedDivisionQuotient
    (hg : ∀ i, MvPowerSeries.adicReduction I 1
        (MvPowerSeries.polynomialToRestricted I (b i)) =
      MvPowerSeries.adicReduction I 1 (g i)) :
    MvPowerSeries.adicallyRestrictedSubring (σ := σ) I →ₗ[R]
      (ι → MvPowerSeries.adicallyRestrictedSubring (σ := σ) I) :=
  (restrictedDivisionQuotient I m b hb).comp
    (MvPowerSeries.restrictedGeometricInverse I
      (restrictedDivisionError I m b hb g)
      (restrictedDivisionError_raises I m b hb g hg))

/-- The corrected restricted-series remainder obtained from the fixed polynomial
division operators. No independence from division choices or uniqueness is
asserted, and no finiteness assumption on the variables is needed. -/
noncomputable def restrictedPerturbedDivisionRemainder
    (hg : ∀ i, MvPowerSeries.adicReduction I 1
        (MvPowerSeries.polynomialToRestricted I (b i)) =
      MvPowerSeries.adicReduction I 1 (g i)) :
    Module.End R (MvPowerSeries.adicallyRestrictedSubring (σ := σ) I) :=
  (restrictedDivisionRemainder I m b hb).comp
    (MvPowerSeries.restrictedGeometricInverse I
      (restrictedDivisionError I m b hb g)
      (restrictedDivisionError_raises I m b hb g hg))

/-- Corrected division reconstructs the original element inside the
restricted subring, using the actual restricted divisors. -/
theorem restrictedPerturbedDivision_decomposition
    (hg : ∀ i, MvPowerSeries.adicReduction I 1
        (MvPowerSeries.polynomialToRestricted I (b i)) =
      MvPowerSeries.adicReduction I 1 (g i))
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I) :
    f = (∑ i, restrictedPerturbedDivisionQuotient I m b hb g hg f i * g i) +
      restrictedPerturbedDivisionRemainder I m b hb g hg f := by
  let s := MvPowerSeries.restrictedGeometricInverse I
    (restrictedDivisionError I m b hb g)
    (restrictedDivisionError_raises I m b hb g hg) f
  have hleft : s - restrictedDivisionError I m b hb g s = f := by
    have h := congrArg (fun F : Module.End R
        (MvPowerSeries.adicallyRestrictedSubring (σ := σ) I) => F f)
      (MvPowerSeries.restrictedGeometricInverse_left_inv I
        (restrictedDivisionError I m b hb g)
        (restrictedDivisionError_raises I m b hb g hg))
    simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] using h
  calc
    f = s - restrictedDivisionError I m b hb g s := hleft.symm
    _ = (∑ i, restrictedDivisionQuotient I m b hb s i *
        MvPowerSeries.polynomialToRestricted I (b i)) +
        restrictedDivisionRemainder I m b hb s -
        (∑ i, restrictedDivisionQuotient I m b hb s i *
          (MvPowerSeries.polynomialToRestricted I (b i) - g i)) := by
      change s - (∑ i, restrictedDivisionQuotient I m b hb s i *
          (MvPowerSeries.polynomialToRestricted I (b i) - g i)) = _
      exact congrArg
        (fun t : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I =>
          t - ∑ i, restrictedDivisionQuotient I m b hb s i *
            (MvPowerSeries.polynomialToRestricted I (b i) - g i))
        (restrictedDivision_decomposition I m b hb s)
    _ = (∑ i, restrictedDivisionQuotient I m b hb s i * g i) +
        restrictedDivisionRemainder I m b hb s := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      abel
    _ = (∑ i, restrictedPerturbedDivisionQuotient I m b hb g hg f i * g i) +
        restrictedPerturbedDivisionRemainder I m b hb g hg f := rfl

/-- The corrected remainder has actual zero coefficients in every leading cone. -/
theorem coeff_restrictedPerturbedDivisionRemainder_eq_zero
    (hg : ∀ i, MvPowerSeries.adicReduction I 1
        (MvPowerSeries.polynomialToRestricted I (b i)) =
      MvPowerSeries.adicReduction I 1 (g i))
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I)
    (α : σ →₀ ℕ) (i : ι) (hi : m.degree (b i) ≤ α) :
    MvPowerSeries.coeff α
      ((restrictedPerturbedDivisionRemainder I m b hb g hg f :
        MvPowerSeries.adicallyRestrictedSubring (σ := σ) I) :
        MvPowerSeries σ R) = 0 :=
  coeff_restrictedDivisionRemainder_eq_zero I m b hb _ α i hi

/-- Every corrected quotient coordinate preserves every coefficientwise kernel. -/
theorem restrictedPerturbedDivisionQuotient_preserves_ker
    (hg : ∀ i, MvPowerSeries.adicReduction I 1
        (MvPowerSeries.polynomialToRestricted I (b i)) =
      MvPowerSeries.adicReduction I 1 (g i))
    (n : ℕ) (f : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I)
    (hf : MvPowerSeries.adicReduction I n f = 0) (i : ι) :
    MvPowerSeries.adicReduction I n
      (restrictedPerturbedDivisionQuotient I m b hb g hg f i) = 0 :=
  restrictedDivisionQuotient_preserves_ker I m b hb n _
    (MvPowerSeries.restrictedGeometricInverse_preserves_ker I _ _ n f hf) i

/-- The corrected remainder preserves every coefficientwise kernel. -/
theorem restrictedPerturbedDivisionRemainder_preserves_ker
    (hg : ∀ i, MvPowerSeries.adicReduction I 1
        (MvPowerSeries.polynomialToRestricted I (b i)) =
      MvPowerSeries.adicReduction I 1 (g i))
    (n : ℕ) (f : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I)
    (hf : MvPowerSeries.adicReduction I n f = 0) :
    MvPowerSeries.adicReduction I n
      (restrictedPerturbedDivisionRemainder I m b hb g hg f) = 0 :=
  restrictedDivisionRemainder_preserves_ker I m b hb n _
    (MvPowerSeries.restrictedGeometricInverse_preserves_ker I _ _ n f hf)

end MonomialOrder

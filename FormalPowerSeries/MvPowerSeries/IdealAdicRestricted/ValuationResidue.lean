/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.IdealChange
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LeadingTerm

public section

/-!
# The polynomial residue as a ring homomorphism

For a parameter in the maximal ideal of a local ring, the shared larger-ideal
reduction gives a polynomial-valued ring homomorphism. Over a valuation domain,
it agrees with the existing `restrictedResidue` function by its
coefficient formula.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

section LocalRing

variable [IsLocalRing R]

/-- Polynomial residue of a principal-adically restricted series at the maximal
ideal. No separatedness, completeness or nonzero-parameter assumption is needed. -/
noncomputable def restrictedResidueHom (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R) :
    adicallyRestrictedSubring (σ := σ) (Ideal.span {a}) →+*
      MvPolynomial σ (R ⧸ IsLocalRing.maximalIdeal R) :=
  reductionAtLargerIdeal (Ideal.span {a}) (IsLocalRing.maximalIdeal R)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ham))

@[simp]
theorem coeff_restrictedResidueHom (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (f : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) (d : σ →₀ ℕ) :
    (restrictedResidueHom a ham f).coeff d =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
        (coeff d (f : MvPowerSeries σ R)) := by
  simp only [restrictedResidueHom, coeff_reductionAtLargerIdeal]

/-- Every residue polynomial has a polynomial lift in the restricted subring. -/
theorem restrictedResidueHom_surjective (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R) :
    Function.Surjective (restrictedResidueHom (σ := σ) a ham) :=
  reductionAtLargerIdeal_surjective _ _ _

end LocalRing

section ValuationDomain

variable [IsDomain R] [ValuationRing R]

/-- The existing valuation-domain residue function is exactly the public ring
homomorphism, not a reduction at the smaller principal ideal. -/
@[simp]
theorem restrictedResidueHom_apply (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (f : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) :
    restrictedResidueHom a ham f = restrictedResidue a ham f := by
  ext d
  simp only [coeff_restrictedResidueHom, coeff_restrictedResidue]

@[simp]
theorem restrictedResidue_zero (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R) :
    restrictedResidue a ham (0 : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) =
      0 := by
  simpa only [restrictedResidueHom_apply] using (map_zero (restrictedResidueHom (σ := σ) a ham))

@[simp]
theorem restrictedResidue_one (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R) :
    restrictedResidue a ham (1 : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) =
      1 := by
  simpa only [restrictedResidueHom_apply] using (map_one (restrictedResidueHom (σ := σ) a ham))

@[simp]
theorem restrictedResidue_add (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (f g : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) :
    restrictedResidue a ham (f + g) = restrictedResidue a ham f + restrictedResidue a ham g := by
  simpa only [restrictedResidueHom_apply] using (map_add (restrictedResidueHom a ham) f g)

@[simp]
theorem restrictedResidue_mul (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (f g : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) :
    restrictedResidue a ham (f * g) = restrictedResidue a ham f * restrictedResidue a ham g := by
  simpa only [restrictedResidueHom_apply] using (map_mul (restrictedResidueHom a ham) f g)

@[simp]
theorem restrictedResidue_polynomial (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R) (p : MvPolynomial σ R) :
    restrictedResidue a ham (polynomialToRestricted (Ideal.span {a}) p) =
      MvPolynomial.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) p := by
  rw [← restrictedResidueHom_apply]
  exact reductionAtLargerIdeal_polynomial _ _ _ p

/-- Units map to units under the existing residue function. This is preservation,
not reflection, and uses no completeness assumption. -/
theorem isUnit_restrictedResidue_of_isUnit (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (f : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) (hf : IsUnit f) :
    IsUnit (restrictedResidue a ham f) := by
  simpa only [restrictedResidueHom_apply] using hf.map (restrictedResidueHom a ham)

end ValuationDomain

end MvPowerSeries

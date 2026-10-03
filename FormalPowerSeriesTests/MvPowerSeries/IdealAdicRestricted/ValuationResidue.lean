/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.ValuationResidue
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.MvPowerSeries.Inverse

public section

/-! Local-ring residue polynomials and valuation-domain compatibility. -/

set_option warningAsError true

open MvPowerSeries

section LocalRing

variable {σ R : Type*} [CommRing R] [IsLocalRing R]
    (a : R) (ham : a ∈ IsLocalRing.maximalIdeal R)

example (f g : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) :
    restrictedResidueHom a ham (f * g) =
      restrictedResidueHom a ham f * restrictedResidueHom a ham g :=
  map_mul _ _ _

example : Function.Surjective (restrictedResidueHom (σ := σ) a ham) :=
  restrictedResidueHom_surjective _ _

example (f : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) (d : σ →₀ ℕ) :
    (restrictedResidueHom a ham f).coeff d =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
        (coeff d (f : MvPowerSeries σ R)) :=
  coeff_restrictedResidueHom a ham f d

end LocalRing

section ValuationDomain

variable {σ R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    (a : R) (ham : a ∈ IsLocalRing.maximalIdeal R)

-- This identifies the existing function without a Hausdorff instance.
example (f g : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) :
    restrictedResidue a ham (f * g + 1) =
      restrictedResidue a ham f * restrictedResidue a ham g + 1 := by
  simp only [restrictedResidue_add, restrictedResidue_mul, restrictedResidue_one]

example (f : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) (hf : IsUnit f) :
    IsUnit (restrictedResidue a ham f) :=
  isUnit_restrictedResidue_of_isUnit _ _ _ hf

-- Empty variables and the zero parameter are allowed; no nonzero parameter is inferred.
example (p : MvPolynomial Empty R) :
    restrictedResidue (0 : R) (Ideal.zero_mem _) (polynomialToRestricted (Ideal.span {0}) p) =
      MvPolynomial.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) p :=
  restrictedResidue_polynomial _ _ _

end ValuationDomain

-- Infinite variables over a concrete field still give finite polynomial residues.
example : Function.Surjective (restrictedResidueHom (σ := ℕ) (0 : ZMod 2) (Ideal.zero_mem _)) :=
  restrictedResidueHom_surjective _ _

-- A two-variable formal-series coefficient ring needs only its local-ring instance.
example : Function.Surjective (restrictedResidueHom (σ := ℕ)
    (0 : MvPowerSeries (Fin 2) (ZMod 2)) (Ideal.zero_mem _)) :=
  restrictedResidueHom_surjective _ _

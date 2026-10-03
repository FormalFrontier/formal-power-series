/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted
public import Mathlib.RingTheory.MvPowerSeries.Equiv

public section

/-!
# Renaming ideal-adically restricted series

A bijection of variables transports the restricted subring without changing
the coefficient ideal. The transport agrees with raw variable renaming.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {R σ υ γ : Type*} [CommRing R]

private theorem isAdicallyRestricted_renameEquiv (I : Ideal R) (e : σ ≃ υ)
    (f : MvPowerSeries σ R) (hf : IsAdicallyRestricted I f) :
    IsAdicallyRestricted I (renameEquiv R e f) := by
  intro k
  let shift : (σ →₀ ℕ) ≃+ (υ →₀ ℕ) := Finsupp.domCongr e
  have hcoeff (α : σ →₀ ℕ) :
      coeff (shift α) (renameEquiv R e f) = coeff α f := by
    simpa [shift, Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
      Finsupp.embDomain_eq_mapDomain, renameEquiv_apply] using
      coeff_embDomain_rename e.toEmbedding f α
  have hfinite : (shift.symm ⁻¹' {α : σ →₀ ℕ | coeff α f ∉ I ^ k}).Finite :=
    Set.Finite.preimage shift.symm.injective.injOn (hf k)
  convert hfinite using 1
  ext β
  change coeff β (renameEquiv R e f) ∉ I ^ k ↔
    coeff (shift.symm β) f ∉ I ^ k
  have heq : coeff β (renameEquiv R e f) = coeff (shift.symm β) f := by
    simpa only [shift.apply_symm_apply] using hcoeff (shift.symm β)
  rw [heq]

/-- A bijection of variables preserves ideal-adic restrictedness. -/
noncomputable def restrictedRenameEquiv (I : Ideal R) (e : σ ≃ υ) :
    adicallyRestrictedSubring (σ := σ) I ≃+*
      adicallyRestrictedSubring (σ := υ) I where
  toFun f := ⟨renameEquiv R e f,
    (mem_adicallyRestrictedSubring I _).2
      (isAdicallyRestricted_renameEquiv I e _
        ((mem_adicallyRestrictedSubring I _).1 f.property))⟩
  invFun f := ⟨renameEquiv R e.symm f,
    (mem_adicallyRestrictedSubring I _).2
      (isAdicallyRestricted_renameEquiv I e.symm _
        ((mem_adicallyRestrictedSubring I _).1 f.property))⟩
  left_inv f := by
    apply Subtype.ext
    exact (renameEquiv R e).left_inv f
  right_inv f := by
    apply Subtype.ext
    exact (renameEquiv R e).right_inv f
  map_mul' f g := by
    apply Subtype.ext
    exact (renameEquiv R e).map_mul f g
  map_add' f g := by
    apply Subtype.ext
    exact (renameEquiv R e).map_add f g

@[simp]
theorem restrictedRenameEquiv_coe (I : Ideal R) (e : σ ≃ υ)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    (restrictedRenameEquiv I e f : MvPowerSeries υ R) =
      renameEquiv R e (f : MvPowerSeries σ R) := by
  simp [restrictedRenameEquiv]

/-- Renaming a restricted series reindexes its coefficients. -/
@[simp]
theorem coeff_restrictedRenameEquiv (I : Ideal R) (e : σ ≃ υ)
    (f : adicallyRestrictedSubring (σ := σ) I) (d : σ →₀ ℕ) :
    coeff (Finsupp.domCongr e d)
        (restrictedRenameEquiv I e f : MvPowerSeries υ R) =
      coeff d (f : MvPowerSeries σ R) := by
  simpa [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.embDomain_eq_mapDomain, renameEquiv_apply] using
    coeff_embDomain_rename e.toEmbedding (f : MvPowerSeries σ R) d

/-! Restricted variable renaming has the same identity and composition laws
as renaming unrestricted multivariate power series. -/

@[simp]
theorem restrictedRenameEquiv_refl (I : Ideal R) :
    restrictedRenameEquiv I (Equiv.refl σ) = RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro f
  apply Subtype.ext
  simp

@[simp]
theorem restrictedRenameEquiv_trans (I : Ideal R) (e : σ ≃ υ) (f : υ ≃ γ) :
    (restrictedRenameEquiv I e).trans (restrictedRenameEquiv I f) =
      restrictedRenameEquiv I (e.trans f) := by
  apply RingEquiv.ext
  intro p
  apply Subtype.ext
  change renameEquiv R f (renameEquiv R e (p : MvPowerSeries σ R)) =
    renameEquiv R (e.trans f) p
  rw [← AlgEquiv.trans_apply, renameEquiv_trans]

end MvPowerSeries

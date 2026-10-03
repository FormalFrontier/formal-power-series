/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.RestrictedGeometricInverse
public import Mathlib.Data.ZMod.Basic

public section

/-!
# Ordinary-import clients for the restricted geometric inverse
-/

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
variable (E : Module.End R (adicallyRestrictedSubring (σ := σ) I))
variable (hE : ∀ n x, adicReduction I n x = 0 → adicReduction I (n + 1) (E x) = 0)

private theorem client_level (n : ℕ) (x : adicallyRestrictedSubring (σ := σ) I) :
    adicReduction I n (restrictedGeometricInverse I E hE x) =
      adicReduction I n ((∑ j ∈ Finset.range n, E ^ j) x) :=
  restrictedGeometricInverse_reduction I E hE n x

/-- The geometric inverse preserves the kernel of linear polynomial reduction. -/
theorem client_kernel (n : ℕ) (x : adicallyRestrictedSubring (σ := σ) I)
    (hx : x ∈ LinearMap.ker (linearAdicReduction (σ := σ) I n)) :
    restrictedGeometricInverse I E hE x ∈
      LinearMap.ker (linearAdicReduction (σ := σ) I n) := by
  rw [LinearMap.mem_ker, linearAdicReduction_apply] at hx ⊢
  exact restrictedGeometricInverse_preserves_ker I E hE n x hx

private theorem client_left_inv :
    (LinearMap.id - E).comp (restrictedGeometricInverse I E hE) = LinearMap.id :=
  restrictedGeometricInverse_left_inv I E hE

private theorem client_right_inv :
    (restrictedGeometricInverse I E hE).comp (LinearMap.id - E) = LinearMap.id :=
  restrictedGeometricInverse_right_inv I E hE

private theorem client_unique
    (U : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (hU : (LinearMap.id - E).comp U = LinearMap.id) :
    U = restrictedGeometricInverse I E hE :=
  restrictedGeometricInverse_unique I E hE U hU

private theorem client_add (x y : adicallyRestrictedSubring (σ := σ) I) :
    restrictedGeometricInverse I E hE (x + y) =
      restrictedGeometricInverse I E hE x + restrictedGeometricInverse I E hE y :=
  (restrictedGeometricInverse I E hE).map_add x y

private theorem client_smul (r : R) (x : adicallyRestrictedSubring (σ := σ) I) :
    restrictedGeometricInverse I E hE (r • x) =
      r • restrictedGeometricInverse I E hE x :=
  (restrictedGeometricInverse I E hE).map_smul r x

private theorem client_level_zero (x : adicallyRestrictedSubring (σ := σ) I) :
    adicReduction I 0 (restrictedGeometricInverse I E hE x) = 0 := by
  simpa only [Finset.range_zero, Finset.sum_empty, LinearMap.zero_apply, map_zero]
    using client_level I E hE 0 x

omit [IsAdicComplete I R] in
private theorem client_zero_raises :
    ∀ n (x : adicallyRestrictedSubring (σ := σ) I),
      adicReduction I n x = 0 →
        adicReduction I (n + 1) ((0 : Module.End R _) x) = 0 := by
  intro n x hx
  simp

private theorem client_zero_operator (x : adicallyRestrictedSubring (σ := σ) I) :
    restrictedGeometricInverse I
      (0 : Module.End R (adicallyRestrictedSubring (σ := σ) I))
      (client_zero_raises I) x = x := by
  have h := restrictedGeometricInverse_right_inv I
    (0 : Module.End R (adicallyRestrictedSubring (σ := σ) I)) (client_zero_raises I)
  simpa only [sub_zero, LinearMap.comp_id, LinearMap.id_apply] using
    congrArg (fun f : Module.End R (adicallyRestrictedSubring (σ := σ) I) => f x) h

private theorem client_empty_variables
    (F : Module.End R (adicallyRestrictedSubring (σ := Empty) I))
    (hF : ∀ n x, adicReduction I n x = 0 → adicReduction I (n + 1) (F x) = 0) :
    (restrictedGeometricInverse I F hF).comp (LinearMap.id - F) = LinearMap.id :=
  client_right_inv (σ := Empty) I F hF

private theorem client_zero_ideal [IsAdicComplete (⊥ : Ideal R) R]
    (F : Module.End R (adicallyRestrictedSubring (σ := σ) (⊥ : Ideal R)))
    (hF : ∀ n x, adicReduction (⊥ : Ideal R) n x = 0 →
      adicReduction (⊥ : Ideal R) (n + 1) (F x) = 0) :
    (LinearMap.id - F).comp (restrictedGeometricInverse (⊥ : Ideal R) F hF) =
      LinearMap.id :=
  client_left_inv (σ := σ) (⊥ : Ideal R) F hF

private theorem client_zero_ring
    [IsAdicComplete (⊥ : Ideal (ZMod 1)) (ZMod 1)]
    (x : adicallyRestrictedSubring (σ := Empty) (⊥ : Ideal (ZMod 1))) :
    letI : Algebra (ZMod 1)
        (adicallyRestrictedSubring (σ := Empty) (⊥ : Ideal (ZMod 1))) :=
      adicallyRestrictedAlgebra (⊥ : Ideal (ZMod 1))
    let F : @Module.End (ZMod 1)
        (adicallyRestrictedSubring (σ := Empty) (⊥ : Ideal (ZMod 1)))
        _ _ (Algebra.toModule) := 0
    restrictedGeometricInverse (⊥ : Ideal (ZMod 1)) F
      (by intro n y _; simp [F]) x = x := by
  simpa using client_zero_operator (σ := Empty) (⊥ : Ideal (ZMod 1)) x

end MvPowerSeries

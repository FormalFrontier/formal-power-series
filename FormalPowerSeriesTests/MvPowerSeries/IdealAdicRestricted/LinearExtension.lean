/- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LinearExtension
public import Mathlib.Data.ZMod.Basic

public section

/-!
# Ordinary-import clients for the restricted linear extension

These examples exercise polynomial and linear compatibility through public imports.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
variable (F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R)

private theorem client_linear_add (f g : adicallyRestrictedSubring (σ := σ) I) :
    restrictedLinearExtension I F (f + g) =
      restrictedLinearExtension I F f + restrictedLinearExtension I F g :=
  (restrictedLinearExtension I F).map_add f g

private theorem client_linear_smul (r : R) (f : adicallyRestrictedSubring (σ := σ) I) :
    restrictedLinearExtension I F (r • f) = r • restrictedLinearExtension I F f :=
  (restrictedLinearExtension I F).map_smul r f

private theorem client_level (n : ℕ) (f : adicallyRestrictedSubring (σ := σ) I) :
    adicReduction I n (restrictedLinearExtension I F f) =
      polynomialLinearMapMod I n F (adicReduction I n f) :=
  adicReduction_restrictedLinearExtension I F n f

/-- Linear extension acts on an embedded polynomial by the polynomial operator. -/
theorem client_polynomial (p : MvPolynomial σ R) :
    restrictedLinearExtension I F (polynomialToRestricted I p) =
      polynomialToRestricted I (F p) :=
  restrictedLinearExtension_polynomial I F p

private theorem client_kernel (n : ℕ) (f : adicallyRestrictedSubring (σ := σ) I)
    (hf : f ∈ RingHom.ker (adicReduction (σ := σ) I n)) :
    restrictedLinearExtension I F f ∈ RingHom.ker (adicReduction (σ := σ) I n) :=
  restrictedLinearExtension_preserves_ker I F n f hf

private theorem client_uniqueness
    (G : adicallyRestrictedSubring (σ := σ) I →ₗ[R]
      adicallyRestrictedSubring (σ := σ) I)
    (hpoly : ∀ p : MvPolynomial σ R,
      G (polynomialToRestricted I p) = polynomialToRestricted I (F p))
    (hker : ∀ n f, adicReduction I n f = 0 → adicReduction I n (G f) = 0) :
    G = restrictedLinearExtension I F :=
  restrictedLinearExtension_unique I F G hpoly hker

private theorem client_identity :
    restrictedLinearExtension (σ := σ) I
      (LinearMap.id (R := R) (M := MvPolynomial σ R)) = LinearMap.id := by
  symm
  apply restrictedLinearExtension_unique I
    (LinearMap.id (R := R) (M := MvPolynomial σ R))
  · intro p
    rfl
  · intro n g hg
    exact hg

private theorem client_level_zero (f : adicallyRestrictedSubring (σ := σ) I) :
    adicReduction I 0 (restrictedLinearExtension I F f) = 0 := by
  rw [client_level I F 0 f]
  have hsingleton : Subsingleton (R ⧸ I ^ 0) :=
    Ideal.Quotient.subsingleton_iff.mpr (by simp)
  apply MvPolynomial.ext
  intro index
  exact @Subsingleton.elim _ hsingleton _ _

private theorem client_empty_variables (f : adicallyRestrictedSubring (σ := Empty) I) :
    restrictedLinearExtension I (LinearMap.id (R := R) (M := MvPolynomial Empty R)) f = f := by
  rw [client_identity (σ := Empty) I]
  rfl

private theorem client_zero_ideal (f : adicallyRestrictedSubring (σ := σ) (⊥ : Ideal R)) :
    restrictedLinearExtension (⊥ : Ideal R)
      (LinearMap.id (R := R) (M := MvPolynomial σ R)) f = f := by
  rw [client_identity (σ := σ) (⊥ : Ideal R)]
  rfl

private theorem client_zero_ring (f : adicallyRestrictedSubring (σ := Empty)
    (⊥ : Ideal (ZMod 1))) :
    restrictedLinearExtension (⊥ : Ideal (ZMod 1))
      (LinearMap.id (R := ZMod 1) (M := MvPolynomial Empty (ZMod 1))) f = f := by
  rw [client_identity (σ := Empty) (⊥ : Ideal (ZMod 1))]
  rfl

end MvPowerSeries

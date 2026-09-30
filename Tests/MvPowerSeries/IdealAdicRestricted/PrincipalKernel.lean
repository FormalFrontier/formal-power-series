/- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.PrincipalKernel
import Mathlib.Algebra.Regular.Prod
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.ZMod.Defs

set_option warningAsError true

namespace FormalPowerSeriesTests.MvPowerSeries.IdealAdicRestricted.PrincipalKernel

open _root_.MvPowerSeries

private theorem generic_factorization {σ R : Type*} [CommRing R]
    (a : R) (ha : IsRegular a) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R)))
    (hf : ∀ m : σ →₀ ℕ,
      MvPowerSeries.coeff m (f : MvPowerSeries σ R) ∈
        (Ideal.span ({a} : Set R)) ^ k) :
    ∃ g : adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R)),
      f = principalAdicConstant a k * g :=
  exists_restricted_principal_quotient a ha k f hf

private theorem generic_kernel {σ R : Type*} [CommRing R]
    (a : R) (ha : IsRegular a) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R))) :
    f ∈ RingHom.ker (adicReduction (σ := σ) (Ideal.span ({a} : Set R)) k) ↔
      ∃ g : adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R)),
        g * principalAdicConstant a k = f := by
  rw [ker_adicReduction_principal a ha k, Ideal.mem_span_singleton']

private theorem integer_level_zero
    (f : adicallyRestrictedSubring (σ := Fin 2) (Ideal.span ({(2 : ℤ)} : Set ℤ))) :
    ∃ g : adicallyRestrictedSubring (σ := Fin 2)
        (Ideal.span ({(2 : ℤ)} : Set ℤ)),
      f = principalAdicConstant (2 : ℤ) 0 * g := by
  apply exists_restricted_principal_quotient (2 : ℤ)
    (IsRegular.of_ne_zero (by decide)) 0 f
  intro m
  simp

private theorem unit_parameter {σ R : Type*} [CommRing R] (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) (Ideal.span ({(1 : R)} : Set R))) :
    ∃ g : adicallyRestrictedSubring (σ := σ) (Ideal.span ({(1 : R)} : Set R)),
      f = principalAdicConstant (1 : R) k * g := by
  apply exists_restricted_principal_quotient (1 : R) isRegular_one k f
  intro m
  simp [Ideal.top_pow]

private theorem no_variables (a : ℤ) (ha : IsRegular a) (k : ℕ) :
    RingHom.ker (adicReduction (σ := Fin 0) (Ideal.span ({a} : Set ℤ)) k) =
      Ideal.span ({principalAdicConstant (σ := Fin 0) a k} :
        Set (adicallyRestrictedSubring (σ := Fin 0) (Ideal.span ({a} : Set ℤ)))) :=
  ker_adicReduction_principal a ha k

private theorem infinitely_many_variables (a : ℤ) (ha : IsRegular a) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := ℕ) (Ideal.span ({a} : Set ℤ)))
    (hf : ∀ m : ℕ →₀ ℕ, MvPowerSeries.coeff m (f : MvPowerSeries ℕ ℤ) ∈
      (Ideal.span ({a} : Set ℤ)) ^ k) :
    ∃ g : adicallyRestrictedSubring (σ := ℕ) (Ideal.span ({a} : Set ℤ)),
      f = principalAdicConstant a k * g :=
  exists_restricted_principal_quotient a ha k f hf

private theorem zero_ring_parameter : IsRegular (0 : ZMod 1) :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩

private theorem zero_ring_kernel (k : ℕ) :
    RingHom.ker (adicReduction (σ := Fin 2)
      (Ideal.span ({(0 : ZMod 1)} : Set (ZMod 1))) k) =
      Ideal.span ({principalAdicConstant (σ := Fin 2) (0 : ZMod 1) k} :
        Set (adicallyRestrictedSubring (σ := Fin 2)
          (Ideal.span ({(0 : ZMod 1)} : Set (ZMod 1))))) :=
  ker_adicReduction_principal 0 zero_ring_parameter k

private theorem regular_nonunit_product (k : ℕ) :
    RingHom.ker (adicReduction (σ := Fin 2)
      (Ideal.span ({((2, 1) : ℤ × ℤ)} : Set (ℤ × ℤ))) k) =
      Ideal.span ({principalAdicConstant (σ := Fin 2) ((2, 1) : ℤ × ℤ) k} :
        Set (adicallyRestrictedSubring (σ := Fin 2)
          (Ideal.span ({((2, 1) : ℤ × ℤ)} : Set (ℤ × ℤ))))) := by
  exact ker_adicReduction_principal (2, 1)
    (IsRegular.prodMk (IsRegular.of_ne_zero (by decide : (2 : ℤ) ≠ 0))
      isRegular_one) k

private theorem integer_quotient_isomorphism (a : ℤ) (ha : IsRegular a) (k : ℕ) :
    Nonempty
      ((adicallyRestrictedSubring (σ := Fin 2) (Ideal.span ({a} : Set ℤ))) ⧸
          Ideal.span ({principalAdicConstant (σ := Fin 2) a k} :
            Set (adicallyRestrictedSubring (σ := Fin 2)
              (Ideal.span ({a} : Set ℤ)))) ≃+*
        MvPolynomial (Fin 2) (ℤ ⧸ (Ideal.span ({a} : Set ℤ)) ^ k)) := by
  rw [← ker_adicReduction_principal (σ := Fin 2) a ha k]
  exact ⟨RingHom.quotientKerEquivOfSurjective
    (adicReduction_surjective (σ := Fin 2) (Ideal.span ({a} : Set ℤ)) k)⟩

private theorem integer_quotient_representative (a : ℤ) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := Fin 2) (Ideal.span ({a} : Set ℤ))) :
    (RingHom.quotientKerEquivOfSurjective
      (adicReduction_surjective (σ := Fin 2) (Ideal.span ({a} : Set ℤ)) k))
      (Ideal.Quotient.mk _ f) =
        adicReduction (Ideal.span ({a} : Set ℤ)) k f :=
  RingHom.quotientKerEquivOfSurjective_apply_mk _ f

end FormalPowerSeriesTests.MvPowerSeries.IdealAdicRestricted.PrincipalKernel

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.InverseLimit
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Maps between coefficient-adic polynomial completions

A coefficient homomorphism sending `I` into `J` and an arbitrary map of variables
induce a homomorphism between the polynomial completions at the extended
coefficient ideals. This is `AdicCompletion.mapRingHom` applied to polynomial
coefficient change followed by polynomial renaming. Its quotient-polynomial
square holds at every natural precision, including zero.

The completed original coefficient maps commute with this homomorphism. They
are written as the canonical `AdicCompletion.mapRingHom` values defining
`AdicCompletion.extendedAlgebra`, so no additional algebra instance is needed.
No finiteness, completeness, separation or condition on variable fibers is used.

## References

The construction uses AdicModules' `AdicCompletion.mapRingHom` and its
functoriality, Mathlib's polynomial coefficient maps and renaming, and this
library's `MvPowerSeries.adicPolynomialLevelEquiv`.
-/

@[expose] public section

noncomputable section

universe uR uT uU uσ uτ uυ

namespace MvPolynomial

section CoefficientIdeal

variable {R : Type uR} {T : Type uT} [CommSemiring R] [CommSemiring T]
variable {σ : Type uσ} {τ : Type uτ}

/-- Coefficient change and variable renaming send the extended source ideal
into the extended target ideal whenever the coefficient map sends `I` into `J`. -/
theorem map_C_le_comap_rename_map (I : Ideal R) (J : Ideal T)
    (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ) :
    I.map (C : R →+* MvPolynomial σ R) ≤
      (J.map (C : T →+* MvPolynomial τ T)).comap
        ((rename g).toRingHom.comp (map f)) := by
  apply Ideal.map_le_iff_le_comap.2
  intro r hr
  change rename g (map f (C r)) ∈ J.map (C : T →+* MvPolynomial τ T)
  rw [map_C, rename_C]
  exact Ideal.mem_map_of_mem (C : T →+* MvPolynomial τ T) (hf hr)

private theorem rename_map_id :
    (rename (R := R) (id : σ → σ)).toRingHom.comp (map (RingHom.id R)) =
      RingHom.id (MvPolynomial σ R) := by
  apply RingHom.ext
  intro p
  change rename id (map (RingHom.id R) p) = p
  rw [map_id, rename_id_apply]

private theorem rename_map_comp_C (f : R →+* T) (g : σ → τ) :
    ((rename g).toRingHom.comp (map f)).comp (C : R →+* MvPolynomial σ R) =
      (C : T →+* MvPolynomial τ T).comp f := by
  apply RingHom.ext
  intro r
  change rename g (map f (C r)) = C (f r)
  rw [map_C, rename_C]

private theorem rename_map_comp {U : Type uU} [CommSemiring U]
    {υ : Type uυ} (f : R →+* T) (k : T →+* U) (g : σ → τ) (h : τ → υ) :
    ((rename h).toRingHom.comp (map k)).comp
        ((rename g).toRingHom.comp (map f)) =
      (rename (h ∘ g)).toRingHom.comp (map (k.comp f)) := by
  apply RingHom.ext
  intro p
  change rename h (map k (rename g (map f p))) =
    rename (h ∘ g) (map (k.comp f) p)
  rw [map_rename, rename_rename, map_map]

end CoefficientIdeal

variable {R : Type uR} {T : Type uT} [CommRing R] [CommRing T]
variable {σ : Type uσ} {τ : Type uτ}

/-- The homomorphism between polynomial completions induced by coefficient
change and an arbitrary map of variables. It is the stock completed ring map
of polynomial coefficient change followed by polynomial renaming. -/
def adicCompletionMap (I : Ideal R) (J : Ideal T) (f : R →+* T)
    (hf : I ≤ J.comap f) (g : σ → τ) :
    AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R) →+*
      AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T) :=
  AdicCompletion.mapRingHom
    (I.map (C : R →+* MvPolynomial σ R))
    (J.map (C : T →+* MvPolynomial τ T))
    ((rename g).toRingHom.comp (map f)) (map_C_le_comap_rename_map I J f hf g)

/-- Original polynomials are sent to their coefficientwise images with renamed
variables. -/
@[simp]
theorem adicCompletionMap_of (I : Ideal R) (J : Ideal T) (f : R →+* T)
    (hf : I ≤ J.comap f) (g : σ → τ) (p : MvPolynomial σ R) :
    adicCompletionMap I J f hf g
        (AdicCompletion.of (I.map (C : R →+* MvPolynomial σ R))
          (MvPolynomial σ R) p) =
      AdicCompletion.of (J.map (C : T →+* MvPolynomial τ T))
        (MvPolynomial τ T) (rename g (map f p)) :=
  AdicCompletion.mapRingHom_of _ _ _ _ p

/-- The original constant polynomial `C r` maps to `C (f r)` in completion. -/
theorem adicCompletionMap_of_C (I : Ideal R) (J : Ideal T) (f : R →+* T)
    (hf : I ≤ J.comap f) (g : σ → τ) (r : R) :
    adicCompletionMap I J f hf g
        (AdicCompletion.of (I.map (C : R →+* MvPolynomial σ R))
          (MvPolynomial σ R) (C r)) =
      AdicCompletion.of (J.map (C : T →+* MvPolynomial τ T))
        (MvPolynomial τ T) (C (f r)) := by
  rw [adicCompletionMap_of, map_C, rename_C]

/-- Original variables map according to the chosen variable map. -/
theorem adicCompletionMap_of_X (I : Ideal R) (J : Ideal T) (f : R →+* T)
    (hf : I ≤ J.comap f) (g : σ → τ) (i : σ) :
    adicCompletionMap I J f hf g
        (AdicCompletion.of (I.map (C : R →+* MvPolynomial σ R))
          (MvPolynomial σ R) (X i)) =
      AdicCompletion.of (J.map (C : T →+* MvPolynomial τ T))
        (MvPolynomial τ T) (X (g i)) := by
  rw [adicCompletionMap_of, map_X, rename_X]

/-- Raw evaluation of the completed polynomial map is the induced quotient map. -/
theorem evalₐ_adicCompletionMap (I : Ideal R) (J : Ideal T) (f : R →+* T)
    (hf : I ≤ J.comap f) (g : σ → τ) (n : ℕ)
    (x : AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) :
    AdicCompletion.evalₐ (J.map (C : T →+* MvPolynomial τ T)) n
        (adicCompletionMap I J f hf g x) =
      Ideal.quotientMap ((J.map (C : T →+* MvPolynomial τ T)) ^ n)
        ((rename g).toRingHom.comp (map f))
        ((Ideal.pow_right_mono (map_C_le_comap_rename_map I J f hf g) n).trans
          (Ideal.le_comap_pow ((rename g).toRingHom.comp (map f)) n))
        (AdicCompletion.evalₐ (I.map (C : R →+* MvPolynomial σ R)) n x) :=
  AdicCompletion.evalₐ_mapRingHom _ _ _ _ n x

/-- The polynomial quotient equivalence commutes with coefficient change and
renaming, on every element of the original polynomial quotient. -/
theorem adicPolynomialLevelEquiv_quotientMap
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f)
    (g : σ → τ) (n : ℕ)
    (x : MvPolynomial σ R ⧸ (I.map (C : R →+* MvPolynomial σ R)) ^ n) :
    MvPowerSeries.adicPolynomialLevelEquiv J n
        (Ideal.quotientMap ((J.map (C : T →+* MvPolynomial τ T)) ^ n)
          ((rename g).toRingHom.comp (map f))
          ((Ideal.pow_right_mono (map_C_le_comap_rename_map I J f hf g) n).trans
            (Ideal.le_comap_pow ((rename g).toRingHom.comp (map f)) n)) x) =
      rename g (map (Ideal.quotientMap (J ^ n) f
        ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow f n)))
        (MvPowerSeries.adicPolynomialLevelEquiv I n x)) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.quotientMap_mk, MvPowerSeries.adicPolynomialLevelEquiv_mk]
  change map (Ideal.Quotient.mk (J ^ n)) (rename g (map f p)) =
    rename g (map (Ideal.quotientMap (J ^ n) f
      ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow f n)))
      (map (Ideal.Quotient.mk (I ^ n)) p))
  simp only [map_rename, map_map, Ideal.quotientMap_comp_mk]

/-- At every precision, including zero, the completed polynomial map becomes
polynomial coefficient change followed by renaming. -/
@[simp]
theorem adicPolynomialLevelEquiv_evalₐ_adicCompletionMap
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f)
    (g : σ → τ) (n : ℕ)
    (x : AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) :
    MvPowerSeries.adicPolynomialLevelEquiv J n
        (AdicCompletion.evalₐ (J.map (C : T →+* MvPolynomial τ T)) n
          (adicCompletionMap I J f hf g x)) =
      rename g (map (Ideal.quotientMap (J ^ n) f
        ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow f n)))
        (MvPowerSeries.adicPolynomialLevelEquiv I n
          (AdicCompletion.evalₐ (I.map (C : R →+* MvPolynomial σ R)) n x))) := by
  rw [evalₐ_adicCompletionMap]
  exact adicPolynomialLevelEquiv_quotientMap I J f hf g n _

/-- The all-precision polynomial squares uniquely determine the completed map. -/
theorem eq_adicCompletionMap (I : Ideal R) (J : Ideal T) (f : R →+* T)
    (hf : I ≤ J.comap f) (g : σ → τ)
    (H : AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R) →+*
      AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T))
    (hH : ∀ (n : ℕ) (x : AdicCompletion
        (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)),
      MvPowerSeries.adicPolynomialLevelEquiv J n
          (AdicCompletion.evalₐ (J.map (C : T →+* MvPolynomial τ T)) n (H x)) =
        rename g (map (Ideal.quotientMap (J ^ n) f
          ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow f n)))
          (MvPowerSeries.adicPolynomialLevelEquiv I n
            (AdicCompletion.evalₐ (I.map (C : R →+* MvPolynomial σ R)) n x)))) :
    H = adicCompletionMap I J f hf g := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  apply (MvPowerSeries.adicPolynomialLevelEquiv (σ := τ) J n).injective
  exact (hH n x).trans
    (adicPolynomialLevelEquiv_evalₐ_adicCompletionMap I J f hf g n x).symm

/-- Completing the identity coefficient map and identity variable map gives
the identity ring homomorphism. -/
@[simp]
theorem adicCompletionMap_id (I : Ideal R) :
    adicCompletionMap I I (RingHom.id R) (by intro r hr; exact hr) (id : σ → σ) =
      RingHom.id (AdicCompletion (I.map (C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R)) := by
  simpa only [adicCompletionMap, rename_map_id] using
    AdicCompletion.mapRingHom_id (I.map (C : R →+* MvPolynomial σ R))

/-- Completed polynomial maps compose in the order of coefficient maps and
variable maps. The composite ideal bound is derived from the two given bounds. -/
theorem adicCompletionMap_comp {U : Type uU} [CommRing U] {υ : Type uυ}
    (I : Ideal R) (J : Ideal T) (L : Ideal U) (f : R →+* T) (k : T →+* U)
    (hf : I ≤ J.comap f) (hk : J ≤ L.comap k) (g : σ → τ) (h : τ → υ) :
    (adicCompletionMap J L k hk h).comp (adicCompletionMap I J f hf g) =
      adicCompletionMap I L (k.comp f) (by intro r hr; exact hk (hf hr)) (h ∘ g) := by
  simpa only [adicCompletionMap, rename_map_comp] using
    AdicCompletion.mapRingHom_comp
      (I.map (C : R →+* MvPolynomial σ R))
      (J.map (C : T →+* MvPolynomial τ T))
      (L.map (C : U →+* MvPolynomial υ U))
      ((rename g).toRingHom.comp (map f))
      ((rename h).toRingHom.comp (map k))
      (map_C_le_comap_rename_map I J f hf g)
      (map_C_le_comap_rename_map J L k hk h)

/-- The completed polynomial map commutes with the completed original
coefficient maps defining `AdicCompletion.extendedAlgebra`. This is an equality
of ring maps and requires no algebra instance on either polynomial completion. -/
theorem adicCompletionMap_comp_completedCoefficient
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ) :
    (adicCompletionMap I J f hf g).comp
        (AdicCompletion.mapRingHom I (I.map (C : R →+* MvPolynomial σ R))
          (C : R →+* MvPolynomial σ R) Ideal.le_comap_map) =
      (AdicCompletion.mapRingHom J (J.map (C : T →+* MvPolynomial τ T))
        (C : T →+* MvPolynomial τ T) Ideal.le_comap_map).comp
          (AdicCompletion.mapRingHom I J f hf) := by
  simp only [adicCompletionMap, AdicCompletion.mapRingHom_comp, rename_map_comp_C]

/-- Apply the completed coefficient commutation square to a completed original
coefficient. -/
@[simp]
theorem adicCompletionMap_completedCoefficient
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f)
    (g : σ → τ) (a : AdicCompletion I R) :
    adicCompletionMap I J f hf g
        (AdicCompletion.mapRingHom I (I.map (C : R →+* MvPolynomial σ R))
          (C : R →+* MvPolynomial σ R) Ideal.le_comap_map a) =
      AdicCompletion.mapRingHom J (J.map (C : T →+* MvPolynomial τ T))
        (C : T →+* MvPolynomial τ T) Ideal.le_comap_map
        (AdicCompletion.mapRingHom I J f hf a) :=
  RingHom.congr_fun (adicCompletionMap_comp_completedCoefficient I J f hf g) a

/-- Multiplication by a completed original coefficient is transported through
the completed coefficient map, without choosing an algebra instance. -/
theorem adicCompletionMap_completedCoefficient_mul
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f)
    (g : σ → τ) (a : AdicCompletion I R)
    (x : AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) :
    adicCompletionMap I J f hf g
        (AdicCompletion.mapRingHom I (I.map (C : R →+* MvPolynomial σ R))
          (C : R →+* MvPolynomial σ R) Ideal.le_comap_map a * x) =
      AdicCompletion.mapRingHom J (J.map (C : T →+* MvPolynomial τ T))
        (C : T →+* MvPolynomial τ T) Ideal.le_comap_map
        (AdicCompletion.mapRingHom I J f hf a) * adicCompletionMap I J f hf g x := by
  rw [map_mul, adicCompletionMap_completedCoefficient]

/-- A vanishing raw quotient evaluation stays zero at the same precision after
coefficient change and renaming. No intrinsic kernel identification is needed. -/
theorem ker_evalₐ_le_comap_adicCompletionMap
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f)
    (g : σ → τ) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ (I.map (C : R →+* MvPolynomial σ R)) n :
        AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R) →+*
          MvPolynomial σ R ⧸ (I.map (C : R →+* MvPolynomial σ R)) ^ n) ≤
      (RingHom.ker (AdicCompletion.evalₐ (J.map (C : T →+* MvPolynomial τ T)) n :
        AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T) →+*
          MvPolynomial τ T ⧸ (J.map (C : T →+* MvPolynomial τ T)) ^ n)).comap
        (adicCompletionMap I J f hf g) := by
  intro x hx
  change AdicCompletion.evalₐ (I.map (C : R →+* MvPolynomial σ R)) n x = 0 at hx
  change AdicCompletion.evalₐ (J.map (C : T →+* MvPolynomial τ T)) n
    (adicCompletionMap I J f hf g x) = 0
  rw [evalₐ_adicCompletionMap, hx, map_zero]

end MvPolynomial

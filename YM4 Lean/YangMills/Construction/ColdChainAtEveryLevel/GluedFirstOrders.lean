import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PartitionGluing
variable {U T Z E : Type} [AddCommGroup E] [Module ℝ E]
def weighted (w : U → ℝ) (Y : U → E) : U → E := fun u => w u • Y u
def weightGap (φ : Z → U → ℝ) (φt : Z → T → ℝ) (z : Z) (t : T) : U → ℝ := fun u => φ z u - φt z t
theorem weighted_weightGap (φ : Z → U → ℝ) (φt : Z → T → ℝ) (z : Z) (t : T) (Y : U → E) :
    weighted (weightGap φ φt z t) Y = weighted (φ z) Y - φt z t • Y := by
  funext u
  simp [weighted, weightGap, sub_smul]
theorem weighted_sub (w : U → ℝ) (Y Y' : U → E) : weighted w (Y - Y') = weighted w Y - weighted w Y' := by
  funext u
  simp [weighted, smul_sub]
variable (A : Finset Z) (l : T → (U → E) →ₗ[ℝ] ℝ) (φ : Z → U → ℝ) (φt : Z → T → ℝ) (Y : Z → U → E)
  (Cm : Z → U → E)
def residual (t : T) : ℝ :=
  ∑ z ∈ A, l t (weighted (weightGap φ φt z t) (Y z)) + ∑ z ∈ A, l t (weighted (φ z) (Cm z))
theorem sum_weighted_eq_neg_sum_residual (Ts : Finset T) (hA : ∀ V : U → E, ∑ t ∈ Ts, l t V = 0) :
    ∑ z ∈ A, ∑ t ∈ Ts, φt z t * l t (Y z) = - ∑ t ∈ Ts, residual A l φ φt Y Cm t := by
  have h0 := hA (∑ z ∈ A, weighted (φ z) (Y z) + ∑ z ∈ A, weighted (φ z) (Cm z))
  have h1 : ∀ t, l t (∑ z ∈ A, weighted (φ z) (Y z) + ∑ z ∈ A, weighted (φ z) (Cm z)) =
      residual A l φ φt Y Cm t + ∑ z ∈ A, φt z t * l t (Y z) := by
    intro t
    unfold residual
    rw [map_add, map_sum, map_sum]
    have : ∀ z, l t (weighted (weightGap φ φt z t) (Y z)) = l t (weighted (φ z) (Y z)) - φt z t * l t (Y z) := by
      intro z
      rw [weighted_weightGap, map_sub, map_smul, smul_eq_mul]
    simp only [this, Finset.sum_sub_distrib]
    ring
  simp only [h1, Finset.sum_add_distrib] at h0
  rw [Finset.sum_comm]
  linarith
variable (G H : Z → Z → U → E)
def invariantCorrection (z₀ : Z) : U → E := ∑ z ∈ A, (H z z₀ - weighted (φ z) (G z z₀))
variable {A l φ φt Y Cm G H}
theorem map_weighted_weightGap_of_invariant {t : T} {z z₀ : Z} (hG : l t (G z z₀) = 0) (hH : l t (H z z₀) = 0) :
    l t (weighted (weightGap φ φt z t) (G z z₀)) = - l t (H z z₀ - weighted (φ z) (G z z₀)) := by
  rw [weighted_weightGap, map_sub, map_sub, map_smul, hG, hH]
  simp
theorem map_invariantCorrection {t : T} {z₀ : Z} (hG : ∀ z ∈ A, l t (G z z₀) = 0)
    (hH : ∀ z ∈ A, l t (H z z₀) = 0) :
    l t (invariantCorrection A φ G H z₀) = - ∑ z ∈ A, l t (weighted (weightGap φ φt z t) (G z z₀)) := by
  unfold invariantCorrection
  rw [map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [map_weighted_weightGap_of_invariant (hG z hz) (hH z hz), neg_neg]
theorem residual_invariantCorrection_eq {t : T} (hG : ∀ z ∈ A, ∀ z₀ ∈ A, l t (G z z₀) = 0)
    (hH : ∀ z ∈ A, ∀ z₀ ∈ A, l t (H z z₀) = 0) :
    residual A l φ φt Y (invariantCorrection A φ G H) t =
      ∑ z ∈ A, l t (weighted (weightGap φ φt z t) (Y z)) -
        ∑ z₀ ∈ A, φt z₀ t * ∑ z ∈ A, l t (weighted (weightGap φ φt z t) (G z z₀)) +
        ∑ z₀ ∈ A, l t (weighted (weightGap φ φt z₀ t) (invariantCorrection A φ G H z₀)) := by
  unfold residual
  have h : ∀ z₀ ∈ A, l t (weighted (φ z₀) (invariantCorrection A φ G H z₀)) =
      l t (weighted (weightGap φ φt z₀ t) (invariantCorrection A φ G H z₀)) -
        φt z₀ t * ∑ z ∈ A, l t (weighted (weightGap φ φt z t) (G z z₀)) := by
    intro z₀ hz₀
    rw [weighted_weightGap, map_sub, map_smul, smul_eq_mul,
      map_invariantCorrection (φt := φt) (fun z hz => hG z hz z₀ hz₀) (fun z hz => hH z hz z₀ hz₀)]
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib]
  ring
theorem sum_map_weighted_weightGap_eq_zero {t : T} {R : U → Prop}
    (hloc : ∀ V : U → E, (∀ u, R u → V u = 0) → l t V = 0)
    (hR : ∀ u, R u → ∑ z ∈ A, φ z u = 1) (h1 : ∑ z ∈ A, φt z t = 1) (V : U → E) :
    ∑ z ∈ A, l t (weighted (weightGap φ φt z t) V) = 0 := by
  rw [← map_sum]
  refine hloc _ fun u hu => ?_
  have : (∑ z ∈ A, weighted (weightGap φ φt z t) V) u = (∑ z ∈ A, (φ z u - φt z t)) • V u := by
    simp only [Finset.sum_apply, weighted, weightGap, Finset.sum_smul]
  rw [this, Finset.sum_sub_distrib, hR u hu, h1]
  simp
theorem residual_invariantCorrection_eq_of_partition {t : T} {R : U → Prop}
    (hG : ∀ z ∈ A, ∀ z₀ ∈ A, l t (G z z₀) = 0)
    (hH : ∀ z ∈ A, ∀ z₀ ∈ A, l t (H z z₀) = 0) (hloc : ∀ V : U → E, (∀ u, R u → V u = 0) → l t V = 0)
    (hR : ∀ u, R u → ∑ z ∈ A, φ z u = 1) (h1 : ∑ z ∈ A, φt z t = 1) (z₁ : Z) :
    residual A l φ φt Y (invariantCorrection A φ G H) t =
      ∑ z₀ ∈ A, φt z₀ t * ∑ z ∈ A, l t (weighted (weightGap φ φt z t) (Y z - Y z₀ - G z z₀)) +
        ∑ z₀ ∈ A, l t (weighted (weightGap φ φt z₀ t)
          (invariantCorrection A φ G H z₀ - invariantCorrection A φ G H z₁)) := by
  rw [residual_invariantCorrection_eq hG hH]
  have hs := sum_map_weighted_weightGap_eq_zero (φ := φ) (φt := φt) (A := A) hloc hR h1
  have e1 : ∀ z₀, ∑ z ∈ A, l t (weighted (weightGap φ φt z t) (Y z - Y z₀ - G z z₀)) =
      ∑ z ∈ A, l t (weighted (weightGap φ φt z t) (Y z)) -
        ∑ z ∈ A, l t (weighted (weightGap φ φt z t) (G z z₀)) := by
    intro z₀
    have : ∀ z, l t (weighted (weightGap φ φt z t) (Y z - Y z₀ - G z z₀)) =
        l t (weighted (weightGap φ φt z t) (Y z)) - l t (weighted (weightGap φ φt z t) (Y z₀)) -
          l t (weighted (weightGap φ φt z t) (G z z₀)) := by
      intro z
      rw [weighted_sub, weighted_sub, map_sub, map_sub]
    simp only [this, Finset.sum_sub_distrib, hs (Y z₀), sub_zero]
  have e2 : ∑ z₀ ∈ A, l t (weighted (weightGap φ φt z₀ t)
      (invariantCorrection A φ G H z₀ - invariantCorrection A φ G H z₁)) =
      ∑ z₀ ∈ A, l t (weighted (weightGap φ φt z₀ t) (invariantCorrection A φ G H z₀)) := by
    have : ∀ z₀, l t (weighted (weightGap φ φt z₀ t)
        (invariantCorrection A φ G H z₀ - invariantCorrection A φ G H z₁)) =
        l t (weighted (weightGap φ φt z₀ t) (invariantCorrection A φ G H z₀)) -
          l t (weighted (weightGap φ φt z₀ t) (invariantCorrection A φ G H z₁)) := by
      intro z₀
      rw [weighted_sub, map_sub]
    simp only [this, Finset.sum_sub_distrib, hs (invariantCorrection A φ G H z₁), sub_zero]
  rw [e2]
  simp only [e1, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
end YangMills.Construction.PartitionGluing
end

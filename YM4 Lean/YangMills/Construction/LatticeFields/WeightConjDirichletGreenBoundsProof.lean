import YangMills.Construction.LatticeFields.BlockAvgAdjoints
import YangMills.Construction.LatticeFields.ConjugatedDifferenceBound
import YangMills.Construction.LatticeFields.SobolevOneNormProducts
import YangMills.Construction.LatticeFields.WeightConjProjComplProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.LatticeFields
namespace WeightConjGreen
section InnerProduct
variable {d M : ℕ} {κ : LatticeShape d} {I : Type} [Fintype (LatticeSite M κ)] [Fintype I]
def toEuclidean (F : LatticeField M κ I) : EuclideanSpace ℝ (LatticeSite M κ × I) :=
  WithLp.toLp 2 fun p => Real.sqrt (latticeSpacing M ^ d) * F p.1 p.2
theorem latticeSpacing_pow_nonneg_aux : 0 ≤ latticeSpacing M ^ d := by
  unfold latticeSpacing
  positivity
theorem inner_toEuclidean (F G : LatticeField M κ I) :
    inner ℝ (toEuclidean F) (toEuclidean G) = fieldInner F G := by
  have hw : Real.sqrt (latticeSpacing M ^ d) * Real.sqrt (latticeSpacing M ^ d) =
      latticeSpacing M ^ d :=
    Real.mul_self_sqrt latticeSpacing_pow_nonneg_aux
  rw [fieldInner, tsum_fintype, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [toEuclidean, RCLike.inner_apply, conj_trivial]
  linear_combination (F p.1 p.2 * G p.1 p.2) * hw
theorem fieldNorm_eq_euclidean (F : LatticeField M κ I) : fieldNorm F = ‖toEuclidean F‖ := by
  rw [fieldNorm, ← inner_toEuclidean, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
theorem toEuclidean_add (F G : LatticeField M κ I) :
    toEuclidean (F + G) = toEuclidean F + toEuclidean G := by
  ext p
  simp [toEuclidean, mul_add]
theorem toEuclidean_sub (F G : LatticeField M κ I) :
    toEuclidean (F - G) = toEuclidean F - toEuclidean G := by
  ext p
  simp [toEuclidean, mul_sub]
theorem fieldInner_sub_right_aux (F G G' : LatticeField M κ I) :
    fieldInner F (G - G') = fieldInner F G - fieldInner F G' := by
  simp only [← inner_toEuclidean, toEuclidean_sub, inner_sub_right]
theorem fieldInner_sub_left_aux (F F' G : LatticeField M κ I) :
    fieldInner (F - F') G = fieldInner F G - fieldInner F' G := by
  simp only [← inner_toEuclidean, toEuclidean_sub, inner_sub_left]
theorem fieldInner_comm_aux (F G : LatticeField M κ I) : fieldInner F G = fieldInner G F := by
  simp only [← inner_toEuclidean]
  exact real_inner_comm _ _
theorem abs_fieldInner_le_aux (F G : LatticeField M κ I) :
    |fieldInner F G| ≤ fieldNorm F * fieldNorm G := by
  simp only [← inner_toEuclidean, fieldNorm_eq_euclidean]
  exact abs_real_inner_le_norm _ _
theorem fieldNorm_nonneg_aux (F : LatticeField M κ I) : 0 ≤ fieldNorm F := Real.sqrt_nonneg _
theorem fieldInner_self_aux (F : LatticeField M κ I) : fieldInner F F = fieldNorm F ^ 2 := by
  simp only [← inner_toEuclidean, fieldNorm_eq_euclidean]
  exact real_inner_self_eq_norm_sq _
theorem eq_zero_of_fieldNorm_eq_zero_aux [NeZero M] (F : LatticeField M κ I)
    (h : fieldNorm F = 0) : F = 0 := by
  have hs : 0 < Real.sqrt (latticeSpacing M ^ d) := by
    refine Real.sqrt_pos.mpr (pow_pos ?_ d)
    have : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
    exact inv_pos.mpr this
  rw [fieldNorm_eq_euclidean, norm_eq_zero] at h
  funext x i
  have hp : (toEuclidean F) (x, i) = 0 := by rw [h]; rfl
  have hq : Real.sqrt (latticeSpacing M ^ d) * F x i = 0 := hp
  exact (mul_eq_zero.mp hq).resolve_left hs.ne'
theorem abs_fieldInner_sub_le_of_near {F' F G' G : LatticeField M κ I} {e' e : ℝ}
    (h' : fieldNorm (F' - G') ≤ e') (h : fieldNorm (F - G) ≤ e) :
    |fieldInner F' F - fieldInner G' G| ≤
      e' * fieldNorm G + fieldNorm G' * e + e' * e := by
  have id : fieldInner F' F - fieldInner G' G =
      fieldInner (F' - G') G + fieldInner G' (F - G) + fieldInner (F' - G') (F - G) := by
    simp only [fieldInner_sub_left_aux, fieldInner_sub_right_aux]
    ring
  have h1 : |fieldInner (F' - G') G| ≤ e' * fieldNorm G :=
    (abs_fieldInner_le_aux _ _).trans (mul_le_mul_of_nonneg_right h' (fieldNorm_nonneg_aux _))
  have h2 : |fieldInner G' (F - G)| ≤ fieldNorm G' * e :=
    (abs_fieldInner_le_aux _ _).trans (mul_le_mul_of_nonneg_left h (fieldNorm_nonneg_aux _))
  have h3 : |fieldInner (F' - G') (F - G)| ≤ e' * e :=
    (abs_fieldInner_le_aux _ _).trans
      (mul_le_mul h' h (fieldNorm_nonneg_aux _) ((fieldNorm_nonneg_aux _).trans h'))
  obtain ⟨l1, u1⟩ := abs_le.mp h1
  obtain ⟨l2, u2⟩ := abs_le.mp h2
  obtain ⟨l3, u3⟩ := abs_le.mp h3
  rw [id]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
end InnerProduct
section BaseMultiplication
variable {d M : ℕ} {κ : LatticeShape d} {I : Type}
end BaseMultiplication
section GreenCore
variable {d N : ℕ} [NeZero N] {κ : LatticeShape d} [Fintype (LatticeSite N κ)]
end GreenCore
section ConjugatePairs
variable {d N : ℕ} [NeZero N] {κ : LatticeShape d}
theorem tensorGrad_eq_latticeGrad (f : ScalarField N κ) : tensorGrad f = latticeGrad f := by
  funext x i
  exact congrArg (forwardDiff (i 0) f x) (Subsingleton.elim _ _)
end ConjugatePairs
end WeightConjGreen
end YangMills.Construction.LatticeFields

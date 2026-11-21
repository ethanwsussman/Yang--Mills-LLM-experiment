import YangMills.Construction.ColdStepAtMirrorFrames.BlockMeansOfFormsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
theorem plaquetteCurl_latticeGradient {j : ℕ} (φ : F.Site j → ℝ) (x : F.Site j) (k l : Fin 4) :
    plaquetteCurl (latticeGradient φ) x k l = 0 := by
  unfold plaquetteCurl latticeGradient
  rw [add_right_comm x (unitStep j l)]
  ring
theorem plaquetteCurl_sub {j : ℕ} (B D : LevelForm F j) (x : F.Site j) (k l : Fin 4) :
    plaquetteCurl (B - D) x k l = plaquetteCurl B x k l - plaquetteCurl D x k l := by
  simp only [plaquetteCurl, Pi.sub_apply]
  ring
theorem sum_abs_mul_abs_le_sqrt_mul_sqrt {α : Type*} (s : Finset α) (f g : α → ℝ) :
    ∑ x ∈ s, |f x| * |g x| ≤ Real.sqrt (∑ x ∈ s, f x ^ 2) * Real.sqrt (∑ x ∈ s, g x ^ 2) := by
  have h0 := Finset.sum_mul_sq_le_sq_mul_sq s (fun x => |f x|) (fun x => |g x|)
  simp only [sq_abs] at h0
  have h1 := Real.abs_le_sqrt h0
  rw [Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h1
  exact (le_abs_self _).trans h1
theorem sum_sq_component_le_weightedNormSq {j : ℕ} (w : F.Site j → ℝ) (B : LevelForm F j)
    (l : Fin 4) :
    ∑ x ∈ allSites F j, (w x * B x l) ^ 2 ≤ weightedNormSq w B := by
  refine Finset.sum_le_sum fun x _ => ?_
  exact Finset.single_le_sum (f := fun i => (w x * B x i) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ l)
theorem plaquetteCurl_mul_left (W : F.Site 0 → ℝ) (B : LevelForm F 0) (x : F.Site 0) (k l : Fin 4) :
    plaquetteCurl (fun x i => W x * B x i : LevelForm F 0) x k l = W x * plaquetteCurl B x k l +
      (W (x + unitStep 0 k) - W x) * B (x + unitStep 0 k) l -
      (W (x + unitStep 0 l) - W x) * B (x + unitStep 0 l) k := by
  unfold plaquetteCurl
  ring
theorem card_orientedPlanes : orientedPlanes.card = 6 := by
  decide
end ColdStepAtMirrorFrames
end YangMills.Construction
end

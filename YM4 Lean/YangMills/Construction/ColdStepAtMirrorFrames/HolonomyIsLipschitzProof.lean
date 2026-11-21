import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.ColdStepAtMirrorFrames.HolonomyIsLipschitz
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace PathHolonomy
theorem norm_inv_sub_inv (g h : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((h⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(g : ℍ[ℝ]) - (h : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
theorem norm_mul_sub_mul_le (g g' h h' : UnitQuaternion) :
    ‖((g * h : UnitQuaternion) : ℍ[ℝ]) - ((g' * h' : UnitQuaternion) : ℍ[ℝ])‖ ≤
    ‖(g : ℍ[ℝ]) - (g' : ℍ[ℝ])‖ + ‖(h : ℍ[ℝ]) - (h' : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.coe_mul_sub_mul_le <;> assumption
end PathHolonomy
open PathHolonomy in
theorem pathHolonomyLipschitz_holds : PathHolonomyLipschitz := by
  intro F j X X' ε h x l
  induction l generalizing x with
  | nil => simp [pathHolonomy]
  | cons st r ih =>
    simp only [pathHolonomy, List.length_cons]
    refine (norm_mul_sub_mul_le _ _ _ _).trans ?_
    have h1 : ‖((linkValue X x st : UnitQuaternion) : ℍ[ℝ]) - ((linkValue X' x st : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
      unfold linkValue
      split_ifs
      · exact h _ _
      · rw [norm_inv_sub_inv]
        exact h _ _
    have h2 := ih (x + stepDisplacement j st)
    push_cast
    linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end

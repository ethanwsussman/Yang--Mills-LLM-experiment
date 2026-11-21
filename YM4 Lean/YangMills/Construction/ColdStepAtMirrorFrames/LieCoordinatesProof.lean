import YangMills.Construction.ClusterExpansionOfAStep.MovesOfFreeBondsForm
import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenBoundsProof
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexAboveAChartPointProof
import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace ImaginaryCoordinates
theorem toImaginary_add (u v : BondVector) : toImaginary (u + v) = toImaginary u + toImaginary v := by apply _root_.YangMills.Construction.FreeBondMoves.toImaginary_add <;> assumption
theorem toImaginary_smul (c : ℝ) (v : BondVector) : toImaginary (c • v) = c • toImaginary v := by apply _root_.YangMills.Construction.FreeBondMoves.toImaginary_smul <;> assumption
theorem norm_toImaginary (v : BondVector) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem exists_toImaginary_eq (q : imaginaryQuaternions) : ∃ v : BondVector, toImaginary v = q := by
  refine ⟨!₂[(q : ℍ[ℝ]).imI, (q : ℍ[ℝ]).imJ, (q : ℍ[ℝ]).imK], ?_⟩
  apply Subtype.ext
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
  · exact q.2.symm
  · rfl
  · rfl
  · rfl
variable {F : BlockFrame}
theorem stepCoordinates_add (η ζ : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (η + ζ) x i = stepCoordinates η x i + stepCoordinates ζ x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_add <;> assumption
end ImaginaryCoordinates
open ImaginaryCoordinates in
theorem imaginaryCoordinatesIsometric_of_blocksCover (hcover : BlocksCoverLowerLevel) :
    ImaginaryCoordinatesIsometric := by
  refine ⟨toImaginary_add, toImaginary_smul, norm_toImaginary, exists_toImaginary_eq, ?_, ?_, ?_⟩
  · intro F w η ζ
    funext x i
    simp only [shiftCoordinates, stepCoordinates_add, add_assoc]
  · intro F w
    funext x i
    have hzero : stepCoordinates (0 : StepVariable (finiteCells F)) x i = 0 := by
      unfold stepCoordinates
      split_ifs
      · apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;> rfl
      · rfl
    simp [shiftCoordinates, hzero]
  · intro F w w₂ V hodd hside hagree
    funext x i
    unfold chartedField
    have hmem : ∀ y : F.Site F.depth, y ∈ sitesOfCells (finiteCells F) F.depth := hcover F hodd hside
    have hchord : ¬ IsAxialTreeBond (x, i) → (x, i) ∈ chordBonds (finiteCells F) := fun htree => by
      unfold chordBonds innerBonds
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, hmem, true_and]
      exact htree
    by_cases hcross : IsCrossingBond (x, i)
    · have htree : ¬ IsAxialTreeBond (x, i) := fun htree => htree.1 hcross
      have hxi := hagree _ (hchord htree)
      simp only [if_pos hcross]
      rw [show w x i = w₂ x i from hxi]
    · by_cases htree : IsAxialTreeBond (x, i)
      · simp only [if_neg hcross, if_pos htree]
      · have hxi := hagree _ (hchord htree)
        simp only [if_neg hcross, if_neg htree]
        rw [show w x i = w₂ x i from hxi]
end ColdStepAtMirrorFrames
end YangMills.Construction
end

import YangMills.Construction.Splines.CubicSplineBasicFacts
import YangMills.Construction.TwoPoints.ShapeConstantInTheUnitInterval
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints.Shapes
open YangMills.Construction.Splines (cubicSpline cubicSplineIntegral)
namespace ShapeConstMemIoc
theorem derivUniformNorm_nonneg (f : ℝ → ℂ) : 0 ≤ YangMills.Construction.TwoPoints.derivUniformNorm f := by
  unfold YangMills.Construction.TwoPoints.derivUniformNorm YangMills.Construction.TestFunctions.uniformNorm
  exact Real.iSup_nonneg fun _ => norm_nonneg _
theorem gradPlaneSup_nonneg (f : (Fin 2 → ℝ) → ℂ) : 0 ≤ YangMills.Construction.TwoPoints.gradPlaneSup f :=
  ENNReal.toReal_nonneg
theorem holds (hE : ShapesExist.Statement)
    (hB : YangMills.Construction.Splines.CubicSplineBasicFacts) : Statement := by
  obtain ⟨-, -, -, -, ha, hb, hψ, hψ', ha0, -, hP⟩ := hE
  obtain ⟨-, -, ⟨-, -, hI⟩, -⟩ := hB
  have hb0 := derivUniformNorm_nonneg (ofRealFun cubicSpline)
  have hg := gradPlaneSup_nonneg (ofRealFun planePlateau)
  have hg' := gradPlaneSup_nonneg (ofRealFun planePartitionOfUnity)
  have hlow : 0 < lowerShapeBound := by
    unfold lowerShapeBound
    linarith
  have hup : 0 < upperShapeBound := by
    unfold upperShapeBound
    linarith
  have hfirst : 0 < shapeCoeffOne * (∫ s, cubicSpline s) * ∫ ζ, planePlateau ζ := by
    have hc : 0 < shapeCoeffOne := by
      unfold shapeCoeffOne
      norm_num
    positivity
  have hsecond : 0 < shapeCoeffTwo / lowerShapeBound :=
    div_pos (by unfold shapeCoeffTwo; norm_num) hlow
  have hthird : 0 < shapeCoeffThree / upperShapeBound :=
    div_pos (by unfold shapeCoeffThree; norm_num) hup
  refine ⟨ha, hb, hψ, hψ', hlow, hup, ?_, ?_⟩
  · unfold shapeConst
    exact lt_min one_pos (lt_min hfirst (lt_min hsecond hthird))
  · unfold shapeConst
    exact min_le_left _ _
end ShapeConstMemIoc
end YangMills.Construction.TwoPoints.Shapes

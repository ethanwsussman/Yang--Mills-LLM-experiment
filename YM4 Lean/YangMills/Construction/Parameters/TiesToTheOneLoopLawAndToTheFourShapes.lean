import YangMills.Construction.OneLoopLaw.TheOneLoopLaw
import YangMills.Construction.TwoPoints.FourShapesAndTheShapeConstant
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ParameterChoice
structure TiedToOneLoopLawAndShapes (T : YangMills.Construction.ParameterChoice.DerivedConstants) :
    Prop where
  coefficient_eq : ∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
    T.c₂ L = YangMills.Construction.OneLoopLaw.shiftSumBound L
  shapeConst_eq : T.ϑ₀ = YangMills.Construction.TwoPoints.Shapes.shapeConst
end YangMills.Construction.ParameterChoice
end

import YangMills.Construction.TwoPoints.FourShapesAndTheShapeConstant
import Mathlib
open Set
open scoped ENNReal
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints.Shapes
open Splines (cubicSpline)
def ShapeConstMemIoc.Statement : Prop :=
  BddDeriv timeBump ∧
  BddDeriv cubicSpline ∧
  gradPlaneEsup (ofRealFun planePartitionOfUnity) ≠ ∞ ∧
  gradPlaneEsup (ofRealFun planePlateau) ≠ ∞ ∧
  0 < lowerShapeBound ∧
  0 < upperShapeBound ∧
  shapeConst ∈ Ioc (0 : ℝ) 1
end YangMills.Construction.TwoPoints.Shapes
end

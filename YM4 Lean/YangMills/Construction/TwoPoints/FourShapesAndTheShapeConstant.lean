import YangMills.Construction.TwoPoints.SmoothedIndicatorsAndTheThreeShapes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints.Shapes
open YangMills.Construction.Splines (cubicSpline)
def lowerShapeBound : ℝ :=
  derivUniformNorm (ofRealFun timeBump) + 4 * derivUniformNorm (ofRealFun cubicSpline) +
    gradPlaneSup (ofRealFun planePlateau)
def upperShapeBound : ℝ :=
  3 * derivUniformNorm (ofRealFun timeBump) + 12 * derivUniformNorm (ofRealFun cubicSpline) +
    2 * gradPlaneSup (ofRealFun planePlateau) + gradPlaneSup (ofRealFun planePartitionOfUnity) + 1
def shapeCoeffOne : ℝ := 2 / 1875
def shapeCoeffTwo : ℝ := 2 / 5
def shapeCoeffThree : ℝ := 2 / 5
def shapeConst : ℝ :=
  min 1 (min (shapeCoeffOne * (∫ s, cubicSpline s) * ∫ ζ, planePlateau ζ)
    (min (shapeCoeffTwo / lowerShapeBound) (shapeCoeffThree / upperShapeBound)))
end YangMills.Construction.TwoPoints.Shapes

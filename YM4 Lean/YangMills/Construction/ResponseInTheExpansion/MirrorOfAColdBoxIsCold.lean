import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import YangMills.Construction.ResponseInTheExpansion.MirrorLawOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.TorusFields YangMills.Construction.BlockAverages
def mirrorOfColdBallSmallCurvatureStatement : Prop :=
  ∀ (L t m n : ℕ) [NeZero n] (o : TorusSite n) (V : TorusField n) (g : TorusSite n → UnitQuaternion) (s : ℝ),
    0 < s → 0 < m → 2 * m + 2 < n → Odd L → IsColdOnBall s V o m →
      ColdStepAtMirrorFrames.IsSmallCurvature s (reflectedTopField L t m o (TorusFields.gaugeTransform g V))
end YangMills.Construction.ResponseInTheExpansion
end

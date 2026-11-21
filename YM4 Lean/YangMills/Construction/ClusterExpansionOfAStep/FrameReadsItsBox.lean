import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepCosts
namespace FrameLocality
def FrameCoordLocal : Prop :=
  ∀ (ℓ : StepParameters) (ρA : ℝ) (t m n n' : ℕ) [NeZero n] [NeZero n'] (V : TorusField n) (V' : TorusField n')
    (b : TorusBond (n * ℓ.side)) (b' : TorusBond (n' * ℓ.side)), ℓ.Admissible → 0 < m → 4 * m + 5 < n →
    4 * m + 5 < n' → b.2 = b'.2 →
    cellOffset (F := torusFrame ℓ.side t n)
        (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1) =
      cellOffset (F := torusFrame ℓ.side t n')
        (torusSiteInFrame (torusFrame ℓ.side t n') (torusFrame ℓ.side t n').depth b'.1) →
    FieldsAgreeNear V V' (parentBlock ℓ.side b.1) (parentBlock ℓ.side b'.1) m →
    frameCoord ℓ ρA t m V b = frameCoord ℓ ρA t m V' b'
end FrameLocality
end YangMills.Construction
end

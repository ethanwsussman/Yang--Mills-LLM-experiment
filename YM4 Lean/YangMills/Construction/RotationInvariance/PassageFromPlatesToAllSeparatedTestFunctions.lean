import YangMills.Construction.RotationInvariance.ComplexTuplesAndPlaneData
import YangMills.Construction.RotationInvariance.TopFrequencyOfTheHarmonics
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.RotationFromProducts
open RealPlane
def InvariantOnComplexTuples : Prop :=
  ∀ (M : SharpScale) (S : ConnFamily) (_ : ProductPlaneData M S) (α : openingAngles),
    (∀ k : ℕ, 2 ≤ k → maxFrequency S α k = 0) →
    ∀ k : ℕ, 2 ≤ k → ∀ t : ℝ, ∀ g ∈ disjointComplexTuples k,
      centeredFnFree S
          (complexTuple fun i => (rotateMotion t).actFn (g i)) =
        centeredFnFree S (complexTuple g)
end YangMills.Construction.EuclideanFunctionals.RotationFromProducts
end

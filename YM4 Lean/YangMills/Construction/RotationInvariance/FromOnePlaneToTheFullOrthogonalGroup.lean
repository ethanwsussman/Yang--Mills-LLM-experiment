import YangMills.Construction.EuclideanFunctionals.ElementOfTheOrthogonalGroupAsAnIsometry
import YangMills.Construction.RotationInvariance.ComplexTuplesAndPlaneData
import YangMills.Construction.RotationInvariance.TopFrequencyOfTheHarmonics
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror YangMills.Construction.RealPlane
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
def FullOrthogonalInvariance.Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (_ : ProductPlaneData m S) (φ₀ : openingAngles),
    (∀ n : ℕ, 2 ≤ n → maxFrequency S φ₀ n = 0) →
    ∀ (n : ℕ) (hn : 2 ≤ n) (R : Matrix.orthogonalGroup (Fin 4) ℝ),
      (∀ h ∈ disjointComplexTuples n,
        centeredFnFree S ((EuclidMotion.ofOrthogonalMatrix R).actFree (complexTuple h)) =
          centeredFnFree S (complexTuple h)) ∧
      ∀ X ∈ sepN n,
        Ambient.evalOrZero (S.fn n hn) ((EuclidMotion.ofOrthogonalMatrix R).actList X) =
          Ambient.evalOrZero (S.fn n hn) X
end YangMills.Construction.EuclideanFunctionals
end

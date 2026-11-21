import YangMills.Construction.SummableBoundsOfTheFlow.NumbersOfFamilies
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace StepDensities
def stepCurvatureValueStatement : Prop :=
  EventuallyOrdered fun T => T.AdmitsReference → ∃ y C : ℝ, 0 < y ∧ 0 < C ∧
    ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible → ∀ t : ℕ,
    (FamilyNorms.HasUnitPlaneValue (T.secondOrderDensity t) (T.secondCoeff t) ∧ |T.secondCoeff t| ≤ C) ∧
    ∀ x : ℝ, y ≤ x → ∃ v : ℝ, FamilyNorms.HasUnitPlaneValue (T.minimizerDensity t x) v ∧
      |v - T.oneLoopCoeff t - T.secondCoeff t / x| ≤ C * x ^ (-(3 / 2 : ℝ))
end StepDensities
end YangMills.Construction
end

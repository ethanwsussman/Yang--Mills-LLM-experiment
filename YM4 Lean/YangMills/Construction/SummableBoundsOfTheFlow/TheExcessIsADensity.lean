import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessOfTheDensitiesIsSmall
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepDensities
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
def densityExcessIsLocalDensity : Prop :=
  EventuallyOrdered fun T => T.AdmitsReference → ∃ y : ℝ, 0 < y ∧ ∀ (t : ℕ) (x : ℝ), y ≤ x →
    IsLocalDensity T.L t T.n₀ (9 / 8 * T.σ) (densityExcess T t x)
end YangMills.Construction.StepDensities
end

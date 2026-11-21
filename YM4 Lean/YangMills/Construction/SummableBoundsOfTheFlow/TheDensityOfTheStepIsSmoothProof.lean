import YangMills.Construction.SummableBoundsOfTheFlow.TheDensityOfTheStepHasItsLowOrders
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensityOfTheStepIsAnalytic
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensityOfTheStepIsSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.TheHigherDerivativesOfTheDensityOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusLumps StepDensities
namespace ReferenceDensity
theorem stepDensityIsSmooth_holds (h₁ : stepDensityLowOrderStatement)
    (h₂ : stepDensityAnalyticStatement) (h₃ : StepDensityHigherDerivBound) :
    StepDensityIsSmooth := by
  refine EventuallyOrdered.mono (EventuallyOrdered.and h₁ (EventuallyOrdered.and h₂ h₃)) ?_
  rintro T - - ⟨g₁, g₂, C, g₃⟩
  refine ⟨C, fun ℓ hm hf t => ?_⟩
  obtain ⟨p, d, c⟩ := g₁ ℓ hm hf t
  exact ⟨p, d, c, fun n _ hn y W hW k b X => g₂ ℓ hm hf t n hn y W hW k b X,
    fun n _ hn y W hW k b X h4 h6 hX => g₃ ℓ hm hf t n hn y W hW k b X h4 h6 hX⟩
end ReferenceDensity
end YangMills.Construction
end

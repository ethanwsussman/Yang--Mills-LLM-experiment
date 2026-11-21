import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfTheStepAreDensities
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfTheStepAreInvariant
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfTheStepAreSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem meansAreLocalDensities_holds (hJ : EventuallyInParametersCombines)
    (hS : meansContDiffThree) (hI : stepMeansInvariantStatement) :
    meansAreLocalDensities := by
  obtain ⟨join, weaken⟩ := hJ
  refine weaken _ _ (fun T hT h t x hx f hf => ?_) (join _ _ hS hI)
  obtain ⟨hS, hI⟩ := h
  have hσ := hT.σ_pos
  have hc : ∀ {F : BlockFrame} {V : F.GaugeField F.top}, IsSmallCurvature (9 / 8 * T.σ) V →
      IsSmallCurvature (5 / 4 * T.σ) V := fun hV q hq => lt_of_lt_of_le (hV q hq) (by linarith)
  exact ⟨⟨fun F hF Y V hV => (hS t x hx f hf F hF Y V (hc hV)).1,
      fun F hF Y V γ hV => ((hI t x hx f hf F hF V (hc hV)).1 Y γ).1,
      fun F hF Y h V hV => ((hI t x hx f hf F hF V (hc hV)).2 Y h).1⟩,
    ⟨fun F hF Y V hV => (hS t x hx f hf F hF Y V (hc hV)).2,
      fun F hF Y V γ hV => ((hI t x hx f hf F hF V (hc hV)).1 Y γ).2,
      fun F hF Y h V hV => ((hI t x hx f hf F hF V (hc hV)).2 Y h).2⟩⟩
end YangMills.Construction.ColdStepAtMirrorFrames
end

import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.DensitiesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormOfTheExpansionDensity
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfTheStepAreDensities
import YangMills.Construction.ColdStepAtMirrorFrames.MeasuresOfTheStepAreRegular
import YangMills.Construction.ColdStepAtMirrorFrames.SizesOfTheExpansionDensity
import YangMills.Construction.ColdStepAtMirrorFrames.SizesOfTheFrameDensityForm
import YangMills.Construction.ColdStepAtMirrorFrames.SizesOfTheMeanDensity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem stepDensityBounds_of_components (hJ : EventuallyInParametersCombines)
    (hR : stepMeasuresRegularStatement) (hD : meansAreLocalDensities)
    (hU : interactionDensityBoundsStatement) (hS : expansionDensityBoundsStatement)
    (hT : frameDensityBoundsEventually) (hQ : flatLimitOfStepDensity) :
    stepDensityBoundsStatement := by
  obtain ⟨combine, weaken⟩ := hJ
  refine weaken _ _ (fun T _ h t x hx f hf => ?_)
    (combine _ _ hR (combine _ _ hD (combine _ _ hU (combine _ _ hS (combine _ _ hT hQ)))))
  obtain ⟨hR, hD, hU, hS, hT, hQ⟩ := h
  obtain ⟨hdu, hds⟩ := hD t x hx f hf
  obtain ⟨hsu, hdcu, hlu⟩ := hU t x hx f hf
  obtain ⟨hdcs, hls⟩ := hS t x hx f hf
  obtain ⟨hdt, hst, hdct, hlt, hzt⟩ := hT t x hx
  exact ⟨hR t x hx f hf, hdu, hds, hdt, hsu, hdcu, hlu, hdcs, hls, hst, hdct, hlt, hzt,
    hQ t x hx f hf⟩
end YangMills.Construction.ColdStepAtMirrorFrames
end

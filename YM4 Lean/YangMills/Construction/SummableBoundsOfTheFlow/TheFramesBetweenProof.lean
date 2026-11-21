import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenBounds
import YangMills.Construction.SummableBoundsOfTheFlow.FieldsOfTheTopBetween
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenStayNear
import YangMills.Construction.SummableBoundsOfTheFlow.LawsBetweenAreConvex
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetween
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeBetweenComparesOnTwoTori
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeOfTheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.TheFramesBetween
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
theorem interpolatedFrames_of_components (hControl : interpolatedFramesControlled)
    (hSlope : interpolatedSlopeSmallOnTorus) (hLocal : interpolatedSlopeLocalOnTwoTori)
    (hExponent : interpolatedExponentBoundsStatement) (hTop : topVariationAlongFields)
    (hMix : mixturesOfIntermediateLawsConvex) (hMoments : intermediateLawMoments)
    (hSizes : observableSizesStatement)
    (hCombine : ColdStepAtMirrorFrames.EventuallyInParametersCombines) :
    interpolatedFramesStatement := by
  obtain ⟨Cq, Cr, hM⟩ := hMoments
  obtain ⟨Cz, hO⟩ := hSizes
  obtain ⟨hAnd, hMono⟩ := hCombine
  refine ⟨Cq, Cz, Cr, ?_⟩
  refine hMono _ _ ?_ (hAnd _ _ hControl (hAnd _ _ hSlope (hAnd _ _ hLocal (hAnd _ _ hExponent
    (hAnd _ _ hTop (hAnd _ _ hMix (hAnd _ _ hM hO)))))))
  rintro T - ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ t x hx
  refine ⟨fun F V s ht hc h0 h1' => ?_, fun F F' V V' Y Y' r s ht ht' hc hc' hag h0 h1' => ?_,
    fun ι _ _ d n w M hw hM' => ?_⟩
  · obtain ⟨a1, a2⟩ := (h1 t x hx).single F V s ht hc h0 h1'
    exact ⟨a1, a2, h2 t x hx F V s ht hc h0 h1', h4 t x hx F V s ht hc h0 h1', h5 t x hx F V s ht hc h0 h1'⟩
  · exact ⟨(h1 t x hx).pair F F' V V' Y Y' r s ht ht' hc hc' hag h0 h1',
      h3 t x hx F F' V V' Y Y' r s ht ht' hc hc' hag h0 h1'⟩
  · exact ⟨h6 t x hx ι d n w M hw hM', h7 t x hx ι d n w M hw hM',
      fun M₀ hM₀ => h8 t x hx ι d n w M hw hM' M₀ hM₀⟩
end Interpolation
end YangMills.Construction
end

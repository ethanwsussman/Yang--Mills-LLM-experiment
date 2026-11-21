import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.SummableBoundsOfTheFlow.FlatFormOfTheMean
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOfOneFamilyInTheLawOfAnother
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOnOneTorus
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOnTwoTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BlockMeans
theorem conditionalMean (hone : BlockMeans.singleTorusMeanStatement)
    (htwo : BlockMeans.twoTorusMeanStatement) (hfl : SummableBounds.meanHessianAtUniformStatement)
    (hJ : ColdStepAtMirrorFrames.EventuallyInParametersCombines) :
    BlockMeans.conditionalMeanStatement := by
  refine hJ.2 _ _ (fun T _ h => ?_) (hJ.1 _ _ hone (hJ.1 _ _ htwo hfl))
  obtain ⟨h1, h2, h3⟩ := h
  intro t x φ h ε U hx hε hφ hh
  have one := h1 t x φ h ε U hx hε hφ hh
  have two := h2 t x φ h ε U hx hε hφ hh
  exact ⟨one.isMean, one.density, one.near_block, one.decay, two.centred_close, two.locality,
    h3 t x φ h ε U hx hε hφ hh⟩
end YangMills.Construction.BlockMeans
end

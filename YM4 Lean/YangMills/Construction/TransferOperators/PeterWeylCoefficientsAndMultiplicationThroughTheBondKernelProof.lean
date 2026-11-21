import YangMills.Construction.TransferOperators.FieldsKeepProductCoefficientSpaces
import YangMills.Construction.TransferOperators.HatAndFunctionsOfTheOtherVariables
import YangMills.Construction.TransferOperators.HatIsLinearAndKeepsRealFunctions
import YangMills.Construction.TransferOperators.InverseWeightSumConverges
import YangMills.Construction.TransferOperators.OperatorHatAlongInjectionsAndPermutations
import YangMills.Construction.TransferOperators.OperatorHatKeepsTwoSidedInvariance
import YangMills.Construction.TransferOperators.OperatorHatOnFibres
import YangMills.Construction.TransferOperators.OperatorsHatOfDisjointPartsCommute
import YangMills.Construction.TransferOperators.PeterWeylCoefficientsAndMultiplicationThroughTheBondKernel
import YangMills.Construction.TransferOperators.PolynomialThroughTheBondKernelAtSmoothFunctions
import YangMills.Construction.TransferOperators.RapidDecayGivesASmoothFunction
import YangMills.Construction.TransferOperators.SeriesOfTheOperatorHatConverges
import YangMills.Construction.TransferOperators.SmoothFunctionsDecayRapidly
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.SpinHarmonics
theorem mulThroughLinkKernel_holds
    (hFields : FieldsPreserveIsotypicSpans.Statement)
    (hSmooth : SmoothToSobolevDecayStatement)
    (hDecay : SobolevDecayToSmoothStatement)
    (hWeight : WeightDecaySum.Statement)
    (hSeries : HatSeriesConvergesStatement)
    (hLinearReal : HatLinearRealStatement)
    (hOther : HatComplementMulStatement)
    (hDisjoint : HatDisjointCommuteStatement)
    (hFibres : HatFibrewiseStatement)
    (hReindex : HatNaturalityStatement)
    (hInvariance : HatBiInvarianceStatement)
    (hKernel : PolyThroughLinkKernelSmoothStatement) :
    MulThroughLinkKernelStatement := by
  intro J _ _
  refine ⟨hFields J, hSmooth J, hDecay J, hWeight J, ?_⟩
  intro β B f hf D hβ hB hD
  refine ⟨fun F hF => hSeries J β B f hf D hβ hB hD F hF, ?_⟩
  obtain ⟨hLinear, hReal⟩ := hLinearReal J β B f hf hβ hB
  obtain ⟨hInjection, hPermutation⟩ := hReindex J β B f hf hβ hB
  exact ⟨hLinear, hReal, hOther J β B f hf hβ hB, hDisjoint J β B f hf hβ hB,
    hFibres J β B f hf hβ hB, hInjection, hInvariance J β B f hf hβ hB, hPermutation,
    hKernel J β B f hf hβ hB⟩
end YangMills.Construction.SpinHarmonics
end

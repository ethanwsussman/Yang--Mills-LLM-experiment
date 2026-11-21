import YangMills.Construction.TransferOperators.CopiesOfABlockAreDisjointOnATorus
import YangMills.Construction.TransferOperators.InsertedOperatorsOfABlockAreContractions
import YangMills.Construction.TransferOperators.InsertionObservableHasNonPositiveStateValue
import YangMills.Construction.TransferOperators.InsertionObservableIsRealLocalAndGaugeInvariant
import YangMills.Construction.TransferOperators.InsertionOfContractionsBetweenLayers
import YangMills.Construction.TransferOperators.IntegralOfAnInsertionIsAtMostTheNormaliser
import YangMills.Construction.TransferOperators.IntegralOfAnInsertionOfContractionsIsATrace
import YangMills.Construction.TransferOperators.NormaliserOfACubicTorusIsATrace
import YangMills.Construction.TransferOperators.TorusWeightIsAProductOverLayers
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.TransferOperators.ContractionInsertion
theorem contractionInsertion_holds
    (hLocal : LogKernelRatio.RealLocalInvariantStatement)
    (hWeight : BoltzmannWeight.ProdSlicesStatement)
    (hPartition : CubicPartitionFunctionTraceStatement)
    (hCopies : BlockCopies.DisjointStatement)
    (hContractions : LevelProductOps.ContractionStatement)
    (hTrace : ExpShiftIntegralTraceStatement)
    (hBound : ExpShiftIntegral.BoundStatement)
    (hState : LogKernelRatio.NonposStateStatement) :
    ContractionInsertionStatement := by
  intro β hβ μ B Ξ hΞ hReal hGauge hPos i
  refine ⟨hLocal β hβ μ B Ξ hΞ hReal hGauge hPos i, fun Γ => hWeight β hβ μ Γ,
    fun Γ => hPartition β hβ μ Γ, ?_, ?_⟩
  · intro Q' hIndex hDisjoint Γ hΓ
    exact ⟨hCopies μ B i Q' hIndex hDisjoint Γ hΓ,
      hContractions μ B Ξ hΞ i Q' hDisjoint Γ hΓ,
      hTrace β hβ μ B Ξ hΞ hReal hGauge hPos i Q' hIndex hDisjoint Γ hΓ,
      hBound β hβ μ B Ξ hΞ hReal hGauge hPos i Q' hIndex hDisjoint Γ hΓ⟩
  · intro ν hν
    exact hState β hβ μ B Ξ hΞ hReal hGauge hPos i ν hν
end YangMills.Construction.TransferOperators.ContractionInsertion

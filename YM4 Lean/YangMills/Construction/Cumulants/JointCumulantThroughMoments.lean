import YangMills.Construction.Cumulants.NumberOfBlocksAndImagesOfPartitions
import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace YangMills.Construction.Cumulants
open YangMills.Construction.Probability (IsBoundedRealRV)
open YangMills.Construction.SetPartition (PartitionsFin blockCount)
def MixedCumulantMomentExpansion : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ℕ)
    (X : Fin p → Ω → ℝ), 1 ≤ p → (∀ l, IsBoundedRealRV (X l)) →
    mixedCumulant μ X =
      ∑ π : PartitionsFin p, (-1 : ℂ) ^ (blockCount π - 1) *
        ((blockCount π - 1).factorial : ℂ) *
          ∏ J ∈ π.parts, ((∫ ω, ∏ l ∈ J, X l ω ∂μ : ℝ) : ℂ)
end YangMills.Construction.Cumulants

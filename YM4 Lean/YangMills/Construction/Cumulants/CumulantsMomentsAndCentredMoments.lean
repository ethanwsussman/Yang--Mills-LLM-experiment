import YangMills.Construction.Cumulants.LogMomentGeneratingFunction
import YangMills.Construction.Cumulants.NumberOfBlocksAndImagesOfPartitions
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants
open YangMills.Construction.Probability (IsBoundedRealRV complexExpectation)
open YangMills.Construction.SetPartition (PartitionsFin blockCount singletonFree)
def CumulantMomentRelations : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (q : ℕ)
    (X : Fin q → Ω → ℝ), (∀ l, IsBoundedRealRV (X l)) →
    (∀ (n : ℕ) (Y : Fin n → Ω → ℝ) (Y' : Ω → ℝ), 1 ≤ n →
      (∀ i, IsBoundedRealRV (Y i)) → IsBoundedRealRV Y' →
      (mixedCumulant μ Y).im = 0 ∧
      (∀ σ : Equiv.Perm (Fin n), mixedCumulant μ (fun i => Y (σ i)) = mixedCumulant μ Y) ∧
      ∀ (j : Fin n) (a a' : ℝ),
        mixedCumulant μ (Function.update Y j fun ω => a * Y j ω + a' * Y' ω) =
          (a : ℂ) * mixedCumulant μ Y + (a' : ℂ) * mixedCumulant μ (Function.update Y j Y')) ∧
    (∀ l, finsetCumulant μ X {l} = complexExpectation μ fun ω => (X l ω : ℂ)) ∧
    (∀ (J : Finset (Fin q)) (c : Fin q → ℝ), 2 ≤ J.card →
      finsetCumulant μ (shiftTuple X c) J = finsetCumulant μ X J) ∧
    (∀ (n : ℕ) (Y : Fin n → Ω → ℝ) (c : Fin n → ℝ), 2 ≤ n →
      (∀ i, IsBoundedRealRV (Y i)) →
      mixedCumulant μ (shiftTuple Y c) = mixedCumulant μ Y) ∧
    (complexExpectation μ fun ω => ((∏ l, X l ω : ℝ) : ℂ)) =
      ∑ π : PartitionsFin q, ∏ J ∈ π.parts, finsetCumulant μ X J ∧
    (complexExpectation μ fun ω => ∏ l, ((X l ω : ℂ) - complexExpectation μ fun ω' => (X l ω' : ℂ))) =
      ∑ π ∈ singletonFree q, ∏ J ∈ π.parts, finsetCumulant μ X J ∧
    (1 ≤ q → mixedCumulant μ X =
      ∑ π : PartitionsFin q, (-1 : ℂ) ^ (blockCount π - 1) *
        ((blockCount π - 1).factorial : ℂ) * ∏ J ∈ π.parts, finsetMoment μ X J)
end YangMills.Construction.Cumulants

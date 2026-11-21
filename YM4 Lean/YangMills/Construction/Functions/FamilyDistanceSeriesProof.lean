import YangMills.Construction.Functions.PropertiesOfTheTopologyOfAFamilyProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.FamilySeries
open FamilyTopology
private theorem summable_two_zpow_neg_pnat :
    Summable fun s : ℕ+ => (2 : ℝ) ^ (-((s : ℕ) : ℤ)) := by apply _root_.YangMills.Construction.FamilyTopology.Properties.summable_two_zpow_neg <;> assumption
theorem familySeriesTerms : FamilySeriesTerms := by
  intro X 𝔄 e α hα x x'
  have hbound : ∀ s : ℕ+,
      seriesTerm e α x x' s ∈ Set.Icc (0 : ℝ) ((2 : ℝ) ^ (-((s : ℕ) : ℤ))) := by
    intro s
    have hp : (0 : ℝ) < (2 : ℝ) ^ (-((s : ℕ) : ℤ)) := zpow_pos (by norm_num) _
    have h0 : (0 : ℝ) ≤ min 1 |e (α s) x - e (α s) x'| := le_min zero_le_one (abs_nonneg _)
    have h1 : min 1 |e (α s) x - e (α s) x'| ≤ 1 := min_le_left _ _
    constructor
    · exact mul_nonneg hp.le h0
    · exact mul_le_of_le_one_right hp.le h1
  refine ⟨hbound, ?_⟩
  have hsum : Summable (seriesTerm e α x x') :=
    Summable.of_nonneg_of_le (fun s => (hbound s).1) (fun s => (hbound s).2)
      summable_two_zpow_neg_pnat
  exact hsum.hasSum
end YangMills.Construction.FamilySeries

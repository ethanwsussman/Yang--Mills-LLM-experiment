import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfAWeightWithCores
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.CoreColumns
open Dobrushin TorusLumps
theorem columnsOfActivityWithCores_holds (hi : ActivityInfluenceStatement) (hcol : ColumnSumBound) :
    ColumnsOfActivityWithCores := by
  intro n _ I _ _ S _ A m _ G z h core near rt e Dn hrt hz hne hsum hnear hfar
  classical
  obtain ⟨h1, h2, h3⟩ := hi I S A m G z h hz
  have hz0 := h.activity_nonneg
  refine ⟨fun i j hij σ σ' hσ hσ' hd B hB => ?_, fun Y j => ?_, fun Y F hF hb h0 => ?_⟩
  · by_cases hn : near i j
    · have := h1 i j hij σ σ' hσ hσ' hd B hB
      simp only [spinInfluence, if_pos hn]
      linarith [hz0 i]
    · obtain ⟨hf, hr⟩ := hfar i j hij hn
      have := h2 i j _ hij hf (by positivity) hr σ σ' hσ hσ' hd B hB
      simp only [spinInfluence, if_neg hn]
      linarith
  · refine hcol n I core z (spinInfluence near rt core z) Y rt e Dn hrt hne hz0 hsum (fun i j => ?_) j
    by_cases hn : near i j
    · left
      simp only [spinInfluence, if_pos hn]
      exact ⟨hnear i j hn, le_rfl⟩
    · right
      simp only [spinInfluence, if_neg hn]
      exact le_rfl
  · have hM := h3 (Finset.univ.filter fun i => Y ∈ core i) F hF hb fun σ hσ =>
      h0 σ fun i hi' => hσ i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi'⟩)
    refine hM.trans (le_trans (Finset.sum_le_sum fun i _ => ?_) (hsum Y))
    have hT : (1 : ℝ) ≤ ((core i).card : ℝ) := by exact_mod_cast Finset.card_pos.mpr (hne i)
    have hE : 1 ≤ Real.exp (2 * rt * (siteDiameter (core i) : ℝ)) := Real.one_le_exp (by positivity)
    have hT4 : (1 : ℝ) ≤ ((core i).card : ℝ) ^ 4 := one_le_pow₀ hT
    have := hz0 i
    calc z i = z i * 1 * 1 := by ring
      _ ≤ _ := by gcongr
end YangMills.Construction.CoreColumns
end

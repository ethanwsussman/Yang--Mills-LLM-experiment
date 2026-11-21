import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.TheExpansionFlowIsTheTotalFlow
import YangMills.Construction.TotalDensitiesGiveASystem.TheFlowPasses
import YangMills.Construction.TotalDensitiesGiveASystem.TheWindowHasItsData
import YangMills.Construction.TotalDensitiesGiveASystem.TheWindowsRecur
import Mathlib
set_option autoImplicit false
open Set Filter
noncomputable section
namespace YangMills.Construction.TotalDensities
open SequencePassage (passageThreshold)
theorem flowPasses_holds (hW : TotalDensitiesGiveASystem.passageWindowDataStatement)
    (hR : TotalDensitiesGiveASystem.FirstPassageWindowsRecur)
    (hJ : expansionFlowEqTotalFlow) : FlowPasses := by
  refine HoldsAtAdmissibleParameters.mono (HoldsAtAdmissibleParameters.and (HoldsAtAdmissibleParameters.and hW hR) hJ)
    fun T y hAdm hA => ?_
  obtain ⟨⟨hw, Nw, hNw, y₃, fR⟩, hj⟩ := hA
  obtain ⟨c, hc, y₁, fW⟩ := hw (2 * T.B) le_rfl
  obtain ⟨y₂, fJ⟩ := hj (2 * T.B) le_rfl
  have hlam : 0 < 3 / 4 * (SystemsWithFiveBounds.asymptoticFreedomSlope * Real.log T.side) := by
    have hL' : (1 : ℝ) < T.side := by
      have h : 2 ^ 40 ≤ T.side := hAdm.L_ge
      have h' : 1 < T.side := lt_of_lt_of_le (by norm_num) h
      exact_mod_cast h'
    have hlog := Real.log_pos hL'
    have hpi := Real.pi_pos
    unfold SystemsWithFiveBounds.asymptoticFreedomSlope
    positivity
  refine ⟨c, Nw, hc, hNw, fun c₅ hc₅ => ⟨max y₁ (max y₂ y₃), fun g hg hy => ?_⟩⟩
  have h₁ : y₁ ≤ g ^ (-2 : ℤ) := le_trans (le_max_left _ _) hy
  have h₂ : y₂ ≤ g ^ (-2 : ℤ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have h₃ : y₃ ≤ g ^ (-2 : ℤ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  have w := fW g hg h₁
  have j := fJ g hg h₂
  have toTotal : ∀ (K : ℕ) (β : ℝ), IsFirstPassagePoint (T.stepParameters y) (2 * T.B) g K β →
      TotalDensitySystem.IsFirstPassageDatum (T.stepParameters y) (2 * T.B) g K β := fun K β h => by
    unfold TotalDensitySystem.IsFirstPassageDatum
    rw [(j K).1]
    exact h
  have toExpansion : ∀ (K : ℕ) (β : ℝ), TotalDensitySystem.IsFirstPassageDatum (T.stepParameters y) (2 * T.B) g K β →
      IsFirstPassagePoint (T.stepParameters y) (2 * T.B) g K β := fun K β h => by
    unfold TotalDensitySystem.IsFirstPassageDatum at h
    rw [(j K).1] at h
    exact h
  refine ⟨fun β hβ => ?_, ?_, fun K' => ?_⟩
  · obtain ⟨K, hK⟩ := w.passes_from β hβ
    obtain ⟨l, u⟩ := w.cutoff_bounds K β hK
    refine ⟨K, toTotal K β hK, l, ?_, ?_⟩
    · refine le_trans u ?_
      have := div_le_div_of_nonneg_right (a := β - g ^ (-2 : ℤ) - 2 * T.B + c)
        (b := β - g ^ (-2 : ℤ) - 2 * T.B + c₅) (by linarith) hlam.le
      exact add_le_add_right this 1
    · rw [(j K).2 β hK K le_rfl]
      exact w.coupling_gt K β hK K le_rfl
  · obtain ⟨δ, hδ, h⟩ := w.slope_tendsto
    exact ⟨δ, hδ, fun K β hK hp => h K β hK (toExpansion K β hp)⟩
  · obtain ⟨K, h1, h2, β, hβ⟩ := fR g hg h₃ K'
    exact ⟨K, h1, h2, β, toTotal K β hβ⟩
end YangMills.Construction.TotalDensities
end

import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.FactorOfAClassIsOneRuleProof
import YangMills.Construction.ClusterExpansionOfAStep.IntegralNearAClassIsBounded
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages TorusFields TorusLumps StepSettings ColdStepAtMirrorFrames
namespace LocalIntegralBound
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)
theorem coordNorm_eq_norm (v : E3) : coordNorm v = ‖v‖ := by apply _root_.YangMills.Construction.BlockTrees.norm_toImaginary <;> assumption
theorem cutoffFactor_le_one {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) (u : ℝ) (h0 : 0 ≤ u) :
    cutoffFactor ρ p u ≤ 1 := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_le_one <;> assumption
theorem cutoffFactor_nonneg (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
open Classical in
theorem integral_cutoff_le {ι : Type} [Fintype ι] {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (U : (ι → E3) → ℝ) (m : ℝ) (hU : ∀ ζ, (∀ b, ‖ζ b‖ < ρ) → -U ζ ≤ m) :
    ∫ ζ : ι → E3, (∏ b, cutoffFactor ρ p (coordNorm (ζ b))) * Real.exp (-U ζ) ≤
      liePointBallVolume ρ ^ Fintype.card ι * Real.exp m := by
  have hfin : volume (Metric.ball (0 : E3) ρ) ≠ ⊤ := measure_ball_lt_top.ne
  set g : (ι → E3) → ℝ :=
    fun ζ => (∏ b, (Metric.ball (0 : E3) ρ).indicator (fun _ => (1 : ℝ)) (ζ b)) * Real.exp m with hg
  have hint1 : Integrable ((Metric.ball (0 : E3) ρ).indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
      (integrableOn_const (by exact hfin))
  have hgi : Integrable g := by
    refine Integrable.mul_const ?_ _
    exact Integrable.fintype_prod (f := fun _ => (Metric.ball (0 : E3) ρ).indicator (fun _ => (1 : ℝ)))
      fun _ => hint1
  have hle : ∫ ζ : ι → E3, (∏ b, cutoffFactor ρ p (coordNorm (ζ b))) * Real.exp (-U ζ) ≤ ∫ ζ, g ζ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ζ => ?_) hgi
      (Filter.Eventually.of_forall fun ζ => ?_)
    · exact mul_nonneg (Finset.prod_nonneg fun b _ => cutoffFactor_nonneg _ _ _) (Real.exp_pos _).le
    · show _ ≤ g ζ
      by_cases hz : ∀ b, ‖ζ b‖ < ρ
      · have h1 : ∏ b, cutoffFactor ρ p (coordNorm (ζ b)) ≤ 1 :=
          Finset.prod_le_one (fun b _ => cutoffFactor_nonneg _ _ _)
            fun b _ => cutoffFactor_le_one hρ hp _ (by rw [coordNorm_eq_norm]; exact norm_nonneg _)
        have h2 : ∏ b, (Metric.ball (0 : E3) ρ).indicator (fun _ => (1 : ℝ)) (ζ b) = 1 :=
          Finset.prod_eq_one fun b _ => by simp [Set.indicator, hz b]
        simp only [hg, h2, one_mul]
        calc _ ≤ 1 * Real.exp (-U ζ) := by gcongr
          _ ≤ _ := by simpa using Real.exp_le_exp.mpr (hU ζ hz)
      · push Not at hz
        obtain ⟨b, hb⟩ := hz
        have h0 : ∏ b, cutoffFactor ρ p (coordNorm (ζ b)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ b) (by
            simp [cutoffFactor, coordNorm_eq_norm, not_lt.mpr hb])
        show (∏ b, cutoffFactor ρ p (coordNorm (ζ b))) * Real.exp (-U ζ) ≤ g ζ
        rw [h0, zero_mul]
        exact mul_nonneg (Finset.prod_nonneg fun b _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
          (Real.exp_pos _).le
  refine hle.trans (le_of_eq ?_)
  simp only [hg]
  rw [integral_mul_const,
    integral_fintype_prod_volume_eq_pow ((Metric.ball (0 : E3) ρ).indicator (fun _ => (1 : ℝ)))]
  simp [liePointBallVolume, integral_indicator Metric.isOpen_ball.measurableSet, Measure.real]
end LocalIntegralBound
open LocalIntegralBound in
theorem localIntegralLeBallVolume_holds : LocalIntegralLeBallVolume := by
  intro R n _ s N M hρ hp hU
  have := integral_cutoff_le hρ hp (s.localPotential N) M (fun ζ hζ => hU ζ fun b => by
    rw [coordNorm_eq_norm]
    exact hζ b)
  simpa [ChartSetting.localIntegral, Fintype.card_coe] using this
end YangMills.Construction.ClusterExpansionOfAStep
end

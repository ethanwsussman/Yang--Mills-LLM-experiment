import YangMills.Construction.ColdStepAtMirrorFrames.MeanAlongASegmentProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace CutoffExpectation
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ}
theorem openPolyball_eq_ball (hρ : 0 < ρ) : openPolyball ι ρ = Metric.ball (0 : BondField ι) ρ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.openPolyball_eq_ball <;> assumption
theorem isOpen_openPolyball (hρ : 0 < ρ) : IsOpen (openPolyball ι ρ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.isOpen_openPolyball <;> assumption
theorem measurable_indicator_openPolyball (hρ : 0 < ρ) {f : BondField ι → ℝ}
    (hf : ContinuousOn f (openPolyball ι ρ)) : Measurable ((openPolyball ι ρ).indicator f) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SegmentMean.measurable_indicator_openPolyball <;> assumption
end CutoffExpectation
open CutoffExpectation in
theorem cutoffExpectationIsPositiveForm_of_cutoffFactor (hcut : CutoffFactorIsRadialCutoff) :
    CutoffExpectationIsPositiveForm := by
  intro ι _ _ ρ p Ψ hρ hp hΨc
  have hr := hcut ρ p hρ hp
  set r : ℝ → ℝ := fun u => cutoffFactor ρ p (max u 0) with hrd
  have hprod : radialWeightProd (ι := ι) (cutoffFactor ρ p) = radialWeightProd r := by
    funext η
    simp only [radialWeightProd, hrd, max_eq_left (norm_nonneg _)]
  have hrc : Continuous (radialWeightProd (ι := ι) r) := by
    unfold radialWeightProd
    refine continuous_finsetProd _ fun b _ => ?_
    have h1 : ContDiff ℝ 1 r := hr.smooth
    exact h1.continuous.comp ((continuous_apply b).norm)
  have hzero : ∀ (Φ : BondField ι → ℝ) η, η ∉ openPolyball ι ρ → ballDensity (cutoffFactor ρ p) Φ η = 0 := by
    intro Φ η hη
    simp only [openPolyball, Set.mem_ofPred_eq, not_forall, not_lt] at hη
    obtain ⟨b, hb⟩ := hη
    have h0 : ∏ b, r ‖η b‖ = 0 := Finset.prod_eq_zero (Finset.mem_univ b) (hr.zero _ hb)
    have h1 : radialWeightProd (cutoffFactor ρ p) η = 0 := by
      rw [hprod]
      exact h0
    simp [ballDensity, h1]
  have hcont : Continuous (ballDensity (cutoffFactor ρ p) Ψ) := by
    unfold ballDensity
    rw [hprod]
    exact hrc.mul hΨc.neg.rexp
  have hnn : ∀ η, 0 ≤ ballDensity (cutoffFactor ρ p) Ψ η := by
    intro η
    unfold ballDensity
    rw [hprod]
    refine mul_nonneg (Finset.prod_nonneg fun b _ => ?_) (Real.exp_pos _).le
    rcases lt_or_ge ‖η b‖ ρ with h | h
    · exact (hr.pos _ (norm_nonneg _) h).le
    · rw [hr.zero _ h]
  have hpos : ∀ η ∈ openPolyball ι ρ, 0 < ballDensity (cutoffFactor ρ p) Ψ η := by
    intro η hη
    unfold ballDensity
    rw [hprod]
    exact mul_pos (Finset.prod_pos fun b _ => hr.pos _ (norm_nonneg _) (hη b)) (Real.exp_pos _)
  have hint : Integrable (ballDensity (cutoffFactor ρ p) Ψ) := by
    apply hcont.integrable_of_hasCompactSupport
    refine HasCompactSupport.intro (isCompact_closedBall (0 : BondField ι) ρ) fun η hη => ?_
    apply hzero
    intro h
    apply hη
    rw [openPolyball_eq_ball hρ] at h
    exact Metric.ball_subset_closedBall h
  have hmem0 : (0 : BondField ι) ∈ openPolyball ι ρ := fun b => by simpa using hρ
  have hZ : 0 < ∫ η, ballDensity (cutoffFactor ρ p) Ψ η := by
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    have hsub : openPolyball ι ρ ⊆ Function.support (ballDensity (cutoffFactor ρ p) Ψ) :=
      fun η hη => (hpos η hη).ne'
    exact lt_of_lt_of_le ((isOpen_openPolyball hρ).measure_pos _ ⟨0, hmem0⟩) (measure_mono hsub)
  have hbdd : ∀ f : BondField ι → ℝ, IsBoundedContinuousOn ι ρ f →
      Integrable (fun η => f η * ballDensity (cutoffFactor ρ p) Ψ η) := by
    rintro f ⟨hfc, M, hM⟩
    have hm := measurable_indicator_openPolyball hρ hfc
    have hb : Integrable (fun η => (openPolyball ι ρ).indicator f η * ballDensity (cutoffFactor ρ p) Ψ η) := by
      refine Integrable.mono' (hint.const_mul |M|) (hm.aestronglyMeasurable.mul hint.1) ?_
      refine Eventually.of_forall fun η => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn η)]
      refine mul_le_mul_of_nonneg_right ?_ (hnn η)
      by_cases hη : η ∈ openPolyball ι ρ
      · rw [Set.indicator_of_mem hη]
        exact (hM η hη).trans (le_abs_self M)
      · rw [Set.indicator_of_notMem hη]
        simp
    refine hb.congr (Eventually.of_forall fun η => ?_)
    by_cases hη : η ∈ openPolyball ι ρ
    · simp only [Set.indicator_of_mem hη]
    · simp [hzero Ψ η hη]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ballExpectation
    simp only [one_mul]
    exact div_self hZ.ne'
  · intro f g h
    unfold ballExpectation
    congr 1
    apply integral_congr_ae
    refine Eventually.of_forall fun η => ?_
    by_cases hη : η ∈ openPolyball ι ρ
    · simp only [h η hη]
    · simp [hzero Ψ η hη]
  · intro Ψ' f h
    have key : ballDensity (cutoffFactor ρ p) Ψ = ballDensity (cutoffFactor ρ p) Ψ' := by
      funext η
      by_cases hη : η ∈ openPolyball ι ρ
      · simp only [ballDensity, h η hη]
      · rw [hzero Ψ η hη, hzero Ψ' η hη]
    unfold ballExpectation
    rw [key]
  · intro f g hf hg h
    unfold ballExpectation
    apply div_le_div_of_nonneg_right _ hZ.le
    apply integral_mono (hbdd f hf) (hbdd g hg)
    intro η
    by_cases hη : η ∈ openPolyball ι ρ
    · exact mul_le_mul_of_nonneg_right (h η hη) (hnn η)
    · simp [hzero Ψ η hη]
  · intro f g hf hg
    unfold ballExpectation
    rw [← add_div, ← integral_add (hbdd f hf) (hbdd g hg)]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun η => by
      simp only
      ring
  · intro c f
    unfold ballExpectation
    rw [mul_div_assoc', ← integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun η => by
      simp only
      ring
end YangMills.Construction.ColdStepAtMirrorFrames
end

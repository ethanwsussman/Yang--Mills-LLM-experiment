import YangMills.Construction.ColdStepAtMirrorFrames.ChartFieldIsLeastAtACriticalPoint
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
private theorem le_of_convex_of_no_initial_descent (φ : ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (h2 : ∀ τ, 0 ≤ τ → τ ≤ 1 → κ ≤ deriv (deriv φ) τ)
    (h1 : ∀ ε : ℝ, 0 < ε → ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ < τ₀ → φ 0 - ε * τ ≤ φ τ) :
    φ 0 ≤ φ 1 := by
  have hdiff : ∀ τ, 0 ≤ τ → τ ≤ 1 → DifferentiableAt ℝ (deriv φ) τ := by
    intro τ h0 h1'
    apply differentiableAt_of_deriv_ne_zero
    exact (lt_of_lt_of_le hκ (h2 τ h0 h1')).ne'
  have hcont : ContinuousOn (deriv φ) (Set.Icc 0 1) :=
    fun τ hτ => (hdiff τ hτ.1 hτ.2).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn (deriv φ) (Set.Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) hcont
    intro τ hτ
    rw [interior_Icc] at hτ
    exact lt_of_lt_of_le hκ (h2 τ hτ.1.le hτ.2.le)
  have hD0 : 0 ≤ deriv φ 0 := by
    by_contra hneg
    push_neg at hneg
    have hd : DifferentiableAt ℝ φ 0 := differentiableAt_of_deriv_ne_zero hneg.ne
    obtain ⟨τ₀, hτ₀, hb⟩ := h1 (- deriv φ 0 / 4) (by linarith)
    have hhas : HasDerivAt φ (deriv φ 0) 0 := hd.hasDerivAt
    have hε : 0 < - deriv φ 0 / 4 := by linarith
    have hev := (Asymptotics.isLittleO_iff.1 hhas.isLittleO) hε
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨r, hr, hball⟩ := hev
    set τ : ℝ := min (τ₀ / 2) (r / 2) with hτdef
    have hτpos : 0 < τ := lt_min (by linarith) (by linarith)
    have hτ1 : τ < τ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hτ2 : τ < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hb' := hb τ hτpos hτ1
    have hn := hball (y := τ) (by simpa [abs_of_pos hτpos] using hτ2)
    simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs, abs_of_pos hτpos] at hn
    have := (abs_le.1 hn).2
    nlinarith
  have hpos : ∀ τ, 0 < τ → τ ≤ 1 → 0 < deriv φ τ := by
    intro τ h0 h1'
    exact lt_of_le_of_lt hD0 (hmono ⟨le_rfl, zero_le_one⟩ ⟨h0.le, h1'⟩ h0)
  have hdφ : ∀ τ, 0 < τ → τ ≤ 1 → DifferentiableAt ℝ φ τ := fun τ h0 h1' =>
    differentiableAt_of_deriv_ne_zero (hpos τ h0 h1').ne'
  have hmonoφ : MonotoneOn φ (Set.Ioc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
    · exact fun τ hτ => (hdφ τ hτ.1 hτ.2).continuousAt.continuousWithinAt
    · intro τ hτ
      rw [interior_Ioc] at hτ
      exact (hdφ τ hτ.1 hτ.2.le).differentiableWithinAt
    · intro τ hτ
      rw [interior_Ioc] at hτ
      exact (hpos τ hτ.1 hτ.2.le).le
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨τ₀, hτ₀, hb⟩ := h1 ε hε
  set τ : ℝ := min (τ₀ / 2) 1 with hτdef
  have hτpos : 0 < τ := lt_min (by linarith) one_pos
  have hτ1 : τ < τ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hτle : τ ≤ 1 := min_le_right _ _
  have h3 := hb τ hτpos hτ1
  have h4 := hmonoφ ⟨hτpos, hτle⟩ ⟨one_pos, le_rfl⟩ hτle
  nlinarith
variable {F : BlockFrame}
theorem chartCriticalPointIsMinimal : ChartCriticalPointIsMinimal := by
  intro F a lam ρ σ S V w₀ w₁ hlam hfloor h0 h1 hseg hcrit
  set dw : F.Site F.depth → Fin 4 → imaginaryQuaternions := fun x i => w₁ x i - w₀ x i with hdw
  set φ : ℝ → ℝ := chartEnergyOnSegment a S V w₀ dw with hφ
  have hend0 : φ 0 = blockEnergy a S F.depth (chartedField w₀ V) V := by
    simp [hφ, chartEnergyOnSegment]
  have hend1 : φ 1 = blockEnergy a S F.depth (chartedField w₁ V) V := by
    simp [hφ, chartEnergyOnSegment, hdw]
  rw [← hend0, ← hend1]
  by_cases hzero : ∀ b ∈ chordBonds S, dw b.1 b.2 = 0
  · have hall : ∀ x i, dw x i = 0 := by
      intro x i
      by_cases hb : (x, i) ∈ chordBonds S
      · exact hzero _ hb
      · have e0 := h0 (x, i) hb
        have e1 := h1 (x, i) hb
        simp only [hdw, e0, e1, sub_zero]
    have : φ 1 = φ 0 := by
      simp [hφ, chartEnergyOnSegment, hall]
    rw [this]
  · push_neg at hzero
    obtain ⟨b₀, hb₀, hne⟩ := hzero
    have hκ : 0 < lam * ∑ b ∈ chordBonds S, ‖dw b.1 b.2‖ ^ 2 := by
      apply mul_pos hlam
      apply Finset.sum_pos' (fun _ _ => by positivity)
      exact ⟨b₀, hb₀, by have := norm_pos_iff.2 hne; positivity⟩
    refine le_of_convex_of_no_initial_descent φ _ hκ ?_ hcrit
    intro τ hτ0 hτ1
    obtain ⟨hρ, hcold⟩ := hseg τ hτ0 hτ1
    have hoff : ∀ b, b ∉ chordBonds S → (w₀ b.1 b.2 + τ • dw b.1 b.2) = 0 := by
      intro b hb
      simp only [hdw, h0 b hb, h1 b hb, sub_zero, smul_zero, add_zero]
    have hoff' : ∀ b, b ∉ chordBonds S → dw b.1 b.2 = 0 := by
      intro b hb
      simp only [hdw, h0 b hb, h1 b hb, sub_zero]
    have := hfloor (fun x i => w₀ x i + τ • dw x i) dw hoff hoff' hρ hcold
    have hshift : (fun s : ℝ => blockEnergy a S F.depth
        (chartedField (fun x i => (w₀ x i + τ • dw x i) + s • dw x i) V) V) = fun s => φ (τ + s) := by
      funext s
      simp only [hφ, chartEnergyOnSegment, add_smul, add_assoc]
    rw [hshift] at this
    have hd1 : deriv (fun s => φ (τ + s)) = fun s => deriv φ (τ + s) := by
      funext s
      exact deriv_comp_const_add φ τ s
    rw [hd1] at this
    have hd2 := deriv_comp_const_add (deriv φ) τ 0
    rw [hd2, add_zero] at this
    exact this
end YangMills.Construction.ColdStepAtMirrorFrames
end

import YangMills.Construction.ClusterExpansionOfAStep.OrderOfTheBlocks
import YangMills.Construction.ClusterExpansionOfAStep.RandomOrderOfBlocks
import YangMills.Construction.ClusterExpansionOfAStep.RatiosOfXi
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheGasDensities
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
theorem markedPrecedingBlocks_eq_precedingBlocks {n : ℕ} [NeZero n] (u : TorusFields.TorusSite n → ℝ)
    (hu : Function.Injective u) (Y : TorusFields.TorusSite n) (o : LinearOrder (TorusFields.TorusSite n)) :
    MarkedIntegrals.precedingBlocks u Y = @BlockOrder.precedingBlocks _ _ o u Y := by
  classical
  ext i
  simp only [MarkedIntegrals.precedingBlocks, BlockOrder.precedingBlocks, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · exact Or.inl
  · rintro (h | ⟨h, h'⟩)
    · exact h
    · exact absurd (hu h ▸ h') (lt_irrefl _)
theorem logPartitionEqSumDensities_of_bounds (hC : GasColumnsSmall) (hX : PartitionRatioBounds)
    (hO : BlockOrder.RandomOrderFacts) (hR : BlockOrder.SumIncrementsAlongOrder) :
    StepGas.LogPartitionEqSumDensities := by
  obtain ⟨r₀, hr₀, h⟩ := hC
  refine ⟨r₀, hr₀, fun T hT hle => ?_⟩
  obtain ⟨y₀, hy⟩ := h T hT hle
  have hκ₁ : 0 < T.κ₁ := lt_min (div_pos hT.κ_pos (by norm_num))
    (div_pos hT.cE_pos (by have := hT.σ_pos; positivity))
  have hrate : 0 < T.gasRate := by
    have h1 : 0 < T.κ * T.threshold ^ 2 := mul_pos hT.κ_pos (pow_pos hT.σ_pos 2)
    have h2 : 0 < T.κ₁ * T.threshold ^ 2 := mul_pos hκ₁ (pow_pos hT.σ_pos 2)
    exact mul_pos (by norm_num) (lt_min hT.cE_pos (lt_min h1 h2))
  refine ⟨max y₀ (1 / T.gasRate), fun y hyy R hRT hx' n _ G hG => ?_⟩
  have hall := hy y (le_trans (le_max_left _ _) hyy) R hRT hx' n G hG
  obtain ⟨-, xpos, xuniv, -, xrat⟩ := hX R n G T.gasRate hall
  obtain ⟨hp, hinj, hintg, -⟩ := hO n
  have hx1 : 1 ≤ T.gasRate * R.coupling := by
    have h1 : 1 / T.gasRate ≤ R.coupling := (le_trans (le_max_right _ _) hyy).trans hRT.le_coupling
    rw [div_le_iff₀ hrate] at h1
    linarith
  have hb : ∀ (A : Finset (TorusFields.TorusSite n)) (Y : TorusFields.TorusSite n),
      0 ≤ Real.log (G.xi A) - Real.log (G.xi (insert Y A)) ∧
        Real.log (G.xi A) - Real.log (G.xi (insert Y A)) ≤ Real.exp (-(6 * T.gasRate * R.coupling)) := by
    intro A Y
    obtain ⟨h1, h2⟩ := xrat A Y
    have hpA := xpos A
    have hpYA := xpos (insert Y A)
    set ρ := G.xi (insert Y A) / G.xi A with hρ
    have hρ0 : 0 < ρ := div_pos hpYA hpA
    have hlog : Real.log (G.xi A) - Real.log (G.xi (insert Y A)) = -Real.log ρ := by
      rw [hρ, Real.log_div hpYA.ne' hpA.ne']
      ring
    rw [hlog]
    have e1 : Real.exp (-(7 * T.gasRate * R.coupling)) =
        Real.exp (-(6 * T.gasRate * R.coupling)) * Real.exp (-(T.gasRate * R.coupling)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (-(T.gasRate * R.coupling)) ≤ 1 / 2 := by
      have h0 : Real.exp (-(T.gasRate * R.coupling)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      have h3 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
      linarith
    have e3 : 0 < Real.exp (-(6 * T.gasRate * R.coupling)) := Real.exp_pos _
    have e4 : Real.exp (-(6 * T.gasRate * R.coupling)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have e5 : Real.exp (-(7 * T.gasRate * R.coupling)) ≤ Real.exp (-(6 * T.gasRate * R.coupling)) / 2 := by
      rw [e1]
      nlinarith
    have hρh : 1 / 2 ≤ ρ := by linarith
    constructor
    · have := Real.log_nonpos hρ0.le h2
      linarith
    · have h3 := Real.one_sub_inv_le_log_of_pos hρ0
      have h4 : ρ⁻¹ - 1 ≤ 2 * (1 - ρ) := by
        rw [inv_eq_one_div, sub_le_iff_le_add, div_le_iff₀ hρ0]
        nlinarith
      linarith
  have hint : ∀ Y : TorusFields.TorusSite n, Integrable
      (fun u => Real.log (G.xi (MarkedIntegrals.precedingBlocks u Y)) -
        Real.log (G.xi (insert Y (MarkedIntegrals.precedingBlocks u Y)))) (MarkedIntegrals.randomOrderLaw n) :=
    fun Y => hintg (fun A => Real.log (G.xi A) - Real.log (G.xi (insert Y A))) Y
  have key : ∀ u : TorusFields.TorusSite n → ℝ, Function.Injective u →
      ∑ Y, (Real.log (G.xi (MarkedIntegrals.precedingBlocks u Y)) -
        Real.log (G.xi (insert Y (MarkedIntegrals.precedingBlocks u Y)))) = Real.log (G.xi ∅) := by
    intro u hu
    classical
    let o : LinearOrder (TorusFields.TorusSite n) :=
      LinearOrder.lift' (Fintype.equivFin (TorusFields.TorusSite n)) (Fintype.equivFin _).injective
    have h1 := @hR (TorusFields.TorusSite n) _ o (fun A => Real.log (G.xi A)) u
    have h2 : ∑ Y, (Real.log (G.xi (insert Y (MarkedIntegrals.precedingBlocks u Y))) -
        Real.log (G.xi (MarkedIntegrals.precedingBlocks u Y))) =
        Real.log (G.xi Finset.univ) - Real.log (G.xi ∅) := by
      simp_rw [markedPrecedingBlocks_eq_precedingBlocks u hu _ o]
      convert h1 using 4
      congr 1
      ext z
      simp
    rw [xuniv, Real.log_one, zero_sub] at h2
    have h3 : ∑ Y, (Real.log (G.xi (MarkedIntegrals.precedingBlocks u Y)) -
        Real.log (G.xi (insert Y (MarkedIntegrals.precedingBlocks u Y)))) =
        -∑ Y, (Real.log (G.xi (insert Y (MarkedIntegrals.precedingBlocks u Y))) -
          Real.log (G.xi (MarkedIntegrals.precedingBlocks u Y))) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun Y _ => ?_
      ring
    rw [h3, h2, neg_neg]
  constructor
  · unfold StepGas.GasGround.blockDensity
    rw [← integral_finset_sum _ fun Y _ => hint Y]
    rw [integral_congr_ae (g := fun _ => Real.log (G.xi ∅)) (hinj.mono fun u hu => key u hu)]
    simp
  · intro Y
    unfold StepGas.GasGround.blockDensity
    constructor
    · exact integral_nonneg fun u => (hb _ Y).1
    · calc ∫ u, (Real.log (G.xi (MarkedIntegrals.precedingBlocks u Y)) -
            Real.log (G.xi (insert Y (MarkedIntegrals.precedingBlocks u Y)))) ∂MarkedIntegrals.randomOrderLaw n
          ≤ ∫ _, Real.exp (-(6 * T.gasRate * R.coupling)) ∂MarkedIntegrals.randomOrderLaw n :=
            integral_mono (hint Y) (integrable_const _) fun u => (hb _ Y).2
        _ = Real.exp (-(6 * T.gasRate * R.coupling)) := by simp
end YangMills.Construction.ClusterExpansionOfAStep
end

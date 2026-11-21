import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheTerms
import YangMills.Construction.ResponseInTheExpansion.ElementsOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.WeightedResponses
theorem abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
open TorusFields TorusLumps StepCosts BlockAverages LumpContours
theorem norm_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := CStarRing.norm_coe_unitary g
theorem abs_re_mul_inv_le (q : ℍ[ℝ]) (g : UnitQuaternion) :
    |(q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re| ≤ ‖q‖ := by
  refine (abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_unitQuaternion, mul_one]
theorem norm_contourMean_le {F : BlockFrame} (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth)))
    (b : F.Cell → F.Site F.depth) (w : F.GaugeField F.depth) (c : F.Cell × Fin 4) :
    ‖contourMean J₀ h b w c‖ ≤ 1 := by
  unfold contourMean
  rw [norm_smul]
  set U := usedContours J₀ h b c with hU
  have hsum : ‖∑ e ∈ U, ((pathHolonomy w (b c.1) (contourPath b c e.1 e.2) : UnitQuaternion) : ℍ[ℝ])‖ ≤
      (U.card : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_unitQuaternion]
    simp
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rcases Nat.eq_zero_or_pos U.card with h0 | h0
  · simp [h0]
  · have hc : (0 : ℝ) < U.card := by exact_mod_cast h0
    rw [one_div]
    exact (inv_mul_le_one₀ hc).mpr hsum
theorem norm_bondMean_le {n : ℕ} (p : StepParameters) (w : (stepBlockFrame p.side n).GaugeField 0)
    (b : BaseChoice p.side n) (c : TorusBond n) : ‖bondMean p w b c‖ ≤ 1 :=
  norm_contourMean_le _ _ _ _ _
end YangMills.Construction.WeightedResponses
end

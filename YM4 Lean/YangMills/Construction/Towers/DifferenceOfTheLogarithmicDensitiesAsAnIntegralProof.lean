import YangMills.Construction.Towers.DifferenceOfTheLogarithmicDensitiesAsAnIntegral
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
namespace YangMills.Construction
open OperatorCalculus OneLoopNotation Tower.AbelianFieldDensity
namespace Tower.LocalFamilies
namespace LogTraceDiff
section General
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem continuousOn_Ici_of_normContinuousOn {F : ℝ → BddOp H}
    (h : ∀ y : ℝ, 0 < y → NormContinuousOn F 0 y) : ContinuousOn F (Ici 0) := by
  intro w hw
  have hw0 : (0 : ℝ) ≤ w := hw
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hF⟩ := h (w + 1) (by linarith) w ⟨hw0, by linarith⟩ (ε / 2) (half_pos hε)
  refine ⟨min δ 1, lt_min hδ one_pos, fun x hx hdist => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := hx
  have hmin : |x - w| < min δ 1 := by simpa [Real.dist_eq] using hdist
  have hone : |x - w| < 1 := lt_of_lt_of_le hmin (min_le_right _ _)
  have hδ' : |x - w| < δ := lt_of_lt_of_le hmin (min_le_left _ _)
  have hxw : x ≤ w + 1 := by
    have := (abs_lt.mp hone).2
    linarith
  have hest := hF x ⟨hx0, hxw⟩ (by rw [abs_sub_comm]; exact hδ'.le)
  rw [dist_comm, dist_eq_norm]
  linarith
theorem map_sub_of_boundedLinear {τ : BddOp H → ℂ} {N : ℕ} (h : IsBoundedLinearTrace τ N)
    (A B : BddOp H) : τ (A - B) = τ A - τ B := by
  have := h.1 A B (-1)
  rw [neg_one_smul, ← sub_eq_add_neg] at this
  rw [this]
  ring
theorem continuous_of_boundedLinear {τ : BddOp H → ℂ} {N : ℕ}
    (h : IsBoundedLinearTrace τ N) : Continuous τ := by
  refine (LipschitzWith.of_dist_le_mul (K := (N : NNReal)) fun A B => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← map_sub_of_boundedLinear h]
  simpa using h.2.1 (A - B)
theorem continuousOn_scalarOp_inv_one_add :
    ContinuousOn (fun w : ℝ => (scalarOp (((1 + w)⁻¹ : ℝ) : ℂ) : BddOp H))
      (Ici 0) := by
  have hs : ContinuousOn (fun w : ℝ => (((1 + w)⁻¹ : ℝ) : ℂ)) (Ici 0) :=
    Complex.continuous_ofReal.comp_continuousOn
      (ContinuousOn.inv₀ (by fun_prop) fun w hw => by
        have : (0 : ℝ) ≤ w := hw
        positivity)
  exact hs.smul continuousOn_const
variable [CompleteSpace H]
theorem halfLine_integral_facts {τ : BddOp H → ℂ} {N : ℕ} {z : ℝ}
    (hcomm : CommutesWithIntegral τ N) (hlog : SectorDecomposition.LogShiftedProps H z)
    (hint : SectorDecomposition.LogEqIntegralIoi H z) {A : BddOp H}
    (hA : SectorDecomposition.ShiftedHalfPositive z A) :
    ContinuousOn (resolventDiff (addScalar A z)) (Ici 0) ∧
      IntegrableOn (fun w => τ (resolventDiff (addScalar A z) w)) (Ioi 0) ∧
      τ (opLog (addScalar A z)) =
        ∫ w in Ioi (0 : ℝ), τ (resolventDiff (addScalar A z) w) := by
  obtain ⟨-, -, hcont, hnorm, -, -, -⟩ := hlog A hA
  obtain ⟨l, hl⟩ := hnorm
  have hl' : Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y, ‖resolventDiff (addScalar A z) w‖) atTop
      (nhds l) := by
    simpa only [abs_norm] using hl
  obtain ⟨-, -, hτc, hτb, hτt, hτe⟩ := hcomm _ hcont ⟨l, hl'⟩
  have hc := continuousOn_Ici_of_normContinuousOn hcont
  have hFi : IntegrableOn (resolventDiff (addScalar A z)) (Ioi 0) :=
    integrableOn_Ioi_of_intervalIntegral_norm_tendsto l 0
      (fun y => ((hc.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
      tendsto_id hl'
  have hgi : IntegrableOn (fun w => τ (resolventDiff (addScalar A z) w)) (Ioi 0) := by
    refine Integrable.mono' (hFi.norm.const_mul (N : ℝ))
      ((hτc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_)
    exact hτb w (le_of_lt hw)
  refine ⟨hc, hgi, ?_⟩
  rw [hint A hA, hτe]
  exact tendsto_nhds_unique hτt (intervalIntegral_tendsto_integral_Ioi 0 hgi tendsto_id)
end General
end LogTraceDiff
open LogTraceDiff in
theorem logTraceDiffIntegral_holds : LogTraceDiffIntegral := by
  intro J B position tail m m' z C T hz hC hset
  have hv : PeriodicOperators.castVec (0 : Fin 4 → ℤ) = 0 := by
    funext μ
    simp [PeriodicOperators.castVec]
  have hlin := hset.space.trace_bounded 0
  have hcomm := hset.space.trace_integral 0
  rw [hv] at hlin hcomm
  obtain ⟨r, hr, hlow⟩ := hset.lower_bound
  have hA₀ : SectorDecomposition.ShiftedHalfPositive z (T fun _ => 0) :=
    ⟨hset.family.selfAdjoint _, hlow _ fun _ => by simpa using hr.le⟩
  obtain ⟨hc₀, hi₀, he₀⟩ :=
    halfLine_integral_facts hcomm hset.space.logShifted hset.space.log_eq_integral hA₀
  refine ⟨fun θ hθ => ?_, fun X => ?_⟩
  · have hA : SectorDecomposition.ShiftedHalfPositive z (T θ) := ⟨hset.family.selfAdjoint _, hθ⟩
    obtain ⟨-, hi, he⟩ :=
      halfLine_integral_facts hcomm hset.space.logShifted hset.space.log_eq_integral hA
    have hd : (fun w : ℝ => traceAt position (baseResolvent T z w) 0 -
        traceAt position (inverseOp (addScalar (addScalar (T θ) z) w)) 0) =
        fun w => traceAt position (resolventDiff (addScalar (T θ) z) w) 0 -
          traceAt position (resolventDiff (addScalar (T fun _ => 0) z) w) 0 := by
      funext w
      have e1 := map_sub_of_boundedLinear hlin (scalarOp (((1 + w)⁻¹ : ℝ) : ℂ))
        (inverseOp (addScalar (addScalar (T θ) z) w))
      have e2 := map_sub_of_boundedLinear hlin (scalarOp (((1 + w)⁻¹ : ℝ) : ℂ))
        (inverseOp (addScalar (addScalar (T fun _ => 0) z) w))
      beta_reduce at e1 e2
      unfold resolventDiff baseResolvent
      rw [e1, e2]
      ring
    rw [hd]
    refine ⟨hi.sub hi₀, ?_⟩
    rw [integral_sub hi hi₀, ← he, ← he₀]
    rfl
  · have hRc : ContinuousOn (baseResolvent T z) (Ici 0) := by
      have := continuousOn_scalarOp_inv_one_add.sub hc₀
      refine this.congr fun w _ => ?_
      simp [resolventDiff, baseResolvent]
    have hfc : ContinuousOn (fun w : ℝ => traceAt position
        ((baseResolvent T z w).comp (X.comp (baseResolvent T z w))) 0) (Ici 0) :=
      (continuous_of_boundedLinear hlin).comp_continuousOn
        (hRc.clm_comp (continuousOn_const.clm_comp hRc))
    have hG : IntegrableOn (fun w : ℝ => ((m : ℝ) * ‖X‖) * (w + z / 2) ^ (-2 : ℝ)) (Ioi 0) :=
      (integrableOn_add_rpow_Ioi_of_lt (a := -2) (m := z / 2) (c := 0) (by norm_num)
        (by linarith)).const_mul _
    refine Integrable.mono' hG
      ((hfc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_)
    have hw0 : (0 : ℝ) < w := hw
    have hR : ‖baseResolvent T z w‖ ≤ (z / 2 + w)⁻¹ :=
      ((hset.space.logShifted _ hA₀).1 w hw0.le).2
    have hpos : 0 < z / 2 + w := by linarith
    have hb : ‖(baseResolvent T z w).comp (X.comp (baseResolvent T z w))‖ ≤
        (z / 2 + w)⁻¹ * (‖X‖ * (z / 2 + w)⁻¹) := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      refine mul_le_mul hR ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left hR (norm_nonneg _))) (norm_nonneg _) (by positivity)
    have hrp : (w + z / 2) ^ (-2 : ℝ) = ((z / 2 + w)⁻¹) ^ 2 := by
      rw [Real.rpow_neg (by linarith), Real.rpow_two, inv_pow, add_comm]
    calc ‖traceAt position
          ((baseResolvent T z w).comp (X.comp (baseResolvent T z w))) 0‖
        ≤ (m : ℝ) * ‖(baseResolvent T z w).comp (X.comp (baseResolvent T z w))‖ := hlin.2.1 _
      _ ≤ (m : ℝ) * ((z / 2 + w)⁻¹ * (‖X‖ * (z / 2 + w)⁻¹)) :=
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = ((m : ℝ) * ‖X‖) * (w + z / 2) ^ (-2 : ℝ) := by
          rw [hrp]
          ring
end Tower.LocalFamilies
end YangMills.Construction
end

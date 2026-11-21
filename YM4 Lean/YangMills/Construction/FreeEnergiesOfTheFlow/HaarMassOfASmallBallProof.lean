import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdStepAtMirrorFrames.WeylFormulaOfTheGroup
import YangMills.Construction.FreeEnergiesOfTheFlow.HaarMassOfASmallBall
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.HaarBalls
open BlockAverages ColdStepAtMirrorFrames TorusFields
private theorem norm_sub_one_sq_eq (g : UnitQuaternion) :
    ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 = 2 * (1 - ((g : UnitQuaternion) : ℍ[ℝ]).re) := by apply _root_.YangMills.Construction.TorusFields.sq_norm_unitQuaternion_sub_one <;> assumption
theorem haarMassCubicLowerBound_of_weylIntegrationFormula (hW : WeylIntegrationFormula) :
    HaarMassCubicLowerBound := by
  refine ⟨1 / (32 * Real.pi), by positivity, fun r hr hr1 => ?_⟩
  set t : ℝ := r ^ 2 / 2 with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 / 2 := by
    have : r ^ 2 ≤ 1 := by nlinarith
    rw [ht]
    linarith
  let ψ : ℝ → ℝ := fun v => max 0 (1 - v / t)
  have hψc : Continuous ψ := by fun_prop
  have hψ0 : ∀ v, 0 ≤ ψ v := fun v => le_max_left _ _
  have hψ1 : ∀ v, 0 ≤ v → ψ v ≤ 1 := by
    intro v hv
    refine max_le zero_le_one ?_
    have : 0 ≤ v / t := by positivity
    linarith
  have hclosed : IsClosed (closedBallAtOne r) := by
    have : Continuous fun g : UnitQuaternion => ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1‖ :=
      (continuous_subtype_val.sub continuous_const).norm
    exact isClosed_le this continuous_const
  have hmeas : MeasurableSet (closedBallAtOne r) := hclosed.measurableSet
  have hcont : Continuous fun g : UnitQuaternion => ψ (1 - ((g : UnitQuaternion) : ℍ[ℝ]).re) :=
    hψc.comp (continuous_const.sub (Quaternion.continuous_re.comp continuous_subtype_val))
  have hint : Integrable (fun g : UnitQuaternion => ψ (1 - ((g : UnitQuaternion) : ℍ[ℝ]).re))
      haarUnit :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hle : ∫ g : UnitQuaternion, ψ (1 - ((g : UnitQuaternion) : ℍ[ℝ]).re) ∂haarUnit ≤
      (haarUnit (closedBallAtOne r)).toReal := by
    have hind : Integrable ((closedBallAtOne r).indicator fun _ : UnitQuaternion => (1 : ℝ))
        haarUnit :=
      (integrable_const (1 : ℝ)).indicator hmeas
    have h1 : ∫ g, (closedBallAtOne r).indicator (fun _ : UnitQuaternion => (1 : ℝ)) g ∂haarUnit =
        (haarUnit (closedBallAtOne r)).toReal := by
      rw [integral_indicator_const _ hmeas]
      simp [Measure.real]
    rw [← h1]
    refine integral_mono hint hind fun g => ?_
    have hn := norm_sub_one_sq_eq g
    have hge : 0 ≤ 1 - ((g : UnitQuaternion) : ℍ[ℝ]).re := by
      nlinarith [sq_nonneg ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1‖]
    by_cases hg : g ∈ closedBallAtOne r
    · simp only [Set.indicator_of_mem hg]
      exact hψ1 _ hge
    · simp only [Set.indicator_of_notMem hg]
      refine max_le le_rfl ?_
      have hlt : r < ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1‖ := not_le.mp hg
      have hsq : r ^ 2 < ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 := by nlinarith
      have : t < 1 - ((g : UnitQuaternion) : ℍ[ℝ]).re := by
        rw [ht]
        linarith
      have : 1 ≤ (1 - ((g : UnitQuaternion) : ℍ[ℝ]).re) / t := (one_le_div ht0).mpr this.le
      linarith
  rw [hW.1 ψ hψc] at hle
  refine le_trans ?_ hle
  set f : ℝ → ℝ := fun v => ψ v * haarRealPartDensity v with hf
  have hfc : Continuous f := by
    refine hψc.mul ?_
    unfold haarRealPartDensity
    fun_prop
  have hf0 : ∀ v, 0 ≤ f v := fun v =>
    mul_nonneg (hψ0 v) (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  have hsub : ∫ v in (t / 4)..(t / 2), f v ≤ ∫ v in (0 : ℝ)..2, f v := by
    refine intervalIntegral.integral_mono_interval (by positivity) (by linarith) (by linarith)
      (Filter.Eventually.of_forall hf0) (hfc.intervalIntegrable _ _)
  refine le_trans ?_ hsub
  set c : ℝ := 1 / (2 * Real.pi) * Real.sqrt t with hc
  have hlow : ∀ v ∈ Set.Icc (t / 4) (t / 2), c ≤ f v := by
    intro v hv
    have hv1 : v ≤ 1 := by linarith [hv.2]
    have hvpos : 0 < v := by linarith [hv.1]
    have hψv : 1 / 2 ≤ ψ v := by
      refine le_trans ?_ (le_max_right _ _)
      have : v / t ≤ 1 / 2 := by
        rw [div_le_iff₀ ht0]
        linarith [hv.2]
      linarith
    have hs : Real.sqrt t / 2 ≤ Real.sqrt (2 * v - v ^ 2) := by
      refine Real.le_sqrt_of_sq_le ?_
      have : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
      have h3 : v ≤ 2 * v - v ^ 2 := by nlinarith
      have h4 := hv.1
      nlinarith
    have hρ : 1 / Real.pi * Real.sqrt t ≤ haarRealPartDensity v := by
      unfold haarRealPartDensity
      have : 2 / Real.pi * (Real.sqrt t / 2) ≤ 2 / Real.pi * Real.sqrt (2 * v - v ^ 2) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      calc 1 / Real.pi * Real.sqrt t = 2 / Real.pi * (Real.sqrt t / 2) := by ring
        _ ≤ _ := this
    have hρ0 : 0 ≤ 1 / Real.pi * Real.sqrt t := by positivity
    calc c = 1 / 2 * (1 / Real.pi * Real.sqrt t) := by rw [hc]; field_simp
      _ ≤ ψ v * haarRealPartDensity v := mul_le_mul hψv hρ hρ0 (hψ0 v)
  have hconst : ∫ _v in (t / 4)..(t / 2), c ≤ ∫ v in (t / 4)..(t / 2), f v :=
    intervalIntegral.integral_mono_on (by linarith) (by simp) (hfc.intervalIntegrable _ _) hlow
  refine le_trans ?_ hconst
  rw [intervalIntegral.integral_const, smul_eq_mul]
  have hsq : r / 2 ≤ Real.sqrt t := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [ht]
    nlinarith [sq_nonneg r]
  have hfin : (t / 2 - t / 4) * c = r ^ 2 / 8 * (1 / (2 * Real.pi) * Real.sqrt t) := by
    rw [hc, ht]
    ring
  rw [hfin]
  have : r ^ 2 / 8 * (1 / (2 * Real.pi) * (r / 2)) ≤
      r ^ 2 / 8 * (1 / (2 * Real.pi) * Real.sqrt t) := by
    gcongr
  refine le_trans (le_of_eq ?_) this
  field_simp
  ring
end YangMills.Construction.HaarBalls
end

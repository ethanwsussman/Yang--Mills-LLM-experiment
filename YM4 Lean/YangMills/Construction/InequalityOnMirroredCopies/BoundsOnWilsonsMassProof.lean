import YangMills.Construction.InequalityOnMirroredCopies.BoundsOnWilsonsMass
import YangMills.Construction.ResponseInTheExpansion.MassOfALevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ReflectedCopies
open TorusFields TorusFrame TorusLumps ClusterExpansionOfAStep HaarBalls BlockAverages
private theorem norm_word_sub_one_le {ε : ℝ} (a b c d : UnitQuaternion) (ha : a ∈ closedBallAtOne ε)
    (hb : b ∈ closedBallAtOne ε) (hc : c ∈ closedBallAtOne ε) (hd : d ∈ closedBallAtOne ε) :
    ‖((a * b * c⁻¹ * d⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 4 * ε := by apply _root_.YangMills.SharedProofs.p54318 <;> assumption
theorem wilsonPartitionBounds (hH : HaarMassCubicLowerBound) : WilsonPartitionBounds := by
  obtain ⟨c', hc', hball⟩ := hH
  refine ⟨128 - 4 * Real.log c', fun β hβ n _ => ?_⟩
  have hβ0 : 0 < β := by linarith
  set f : TorusField n → ℝ := fun U => Real.exp (-β * wilsonAction Finset.univ U) with hf
  have hcont : Continuous f :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_wilsonAction _))
  have hA0 : ∀ U : TorusField n, 0 ≤ wilsonAction Finset.univ U := fun U =>
    Finset.sum_nonneg fun p _ => plaquetteEnergy_nonneg U _ _ _
  have hf1 : ∀ U, f U ≤ 1 := fun U => by
    have : -β * wilsonAction Finset.univ U ≤ 0 := by nlinarith [hA0 U]
    exact Real.exp_le_one_iff.mpr this
  have hfpos : ∀ U, 0 < f U := fun U => Real.exp_pos _
  have hI : Integrable f (fieldHaar n) := by
    refine Integrable.of_bound hcont.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun U => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (hfpos U)]
    exact hf1 U
  have hZ : wilsonPartition β n = ∫ U, f U ∂(fieldHaar n) := by
    unfold wilsonPartition
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    simp [wilsonWeight, hf, NeZero.ne n]
  have hsq : 1 ≤ Real.sqrt β := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hβ
  have hsq0 : 0 < Real.sqrt β := by linarith
  set ε : ℝ := 1 / Real.sqrt β with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one hsq0]
    exact hsq
  have hβε : β * ε ^ 2 = 1 := by
    rw [hε, div_pow, Real.sq_sqrt hβ0.le]
    field_simp
  set S : Set (TorusField n) :=
    Set.univ.pi fun _ : TorusSite n => Set.univ.pi fun _ : Fin 4 => closedBallAtOne ε with hSdef
  have hmemS : ∀ U ∈ S, ∀ x i, U x i ∈ closedBallAtOne ε := fun U hU x i =>
    (Set.mem_univ_pi.mp ((Set.mem_univ_pi.mp hU) x)) i
  have hclosed : MeasurableSet (closedBallAtOne ε) := by
    have : Continuous fun u : UnitQuaternion => ‖((u : UnitQuaternion) : ℍ[ℝ]) - 1‖ :=
      (continuous_subtype_val.sub continuous_const).norm
    exact (isClosed_le this continuous_const).measurableSet
  have hSm : MeasurableSet S :=
    MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => hclosed
  set M : ℕ := Fintype.card (TorusSite n) with hMdef
  have hcard : (M : ℝ) = (n : ℝ) ^ 4 := by
    simp [hMdef, TorusSite, ZMod.card]
  have hmeasure : (fieldHaar n S).toReal = (haarUnit (closedBallAtOne ε)).toReal ^ (4 * M) := by
    unfold fieldHaar
    rw [hSdef, Measure.pi_pi]
    simp only [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
    rw [pow_mul]
  have hcount : ((plaquettesIn (Finset.univ : Finset (TorusSite n))).card : ℝ) ≤ 16 * (n : ℝ) ^ 4 := by
    have h1 : (plaquettesIn (Finset.univ : Finset (TorusSite n))).card ≤ Fintype.card (TorusPlaquette n) :=
      Finset.card_le_univ _
    have h2 : Fintype.card (TorusPlaquette n) = Fintype.card (TorusSite n) * 16 := by simp [TorusPlaquette]
    have h3 : ((plaquettesIn (Finset.univ : Finset (TorusSite n))).card : ℝ) ≤
        (Fintype.card (TorusPlaquette n) : ℝ) := by
      exact_mod_cast h1
    rw [h2] at h3
    push_cast at h3
    rw [show ((Fintype.card (TorusSite n) : ℕ) : ℝ) = (n : ℝ) ^ 4 from hcard] at h3
    linarith
  have haction : ∀ U ∈ S, wilsonAction Finset.univ U ≤ 128 * ε ^ 2 * (n : ℝ) ^ 4 := by
    intro U hU
    have hp : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        plaquetteEnergy U p.1 p.2.1 p.2.2 ≤ 8 * ε ^ 2 := by
      intro p _
      rw [plaquetteEnergy_eq_curvature_sq]
      have hc : curvature U p.1 p.2.1 p.2.2 ≤ 4 * ε :=
        norm_word_sub_one_le _ _ _ _ (hmemS U hU _ _) (hmemS U hU _ _) (hmemS U hU _ _) (hmemS U hU _ _)
      have h0 : 0 ≤ curvature U p.1 p.2.1 p.2.2 := norm_nonneg _
      nlinarith
    calc wilsonAction Finset.univ U ≤ ∑ _p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), 8 * ε ^ 2 :=
          Finset.sum_le_sum hp
      _ = ((plaquettesIn (Finset.univ : Finset (TorusSite n))).card : ℝ) * (8 * ε ^ 2) := by simp
      _ ≤ 16 * (n : ℝ) ^ 4 * (8 * ε ^ 2) := by gcongr
      _ = 128 * ε ^ 2 * (n : ℝ) ^ 4 := by ring
  set K : ℝ := Real.exp (-(128 * (n : ℝ) ^ 4)) with hK
  have hK0 : 0 < K := Real.exp_pos _
  have hpoint : ∀ U ∈ S, K ≤ f U := by
    intro U hU
    refine Real.exp_le_exp.mpr ?_
    have h1 : β * wilsonAction Finset.univ U ≤ β * (128 * ε ^ 2 * (n : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left (haction U hU) hβ0.le
    have h2 : β * (128 * ε ^ 2 * (n : ℝ) ^ 4) = 128 * (n : ℝ) ^ 4 := by
      calc β * (128 * ε ^ 2 * (n : ℝ) ^ 4) = 128 * (β * ε ^ 2) * (n : ℝ) ^ 4 := by ring
        _ = _ := by rw [hβε]; ring
    linarith
  have hZlow : K * (fieldHaar n S).toReal ≤ wilsonPartition β n := by
    rw [hZ]
    have hind : Integrable (S.indicator fun _ : TorusField n => K) (fieldHaar n) :=
      (integrable_const K).indicator hSm
    have h1 : ∫ U, S.indicator (fun _ : TorusField n => K) U ∂(fieldHaar n) = K * (fieldHaar n S).toReal := by
      rw [integral_indicator_const _ hSm]
      simp [Measure.real, mul_comm]
    rw [← h1]
    refine integral_mono hind hI fun U => ?_
    by_cases hU : U ∈ S
    · simp only [Set.indicator_of_mem hU]
      exact hpoint U hU
    · simp only [Set.indicator_of_notMem hU]
      exact (hfpos U).le
  have hb := hball ε hε0 hε1
  have hbpos : 0 < c' * ε ^ 3 := by positivity
  have hmeas : (c' * ε ^ 3) ^ (4 * M) ≤ (fieldHaar n S).toReal := by
    rw [hmeasure]
    exact pow_le_pow_left₀ hbpos.le hb _
  have hfin : K * (c' * ε ^ 3) ^ (4 * M) ≤ wilsonPartition β n :=
    (mul_le_mul_of_nonneg_left hmeas hK0.le).trans hZlow
  have hpos : 0 < K * (c' * ε ^ 3) ^ (4 * M) := by positivity
  refine ⟨hpos.trans_le hfin, ?_, ?_⟩
  · rw [hZ]
    calc ∫ U, f U ∂(fieldHaar n) ≤ ∫ _U, (1 : ℝ) ∂(fieldHaar n) :=
          integral_mono hI (integrable_const 1) hf1
      _ = 1 := by simp
  · have hlog := Real.log_le_log hpos hfin
    rw [Real.log_mul hK0.ne' (by positivity), Real.log_pow, hK, Real.log_exp,
      Real.log_mul hc'.ne' (by positivity), Real.log_pow] at hlog
    have hlogε : Real.log ε = -(Real.log β / 2) := by
      rw [hε, one_div, Real.log_inv, Real.log_sqrt hβ0.le]
    rw [hlogε] at hlog
    push_cast at hlog
    rw [hcard] at hlog
    have hrearr : -((128 - 4 * Real.log c' + 6 * Real.log β) * (n : ℝ) ^ 4) =
        -(128 * (n : ℝ) ^ 4) + 4 * (n : ℝ) ^ 4 * (Real.log c' + 3 * -(Real.log β / 2)) := by
      ring
    rw [hrearr]
    exact hlog
end YangMills.Construction.ReflectedCopies
end

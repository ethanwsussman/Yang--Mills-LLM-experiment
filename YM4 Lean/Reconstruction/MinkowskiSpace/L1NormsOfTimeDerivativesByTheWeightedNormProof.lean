import YangMills.Construction.LatticeForms.LatticeSymbolAndTheTwoGreensFunctionsProof
import Reconstruction.MinkowskiSpace.L1NormsOfTimeDerivativesByTheWeightedNorm
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction.TimeDerivativeL1Bound
open TestSpaces RealPointVectors WightmanReconstruction
theorem integral_Ioi_cube_mul_inv_one_add_sq_cube :
    ∫ y in Ioi (0 : ℝ), y ^ 3 * ((1 + y ^ 2) ^ 3)⁻¹ = 1 / 4 := by
  have hder : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun y : ℝ => (1 / 2 : ℝ) * (-(1 + y ^ 2)⁻¹ + (1 / 2) * ((1 + y ^ 2) ^ 2)⁻¹))
        (t ^ 3 * ((1 + t ^ 2) ^ 3)⁻¹) t := by
    intro t _
    have hne : (1 + t ^ 2) ≠ 0 := by positivity
    have hsq : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_id t).pow 2).const_add 1
    have hinv := hsq.inv hne
    have hinv2 := (hsq.pow 2).inv (pow_ne_zero 2 hne)
    refine ((hinv.neg.add (hinv2.const_mul (1 / 2 : ℝ))).const_mul (1 / 2 : ℝ)).congr_deriv ?_
    norm_num
    field_simp
    ring
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ t ^ 3 * ((1 + t ^ 2) ^ 3)⁻¹ := by
    intro t ht
    have : 0 < t := ht
    positivity
  have hgrow : Tendsto (fun y : ℝ => 1 + y ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  have hlim : Tendsto
      (fun y : ℝ => (1 / 2 : ℝ) * (-(1 + y ^ 2)⁻¹ + (1 / 2) * ((1 + y ^ 2) ^ 2)⁻¹)) atTop (𝓝 0) := by
    have l1 := tendsto_inv_atTop_zero.comp hgrow
    have l2 := tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp hgrow)
    simpa using (l1.neg.add (l2.const_mul (1 / 2 : ℝ))).const_mul (1 / 2 : ℝ)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hder hnn hlim]
  norm_num
theorem volume_real_ball_zero_one :
    (volume : Measure (EuclideanSpace ℝ (Fin 4))).real (Metric.ball 0 1) = Real.pi ^ 2 / 2 := by apply _root_.YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint.SymbolAndGreen.volume_unitBall_four <;> assumption
theorem integral_inv_one_add_norm_sq_cube :
    ∫ x : EuclideanSpace ℝ (Fin 4), ((1 + ‖x‖ ^ 2) ^ 3)⁻¹ = Real.pi ^ 2 / 2 := by
  have hpolar := MeasureTheory.integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 4)))
    (fun y : ℝ => ((1 + y ^ 2) ^ 3)⁻¹)
  rw [hpolar, volume_real_ball_zero_one]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  norm_num
  rw [integral_Ioi_cube_mul_inv_one_add_sq_cube]
  ring
theorem integrable_inv_one_add_norm_sq_cube :
    Integrable fun x : EuclideanSpace ℝ (Fin 4) => ((1 + ‖x‖ ^ 2) ^ 3)⁻¹ := by
  have hint := integrable_rpow_neg_one_add_norm_sq (E := EuclideanSpace ℝ (Fin 4))
    (μ := volume) (r := 6) (by simp; norm_num)
  refine hint.congr (ae_of_all _ fun x => ?_)
  have hposx : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have : (-6 / 2 : ℝ) = -((3 : ℕ) : ℝ) := by norm_num
  simp only [this]
  rw [Real.rpow_neg hposx.le, Real.rpow_natCast]
def decayWeight (u : Fin 4 → ℝ) : ℝ := ((1 + ∑ μ, u μ ^ 2) ^ 3)⁻¹
theorem decayWeight_eq (u : Fin 4 → ℝ) :
    decayWeight u = ((1 + ‖WithLp.toLp 2 u‖ ^ 2) ^ 3)⁻¹ := by
  rw [decayWeight, EuclideanSpace.real_norm_sq_eq]
theorem integrable_decayWeight : Integrable decayWeight := by
  have hcomp := (PiLp.volume_preserving_toLp (Fin 4)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).measurableEmbedding
    (g := fun x : EuclideanSpace ℝ (Fin 4) => ((1 + ‖x‖ ^ 2) ^ 3)⁻¹)
  refine (hcomp.2 integrable_inv_one_add_norm_sq_cube).congr (ae_of_all _ fun u => ?_)
  simp [decayWeight_eq]
theorem integral_decayWeight : ∫ u, decayWeight u = Real.pi ^ 2 / 2 := by
  have hcomp := (PiLp.volume_preserving_toLp (Fin 4)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).measurableEmbedding
    (fun x : EuclideanSpace ℝ (Fin 4) => ((1 + ‖x‖ ^ 2) ^ 3)⁻¹)
  rw [integral_inv_one_add_norm_sq_cube] at hcomp
  rw [← hcomp]
  exact integral_congr_ae (ae_of_all _ fun u => decayWeight_eq u)
theorem coordDeriv_asOnePointFn (f : (Fin 4 → ℝ) → ℂ) :
    coordDeriv (0 : Fin 1) 0 (WightmanTheory.asOnePointFn f) =
      WightmanTheory.asOnePointFn (TestFunctions.partialDerivR4 0 f) := by
  funext x
  simp only [coordDeriv, WightmanTheory.asOnePointFn, TestFunctions.partialDerivR4, lineDeriv]
  congr 1
theorem iterate_coordDeriv_asOnePointFn (j : ℕ) (f : (Fin 4 → ℝ) → ℂ) :
    (coordDeriv (0 : Fin 1) 0)^[j] (WightmanTheory.asOnePointFn f) =
      WightmanTheory.asOnePointFn ((TestFunctions.partialDerivR4 0)^[j] f) := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply, coordDeriv_asOnePointFn, ih]
def timeMultiIdx (j : ℕ) : MultiIdx4 1 := fun _ μ => if μ = 0 then j else 0
theorem idxOrder_timeMultiIdx (j : ℕ) : idxOrder (timeMultiIdx j) = j := by
  simp [idxOrder, timeMultiIdx]
theorem multiDeriv_timeMultiIdx (j : ℕ) (f : (Fin 4 → ℝ) → ℂ) :
    multiDeriv (timeMultiIdx j) (WightmanTheory.asOnePointFn f) =
      WightmanTheory.asOnePointFn ((TestFunctions.partialDerivR4 0)^[j] f) := by
  rw [← iterate_coordDeriv_asOnePointFn]
  simp [multiDeriv, timeMultiIdx, List.finRange_succ]
theorem tupleNorm_sq_const (u : Fin 4 → ℝ) :
    tupleNorm (fun _ : Fin 1 => u) ^ 2 = ∑ μ, u μ ^ 2 := by
  unfold tupleNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun μ _ => sq_nonneg _)]
  simp
theorem norm_iterate_partial_le_schwartzNorm_mul {k j : ℕ} (hj : j ≤ k + 6)
    (g : (Fin 4 → ℝ) → ℂ) (hfin : WightmanTheory.schwartzNorm (k + 6) g ≠ ⊤) (u : Fin 4 → ℝ) :
    ‖(TestFunctions.partialDerivR4 0)^[j] g u‖ ≤
      (WightmanTheory.schwartzNorm (k + 6) g).toReal * decayWeight u := by
  set s : ℝ := ∑ μ, u μ ^ 2 with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun μ _ => sq_nonneg _
  have hone : (1 : ℝ) ≤ 1 + s := by linarith
  have hsup : ENNReal.ofReal ((1 + s) ^ (((k + 6 : ℕ) : ℝ) / 2) *
      ‖(TestFunctions.partialDerivR4 0)^[j] g u‖) ≤ WightmanTheory.schwartzNorm (k + 6) g := by
    have hnorm := tupleNorm_sq_const u
    unfold WightmanTheory.schwartzNorm weightedSeminorm
    refine le_iSup_of_le (fun _ : Fin 1 => u) (le_iSup_of_le (timeMultiIdx j)
      (le_iSup_of_le (by rw [idxOrder_timeMultiIdx]; exact hj) ?_))
    rw [hnorm, multiDeriv_timeMultiIdx]
    exact le_rfl
  have hreal : (1 + s) ^ (((k + 6 : ℕ) : ℝ) / 2) * ‖(TestFunctions.partialDerivR4 0)^[j] g u‖ ≤
      (WightmanTheory.schwartzNorm (k + 6) g).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfin).1 hsup
  have hcube : (1 + s) ^ 3 ≤ (1 + s) ^ (((k + 6 : ℕ) : ℝ) / 2) := by
    have h3 : (1 + s) ^ 3 = (1 + s) ^ ((3 : ℕ) : ℝ) := (Real.rpow_natCast _ 3).symm
    rw [h3]
    refine Real.rpow_le_rpow_of_exponent_le hone ?_
    push_cast
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hcubepos : (0 : ℝ) < (1 + s) ^ 3 := by positivity
  have hkey : (1 + s) ^ 3 * ‖(TestFunctions.partialDerivR4 0)^[j] g u‖ ≤
      (WightmanTheory.schwartzNorm (k + 6) g).toReal :=
    (mul_le_mul_of_nonneg_right hcube (norm_nonneg _)).trans hreal
  rw [decayWeight, ← hs, ← div_eq_mul_inv, le_div_iff₀ hcubepos, mul_comm]
  exact hkey
theorem statement_holds : Statement := by
  intro k g _
  by_cases hfin : WightmanTheory.schwartzNorm (k + 6) g = ⊤
  · rw [hfin, ENNReal.mul_top (by simp [Real.pi_pos.ne'])]
    exact le_top
  · set M := (WightmanTheory.schwartzNorm (k + 6) g).toReal with hM
    have hmax : maxPartialL1 k g ≤ Real.pi ^ 2 * M := by
      unfold maxPartialL1
      refine Finset.sup'_le _ _ fun j hj => ?_
      have hjk : j ≤ k + 6 := by
        have := Finset.mem_range.1 hj
        omega
      have hl1 : lOneNorm ((TestFunctions.partialDerivR4 0)^[j] g) ≤ ∫ u, M * decayWeight u := by
        unfold lOneNorm
        refine integral_mono_of_nonneg (ae_of_all _ fun u => norm_nonneg _)
          (integrable_decayWeight.const_mul M) (ae_of_all _ fun u => ?_)
        exact norm_iterate_partial_le_schwartzNorm_mul hjk g hfin u
      rw [integral_const_mul, integral_decayWeight] at hl1
      have : 0 ≤ Real.pi ^ 2 * M := by positivity
      linarith
    calc ENNReal.ofReal (maxPartialL1 k g)
        ≤ ENNReal.ofReal (Real.pi ^ 2 * M) := ENNReal.ofReal_le_ofReal hmax
      _ = ENNReal.ofReal (Real.pi ^ 2) * WightmanTheory.schwartzNorm (k + 6) g := by
        rw [ENNReal.ofReal_mul (by positivity), hM, ENNReal.ofReal_toReal hfin]
end YangMills.Construction.TimeDerivativeL1Bound

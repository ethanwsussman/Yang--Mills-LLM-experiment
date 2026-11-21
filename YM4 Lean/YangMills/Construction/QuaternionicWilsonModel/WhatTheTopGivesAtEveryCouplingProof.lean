import YangMills.Construction.Continuum.LinearCombinationsAndTensorsLieInTheFlatSpaces
import YangMills.Construction.QuaternionicWilsonModel.TheLimitsOfTheTopAreRealAndNotZeroProof
import YangMills.Construction.QuaternionicWilsonModel.WhatTheTopGivesAtEveryCoupling
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set YangMills.Construction.TestFunctions YangMills.Construction.TorusMetric
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.NonGaussianLimits
open YangMills.Construction.TotalDensitySystem YangMills.Construction.TotalDensities YangMills.Construction.TorusLumps
open YangMills.Construction.SystemsWithFiveBounds YangMills.Construction.LimitTheorem YangMills.Construction.QuadrupleClasses
open YangMills.Construction.FourPointCondition YangMills.Construction.ModelSeams
open YangMills.Construction.SeparatedTuples (DecompositionData TupleFunctional)
open YangMills.Construction.TestSpaces (SepTupleOfCard SepTuple sepRestrict)
open YangMills.Construction.ConfigSpace (SepFamilyOfLength tensorRealFamily schwartzFlatOffDiagonal)
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (i : Fin 4) : |v i| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem pi_norm_le_euclidNormVec (v : Fin 4 → ℝ) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
def radialProfile (y : Fin 4 → ℝ) : ℝ := Real.smoothTransition (2 - ∑ i, y i ^ 2)
theorem radialProfile_contDiff : ContDiff ℝ ∞ radialProfile := by
  unfold radialProfile
  refine Real.smoothTransition.contDiff.comp ?_
  fun_prop
theorem radialProfile_eq_zero {y : Fin 4 → ℝ} (h : 2 ≤ ∑ i, y i ^ 2) : radialProfile y = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
theorem radialProfile_eq_one {y : Fin 4 → ℝ} (h : ∑ i, y i ^ 2 ≤ 1) : radialProfile y = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
theorem radialProfile_nonneg (y : Fin 4 → ℝ) : 0 ≤ radialProfile y := Real.smoothTransition.nonneg _
theorem radialProfile_le_one (y : Fin 4 → ℝ) : radialProfile y ≤ 1 := Real.smoothTransition.le_one _
theorem sum_sq_le_four_mul_sq {y : Fin 4 → ℝ} {r : ℝ} (h : ∀ i, |y i| ≤ r) : ∑ i, y i ^ 2 ≤ 4 * r ^ 2 := by
  have h1 : ∀ i, y i ^ 2 ≤ r ^ 2 := fun i => sq_le_sq' (by linarith [abs_le.1 (h i)]) (abs_le.1 (h i)).2
  calc ∑ i, y i ^ 2 ≤ ∑ _i : Fin 4, r ^ 2 := Finset.sum_le_sum fun i _ => h1 i
    _ = 4 * r ^ 2 := by simp
theorem tsupport_radialProfile_subset : tsupport radialProfile ⊆ {y : Fin 4 → ℝ | ∑ i, y i ^ 2 ≤ 2} := by
  have hc : IsClosed {y : Fin 4 → ℝ | ∑ i, y i ^ 2 ≤ 2} :=
    isClosed_le (by fun_prop) continuous_const
  refine closure_minimal ?_ hc
  intro y hy
  by_contra h
  exact hy (radialProfile_eq_zero (le_of_lt (not_le.1 h)))
theorem radialProfile_hasCompactSupport : HasCompactSupport radialProfile := by
  have hb : Bornology.IsBounded {y : Fin 4 → ℝ | ∑ i, y i ^ 2 ≤ 2} := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin 4 → ℝ)) (r := 2)).subset ?_
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
    have h1 : y i ^ 2 ≤ ∑ j, y j ^ 2 :=
      Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : y i ^ 2 ≤ 2 := h1.trans hy
    rw [Real.norm_eq_abs]
    exact abs_le_of_sq_le_sq' (by nlinarith) (by norm_num) |> fun h => abs_le.2 h
  have hc : IsClosed {y : Fin 4 → ℝ | ∑ i, y i ^ 2 ≤ 2} :=
    isClosed_le (by fun_prop) continuous_const
  exact (Metric.isCompact_of_isClosed_isBounded hc hb).of_isClosed_subset (isClosed_tsupport _)
    tsupport_radialProfile_subset
def scaledBump (b : ℝ) (c x : Fin 4 → ℝ) : ℝ := radialProfile ((2 / b) • (x - c))
theorem scaledBump_contDiff (b : ℝ) (c : Fin 4 → ℝ) : ContDiff ℝ ∞ (scaledBump b c) := by
  unfold scaledBump
  exact radialProfile_contDiff.comp (by fun_prop)
theorem tsupport_scaledBump_subset {b : ℝ} (hb : 0 < b) (c : Fin 4 → ℝ) :
    tsupport (scaledBump b c) ⊆ closedBallR4 c (3 / 4 * b) := by
  have hc : IsClosed {x : Fin 4 → ℝ | ∑ i, ((2 / b) • (x - c)) i ^ 2 ≤ 2} :=
    isClosed_le (by fun_prop) continuous_const
  have h1 : tsupport (scaledBump b c) ⊆ {x : Fin 4 → ℝ | ∑ i, ((2 / b) • (x - c)) i ^ 2 ≤ 2} := by
    refine closure_minimal ?_ hc
    intro y hy
    by_contra h
    exact hy (radialProfile_eq_zero (le_of_lt (not_le.1 h)))
  intro x hx
  have h2 := h1 hx
  simp only [Set.mem_ofPred_eq, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_pow] at h2
  rw [← Finset.mul_sum] at h2
  show euclidNormVec (x - c) ≤ 3 / 4 * b
  unfold euclidNormVec
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have h3 : (2 / b) ^ 2 = 4 / b ^ 2 := by field_simp; norm_num
  rw [h3] at h2
  have hb2 : 0 < b ^ 2 := by positivity
  have h4 : ∑ i, (x - c) i ^ 2 ≤ b ^ 2 / 2 := by
    have h5' : 4 / b ^ 2 * ∑ i, (x i - c i) ^ 2 ≤ 2 := h2
    have h5 : ∑ i, (x i - c i) ^ 2 ≤ 2 * b ^ 2 / 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hb2] at h5'
      linarith
    simp only [Pi.sub_apply]
    linarith
  nlinarith
theorem scaledBump_self {b : ℝ} (c : Fin 4 → ℝ) : scaledBump b c c = 1 := by
  unfold scaledBump
  simp [radialProfile_eq_one]
theorem scaledBump_le_one (b : ℝ) (c x : Fin 4 → ℝ) : scaledBump b c x ≤ 1 := radialProfile_le_one _
theorem scaledBump_nonneg (b : ℝ) (c x : Fin 4 → ℝ) : 0 ≤ scaledBump b c x := radialProfile_nonneg _
theorem scaledBump_hasCompactSupport {b : ℝ} (hb : 0 < b) (c : Fin 4 → ℝ) : HasCompactSupport (scaledBump b c) := by
  unfold scaledBump
  rw [show (fun x => radialProfile ((2 / b) • (x - c))) = radialProfile ∘ ((Homeomorph.smulOfNeZero (2 / b) (by positivity)) ∘ (Homeomorph.subRight c)) from by
    funext x; simp]
  exact radialProfile_hasCompactSupport.comp_homeomorph ((Homeomorph.subRight c).trans (Homeomorph.smulOfNeZero (2 / b) (by positivity)))
theorem uniformNorm_scaledBump {b : ℝ} (c : Fin 4 → ℝ) : uniformNorm (scaledBump b c) = 1 := by
  unfold uniformNorm
  apply le_antisymm
  · refine ciSup_le fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (scaledBump_nonneg b c x)]
    exact scaledBump_le_one b c x
  · have hb : BddAbove (range fun x => ‖scaledBump b c x‖) := ⟨1, by
      rintro _ ⟨x, rfl⟩
      simp only [Real.norm_eq_abs, abs_of_nonneg (scaledBump_nonneg b c x)]
      exact scaledBump_le_one b c x⟩
    calc (1 : ℝ) = ‖scaledBump b c c‖ := by simp [scaledBump_self (b := b) c]
      _ ≤ _ := le_ciSup hb c
theorem le_integral_scaledBump {b : ℝ} (hb : 0 < b) (c : Fin 4 → ℝ) : b ^ 4 / 16 ≤ ∫ x, scaledBump b c x := by
  have hint : Integrable (scaledBump b c) :=
    ((scaledBump_contDiff b c).continuous).integrable_of_hasCompactSupport (scaledBump_hasCompactSupport hb c)
  set R : Set (Fin 4 → ℝ) := Icc (fun i => c i - b / 4) (fun i => c i + b / 4) with hR
  have hone : ∀ x ∈ R, scaledBump b c x = 1 := by
    intro x hx
    unfold scaledBump
    apply radialProfile_eq_one
    have h : ∀ i, |((2 / b) • (x - c)) i| ≤ 1 / 2 := by
      intro i
      have h1 := hx.1 i
      have h2 := hx.2 i
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 / b)]
      have h3 : |x i - c i| ≤ b / 4 := abs_le.2 ⟨by linarith, by linarith⟩
      calc 2 / b * |x i - c i| ≤ 2 / b * (b / 4) := by gcongr
        _ = 1 / 2 := by field_simp; norm_num
    have h4 := sum_sq_le_four_mul_sq h
    linarith
  have hvol : (volume R).toReal = b ^ 4 / 16 := by
    rw [hR, Real.volume_Icc_pi]
    simp only [Fin.prod_univ_four]
    have h1 : ∀ i, c i + b / 4 - (c i - b / 4) = b / 2 := fun i => by ring
    simp only [h1]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
    ring
  have h1 : ∫ x in R, scaledBump b c x = b ^ 4 / 16 := by
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (1 : ℝ)) hone]
    rw [setIntegral_const, Measure.real, hvol]
    simp
  rw [← h1]
  exact setIntegral_le_integral hint (Eventually.of_forall (scaledBump_nonneg b c))
theorem radialProfile_lipschitz : ∃ C : ℝ, 0 < C ∧ ∀ u v : Fin 4 → ℝ, |radialProfile u - radialProfile v| ≤ C * ‖u - v‖ := by
  obtain ⟨C, hC⟩ := radialProfile_contDiff.lipschitzWith_of_hasCompactSupport radialProfile_hasCompactSupport (by simp)
  refine ⟨C + 1, by positivity, fun u v => ?_⟩
  have h := hC.dist_le_mul u v
  rw [Real.dist_eq, dist_eq_norm] at h
  nlinarith [norm_nonneg (u - v)]
theorem scaledBump_isShapedBump {C ϑ d : ℝ} (hC : 0 < C)
    (hlip : ∀ u v : Fin 4 → ℝ, |radialProfile u - radialProfile v| ≤ C * ‖u - v‖)
    (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1 / 16777216) (hϑ2 : 64 * C * ϑ ≤ 1) (hd : 0 < d) (c : Fin 4 → ℝ) :
    IsShapedBump euclidDistR4 closedBallR4 (fun f => ∫ x, f x) d ϑ c (scaledBump (d / 32) c) := by
  have hb : 0 < d / 32 := by positivity
  have hbound : ∀ x y, ‖scaledBump (d / 32) c x - scaledBump (d / 32) c y‖ ≤ (64 * C / d) * euclidDistR4 x y := by
    intro x y
    rw [Real.norm_eq_abs]
    refine (hlip _ _).trans ?_
    have h1 : (2 / (d / 32)) • (x - c) - (2 / (d / 32)) • (y - c) = (2 / (d / 32)) • (x - y) := by
      rw [← smul_sub]; congr 1; abel
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 / (d / 32))]
    have h2 := pi_norm_le_euclidNormVec (x - y)
    have h3 : (0 : ℝ) < C * (2 / (d / 32)) := by positivity
    calc C * (2 / (d / 32) * ‖x - y‖) = C * (2 / (d / 32)) * ‖x - y‖ := by ring
      _ ≤ C * (2 / (d / 32)) * euclidNormVec (x - y) := by gcongr
      _ = 64 * C / d * euclidDistR4 x y := by
        unfold euclidDistR4
        field_simp
        ring
  refine ⟨⟨64 * C / d, by positivity, hbound⟩, scaledBump_nonneg _ c, ⟨c, ?_⟩, ?_, ?_, ?_⟩
  · rw [scaledBump_self]; exact one_ne_zero
  · intro x hx
    have h : euclidNormVec (x - c) ≤ 3 / 4 * (d / 32) := tsupport_scaledBump_subset hb c hx
    show euclidNormVec (x - c) ≤ d
    linarith
  · rw [uniformNorm_scaledBump]
    have h1 := le_integral_scaledBump hb c
    have h2 : (d / 32) ^ 4 / 16 = 1 / 16777216 * d ^ 4 := by ring
    have h3 : 0 < d ^ 4 := by positivity
    show ϑ * 1 * d ^ 4 ≤ ∫ x, scaledBump (d / 32) c x
    nlinarith
  · rw [uniformNorm_scaledBump]
    have h5 : bestLipschitzConstant euclidDistR4 (scaledBump (d / 32) c) ≤ 64 * C / d :=
      csInf_le ⟨0, fun _ h => h.1⟩ ⟨by positivity, hbound⟩
    refine h5.trans ?_
    rw [div_le_div_iff₀ hd (by positivity)]
    nlinarith
def axisPoint (d : ℝ) (i : Fin 4) : Fin 4 → ℝ := Pi.single 0 (2 * ((i : ℕ) : ℝ) * d)
def collinearBumps (d : ℝ) (i : Fin 4) : (Fin 4 → ℝ) → ℝ := scaledBump (d / 32) (axisPoint d i)
theorem euclidNormVec_single_zero (t : ℝ) : euclidNormVec (Pi.single 0 t : Fin 4 → ℝ) = |t| := by
  unfold euclidNormVec
  have h : ∑ μ, (Pi.single 0 t : Fin 4 → ℝ) μ ^ 2 = t ^ 2 := by
    simp [Pi.single_apply]
  rw [h, Real.sqrt_sq_eq_abs]
theorem axisPoint_sub (d : ℝ) (i j : Fin 4) :
    axisPoint d i - axisPoint d j = Pi.single 0 (2 * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * d) := by
  funext μ
  by_cases h : μ = 0
  · subst h
    simp [axisPoint]
    ring
  · simp [axisPoint, h]
theorem fin_four_index_gap {i j : Fin 4} (h : i ≠ j) :
    1 ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| ∧ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| ≤ 3 := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | norm_num
theorem collinearBumps_pair_mem {C ϑ d : ℝ} (hC : 0 < C)
    (hlip : ∀ u v : Fin 4 → ℝ, |radialProfile u - radialProfile v| ≤ C * ‖u - v‖)
    (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1 / 16777216) (hϑ2 : 64 * C * ϑ ≤ 1) (hd : 0 < d) {i j : Fin 4} (hij : i ≠ j) :
    (collinearBumps d i, collinearBumps d j) ∈ separatedPairsR4 d ϑ := by
  have hb : 0 < d / 32 := by positivity
  obtain ⟨hg1, hg2⟩ := fin_four_index_gap hij
  have hcc : euclidNormVec (axisPoint d i - axisPoint d j) = 2 * |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * d := by
    rw [axisPoint_sub, euclidNormVec_single_zero, abs_mul, abs_mul, abs_of_pos hd]
    norm_num
  refine ⟨axisPoint d i, axisPoint d j, scaledBump_isShapedBump hC hlip hϑ0 hϑ1 hϑ2 hd _,
    scaledBump_isShapedBump hC hlip hϑ0 hϑ1 hϑ2 hd _, ?_, ?_⟩
  · refine le_iInf₂ fun a ha => le_iInf₂ fun e he => ENNReal.ofReal_le_ofReal ?_
    have h1 : euclidNormVec (a - axisPoint d i) ≤ 3 / 4 * (d / 32) := tsupport_scaledBump_subset hb _ ha
    have h2 : euclidNormVec (e - axisPoint d j) ≤ 3 / 4 * (d / 32) := tsupport_scaledBump_subset hb _ he
    have h3 := abs_le.1 ((abs_apply_le_euclidNormVec _ 0).trans h1)
    have h4 := abs_le.1 ((abs_apply_le_euclidNormVec _ 0).trans h2)
    have h5 := abs_apply_le_euclidNormVec (a - e) 0
    have h6 : |(axisPoint d i - axisPoint d j) 0| = 2 * |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * d := by
      rw [axisPoint_sub]
      simp only [Pi.single_eq_same]
      rw [abs_mul, abs_mul, abs_of_pos hd]
      norm_num
    simp only [Pi.sub_apply] at h3 h4 h5 h6
    have h7 : 2 * d ≤ |axisPoint d i 0 - axisPoint d j 0| := by
      rw [h6]
      nlinarith
    have h8 : |axisPoint d i 0 - axisPoint d j 0| ≤ |a 0 - e 0| + 3 / 4 * (d / 32) * 2 := by
      have p := le_abs_self (a 0 - e 0)
      have n := neg_abs_le (a 0 - e 0)
      rw [abs_le]
      constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
    linarith
  · have h0 : axisPoint d i ∈ tsupport (collinearBumps d i) := subset_tsupport _ (by
      show scaledBump (d / 32) (axisPoint d i) (axisPoint d i) ≠ 0
      rw [scaledBump_self]; exact one_ne_zero)
    have h1 : axisPoint d j ∈ tsupport (collinearBumps d j) := subset_tsupport _ (by
      show scaledBump (d / 32) (axisPoint d j) (axisPoint d j) ≠ 0
      rw [scaledBump_self]; exact one_ne_zero)
    refine (iInf₂_le (axisPoint d i) h0).trans ((iInf₂_le (axisPoint d j) h1).trans (ENNReal.ofReal_le_ofReal ?_))
    rw [hcc]
    nlinarith
theorem collinearBumps_mem_collinear {C ϑ d : ℝ} (hC : 0 < C)
    (hlip : ∀ u v : Fin 4 → ℝ, |radialProfile u - radialProfile v| ≤ C * ‖u - v‖)
    (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1 / 16777216) (hϑ2 : 64 * C * ϑ ≤ 1) (hd : 0 < d) :
    collinearBumps d ∈ collinearQuadsR4 d ϑ := by
  have hb : 0 < d / 32 := by positivity
  have hϑle : ϑ ≤ 1 := by linarith
  refine ⟨⟨⟨hd, hϑ0, hϑle⟩, fun i => ?_, fun i j hij => collinearBumps_pair_mem hC hlip hϑ0 hϑ1 hϑ2 hd hij⟩,
    axisPoint d, ⟨Pi.single 0 1, ?_, fun i j => ⟨2 * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * d, ?_⟩⟩, fun i => ?_⟩
  · exact ⟨(scaledBump_isShapedBump hC hlip hϑ0 hϑ1 hϑ2 hd _).1, scaledBump_nonneg _ _⟩
  · rw [euclidNormVec_single_zero]
    simp
  · rw [axisPoint_sub]
    funext μ
    by_cases h : μ = 0
    · subst h
      simp
    · simp [h]
  · rw [euclideanTSupport_eq_tsupport]
    intro x hx
    have h : euclidNormVec (x - axisPoint d i) ≤ 3 / 4 * (d / 32) := tsupport_scaledBump_subset hb _ hx
    show euclidNormVec (x - axisPoint d i) ≤ d / 16
    linarith
theorem disjoint_of_le_setDistR4 {A B : Set (Fin 4 → ℝ)} {d : ℝ} (hd : 0 < d)
    (h : ENNReal.ofReal d ≤ setDistR4 A B) : Disjoint A B := by
  rw [Set.disjoint_left]
  intro a ha hb
  have h1 : setDistR4 A B ≤ ENNReal.ofReal (euclidNormVec (a - a)) :=
    (iInf₂_le a ha).trans (iInf₂_le a hb)
  have h0 : euclidNormVec (a - a) = 0 := by simp [euclidNormVec]
  rw [h0] at h1
  have h2 := h.trans h1
  simp at h2
  linarith
theorem collinearBumps_mem_disjointSupportTuples {C ϑ d : ℝ} (hC : 0 < C)
    (hlip : ∀ u v : Fin 4 → ℝ, |radialProfile u - radialProfile v| ≤ C * ‖u - v‖)
    (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1 / 16777216) (hϑ2 : 64 * C * ϑ ≤ 1) (hd : 0 < d) :
    collinearBumps d ∈ TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) 4 := by
  refine ⟨fun i => ⟨(scaledBump_contDiff _ _).of_le (by exact_mod_cast le_top), scaledBump_hasCompactSupport (by positivity) _,
    Set.subset_univ _⟩, fun i j hij => ?_⟩
  obtain ⟨x₁, x₂, -, -, h, -⟩ := collinearBumps_pair_mem hC hlip hϑ0 hϑ1 hϑ2 hd hij
  exact disjoint_of_le_setDistR4 hd h
theorem dyadicRescale_mem {n : ℕ} (i : ℕ) (X : SepTupleOfCard n) :
    dyadicRescale i X.1 ∈ TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) n := by
  have h2 : (2 : ℝ) ^ i ≠ 0 := by positivity
  let e : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) := Homeomorph.smulOfNeZero ((2 : ℝ) ^ i) h2
  have he : ∀ k, dyadicRescale i X.1 k = X.1 k ∘ e := fun k => rfl
  refine ⟨fun k => ⟨?_, ?_, Set.subset_univ _⟩, fun k l hkl => ?_⟩
  · exact (X.2.1 k).1.comp (by fun_prop)
  · rw [he]
    exact (X.2.1 k).2.1.comp_homeomorph e
  · have hd := X.2.2 hkl
    refine Set.disjoint_of_subset ?_ ?_ (hd.preimage e)
    · rw [he]
      exact tsupport_comp_subset_preimage _ e.continuous
    · rw [he]
      exact tsupport_comp_subset_preimage _ e.continuous
theorem partitions_fin_two :
    YangMills.Construction.ClusterExpansion.SymGraph.partitions (Fin 2) = {{Finset.univ}, {{0}, {1}}} := by
  have hcases : ∀ J : Finset (Fin 2), J = ∅ ∨ J = {0} ∨ J = {1} ∨ J = Finset.univ := by decide
  ext η
  simp only [YangMills.Construction.ClusterExpansion.SymGraph.partitions,
    YangMills.Construction.ClusterExpansion.SymGraph.IsPartition, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, hd, hU⟩
    have h0 := Finset.mem_univ (0 : Fin 2)
    have h1 := Finset.mem_univ (1 : Fin 2)
    rw [← hU] at h0 h1
    obtain ⟨J0, hJ0, h0J⟩ : ∃ J ∈ η, (0 : Fin 2) ∈ J := by simpa using h0
    obtain ⟨J1, hJ1, h1J⟩ : ∃ J ∈ η, (1 : Fin 2) ∈ J := by simpa using h1
    by_cases hu : Finset.univ ∈ η
    · left
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨hu, fun K hK => ?_⟩
      by_contra hKu
      have hdis : Disjoint K Finset.univ := hd hK hu hKu
      obtain ⟨e, he⟩ := hne K hK
      exact Finset.disjoint_left.1 hdis he (Finset.mem_univ e)
    · right
      have e0 : J0 = {0} := by
        rcases hcases J0 with rfl | rfl | rfl | rfl
        · simp at h0J
        · rfl
        · simp at h0J
        · exact absurd hJ0 hu
      have e1 : J1 = {1} := by
        rcases hcases J1 with rfl | rfl | rfl | rfl
        · simp at h1J
        · simp at h1J
        · rfl
        · exact absurd hJ1 hu
      subst e0 e1
      ext K
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hK
        rcases hcases K with rfl | rfl | rfl | rfl
        · exact absurd (hne _ hK) (by simp)
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd hK hu
      · rintro (rfl | rfl) <;> assumption
  · rintro (rfl | rfl)
    · refine ⟨by simp, by simp, by simp⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl <;> simp
      rotate_left
      · ext i
        fin_cases i <;> simp
      intro a ha b hb hab
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · show Disjoint ({0} : Finset (Fin 2)) {1}
        decide
      · show Disjoint ({1} : Finset (Fin 2)) {0}
        decide
      · exact absurd rfl hab
def pairFst (X : SepTupleOfCard 2) : SepTupleOfCard 1 := sepRestrict X {0}
def pairSnd (X : SepTupleOfCard 2) : SepTupleOfCard 1 := sepRestrict X {1}
theorem cumulant_pair (σ : SepTuple → ℝ) (X : SepTupleOfCard 2) :
    TestSpaces.cumulant σ X = σ ⟨2, X⟩ - σ ⟨1, pairFst X⟩ * σ ⟨1, pairSnd X⟩ := by
  have hu := TestSpaces.sepRestrict_univ X
  have hne : ({Finset.univ} : Finset (Finset (Fin 2))) ≠ {{0}, {1}} := by decide
  have e0 : (⟨_, sepRestrict X {0}⟩ : SepTuple) = ⟨1, pairFst X⟩ := rfl
  have e1 : (⟨_, sepRestrict X {1}⟩ : SepTuple) = ⟨1, pairSnd X⟩ := rfl
  unfold TestSpaces.cumulant
  rw [partitions_fin_two, Finset.sum_pair hne]
  have h2 : ({{0}, {1}} : Finset (Finset (Fin 2))).card = 2 := by decide
  have h01 : ({0} : Finset (Fin 2)) ≠ {1} := by decide
  rw [h2, Finset.prod_pair h01]
  simp only [Finset.card_singleton, Finset.prod_singleton]
  rw [hu, e0, e1]
  norm_num
  ring
theorem pairFst_apply (X : SepTupleOfCard 2) : (pairFst X).1 0 = X.1 0 := by
  show X.1 ((({0} : Finset (Fin 2))).orderEmbOfFin (Finset.card_singleton _) (0 : Fin 1)) = _
  rw [Finset.orderEmbOfFin_singleton]
theorem pairSnd_apply (X : SepTupleOfCard 2) : (pairSnd X).1 0 = X.1 1 := by
  show X.1 ((({1} : Finset (Fin 2))).orderEmbOfFin (Finset.card_singleton _) (0 : Fin 1)) = _
  rw [Finset.orderEmbOfFin_singleton]
theorem evalOnMap_pos_of_connectedFn_pos {σ : TupleFunctional} {X : SepTupleOfCard 2} {c : ℝ}
    (hone : ∀ Y : SepTupleOfCard 1, connectedFn σ Y = c * ∫ x, Y.1 0 x)
    (h0 : ∀ x, 0 ≤ X.1 0 x) (h1 : ∀ x, 0 ≤ X.1 1 x) (hX : 0 < connectedFn σ X) :
    0 < evalOnMap σ ⟨2, X⟩ := by
  have e := cumulant_pair (evalOnMap σ) X
  have a0 : evalOnMap σ ⟨1, pairFst X⟩ = c * ∫ x, X.1 0 x := by
    have h := hone (pairFst X)
    rw [pairFst_apply] at h
    rw [← h]
    exact (TestSpaces.cumulant_single _ _).symm
  have a1 : evalOnMap σ ⟨1, pairSnd X⟩ = c * ∫ x, X.1 1 x := by
    have h := hone (pairSnd X)
    rw [pairSnd_apply] at h
    rw [← h]
    exact (TestSpaces.cumulant_single _ _).symm
  have i0 : 0 ≤ ∫ x, X.1 0 x := integral_nonneg h0
  have i1 : 0 ≤ ∫ x, X.1 1 x := integral_nonneg h1
  have hp : 0 ≤ evalOnMap σ ⟨1, pairFst X⟩ * evalOnMap σ ⟨1, pairSnd X⟩ := by
    rw [a0, a1]
    nlinarith [mul_nonneg i0 i1, mul_self_nonneg c, mul_nonneg (mul_self_nonneg c) (mul_nonneg i0 i1)]
  have hc : connectedFn σ X = _ := e
  rw [hc] at hX
  linarith
def succGauge (s : ℕ) : ℝ := (s : ℝ) + 1
theorem succGauge_isSubexpGrowth : YangMills.Construction.RoomFunctions.IsSubexpGrowth succGauge := by apply _root_.YangMills.Construction.QuaternionicWilsonModel.TopLimitsRealNonzero.linearGauge_isSubexpGrowth <;> assumption
theorem log_inv_meshSize {L : ℕ} (hL : 0 < L) (K : ℕ) :
    Real.log (1 / YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)) = K * Real.log L := by apply _root_.YangMills.Construction.QuaternionicWilsonModel.TopLimitsRealNonzero.log_inv_meshSize <;> assumption
theorem asymptoticFreedomSlope_pos : 0 < asymptoticFreedomSlope := by apply _root_.YangMills.Construction.QuaternionicWilsonModel.TopLimitsRealNonzero.asymptoticFreedomSlope_pos <;> assumption
theorem tendsto_coupling_atTop {ℓ : StepParameters} {Bs c₅ lam CT g : ℝ} {Nw : ℕ} (hL : 2 ≤ ℓ.side)
    (hc : CouplingConditions ℓ Bs c₅ lam Nw CT g) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ)
    (hp : ∀ j, IsFirstPassagePair ℓ Bs g (K j) (β j)) (hK : Tendsto (fun j => (K j : ℕ)) atTop atTop) :
    Tendsto β atTop atTop := by
  obtain ⟨δ, hδ, hb⟩ := hc.passage.asymptotically_free
  have hr : Tendsto (fun j => β j / Real.log (1 / YangMills.Construction.PeriodicLattice.meshSize ℓ.side (((K j : ℕ) : ℕ) : ℤ))) atTop
      (𝓝 asymptoticFreedomSlope) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun j => hb _ _ (K j).2 (hp j)) (hδ.comp hK)
  have hl : 0 < Real.log ℓ.side := Real.log_pos (by exact_mod_cast (by omega : 1 < ℓ.side))
  have hden : Tendsto (fun j => Real.log (1 / YangMills.Construction.PeriodicLattice.meshSize ℓ.side (((K j : ℕ) : ℕ) : ℤ))) atTop atTop := by
    have e : (fun j => Real.log (1 / YangMills.Construction.PeriodicLattice.meshSize ℓ.side (((K j : ℕ) : ℕ) : ℤ))) =
        fun j => ((K j : ℕ) : ℝ) * Real.log ℓ.side := by
      funext j
      exact log_inv_meshSize (by omega) _
    rw [e]
    exact (tendsto_natCast_atTop_atTop.comp hK).atTop_mul_const hl
  refine (hden.atTop_mul_pos asymptoticFreedomSlope_pos hr).congr' ?_
  filter_upwards [hden.eventually_gt_atTop 0] with j hj
  field_simp
end YangMills.Construction.NonGaussianLimits
end

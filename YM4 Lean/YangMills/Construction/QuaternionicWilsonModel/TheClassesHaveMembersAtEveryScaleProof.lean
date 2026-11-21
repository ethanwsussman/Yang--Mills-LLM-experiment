import YangMills.Construction.QuaternionicWilsonModel.WhatTheTopGivesAtEveryCouplingProof
import YangMills.Construction.Torus.CollinearQuadruples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TopAux.NonemptyTestClasses
open Filter Set MeasureTheory
open scoped ContDiff Topology
open TestFunctions TorusMetric QuadrupleClasses QuadrupleClasses.Collinear
theorem abs_le_euclidNormVec (v : Fin 4 → ℝ) (i : Fin 4) : |v i| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem norm_le_euclidNormVec (v : Fin 4 → ℝ) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
def unitBump (y : Fin 4 → ℝ) : ℝ := Real.smoothTransition (2 - ∑ i, y i ^ 2)
theorem unitBump_contDiff : ContDiff ℝ ∞ unitBump := by
  unfold unitBump
  refine Real.smoothTransition.contDiff.comp ?_
  fun_prop
theorem unitBump_eq_zero {y : Fin 4 → ℝ} (h : 2 ≤ ∑ i, y i ^ 2) : unitBump y = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
theorem unitBump_eq_one {y : Fin 4 → ℝ} (h : ∑ i, y i ^ 2 ≤ 1) : unitBump y = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
theorem unitBump_nonneg (y : Fin 4 → ℝ) : 0 ≤ unitBump y := Real.smoothTransition.nonneg _
theorem unitBump_le_one (y : Fin 4 → ℝ) : unitBump y ≤ 1 := Real.smoothTransition.le_one _
theorem sum_sq_le_of_abs_le {y : Fin 4 → ℝ} {r : ℝ} (h : ∀ i, |y i| ≤ r) :
    ∑ i, y i ^ 2 ≤ 4 * r ^ 2 := by apply _root_.YangMills.Construction.NonGaussianLimits.sum_sq_le_four_mul_sq <;> assumption
theorem tsupport_unitBump_subset : tsupport unitBump ⊆ {y : Fin 4 → ℝ | ∑ i, y i ^ 2 ≤ 2} := by
  have hc : IsClosed {y : Fin 4 → ℝ | ∑ i, y i ^ 2 ≤ 2} :=
    isClosed_le (by fun_prop) continuous_const
  refine closure_minimal ?_ hc
  intro y hy
  by_contra h
  exact hy (unitBump_eq_zero (le_of_lt (not_le.1 h)))
theorem unitBump_hasCompactSupport : HasCompactSupport unitBump := by
  have hb : Bornology.IsBounded {y : Fin 4 → ℝ | ∑ i, y i ^ 2 ≤ 2} := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin 4 → ℝ)) (r := 2)).subset ?_
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
    have h1 : y i ^ 2 ≤ ∑ j, y j ^ 2 :=
      Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : y i ^ 2 ≤ 2 := h1.trans hy
    rw [Real.norm_eq_abs]
    exact abs_le.2 (abs_le_of_sq_le_sq' (by nlinarith) (by norm_num))
  have hc : IsClosed {y : Fin 4 → ℝ | ∑ i, y i ^ 2 ≤ 2} :=
    isClosed_le (by fun_prop) continuous_const
  exact (Metric.isCompact_of_isClosed_isBounded hc hb).of_isClosed_subset (isClosed_tsupport _)
    tsupport_unitBump_subset
theorem exists_unitBump_lipschitz :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : Fin 4 → ℝ, |unitBump u - unitBump v| ≤ C * ‖u - v‖ := by
  obtain ⟨C, hC⟩ := unitBump_contDiff.lipschitzWith_of_hasCompactSupport unitBump_hasCompactSupport (by simp)
  refine ⟨C + 1, by positivity, fun u v => ?_⟩
  have h := hC.dist_le_mul u v
  rw [Real.dist_eq, dist_eq_norm] at h
  nlinarith [norm_nonneg (u - v)]
def scaledBump (d : ℝ) (c : Fin 4 → ℝ) (x : Fin 4 → ℝ) : ℝ := unitBump ((32 / d) • (x - c))
theorem scaledBump_contDiff (d : ℝ) (c : Fin 4 → ℝ) : ContDiff ℝ ∞ (scaledBump d c) := by
  unfold scaledBump
  exact unitBump_contDiff.comp (by fun_prop)
theorem tsupport_scaledBump_subset {d : ℝ} (hd : 0 < d) (c : Fin 4 → ℝ) :
    tsupport (scaledBump d c) ⊆ closedBallR4 c (d / 16) := by
  have hc : IsClosed {x : Fin 4 → ℝ | ∑ i, ((32 / d) • (x - c)) i ^ 2 ≤ 2} :=
    isClosed_le (by fun_prop) continuous_const
  have h1 : tsupport (scaledBump d c) ⊆ {x : Fin 4 → ℝ | ∑ i, ((32 / d) • (x - c)) i ^ 2 ≤ 2} := by
    refine closure_minimal ?_ hc
    intro y hy
    by_contra h
    exact hy (unitBump_eq_zero (le_of_lt (not_le.1 h)))
  intro x hx
  have h2 : ∑ i, ((32 / d) • (x - c)) i ^ 2 ≤ 2 := h1 hx
  have h3 : ∑ i, ((32 / d) • (x - c)) i ^ 2 = (32 / d) ^ 2 * ∑ i, (x - c) i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_pow]
  rw [h3] at h2
  show euclidNormVec (x - c) ≤ d / 16
  unfold euclidNormVec
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h4 : (32 / d) ^ 2 * d ^ 2 = 1024 := by
    field_simp
    norm_num
  have hd2 : 0 < d ^ 2 := by positivity
  have h6 : 1024 * ∑ i, (x - c) i ^ 2 ≤ 2 * d ^ 2 := by
    calc 1024 * ∑ i, (x - c) i ^ 2 = ((32 / d) ^ 2 * ∑ i, (x - c) i ^ 2) * d ^ 2 := by
          rw [← h4]; ring
      _ ≤ 2 * d ^ 2 := by gcongr
  have h7 : (d / 16) ^ 2 = d ^ 2 / 256 := by ring
  rw [h7]
  linarith
theorem scaledBump_self (d : ℝ) (c : Fin 4 → ℝ) : scaledBump d c c = 1 := by
  unfold scaledBump
  simp [unitBump_eq_one]
theorem scaledBump_le_one (d : ℝ) (c x : Fin 4 → ℝ) : scaledBump d c x ≤ 1 := unitBump_le_one _
theorem scaledBump_nonneg (d : ℝ) (c x : Fin 4 → ℝ) : 0 ≤ scaledBump d c x := unitBump_nonneg _
theorem scaledBump_hasCompactSupport {d : ℝ} (hd : 0 < d) (c : Fin 4 → ℝ) :
    HasCompactSupport (scaledBump d c) := by
  have h2 : (32 / d) ≠ 0 := by positivity
  rw [show scaledBump d c = unitBump ∘ ((Homeomorph.subRight c).trans (Homeomorph.smulOfNeZero (32 / d) h2)) from by
    funext x; simp [scaledBump]]
  exact unitBump_hasCompactSupport.comp_homeomorph _
theorem uniformNorm_scaledBump {d : ℝ} (c : Fin 4 → ℝ) : uniformNorm (scaledBump d c) = 1 := by
  unfold uniformNorm
  apply le_antisymm
  · refine ciSup_le fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (scaledBump_nonneg d c x)]
    exact scaledBump_le_one d c x
  · have hb : BddAbove (range fun x => ‖scaledBump d c x‖) := ⟨1, by
      rintro _ ⟨x, rfl⟩
      simp only [Real.norm_eq_abs, abs_of_nonneg (scaledBump_nonneg d c x)]
      exact scaledBump_le_one d c x⟩
    calc (1 : ℝ) = ‖scaledBump d c c‖ := by simp [scaledBump_self d c]
      _ ≤ _ := le_ciSup hb c
theorem le_integral_scaledBump {d : ℝ} (hd : 0 < d) (c : Fin 4 → ℝ) :
    d ^ 4 / 32 ^ 4 ≤ ∫ x, scaledBump d c x := by
  have hint : Integrable (scaledBump d c) :=
    ((scaledBump_contDiff d c).continuous).integrable_of_hasCompactSupport (scaledBump_hasCompactSupport hd c)
  set Q : Set (Fin 4 → ℝ) := Icc (fun i => c i - d / 64) (fun i => c i + d / 64) with hQ
  have hone : ∀ x ∈ Q, scaledBump d c x = 1 := by
    intro x hx
    unfold scaledBump
    apply unitBump_eq_one
    have h : ∀ i, |((32 / d) • (x - c)) i| ≤ 1 / 2 := by
      intro i
      have h1 := hx.1 i
      have h2 := hx.2 i
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [abs_mul, abs_of_pos (by positivity : 0 < 32 / d)]
      have h3 : |x i - c i| ≤ d / 64 := abs_le.2 ⟨by linarith, by linarith⟩
      calc 32 / d * |x i - c i| ≤ 32 / d * (d / 64) := by gcongr
        _ = 1 / 2 := by field_simp; norm_num
    have := sum_sq_le_of_abs_le h
    linarith
  have hvol : (volume Q).toReal = d ^ 4 / 32 ^ 4 := by
    rw [hQ, Real.volume_Icc_pi]
    simp only [Fin.prod_univ_four]
    have : ∀ i, c i + d / 64 - (c i - d / 64) = d / 32 := fun i => by ring
    simp only [this]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal (by positivity)]
    ring
  have h1 : ∫ x in Q, scaledBump d c x = d ^ 4 / 32 ^ 4 := by
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (1 : ℝ)) hone]
    rw [setIntegral_const, Measure.real, hvol]
    simp
  rw [← h1]
  exact setIntegral_le_integral hint (Eventually.of_forall (scaledBump_nonneg d c))
theorem scaledBump_isShapedBump {C ϑ d : ℝ} (hC : 0 < C)
    (hlip : ∀ u v : Fin 4 → ℝ, |unitBump u - unitBump v| ≤ C * ‖u - v‖)
    (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1 / 32 ^ 4) (hϑ2 : 32 * C * ϑ ≤ 1) (hd : 0 < d) (c : Fin 4 → ℝ) :
    IsShapedBump euclidDistR4 closedBallR4 (fun f => ∫ x, f x) d ϑ c (scaledBump d c) := by
  have hbound : ∀ x y, ‖scaledBump d c x - scaledBump d c y‖ ≤ (32 * C / d) * euclidDistR4 x y := by
    intro x y
    rw [Real.norm_eq_abs]
    refine (hlip _ _).trans ?_
    have h1 : (32 / d) • (x - c) - (32 / d) • (y - c) = (32 / d) • (x - y) := by
      rw [← smul_sub]; congr 1; abel
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 32 / d)]
    have h2 := norm_le_euclidNormVec (x - y)
    have h3 : (0 : ℝ) < C * (32 / d) := by positivity
    calc C * (32 / d * ‖x - y‖) = C * (32 / d) * ‖x - y‖ := by ring
      _ ≤ C * (32 / d) * euclidNormVec (x - y) := by gcongr
      _ = 32 * C / d * euclidDistR4 x y := by unfold euclidDistR4; ring
  refine ⟨⟨32 * C / d, by positivity, hbound⟩, scaledBump_nonneg d c, ⟨c, ?_⟩, ?_, ?_, ?_⟩
  · rw [scaledBump_self]; exact one_ne_zero
  · intro x hx
    have h : euclidNormVec (x - c) ≤ d / 16 := tsupport_scaledBump_subset hd c hx
    show euclidNormVec (x - c) ≤ d
    linarith
  · rw [uniformNorm_scaledBump]
    have := le_integral_scaledBump hd c
    have h4 : ϑ * 1 * d ^ 4 ≤ 1 / 32 ^ 4 * d ^ 4 := by
      have : 0 < d ^ 4 := by positivity
      nlinarith
    show ϑ * 1 * d ^ 4 ≤ ∫ x, scaledBump d c x
    have h5 : 1 / 32 ^ 4 * d ^ 4 = d ^ 4 / 32 ^ 4 := by ring
    linarith
  · rw [uniformNorm_scaledBump]
    have h5 : bestLipschitzConstant euclidDistR4 (scaledBump d c) ≤ 32 * C / d :=
      csInf_le ⟨0, fun _ h => h.1⟩ ⟨by positivity, hbound⟩
    refine h5.trans ?_
    rw [div_le_div_iff₀ hd (by positivity)]
    nlinarith
def lineCentre (d : ℝ) (i : Fin 4) : Fin 4 → ℝ := Pi.single 0 (5 / 4 * d * ((i : ℕ) : ℝ))
def bumpQuadruple (d : ℝ) : Fin 4 → (Fin 4 → ℝ) → ℝ := fun i => scaledBump d (lineCentre d i)
theorem lineCentre_zero (d : ℝ) (i : Fin 4) : lineCentre d i 0 = 5 / 4 * d * ((i : ℕ) : ℝ) := by
  simp [lineCentre]
theorem le_abs_lineCentre_sub {d : ℝ} (hd : 0 < d) {i j : Fin 4} (h : i ≠ j) :
    5 / 4 * d ≤ |lineCentre d i 0 - lineCentre d j 0| := by
  rw [lineCentre_zero, lineCentre_zero, ← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 5 / 4 * d)]
  have h1 : (1 : ℝ) ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
    have h2 : ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) ≠ 0 := by
      intro h3
      apply h
      ext
      omega
    have h3 := Int.one_le_abs h2
    exact_mod_cast h3
  nlinarith
theorem euclidNormVec_lineCentre_sub (d : ℝ) (i j : Fin 4) :
    euclidNormVec (lineCentre d i - lineCentre d j) =
      |5 / 4 * d * ((i : ℕ) : ℝ) - 5 / 4 * d * ((j : ℕ) : ℝ)| := by
  unfold euclidNormVec
  have h : ∑ μ, (lineCentre d i - lineCentre d j) μ ^ 2 =
      (5 / 4 * d * ((i : ℕ) : ℝ) - 5 / 4 * d * ((j : ℕ) : ℝ)) ^ 2 := by
    simp [lineCentre, Fin.sum_univ_four, Pi.single_apply]
  rw [h, Real.sqrt_sq_eq_abs]
theorem le_setDistR4_bumpQuadruple {d : ℝ} (hd : 0 < d) {i j : Fin 4} (h : i ≠ j) :
    ENNReal.ofReal d ≤ setDistR4 (tsupport (bumpQuadruple d i)) (tsupport (bumpQuadruple d j)) := by
  refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal ?_
  have h1 : euclidNormVec (a - lineCentre d i) ≤ d / 16 := tsupport_scaledBump_subset hd _ ha
  have h2 : euclidNormVec (b - lineCentre d j) ≤ d / 16 := tsupport_scaledBump_subset hd _ hb
  have h3 := abs_le.1 ((abs_le_euclidNormVec _ 0).trans h1)
  have h4 := abs_le.1 ((abs_le_euclidNormVec _ 0).trans h2)
  have h6 := abs_le_euclidNormVec (a - b) 0
  have h7 := le_abs_lineCentre_sub hd h
  simp only [Pi.sub_apply] at h3 h4 h6
  refine le_trans ?_ h6
  rcases abs_cases (lineCentre d i 0 - lineCentre d j 0) with ⟨e, -⟩ | ⟨e, -⟩
  · rw [e] at h7
    exact le_abs.2 (Or.inl (by linarith [h3.1, h4.2]))
  · rw [e] at h7
    exact le_abs.2 (Or.inr (by linarith [h3.2, h4.1]))
theorem bumpQuadruple_pair_mem {C ϑ d : ℝ} (hC : 0 < C)
    (hlip : ∀ u v : Fin 4 → ℝ, |unitBump u - unitBump v| ≤ C * ‖u - v‖)
    (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1 / 32 ^ 4) (hϑ2 : 32 * C * ϑ ≤ 1) (hd : 0 < d) {i j : Fin 4}
    (h : i ≠ j) : (bumpQuadruple d i, bumpQuadruple d j) ∈ separatedPairsR4 d ϑ := by
  refine ⟨lineCentre d i, lineCentre d j, scaledBump_isShapedBump hC hlip hϑ0 hϑ1 hϑ2 hd _,
    scaledBump_isShapedBump hC hlip hϑ0 hϑ1 hϑ2 hd _, le_setDistR4_bumpQuadruple hd h, ?_⟩
  have h0 : lineCentre d i ∈ tsupport (bumpQuadruple d i) := subset_tsupport _ (by
    show scaledBump d (lineCentre d i) (lineCentre d i) ≠ 0
    rw [scaledBump_self]; exact one_ne_zero)
  have h1 : lineCentre d j ∈ tsupport (bumpQuadruple d j) := subset_tsupport _ (by
    show scaledBump d (lineCentre d j) (lineCentre d j) ≠ 0
    rw [scaledBump_self]; exact one_ne_zero)
  refine (iInf₂_le _ h0).trans ((iInf₂_le _ h1).trans (ENNReal.ofReal_le_ofReal ?_))
  rw [euclidNormVec_lineCentre_sub]
  have hi : ((i : ℕ) : ℝ) ≤ 3 := by exact_mod_cast Nat.le_of_lt_succ i.2
  have hj : ((j : ℕ) : ℝ) ≤ 3 := by exact_mod_cast Nat.le_of_lt_succ j.2
  refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith
theorem bumpQuadruple_mem_collinearQuadsR4 {C ϑ d : ℝ} (hC : 0 < C)
    (hlip : ∀ u v : Fin 4 → ℝ, |unitBump u - unitBump v| ≤ C * ‖u - v‖)
    (hϑ0 : 0 < ϑ) (hϑ : ϑ ≤ 1) (hϑ1 : ϑ ≤ 1 / 32 ^ 4) (hϑ2 : 32 * C * ϑ ≤ 1) (hd : 0 < d) :
    bumpQuadruple d ∈ collinearQuadsR4 d ϑ := by
  have hb := fun i => scaledBump_isShapedBump hC hlip hϑ0 hϑ1 hϑ2 hd (lineCentre d i)
  refine ⟨⟨⟨hd, hϑ0, hϑ⟩, fun i => ⟨(hb i).1, (hb i).2.1⟩, fun i j hij =>
    bumpQuadruple_pair_mem hC hlip hϑ0 hϑ1 hϑ2 hd hij⟩, lineCentre d, ⟨Pi.single 0 1, ?_, fun i j => ?_⟩,
    fun i => tsupport_scaledBump_subset hd _⟩
  · unfold euclidNormVec
    simp [Pi.single_apply]
  · refine ⟨5 / 4 * d * ((i : ℕ) : ℝ) - 5 / 4 * d * ((j : ℕ) : ℝ), ?_⟩
    funext μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [lineCentre]
    · simp [lineCentre, hμ]
theorem disjoint_of_le_setDistR4 {A B : Set (Fin 4 → ℝ)} {d : ℝ} (hd : 0 < d)
    (h : ENNReal.ofReal d ≤ setDistR4 A B) : Disjoint A B := by apply _root_.YangMills.Construction.NonGaussianLimits.disjoint_of_le_setDistR4 <;> assumption
theorem bumpQuadruple_comp_mem {d : ℝ} (hd : 0 < d) {n : ℕ} (φ : Fin n → Fin 4)
    (hφ : Function.Injective φ) :
    (fun i => bumpQuadruple d (φ i)) ∈ TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) n ∧
      TestSpaces.HasSmoothComponents univ fun i => bumpQuadruple d (φ i) := by
  refine ⟨⟨fun i => ⟨?_, scaledBump_hasCompactSupport hd _, subset_univ _⟩, fun i j hij =>
    disjoint_of_le_setDistR4 hd (le_setDistR4_bumpQuadruple hd fun h => hij (hφ h))⟩,
    fun i => ⟨scaledBump_contDiff _ _, scaledBump_hasCompactSupport hd _, subset_univ _⟩⟩
  exact (scaledBump_contDiff _ _).of_le (by exact_mod_cast le_top)
theorem contDiff_periodicSum {ℓ : ℝ} (hℓ : 0 < ℓ) {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : ContDiff ℝ ∞ (periodicSum ℓ f) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Fin 4 → ℝ)
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt ((R + ‖x‖ + 1) / ℓ)
  let S : Finset (Fin 4 → ℤ) := Finset.Icc (fun _ => -(N : ℤ)) (fun _ => (N : ℤ))
  have hloc : ∀ v ∈ Metric.ball x 1,
      periodicSum ℓ f v = ∑ k ∈ S, f (v + latticeTranslate ℓ k) := by
    intro v hv
    unfold periodicSum
    refine tsum_eq_sum fun k hk => ?_
    by_contra hne
    have h1 : v + latticeTranslate ℓ k ∈ Metric.closedBall (0 : Fin 4 → ℝ) R :=
      hR (subset_tsupport _ hne)
    have h2 : ‖v + latticeTranslate ℓ k‖ ≤ R := by simpa using h1
    have h3 : ‖v‖ ≤ ‖x‖ + 1 := by
      have h4 : ‖v - x‖ < 1 := by simpa [dist_eq_norm] using hv
      have h5 := norm_le_norm_add_norm_sub' v x
      linarith
    have h6 : ‖latticeTranslate ℓ k‖ ≤ R + ‖x‖ + 1 := by
      have h7 : latticeTranslate ℓ k = (v + latticeTranslate ℓ k) - v := by abel
      rw [h7]
      have h8 := norm_sub_le (v + latticeTranslate ℓ k) v
      linarith
    apply hk
    have hb : ∀ μ, |(k μ : ℝ)| ≤ N := by
      intro μ
      have h9 := (norm_le_pi_norm (latticeTranslate ℓ k) μ).trans h6
      have h10 : ℓ * |(k μ : ℝ)| ≤ R + ‖x‖ + 1 := by
        have h11 : ‖latticeTranslate ℓ k μ‖ = ℓ * |(k μ : ℝ)| := by
          simp [latticeTranslate, abs_of_pos hℓ]
        linarith
      have h12 : |(k μ : ℝ)| ≤ (R + ‖x‖ + 1) / ℓ := by
        rw [le_div_iff₀ hℓ]
        linarith
      linarith
    refine Finset.mem_Icc.2 ⟨fun μ => ?_, fun μ => ?_⟩
    · have := (abs_le.1 (hb μ)).1
      show -(N : ℤ) ≤ k μ
      exact_mod_cast this
    · have := (abs_le.1 (hb μ)).2
      show k μ ≤ (N : ℤ)
      exact_mod_cast this
  have hsum : ContDiff ℝ ∞ (fun v => ∑ k ∈ S, f (v + latticeTranslate ℓ k)) :=
    ContDiff.sum fun k _ => hf.comp (contDiff_id.add contDiff_const)
  exact hsum.contDiffAt.congr_of_eventuallyEq
    (Filter.eventually_of_mem (Metric.ball_mem_nhds x one_pos) hloc)
theorem periodize_isSmoothReal (s : Conventions.StandingParameters)
    (hℓ : 0 < PeriodicLattice.torusSide s.L s.m)
    {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    AmbientPoints.IsSmoothReal (E := .torus) (s := s) (periodize (PeriodicLattice.torusSide s.L s.m) f) := by
  unfold AmbientPoints.IsSmoothReal
  convert contDiff_periodicSum hℓ hf hc using 1
  exact funext fun v => periodize_torusProj _ f v
theorem mem_separatedTuples_torus (s : Conventions.StandingParameters) {d : ℝ} (hd : 0 < d)
    (hℓ : 0 < PeriodicLattice.torusSide s.L s.m) {n : ℕ} (T : Fin n → AmbientPoints.Pt s .torus → ℝ)
    (hs : ∀ i, AmbientPoints.IsSmoothReal (T i))
    (hsep : ∀ i j, i ≠ j → ENNReal.ofReal d ≤ setEuclidDist (S := PeriodicLattice.torusSide s.L s.m)
      (tsupport (X := Torus4 (PeriodicLattice.torusSide s.L s.m)) (T i))
      (tsupport (X := Torus4 (PeriodicLattice.torusSide s.L s.m)) (T j))) :
    T ∈ AmbientPoints.separatedTuples s .torus n := by
  have : Fact (0 < PeriodicLattice.torusSide s.L s.m) := ⟨hℓ⟩
  have : CompactSpace (AmbientPoints.Pt s .torus) := (AmbientPoints.homeomorphTorus s).symm.compactSpace
  refine ⟨fun i => ⟨(hs i).of_le (by exact_mod_cast le_top), (isClosed_tsupport _).isCompact⟩,
    fun i j hij => ?_⟩
  show Disjoint (tsupport (T i)) (tsupport (T j))
  rw [AmbientPoints.tsupport_eq_of_torus, AmbientPoints.tsupport_eq_of_torus]
  refine Set.disjoint_left.2 fun x hA hB => ?_
  have h0 : setEuclidDist (S := PeriodicLattice.torusSide s.L s.m)
      (tsupport (X := Torus4 (PeriodicLattice.torusSide s.L s.m)) (T i))
      (tsupport (X := Torus4 (PeriodicLattice.torusSide s.L s.m)) (T j)) ≤ 0 := by
    unfold setEuclidDist
    refine (iInf₂_le x hA).trans ((iInf₂_le x hB).trans ?_)
    have h1 : torusEuclidNorm (x - x) = 0 := AmbientPoints.pointDist_self (s := s) .torus x
    rw [h1]
    simp
  have := (hsep i j hij).trans h0
  simp only [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
  linarith
theorem nonemptyOnTorus_of_collinear (hQ : CollinearQuadruplesStatement) {ϑ d : ℝ} (hd : 0 < d)
    (hϑ : ϑ ∈ Ioc (0 : ℝ) 1) (hq : bumpQuadruple d ∈ collinearQuadsR4 d ϑ)
    (s : Conventions.StandingParameters) (h40 : 40 * d ≤ PeriodicLattice.torusSide s.L s.m) :
    NonemptyOnTorus s d ϑ := by
  have hℓ : 0 < PeriodicLattice.torusSide s.L s.m := by linarith
  obtain ⟨-, -, hall⟩ := hQ
  obtain ⟨-, -, -, -, -, htor⟩ := hall d ϑ ⟨hd, hϑ⟩
  obtain ⟨-, -, -, -, htr, -⟩ := htor s h40
  have hT : periodizedQuad s (bumpQuadruple d) ∈ collinearQuadsTorus s d ϑ :=
    (htr (bumpQuadruple d) hq.1).2.2.2 hq
  have hs : ∀ i, AmbientPoints.IsSmoothReal (E := .torus) (s := s)
      (periodizedQuad s (bumpQuadruple d) i) := fun i =>
    periodize_isSmoothReal s hℓ (scaledBump_contDiff _ _) (scaledBump_hasCompactSupport hd _)
  have hsep : ∀ i j, i ≠ j → ENNReal.ofReal d ≤ setEuclidDist (S := PeriodicLattice.torusSide s.L s.m)
      (tsupport (X := Torus4 (PeriodicLattice.torusSide s.L s.m))
        (periodizedQuad s (bumpQuadruple d) i))
      (tsupport (X := Torus4 (PeriodicLattice.torusSide s.L s.m))
        (periodizedQuad s (bumpQuadruple d) j)) := by
    intro i j hij
    obtain ⟨-, -, -, -, h, -⟩ := hT.1.2.2.2 i j hij
    exact h
  refine ⟨⟨⟨fun i => periodizedQuad s (bumpQuadruple d) (Fin.castLE (by norm_num) i),
    mem_separatedTuples_torus s hd hℓ _ (fun i => hs _) fun i j hij => hsep _ _ fun h =>
      hij (Fin.castLE_injective _ h)⟩, hT.1.2.2.2 _ _ (by decide), fun i => hs _⟩,
    ⟨⟨periodizedQuad s (bumpQuadruple d),
      mem_separatedTuples_torus s hd hℓ _ hs hsep⟩, hT, hs⟩⟩
theorem statement_of_collinear (hQ : CollinearQuadruplesStatement) : Statement := by
  obtain ⟨C, hC, hlip⟩ := exists_unitBump_lipschitz
  have h0 : 0 < min (1 / 32 ^ 4 : ℝ) (1 / (32 * C)) := lt_min (by norm_num) (by positivity)
  refine ⟨fun s d hd => ?_, min (1 / 32 ^ 4 : ℝ) (1 / (32 * C)),
    ⟨h0, (min_le_left _ _).trans (by norm_num)⟩, fun ϑ hϑ d hd => ?_⟩
  · have hL : (1 : ℝ) ≤ (s.L : ℝ) := by
      have := s.isAdmissible.2
      exact_mod_cast (by omega : 1 ≤ s.L)
    have h1 : (1 : ℝ) ≤ (s.L : ℝ) ^ (s.m : ℕ) := one_le_pow₀ hL
    have h2 : PeriodicLattice.torusSide s.L s.m = 2 * (s.L : ℝ) ^ (s.m : ℕ) := rfl
    rw [h2]
    linarith
  have hϑ1 : ϑ ≤ 1 / 32 ^ 4 := hϑ.2.trans (min_le_left _ _)
  have hϑ3 : ϑ ≤ 1 := hϑ1.trans (by norm_num)
  have hϑ2 : 32 * C * ϑ ≤ 1 := by
    have h1 : ϑ ≤ 1 / (32 * C) := hϑ.2.trans (min_le_right _ _)
    calc 32 * C * ϑ ≤ 32 * C * (1 / (32 * C)) := by gcongr
      _ = 1 := by field_simp
  have hq := bumpQuadruple_mem_collinearQuadsR4 hC hlip hϑ.1 hϑ3 hϑ1 hϑ2 hd
  obtain ⟨h2, h2s⟩ := bumpQuadruple_comp_mem hd (Fin.castLE (by norm_num : 2 ≤ 4)) (Fin.castLE_injective _)
  obtain ⟨h4, h4s⟩ := bumpQuadruple_comp_mem hd (id : Fin 4 → Fin 4) Function.injective_id
  exact ⟨⟨⟨⟨_, h2⟩, bumpQuadruple_pair_mem hC hlip hϑ.1 hϑ1 hϑ2 hd (by decide), h2s⟩, ⟨⟨_, h4⟩, hq, h4s⟩⟩,
    fun s h40 => nonemptyOnTorus_of_collinear hQ hd ⟨hϑ.1, hϑ3⟩ hq s h40⟩
end YangMills.Construction.TopAux.NonemptyTestClasses
end

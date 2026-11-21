import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.BaseFunctionals.PropertiesOfTheBumpFunctions
import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumpsProof
import YangMills.Construction.Continuum.ChosenSmoothFunctionsPartitionsOfUnityRotationsAndIntegrability
import YangMills.Construction.Continuum.FirstFactsOnTheTestSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff ENNReal Manifold
noncomputable section
namespace YangMills.Construction.WightmanReconstruction.SmoothToolkit
open YangMills.Construction.TestSpaces
theorem euclidNormVec_smul_of_nonneg {t : ℝ} (ht : 0 ≤ t) (x : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (t • x) = t * TorusMetric.euclidNormVec x := by
  unfold TorusMetric.euclidNormVec
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
theorem exists_mollifier_of_bumpFacts (hb : Mollifiers.BumpProperties.bumpFacts) :
    ExistsMollifier := by
  obtain ⟨_, hε, _, _⟩ := hb
  obtain ⟨⟨hsm, hnn, hint, hsupp, hinv⟩, _⟩ := hε 1 one_pos
  have hcd : ContDiff ℝ ∞ (Mollifiers.rescaledMollifier 1) := by
    have := Complex.reCLM.contDiff.comp hsm.1
    simpa [Function.comp_def] using this
  have hcs : HasCompactSupport (Mollifiers.rescaledMollifier 1) := by
    have h2 := hsm.2
    unfold EuclideanFour.closedSupport at h2
    have hset : {x : Fin 4 → ℝ | (Mollifiers.rescaledMollifier 1 x : ℂ) ≠ 0} =
        Function.support (Mollifiers.rescaledMollifier 1) := by
      ext x
      simp
    rw [hset] at h2
    exact h2
  have hout : ∀ x : Fin 4 → ℝ, 1 < TorusMetric.euclidNormVec x →
      Mollifiers.rescaledMollifier 1 x = 0 := by
    intro x hx
    by_contra hne
    have hmem : x ∈ EuclideanFour.closedSupport (Mollifiers.rescaledMollifier 1) :=
      subset_closure hne
    rw [hsupp] at hmem
    have hle : TorusMetric.euclidNormVec (x - 0) ≤ 1 := hmem
    rw [sub_zero] at hle
    exact absurd hle (not_le.2 hx)
  refine ⟨Mollifiers.rescaledMollifier 1, ⟨hcd, hcs, Set.subset_univ _⟩, hnn, hint, ?_, ?_⟩
  · intro x hx
    have hlim : Tendsto (fun t : ℝ => Mollifiers.rescaledMollifier 1 (t • x))
        (𝓝[>] (1 : ℝ)) (𝓝 (Mollifiers.rescaledMollifier 1 x)) := by
      have hc : Continuous fun t : ℝ => Mollifiers.rescaledMollifier 1 (t • x) :=
        hcd.continuous.comp (continuous_id.smul continuous_const)
      have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
      simpa using this
    have hzero : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ),
        Mollifiers.rescaledMollifier 1 (t • x) = 0 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht1 : (1 : ℝ) < t := ht
      apply hout
      rw [euclidNormVec_smul_of_nonneg (by linarith)]
      nlinarith
    exact tendsto_nhds_unique (hlim.congr' hzero) tendsto_const_nhds
  · intro R hR x
    have h := congrFun (hinv (⟨R, hR⟩ : Euclidean.O4)⁻¹) x
    rw [Euclidean.RigidMotion.ofO4_actFun, inv_inv] at h
    exact h
theorem multiDeriv_zero {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (φ : PointTuple n → F) : multiDeriv (0 : MultiIdx4 n) φ = φ := by
  unfold multiDeriv
  have inner : ∀ (i : Fin n) (l : List (Fin 4)) (h : PointTuple n → F),
      l.foldr (fun μ h' => (coordDeriv i μ)^[(0 : MultiIdx4 n) i μ] h') h = h := by
    intro i l h
    induction l with
    | nil => rfl
    | cons a l ih => simp
  have outer : ∀ l : List (Fin n), l.foldr (fun i h => (List.finRange 4).foldr
      (fun μ h' => (coordDeriv i μ)^[(0 : MultiIdx4 n) i μ] h') h) φ = φ := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.foldr_cons, inner]
      exact ih
  exact outer _
def decayWeight (u : Fin 4 → ℝ) : ℝ :=
  (1 + TorusMetric.euclidNormVec u ^ 2) ^ (-((5 : ℕ) : ℝ) / 2)
theorem decayWeight_nonneg (u : Fin 4 → ℝ) : 0 ≤ decayWeight u :=
  Real.rpow_nonneg (by positivity) _
theorem euclidNormVec_sq (u : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec u ^ 2 = ∑ μ, u μ ^ 2 := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_sq <;> assumption
theorem one_le_weight_mul_prod_decayWeight {n : ℕ} (x : PointTuple n) :
    1 ≤ (1 + tupleNorm x ^ 2) ^ (((5 * n : ℕ) : ℝ) / 2) * ∏ i, decayWeight (x i) := by
  have hsq : tupleNorm x ^ 2 = ∑ i, ∑ μ, x i μ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  set B : ℝ := 1 + tupleNorm x ^ 2 with hB
  have hB0 : 0 < B := by positivity
  have hpow : B ^ (((5 * n : ℕ) : ℝ) / 2) = ∏ _i : Fin n, B ^ ((5 : ℝ) / 2) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
      ← Real.rpow_mul hB0.le]
    congr 1
    push_cast
    ring
  rw [hpow, ← Finset.prod_mul_distrib]
  have hone : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (1 : ℝ) ≤ B ^ ((5 : ℝ) / 2) * decayWeight (x i) := by
    intro i _
    set b : ℝ := 1 + TorusMetric.euclidNormVec (x i) ^ 2 with hb
    have hb0 : 0 < b := by positivity
    have hbB : b ≤ B := by
      rw [hb, hB, euclidNormVec_sq, hsq]
      have := Finset.single_le_sum (f := fun i => ∑ μ, x i μ ^ 2)
        (fun j _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      linarith
    have hdf : decayWeight (x i) = (b ^ ((5 : ℝ) / 2))⁻¹ := by
      unfold decayWeight
      rw [← Real.rpow_neg hb0.le]
      congr 1
      push_cast
      ring
    rw [hdf]
    have hpos : 0 < b ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hb0 _
    rw [← div_eq_mul_inv, one_le_div hpos]
    exact Real.rpow_le_rpow hb0.le hbB (by norm_num)
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) hone
theorem schwartzIntegrable_of_basicProperties (hfirst : TestSpaces.Elementary.BasicProperties) :
    SchwartzIntegrable := by
  have hC : weightIntegral 5 < ⊤ := ((hfirst 1 one_pos).2.2.2.2 5 (by norm_num)).2.1
  have hmeas : Measurable decayWeight := by
    unfold decayWeight TorusMetric.euclidNormVec
    fun_prop
  have hI : Integrable decayWeight := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall decayWeight_nonneg)]
    exact hC
  have hCval : weightIntegral 5 = ENNReal.ofReal (∫ u, decayWeight u) :=
    (ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall decayWeight_nonneg)).symm
  intro n hn φ hφ
  obtain ⟨hsm, hfin⟩ := hφ
  have hN : weightedSeminorm (5 * n) φ < ⊤ := hfin _ (by omega)
  have hpt : ∀ x, ‖φ x‖ ≤ (weightedSeminorm (5 * n) φ).toReal * ∏ i, decayWeight (x i) := by
    intro x
    have hle : ENNReal.ofReal ((1 + tupleNorm x ^ 2) ^ (((5 * n : ℕ) : ℝ) / 2) *
        ‖multiDeriv (0 : MultiIdx4 n) φ x‖) ≤ weightedSeminorm (5 * n) φ :=
      le_iSup_of_le x (le_iSup_of_le 0 (le_iSup_of_le (by simp [idxOrder]) le_rfl))
    rw [multiDeriv_zero, ENNReal.ofReal_le_iff_le_toReal hN.ne] at hle
    have hone := one_le_weight_mul_prod_decayWeight x
    have hprod : 0 ≤ ∏ i, decayWeight (x i) :=
      Finset.prod_nonneg fun _ _ => decayWeight_nonneg _
    calc ‖φ x‖ ≤ ((1 + tupleNorm x ^ 2) ^ (((5 * n : ℕ) : ℝ) / 2) *
          ∏ i, decayWeight (x i)) * ‖φ x‖ := le_mul_of_one_le_left (norm_nonneg _) hone
      _ = ((1 + tupleNorm x ^ 2) ^ (((5 * n : ℕ) : ℝ) / 2) * ‖φ x‖) *
          ∏ i, decayWeight (x i) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hle hprod
  have hg : Integrable (fun x : PointTuple n => ∏ i, decayWeight (x i)) :=
    Integrable.fintype_prod (fun _ => hI)
  have hbound : Integrable
      (fun x : PointTuple n => (weightedSeminorm (5 * n) φ).toReal * ∏ i, decayWeight (x i)) :=
    hg.const_mul _
  have hint : Integrable φ :=
    hbound.mono' hsm.continuous.aestronglyMeasurable (Eventually.of_forall hpt)
  refine ⟨hint, ?_⟩
  have hval : ∫ x : PointTuple n, ∏ i, decayWeight (x i) = (∫ u, decayWeight u) ^ n := by
    simpa using integral_fintype_prod_volume_eq_pow (ι := Fin n) decayWeight
  have hl1 : lOneNorm φ ≤ (weightedSeminorm (5 * n) φ).toReal * (∫ u, decayWeight u) ^ n := by
    unfold lOneNorm
    calc ∫ x, ‖φ x‖ ≤ ∫ x : PointTuple n,
          (weightedSeminorm (5 * n) φ).toReal * ∏ i, decayWeight (x i) :=
          integral_mono hint.norm hbound hpt
      _ = _ := by rw [integral_const_mul, hval]
  have hI0 : 0 ≤ ∫ u, decayWeight u := integral_nonneg decayWeight_nonneg
  calc ENNReal.ofReal (lOneNorm φ)
      ≤ ENNReal.ofReal ((weightedSeminorm (5 * n) φ).toReal * (∫ u, decayWeight u) ^ n) :=
        ENNReal.ofReal_le_ofReal hl1
    _ = weightIntegral 5 ^ n * weightedSeminorm (5 * n) φ := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hN.ne,
          ENNReal.ofReal_pow hI0, ← hCval, mul_comm]
theorem exists_smoothStep : ∃ Λ, IsSmoothStepFunction Λ := by
  refine ⟨fun t => Real.smoothTransition (t - 1), ?_,
    fun t => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
    fun t ht => Real.smoothTransition.zero_of_nonpos (by linarith),
    fun t ht => Real.smoothTransition.one_of_one_le (by linarith)⟩
  exact Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
theorem vecLength_sq {a : ℕ} (x : Fin a → ℝ) : vecLength x ^ 2 = ∑ i, x i ^ 2 := by
  have h0 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [vecLength, Real.sq_sqrt h0]
  simp [dotProduct, sq]
theorem isBallCutoff_of_contDiff_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {Λ : ℝ → ℝ} (hΛ : IsSmoothStepFunction Λ) (len : E → ℝ)
    (hnn : ∀ x, 0 ≤ len x) (hle : ∀ x, ‖x‖ ≤ len x)
    (hsm : ContDiff ℝ ∞ fun x => len x ^ 2) :
    IsBallCutoff len (fun x => 1 - Λ (len x ^ 2)) := by
  obtain ⟨hsmooth, hbound, hzero, hone⟩ := hΛ
  have hsmooth' : ContDiff ℝ ∞ Λ := hsmooth
  have hfar : ∀ x, 2 ≤ len x → 1 - Λ (len x ^ 2) = 0 := by
    intro x hx
    have : 2 ≤ len x ^ 2 := by nlinarith
    rw [hone _ this]; ring
  refine ⟨⟨contDiff_const.sub (hsmooth'.comp hsm), ?_, Set.subset_univ _⟩, ?_, ?_, hfar⟩
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : E) 2) fun x hx => hfar x ?_
    have : 2 < ‖x‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
    linarith [hle x]
  · intro x
    have := hbound (len x ^ 2)
    constructor <;> linarith [this.1, this.2]
  · intro x hx
    have : len x ^ 2 ≤ 1 := by nlinarith [hnn x]
    show 1 - Λ (len x ^ 2) = 1
    rw [hzero _ this]; ring
theorem norm_le_vecLength {a : ℕ} (x : Fin a → ℝ) : ‖x‖ ≤ vecLength x := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  refine Real.abs_le_sqrt ?_
  have := Finset.single_le_sum (f := fun i => x i * x i) (fun i _ => mul_self_nonneg (x i))
    (Finset.mem_univ i)
  simpa [dotProduct, sq] using this
theorem norm_le_tupleNorm {n : ℕ} (x : PointTuple n) : ‖x‖ ≤ tupleNorm x := by apply _root_.YangMills.SharedProofs.p25561 <;> assumption
theorem tupleNorm_sq {n : ℕ} (x : PointTuple n) :
    tupleNorm x ^ 2 = ∑ i, ∑ μ, x i μ ^ 2 := by
  rw [tupleNorm, Real.sq_sqrt
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
theorem lineCutoff_spec {Λ : ℝ → ℝ} (hΛ : IsSmoothStepFunction Λ) :
    lineCutoff Λ ∈ smoothCompactSupp (Set.univ : Set ℝ) ∧
      (∀ t, 0 ≤ lineCutoff Λ t ∧ lineCutoff Λ t ≤ 1) ∧
      (∀ t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2), lineCutoff Λ t = 1) ∧
      ∀ t, t ∉ Set.Icc (-1 : ℝ) 1 → lineCutoff Λ t = 0 := by
  have hsq : ∀ t : ℝ, (2 * |t|) ^ 2 = 4 * t ^ 2 := fun t => by rw [mul_pow, sq_abs]; norm_num
  have hcut := isBallCutoff_of_contDiff_sq hΛ (fun t : ℝ => 2 * |t|)
    (fun t => by positivity) (fun t => by rw [Real.norm_eq_abs]; linarith [abs_nonneg t])
    (by simp only [hsq]; fun_prop)
  have heq : (fun t : ℝ => 1 - Λ ((2 * |t|) ^ 2)) = lineCutoff Λ := by
    funext t; rw [hsq]; rfl
  rw [heq] at hcut
  obtain ⟨h1, h2, h3, h4⟩ := hcut
  refine ⟨h1, h2, fun t ht => h3 t ?_, fun t ht => h4 t ?_⟩
  · have : |t| ≤ 1 / 2 := abs_le.2 ht
    linarith
  · have : 1 < |t| := by
      by_contra hcon
      exact ht (abs_le.1 (not_lt.1 hcon))
    linarith
theorem cutoffsOfSmoothStep_holds : CutoffsOfSmoothStep := by
  refine ⟨exists_smoothStep, fun Λ hΛ => ⟨fun a _ => ?_, fun n _ => ?_,
    lineCutoff_spec hΛ⟩⟩
  · refine isBallCutoff_of_contDiff_sq hΛ vecLength (fun x => Real.sqrt_nonneg _)
      norm_le_vecLength ?_
    simp only [vecLength_sq]
    fun_prop
  · refine isBallCutoff_of_contDiff_sq hΛ tupleNorm (fun x => Real.sqrt_nonneg _)
      norm_le_tupleNorm ?_
    simp only [tupleNorm_sq]
    fun_prop
def boxApprox (Λ : ℝ → ℝ) (a b : Fin 4 → ℝ) (j : ℕ) (x : Fin 4 → ℝ) : ℝ :=
  ∏ μ, Λ (1 + j * (x μ - a μ)) * Λ (1 + j * (b μ - x μ))
theorem boxApprox_eq_zero_of_not_mem {Λ : ℝ → ℝ} (hΛ : IsSmoothStepFunction Λ)
    (a b : Fin 4 → ℝ) (j : ℕ) {x : Fin 4 → ℝ} (hx : x ∉ openBox4 a b) :
    boxApprox Λ a b j x = 0 := by
  obtain ⟨-, -, hzero, -⟩ := hΛ
  simp only [openBox4, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, not_forall] at hx
  obtain ⟨μ, hμ⟩ := hx
  refine Finset.prod_eq_zero (Finset.mem_univ μ) ?_
  by_cases ha : a μ < x μ
  · have hb : b μ ≤ x μ := by
      by_contra hcon
      exact hμ ⟨ha, not_le.1 hcon⟩
    rw [hzero (1 + j * (b μ - x μ)) (by nlinarith), mul_zero]
  · rw [hzero (1 + j * (x μ - a μ)) (by nlinarith [not_lt.1 ha]), zero_mul]
theorem boxIndicator_isPointwiseLimit : BoxIndicatorIsPointwiseLimit := by
  intro a b _
  obtain ⟨Λ, hΛ⟩ := exists_smoothStep
  refine ⟨boxApprox Λ a b, fun j _ => ⟨⟨?_, ?_, Set.subset_univ _⟩, fun x => ?_⟩, fun x => ?_⟩
  · have hs : ContDiff ℝ ∞ Λ := hΛ.1
    refine contDiff_prod fun μ _ => ?_
    refine ContDiff.mul (hs.comp ?_) (hs.comp ?_) <;> fun_prop
  · refine HasCompactSupport.intro (isCompact_Icc (a := a) (b := b)) fun x hx => ?_
    refine boxApprox_eq_zero_of_not_mem hΛ a b j fun hbox => hx ?_
    have hbox' : ∀ μ, a μ < x μ ∧ x μ < b μ := fun μ => hbox μ (Set.mem_univ μ)
    exact ⟨fun μ => (hbox' μ).1.le, fun μ => (hbox' μ).2.le⟩
  · have hb := hΛ.2.1
    exact ⟨Finset.prod_nonneg fun μ _ => mul_nonneg (hb _).1 (hb _).1,
      Finset.prod_le_one (fun μ _ => mul_nonneg (hb _).1 (hb _).1) fun μ _ =>
        mul_le_one₀ (hb _).2 (hb _).1 (hb _).2⟩
  · by_cases hx : x ∈ openBox4 a b
    · rw [Set.indicator_of_mem hx]
      have hx' : ∀ μ, a μ < x μ ∧ x μ < b μ := fun μ => hx μ (Set.mem_univ μ)
      have hone := hΛ.2.2.2
      have hfac : ∀ μ, ∀ᶠ j : ℕ in atTop,
          Λ (1 + j * (x μ - a μ)) * Λ (1 + j * (b μ - x μ)) = 1 := by
        intro μ
        obtain ⟨N₁, hN₁⟩ := exists_nat_ge (x μ - a μ)⁻¹
        obtain ⟨N₂, hN₂⟩ := exists_nat_ge (b μ - x μ)⁻¹
        filter_upwards [eventually_ge_atTop (max N₁ N₂)] with j hj
        have hpa : 0 < x μ - a μ := sub_pos.2 (hx' μ).1
        have hpb : 0 < b μ - x μ := sub_pos.2 (hx' μ).2
        have hj₁ : (x μ - a μ)⁻¹ ≤ j :=
          hN₁.trans (Nat.cast_le.2 ((le_max_left _ _).trans hj))
        have hj₂ : (b μ - x μ)⁻¹ ≤ j :=
          hN₂.trans (Nat.cast_le.2 ((le_max_right _ _).trans hj))
        have h₁ : 1 ≤ j * (x μ - a μ) := by
          have := mul_le_mul_of_nonneg_right hj₁ hpa.le
          rwa [inv_mul_cancel₀ hpa.ne'] at this
        have h₂ : 1 ≤ j * (b μ - x μ) := by
          have := mul_le_mul_of_nonneg_right hj₂ hpb.le
          rwa [inv_mul_cancel₀ hpb.ne'] at this
        rw [hone _ (by linarith), hone _ (by linarith), one_mul]
      have hall : ∀ᶠ j : ℕ in atTop, boxApprox Λ a b j x = 1 := by
        filter_upwards [eventually_all.2 hfac] with j hj
        simp only [boxApprox, hj, Finset.prod_const_one]
      exact tendsto_const_nhds.congr' (hall.mono fun j hj => hj.symm)
    · rw [Set.indicator_of_notMem hx]
      exact tendsto_const_nhds.congr fun j => (boxApprox_eq_zero_of_not_mem hΛ a b j hx).symm
theorem exists_smoothPartitionOfUnity : ExistsSmoothPartitionOfUnity := by
  intro n r _ _ C U hC hU hCU
  have hW : IsOpen (⋃ α, U α) := isOpen_iUnion hU
  obtain ⟨K, hK, hCK, hKU⟩ := exists_compact_between hC hW hCU
  obtain ⟨L, hL, hKL, -⟩ := exists_compact_between hK isOpen_univ (Set.subset_univ K)
  have hdisj : Disjoint (interior L)ᶜ K :=
    Set.disjoint_left.2 fun x hx hxK => hx (hKL hxK)
  obtain ⟨g, hg0, hg1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ, PointTuple n)
    isOpen_interior.isClosed_compl hK.isClosed hdisj
  obtain ⟨f, hf⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, PointTuple n) hK.isClosed U hU hKU
  have hgc : HasCompactSupport (g : PointTuple n → ℝ) :=
    HasCompactSupport.intro hL fun x hx => hg0 fun hxi => hx (interior_subset hxi)
  refine ⟨fun α x => g x * f α x, fun α => ⟨?_, ?_, ?_⟩, interior K, isOpen_interior, hCK, ?_⟩
  · exact g.contMDiff.contDiff.mul (f α).contMDiff.contDiff
  · exact hgc.mul_right
  · exact (tsupport_mul_subset_right).trans (hf α)
  · intro x hx
    have hxK : x ∈ K := interior_subset hx
    have hsum : ∑ α, f α x = 1 := by
      rw [← finsum_eq_sum_of_fintype]
      exact f.sum_eq_one hxK
    rw [← Finset.mul_sum, hsum, mul_one]
    exact hg1 hxK
theorem continuousOrthogonalToTest_vanishes : ContinuousOrthogonalToTestVanishes := by
  intro n _ U u hU hu horth x hx
  have hae : ∀ᵐ y ∂(volume : Measure (PointTuple n)), y ∈ U → u y = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hu.locallyIntegrableOn hU.measurableSet) fun g hg hgc hgU => ?_
    have := horth g ⟨hg, hgc, hgU⟩
    simpa only [Complex.real_smul] using this
  have hzero : u =ᵐ[volume.restrict U] fun _ => (0 : ℂ) :=
    (ae_restrict_iff' hU.measurableSet).2 hae
  exact Measure.eqOn_open_of_ae_eq hzero hU hu continuousOn_const hx
theorem dotProduct_self_of_isUnitVec {a : ℕ} {e : Fin a → ℝ} (h : IsUnitVec e) : e ⬝ᵥ e = 1 :=
  Real.sqrt_eq_one.1 h
theorem isUnitVec_of_dotProduct_self {a : ℕ} {e : Fin a → ℝ} (h : e ⬝ᵥ e = 1) : IsUnitVec e := by
  simp [IsUnitVec, vecLength, h]
theorem planeRotation_apply {a : ℕ} (e w : Fin a → ℝ) (θ : ℝ) (x : Fin a → ℝ) :
    planeRotation e w θ x = x + (Real.cos θ - 1) • ((e ⬝ᵥ x) • e + (w ⬝ᵥ x) • w) +
      Real.sin θ • ((e ⬝ᵥ x) • w - (w ⬝ᵥ x) • e) := rfl
theorem planeRotation_dotProduct {a : ℕ} {e w : Fin a → ℝ} (θ : ℝ) (he : e ⬝ᵥ e = 1)
    (hw : w ⬝ᵥ w = 1) (hew : e ⬝ᵥ w = 0) (x y : Fin a → ℝ) :
    planeRotation e w θ x ⬝ᵥ planeRotation e w θ y = x ⬝ᵥ y := by
  have hwe : w ⬝ᵥ e = 0 := by rw [dotProduct_comm]; exact hew
  have hxe : x ⬝ᵥ e = e ⬝ᵥ x := dotProduct_comm _ _
  have hxw : x ⬝ᵥ w = w ⬝ᵥ x := dotProduct_comm _ _
  simp only [planeRotation_apply, add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, he, hw, hew, hwe, hxe, hxw]
  have hs := Real.sin_sq_add_cos_sq θ
  linear_combination ((e ⬝ᵥ x) * (e ⬝ᵥ y) + (w ⬝ᵥ x) * (w ⬝ᵥ y)) * hs
theorem toMatrix'_apply_eq {a : ℕ} (f : (Fin a → ℝ) →ₗ[ℝ] (Fin a → ℝ)) (k i : Fin a) :
    LinearMap.toMatrix' f k i = f (Pi.single i 1) k := by
  rw [LinearMap.toMatrix'_apply]
theorem toMatrix'_planeRotation_mem_orthogonalGroup {a : ℕ} {e w : Fin a → ℝ} (θ : ℝ)
    (he : e ⬝ᵥ e = 1) (hw : w ⬝ᵥ w = 1) (hew : e ⬝ᵥ w = 0) :
    LinearMap.toMatrix' (planeRotation e w θ) ∈ Matrix.orthogonalGroup (Fin a) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  ext i j
  have key := planeRotation_dotProduct θ he hw hew (Pi.single i 1) (Pi.single j 1)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, toMatrix'_apply_eq]
  rw [dotProduct] at key
  rw [key]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]
theorem continuous_toMatrix'_planeRotation {a : ℕ} (e w : Fin a → ℝ) :
    Continuous fun θ : ℝ => LinearMap.toMatrix' (planeRotation e w θ) := by
  refine continuous_matrix fun k i => ?_
  simp only [toMatrix'_apply_eq, planeRotation_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul]
  fun_prop
theorem planeRotation_zero {a : ℕ} (e w : Fin a → ℝ) :
    planeRotation e w 0 = LinearMap.id := by
  ext x
  simp [planeRotation_apply]
theorem det_toMatrix'_planeRotation {a : ℕ} {e w : Fin a → ℝ} (θ : ℝ)
    (he : e ⬝ᵥ e = 1) (hw : w ⬝ᵥ w = 1) (hew : e ⬝ᵥ w = 0) :
    (LinearMap.toMatrix' (planeRotation e w θ)).det = 1 := by
  set f : ℝ → ℝ := fun t => (LinearMap.toMatrix' (planeRotation e w t)).det with hf
  have hcont : Continuous f := (continuous_toMatrix'_planeRotation e w).matrix_det
  have hsq : ∀ t, f t = 1 ∨ f t = -1 := fun t => by
    have h := toMatrix'_planeRotation_mem_orthogonalGroup t he hw hew
    rw [Matrix.mem_orthogonalGroup_iff'] at h
    have h2 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one, Matrix.det_transpose] at h2
    exact mul_self_eq_one_iff.1 h2
  have h0 : f 0 = 1 := by
    simp [hf, planeRotation_zero]
  rcases hsq θ with h | h
  · exact h
  · exfalso
    have hivt := intermediate_value_uIcc (a := 0) (b := θ) (f := f) hcont.continuousOn
    have hmem : (0 : ℝ) ∈ Set.uIcc (f 0) (f θ) := by
      rw [h0, h, Set.uIcc_of_ge (by norm_num)]
      norm_num
    obtain ⟨t, -, ht⟩ := hivt hmem
    rcases hsq t with h1 | h1 <;> rw [ht] at h1 <;> norm_num at h1
theorem planeRotation_apply_first {a : ℕ} {e w : Fin a → ℝ} (θ : ℝ)
    (he : e ⬝ᵥ e = 1) (hew : e ⬝ᵥ w = 0) :
    planeRotation e w θ e = Real.cos θ • e + Real.sin θ • w := by
  have hwe : w ⬝ᵥ e = 0 := by rw [dotProduct_comm]; exact hew
  rw [planeRotation_apply, he, hwe]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring
theorem exists_unit_orthogonal_of_ne_zero {a : ℕ} (ha : 2 ≤ a) {e : Fin a → ℝ} (he : e ≠ 0) :
    ∃ w : Fin a → ℝ, w ⬝ᵥ w = 1 ∧ e ⬝ᵥ w = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra h
    push Not at h
    exact he (funext h)
  obtain ⟨j, hj⟩ : ∃ j : Fin a, j ≠ i := by
    by_cases h0 : i = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [h0]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, fun h => h0 h.symm⟩
  set u : Fin a → ℝ := e j • Pi.single i 1 - e i • Pi.single j 1 with hu
  have huj : u j = - e i := by simp [hu, hj]
  have hdot : e ⬝ᵥ u = 0 := by
    simp only [hu, dotProduct_sub, dotProduct_smul, dotProduct_single, smul_eq_mul]
    ring
  have hpos : 0 < u ⬝ᵥ u := by
    have hne : u ≠ 0 := fun h => hi (by simpa [h] using huj.symm)
    have h1 : u ⬝ᵥ u ≠ 0 := fun h => hne (dotProduct_self_eq_zero.1 h)
    have h2 : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    exact lt_of_le_of_ne h2 h1.symm
  refine ⟨(Real.sqrt (u ⬝ᵥ u))⁻¹ • u, ?_, ?_⟩
  · rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_inv,
      Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  · rw [dotProduct_smul, hdot, smul_zero]
theorem toMatrix'_planeRotation_mem_specialOrthogonalGroup {a : ℕ} {e w : Fin a → ℝ} (θ : ℝ)
    (he : e ⬝ᵥ e = 1) (hw : w ⬝ᵥ w = 1) (hew : e ⬝ᵥ w = 0) :
    LinearMap.toMatrix' (planeRotation e w θ) ∈ Matrix.specialOrthogonalGroup (Fin a) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨toMatrix'_planeRotation_mem_orthogonalGroup θ he hw hew,
    det_toMatrix'_planeRotation θ he hw hew⟩
theorem exists_specialOrthogonal_mulVec_eq {a : ℕ} (ha : 2 ≤ a) {e e' : Fin a → ℝ}
    (he : e ⬝ᵥ e = 1) (he' : e' ⬝ᵥ e' = 1) :
    ∃ R ∈ Matrix.specialOrthogonalGroup (Fin a) ℝ, R.mulVec e = e' := by
  set c := e ⬝ᵥ e' with hc
  set v := e' - c • e with hv
  have hev : e ⬝ᵥ v = 0 := by
    simp only [hv, dotProduct_sub, dotProduct_smul, he, smul_eq_mul, ← hc]
    ring
  have hvv : v ⬝ᵥ v = 1 - c ^ 2 := by
    have h1 : e' ⬝ᵥ e = c := dotProduct_comm _ _
    simp only [hv, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, he, he',
      smul_eq_mul, ← hc, h1]
    ring
  have hnn : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun k _ => mul_self_nonneg _
  have hc2 : c ^ 2 ≤ 1 := by rw [hvv] at hnn; linarith
  have hcl : -1 ≤ c := by nlinarith
  have hcu : c ≤ 1 := by nlinarith
  have hne : e ≠ 0 := by
    rintro rfl
    simp at he
  obtain ⟨w, hw, hew, hdecomp⟩ : ∃ w : Fin a → ℝ, w ⬝ᵥ w = 1 ∧ e ⬝ᵥ w = 0 ∧
      e' = c • e + Real.sqrt (1 - c ^ 2) • w := by
    by_cases hv0 : v = 0
    · obtain ⟨w, hw, hew⟩ := exists_unit_orthogonal_of_ne_zero ha hne
      have hz : Real.sqrt (1 - c ^ 2) = 0 := by
        rw [← hvv, hv0]
        simp
      refine ⟨w, hw, hew, ?_⟩
      rw [hz, zero_smul, add_zero]
      exact sub_eq_zero.1 hv0
    · have hpos : 0 < v ⬝ᵥ v := lt_of_le_of_ne hnn fun h => hv0 (dotProduct_self_eq_zero.1 h.symm)
      have hr : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.2 hpos
      refine ⟨(Real.sqrt (v ⬝ᵥ v))⁻¹ • v, ?_, ?_, ?_⟩
      · rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_inv,
          Real.mul_self_sqrt hnn, inv_mul_cancel₀ hpos.ne']
      · rw [dotProduct_smul, hev, smul_zero]
      · rw [← hvv, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, hv]
        abel
  refine ⟨LinearMap.toMatrix' (planeRotation e w (Real.arccos c)),
    toMatrix'_planeRotation_mem_specialOrthogonalGroup _ he hw hew, ?_⟩
  rw [LinearMap.toMatrix'_mulVec, planeRotation_apply_first _ he hew, Real.cos_arccos hcl hcu,
    Real.sin_arccos, ← hdecomp]
theorem planeRotationsAndTransitivity_holds : PlaneRotationsAndTransitivity := by
  intro a ha
  have h2 : 2 ≤ a := by omega
  refine ⟨fun e w θ he hw hew => ?_, fun e e' he he' => ?_⟩
  · exact ⟨toMatrix'_planeRotation_mem_specialOrthogonalGroup θ (dotProduct_self_of_isUnitVec he)
      (dotProduct_self_of_isUnitVec hw) hew,
      planeRotation_apply_first θ (dotProduct_self_of_isUnitVec he) hew⟩
  · exact exists_specialOrthogonal_mulVec_eq h2 (dotProduct_self_of_isUnitVec he)
      (dotProduct_self_of_isUnitVec he')
def momentPolynomial (y : Fin 4 → ℝ) : Polynomial ℝ :=
  ∑ i : Fin 4, Polynomial.C (y i) * Polynomial.X ^ (i : ℕ)
theorem momentPolynomial_ne_zero {y : Fin 4 → ℝ} (hy : y ≠ 0) : momentPolynomial y ≠ 0 := by
  intro h
  apply hy
  funext i
  have := congrArg (fun p => Polynomial.coeff p (i : ℕ)) h
  simp only [momentPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_zero] at this
  simpa [Fin.val_inj, Finset.sum_ite_eq] using this
theorem eval_momentPolynomial (y : Fin 4 → ℝ) (t : ℝ) :
    (momentPolynomial y).eval t = (fun i : Fin 4 => t ^ (i : ℕ)) ⬝ᵥ y := by
  simp only [momentPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
theorem exists_unitVec_not_orthogonal : ExistsUnitVecNotOrthogonal := by
  intro r y hy
  have hP : ∏ l, momentPolynomial (y l) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => momentPolynomial_ne_zero (hy l)
  obtain ⟨t, ht⟩ : ∃ t, (∏ l, momentPolynomial (y l)).eval t ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (Polynomial.funext fun t => by simpa using h t)
  rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff] at ht
  set u : Fin 4 → ℝ := fun i => t ^ (i : ℕ) with hu
  have hpos : 0 < u ⬝ᵥ u := by
    have hne : u ≠ 0 := fun h => by simpa [hu] using congrFun h 0
    have h1 : u ⬝ᵥ u ≠ 0 := fun h => hne (dotProduct_self_eq_zero.1 h)
    have h2 : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    exact lt_of_le_of_ne h2 h1.symm
  have hr : 0 < Real.sqrt (u ⬝ᵥ u) := Real.sqrt_pos.2 hpos
  refine ⟨(Real.sqrt (u ⬝ᵥ u))⁻¹ • u, isUnitVec_of_dotProduct_self ?_, fun l => ?_⟩
  · rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_inv,
      Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  · rw [smul_dotProduct, smul_eq_mul]
    refine mul_ne_zero (inv_ne_zero hr.ne') ?_
    rw [← eval_momentPolynomial (y l) t]
    exact ht l (Finset.mem_univ l)
theorem toolkit_of_bumpFacts (hBumps : Mollifiers.BumpProperties.bumpFacts)
    (hFirst : TestSpaces.Elementary.BasicProperties) : Toolkit :=
  ⟨exists_mollifier_of_bumpFacts hBumps, cutoffsOfSmoothStep_holds, boxIndicator_isPointwiseLimit,
    exists_smoothPartitionOfUnity, continuousOrthogonalToTest_vanishes,
    planeRotationsAndTransitivity_holds, exists_unitVec_not_orthogonal,
    schwartzIntegrable_of_basicProperties hFirst⟩
end YangMills.Construction.WightmanReconstruction.SmoothToolkit
end

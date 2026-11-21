import YangMills.Construction.ParameterData.FirstPassagesAreData
import YangMills.Construction.ParameterData.TheNumberOfTheFlowIsNearOne
import YangMills.Construction.SystemOfAdmissibleConstants.EnvelopesOfTheLevel
import YangMills.Construction.SystemOfAdmissibleConstants.TheThresholdsAlongTheTrajectory
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.SystemOfAdmissibleConstants
open RenormalizationStepParameters TrajectoryData WeightedResponses ResponseInTheExpansion AdmissibleConstants StateLaws
variable {T : ParameterAssignment} {y : ℝ}
private theorem logSlope_pos : 0 < logSlope := by
  unfold logSlope
  positivity
private theorem tendsto_log_inv_nhdsGT : Tendsto (fun d : ℝ => Real.log (1 / d)) (𝓝[>] 0) atTop := by
  have h := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  refine h.congr (fun d => ?_)
  simp [one_div]
abbrev _root_.YangMills.SharedProofs.p8376 := @tendsto_log_inv_nhdsGT
private theorem lowerCouplingEnvelope_tendsto (D : TrajectoryParameters T y) (g : ℝ) :
    Tendsto (lowerCouplingEnvelope D g) (𝓝[>] 0) atTop := by
  have h : Tendsto (fun d : ℝ => 3 / 4 * logSlope * Real.log (1 / d)) (𝓝[>] 0) atTop :=
    tendsto_log_inv_nhdsGT.const_mul_atTop (by have := logSlope_pos; positivity)
  have h2 := tendsto_atTop_add_const_left (𝓝[>] (0 : ℝ)) ((g ^ 2)⁻¹ - 2 * D.cH) h
  exact h2
private theorem upperCouplingEnvelope_eq (D : TrajectoryParameters T y) (g d : ℝ) :
    upperCouplingEnvelope D g d = 2 * (D.threshold g + 2 * D.cH + 1 +
        5 / 4 * logSlope * Real.log (2 ^ 13 * (T.side : ℝ))) +
      5 / 2 * logSlope * Real.log (1 / d) := by
  unfold upperCouplingEnvelope
  ring
private theorem upperCouplingEnvelope_tendsto (D : TrajectoryParameters T y) (g : ℝ) :
    Tendsto (upperCouplingEnvelope D g) (𝓝[>] 0) atTop := by
  have h : Tendsto (fun d : ℝ => 5 / 2 * logSlope * Real.log (1 / d)) (𝓝[>] 0) atTop :=
    tendsto_log_inv_nhdsGT.const_mul_atTop (by have := logSlope_pos; positivity)
  have h2 := tendsto_atTop_add_const_left (𝓝[>] (0 : ℝ)) (2 * (D.threshold g + 2 * D.cH + 1 +
        5 / 4 * logSlope * Real.log (2 ^ 13 * (T.side : ℝ)))) h
  exact h2.congr (fun d => (upperCouplingEnvelope_eq D g d).symm)
private theorem upperCouplingEnvelope_mul_tendsto (D : TrajectoryParameters T y) (g : ℝ) :
    Tendsto (fun d : ℝ => upperCouplingEnvelope D g d * d) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun d : ℝ => d * Real.log d) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuous_mul_log.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using h
  have h2 : Tendsto (fun d : ℝ => d) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h3 := (h2.const_mul (2 * (D.threshold g + 2 * D.cH + 1 +
        5 / 4 * logSlope * Real.log (2 ^ 13 * (T.side : ℝ))))).sub
    (h1.const_mul (5 / 2 * logSlope))
  have h4 : Tendsto (fun d : ℝ => upperCouplingEnvelope D g d * d) (𝓝[>] 0) (𝓝 (0 - 0)) := by
    simp only [mul_zero] at h3
    refine h3.congr (fun d => ?_)
    rw [upperCouplingEnvelope_eq, one_div, Real.log_inv]
    ring
  simpa using h4
private theorem rpow_inv27_le_one_add (x : ℝ) (hx : 0 ≤ x) : x ^ ((1 : ℝ) / 27) ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · have := Real.rpow_le_one hx h (by norm_num : (0 : ℝ) ≤ 1 / 27)
    linarith
  · have h2 := Real.rpow_le_rpow_of_exponent_le h (by norm_num : (1 : ℝ) / 27 ≤ 1)
    rw [Real.rpow_one] at h2
    linarith
private theorem product_mem_Icc_and_abs_sub_one_le (a u e ε η : ℝ) (h1 : |a - 1| ≤ η) (h2 : |u - 1| ≤ η)
    (hε : |ε| ≤ e) (he : e ≤ 1 / 2) (hη : η ≤ 1 / 3) :
    a ^ 2 * u ^ 2 * (1 + ε) ∈ Set.Icc (1 / 2 * (1 - η) ^ 4) (3 / 2 * (1 + η) ^ 4) ∧
      |a ^ 2 * u ^ 2 * (1 + ε) - 1| ≤ (1 + e) * (1 + η) ^ 4 - 1 := by
  have hη0 : 0 ≤ η := (abs_nonneg _).trans h1
  have he0 : 0 ≤ e := (abs_nonneg _).trans hε
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  obtain ⟨c1, c2⟩ := abs_le.1 hε
  have hm : 0 < 1 - η := by linarith
  have hau : (1 - η) ^ 2 ≤ a * u := by nlinarith
  have hau' : a * u ≤ (1 + η) ^ 2 := by nlinarith
  have hP : (1 - η) ^ 4 ≤ a ^ 2 * u ^ 2 := by
    have h0 : 0 ≤ (1 - η) ^ 2 := by positivity
    have : ((1 - η) ^ 2) ^ 2 ≤ (a * u) ^ 2 := pow_le_pow_left₀ h0 hau 2
    nlinarith
  have hP' : a ^ 2 * u ^ 2 ≤ (1 + η) ^ 4 := by
    have h0 : 0 ≤ a * u := (by positivity : 0 ≤ (1 - η) ^ 2).trans hau
    have : (a * u) ^ 2 ≤ ((1 + η) ^ 2) ^ 2 := pow_le_pow_left₀ h0 hau' 2
    nlinarith
  have hlo0 : 0 ≤ (1 - η) ^ 4 := by positivity
  have hP0 : 0 ≤ a ^ 2 * u ^ 2 := hlo0.trans hP
  have hup : a ^ 2 * u ^ 2 * (1 + ε) ≤ (1 + e) * (1 + η) ^ 4 := by
    have s1 : a ^ 2 * u ^ 2 * (1 + ε) ≤ a ^ 2 * u ^ 2 * (1 + e) :=
      mul_le_mul_of_nonneg_left (by linarith) hP0
    have s2 : a ^ 2 * u ^ 2 * (1 + e) ≤ (1 + η) ^ 4 * (1 + e) :=
      mul_le_mul_of_nonneg_right hP' (by linarith)
    linarith
  have hdn : (1 - e) * (1 - η) ^ 4 ≤ a ^ 2 * u ^ 2 * (1 + ε) := by
    have s1 : a ^ 2 * u ^ 2 * (1 - e) ≤ a ^ 2 * u ^ 2 * (1 + ε) :=
      mul_le_mul_of_nonneg_left (by linarith) hP0
    have s2 : (1 - η) ^ 4 * (1 - e) ≤ a ^ 2 * u ^ 2 * (1 - e) :=
      mul_le_mul_of_nonneg_right hP (by linarith)
    linarith
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · nlinarith
  · nlinarith
  · have hsum : 2 ≤ (1 + η) ^ 4 + (1 - η) ^ 4 := by nlinarith [sq_nonneg η, sq_nonneg (η ^ 2)]
    have hmul : 0 ≤ e * ((1 + η) ^ 4 - (1 - η) ^ 4) := mul_nonneg he0 (by linarith)
    refine abs_le.2 ⟨?_, by linarith⟩
    nlinarith
private theorem twoPoint_eq_leadingTerm_mul (d x a Kf ε : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (hx : x ≠ 0)
    (f h : (Fin 4 → ℝ) → ℝ) (hK : TestFunctions.inverseEighthKernel f h = Kf) :
    a ^ 2 * (9 / Real.pi ^ 4) * (x ^ 2)⁻¹ * Kf * (1 + ε) =
      leadingTwoPointTerm d f h * (a ^ 2 * (logSlope * x⁻¹ * Real.log (1 / d)) ^ 2 * (1 + ε)) := by
  have hL : Real.log (1 / d) ≠ 0 := by
    have : 0 < Real.log (1 / d) := Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hd0).2 hd1)
    exact this.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold leadingTwoPointTerm logSlope
  rw [hK]
  field_simp
  ring
private theorem ratio_bddAbove (D : TrajectoryParameters T y) (g : ℝ)
    (hb : BddAbove ((fun d => heightBound D g d / lowerCouplingEnvelope D g d) '' Set.Ioo 0 1)) {d : ℝ}
    (hd : d < 1) :
    BddAbove (Set.range fun e : Set.Ioc (0 : ℝ) d => heightBound D g e / lowerCouplingEnvelope D g e) := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨M, ?_⟩
  rintro _ ⟨⟨e, he⟩, rfl⟩
  exact hM ⟨e, ⟨he.1, lt_of_le_of_lt he.2 hd⟩, rfl⟩
private theorem ratio_le_ratioModulus (D : TrajectoryParameters T y) (g : ℝ)
    (hb : BddAbove ((fun d => heightBound D g d / lowerCouplingEnvelope D g d) '' Set.Ioo 0 1)) {d : ℝ}
    (h0 : 0 < d) (h1 : d < 1) : heightBound D g d / lowerCouplingEnvelope D g d ≤ ratioModulus D g d :=
  le_ciSup (f := fun e : Set.Ioc (0 : ℝ) d => heightBound D g e / lowerCouplingEnvelope D g e)
    (ratio_bddAbove D g hb h1) ⟨d, h0, le_rfl⟩
private theorem ratioModulus_mono (D : TrajectoryParameters T y) (g : ℝ)
    (hb : BddAbove ((fun d => heightBound D g d / lowerCouplingEnvelope D g d) '' Set.Ioo 0 1)) {d d' : ℝ}
    (h0 : 0 < d) (h : d ≤ d') (h1 : d' < 1) : ratioModulus D g d ≤ ratioModulus D g d' := by
  have : Nonempty (Set.Ioc (0 : ℝ) d) := ⟨⟨d, h0, le_rfl⟩⟩
  refine ciSup_le fun e => ?_
  exact le_ciSup (f := fun e : Set.Ioc (0 : ℝ) d' => heightBound D g e / lowerCouplingEnvelope D g e)
    (ratio_bddAbove D g hb h1) ⟨e.1, e.2.1, e.2.2.trans h⟩
private theorem ratioModulus_tendsto (D : TrajectoryParameters T y) (g : ℝ)
    (hb : BddAbove ((fun d => heightBound D g d / lowerCouplingEnvelope D g d) '' Set.Ioo 0 1))
    (ht : Tendsto (fun d => heightBound D g d / lowerCouplingEnvelope D g d) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (ratioModulus D g) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev := (Metric.tendsto_nhds.1 ht) (ε / 2) (half_pos hε)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev
  have hm : 0 < min u (1 / 2) := lt_min hu (by norm_num)
  filter_upwards [Ioc_mem_nhdsGT hm] with d hd
  have hd1 : d < 1 := lt_of_le_of_lt (hd.2.trans (min_le_right _ _)) (by norm_num)
  have hval : ∀ e ∈ Set.Ioc (0 : ℝ) d,
      |heightBound D g e / lowerCouplingEnvelope D g e| < ε / 2 := fun e he => by
    have h : dist (heightBound D g e / lowerCouplingEnvelope D g e) 0 < ε / 2 :=
      hsub ⟨he.1, he.2.trans (hd.2.trans (min_le_left _ _))⟩
    rwa [Real.dist_eq, sub_zero] at h
  have : Nonempty (Set.Ioc (0 : ℝ) d) := ⟨⟨d, hd.1, le_rfl⟩⟩
  have hlow := ratio_le_ratioModulus D g hb hd.1 hd1
  have hup : ratioModulus D g d ≤ ε / 2 := ciSup_le fun e => (abs_lt.1 (hval e.1 e.2)).2.le
  have hl := (abs_lt.1 (hval d ⟨hd.1, le_rfl⟩)).1
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith
private theorem rateBound_pos (D : TrajectoryParameters T y) (hD : D.Admissible) : 0 < D.rateBound :=
  hD.lam_pos.trans_le hD.lam_le
private theorem normalizationModulus_nonneg (D : TrajectoryParameters T y) (hD : D.Admissible) {C : ℝ} (hC : 0 ≤ C)
    (g d : ℝ) (hx : 0 ≤ lowerCouplingEnvelope D g d) : 0 ≤ normalizationModulus D C g d := by
  have := rateBound_pos D hD
  unfold normalizationModulus
  exact mul_nonneg (by positivity) (Real.rpow_nonneg hx _)
private theorem inv_sqrt_term_anti (D : TrajectoryParameters T y) (hD : D.Admissible) {C : ℝ} (hC : 0 ≤ C) {x x' : ℝ}
    (hx : 0 < x) (h : x ≤ x') :
    6 * C / D.rateBound * x' ^ (-(1 / 2) : ℝ) ≤ 6 * C / D.rateBound * x ^ (-(1 / 2) : ℝ) := by
  have := rateBound_pos D hD
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx h (by norm_num)) (by positivity)
private theorem normalizationModulus_tendsto (D : TrajectoryParameters T y) (C g : ℝ) :
    Tendsto (normalizationModulus D C g) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun d => lowerCouplingEnvelope D g d ^ (-(1 / 2) : ℝ)) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp (lowerCouplingEnvelope_tendsto D g)
  have h2 := h.const_mul (6 * C / D.rateBound)
  rw [mul_zero] at h2
  exact h2
private theorem lawError_tendsto (D : TrajectoryParameters T y) (C g : ℝ) :
    Tendsto (lawError D C g) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun d => lowerCouplingEnvelope D g d ^ (-(1 / 200) : ℝ)) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 200)).comp (lowerCouplingEnvelope_tendsto D g)
  have h2 := h.const_mul C
  rw [mul_zero] at h2
  exact h2
private theorem combinedModulus_tendsto (D : TrajectoryParameters T y) (C g : ℝ)
    (hb : BddAbove ((fun d => heightBound D g d / lowerCouplingEnvelope D g d) '' Set.Ioo 0 1))
    (ht : Tendsto (fun d => heightBound D g d / lowerCouplingEnvelope D g d) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (combinedModulus D C g) (𝓝[>] 0) (𝓝 0) := by
  have h := (normalizationModulus_tendsto D C g).max (ratioModulus_tendsto D g hb ht)
  rw [max_self] at h
  exact h
private theorem admissibleConditions_eventually (D : TrajectoryParameters T y) (C XL CL g : ℝ)
    (hb : BddAbove ((fun d => heightBound D g d / lowerCouplingEnvelope D g d) '' Set.Ioo 0 1))
    (ht : Tendsto (fun d => heightBound D g d / lowerCouplingEnvelope D g d) (𝓝[>] 0) (𝓝 0)) :
    ∀ᶠ d in 𝓝[>] (0 : ℝ), combinedModulus D C g d ≤ 1 / 3 ∧ lawError D CL g d ≤ 1 / 2 ∧
      XL ≤ lowerCouplingEnvelope D g d ∧ (upperCouplingEnvelope D g d ^ ((1 : ℝ) / 27) + 10) * d < 1 / 2 := by
  have e1 := (combinedModulus_tendsto D C g hb ht).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 3)
  have e2 := (lawError_tendsto D CL g).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
  have e3 := (lowerCouplingEnvelope_tendsto D g).eventually_ge_atTop XL
  have e4 := (upperCouplingEnvelope_tendsto D g).eventually_ge_atTop 0
  have hm : Tendsto (fun d : ℝ => upperCouplingEnvelope D g d * d + 11 * d) (𝓝[>] 0) (𝓝 0) := by
    have h2 : Tendsto (fun d : ℝ => d) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h3 := (upperCouplingEnvelope_mul_tendsto D g).add (h2.const_mul 11)
    simpa using h3
  have e5 := hm.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  have e6 : ∀ᶠ d in 𝓝[>] (0 : ℝ), 0 < d := self_mem_nhdsWithin
  filter_upwards [e1, e2, e3, e4, e5, e6] with d h1 h2 h3 h4 h5 h6
  refine ⟨h1, h2, h3, ?_⟩
  have h7 := rpow_inv27_le_one_add _ h4
  nlinarith
private theorem thresholdEstimates_of_envelopes (D : TrajectoryParameters T y) (hD : D.Admissible)
    (Kr : ResponseParameters) (hC : 0 ≤ Kr.Cstar)
    (g vt XL CL : ℝ) (hCL : 0 ≤ CL)
    (hpts : ∀ d : ℝ, 0 < d → d < 1 → ∀ (K : ℕ) (β : ℝ), IsDatumAtDistance D g d K β →
      lowerCouplingEnvelope D g d ≤ D.coupling β (separationLevel (T.stepParameters y) β K d) ∧
      D.coupling β (separationLevel (T.stepParameters y) β K d) ≤ upperCouplingEnvelope D g d ∧
      (K : ℝ) - separationLevel (T.stepParameters y) β K d ≤ scaleDepthEnvelope D g d ∧
      |logSlope * Real.log (1 / d) - D.coupling β (separationLevel (T.stepParameters y) β K d)| ≤
        heightBound D g d)
    (hlow : AntitoneOn (lowerCouplingEnvelope D g) (Set.Ioo 0 1))
    (h8 : ∀ d : ℝ, 0 < d → d < 1 → 8 < lowerCouplingEnvelope D g d)
    (hb : BddAbove ((fun d => heightBound D g d / lowerCouplingEnvelope D g d) '' Set.Ioo 0 1))
    (ht : Tendsto (fun d => heightBound D g d / lowerCouplingEnvelope D g d) (𝓝[>] 0) (𝓝 0))
    (hfloor : ∀ (K : ℕ) (β : ℝ), 2 ≤ K → β ∈ D.passageWindow K g → ∀ j ≤ K, y ≤ D.coupling β j)
    (hnum : ∀ (β : ℝ) (k : ℕ), (∀ j ≤ k, y ≤ flowCouplings (T.stepParameters y) β j) →
      ∃ a : ℕ → ℝ, IsChainResponseCoeff (T.stepParameters y) Kr β k a ∧
        |a k - 1| ≤ 6 * Kr.Cstar / D.rateBound * D.coupling β k ^ (-(1 / 2) : ℝ))
    (hlaw : couplingLawAt D Kr g vt XL CL) :
    ThresholdEstimates D Kr g vt XL CL := by
  have hmod := combinedModulus_tendsto D Kr.Cstar g hb ht
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1
    (admissibleConditions_eventually D Kr.Cstar XL CL g hb ht)
  have hmin : 0 < min u (1 / 2) := lt_min hu (by norm_num)
  have hδ : min u (1 / 2) ∈ admissibleDistances D Kr.Cstar XL CL g :=
    ⟨⟨hmin, lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩,
      fun d hd => hsub ⟨hd.1, hd.2.trans (min_le_left _ _)⟩⟩
  have hB : BddAbove (admissibleDistances D Kr.Cstar XL CL g) := ⟨1, fun δ h => h.1.2.le⟩
  have hS0 : 0 < sSup (admissibleDistances D Kr.Cstar XL CL g) := hmin.trans_le (le_csSup hB hδ)
  have hS1 : sSup (admissibleDistances D Kr.Cstar XL CL g) ≤ 1 := csSup_le ⟨_, hδ⟩ fun δ h => h.1.2.le
  have hdef : distanceCutoff D Kr.Cstar XL CL g = 1 / 2 * sSup (admissibleDistances D Kr.Cstar XL CL g) := rfl
  have hpos : 0 < distanceCutoff D Kr.Cstar XL CL g := by rw [hdef]; positivity
  have hlt : distanceCutoff D Kr.Cstar XL CL g < 1 := by rw [hdef]; linarith
  have hcond : ∀ d ∈ Set.Ioc 0 (distanceCutoff D Kr.Cstar XL CL g),
      combinedModulus D Kr.Cstar g d ≤ 1 / 3 ∧ lawError D CL g d ≤ 1 / 2 ∧ XL ≤ lowerCouplingEnvelope D g d ∧
        (upperCouplingEnvelope D g d ^ ((1 : ℝ) / 27) + 10) * d < 1 / 2 := fun d hd => by
    obtain ⟨δ, hδB, hδlt⟩ := exists_lt_of_lt_csSup ⟨_, hδ⟩
      (show distanceCutoff D Kr.Cstar XL CL g < sSup (admissibleDistances D Kr.Cstar XL CL g) by
        rw [hdef]; linarith)
    exact hδB.2 d ⟨hd.1, hd.2.trans hδlt.le⟩
  have hlt' : ∀ d ∈ Set.Ioc 0 (distanceCutoff D Kr.Cstar XL CL g), d < 1 := fun d hd => hd.2.trans_lt hlt
  refine ⟨hpos, hlt, ?_, ?_, hmod, ?_⟩
  · intro d hd
    refine ⟨le_max_of_le_left (normalizationModulus_nonneg D hD hC g d ?_), (hcond d hd).1⟩
    linarith [h8 d hd.1 (hlt' d hd)]
  · intro d hd d' hd' hdd
    have h1 := hlt' d' hd'
    have hx : 0 < lowerCouplingEnvelope D g d' := by linarith [h8 d' hd'.1 h1]
    have hanti := hlow ⟨hd.1, hlt' d hd⟩ ⟨hd'.1, h1⟩ hdd
    refine max_le_max ?_ (ratioModulus_mono D g hb hd.1 hdd h1)
    exact inv_sqrt_term_anti D hD hC hx hanti
  · intro d hd K β hdat
    obtain ⟨c1, c2, c3, c4⟩ := hcond d hd
    have hd1 := hlt' d hd
    have hd0 := hd.1
    obtain ⟨p1, p2, -, p4⟩ := hpts d hd0 hd1 K β hdat
    have hK2 : 2 ≤ (K : ℕ) := le_trans (le_max_left _ _) hdat.2
    have hkK : separationLevel (T.stepParameters y) β K d ≤ K := by
      unfold separationLevel
      classical exact Nat.findGreatest_le _
    have hfl := hfloor K β hK2 hdat.1
    obtain ⟨a, ha, hnear⟩ := hnum β (separationLevel (T.stepParameters y) β K d)
      (fun j hj => hfl j (hj.trans hkK))
    set k := separationLevel (T.stepParameters y) β K d with hk
    have hlpos : 0 < lowerCouplingEnvelope D g d := by linarith [h8 d hd0 hd1]
    have hxpos : 0 < D.coupling β k := hlpos.trans_le p1
    have hnear' : |a k - 1| ≤ combinedModulus D Kr.Cstar g d :=
      hnear.trans ((inv_sqrt_term_anti D hD hC hlpos p1).trans (le_max_left _ _))
    have hslope : |logSlope * (D.coupling β k)⁻¹ * Real.log (1 / d) - 1| ≤ combinedModulus D Kr.Cstar g d := by
      have hH : 0 ≤ heightBound D g d := (abs_nonneg _).trans p4
      have e : logSlope * (D.coupling β k)⁻¹ * Real.log (1 / d) - 1 =
          (logSlope * Real.log (1 / d) - D.coupling β k) / D.coupling β k := by
        field_simp
      rw [e, abs_div, abs_of_pos hxpos]
      calc |logSlope * Real.log (1 / d) - D.coupling β k| / D.coupling β k
          ≤ heightBound D g d / D.coupling β k := by gcongr
        _ ≤ heightBound D g d / lowerCouplingEnvelope D g d := by gcongr
        _ ≤ ratioModulus D g d := ratio_le_ratioModulus D g hb hd0 hd1
        _ ≤ combinedModulus D Kr.Cstar g d := le_max_right _ _
    have hsm : (D.coupling β k ^ ((1 : ℝ) / 27) + 10) * d < 1 / 2 := by
      have hr := Real.rpow_le_rpow hxpos.le p2 (by norm_num : (0 : ℝ) ≤ 1 / 27)
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith) hd0.le) c4
    have hlawk := (hlaw d hd0 hd1 K β hdat (c3.trans p1) hsm a ha).1
    have herr : ∀ ε : ℝ, |ε| ≤ CL * D.coupling β k ^ (-(1 / 200) : ℝ) → |ε| ≤ lawError D CL g d :=
      fun ε h => h.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hlpos p1 (by norm_num)) hCL)
    refine ⟨c2, hslope, ⟨a, ha, hnear', fun ν hν p hp => ?_⟩, fun ν hν p hp => ?_⟩
    · obtain ⟨ε, hε, he⟩ := hlawk ν hν p hp
      exact ⟨ε, herr ε hε, he⟩
    · obtain ⟨ε, hε, he⟩ := hlawk ν hν p hp
      have hf := product_mem_Icc_and_abs_sub_one_le (a k) (logSlope * (D.coupling β k)⁻¹ * Real.log (1 / d))
        (lawError D CL g d) ε (combinedModulus D Kr.Cstar g d) hnear' hslope (herr ε hε) c2 c1
      refine ⟨a k ^ 2 * (logSlope * (D.coupling β k)⁻¹ * Real.log (1 / d)) ^ 2 * (1 + ε), hf.1, hf.2, ?_⟩
      rw [he]
      exact congrArg (fun r : ℝ => (r : ℂ))
        (twoPoint_eq_leadingTerm_mul d (D.coupling β k) (a k) _ ε hd0 hd1 hxpos.ne' p.1 p.2 rfl)
theorem thresholdsStatement_proof (hLaw : levelLawStatement) (hEnv : levelEnvelopesStatement)
    (hNum : responseCoeffNearOneStatement) (hPass : windowMembersAreDataStatement) : thresholdsStatement := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, h₁⟩ := hLaw a ha
  obtain ⟨L₂, r₂, C₂, hr₂, h₂⟩ := hEnv a ha
  obtain ⟨L₃, r₃, C₃, hr₃, h₃⟩ := hNum a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (r₁ c) (min (r₂ c) (r₃ c)), max C₁ (max C₂ C₃),
    fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (hr₃ c)), ?_⟩
  intro L hLo hL T hTa hTL hDr hCS hCH hrt hC
  obtain ⟨y₂, hy₂⟩ := h₂ L hLo (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL) T hTa hTL hDr hCS hCH
    (hrt.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC)
  obtain ⟨Kr, hKr, y₃, hy₃⟩ := h₃ L hLo (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL) T hTa hTL hDr
    hCS hCH (hrt.trans ((min_le_right _ _).trans (min_le_right _ _)))
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC)
  obtain ⟨y₁, hy₁⟩ := h₁ L hLo (le_trans (le_max_left _ _) hL) T hTa hTL hDr hCS hCH
    (hrt.trans (min_le_left _ _)) (le_trans (le_max_left _ _) hC) Kr
  refine ⟨max y₁ (max y₂ y₃), fun y hy hR hW => ⟨Kr, hKr y, fun D hD g hg hfl vt hv0 hv1 => ?_⟩⟩
  have hl := hy₁ y (le_trans (le_max_left _ _) hy) ⟨hR, hW⟩ (hKr y) D hD g hg hfl vt hv0 hv1
  obtain ⟨hpts, hlow, -, h8, hb, ht⟩ :=
    hy₂ y (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy) hR hW D hD g hg hfl
  have hn := hy₃ y (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy) hR hW
  obtain ⟨XL, CL, hXL, hCL, hlaw⟩ := hl
  refine ⟨XL, CL, hXL, hCL, hlaw, ?_⟩
  refine thresholdEstimates_of_envelopes D hD Kr (hKr y).Cstar_nonneg g vt XL CL hCL hpts hlow h8 hb ht ?_ ?_ hlaw
  · intro K β hK hw
    exact (hPass T y D hD g hg ((le_max_left _ _).trans hfl) K β hK hw).floor
  · intro β k hj
    obtain ⟨a, ha, hnear, -⟩ := hn β k hj
    exact ⟨a, ha, hnear⟩
end YangMills.Construction.SystemOfAdmissibleConstants
end

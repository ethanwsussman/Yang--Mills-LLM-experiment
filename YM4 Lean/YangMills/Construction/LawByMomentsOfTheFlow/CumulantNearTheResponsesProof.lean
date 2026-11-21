import YangMills.Construction.Cumulants.MultilinearityShiftsAndMomentsOfJointCumulants
import YangMills.Construction.LawByMomentsOfTheFlow.ABoundAtClearStatesInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.CumulantNearTheResponses
import YangMills.Construction.LawByMomentsOfTheFlow.LawAtLimitPointsProof
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAtTheFarLevelOfTheScale
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsNearAProductAtTheFarLevel
import YangMills.Construction.LawByMomentsOfTheFlow.ResponsesAtTheFarLevelAreSized
import YangMills.Construction.LawByMomentsOfTheFlow.SitesAtTheFarLevelOfTheScale
import YangMills.Construction.ResponseInTheExpansion.WhatTheChainReadsIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.WeightedResponses YangMills.Construction.TorusFields YangMills.Construction.TorusFrame
open YangMills.Construction.Probability (IsBoundedRealRV)
private theorem hullParams_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁)
    (h₂ : ForAllHullParameters Q₂) : ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem hullParams_base :
    ForAllHullParameters fun Λ => Λ.table.Admissible ∧ Λ.table.floorMin ≤ Λ.floor ∧ 2 ≤ Λ.k := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ tab _ _ hD _ _ _ _
  refine ⟨0, fun resp _ _ _ _ _ => ?_⟩
  exact ⟨tab.floorMin, fun y hy _ _ g _ _ k _ hk2 _ R d _ => ⟨hD, hy, hk2⟩⟩
private theorem hullParams_mono {Q₁ Q₂ : MomentParameters → Prop} (h : ForAllHullParameters Q₁)
    (hm : ∀ Λ, Q₁ Λ → Q₂ Λ) : ForAllHullParameters Q₂ := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := h a ha
  refine ⟨L₁, r₁, C₁, hr₁, ?_⟩
  intro L hodd hL tab hTa hTL hD hC hH hrt hc
  obtain ⟨M₁, G₁⟩ := H₁ L hodd hL tab hTa hTL hD hC hH hrt hc
  refine ⟨M₁, fun resp hM hη hN hresp hret => ?_⟩
  obtain ⟨y₁, Y₁⟩ := G₁ resp hM hη hN hresp hret
  exact ⟨y₁, fun y hy hR hW g hg hyg k _ hk2 hk8 R d hd => hm _ (Y₁ y hy hR hW g hg hyg k hk2 hk8 R d hd)⟩
abbrev _root_.YangMills.SharedProofs.p38382 := @hullParams_mono
private theorem hullParams_of_params {Q : MomentParameters → Prop} (h : ForAllParameters Q) :
    ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem hullParams_of_points {Q : ∀ Λ : MomentParameters, (ℕ → ℝ) → ℝ → ℝ → MomentPoint Λ → Prop}
    (h : ForAllPoints Q) :
    ForAllHullParameters fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, Q Λ C c X₀ S :=
  hullParams_of_params h
private theorem hullParams_of_hullPoints {Q : ∀ Λ : MomentParameters, (ℕ → ℝ) → ℝ → ℝ → MomentPoint Λ → Prop}
    (h : ForAllHullPoints Q) :
    ForAllHullParameters fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, Q Λ C c X₀ S :=
  h
private theorem hullPoints_of_hullParams {Q : ∀ Λ : MomentParameters, (ℕ → ℝ) → ℝ → ℝ → MomentPoint Λ → Prop}
    (h : ForAllHullParameters fun Λ =>
      ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, Q Λ C c X₀ S) :
    ForAllHullPoints Q := h
private theorem measurable_bottomField (ℓ : TorusLumps.StepParameters) :
    ∀ (s n : ℕ), Measurable (bottomField ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => by
      let _ := markedSampleMeasurableSpace ℓ s (n * ℓ.side)
      exact (measurable_bottomField ℓ s (n * ℓ.side)).comp measurable_fst
private theorem map_bottomField_eq_wilsonLaw {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) (β : ℝ)
    (hm : ∀ (s n : ℕ) [NeZero n], (markedSampleLaw T β (s + 1) n).map (fun u : MarkedSample ℓ (s + 1) n => u.1) =
      markedSampleLaw T β s (n * ℓ.side)) :
    ∀ (s n : ℕ) [NeZero n], (markedSampleLaw T β s n).map (bottomField ℓ s n) = wilsonLaw β (fineSide ℓ.side s n)
  | 0, n, _ => Measure.map_id
  | s + 1, n, _ => by
      have hfst : Measurable (fun u : MarkedSample ℓ (s + 1) n => u.1) := by
        let _ := markedSampleMeasurableSpace ℓ s (n * ℓ.side)
        exact measurable_fst
      refine (Measure.map_map (measurable_bottomField ℓ s (n * ℓ.side)) hfst).symm.trans ?_
      rw [hm s n]
      exact map_bottomField_eq_wilsonLaw T β hm s (n * ℓ.side)
private theorem connectedCurvature_congr_side {k : ℕ} (β : ℝ) {m m' : ℕ} [NeZero m] [NeZero m'] (h : m = m')
    (f : ∀ m, Fin k → PlaquetteWeight m) : connectedCurvature β m (f m) = connectedCurvature β m' (f m') := by
  subst h
  rfl
private theorem curvatureObservable_isBounded {N : ℕ} [NeZero N] (h : PlaquetteWeight N) :
    IsBoundedRealRV (curvatureObservable h) := by apply _root_.YangMills.SharedProofs.p42321 <;> assumption
private theorem integral_prod_bounds {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ}
    (F N : Fin k → Ω → ℝ) (G : Ω → ℝ) (J : Finset (Fin k)) (hFm : ∀ i, AEMeasurable (F i) μ) (hG : Integrable G μ)
    {A ε E : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε) (hF : ∀ i, ∀ᵐ w ∂μ, |F i w| ≤ A * N i w)
    (hGb : ∀ᵐ w ∂μ, |G w - ∏ i ∈ J, F i w| ≤ ε * ∏ i ∈ J, N i w)
    (hQ : ∫⁻ w, ENNReal.ofReal (∏ i ∈ J, N i w) ∂μ ≤ ENNReal.ofReal E) (hE : 0 ≤ E) :
    |∫ w, ∏ i ∈ J, F i w ∂μ| ≤ A ^ J.card * E ∧ |∫ w, G w ∂μ - ∫ w, ∏ i ∈ J, F i w ∂μ| ≤ ε * E := by
  have hall : ∀ᵐ w ∂μ, ∀ i, |F i w| ≤ A * N i w := ae_all_iff.2 hF
  have hpb : ∀ᵐ w ∂μ, |∏ i ∈ J, F i w| ≤ A ^ J.card * ∏ i ∈ J, N i w := by
    filter_upwards [hall] with w hw
    rw [Finset.abs_prod]
    calc ∏ i ∈ J, |F i w| ≤ ∏ i ∈ J, (A * N i w) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => hw i
      _ = A ^ J.card * ∏ i ∈ J, N i w := by rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hm : AEStronglyMeasurable (fun w => ∏ i ∈ J, F i w) μ :=
    (Finset.aemeasurable_fun_prod _ fun i _ => hFm i).aestronglyMeasurable
  have lint : ∀ c : ℝ, 0 ≤ c → ∫⁻ w, ENNReal.ofReal (c * ∏ i ∈ J, N i w) ∂μ ≤ ENNReal.ofReal (c * E) := by
    intro c hc
    calc ∫⁻ w, ENNReal.ofReal (c * ∏ i ∈ J, N i w) ∂μ
        = ∫⁻ w, ENNReal.ofReal c * ENNReal.ofReal (∏ i ∈ J, N i w) ∂μ :=
          lintegral_congr fun w => ENNReal.ofReal_mul hc
      _ = ENNReal.ofReal c * ∫⁻ w, ENNReal.ofReal (∏ i ∈ J, N i w) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal E := by gcongr
      _ = ENNReal.ofReal (c * E) := (ENNReal.ofReal_mul hc).symm
  have lin2 : ∀ (f : Ω → ℝ) (c : ℝ), 0 ≤ c → (∀ᵐ w ∂μ, |f w| ≤ c * ∏ i ∈ J, N i w) →
      ∫⁻ w, ‖f w‖ₑ ∂μ ≤ ENNReal.ofReal (c * E) := fun f c hc hb =>
    (lintegral_mono_ae (hb.mono fun w h => by
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal h)).trans (lint c hc)
  have absle : ∀ (f : Ω → ℝ), AEStronglyMeasurable f μ → ∀ c : ℝ, 0 ≤ c →
      (∀ᵐ w ∂μ, |f w| ≤ c * ∏ i ∈ J, N i w) → |∫ w, f w ∂μ| ≤ c * E := by
    intro f hf c hc hb
    have h2 : ∫ w, ‖f w‖ ∂μ = (∫⁻ w, ‖f w‖ₑ ∂μ).toReal := integral_norm_eq_lintegral_enorm hf
    calc |∫ w, f w ∂μ| = ‖∫ w, f w ∂μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ w, ‖f w‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ c * E := by
          rw [h2]
          exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hc hE) (lin2 f c hc hb)
  have hAp : 0 ≤ A ^ J.card := pow_nonneg hA _
  have hint : Integrable (fun w => ∏ i ∈ J, F i w) μ := by
    refine ⟨hm, ?_⟩
    exact (lin2 _ _ hAp hpb).trans_lt ENNReal.ofReal_lt_top
  refine ⟨absle _ hm _ hAp hpb, ?_⟩
  rw [← integral_sub hG hint]
  exact absle _ (hG.sub hint).aestronglyMeasurable _ hε hGb
private theorem abs_prod_sub_prod_le {ι : Type} (P : Finset ι) (a b : ι → ℝ) {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 1 ≤ M)
    (ha : ∀ J ∈ P, |a J| ≤ M) (hb : ∀ J ∈ P, |b J| ≤ M) (hab : ∀ J ∈ P, |a J - b J| ≤ δ) :
    |∏ J ∈ P, a J - ∏ J ∈ P, b J| ≤ (P.card : ℝ) * δ * M ^ P.card := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | insert j P hj ih =>
      have ih' := ih (fun J h => ha J (Finset.mem_insert_of_mem h)) (fun J h => hb J (Finset.mem_insert_of_mem h))
        (fun J h => hab J (Finset.mem_insert_of_mem h))
      have hbp : |∏ J ∈ P, b J| ≤ M ^ P.card := by
        rw [Finset.abs_prod]
        calc ∏ J ∈ P, |b J| ≤ ∏ _J ∈ P, M :=
              Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun J h => hb J (Finset.mem_insert_of_mem h)
          _ = M ^ P.card := by simp
      rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
      have e : a j * ∏ J ∈ P, a J - b j * ∏ J ∈ P, b J =
          a j * (∏ J ∈ P, a J - ∏ J ∈ P, b J) + (a j - b j) * ∏ J ∈ P, b J := by ring
      have hM0 : 0 ≤ M := by linarith
      have h1 : |a j * (∏ J ∈ P, a J - ∏ J ∈ P, b J)| ≤ M * ((P.card : ℝ) * δ * M ^ P.card) := by
        rw [abs_mul]
        exact mul_le_mul (ha j (Finset.mem_insert_self _ _)) ih' (abs_nonneg _) hM0
      have h2 : |(a j - b j) * ∏ J ∈ P, b J| ≤ δ * M ^ P.card := by
        rw [abs_mul]
        exact mul_le_mul (hab j (Finset.mem_insert_self _ _)) hbp (abs_nonneg _) hδ
      have h3 : δ * M ^ P.card ≤ δ * M ^ (P.card + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM (Nat.le_succ _)) hδ
      rw [e]
      refine (abs_add_le _ _).trans ?_
      push_cast
      have e2 : ((P.card : ℝ) + 1) * δ * M ^ (P.card + 1) =
          M * ((P.card : ℝ) * δ * M ^ P.card) + δ * M ^ (P.card + 1) := by ring
      rw [e2]
      linarith
private def partitionWeightSum (k : ℕ) : ℝ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin k)), ((π.parts.card - 1).factorial : ℝ)
private theorem mixedCumulant_sub_jointCumulant_le (hC : Cumulants.MixedCumulantMomentExpansion)
    (hS : Cumulants.MomentCumulantRelations.Holds) {k : ℕ} (hk : 2 ≤ k)
    {Ω₀ Ω : Type} [MeasurableSpace Ω₀] [MeasurableSpace Ω] (ν : Measure Ω₀) [IsProbabilityMeasure ν]
    (μ : Measure Ω) (X : Fin k → Ω₀ → ℝ) (hX : ∀ i, IsBoundedRealRV (X i)) (κ : Fin k → ℝ)
    (F : Fin k → Ω → ℝ) {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 1 ≤ M)
    (ha : ∀ J : Finset (Fin k), J.Nonempty → |∫ ω, ∏ i ∈ J, (X i ω + -κ i) ∂ν| ≤ M)
    (hb : ∀ J : Finset (Fin k), J.Nonempty → |∫ w, ∏ i ∈ J, F i w ∂μ| ≤ M)
    (hab : ∀ J : Finset (Fin k), J.Nonempty →
      |∫ ω, ∏ i ∈ J, (X i ω + -κ i) ∂ν - ∫ w, ∏ i ∈ J, F i w ∂μ| ≤ δ) :
    ‖Cumulants.mixedCumulant ν X - (jointCumulant μ F : ℂ)‖ ≤
      partitionWeightSum k * ((k : ℝ) * δ * M ^ k) := by
  have hb' : ∀ i, IsBoundedRealRV fun ω => X i ω + -κ i := fun i => by
    obtain ⟨C, hCb⟩ := (hX i).bounded
    exact ⟨(hX i).measurable.add_const _, C + |κ i|, fun ω =>
      (abs_add_le _ _).trans (by rw [abs_neg]; linarith [hCb ω])⟩
  have h1 := (hS Ω₀ ν).2.2.1 k X (fun i => -κ i) hk hX
  have e : Cumulants.mixedCumulant ν X = (((∑ π : Finpartition (Finset.univ : Finset (Fin k)),
      (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) *
        ∏ J ∈ π.parts, ∫ ω, ∏ i ∈ J, (X i ω + -κ i) ∂ν) : ℝ) : ℂ) := by
    rw [← h1, hC Ω₀ ν k _ (by omega) hb']
    push_cast
    rfl
  rw [e, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  unfold jointCumulant partitionWeightSum
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun π _ => ?_)
  rw [← mul_sub, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ _)]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hne : ∀ J ∈ π.parts, J.Nonempty := fun J hJ => Finset.nonempty_iff_ne_empty.2 (π.ne_bot hJ)
  have h2 := abs_prod_sub_prod_le π.parts (fun J => ∫ ω, ∏ i ∈ J, (X i ω + -κ i) ∂ν)
    (fun J => ∫ w, ∏ i ∈ J, F i w ∂μ) hδ hM
    (fun J hJ => ha J (hne J hJ)) (fun J hJ => hb J (hne J hJ)) (fun J hJ => hab J (hne J hJ))
  refine h2.trans ?_
  have hc : π.parts.card ≤ k := by
    have := π.card_parts_le_card
    simpa using this
  have hcr : (π.parts.card : ℝ) ≤ k := by exact_mod_cast hc
  have hM0 : 0 ≤ M := by linarith
  have h3 : M ^ π.parts.card ≤ M ^ k := pow_le_pow_right₀ hM hc
  calc (π.parts.card : ℝ) * δ * M ^ π.parts.card ≤ (k : ℝ) * δ * M ^ π.parts.card :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcr hδ) (pow_nonneg hM0 _)
    _ ≤ (k : ℝ) * δ * M ^ k := mul_le_mul_of_nonneg_left h3 (by positivity)
private theorem stretchedExp_absorbs_power (Cf : ℝ) (n : ℕ) : ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ r : ℝ, 0 ≤ r →
    r ≤ x ^ ((1 : ℝ) / 100) + 1 →
      Cf * r ^ n * Real.exp (-(x ^ ((1 : ℝ) / 200))) ≤ Real.exp (-(x ^ ((1 : ℝ) / 300))) := by
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (6 * n)).const_mul (|Cf| * 2 ^ n)
  rw [mul_zero] at ht
  obtain ⟨Z, hZ⟩ := Filter.eventually_atTop.1 (ht.eventually (gt_mem_nhds (zero_lt_one' ℝ)))
  refine ⟨max 1 ((max Z 2) ^ 600), le_max_left _ _, fun x hx r hr0 hr => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = x ^ ((1 : ℝ) / 600) := ⟨_, rfl⟩
  have hz0 : 0 ≤ z := hz ▸ Real.rpow_nonneg hx0.le _
  have hzp : ∀ (m : ℕ), z ^ m = x ^ ((m : ℝ) / 600) := fun m => by
    rw [hz, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  have hzZ : max Z 2 ≤ z := by
    have h1 : (max Z 2) ^ 600 ≤ z ^ 600 := by
      rw [hzp]
      have : ((600 : ℕ) : ℝ) / 600 = 1 := by norm_num
      rw [this, Real.rpow_one]
      exact (le_max_right _ _).trans hx
    exact le_of_pow_le_pow_left₀ (by norm_num) hz0 h1
  have hz2 : 2 ≤ z := (le_max_right _ _).trans hzZ
  have hzz : Z ≤ z := (le_max_left _ _).trans hzZ
  have e1 : x ^ ((1 : ℝ) / 100) = z ^ 6 := by
    rw [hzp]
    norm_num
  have e2 : x ^ ((1 : ℝ) / 200) = z ^ 3 := by
    rw [hzp]
    norm_num
  have e3 : x ^ ((1 : ℝ) / 300) = z ^ 2 := by
    rw [hzp]
    norm_num
  rw [e1] at hr
  rw [e2, e3]
  have hz6 : 1 ≤ z ^ 6 := one_le_pow₀ (by linarith)
  have hr2 : r ≤ 2 * z ^ 6 := by linarith
  have hrn : r ^ n ≤ 2 ^ n * z ^ (6 * n) := by
    calc r ^ n ≤ (2 * z ^ 6) ^ n := pow_le_pow_left₀ hr0 hr2 n
      _ = 2 ^ n * z ^ (6 * n) := by rw [mul_pow, ← pow_mul]
  have hmain := hZ z hzz
  have hcf : Cf * r ^ n ≤ |Cf| * (2 ^ n * z ^ (6 * n)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self Cf) (pow_nonneg hr0 n)).trans
      (mul_le_mul_of_nonneg_left hrn (abs_nonneg _))
  have hexp : Real.exp (-(z ^ 3)) ≤ Real.exp (-z) * Real.exp (-(z ^ 2)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_nonneg hz0 hz0, mul_nonneg (mul_nonneg hz0 hz0) (sub_nonneg.2 hz2)]
  have hp : 0 ≤ |Cf| * (2 ^ n * z ^ (6 * n)) := by positivity
  calc Cf * r ^ n * Real.exp (-(z ^ 3)) ≤ |Cf| * (2 ^ n * z ^ (6 * n)) * Real.exp (-(z ^ 3)) :=
        mul_le_mul_of_nonneg_right hcf (Real.exp_pos _).le
    _ ≤ |Cf| * (2 ^ n * z ^ (6 * n)) * (Real.exp (-z) * Real.exp (-(z ^ 2))) :=
        mul_le_mul_of_nonneg_left hexp hp
    _ = (|Cf| * 2 ^ n * (z ^ (6 * n) * Real.exp (-z))) * Real.exp (-(z ^ 2)) := by ring
    _ ≤ 1 * Real.exp (-(z ^ 2)) := mul_le_mul_of_nonneg_right hmain.le (Real.exp_pos _).le
    _ = Real.exp (-(z ^ 2)) := one_mul _
theorem cumulantNearResponses_holds (hE : separatedLevelMomentsStatement)
    (hF : productApproxAtLastSeparatedStatement) (hG : meanScoreMomentBoundStatement)
    (hD : farLevelSupportSitesStatement) (hP : supportTotalBoundStatement)
    (hLaw : ResponseInTheExpansion.chainMeasurabilityStatement) (hC : Cumulants.MixedCumulantMomentExpansion)
    (hS : Cumulants.MomentCumulantRelations.Holds) : cumulantNearResponsesStatement := by
  refine hullPoints_of_hullParams (hullParams_mono (hullParams_and hullParams_base
    (hullParams_and (hullParams_of_points hE) (hullParams_and (hullParams_of_points hF)
    (hullParams_and (hullParams_of_hullPoints hG) (hullParams_and (hullParams_of_points hD)
      (hullParams_of_points hP)))))) fun Λ H => ?_)
  obtain ⟨⟨hDr, hy0, hk⟩, ⟨-, -, -, -, -, HE⟩, ⟨CF, -, XF, -, -, HF⟩, ⟨CG, -, -, -, -, HG⟩, ⟨CD, -, -, -, -, HD⟩,
    ⟨-, -, -, -, -, HP⟩⟩ := H
  have hFit : Λ.stepParams.Admissible := hDr.fits Λ.floor hy0
  obtain ⟨Dn, hDn⟩ : ∃ Dn : ℝ, Dn = 1 + |Λ.response.C₀| * |CD 0| := ⟨_, rfl⟩
  have hDn1 : 1 ≤ Dn := by
    rw [hDn]
    have : 0 ≤ |Λ.response.C₀| * |CD 0| := by positivity
    linarith
  obtain ⟨En, hEn⟩ : ∃ En : ℝ, En = (1 + |CG 0|) ^ Λ.k * (Λ.k.factorial : ℝ) ^ 6 := ⟨_, rfl⟩
  have hEn1 : 1 ≤ En := by
    rw [hEn]
    have h1 : 1 ≤ (1 + |CG 0|) ^ Λ.k := one_le_pow₀ (by linarith [abs_nonneg (CG 0)])
    have h2 : (1 : ℝ) ≤ (Λ.k.factorial : ℝ) ^ 6 :=
      one_le_pow₀ (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _))
    exact one_le_mul_of_one_le_of_one_le h1 h2
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ,
      Cf = partitionWeightSum Λ.k * ((Λ.k : ℝ) * En * (2 * Dn ^ Λ.k * En) ^ Λ.k) := ⟨_, rfl⟩
  obtain ⟨Xs, hXs1, hXs⟩ := stretchedExp_absorbs_power Cf (4 * Λ.k * Λ.k)
  refine ⟨fun _ => 0, 1, max (max XF Xs) Λ.floor, one_pos, le_max_right _ _, fun S hx => ?_⟩
  have hxF : XF ≤ S.scaleCoupling := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxS : Xs ≤ S.scaleCoupling := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx1 : 1 ≤ S.scaleCoupling := hXs1.trans hxS
  have hx0 : 0 < S.scaleCoupling := by linarith
  have hpr : ∀ (s n : ℕ) [NeZero n], IsProbabilityMeasure (markedSampleLaw S.tower S.β s n) ∧
      (markedSampleLaw S.tower S.β (s + 1) n).map (fun u : MarkedSample Λ.stepParams (s + 1) n => u.1) =
        markedSampleLaw S.tower S.β s (n * Λ.stepParams.side) :=
    fun s n _ => hLaw.2.2 Λ.stepParams hFit hDr.L_gt S.tower S.isCutoff S.marksMeasurable S.β s n
  have hμ' : IsProbabilityMeasure (markedSampleLaw S.tower S.β S.lastSeparated (S.levelSide S.lastSeparated)) :=
    (hpr S.lastSeparated (S.levelSide S.lastSeparated)).1
  have hμ : IsProbabilityMeasure (S.law S.lastSeparated (S.levelSide S.lastSeparated)) := hμ'
  have hbot := map_bottomField_eq_wilsonLaw S.tower S.β (fun s n _ => (hpr s n).2) S.lastSeparated
    (S.levelSide S.lastSeparated)
  have hν : IsProbabilityMeasure
      (wilsonLaw S.β (fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated))) := by
    rw [← hbot]
    exact Measure.isProbabilityMeasure_map (measurable_bottomField Λ.stepParams _ _).aemeasurable
  have hts : S.lastSeparated ≤ S.data.windowLevel := by
    refine le_trans ?_ S.supAdmissible.scaleLevel_le
    exact @Nat.findGreatest_le (S.data.SeparatedBelow Λ.stepParams S.β) (fun _ => Classical.propDecidable _)
      S.data.scaleLevel
  have hside : fineSide Λ.stepParams.side S.data.windowLevel (S.data.period Λ.stepParams.side) =
      fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated) := by
    rw [fineSide_eq, fineSide_eq]
    show S.data.period Λ.stepParams.side * Λ.stepParams.side ^ S.data.windowLevel =
      S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - S.lastSeparated) *
        Λ.stepParams.side ^ S.lastSeparated
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hts]
  have e1 : S.torusCumulant = Cumulants.mixedCumulant
      (wilsonLaw S.β (fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated)))
      fun i => curvatureObservable (S.weight i _) :=
    connectedCurvature_congr_side S.β hside fun m i => S.weight i m
  have hXb : ∀ i : Fin Λ.k, IsBoundedRealRV
      (curvatureObservable (S.weight i (fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated)))) :=
    fun i => curvatureObservable_isBounded _
  obtain ⟨κ, hκ⟩ : ∃ κ : Fin Λ.k → ℝ, κ = fun i => S.kappa S.lastSeparated (S.levelSide S.lastSeparated) i :=
    ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = Real.exp (-(S.scaleCoupling ^ ((1 : ℝ) / 200))) := ⟨_, rfl⟩
  have hε0 : 0 < ε := hε ▸ Real.exp_pos _
  have hε1 : ε ≤ 1 := by
    rw [hε, Real.exp_le_one_iff]
    have := Real.rpow_nonneg hx0.le ((1 : ℝ) / 200)
    linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Dn * (S.range : ℝ) ^ 4 := ⟨_, rfl⟩
  have hr1 : (1 : ℝ) ≤ S.range := by
    have h1 : 0 < S.scaleCoupling ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos hx0 _
    have h2 : 0 < S.range := Nat.ceil_pos.2 h1
    exact_mod_cast h2
  have hA1 : 1 ≤ A := by
    rw [hA]
    exact one_le_mul_of_one_le_of_one_le hDn1 (one_le_pow₀ hr1)
  have hA0 : 0 ≤ A := by linarith
  have hsz := HD S
  have hPi := HP S
  have hFb : ∀ i, ∀ᵐ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)),
      |S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| ≤
      A * S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) := fun i => by
    filter_upwards [(hPi i).2] with w hw
    have hN0 : 0 ≤ S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) := by linarith [hw.1]
    refine hw.2.trans (mul_le_mul_of_nonneg_right ?_ hN0)
    have h1 : ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ) ≤ |CD 0| * (S.range : ℝ) ^ 4 :=
      (hsz.1 i).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    calc Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ)
        ≤ |Λ.response.C₀| * ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _)
      _ ≤ |Λ.response.C₀| * (|CD 0| * (S.range : ℝ) ^ 4) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ A := by
          rw [hA, hDn]
          have : 0 ≤ (S.range : ℝ) ^ 4 := by positivity
          nlinarith
  have hNn : ∀ᵐ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)), ∀ i,
      0 ≤ S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) := by
    refine ae_all_iff.2 fun i => ?_
    filter_upwards [(hPi i).2] with w hw
    linarith [hw.1]
  have hmoment : ∀ J : Finset (Fin Λ.k), J.Nonempty →
      ∫⁻ w, ENNReal.ofReal (∏ i ∈ J, S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w))
          ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) ≤ ENNReal.ofReal En := by
    intro J hJ
    have h0 := (HG S J.card (Finset.card_pos.2 hJ) J.toList (Finset.length_toList J)).2
    have e0 : ∀ w, (J.toList.map fun i => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)).prod =
        ∏ i ∈ J, S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) := fun w => Finset.prod_map_toList _ _
    simp only [e0] at h0
    refine h0.trans (ENNReal.ofReal_le_ofReal ?_)
    have hc : J.card ≤ Λ.k := by simpa using Finset.card_le_univ J
    have hf : (J.card.factorial : ℝ) ≤ Λ.k.factorial := by exact_mod_cast Nat.factorial_le hc
    rw [hEn]
    have h1 : CG 0 ^ J.card ≤ (1 + |CG 0|) ^ Λ.k := by
      calc CG 0 ^ J.card ≤ |CG 0 ^ J.card| := le_abs_self _
        _ = |CG 0| ^ J.card := abs_pow _ _
        _ ≤ (1 + |CG 0|) ^ J.card := pow_le_pow_left₀ (abs_nonneg _) (by linarith) _
        _ ≤ (1 + |CG 0|) ^ Λ.k := pow_le_pow_right₀ (by linarith [abs_nonneg (CG 0)]) hc
    have h2 : (J.card.factorial : ℝ) ^ 6 ≤ (Λ.k.factorial : ℝ) ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) hf 6
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hpair : ∀ J : Finset (Fin Λ.k), J.Nonempty →
      |∫ w, ∏ i ∈ J, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)
          ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated))| ≤ A ^ J.card * En ∧
      |∫ w, conditionalCenteredProduct S.tower S.β S.coeff S.lastSeparated (S.levelSide S.lastSeparated)
          (fun i => S.weight i _) J κ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) -
        ∫ w, ∏ i ∈ J, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)
            ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated))| ≤ ε * En := by
    intro J hJ
    obtain ⟨hb1, -, hb3⟩ := HF S J
    have hb3' := hb3 hxF
    refine integral_prod_bounds (fun i w => S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w))
      (fun i w => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)) _ J (fun i => (hPi i).1)
      integrable_condExp hA0 hε0.le hFb ?_ (hmoment J hJ) (by linarith)
    filter_upwards [hb1, hNn] with w hw hN
    rw [hκ]
    refine hw.trans (mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => hN i))
    rw [hε]
    exact hb3'
  have hmomW : ∀ J : Finset (Fin Λ.k),
      ∫ W, ∏ i ∈ J, (curvatureObservable
          (S.weight i (fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated))) W + -κ i)
        ∂(wilsonLaw S.β (fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated))) =
      ∫ w, conditionalCenteredProduct S.tower S.β S.coeff S.lastSeparated (S.levelSide S.lastSeparated)
        (fun i => S.weight i _) J κ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) := by
    intro J
    rw [← HE S J κ, ← hbot, integral_map (measurable_bottomField Λ.stepParams _ _).aemeasurable]
    · simp only [sub_eq_add_neg]
      rfl
    · exact (Finset.measurable_fun_prod _ fun i _ => (hXb i).measurable.add_const _).aestronglyMeasurable
  have hcard : ∀ J : Finset (Fin Λ.k), A ^ J.card ≤ A ^ Λ.k := fun J =>
    pow_le_pow_right₀ hA1 (by simpa using Finset.card_le_univ J)
  have hAk : 1 ≤ A ^ Λ.k := one_le_pow₀ hA1
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * A ^ Λ.k * En := ⟨_, rfl⟩
  have hAEk : 1 ≤ A ^ Λ.k * En := one_le_mul_of_one_le_of_one_le hAk hEn1
  have hM1 : 1 ≤ M := by
    rw [hM, mul_assoc]
    linarith
  have hEn0 : 0 ≤ En := by linarith
  have hclose := mixedCumulant_sub_jointCumulant_le hC hS hk
    (wilsonLaw S.β (fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated)))
    (S.law S.lastSeparated (S.levelSide S.lastSeparated))
    (fun i => curvatureObservable
      (S.weight i (fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated)))) hXb κ
    (fun i w => S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
      (S.state S.lastSeparated (S.levelSide S.lastSeparated) w))
    (δ := ε * En) (M := M) (mul_nonneg hε0.le hEn0) hM1
    (fun J hJ => by
      rw [hmomW J]
      have h1 := (hpair J hJ).1
      have h2 := (hpair J hJ).2
      have h3 := abs_sub_abs_le_abs_sub
        (∫ w, conditionalCenteredProduct S.tower S.β S.coeff S.lastSeparated (S.levelSide S.lastSeparated)
          (fun i => S.weight i _) J κ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)))
        (∫ w, ∏ i ∈ J, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)
            ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)))
      have h4 := mul_le_mul_of_nonneg_right (hcard J) hEn0
      have h5 : ε * En ≤ En := by nlinarith
      have h6 : En ≤ A ^ Λ.k * En := by nlinarith
      rw [hM]
      linarith)
    (fun J hJ => by
      have h1 := (hpair J hJ).1
      have h4 := mul_le_mul_of_nonneg_right (hcard J) hEn0
      rw [hM]
      linarith)
    (fun J hJ => by
      rw [hmomW J]
      exact (hpair J hJ).2)
  rw [e1]
  have hcum : S.responseCumulant = jointCumulant (S.law S.lastSeparated (S.levelSide S.lastSeparated))
      (fun i w => S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)) := rfl
  rw [hcum]
  refine hclose.trans ?_
  have hrr : (S.range : ℝ) ≤ S.scaleCoupling ^ ((1 : ℝ) / 100) + 1 :=
    (Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le _)).le
  have hfin := hXs S.scaleCoupling hxS (S.range : ℝ) (Nat.cast_nonneg _) hrr
  refine le_trans (le_of_eq ?_) hfin
  rw [hCf, hM, hA, hε]
  ring
end YangMills.Construction.MomentLaw
end

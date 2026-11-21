import YangMills.Construction.LawByMomentsOfTheFlow.CompletedFormAcrossAStepProof
import YangMills.Construction.LawByMomentsOfTheFlow.ResponsesAtTheFarLevelAreSized
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
private theorem forAllParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁)
    (h₂ : ForAllParameters Q₂) : ForAllParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_admissible_floor :
    ForAllParameters fun Λ => Λ.table.Admissible ∧ Λ.table.floorMin ≤ Λ.floor := by apply _root_.YangMills.SharedProofs.p9852 <;> assumption
private theorem ForAllParameters.mono {Q₁ Q₂ : MomentParameters → Prop} (h : ForAllParameters Q₁)
    (hm : ∀ Λ, Q₁ Λ → Q₂ Λ) : ForAllParameters Q₂ := by apply _root_.YangMills.SharedProofs.p9549 <;> assumption
private theorem forAllParameters_of_forAllPoints
    {Q : ∀ Λ : MomentParameters, (ℕ → ℝ) → ℝ → ℝ → MomentPoint Λ → Prop} (h : ForAllPoints Q) :
    ForAllParameters fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧
      ∀ S : MomentPoint Λ, Q Λ C c X₀ S := h
private theorem forAllPoints_of_forAllParameters
    {Q : ∀ Λ : MomentParameters, (ℕ → ℝ) → ℝ → ℝ → MomentPoint Λ → Prop}
    (h : ForAllParameters fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧
      ∀ S : MomentPoint Λ, Q Λ C c X₀ S) :
    ForAllPoints Q := h
private theorem forAllParameters_of_holdsOnAllParameters {P : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop}
    (h : WeightedResponses.HoldsAtAdmissibleParameters P) : ForAllParameters fun Λ => P Λ.table Λ.floor := by
  intro a ha
  obtain ⟨L₀, r₀, hr, H⟩ := h a ha
  refine ⟨L₀, r₀, 0, hr, ?_⟩
  intro L hodd hL Tb hTa hTL hD _ _ hrt _ Kr _
  obtain ⟨y₀, Y⟩ := H L hodd hL Tb hTa hTL hD hrt
  exact ⟨y₀, fun y hy hR hW g _ _ k _ _ _ R d _ => Y y hy hR hW⟩
abbrev _root_.YangMills.SharedProofs.p43324 := @forAllParameters_of_holdsOnAllParameters
private theorem measurable_prod_sigma_of_fibers {X A : Type} [MeasurableSpace X] [Countable A] {B : A → Type}
    [∀ a, MeasurableSpace (B a)] {Z : Type} [MeasurableSpace Z] {f : X × Sigma B → Z}
    (h : ∀ a, Measurable fun p : X × B a => f (p.1, ⟨a, p.2⟩)) : Measurable f := by apply _root_.YangMills.SharedProofs.p5842 <;> assumption
section LiveStates
variable {ℓ : TorusLumps.StepParameters} (T : WeightedResponses.StageTower ℓ)
open Classical in
private def deadIndicator (w n : ℕ) [NeZero n] (q : WeightedResponses.StageState T w n) : ENNReal :=
  if WeightedResponses.IsLiveState ℓ (T.stage w).coupling (T.stage w).labelWeight q.1 q.2.1 q.2.2 then 0 else 1
private theorem measurable_deadIndicator (w n : ℕ) [NeZero n] (hb : TorusLumps.IsBlockTorusSide ℓ n)
    (hrow : TorusLumps.HullExpansion ℓ (T.stage w).depth (T.stage w).coupling (T.stage w).functional
      (T.stage w).density (T.stage w).labels (T.stage w).labelWeight
      (T.stage w).clusterFactor (T.stage w).siteDensity) : Measurable (deadIndicator T w n) := by
  classical
  refine measurable_prod_sigma_of_fibers fun Y => ?_
  have h1 := (hrow.borel n hb Y).1
  have hset : MeasurableSet {p : TorusFields.TorusField n × (Y → (T.stage w).labels.Ω) |
      0 < (if TorusLumps.IsHullState ℓ (TorusLumps.clusterRange (T.stage w).coupling) p.1 Y
        then (T.stage w).labelWeight n p.1 Y p.2 else 0)} :=
    measurableSet_lt measurable_const h1
  have e : (fun p : TorusFields.TorusField n × (Y → (T.stage w).labels.Ω) => deadIndicator T w n (p.1, ⟨Y, p.2⟩)) =
      fun p => if 0 < (if TorusLumps.IsHullState ℓ (TorusLumps.clusterRange (T.stage w).coupling) p.1 Y
          then (T.stage w).labelWeight n p.1 Y p.2 else 0)
        then 0 else 1 := by
    funext p
    unfold deadIndicator WeightedResponses.IsLiveState
    by_cases hh : TorusLumps.IsHullState ℓ (TorusLumps.clusterRange (T.stage w).coupling) p.1 Y
    · simp [hh]
    · simp [hh]
  rw [e]
  exact Measurable.ite hset measurable_const measurable_const
private theorem ae_isLiveState (β : ℝ) (k n : ℕ) [NeZero n] (hb : TorusLumps.IsBlockTorusSide ℓ n)
    (hrow : TorusLumps.HullExpansion ℓ (T.stage k).depth (T.stage k).coupling (T.stage k).functional
      (T.stage k).density (T.stage k).labels (T.stage k).labelWeight
      (T.stage k).clusterFactor (T.stage k).siteDensity)
    (hst : Measurable (WeightedResponses.stageState T k n))
    (hZ : (0 : ℝ) < ∫ W, TorusLumps.wilsonWeight β (WeightedResponses.fineSide ℓ.side k n) W
      ∂(TorusFields.fieldHaar (WeightedResponses.fineSide ℓ.side k n)))
    (hd : ∀ G : WeightedResponses.StageState T k n → ENNReal, Measurable G →
      ENNReal.ofReal (∫ W, TorusLumps.wilsonWeight β (WeightedResponses.fineSide ℓ.side k n) W
          ∂(TorusFields.fieldHaar (WeightedResponses.fineSide ℓ.side k n))) *
        ∫⁻ u, G (WeightedResponses.stageState T k n u) ∂(WeightedResponses.markedSampleLaw T β k n) =
      ∫⁻ W, (open Classical in
        ∑ Y ∈ Finset.univ.filter (TorusLumps.IsHullState ℓ (TorusLumps.clusterRange (T.stage k).coupling) W),
          ∫⁻ ω, G (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage k).labelWeight n W Y ω)
            ∂(Measure.pi fun _ : Y => (T.stage k).labels.μ)) ∂(TorusFields.fieldHaar n)) :
    ∀ᵐ d ∂(WeightedResponses.markedSampleLaw T β k n),
      WeightedResponses.IsLiveState ℓ (T.stage k).coupling (T.stage k).labelWeight
        (WeightedResponses.stageState T k n d).1
        (WeightedResponses.stageState T k n d).2.1 (WeightedResponses.stageState T k n d).2.2 := by
  have hm := measurable_deadIndicator T k n hb hrow
  have hd' := hd (deadIndicator T k n) hm
  have hzero : (∫⁻ W, (open Classical in
      ∑ Y ∈ Finset.univ.filter (TorusLumps.IsHullState ℓ (TorusLumps.clusterRange (T.stage k).coupling) W),
        ∫⁻ ω, deadIndicator T k n (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage k).labelWeight n W Y ω)
          ∂(Measure.pi fun _ : Y => (T.stage k).labels.μ)) ∂(TorusFields.fieldHaar n)) = 0 := by
    refine (lintegral_congr fun W => ?_).trans lintegral_zero
    classical
    refine Finset.sum_eq_zero fun Y hY => ?_
    have hH : TorusLumps.IsHullState ℓ (TorusLumps.clusterRange (T.stage k).coupling) W Y :=
      (Finset.mem_filter.mp hY).2
    refine (lintegral_congr fun ω => ?_).trans lintegral_zero
    unfold deadIndicator
    by_cases hp : 0 < (T.stage k).labelWeight n W Y ω
    · rw [if_pos ⟨hH, hp⟩, zero_mul]
    · rw [ENNReal.ofReal_of_nonpos (not_lt.mp hp), mul_zero]
  rw [hzero] at hd'
  have hz := (mul_eq_zero.mp hd').resolve_left (by simpa using hZ)
  have hm2 : Measurable fun d => deadIndicator T k n (WeightedResponses.stageState T k n d) := hm.comp hst
  have hae := (lintegral_eq_zero_iff hm2).mp hz
  filter_upwards [hae] with d hd0
  by_contra hcon
  have h1 : deadIndicator T k n (WeightedResponses.stageState T k n d) = 1 := by
    unfold deadIndicator
    exact if_neg hcon
  rw [show deadIndicator T k n (WeightedResponses.stageState T k n d) = 0 from hd0] at h1
  exact zero_ne_one h1
abbrev _root_.YangMills.SharedProofs.p25706 := @ae_isLiveState
open Classical in
private theorem measurable_sum_centeredResponses (u n : ℕ) [NeZero n]
    (A : WeightedResponses.ResponseSetup (T.stage u).toStepSetup) (hb : TorusLumps.IsBlockTorusSide ℓ n)
    (hrow : A.IsAdmissible) (f : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide ℓ.side (T.stage u).depth n))
    (B : Finset (TorusFields.TorusSite n)) :
    Measurable fun q : WeightedResponses.StageState T u n => ∑ y ∈ B,
      ((if WeightedResponses.IsLiveState ℓ (T.stage u).coupling (T.stage u).labelWeight q.1 q.2.1 q.2.2
        then A.hull n y q.1 q.2.1 q.2.2 f else 0) -
        A.cold n y (TorusFields.trivialField n) f) := by
  refine Finset.measurable_sum _ fun y _ => ?_
  refine Measurable.sub ?_ measurable_const
  exact measurable_prod_sigma_of_fibers fun Y => hrow.bounds.hull_borel n hb y Y f
end LiveStates
private theorem abs_sum_le_card_mul_one_add_mean {ι : Type} (B : Finset ι) (h sc : ι → ℝ) {C₀ sz : ℝ}
    (hC : 1 ≤ C₀) (hz : sz ≤ 1) (hsc : ∀ y, 0 ≤ sc y) (hh : ∀ y ∈ B, |h y| ≤ (C₀ + sc y) * sz) :
    |∑ y ∈ B, h y| ≤ C₀ * (B.card : ℝ) * (1 + (B.card : ℝ)⁻¹ * ∑ y ∈ B, sc y) := by
  have h1 : |∑ y ∈ B, h y| ≤ ∑ y ∈ B, (C₀ + sc y) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y hy => (hh y hy).trans ?_)
    have : 0 ≤ C₀ + sc y := by linarith [hsc y]
    nlinarith
  refine h1.trans ?_
  rcases B.eq_empty_or_nonempty with rfl | hne
  · simp
  have hs : 0 ≤ ∑ y ∈ B, sc y := Finset.sum_nonneg fun y _ => hsc y
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have e : C₀ * (B.card : ℝ) * (1 + (B.card : ℝ)⁻¹ * ∑ y ∈ B, sc y) = C₀ * B.card + C₀ * ∑ y ∈ B, sc y := by
    field_simp
  rw [e]
  nlinarith
private theorem weightSupportSites_congr_depth {L : ℕ} [NeZero L] {a b : ℕ} (e : a = b) (n : ℕ) [NeZero n]
    (f : ∀ m, WeightedResponses.PlaquetteWeight m) :
    ResponseInTheExpansion.weightSupportSites L a n (f (WeightedResponses.fineSide L a n)) =
      ResponseInTheExpansion.weightSupportSites L b n (f (WeightedResponses.fineSide L b n)) := by
  subst e
  rfl
private theorem weightNorm_congr_depth {L : ℕ} [NeZero L] {a b : ℕ} (e : a = b) (n : ℕ) [NeZero n]
    (f : ∀ m, WeightedResponses.PlaquetteWeight m) :
    WeightedResponses.weightNorm L a (f (WeightedResponses.fineSide L a n)) =
      WeightedResponses.weightNorm L b (f (WeightedResponses.fineSide L b n)) := by
  subst e
  rfl
theorem supportTotalBound_holds (hDen : StageDensity.stageStateDensityStatement)
    (hLaw : WeightedResponses.ChainIsProbabilityLaw)
    (hSt : ResponseInTheExpansion.StageStatesMeasurableStatement)
    (hW : weightsSitesBelowScaleStatement) : supportTotalBoundStatement := by
  refine forAllPoints_of_forAllParameters (ForAllParameters.mono (forAllParameters_and forAllParameters_admissible_floor
    (forAllParameters_and (forAllParameters_of_holdsOnAllParameters hDen) (forAllParameters_of_forAllPoints hW))) fun Λ H => ?_)
  obtain ⟨⟨hDr, hy0⟩, HD, ⟨CW, -, -, -, -, HW⟩⟩ := H
  have hFit : Λ.stepParams.Admissible := hDr.fits Λ.floor hy0
  refine ⟨fun _ => 0, 1, Λ.floor, one_pos, le_rfl, fun S i => ?_⟩
  have hus : S.lastSeparated ≤ S.data.scaleLevel :=
    @Nat.findGreatest_le (S.data.SeparatedBelow Λ.stepParams S.β) (fun _ => Classical.propDecidable _)
      S.data.scaleLevel
  have hts : S.lastSeparated ≤ S.data.windowLevel := hus.trans S.supAdmissible.scaleLevel_le
  have lev : ∀ j ≤ S.data.windowLevel, ResponseInTheExpansion.StageOnFlow Λ.table Λ.response Λ.floor S.β j
      ⟨S.tower.stage j, S.resp j⟩ := fun j hj => by
    have h := S.onFlow j hj
    rwa [← S.stage_eq j hj] at h
  have hOnParameters : ResponseInTheExpansion.IsTowerAtParameters Λ.table Λ.floor S.tower S.β S.lastSeparated := by
    refine ⟨S.startsAtWilson, fun j hj => ?_, fun j hj => (lev j (hj.trans hts)).onFamily.onFamily⟩
    cases j with
    | zero => exact (lev 0 (Nat.zero_le _)).coupling_eq
    | succ j' => exact (lev j' (by omega)).nextCoupling_eq
  have hlev := lev S.lastSeparated hts
  have hresp : (S.resp S.lastSeparated).IsAdmissible := hlev.onFamily.admissible
  have hLge : 2 ^ 16 ≤ Λ.stepParams.side := hFit.L_ge
  have hn₀ := hFit.n₀_ge
  have hside := S.side_le
  have hm1 : 1 ≤ S.data.sideExponent := by
    by_contra hcon
    have h0 : S.data.sideExponent = 0 := by omega
    have h2 : S.data.period Λ.stepParams.side = 2 := by
      show 2 * Λ.stepParams.side ^ S.data.sideExponent = 2
      rw [h0, pow_zero, mul_one]
    rw [h2] at hside
    nlinarith
  have hblock : TorusLumps.IsBlockTorusSide Λ.stepParams (S.levelSide S.lastSeparated) := by
    refine ⟨?_, ?_⟩
    · show Λ.stepParams.side ∣ S.data.period Λ.stepParams.side *
        Λ.stepParams.side ^ (S.data.windowLevel - S.lastSeparated)
      refine Dvd.dvd.mul_right ?_ _
      exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) 2
    · refine hside.trans ?_
      show S.data.period Λ.stepParams.side ≤
        S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - S.lastSeparated)
      exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
  have hsz := (HW S S.lastSeparated hus i).1
  have hZ := (hLaw Λ.stepParams hFit hFit.depth_lt S.β (fun _ => 0) S.lastSeparated
    (S.levelSide S.lastSeparated)).2.1
  have hlive := ae_isLiveState S.tower S.β S.lastSeparated (S.levelSide S.lastSeparated) hblock
    (hOnParameters.onFamily S.lastSeparated le_rfl).isStep.1.2
    (hSt Λ.stepParams hFit S.tower S.lastSeparated (S.levelSide S.lastSeparated)) hZ
    (fun G hG => HD S.tower S.β S.lastSeparated (S.levelSide S.lastSeparated) hOnParameters S.marksMeasurable hblock G hG)
  have hlt : (S.tower.stage S.lastSeparated).depth = S.lastSeparated := hlev.depth_eq
  have hsites := weightSupportSites_congr_depth (L := Λ.stepParams.side) hlt (S.levelSide S.lastSeparated)
    (fun m => S.weight i m)
  have hsize := weightNorm_congr_depth (L := Λ.stepParams.side) hlt (S.levelSide S.lastSeparated)
    (fun m => S.weight i m)
  have hK : (S.resp S.lastSeparated).responseParams = Λ.response := hlev.params_eq
  have hC1 : 1 ≤ Λ.response.C₀ := by
    have hk := hresp.params_admissible
    rw [hK] at hk
    have h1 := hk.N₀_nonneg
    have h2 := hk.Kc_ge
    have h3 := hk.C₀_eq
    have h4 : 1 ≤ (S.tower.stage S.lastSeparated).toStepSetup.params.coupling := hDr.a_ge
    rw [h3]
    linarith
  have hsc : ∀ (Y : Finset (TorusFields.TorusSite (S.levelSide S.lastSeparated)))
      (ω : Y → (S.tower.stage S.lastSeparated).labels.Ω) (y : TorusFields.TorusSite (S.levelSide S.lastSeparated)),
      0 ≤ WeightedResponses.siteScore (S.resp S.lastSeparated).score Y ω y := fun Y ω y => by
    unfold WeightedResponses.siteScore
    split_ifs
    · exact hresp.price.nonneg _
    · exact le_rfl
  refine ⟨?_, ?_⟩
  · have hm := (measurable_sum_centeredResponses S.tower S.lastSeparated (S.levelSide S.lastSeparated)
      (S.resp S.lastSeparated) hblock hresp (S.weight i _)
      (ResponseInTheExpansion.weightSupportSites Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
        (S.levelSide S.lastSeparated) (S.weight i _))).comp
      (hSt Λ.stepParams hFit S.tower S.lastSeparated (S.levelSide S.lastSeparated))
    refine ⟨_, hm, ?_⟩
    filter_upwards [hlive] with w hw
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [if_pos hw]
    rfl
  · filter_upwards [hlive] with w hw
    refine ⟨?_, ?_⟩
    · show 1 ≤ 1 + _ * _
      have h1 : 0 ≤ ∑ y ∈ S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i,
          WeightedResponses.siteScore (S.resp S.lastSeparated).score
            (WeightedResponses.stageState S.tower S.lastSeparated (S.levelSide S.lastSeparated) w).2.1
            (WeightedResponses.stageState S.tower S.lastSeparated (S.levelSide S.lastSeparated) w).2.2 y :=
        Finset.sum_nonneg fun y _ => hsc _ _ y
      exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg (α := ℝ)
        (S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i).card)) h1)
    · have hb := abs_sum_le_card_mul_one_add_mean
        (ResponseInTheExpansion.weightSupportSites Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
          (S.levelSide S.lastSeparated) (S.weight i _))
        (fun y => WeightedResponses.centeredHullResponse (S.resp S.lastSeparated).cold (S.resp S.lastSeparated).hull
          (S.levelSide S.lastSeparated) y
          (WeightedResponses.stageState S.tower S.lastSeparated (S.levelSide S.lastSeparated) w).1
          (WeightedResponses.stageState S.tower S.lastSeparated (S.levelSide S.lastSeparated) w).2.1
          (WeightedResponses.stageState S.tower S.lastSeparated (S.levelSide S.lastSeparated) w).2.2 (S.weight i _))
        (fun y => WeightedResponses.siteScore (S.resp S.lastSeparated).score
          (WeightedResponses.stageState S.tower S.lastSeparated (S.levelSide S.lastSeparated) w).2.1
          (WeightedResponses.stageState S.tower S.lastSeparated (S.levelSide S.lastSeparated) w).2.2 y)
        hC1 (hsize.le.trans hsz) (fun y => hsc _ _ y) (fun y _ => by
          have h := hresp.bounds.size_hull (S.levelSide S.lastSeparated) hblock y _ _ _ hw (S.weight i _)
          rw [hK] at h
          exact h)
      have e1 : S.data.supportSites Λ.stepParams.side S.lastSeparated i =
          ResponseInTheExpansion.weightSupportSites Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
            (S.levelSide S.lastSeparated) (S.weight i _) := hsites.symm
      have e2 : S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i =
          ResponseInTheExpansion.weightSupportSites Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
            (S.levelSide S.lastSeparated) (S.weight i _) := hsites.symm
      rw [e1]
      show |∑ y ∈ _, _| ≤ _ * ResponseInTheExpansion.meanSiteScore (S.resp S.lastSeparated).score
        (S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i) _ _
      unfold ResponseInTheExpansion.meanSiteScore
      rw [e2]
      exact hb
end YangMills.Construction.MomentLaw
end

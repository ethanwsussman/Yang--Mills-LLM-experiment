import YangMills.Construction.LawByMomentsOfTheFlow.ResponsesAtTheFarLevelAreBounded
import YangMills.Construction.LawByMomentsOfTheFlow.VariablesOfAPointSplitProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps RenormalizationStepParameters StepSettings WeightedResponses ResponseInTheExpansion StageDensity
private theorem forAllParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁)
    (h₂ : ForAllParameters Q₂) : ForAllParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_of_forAllPoints
    {Q : ∀ Λ : MomentParameters, (ℕ → ℝ) → ℝ → ℝ → MomentPoint Λ → Prop} (h : ForAllPoints Q) :
    ForAllParameters fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, Q Λ C c X₀ S := h
private theorem forAllParameters_mono {Q Q' : MomentParameters → Prop} (h : ForAllParameters Q)
    (hq : ∀ Λ : MomentParameters, Λ.table.Admissible → Λ.table.floorMin ≤ Λ.floor → Q Λ → Q' Λ) :
    ForAllParameters Q' := by
  intro a ha
  obtain ⟨L₁, rt₁, C₁, hrt₁, H₁⟩ := h a ha
  refine ⟨L₁, rt₁, C₁, hrt₁, ?_⟩
  intro L hLodd hLge Tb hTa hTL hDr hCS hOn hrt hCd Kr hKr
  obtain ⟨y₁, Y₁⟩ := H₁ L hLodd hLge Tb hTa hTL hDr hCS hOn hrt hCd Kr hKr
  refine ⟨max y₁ Tb.floorMin, ?_⟩
  intro y hy hRet hHas g hg hyg k _ hk2 hk8 R d hd
  exact hq ⟨Tb, Kr, y, g, k, R, d⟩ hDr ((le_max_right _ _).trans hy)
    (Y₁ y ((le_max_left _ _).trans hy) hRet hHas g hg hyg k hk2 hk8 R d hd)
private def StageDensityAt (Tb : ParameterAssignment) (y : ℝ) : Prop :=
  ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n],
    IsTowerAtParameters Tb y T β k → T.MarksMeasurable → IsBlockTorusSide (Tb.stepParameters y) n →
    ∀ G : StageState T k n → ENNReal, Measurable G →
      ENNReal.ofReal (∫ W, wilsonWeight β (fineSide (Tb.stepParameters y).side k n) W
          ∂(fieldHaar (fineSide (Tb.stepParameters y).side k n))) *
        ∫⁻ u, G (stageState T k n u) ∂(markedSampleLaw T β k n) =
      ∫⁻ W, (open Classical in
        ∑ Y ∈ Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange (T.stage k).coupling) W),
          ∫⁻ ω, G (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage k).labelWeight n W Y ω)
            ∂(Measure.pi fun _ : Y => (T.stage k).labels.μ)) ∂(fieldHaar n)
private theorem forAllParameters_stageDensity (hDen : stageStateDensityStatement) :
    ForAllParameters fun Λ => StageDensityAt Λ.table Λ.floor := by
  intro a ha
  obtain ⟨L₀, rt₀, hrt₀, H⟩ := hDen a ha
  refine ⟨L₀, rt₀, 0, hrt₀, ?_⟩
  intro L hLodd hLge Tb hTa hTL hDr _ _ hrt _ Kr _
  obtain ⟨y₁, Y₁⟩ := H L hLodd hLge Tb hTa hTL hDr hrt
  refine ⟨y₁, ?_⟩
  intro y hy hRet hHas g hg hyg k _ hk2 hk8 R d hd
  exact Y₁ y hy hRet hHas
private theorem measurable_of_sigma_slices {X A : Type} [MeasurableSpace X] [Countable A] {β : A → Type}
    [∀ a, MeasurableSpace (β a)] {γ : Type} [MeasurableSpace γ] {f : X × Sigma β → γ}
    (h : ∀ a, Measurable fun p : X × β a => f (p.1, ⟨a, p.2⟩)) : Measurable f := by apply _root_.YangMills.SharedProofs.p5842 <;> assumption
section Live
variable {ℓ : StepParameters} (T : StageTower ℓ)
open Classical in
private def deadIndicator (w n : ℕ) [NeZero n] (q : StageState T w n) : ENNReal :=
  if IsLiveState ℓ (T.stage w).coupling (T.stage w).labelWeight q.1 q.2.1 q.2.2 then 0 else 1
private theorem measurable_deadIndicator (w n : ℕ) [NeZero n] (hb : IsBlockTorusSide ℓ n)
    (hrow : HullExpansion ℓ (T.stage w).depth (T.stage w).coupling (T.stage w).functional (T.stage w).density
      (T.stage w).labels (T.stage w).labelWeight (T.stage w).clusterFactor (T.stage w).siteDensity) :
    Measurable (deadIndicator T w n) := by
  classical
  refine measurable_of_sigma_slices fun Y => ?_
  have h1 := (hrow.borel n hb Y).1
  have hset : MeasurableSet {p : TorusField n × (Y → (T.stage w).labels.Ω) |
      0 < (if IsHullState ℓ (clusterRange (T.stage w).coupling) p.1 Y then (T.stage w).labelWeight n p.1 Y p.2
        else 0)} :=
    measurableSet_lt measurable_const h1
  have e : (fun p : TorusField n × (Y → (T.stage w).labels.Ω) => deadIndicator T w n (p.1, ⟨Y, p.2⟩)) =
      fun p => if 0 < (if IsHullState ℓ (clusterRange (T.stage w).coupling) p.1 Y then
          (T.stage w).labelWeight n p.1 Y p.2 else 0)
        then 0 else 1 := by
    funext p
    unfold deadIndicator IsLiveState
    by_cases hh : IsHullState ℓ (clusterRange (T.stage w).coupling) p.1 Y
    · simp [hh]
    · simp [hh]
  rw [e]
  exact Measurable.ite hset measurable_const measurable_const
end Live
private theorem ae_isLiveState {Tb : ParameterAssignment} {y : ℝ} (hD : StageDensityAt Tb y)
    (hfit : (Tb.stepParameters y).Admissible) (hLaw : ChainIsProbabilityLaw)
    (hSt : StageStatesMeasurableStatement) (T : StageTower (Tb.stepParameters y))
    (β : ℝ) (w n : ℕ) [NeZero n] (hstand : IsTowerAtParameters Tb y T β w) (hco : T.MarksMeasurable)
    (hn : IsBlockTorusSide (Tb.stepParameters y) n) :
    ∀ᵐ d ∂(markedSampleLaw T β w n), IsLiveState (Tb.stepParameters y) (T.stage w).coupling (T.stage w).labelWeight
      (stageState T w n d).1 (stageState T w n d).2.1 (stageState T w n d).2.2 := by
  have hhull := (hstand.onFamily w le_rfl).isStep.1.2
  have hm := measurable_deadIndicator T w n hn hhull
  have hd := hD T β w n hstand hco hn (deadIndicator T w n) hm
  have hzero : (∫⁻ W, (open Classical in
      ∑ Y ∈ Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange (T.stage w).coupling) W),
        ∫⁻ ω, deadIndicator T w n (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage w).labelWeight n W Y ω)
          ∂(Measure.pi fun _ : Y => (T.stage w).labels.μ)) ∂(fieldHaar n)) = 0 := by
    refine (lintegral_congr fun W => ?_).trans lintegral_zero
    classical
    refine Finset.sum_eq_zero fun Y hY => ?_
    have hH : IsHullState (Tb.stepParameters y) (clusterRange (T.stage w).coupling) W Y :=
      (Finset.mem_filter.mp hY).2
    refine (lintegral_congr fun ω => ?_).trans lintegral_zero
    unfold deadIndicator
    by_cases hp : 0 < (T.stage w).labelWeight n W Y ω
    · rw [if_pos ⟨hH, hp⟩, zero_mul]
    · rw [ENNReal.ofReal_of_nonpos (not_lt.mp hp), mul_zero]
  have hZ : (0 : ℝ) < ∫ W, wilsonWeight β (fineSide (Tb.stepParameters y).side w n) W
      ∂(fieldHaar (fineSide (Tb.stepParameters y).side w n)) :=
    (hLaw (Tb.stepParameters y) hfit hfit.depth_lt β (fun _ => 0) w n).2.1
  rw [hzero] at hd
  have hz := (mul_eq_zero.mp hd).resolve_left (by simpa using hZ)
  have hm2 : Measurable fun d => deadIndicator T w n (stageState T w n d) := hm.comp (hSt _ hfit T w n)
  have hae := (lintegral_eq_zero_iff hm2).mp hz
  filter_upwards [hae] with d hd0
  by_contra hcon
  have : deadIndicator T w n (stageState T w n d) = 1 := by
    unfold deadIndicator
    exact if_neg hcon
  rw [show deadIndicator T w n (stageState T w n d) = 0 from hd0] at this
  exact zero_ne_one this
private theorem one_le_meanSiteScore {n : ℕ} [NeZero n] {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w)
    (B Y : Finset (TorusSite n)) (ω : Y → Ω) : 1 ≤ meanSiteScore s B Y ω := by apply _root_.YangMills.SharedProofs.p16546 <;> assumption
private theorem abs_supportResponseTotal_le {R : StepSetup} {A : ResponseSetup R} (hA : A.IsAdmissible)
    (hC₀ : 1 ≤ A.responseParams.C₀) {n : ℕ} [NeZero n]
    (hs : IsBlockTorusSide R.params n) (f : PlaquetteWeight (fineSide R.params.side R.depth n))
    (hf : weightNorm R.params.side R.depth f ≤ 1) (W : TorusField n)
    (Y : Finset (TorusSite n)) (ω : Y → R.labels.Ω) (hq : IsLiveState R.params R.coupling R.labelWeight W Y ω) :
    |supportResponseTotal A f W Y ω| ≤ A.responseParams.C₀ *
      ((weightSupportSites R.params.side R.depth n f).card : ℝ) *
      meanSiteScore A.score (weightSupportSites R.params.side R.depth n f) Y ω := by apply _root_.YangMills.SharedProofs.p79992 <;> assumption
theorem farLevelResponseBoundStatement_holds (hW : weightsSitesBelowScaleStatement)
    (hDen : stageStateDensityStatement) (hLaw : ChainIsProbabilityLaw)
    (hSt : StageStatesMeasurableStatement) : farLevelResponseBoundStatement := by
  suffices h : ForAllParameters fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ,
      ∀ i : Fin Λ.k,
      ∀ᵐ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)),
        1 ≤ S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) ∧
        |S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| ≤
          Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ) *
            S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
              (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) from h
  refine forAllParameters_mono (forAllParameters_and (forAllParameters_of_forAllPoints hW)
    (forAllParameters_stageDensity hDen)) ?_
  rintro Λ hDr hy ⟨⟨C, _, _, _, _, HW⟩, HD⟩
  refine ⟨fun _ => 0, 1, Λ.floor, one_pos, le_rfl, fun S i => ?_⟩
  have hFit : Λ.stepParams.Admissible := hDr.fits Λ.floor hy
  have hts : S.lastSeparated ≤ S.data.scaleLevel := by
    unfold MomentPoint.lastSeparated
    classical exact Nat.findGreatest_le _
  have hsK : S.data.scaleLevel ≤ S.data.windowLevel := S.supAdmissible.scaleLevel_le
  have htK : S.lastSeparated ≤ S.data.windowLevel := hts.trans hsK
  have hon : ∀ j ≤ S.data.windowLevel, (S.tower.stage j).toStepSetup.OnParameters Λ.table Λ.floor := fun j hj => by
    have h := (S.onFlow j hj).onFamily.onFamily
    rw [← S.stage_eq j hj] at h
    exact h
  have hx : ∀ j ≤ S.data.windowLevel,
      (S.tower.stage j).coupling = (couplingFlow (Λ.table.stepParameters Λ.floor) S.β j).1 := fun j hj => by
    have h := (S.onFlow j hj).coupling_eq
    rw [← S.stage_eq j hj] at h
    exact h
  have hx' : ∀ j ≤ S.data.windowLevel,
      (S.tower.stage j).nextCoupling = (couplingFlow (Λ.table.stepParameters Λ.floor) S.β (j + 1)).1 :=
    fun j hj => by
    have h := (S.onFlow j hj).nextCoupling_eq
    rw [← S.stage_eq j hj] at h
    exact h
  have hstand : IsTowerAtParameters Λ.table Λ.floor S.tower S.β S.lastSeparated := by
    refine ⟨S.startsAtWilson, fun j hj => ?_, fun j hj => hon j (hj.trans htK)⟩
    rcases Nat.lt_or_ge j (S.lastSeparated + 1) with h | h
    · exact hx j (by omega)
    · have e : j = S.lastSeparated + 1 := by omega
      subst e
      exact hx' S.lastSeparated htK
  have hblock : IsBlockTorusSide Λ.stepParams (S.levelSide S.lastSeparated) := by
    have hn₀ : 4096 ≤ Λ.stepParams.n₀ := hDr.n₀_ge
    have hLge : 2 ^ 16 ≤ Λ.stepParams.side := hFit.L_ge
    have hside : Λ.stepParams.side * Λ.stepParams.n₀ ≤ 2 * Λ.stepParams.side ^ S.data.sideExponent := S.side_le
    have hm : S.data.sideExponent ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hside
      nlinarith
    have hpos : 0 < Λ.stepParams.side ^ (S.data.windowLevel - S.lastSeparated) := pow_pos (by omega) _
    refine ⟨?_, ?_⟩
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ hm) _) _
    · exact hside.trans (Nat.le_mul_of_pos_right _ hpos)
  have hlive := ae_isLiveState HD hFit hLaw hSt S.tower S.β S.lastSeparated (S.levelSide S.lastSeparated)
    hstand S.marksMeasurable hblock
  have hA : (S.resp S.lastSeparated).IsAdmissible := by
    have h := (S.onFlow S.lastSeparated htK).onFamily.admissible
    rw [← S.stage_eq S.lastSeparated htK] at h
    exact h
  have hK : (S.resp S.lastSeparated).responseParams = Λ.response := by
    have h := (S.onFlow S.lastSeparated htK).params_eq
    rw [← S.stage_eq S.lastSeparated htK] at h
    exact h
  have hlev : (S.tower.stage S.lastSeparated).toStepSetup.depth = S.lastSeparated := by
    have h := (S.onFlow S.lastSeparated htK).depth_eq
    rw [← S.stage_eq S.lastSeparated htK] at h
    exact h
  have hC₀ : 1 ≤ (S.resp S.lastSeparated).responseParams.C₀ := by
    have hk' := hA.params_admissible
    have h1 : 1 ≤ Λ.stepParams.coupling := hFit.a_ge
    have h2 := hk'.N₀_nonneg
    have h3 := hk'.Kc_ge
    have h4 : (S.tower.stage S.lastSeparated).toStepSetup.params.coupling = Λ.stepParams.coupling := rfl
    rw [hk'.C₀_eq, h4]
    linarith
  have e1 : ∀ t' : ℕ, t' = S.lastSeparated →
      weightSupportSites Λ.stepParams.side t' (S.levelSide S.lastSeparated)
        (S.weight i (fineSide Λ.stepParams.side t' (S.levelSide S.lastSeparated))) =
      S.data.supportSites Λ.stepParams.side S.lastSeparated i := by
    rintro _ rfl
    rfl
  have e2 : ∀ t' : ℕ, t' = S.lastSeparated →
      weightNorm Λ.stepParams.side t' (S.weight i (fineSide Λ.stepParams.side t' (S.levelSide S.lastSeparated))) ≤ 1 := by
    rintro _ rfl
    exact (HW S S.lastSeparated hts i).1
  filter_upwards [hlive] with w hq
  refine ⟨one_le_meanSiteScore hA.price.nonneg _ _ _, ?_⟩
  have h := abs_supportResponseTotal_le hA hC₀ hblock (S.weight i _) (e2 _ hlev) _ _ _ hq
  rw [e1 _ hlev, hK] at h
  have e3 : S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
      (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) =
      meanSiteScore (S.resp S.lastSeparated).score (S.data.supportSites Λ.stepParams.side S.lastSeparated i)
        (stageState S.tower S.lastSeparated (S.levelSide S.lastSeparated) w).2.1
        (stageState S.tower S.lastSeparated (S.levelSide S.lastSeparated) w).2.2 := rfl
  rw [e3]
  exact h
end YangMills.Construction.MomentLaw
end

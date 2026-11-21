import YangMills.Construction.LawByMomentsOfTheFlow.GoodStatesInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.PlacesOfTheSitesOfASupport
import YangMills.Construction.LawByMomentsOfTheFlow.ScoresInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.VariablesOfAPointSplit
import YangMills.Construction.LawByMomentsOfTheFlow.WeightsAndSitesBelowTheScale
import YangMills.Construction.ResponseInTheExpansion.FarObservablesSplitOverAStep
import YangMills.Construction.TransfersOffTheWalk.OneStepOfSeveralResponsesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace YangMills.Construction.MomentLaw
open StepSettings StepCosts RenormalizationStepParameters StepGas TorusFields TorusLumps ClusterExpansionOfAStep WeightedResponses ResponseInTheExpansion
  FreeEnergies LevelTestFunctions
section CaseFunctions
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem caseTerm_liveCaseFunction
    (hnn : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω),
      IsHullState R.params R.range W Yt → 0 ≤ R.labelWeight (n * R.params.side) W Yt ωt)
    (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) (F : CaseFunction R n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω) :
    caseTerm R C V q (liveCaseFunction F) bad Yt b W ν = caseTerm R C V q F bad Yt b W ν := by apply _root_.YangMills.SharedProofs.p99396 <;> assumption
private theorem caseMean_liveCaseFunction
    (hnn : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω),
      IsHullState R.params R.range W Yt → 0 ≤ R.labelWeight (n * R.params.side) W Yt ωt)
    (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) (F : CaseFunction R n) :
    caseMean R C V q (liveCaseFunction F) = caseMean R C V q F := by
  unfold caseMean caseIntegral
  simp only [caseTerm_liveCaseFunction hnn]
private theorem caseTerm_congr_baseChoices {F F' : CaseFunction R n}
    (h : ∀ W Yt ωt bad b, b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) →
      F' W Yt ωt bad b = F W Yt ωt bad b)
    (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω) :
    caseTerm R C V q F' bad Yt b W ν = caseTerm R C V q F bad Yt b W ν := by
  classical
  unfold caseTerm
  split_ifs with hh
  · by_cases hb : b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 (q.fieldWithStoredLinks W))
    · rw [h _ _ _ _ _ hb]
    · have hz : baseLaw (R := R) (q.fieldWithStoredLinks W) b = 0 := by
        unfold baseLaw
        rw [if_neg hb]
      simp [stepWeight, hz]
  · rfl
private theorem caseMean_congr_baseChoices {F F' : CaseFunction R n}
    (h : ∀ W Yt ωt bad b, b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) →
      F' W Yt ωt bad b = F W Yt ωt bad b)
    (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) :
    caseMean R C V q F' = caseMean R C V q F := by
  unfold caseMean caseIntegral
  simp only [caseTerm_congr_baseChoices h]
private theorem prod_liveCaseFunction {ι : Type} {J : Finset ι} (hJ : J.Nonempty) (X : ι → CaseFunction R n) :
    (fun W Yt ωt bad b => ∏ i ∈ J, liveCaseFunction (X i) W Yt ωt bad b) =
      liveCaseFunction (fun W Yt ωt bad b => ∏ i ∈ J, X i W Yt ωt bad b) := by
  classical
  funext W Yt ωt bad b
  by_cases hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt
  · simp only [liveCaseFunction, if_pos hl]
  · obtain ⟨i, hi⟩ := hJ
    simp only [liveCaseFunction, if_neg hl]
    exact Finset.prod_eq_zero hi rfl
end CaseFunctions
section Transport
private theorem fineWeight_heq (f : FinePlaquetteFunction) {m m' : ℕ} (h : m = m') :
    HEq (fineWeight f m) (fineWeight f m') := by
  subst h
  rfl
private theorem responseSetup_with_params {R : StepSetup} (A : ResponseSetup R) {K : ResponseParameters}
    (h : A.responseParams = K) : ({ A with responseParams := K } : ResponseSetup R) = A := by
  subst h
  rfl
private theorem nextStageWithResponse_fields {ℓ : StepParameters}
    (hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup) (lam x'' : ℝ) (c c' : ChainStage ℓ)
    (A : ResponseSetup c.toStepSetup) (A' : ResponseSetup c'.toStepSetup) (z : StageWithResponse ℓ)
    (h : (⟨c, A⟩ : StageWithResponse ℓ) = z)
    (h' : (⟨c', A'⟩ : StageWithResponse ℓ) = nextStageWithResponse hL lam x'' z) :
    HEq A'.cold A.coldStep ∧ HEq A'.hull A.hullStep ∧
      HEq A'.score (coarseLabelScore (L := ℓ.side) A.responseParams.s₁ A.score) := by
  subst h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h'
  cases h2
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩
abbrev _root_.YangMills.SharedProofs.p59553 := @nextStageWithResponse_fields
private theorem weightSupportSites_depth_congr {L : ℕ} [NeZero L] (w : ∀ m : ℕ, PlaquetteWeight m) {t s : ℕ} (n : ℕ)
    [NeZero n] (h : t = s) :
    weightSupportSites L t n (w (fineSide L t n)) = weightSupportSites L s n (w (fineSide L s n)) := by
  subst h
  rfl
abbrev _root_.YangMills.SharedProofs.p57791 := @weightSupportSites_depth_congr
private theorem card_weightSupportSites_congr {L : ℕ} [NeZero L] (w : ∀ m : ℕ, PlaquetteWeight m) (t : ℕ) {N M : ℕ}
    [NeZero N] [NeZero M] (h : N = M) :
    (weightSupportSites L t N (w (fineSide L t N))).card = (weightSupportSites L t M (w (fineSide L t M))).card := by
  subst h
  rfl
private theorem weightNorm_congr {L : ℕ} (w : ∀ m : ℕ, PlaquetteWeight m) {t s N M : ℕ} (h : t = s) (h' : N = M) :
    weightNorm L t (w (fineSide L t N)) = weightNorm L s (w (fineSide L s M)) := by
  subst h
  subst h'
  rfl
private theorem sideAt_succ_mul {k : ℕ} (P : LevelData k) (L v : ℕ) (hv : v + 1 ≤ P.windowLevel) :
    P.sideAt L (v + 1) * L = P.sideAt L v := by apply _root_.YangMills.SharedProofs.p32891 <;> assumption
private theorem separation_le_supDist {k : ℕ} (P : LevelData k) (L : ℕ) [NeZero L] (u : ℕ) {N : ℕ} [NeZero N]
    (hN : N = P.sideAt L (u + 1)) {i j : Fin k} (hij : i ≠ j) {Y Y' : TorusSite N}
    (hY : Y ∈ thickening 2 (weightSupportSites L (u + 1) N (P.testWeight L i (fineSide L (u + 1) N))))
    (hY' : Y' ∈ thickening 2 (weightSupportSites L (u + 1) N (P.testWeight L j (fineSide L (u + 1) N)))) :
    P.separation L u ≤ TorusFields.supDist Y Y' := by
  subst hN
  exact Nat.sInf_le ⟨i, j, hij, Y, hY, Y', hY', rfl⟩
private theorem meanSiteScore_nonneg {Ω : Type} {m : ℕ} [NeZero m] {s : Ω → ℝ} (h0 : ∀ w, 0 ≤ s w)
    (B Y : Finset (TorusSite m)) (ω : Y → Ω) : 0 ≤ meanSiteScore s B Y ω := by
  unfold meanSiteScore
  have : 0 ≤ ((B.card : ℝ))⁻¹ * ∑ y ∈ B, siteScore s Y ω y :=
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun y _ => by
      unfold siteScore
      split_ifs
      · exact h0 _
      · exact le_rfl)
  linarith
private theorem markedSampleLaw_cast {ℓ : StepParameters} (T : StageTower ℓ) (β : ℝ) {K K' : ℕ} (h : K = K') (n : ℕ)
    [NeZero n] :
    Measurable (fun w : MarkedSample ℓ K n => (h ▸ w : MarkedSample ℓ K' n)) ∧
      (markedSampleLaw T β K n).map (fun w : MarkedSample ℓ K n => (h ▸ w : MarkedSample ℓ K' n)) =
        markedSampleLaw T β K' n := by
  subst h
  exact ⟨measurable_id, Measure.map_id⟩
end Transport
section Parameters
private theorem forAllParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁)
    (h₂ : ForAllParameters Q₂) : ForAllParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := h₁ a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := h₂ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hL hLL Tb e1 e2 e3 e4 e5 e6 e7 Kr hKr
  obtain ⟨y₁, Y₁⟩ := H₁ L hL (le_of_max_le_left hLL) Tb e1 e2 e3 e4 e5 (e6.trans (min_le_left _ _))
    (le_of_max_le_left e7) Kr hKr
  obtain ⟨y₂, Y₂⟩ := H₂ L hL (le_of_max_le_right hLL) Tb e1 e2 e3 e4 e5 (e6.trans (min_le_right _ _))
    (le_of_max_le_right e7) Kr hKr
  refine ⟨max y₁ y₂, fun y hy hR hW g hg hgy k _ hk2 hk8 R d hd => ⟨?_, ?_⟩⟩
  · exact Y₁ y (le_of_max_le_left hy) hR hW g hg hgy k hk2 hk8 R d hd
  · exact Y₂ y (le_of_max_le_right hy) hR hW g hg hgy k hk2 hk8 R d hd
abbrev _root_.YangMills.SharedProofs.p2495 := @forAllParameters_and
private theorem forAllParameters_mono {Q₁ Q₂ : MomentParameters → Prop} (h : ∀ Λ, Q₁ Λ → Q₂ Λ)
    (h₁ : ForAllParameters Q₁) : ForAllParameters Q₂ := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := h₁ a ha
  refine ⟨L₁, r₁, C₁, hr₁, ?_⟩
  intro L hL hLL Tb e1 e2 e3 e4 e5 e6 e7 Kr hKr
  obtain ⟨y₁, Y₁⟩ := H₁ L hL hLL Tb e1 e2 e3 e4 e5 e6 e7 Kr hKr
  exact ⟨y₁, fun y hy hR hW g hg hgy k _ hk2 hk8 R d hd =>
    h _ (Y₁ y hy hR hW g hg hgy k hk2 hk8 R d hd)⟩
abbrev _root_.YangMills.SharedProofs.p432 := @forAllParameters_mono
private theorem forAllParameters_admissible :
    ForAllParameters fun Λ => Λ.table.Admissible ∧ 1 ≤ Λ.floor ∧ Λ.k ≤ 8 ∧ Odd Λ.stepParams.side := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L hodd _ Tb _ e2 e3 _ _ _ _ Kr _
  exact ⟨1, fun y hy _ _ g _ _ k _ _ hk8 R d _ => ⟨e3, hy, hk8, by show Odd Tb.side; rw [e2]; exact hodd⟩⟩
private theorem forAllParameters_of_atResponseParameters {P : ParameterAssignment → ResponseParameters → ℝ → Prop}
    (h : AtResponseParameters P) : ForAllParameters fun Λ => P Λ.table Λ.response Λ.floor := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := h a ha
  refine ⟨L₁, r₁, C₁, hr₁, ?_⟩
  intro L hL hLL Tb e1 e2 e3 e4 e5 e6 e7 Kr _
  obtain ⟨y₁, Y₁⟩ := H₁ L hL hLL Tb e1 e2 e3 e4 e5 e6 e7 Kr
  exact ⟨y₁, fun y hy hR hW g _ _ k _ _ _ R d _ => Y₁ y hy ⟨hR, hW⟩⟩
abbrev _root_.YangMills.SharedProofs.p38170 := @forAllParameters_of_atResponseParameters
private theorem forAllParameters_of_holdsOnParameters {P : ParameterAssignment → ℝ → Prop}
    (h : HoldsOnParameterFamilies P) : ForAllParameters fun Λ => P Λ.table Λ.floor := by
  intro a ha
  obtain ⟨L₀, r₀, C₀, hr, h⟩ := h a ha
  refine ⟨L₀, r₀, C₀, hr, ?_⟩
  intro L hodd hL Tb e1 e2 hD hCS hCH hrt hC Kr _
  obtain ⟨y₀, h⟩ := h L hodd hL Tb e1 e2 hD hCS hCH hrt hC
  exact ⟨y₀, fun y hy hR hW g _ _ k _ _ _ R d _ => h y hy hR hW⟩
abbrev _root_.YangMills.SharedProofs.p27928 := @forAllParameters_of_holdsOnParameters
private theorem forAllParameters_of_holdsAtEveryStepWithConstant
    {P : ℝ → ParameterAssignment → ∀ R : StepSetup, ResponseSetup R → Prop} (h : HoldsAtEveryStepWithConstant P) :
    ForAllParameters fun Λ => ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : StepSetup) (A : ResponseSetup R),
      A.responseParams = Λ.response → OnStepParameters Λ.table Λ.floor A → P C Λ.table R A := by
  obtain ⟨rt₀, hr, H⟩ := h
  intro a _
  refine ⟨0, rt₀, 0, hr, ?_⟩
  intro L _ _ Tb _ _ hD _ _ hrt _ Kr _
  obtain ⟨y₀, C, hC, h⟩ := H Tb hD hrt Kr
  exact ⟨y₀, fun y hy _ _ g _ _ k _ _ _ R d _ => ⟨C, hC, h y hy⟩⟩
end Parameters
section Point
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private def scoredTower : ScoredStageTower S.tower :=
  ⟨Λ.response, fun u => { S.resp u with responseParams := Λ.response }⟩
private def fineFunctionOf (i : Fin Λ.k) : FinePlaquetteFunction := fun b =>
  S.data.fn i (WithLp.toLp 2 fun a => (Λ.stepParams.side : ℝ) ^ S.data.windowLevel /
    (Λ.stepParams.side : ℝ) ^ S.data.scaleLevel *
    circleRep (S.data.period Λ.stepParams.side) (b a / (Λ.stepParams.side : ℝ) ^ S.data.windowLevel - S.data.center a))
private theorem stageOnFlow_at {u : ℕ} (hu : u ≤ S.data.windowLevel) :
    StageOnFlow Λ.table Λ.response Λ.floor S.β u (⟨S.tower.stage u, S.resp u⟩ : StageWithResponse Λ.stepParams) := by apply _root_.YangMills.SharedProofs.p21183 <;> assumption
private theorem scoredTower_setup {u : ℕ} (hu : u ≤ S.data.windowLevel) : (scoredTower S).setup u = S.resp u :=
  responseSetup_with_params _ (stageOnFlow_at S hu).params_eq
private theorem resp_succ_fields {u : ℕ} (hu : u + 1 ≤ S.data.windowLevel) :
    HEq (S.resp (u + 1)).cold (S.resp u).coldStep ∧ HEq (S.resp (u + 1)).hull (S.resp u).hullStep ∧
      HEq (S.resp (u + 1)).score
        (coarseLabelScore (L := Λ.stepParams.side) (S.resp u).responseParams.s₁ (S.resp u).score) :=
  nextStageWithResponse_fields S.labelFacts Λ.table.lam _ _ _ _ _ _ (S.stage_eq u (by omega)) (S.stage_eq (u + 1) hu)
private theorem scoredTower_followsFlow {tp : ℕ} (htp : tp ≤ S.data.windowLevel) :
    (scoredTower S).FollowsFlow S.β tp := by
  have h00 := stageOnFlow_at S (Nat.zero_le S.data.windowLevel)
  have hf := S.isInitial
  have h0 : (⟨S.tower.stage 0, S.resp 0⟩ : StageWithResponse Λ.stepParams) = S.initial := S.stage_eq 0 (Nat.zero_le _)
  rw [← h0] at hf
  have ht0 : (S.tower.stage 0).depth = 0 := hf.depth_eq
  refine
    { isFlowStep := fun u hu => ?_
      startsAtWilson := S.startsAtWilson
      bottom_coupling := hf.coupling_eq
      isCutoff_bottom := S.isCutoff
      marksMeasurable := S.marksMeasurable
      params_eq := fun _ => rfl
      N₀_eq := ?_
      coeff_zero := hf.coeff_eq
      score_zero := hf.score_eq
      cold_zero := fun n _ z W f => ?_
      hull_zero := fun n _ z W Y ω f => ?_
      score_succ := fun u hu => ?_
      cold_succ := fun u hu => eq_of_heq (resp_succ_fields S (by omega)).1
      hull_succ := fun u hu => eq_of_heq (resp_succ_fields S (by omega)).2.1
      isAdmissible := fun u hu => ?_
      coeff_near_one := fun u hu => (stageOnFlow_at S (hu.trans htp)).abs_coeff_sub_one_le }
  · have h := stageOnFlow_at S (hu.trans htp)
    exact ⟨h.onFamily.onFamily, h.depth_eq, h.coupling_eq, h.nextCoupling_eq, h.functional_eq⟩
  · have h := h00.onFamily.N₀_eq
    have hk : (S.resp 0).responseParams = Λ.response := h00.params_eq
    show Λ.response.N₀ = _
    rw [← hk]
    exact h
  · exact S.cold_zero n z W _ _
      (fineWeight_heq f (by show n = fineSide _ (S.tower.stage 0).depth n; rw [ht0]; rfl))
  · exact S.hull_zero n z W Y ω _ _
      (fineWeight_heq f (by show n = fineSide _ (S.tower.stage 0).depth n; rw [ht0]; rfl))
  · have h := eq_of_heq (resp_succ_fields S (u := u) (by omega)).2.2
    have hk : (S.resp u).responseParams = Λ.response := (stageOnFlow_at S (by omega)).params_eq
    rw [hk] at h
    exact h
  · rw [scoredTower_setup S (hu.trans htp)]
    exact (stageOnFlow_at S (hu.trans htp)).onFamily.admissible
abbrev _root_.YangMills.DeltaSharedProofs.p502274 := @scoredTower_followsFlow
private theorem couplingsAboveFloor_of_le {t : ℕ} (ht : t ≤ S.data.windowLevel) :
    CouplingsAboveFloor (Λ.table.stepParameters Λ.floor) S.β t := fun j hj => by
  have h := stageOnFlow_at S (hj.trans ht)
  exact le_of_le_of_eq h.onFamily.onFamily.le_coupling h.coupling_eq
private theorem isBlockTorusSide_levelSide (hn : 3 ≤ Λ.stepParams.n₀) (t : ℕ) :
    IsBlockTorusSide Λ.stepParams (S.levelSide t) := by
  have hL : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hs := S.side_le
  have hm : S.data.sideExponent ≠ 0 := by
    intro h0
    unfold LevelData.period at hs
    rw [h0] at hs
    have : 1 * 3 ≤ Λ.stepParams.side * Λ.stepParams.n₀ := Nat.mul_le_mul hL hn
    simp at hs
    omega
  obtain ⟨m, hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm
  refine ⟨?_, ?_⟩
  · show Λ.stepParams.side ∣ S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - t)
    unfold LevelData.period
    rw [hm', pow_succ]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Dvd.intro_left _ rfl) _) _
  · show _ ≤ S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - t)
    exact hs.trans (Nat.le_mul_of_pos_right _ (pow_pos hL _))
abbrev _root_.YangMills.SharedProofs.p33093 := @isBlockTorusSide_levelSide
private theorem sideAtLevel_eq_levelSide (u : ℕ) : S.sideAtLevel u = S.levelSide u := by apply _root_.YangMills.SharedProofs.p7138 <;> assumption
private theorem fittedResponse_eq_supportTotal (i : Fin Λ.k) {u : ℕ} (hu : u ≤ S.data.windowLevel) (n : ℕ) [NeZero n]
    (q : StageState S.tower u n) : fittedResponse (scoredTower S) (fineFunctionOf S i) u n q = S.supportTotal u n i q := by
  unfold fittedResponse functionSites MomentPoint.supportTotal supportResponseTotal
  exact Finset.sum_congr
    (weightSupportSites_depth_congr (fun m => S.weight i m) n (stageOnFlow_at S hu).depth_eq).symm fun _ _ => rfl
open Classical in
private theorem separatedBelow_lastSeparated : S.data.SeparatedBelow Λ.stepParams S.β S.lastSeparated := by
  unfold MomentPoint.lastSeparated
  exact Nat.findGreatest_spec (P := S.data.SeparatedBelow Λ.stepParams S.β) (Nat.zero_le _)
    (fun u hu => absurd hu (Nat.not_lt_zero u))
private theorem ae_sampleAtLevel
    (down : ∀ (s d n : ℕ) [NeZero n], Measurable (sampleBelow Λ.stepParams s d n) ∧
      Measure.map (sampleBelow Λ.stepParams s d n) (markedSampleLaw S.tower S.β (s + d) n) =
        markedSampleLaw S.tower S.β s (fineSide Λ.stepParams.side d n))
    (u : ℕ) (hu : u ≤ S.data.windowLevel) {p : MarkedSample Λ.stepParams u (S.sideAtLevel u) → Prop}
    (hp : ∀ᵐ x ∂(S.law u (S.sideAtLevel u)), p x) :
    ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)), p (S.sampleAtLevel u hu w) := by
  have hc := markedSampleLaw_cast S.tower S.β (Nat.add_sub_of_le hu).symm (S.data.period Λ.stepParams.side)
  obtain ⟨m1, e1⟩ := down u (S.data.windowLevel - u) (S.data.period Λ.stepParams.side)
  have e2 := Measure.map_map (μ := markedSampleLaw S.tower S.β S.data.windowLevel (S.data.period Λ.stepParams.side))
    m1 hc.1
  rw [hc.2, e1] at e2
  have hm : Measurable (S.sampleAtLevel u hu) := m1.comp hc.1
  have e3 : (S.law S.data.windowLevel (S.data.period Λ.stepParams.side)).map (S.sampleAtLevel u hu) =
      S.law u (S.sideAtLevel u) := e2.symm
  rw [← e3] at hp
  exact ae_of_ae_map hm.aemeasurable hp
end Point
theorem stepVariableMeanSplit_proof (hF : separatedProductOverStepStatement) (hS : weightsSitesBelowScaleStatement)
    (hG : flowStatesAreGroundsStatement) (hM : fittedResponseIsConditionalMeanStatement)
    (hLD : sampleBelowLawStatement) (hRT : TowerAlongFlowStatement) (hP : supportSitesLocationStatement) :
    stepVariableMeanSplitStatement := by
  unfold weightsSitesBelowScaleStatement ForAllPoints at hS
  unfold flowStatesAreGroundsStatement at hG
  unfold fittedResponseIsConditionalMeanStatement at hM
  unfold TowerAlongFlowStatement at hRT
  unfold separatedProductOverStepStatement at hF
  unfold stepVariableMeanSplitStatement ForAllPoints
  have h := forAllParameters_and (forAllParameters_of_holdsAtEveryStepWithConstant hF)
    (forAllParameters_and hS (forAllParameters_and (forAllParameters_of_atResponseParameters hG)
      (forAllParameters_and (forAllParameters_of_atResponseParameters hM)
        (forAllParameters_and (forAllParameters_of_holdsOnParameters hRT) forAllParameters_admissible))))
  refine forAllParameters_mono (fun Λ hh => ?_) h
  obtain ⟨⟨Cf, hCf, Hf⟩, ⟨Cs, _, _, _, _, Hs⟩, Hg, Hm, ⟨hfit, hlam, -⟩, hD, hy, hk, hodd⟩ := hh
  refine ⟨fun _ => Cf * 64 * Real.exp 16, 1, Λ.floor, one_pos, le_rfl, fun S u hu J hJ => ?_⟩
  classical
  have hn3 : 3 ≤ Λ.stepParams.n₀ := le_trans (by norm_num) hfit.n₀_ge
  have htK : S.lastSeparated ≤ S.data.windowLevel := S.lastSeparated_le
  have hts : S.lastSeparated ≤ S.data.scaleLevel := Nat.findGreatest_le S.data.scaleLevel
  have h1 : u + 1 ≤ S.data.windowLevel := by omega
  have h0 : u ≤ S.data.windowLevel := by omega
  have hus : u ≤ S.data.scaleLevel := by omega
  have hst := stageOnFlow_at S h0
  have htab : OnStepParameters Λ.table Λ.floor (S.resp u) := hst.onFamily
  have hAK : (S.resp u).responseParams = Λ.response := hst.params_eq
  have hτ : (S.tower.stage u).depth = u := hst.depth_eq
  have hside' : S.sideAtLevel (u + 1) * Λ.stepParams.side = S.levelSide u := by
    rw [sideAtLevel_eq_levelSide]
    exact sideAt_succ_mul _ _ _ h1
  have hfarD := separatedBelow_lastSeparated S u hu
  have hsAbove : ∀ i, weightSupportSites Λ.stepParams.side ((S.tower.stage u).depth + 1) (S.sideAtLevel (u + 1))
      (S.weight i (fineSide Λ.stepParams.side ((S.tower.stage u).depth + 1) (S.sideAtLevel (u + 1)))) =
      weightSupportSites Λ.stepParams.side (u + 1) (S.sideAtLevel (u + 1))
        (S.weight i (fineSide Λ.stepParams.side (u + 1) (S.sideAtLevel (u + 1)))) :=
    fun i => weightSupportSites_depth_congr (fun m => S.weight i m) _ (by rw [hτ])
  have hcard : ∀ i, (weightSupportSites Λ.stepParams.side (S.tower.stage u).depth
      (S.sideAtLevel (u + 1) * Λ.stepParams.side)
      (S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth
        (S.sideAtLevel (u + 1) * Λ.stepParams.side)))).card =
      (S.data.supportSites Λ.stepParams.side u i).card := fun i => by
    rw [weightSupportSites_depth_congr (fun m => S.weight i m) _ hτ]
    exact card_weightSupportSites_congr (fun m => S.weight i m) u hside'
  have hr : (S.tower.stage u).toStepSetup.range = clusterRange (couplingFlow Λ.stepParams S.β u).1 := by
    show clusterRange (S.tower.stage u).coupling = _
    rw [show (S.tower.stage u).coupling = _ from hst.coupling_eq]
    rfl
  have hap : SeparatedWeights (R := (S.tower.stage u).toStepSetup) (n := S.sideAtLevel (u + 1)) J
      (fun i => S.weight i _) (S.data.separation Λ.stepParams.side u) := by
    refine ⟨fun i _ => ?_, fun i _ => ?_, ?_, hfarD.2, fun i _ j _ hij Y hY Y' hY' => ?_⟩
    · exact (weightNorm_congr (fun m => S.weight i m) hτ hside').le.trans (Hs S u hus i).1
    · have h2 := (hP Λ.stepParams.side hodd Λ.k S.data (u + 1) h1 i).2 (S.supAdmissible.exists_ne_zero i)
      have h3 : (weightSupportSites Λ.stepParams.side (u + 1) (S.sideAtLevel (u + 1))
          (S.weight i (fineSide Λ.stepParams.side (u + 1) (S.sideAtLevel (u + 1))))).card =
          (S.data.supportSites Λ.stepParams.side (u + 1) i).card :=
        card_weightSupportSites_congr (fun m => S.weight i m) (u + 1) (sideAtLevel_eq_levelSide S (u + 1))
      show (weightSupportSites Λ.stepParams.side ((S.tower.stage u).depth + 1) (S.sideAtLevel (u + 1)) _).Nonempty
      rw [hsAbove i, ← Finset.card_pos, h3, Finset.card_pos]
      exact h2
    · rw [hr]
      exact hfarD.1
    · have hY2 : Y ∈ thickening 2 (weightSupportSites Λ.stepParams.side (u + 1) (S.sideAtLevel (u + 1))
          (S.weight i (fineSide Λ.stepParams.side (u + 1) (S.sideAtLevel (u + 1))))) := by
        rw [← hsAbove i]
        exact hY
      have hY2' : Y' ∈ thickening 2 (weightSupportSites Λ.stepParams.side (u + 1) (S.sideAtLevel (u + 1))
          (S.weight j (fineSide Λ.stepParams.side (u + 1) (S.sideAtLevel (u + 1))))) := by
        rw [← hsAbove j]
        exact hY'
      exact separation_le_supDist S.data Λ.stepParams.side u (sideAtLevel_eq_levelSide S (u + 1)) hij hY2 hY2'
  have hblock : IsBlockTorusSide Λ.stepParams (S.sideAtLevel (u + 1)) := by
    rw [sideAtLevel_eq_levelSide]
    exact isBlockTorusSide_levelSide S hn3 _
  have hgr := ((Hg S.β S.tower (scoredTower S) (u + 1) rfl (scoredTower_followsFlow S h1)
    (couplingsAboveFloor_of_le S h1)).2 (S.sideAtLevel (u + 1)) hblock).2 u (Nat.lt_succ_self u)
  have hup := fun i => (Hm S.β S.tower (scoredTower S) (u + 1) rfl (scoredTower_followsFlow S h1)
    (couplingsAboveFloor_of_le S h1) (fineFunctionOf S i) u (Nat.le_succ u)
    (S.sideAtLevel (u + 1)) hblock).2.2 (Nat.lt_succ_self u)
  have down := (hLD Λ.stepParams hfit hlam S.tower S.isCutoff S.marksMeasurable S.β S.coeff).1
  have hon := htab.onFamily
  have hrow : (S.tower.stage u).toStepSetup.HasExpansions := hon.isStep.1
  have hbl : IsBlockTorusSide (S.tower.stage u).toStepSetup.params (S.sideAtLevel (u + 1) * Λ.stepParams.side) := by
    rw [hside']
    exact isBlockTorusSide_levelSide S hn3 u
  have hnn : ∀ (W : TorusField (S.sideAtLevel (u + 1) * Λ.stepParams.side))
      (Yt : Finset (TorusSite (S.sideAtLevel (u + 1) * Λ.stepParams.side)))
      (ωt : Yt → (S.tower.stage u).toStepSetup.labels.Ω),
      IsHullState (S.tower.stage u).toStepSetup.params (S.tower.stage u).toStepSetup.range W Yt →
      0 ≤ (S.tower.stage u).toStepSetup.labelWeight (S.sideAtLevel (u + 1) * Λ.stepParams.side) W Yt ωt :=
    fun W Yt ωt h => hrow.2.nonneg _ hbl W Yt ωt h
  have hs0 : ∀ ω, 0 ≤ (S.resp (u + 1)).score ω := (stageOnFlow_at S h1).onFamily.admissible.price.nonneg
  have hss : (S.resp (u + 1)).score =
      coarseLabelScore (L := Λ.stepParams.side) (S.resp u).responseParams.s₁ (S.resp u).score :=
    eq_of_heq (resp_succ_fields S h1).2.2
  have hch : 0 ≤ Λ.table.gasRate := by
    unfold ParameterAssignment.gasRate ParameterAssignment.κ₁
    have := hD.cE_pos
    have := hD.κ_pos
    have := hD.σ_pos
    positivity
  have hC₀ : 0 ≤ Λ.response.C₀ := by
    have h3 := htab.admissible.params_admissible
    rw [hAK] at h3
    have h4 := h3.C₀_eq
    have h5 := h3.N₀_nonneg
    have h6 := h3.Kc_ge
    have ha : 1 ≤ (S.tower.stage u).toStepSetup.params.coupling := by
      rw [hon.params_eq]
      exact hD.a_ge
    rw [h4]
    linarith
  filter_upwards [ae_sampleAtLevel S down (u + 1) h1 hgr, ae_sampleAtLevel S down (u + 1) h1 (ae_all_iff.2 hup)]
    with w hgw huw
  obtain ⟨x, hx⟩ : ∃ x, x = S.sampleAtLevel (u + 1) h1 w := ⟨_, rfl⟩
  rw [← hx] at hgw huw
  have hb := (Hf (S.tower.stage u).toStepSetup (S.resp u) hAK htab (S.sideAtLevel (u + 1))
    (hotCaseGround (S.tower.stage u).toStepSetup x.2.2.1 (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2) hgw
    (Fin Λ.k) J (fun i => S.weight i _) (S.data.separation Λ.stepParams.side u) hJ hap).2
  have hmean : variableMean u J S w = caseMean (S.tower.stage u).toStepSetup
      (hotCoreSites (S.tower.stage u).toStepSetup x.2.2.1) x.2.2.1
      (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2
      (fun W Yt ωt bad b => ∏ i ∈ J, centeredSupportResponse (S.resp u) x.2.2.1 (S.weight i _) W Yt ωt bad b) := by
    unfold variableMean
    rw [dif_pos h1, ← hx]
    show caseMean (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup x.2.2.1) x.2.2.1
      (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2 (S.variableCaseProduct u J x.2.2.1) = _
    have e0 := caseMean_congr_baseChoices (R := (S.tower.stage u).toStepSetup) (n := S.sideAtLevel (u + 1))
      (F' := S.variableCaseProduct u J x.2.2.1)
      (F := fun W Yt ωt bad b =>
        ∏ i ∈ J, liveCaseFunction (centeredSupportResponse (S.resp u) x.2.2.1 (S.weight i _)) W Yt ωt bad b)
      (fun W Yt ωt bad b hb => by
        show ∏ i ∈ J, liveCaseFunction (centeredSupportResponse (S.resp u) x.2.2.1 (S.weight i _)) W Yt ωt bad
          (clampBasesToBlocks b) = _
        rw [clampBasesToBlocks_of_isBaseChoice (Finset.mem_filter.1 hb).2])
      (hotCoreSites (S.tower.stage u).toStepSetup x.2.2.1) x.2.2.1
      (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2
    exact e0.trans ((congrArg (caseMean (S.tower.stage u).toStepSetup
      (hotCoreSites (S.tower.stage u).toStepSetup x.2.2.1) x.2.2.1
      (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2)
      (prod_liveCaseFunction hJ (fun i => centeredSupportResponse (S.resp u) x.2.2.1 (S.weight i _)))).trans
        (caseMean_liveCaseFunction hnn _ _ _ _))
  have hresp : ∀ i, responseAtLevel (u + 1) i S w = caseMean (S.tower.stage u).toStepSetup
      (hotCoreSites (S.tower.stage u).toStepSetup x.2.2.1) x.2.2.1
      (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2
      (centeredSupportResponse (S.resp u) x.2.2.1 (S.weight i _)) := fun i => by
    have e := huw i
    rw [scoredTower_setup S h0, fittedResponse_eq_supportTotal S i h1] at e
    unfold responseAtLevel
    rw [dif_pos h1]
    show S.supportTotal (u + 1) (S.sideAtLevel (u + 1)) i
      (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) (S.sampleAtLevel (u + 1) h1 w)) = _
    rw [← hx]
    exact e.symm
  have hscore : ∀ i, meanScoreAtLevel (u + 1) i S w =
      meanSiteScore (coarseLabelScore (L := Λ.stepParams.side) (S.resp u).responseParams.s₁ (S.resp u).score)
        (weightSupportSites Λ.stepParams.side ((S.tower.stage u).depth + 1) (S.sideAtLevel (u + 1)) (S.weight i _))
        (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2.1
        (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2.2 := fun i => by
    unfold meanScoreAtLevel
    rw [dif_pos h1, hsAbove i, ← hss]
    show meanSiteScore (S.resp (u + 1)).score _
      (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) (S.sampleAtLevel (u + 1) h1 w)).2.1
      (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) (S.sampleAtLevel (u + 1) h1 w)).2.2 = _
    rw [← hx]
    rfl
  have hNnn : ∀ i, 0 ≤ meanScoreAtLevel (u + 1) i S w := fun i => by
    unfold meanScoreAtLevel
    rw [dif_pos h1]
    exact meanSiteScore_nonneg hs0 _ _ _
  have hmaj : ∀ i, upperMajorant (S.resp u)
      (hotCaseGround (S.tower.stage u).toStepSetup x.2.2.1 (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2)
      (S.weight i _) =
      4 * (Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ)) *
        meanScoreAtLevel (u + 1) i S w := fun i => by
    rw [hscore i]
    unfold upperMajorant lowerSizeConst lowerSites upperSites
    rw [hAK]
    exact congrArg₂ (· * ·)
      (congrArg (4 * ·) (congrArg (Λ.response.C₀ * ·) (congrArg (Nat.cast (R := ℝ)) (hcard i)))) rfl
  have hsum : totalLowerSites (R := (S.tower.stage u).toStepSetup) (n := S.sideAtLevel (u + 1)) J
      (fun i => S.weight i _) = ∑ i ∈ J, ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) :=
    Finset.sum_congr rfl fun i _ => congrArg (Nat.cast (R := ℝ)) (hcard i)
  have hprod : ∏ i ∈ J, upperMajorant (S.resp u)
      (hotCaseGround (S.tower.stage u).toStepSetup x.2.2.1 (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2)
      (S.weight i _) =
      (∏ i ∈ J, (4 * (Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ)))) *
        ∏ i ∈ J, meanScoreAtLevel (u + 1) i S w := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => hmaj i
  rw [hmean, Finset.prod_congr rfl fun i _ => hresp i]
  refine (hb.trans ?_)
  rw [hsum, hprod]
  unfold MomentPoint.stepErrorBound
  have hp8 : (J.card : ℝ) ≤ 8 := by
    have h2 : J.card ≤ 8 := (Finset.card_le_univ J).trans (by simpa using hk)
    exact_mod_cast h2
  have hp0 : (0 : ℝ) ≤ J.card := Nat.cast_nonneg _
  have hp2 : (J.card : ℝ) ^ 2 ≤ 64 := by nlinarith
  have hx1 : 0 ≤ (S.tower.stage u).toStepSetup.coupling := le_trans (by linarith) hon.le_coupling
  have hE0 : Real.exp (-(7 * Λ.table.gasRate * (S.tower.stage u).toStepSetup.coupling)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have : 0 ≤ Λ.table.gasRate * (S.tower.stage u).toStepSetup.coupling := mul_nonneg hch hx1
      linarith)
  have hE1 : Real.exp (2 * (J.card : ℝ) * Real.exp (-(7 * Λ.table.gasRate * (S.tower.stage u).toStepSetup.coupling))) ≤
      Real.exp 16 := by
    refine Real.exp_le_exp.2 ?_
    have h0' : 0 ≤ Real.exp (-(7 * Λ.table.gasRate * (S.tower.stage u).toStepSetup.coupling)) := (Real.exp_pos _).le
    nlinarith
  have hrt : 0 ≤ Λ.stepParams.rt := hfit.rt_pos.le
  have hE2 : Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 6)) ≤
      Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 7)) := by
    refine Real.exp_le_exp.2 ?_
    have h3 : 0 ≤ Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) := mul_nonneg hrt (Nat.cast_nonneg _)
    norm_num
    linarith
  obtain ⟨Sm, hSm⟩ : ∃ Sm, Sm = ∑ i ∈ J, ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) := ⟨_, rfl⟩
  obtain ⟨Kp, hKp⟩ : ∃ Kp, Kp = ∏ i ∈ J, (4 * (Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ))) :=
    ⟨_, rfl⟩
  obtain ⟨Nn, hNn⟩ : ∃ Nn, Nn = ∏ i ∈ J, meanScoreAtLevel (u + 1) i S w := ⟨_, rfl⟩
  have hSm0 : 0 ≤ Sm := hSm ▸ Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have hKp0 : 0 ≤ Kp := hKp ▸ Finset.prod_nonneg fun i _ => by positivity
  have hNn0 : 0 ≤ Nn := hNn ▸ Finset.prod_nonneg fun i _ => hNnn i
  rw [← hSm, ← hKp, ← hNn]
  have hq : (J.card : ℝ) ^ 2 *
      Real.exp (2 * (J.card : ℝ) * Real.exp (-(7 * Λ.table.gasRate * (S.tower.stage u).toStepSetup.coupling))) *
      Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 6)) ≤
      64 * Real.exp 16 * Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 7)) := by
    have := Real.exp_pos (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 6))
    gcongr
  have hw0 : 0 ≤ Cf * (Sm * (Kp * Nn)) := mul_nonneg hCf (mul_nonneg hSm0 (mul_nonneg hKp0 hNn0))
  have := mul_le_mul_of_nonneg_right hq hw0
  calc _ = (J.card : ℝ) ^ 2 *
        Real.exp (2 * (J.card : ℝ) * Real.exp (-(7 * Λ.table.gasRate * (S.tower.stage u).toStepSetup.coupling))) *
        Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 6)) * (Cf * (Sm * (Kp * Nn))) := by
        ring
    _ ≤ 64 * Real.exp 16 * Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 7)) *
        (Cf * (Sm * (Kp * Nn))) := this
    _ = _ := by ring
end YangMills.Construction.MomentLaw
end

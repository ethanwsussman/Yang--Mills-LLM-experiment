import YangMills.Construction.LawByMomentsOfTheFlow.VariablesOfAPointSplitProof
import YangMills.Construction.LawByMomentsOfTheFlow.ColdLawOfAGoodStateProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open FreeEnergies WeightedResponses ResponseInTheExpansion StepSettings TorusLumps ClusterExpansionOfAStep RenormalizationStepParameters LevelTestFunctions
section Transport
private theorem fineWeight_heq (f : FinePlaquetteFunction) {m m' : ℕ} (h : m = m') :
    HEq (fineWeight f m) (fineWeight f m') := by
  subst h
  rfl
private theorem setup_with_params {R : StepSetup} (A : ResponseSetup R) {K : ResponseParameters}
    (h : A.responseParams = K) : ({ A with responseParams := K } : ResponseSetup R) = A := by
  subst h
  rfl
private theorem supportSites_depth {L : ℕ} [NeZero L] (w : ∀ m : ℕ, PlaquetteWeight m) {t s : ℕ} (n : ℕ)
    [NeZero n] (h : t = s) :
    weightSupportSites L t n (w (fineSide L t n)) = weightSupportSites L s n (w (fineSide L s n)) := by apply _root_.YangMills.SharedProofs.p57791 <;> assumption
private theorem weightNorm_depth {L : ℕ} (w : ∀ m : ℕ, PlaquetteWeight m) {t s : ℕ} (n : ℕ) (h : t = s) :
    weightNorm L t (w (fineSide L t n)) = weightNorm L s (w (fineSide L s n)) := by
  subst h
  rfl
end Transport
section Parameters
private theorem forAllParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁)
    (h₂ : ForAllParameters Q₂) : ForAllParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_mono {Q₁ Q₂ : MomentParameters → Prop} (h : ∀ Λ, Q₁ Λ → Q₂ Λ)
    (h₁ : ForAllParameters Q₁) : ForAllParameters Q₂ := by apply _root_.YangMills.SharedProofs.p432 <;> assumption
private theorem forAllParameters_admissible : ForAllParameters fun Λ => Λ.table.Admissible := by apply _root_.YangMills.SharedProofs.p23915 <;> assumption
private theorem forAllParameters_of_response {P : ParameterAssignment → ResponseParameters → ℝ → Prop}
    (h : AtResponseParameters P) : ForAllParameters fun Λ => P Λ.table Λ.response Λ.floor := by apply _root_.YangMills.SharedProofs.p38170 <;> assumption
end Parameters
section Point
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private def scoredTower : ScoredStageTower S.tower :=
  ⟨Λ.response, fun u => { S.resp u with responseParams := Λ.response }⟩
private theorem stageOnFlow {u : ℕ} (hu : u ≤ S.data.windowLevel) :
    StageOnFlow Λ.table Λ.response Λ.floor S.β u (⟨S.tower.stage u, S.resp u⟩ : StageWithResponse Λ.stepParams) := by apply _root_.YangMills.SharedProofs.p21183 <;> assumption
private theorem scoredTower_setup {u : ℕ} (hu : u ≤ S.data.windowLevel) : (scoredTower S).setup u = S.resp u :=
  setup_with_params _ (stageOnFlow S hu).params_eq
private theorem scoredTower_followsFlow {tp : ℕ} (htp : tp ≤ S.data.windowLevel) :
    (scoredTower S).FollowsFlow S.β tp := by apply _root_.YangMills.DeltaSharedProofs.p502274 <;> assumption
private theorem couplingsAboveFloor {t : ℕ} (ht : t ≤ S.data.windowLevel) :
    CouplingsAboveFloor (Λ.table.stepParameters Λ.floor) S.β t := fun j hj => by
  have h := stageOnFlow S (hj.trans ht)
  exact le_of_le_of_eq h.onFamily.onFamily.le_coupling h.coupling_eq
private theorem isBlockTorusSide_levelSide (hn : 3 ≤ Λ.stepParams.n₀) (t : ℕ) :
    IsBlockTorusSide Λ.stepParams (S.levelSide t) := by apply _root_.YangMills.SharedProofs.p33093 <;> assumption
private theorem supportTotal_le_of_live (hn : 3 ≤ Λ.stepParams.n₀) (ha : 0 ≤ Λ.stepParams.coupling) {u : ℕ}
    (hu : u ≤ S.data.windowLevel) (i : Fin Λ.k)
    (hsize : weightNorm Λ.stepParams.side u (S.weight i (fineSide Λ.stepParams.side u (S.levelSide u))) ≤ 1)
    (q : StageState S.tower u (S.levelSide u))
    (hlive : IsLiveState Λ.stepParams (S.tower.stage u).coupling (S.tower.stage u).labelWeight q.1 q.2.1 q.2.2) :
    |S.supportTotal u (S.levelSide u) i q| ≤
      Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) * S.meanScore u (S.levelSide u) i q := by
  classical
  have hst := stageOnFlow S hu
  have hτ : (S.tower.stage u).depth = u := hst.depth_eq
  have hK : (S.resp u).responseParams = Λ.response := hst.params_eq
  have hres : (S.resp u).IsAdmissible := hst.onFamily.admissible
  have hfit := hres.params_admissible
  rw [hK] at hfit
  have hC₀ : 1 ≤ Λ.response.C₀ := by
    have h1 := hfit.C₀_eq
    have h2 := hfit.Kc_ge
    have h3 := hfit.N₀_nonneg
    rw [h1]
    linarith
  have hsites : weightSupportSites Λ.stepParams.side (S.tower.stage u).depth (S.levelSide u)
      (S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth (S.levelSide u))) =
      S.data.supportSites Λ.stepParams.side u i :=
    supportSites_depth (fun m => S.weight i m) _ hτ
  have hsz : weightNorm Λ.stepParams.side (S.tower.stage u).depth
      (S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth (S.levelSide u))) ≤ 1 := by
    rw [weightNorm_depth (fun m => S.weight i m) _ hτ]
    exact hsize
  have hs0 : ∀ y, 0 ≤ siteScore (S.resp u).score q.2.1 q.2.2 y := fun y => by
    unfold WeightedResponses.siteScore
    split_ifs
    · exact hres.price.nonneg _
    · exact le_rfl
  have hterm : ∀ y, |centeredHullResponse (S.resp u).cold (S.resp u).hull (S.levelSide u) y q.1 q.2.1 q.2.2
      (S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth (S.levelSide u)))| ≤
      Λ.response.C₀ + siteScore (S.resp u).score q.2.1 q.2.2 y := fun y => by
    have h := hres.bounds.size_hull (S.levelSide u) (isBlockTorusSide_levelSide S hn u) y q.1 q.2.1 q.2.2 hlive
      (S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth (S.levelSide u)))
    rw [hK] at h
    refine h.trans ?_
    have hc : 0 ≤ Λ.response.C₀ + siteScore (S.resp u).score q.2.1 q.2.2 y := by linarith [hs0 y]
    exact mul_le_of_le_one_right hc hsz
  have hF : S.supportTotal u (S.levelSide u) i q = ∑ y ∈ S.data.supportSites Λ.stepParams.side u i,
      centeredHullResponse (S.resp u).cold (S.resp u).hull (S.levelSide u) y q.1 q.2.1 q.2.2
        (S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth (S.levelSide u))) := by
    rw [← hsites]
    rfl
  have hN : S.meanScore u (S.levelSide u) i q = 1 + ((S.data.supportSites Λ.stepParams.side u i).card : ℝ)⁻¹ *
      ∑ y ∈ S.data.supportSites Λ.stepParams.side u i, siteScore (S.resp u).score q.2.1 q.2.2 y := rfl
  rw [hF, hN]
  have hsum : |∑ y ∈ S.data.supportSites Λ.stepParams.side u i,
      centeredHullResponse (S.resp u).cold (S.resp u).hull (S.levelSide u) y q.1 q.2.1 q.2.2
        (S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth (S.levelSide u)))| ≤
      Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) +
        ∑ y ∈ S.data.supportSites Λ.stepParams.side u i, siteScore (S.resp u).score q.2.1 q.2.2 y := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun y _ => hterm y).trans (le_of_eq ?_))
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine hsum.trans ?_
  set c : ℝ := ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) with hc
  set sc : ℝ := ∑ y ∈ S.data.supportSites Λ.stepParams.side u i, siteScore (S.resp u).score q.2.1 q.2.2 y with hsc
  have hsc0 : 0 ≤ sc := Finset.sum_nonneg fun y _ => hs0 y
  by_cases hc0 : c = 0
  · have hempty : S.data.supportSites Λ.stepParams.side u i = ∅ := by
      have h0 : ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) = 0 := hc0
      rw [← Finset.card_eq_zero]
      exact_mod_cast h0
    have : sc = 0 := by rw [hsc, hempty, Finset.sum_empty]
    rw [hc0, this]
    simp
  · have e : Λ.response.C₀ * c * (1 + c⁻¹ * sc) = Λ.response.C₀ * c + Λ.response.C₀ * sc := by
      field_simp
    rw [e]
    nlinarith
end Point
theorem supportTotalBoundedByScores_of (h₁ : weightsSitesBelowScaleStatement)
    (h₂ : flowStatesAreGroundsStatement) : supportTotalBoundedByScoresStatement := by
  unfold MomentLaw.weightsSitesBelowScaleStatement at h₁
  unfold FreeEnergies.flowStatesAreGroundsStatement at h₂
  unfold MomentLaw.supportTotalBoundedByScoresStatement
  unfold MomentLaw.ForAllPoints at h₁ ⊢
  refine forAllParameters_mono ?_
    (forAllParameters_and h₁ (forAllParameters_and (forAllParameters_of_response h₂) forAllParameters_admissible))
  rintro Λ ⟨⟨C, _, _, _, _, HW⟩, HG, hD⟩
  refine ⟨fun _ => 0, 1, Λ.floor, one_pos, le_rfl, fun S _ => ?_⟩
  have hn : 3 ≤ Λ.stepParams.n₀ := le_trans (by norm_num) hD.n₀_ge
  have ha : 0 ≤ Λ.stepParams.coupling := le_trans zero_le_one hD.a_ge
  have hts : S.lastSeparated ≤ S.data.scaleLevel :=
    @Nat.findGreatest_le (S.data.SeparatedBelow Λ.stepParams S.β) (fun _ => Classical.propDecidable _)
      S.data.scaleLevel
  have htK : S.lastSeparated ≤ S.data.windowLevel := hts.trans S.supAdmissible.scaleLevel_le
  have hlive := (HG S.β S.tower (scoredTower S) S.data.windowLevel rfl (scoredTower_followsFlow S le_rfl)
    (couplingsAboveFloor S le_rfl)).2 (S.levelSide S.lastSeparated) (isBlockTorusSide_levelSide S hn S.lastSeparated)
  filter_upwards [hlive.1 S.lastSeparated htK] with w hw i
  exact supportTotal_le_of_live S hn ha htK i (HW S S.lastSeparated hts i).1 _ hw
end YangMills.Construction.MomentLaw
end

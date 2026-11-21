import YangMills.Construction.LawByMomentsOfTheFlow.ABoundAtClearStatesInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheResponsesInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.ResponsesAtTheFieldOneAddUp
import YangMills.Construction.LawByMomentsOfTheFlow.SizesAlongTheTelescopeProof
import YangMills.Construction.LawByMomentsOfTheFlow.TelescopeOfAPoint
import YangMills.Construction.LawOnABoxOfTheFlow.DrawsHaveTheirBases
import YangMills.Construction.ResponseInTheExpansion.MomentsAlongTheLevelsProof
import YangMills.Construction.ResponseInTheExpansion.WilsonWeightHasTheExpansionOfTheResponseProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps StepSettings StepGas RenormalizationStepParameters ClusterExpansionOfAStep WeightedResponses ResponseInTheExpansion LevelTestFunctions BoxEvents
section SupportSites
private theorem weight_heq (w : (m : ℕ) → PlaquetteWeight m) {m m' : ℕ} (h : m = m') : HEq (w m) (w m') := by
  subst h
  rfl
private theorem supportSites_congr {L : ℕ} [NeZero L] (w : (m : ℕ) → PlaquetteWeight m) {t s : ℕ} (n : ℕ) [NeZero n] (h : t = s) :
    weightSupportSites L t n (w (fineSide L t n)) = weightSupportSites L s n (w (fineSide L s n)) := by apply _root_.YangMills.SharedProofs.p57791 <;> assumption
private theorem mem_supportSites_of_blockMean_ne_zero (L : ℕ) [NeZero L] : ∀ (t n : ℕ) [NeZero n] (y : TorusSite n)
    (h : PlaquetteWeight (fineSide L t n)), blockMean L t n y h ≠ 0 → y ∈ weightSupportSites L t n h := by apply _root_.YangMills.SharedProofs.p53316 <;> assumption
private theorem sum_supportSites_blockMean {L : ℕ} [NeZero L] (w : (m : ℕ) → PlaquetteWeight m) {t u : ℕ} (h : t = u) (n : ℕ) [NeZero n]
    (G : TorusSite n → ℝ) :
    ∑ Y ∈ weightSupportSites L (t + 1) n (w (fineSide L (t + 1) n)), blockMean L (t + 1) n Y (w (fineSide L (t + 1) n)) * G Y =
      ∑ Y : TorusSite n, blockMean L (u + 1) n Y (w (fineSide L (u + 1) n)) * G Y := by
  subst h
  refine Finset.sum_subset (Finset.subset_univ _) fun Y _ hY => ?_
  by_cases h0 : blockMean L (t + 1) n Y (w (fineSide L (t + 1) n)) = 0
  · rw [h0, zero_mul]
  · exact absurd (mem_supportSites_of_blockMean_ne_zero L _ n Y _ h0) hY
private theorem plaquetteEnergyOf_trivialField {m : ℕ} (p : TorusPlaquette m) : plaquetteEnergyOf (trivialField m) p = 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.plaquetteEnergyOf_trivialField <;> assumption
private theorem siteResponse_trivialField {m : ℕ} [NeZero m] (y : TorusSite m) (h : PlaquetteWeight m) :
    siteResponse y (trivialField m) h = 0 := by
  unfold siteResponse
  simp [plaquetteEnergyOf_trivialField]
private theorem sum_supportSites_siteResponse_sub (L : ℕ) [NeZero L] {m : ℕ} [NeZero m] (h : PlaquetteWeight m) (W : TorusField m) :
    ∑ y ∈ weightSupportSites L 0 m h, (siteResponse y W h - siteResponse y (trivialField m) h) = curvatureObservable h W := by apply _root_.YangMills.SharedProofs.p55288 <;> assumption
private theorem cold_heq_of_nextStage {ℓ : StepParameters} (hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup) (lam x'' : ℝ)
    (c c' : ChainStage ℓ) (A : ResponseSetup c.toStepSetup) (A' : ResponseSetup c'.toStepSetup) (z : StageWithResponse ℓ)
    (h : (⟨c, A⟩ : StageWithResponse ℓ) = z)
    (h' : (⟨c', A'⟩ : StageWithResponse ℓ) = nextStageWithResponse hL lam x'' z) : HEq A'.cold A.coldStep := by
  subst h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h'
  cases h2
  exact HEq.rfl
end SupportSites
section Samples
variable {ℓ : StepParameters}
private theorem sampleBelow_fst (u : ℕ) : ∀ (d n : ℕ) (w₁ : MarkedSample ℓ (u + 1 + d) n) (w₂ : MarkedSample ℓ (u + (d + 1)) n),
    HEq w₁ w₂ →
    fineSide ℓ.side d n * ℓ.side = fineSide ℓ.side (d + 1) n ∧
      HEq (sampleBelow ℓ (u + 1) d n w₁).1 (sampleBelow ℓ u (d + 1) n w₂) := by apply _root_.YangMills.SharedProofs.p2695 <;> assumption
private theorem sample_cast_heq {K K' n : ℕ} (h : K = K') (w : MarkedSample ℓ K n) :
    HEq (h ▸ w : MarkedSample ℓ K' n) w := by
  subst h
  exact HEq.rfl
private theorem sampleBelow_cast (u K n : ℕ) (w : MarkedSample ℓ K n) {d₁ d₂ : ℕ} (h₁ : K = u + 1 + d₁) (h₂ : K = u + d₂)
    (hd : d₂ = d₁ + 1) :
    fineSide ℓ.side d₁ n * ℓ.side = fineSide ℓ.side d₂ n ∧
      HEq (sampleBelow ℓ (u + 1) d₁ n (h₁ ▸ w)).1 (sampleBelow ℓ u d₂ n (h₂ ▸ w)) := by
  subst hd
  exact sampleBelow_fst u d₁ n _ _ ((sample_cast_heq h₁ w).trans (sample_cast_heq h₂ w).symm)
private theorem sample_congr {s : ℕ} (Φ : (n : ℕ) → [NeZero n] → MarkedSample ℓ s n → ℝ) {n m : ℕ} [NeZero n] [NeZero m]
    (e : n = m) {x : MarkedSample ℓ s n} {y : MarkedSample ℓ s m} (h : HEq x y) : Φ n x = Φ m y := by
  subst e
  rw [eq_of_heq h]
private theorem sample_holds {s : ℕ} (Φ : (n : ℕ) → [NeZero n] → MarkedSample ℓ s n → Prop) {n m : ℕ} [NeZero n] [NeZero m]
    (e : n = m) {x : MarkedSample ℓ s n} {y : MarkedSample ℓ s m} (h : HEq x y) (hy : Φ m y) : Φ n x := by
  subst e
  rwa [eq_of_heq h]
private theorem stageState_fst (T : StageTower ℓ) (s n : ℕ) [NeZero n] (x : MarkedSample ℓ s n) :
    (stageState T s n x).1 = topField ℓ s n x := by apply _root_.YangMills.SharedProofs.p2480 <;> assumption
end Samples
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem onFlow_at {u : ℕ} (hu : u ≤ S.data.windowLevel) :
    StageOnFlow Λ.table Λ.response Λ.floor S.β u (⟨S.tower.stage u, S.resp u⟩ : StageWithResponse Λ.stepParams) := by apply _root_.YangMills.SharedProofs.p21183 <;> assumption
private theorem depth_eq_of_le {u : ℕ} (hu : u ≤ S.data.windowLevel) : (S.tower.stage u).depth = u :=
  (onFlow_at S hu).depth_eq
private theorem cold_succ {u : ℕ} (hu : u + 1 ≤ S.data.windowLevel) : HEq (S.resp (u + 1)).cold (S.resp u).coldStep :=
  cold_heq_of_nextStage S.labelFacts Λ.table.lam _ _ _ _ _ _ (S.stage_eq u (by omega)) (S.stage_eq (u + 1) hu)
private theorem kappa_congr (u : ℕ) (i : Fin Λ.k) {n n' : ℕ} [NeZero n] [NeZero n'] (h : n = n') :
    S.kappa u n i = S.kappa u n' i := by
  subst h
  rfl
private theorem sideAtLevel_eq (u : ℕ) :
    S.sideAtLevel u = S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - u) := by apply _root_.YangMills.DeltaSharedProofs.p7007 <;> assumption
private theorem n₀_le_sideAtLevel (u : ℕ) : Λ.stepParams.n₀ ≤ S.sideAtLevel u := by
  have hL : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  rw [sideAtLevel_eq]
  exact (Nat.le_mul_of_pos_left _ hL).trans (S.side_le.trans (Nat.le_mul_of_pos_right _ (pow_pos hL _)))
private theorem isBlockTorusSide_sideAtLevel (hn : 3 ≤ Λ.stepParams.n₀) (u : ℕ) :
    IsBlockTorusSide Λ.stepParams (S.sideAtLevel u) := by apply _root_.YangMills.SharedProofs.p22950 <;> assumption
private theorem sampleAtLevel_fst (u : ℕ) (h1 : u + 1 ≤ S.data.windowLevel) (h0 : u ≤ S.data.windowLevel)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    S.sideAtLevel (u + 1) * Λ.stepParams.side = S.sideAtLevel u ∧
      HEq (S.sampleAtLevel (u + 1) h1 w).1 (S.sampleAtLevel u h0 w) :=
  sampleBelow_cast u S.data.windowLevel (S.data.period Λ.stepParams.side) w (Nat.add_sub_of_le h1).symm
    (Nat.add_sub_of_le h0).symm (by omega)
private theorem map_sampleAtLevel (hB : sampleBelowLawStatement) (hFit : Λ.stepParams.Admissible) (u : ℕ)
    (hu : u ≤ S.data.windowLevel) :
    Measurable (S.sampleAtLevel u hu) ∧
      (S.law S.data.windowLevel (S.data.period Λ.stepParams.side)).map (S.sampleAtLevel u hu) = S.law u (S.sideAtLevel u) := by apply _root_.YangMills.SharedProofs.p20473 <;> assumption
private theorem kappa_zero (n : ℕ) [NeZero n] (i : Fin Λ.k) : S.kappa 0 n i = 0 := by
  have ht0 : (S.tower.stage 0).depth = 0 := depth_eq_of_le S (Nat.zero_le _)
  refine Finset.sum_eq_zero fun y _ => ?_
  have e := S.cold_zero n y (trivialField n) (S.weight i n) (S.weight i _)
    (weight_heq _ (by show n = fineSide _ (S.tower.stage 0).depth n; rw [ht0]; rfl))
  exact e.trans (siteResponse_trivialField y _)
abbrev _root_.YangMills.SharedProofs.p41593 := @kappa_zero
private def StepIdentity : Prop :=
  ∀ u < S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n →
    ∀ f : PlaquetteWeight (fineSide Λ.stepParams.side ((S.tower.stage u).depth + 1) n),
      ∑ Y ∈ weightSupportSites Λ.stepParams.side ((S.tower.stage u).depth + 1) n f, (S.resp u).coldStep n Y (trivialField n) f =
        ∑ y ∈ weightSupportSites Λ.stepParams.side (S.tower.stage u).depth (n * Λ.stepParams.side) f,
            (S.resp u).cold (n * Λ.stepParams.side) y (trivialField (n * Λ.stepParams.side)) f +
          caseMean (S.tower.stage u).toStepSetup ∅ (trivialField n) (emptyCoarseState _)
            (supportResponseSum (S.resp u) (trivialField n) f)
private theorem kappa_succ (hadd : StepIdentity S) {u : ℕ} (hu : u + 1 ≤ S.data.windowLevel) (n : ℕ) [NeZero n]
    (hn : Λ.stepParams.n₀ ≤ n) (i : Fin Λ.k) :
    S.kappa (u + 1) n i = S.kappa u (n * Λ.stepParams.side) i + stepMeanShift (n := n) (S.resp u) (S.weight i _) := by
  have hu' : u ≤ S.data.windowLevel := by omega
  have ht := depth_eq_of_le S hu'
  have hP : (S.resp (u + 1)).cold = (S.resp u).coldStep := eq_of_heq (cold_succ S hu)
  have h := hadd u (by omega) n hn (S.weight i _)
  have hk1 : S.kappa (u + 1) n i = ∑ Y ∈ weightSupportSites Λ.stepParams.side ((S.tower.stage u).depth + 1) n (S.weight i _),
      (S.resp u).coldStep n Y (trivialField n) (S.weight i _) := by
    unfold MomentPoint.kappa MomentPoint.supportAt
    rw [hP]
    exact Finset.sum_congr (supportSites_congr (S.weight i) n (by rw [ht])).symm fun _ _ => rfl
  have hk0 : S.kappa u (n * Λ.stepParams.side) i =
      ∑ y ∈ weightSupportSites Λ.stepParams.side (S.tower.stage u).depth (n * Λ.stepParams.side) (S.weight i _),
        (S.resp u).cold (n * Λ.stepParams.side) y (trivialField (n * Λ.stepParams.side)) (S.weight i _) := by
    unfold MomentPoint.kappa MomentPoint.supportAt
    exact Finset.sum_congr (supportSites_congr (S.weight i) _ ht).symm fun _ _ => rfl
  rw [hk0]
  exact hk1.trans h
private theorem curvatureObservable_eq_responseAtLevel_zero (i : Fin Λ.k)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    curvatureObservable (S.weight i (S.sideAtLevel 0)) (S.sampleAtLevel 0 (Nat.zero_le _) w) = responseAtLevel 0 i S w := by
  have ht0 : (S.tower.stage 0).depth = 0 := depth_eq_of_le S (Nat.zero_le _)
  unfold responseAtLevel
  rw [dif_pos (Nat.zero_le _)]
  unfold MomentPoint.supportTotal supportResponseTotal
  rw [← sum_supportSites_siteResponse_sub Λ.stepParams.side (S.weight i (S.sideAtLevel 0)) (S.sampleAtLevel 0 (Nat.zero_le _) w)]
  refine Finset.sum_congr (supportSites_congr (S.weight i) _ ht0.symm) fun y _ => ?_
  have hh : HEq (S.weight i (S.sideAtLevel 0))
      (S.weight i (fineSide Λ.stepParams.side (S.tower.stage 0).depth (S.sideAtLevel 0))) :=
    weight_heq _ (by show S.sideAtLevel 0 = fineSide _ (S.tower.stage 0).depth (S.sideAtLevel 0); rw [ht0]; rfl)
  unfold centeredHullResponse
  rw [S.hull_zero _ y _ _ _ _ _ hh, S.cold_zero _ y _ _ _ hh]
  rfl
private theorem telescope_sum (hadd : StepIdentity S) (i : Fin Λ.k) : ∀ (t' : ℕ) (ht : t' ≤ S.data.windowLevel)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)),
    _root_.YangMills.Construction.WeightedResponses.completedObservable S.tower S.coeff t' (S.sideAtLevel t') (S.weight i _) (S.sampleAtLevel t' ht w) - S.kappa t' (S.sideAtLevel t') i =
      responseAtLevel 0 i S w + ∑ j ∈ Finset.range t', centredStepScore j i S w := by
  intro t'
  induction t' with
  | zero =>
    intro ht w
    rw [kappa_zero, Finset.sum_range_zero, add_zero, sub_zero, ← curvatureObservable_eq_responseAtLevel_zero]
    show curvatureObservable _ _ + 0 = _
    rw [add_zero]
    rfl
  | succ t ih =>
    intro ht w
    have ht' : t ≤ S.data.windowLevel := by omega
    obtain ⟨e, hh⟩ := sampleAtLevel_fst S t ht ht' w
    have e1 : _root_.YangMills.Construction.WeightedResponses.completedObservable S.tower S.coeff (t + 1) (S.sideAtLevel (t + 1)) (S.weight i _) (S.sampleAtLevel (t + 1) ht w) =
        _root_.YangMills.Construction.WeightedResponses.completedObservable S.tower S.coeff t (S.sideAtLevel (t + 1) * Λ.stepParams.side) (S.weight i _)
            (S.sampleAtLevel (t + 1) ht w).1 +
          sourceTerm S.tower S.coeff t (S.sideAtLevel (t + 1)) (S.weight i _) (S.sampleAtLevel (t + 1) ht w) := by
      unfold _root_.YangMills.Construction.WeightedResponses.completedObservable
      show _ + (cumulativeSource S.tower S.coeff t _ _ _ + _) = _
      rw [add_assoc]
      rfl
    have e2 : _root_.YangMills.Construction.WeightedResponses.completedObservable S.tower S.coeff t (S.sideAtLevel (t + 1) * Λ.stepParams.side) (S.weight i _)
          (S.sampleAtLevel (t + 1) ht w).1 =
        _root_.YangMills.Construction.WeightedResponses.completedObservable S.tower S.coeff t (S.sideAtLevel t) (S.weight i _) (S.sampleAtLevel t ht' w) :=
      sample_congr (fun n _ y => _root_.YangMills.Construction.WeightedResponses.completedObservable S.tower S.coeff t n (S.weight i _) y) e hh
    have e3 := kappa_succ S hadd ht (S.sideAtLevel (t + 1)) (n₀_le_sideAtLevel S _) i
    have e4 := kappa_congr S t i e
    have e5 : centredStepScore t i S w =
        sourceTerm S.tower S.coeff t (S.sideAtLevel (t + 1)) (S.weight i _) (S.sampleAtLevel (t + 1) ht w) -
          stepMeanShift (n := S.sideAtLevel (t + 1)) (S.resp t) (S.weight i _) := by
      unfold centredStepScore
      rw [dif_pos ht]
    have e6 := ih ht' w
    rw [Finset.sum_range_succ, e1, e3, e5]
    rw [e2, e4]
    linarith
private theorem variableCase_eq {u : ℕ} (h1 : u + 1 ≤ S.data.windowLevel) (h0 : u ≤ S.data.windowLevel) (i : Fin Λ.k)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    centeredSupportResponse (S.resp u) (S.sampleAtLevel (u + 1) h1 w).2.2.1 (S.weight i _)
        (topField Λ.stepParams u _ (S.sampleAtLevel (u + 1) h1 w).1)
        (stageState S.tower u _ (S.sampleAtLevel (u + 1) h1 w).1).2.1 (stageState S.tower u _ (S.sampleAtLevel (u + 1) h1 w).1).2.2
        (S.sampleAtLevel (u + 1) h1 w).2.2.2 (S.sampleAtLevel (u + 1) h1 w).2.1 =
      responseAtLevel u i S w + centredStepScore u i S w := by
  obtain ⟨e, hh⟩ := sampleAtLevel_fst S u h1 h0 w
  have e1 : responseAtLevel u i S w = S.supportTotal u (S.sideAtLevel (u + 1) * Λ.stepParams.side) i
      (stageState S.tower u _ (S.sampleAtLevel (u + 1) h1 w).1) := by
    unfold responseAtLevel
    rw [dif_pos h0]
    exact (sample_congr (fun n _ y => S.supportTotal u n i (stageState S.tower u n y)) e hh).symm
  have e2 : centredStepScore u i S w =
      sourceTerm S.tower S.coeff u (S.sideAtLevel (u + 1)) (S.weight i _) (S.sampleAtLevel (u + 1) h1 w) -
        stepMeanShift (n := S.sideAtLevel (u + 1)) (S.resp u) (S.weight i _) := by
    unfold centredStepScore
    rw [dif_pos h1]
  rw [e1, e2]
  have hs := sum_supportSites_blockMean (L := Λ.stepParams.side) (S.weight i) (depth_eq_of_le S h0) (S.sideAtLevel (u + 1))
    (fun Y => blockBondScores (R := (S.tower.stage u).toStepSetup) (topField Λ.stepParams u _ (S.sampleAtLevel (u + 1) h1 w).1)
      (S.sampleAtLevel (u + 1) h1 w).2.2.1 (S.sampleAtLevel (u + 1) h1 w).2.1 Y)
  have e3 := stageState_fst S.tower u _ (S.sampleAtLevel (u + 1) h1 w).1
  unfold centeredSupportResponse supportResponseSum MomentPoint.supportTotal supportResponseTotal stepMeanShift sourceTerm
    stepSourceTerm
  rw [e3]
  beta_reduce at hs
  rw [hs]
  exact add_sub_assoc _ _ _
private theorem telescope_of_live_of_bases (hadd : StepIdentity S)
    (hlive : ∀ (u : ℕ) (hu : u ≤ S.data.windowLevel), ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)),
      IsLiveState Λ.stepParams (S.tower.stage u).coupling (S.tower.stage u).labelWeight
        (S.state u (S.sideAtLevel u) (S.sampleAtLevel u hu w)).1
        (S.state u (S.sideAtLevel u) (S.sampleAtLevel u hu w)).2.1 (S.state u (S.sideAtLevel u) (S.sampleAtLevel u hu w)).2.2)
    (hbase : ∀ (u : ℕ) (hu : u + 1 ≤ S.data.windowLevel), ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)),
      (S.sampleAtLevel (u + 1) hu w).2.1 ∈ baseChoices Λ.stepParams
        (readAtLevel (stepBlockFrame Λ.stepParams.side (S.sideAtLevel (u + 1))) 0
          (topField Λ.stepParams u (S.sideAtLevel (u + 1) * Λ.stepParams.side) (S.sampleAtLevel (u + 1) hu w).1))) :
    (∀ (i : Fin Λ.k) (t' : ℕ) (ht : t' ≤ S.data.windowLevel),
      ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)),
        _root_.YangMills.Construction.WeightedResponses.completedObservable S.tower S.coeff t' (S.sideAtLevel t') (S.weight i _) (S.sampleAtLevel t' ht w) -
            S.kappa t' (S.sideAtLevel t') i =
          responseAtLevel 0 i S w + ∑ j ∈ Finset.range t', centredStepScore j i S w) ∧
    ∀ (u : ℕ), u < S.data.windowLevel → ∀ J : Finset (Fin Λ.k),
      ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)),
        variableProduct u J S w = ∏ i ∈ J, (responseAtLevel u i S w + centredStepScore u i S w) := by
  refine ⟨fun i t' ht => Eventually.of_forall (telescope_sum S hadd i t' ht), fun u hu J => ?_⟩
  have h0 : u ≤ S.data.windowLevel := hu.le
  have h1 : u + 1 ≤ S.data.windowLevel := hu
  filter_upwards [hlive u h0, hbase u h1] with w hw hb
  have hbb : clampBasesToBlocks (S.sampleAtLevel (u + 1) h1 w).2.1 = (S.sampleAtLevel (u + 1) h1 w).2.1 := by
    classical
    exact clampBasesToBlocks_of_isBaseChoice (Finset.mem_filter.mp hb).2
  obtain ⟨e, hh⟩ := sampleAtLevel_fst S u h1 h0 w
  have hl : IsLiveState Λ.stepParams (S.tower.stage u).coupling (S.tower.stage u).labelWeight
      (stageState S.tower u _ (S.sampleAtLevel (u + 1) h1 w).1).1
      (stageState S.tower u _ (S.sampleAtLevel (u + 1) h1 w).1).2.1
      (stageState S.tower u _ (S.sampleAtLevel (u + 1) h1 w).1).2.2 :=
    sample_holds (fun n _ y => IsLiveState Λ.stepParams (S.tower.stage u).coupling (S.tower.stage u).labelWeight
      (stageState S.tower u n y).1 (stageState S.tower u n y).2.1 (stageState S.tower u n y).2.2) e hh hw
  rw [stageState_fst] at hl
  unfold variableProduct
  rw [dif_pos h1]
  unfold FreeEnergies.caseLift MomentPoint.variableCaseProduct
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hbb]
  unfold FreeEnergies.liveCaseFunction
  rw [if_pos hl]
  exact variableCase_eq S h1 h0 i w
theorem telescopeIdentity (hA : responsesAtTrivialFieldSumStatement) (hV : liveStatesStatement)
    (hB : sampleBelowLawStatement) (hH : ae_hasBaseChoicesStatement) : telescopeIdentityStatement := by
  intro a ha
  obtain ⟨L₁, rt₁, C₁, hrt₁, H₁⟩ := hV a ha
  obtain ⟨rt₂, hrt₂, H₂⟩ := hA
  refine ⟨L₁, fun c => min (rt₁ c) (rt₂ c), C₁, fun c => lt_min (hrt₁ c) (hrt₂ c), ?_⟩
  intro L hL hL₁ Tb hTa hTL hD hCS hCH hrt hCd Kr hKr
  obtain ⟨y₁, Y₁⟩ := H₁ L hL hL₁ Tb hTa hTL hD hCS hCH (hrt.trans (min_le_left _ _)) hCd Kr hKr
  obtain ⟨y₂, Y₂⟩ := H₂ Tb hD (hrt.trans (min_le_right _ _)) Kr
  refine ⟨max y₁ (max y₂ Tb.floorMin), ?_⟩
  intro y hy hret hwil g hg hgy k _ hk2 hk8 R d hd
  obtain ⟨_, _, _, _, _, Q⟩ := Y₁ y ((le_max_left _ _).trans hy) hret hwil g hg hgy k hk2 hk8 R d hd
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y ((le_max_right _ _).trans ((le_max_right _ _).trans hy))
  refine ⟨fun _ => 0, 1, y, one_pos, le_rfl, fun S => ?_⟩
  have hn : 3 ≤ (Tb.stepParameters y).n₀ := le_trans (by norm_num) hfit.n₀_ge
  have hadd : StepIdentity S := fun u hu n _ hn' f =>
    Y₂ y ((le_max_left _ _).trans ((le_max_right _ _).trans hy)) _ (S.resp u) (onFlow_at S hu.le).params_eq
      (onFlow_at S hu.le).onFamily n hn' f
  refine telescope_of_live_of_bases S hadd (fun u hu => ?_) fun u hu => ?_
  · obtain ⟨m1, e1⟩ := map_sampleAtLevel S hB hfit u hu
    have h := Q S u hu (S.sideAtLevel u) (isBlockTorusSide_sideAtLevel S hn u)
    rw [← e1] at h
    exact ae_of_ae_map m1.aemeasurable h
  · obtain ⟨m1, e1⟩ := map_sampleAtLevel S hB hfit (u + 1) hu
    have h : ∀ᵐ x ∂(S.law (u + 1) (S.sideAtLevel (u + 1))), x.2.1 ∈ baseChoices (Tb.stepParameters y)
        (readAtLevel (stepBlockFrame (Tb.stepParameters y).side (S.sideAtLevel (u + 1))) 0
          (topField (Tb.stepParameters y) u (S.sideAtLevel (u + 1) * (Tb.stepParameters y).side) x.1)) := by
      filter_upwards [hH (Tb.stepParameters y) S.tower S.β u 1 (S.sideAtLevel (u + 1))] with x hx
      exact hx.1
    rw [← e1] at h
    exact ae_of_ae_map m1.aemeasurable h
end YangMills.Construction.MomentLaw
end

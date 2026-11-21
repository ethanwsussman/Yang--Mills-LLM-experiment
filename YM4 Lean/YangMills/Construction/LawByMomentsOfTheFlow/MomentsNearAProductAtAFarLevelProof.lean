import YangMills.Construction.LawByMomentsOfTheFlow.VariablesOfAPointSplitProof
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsNearAProductAtAFarLevel
import YangMills.Construction.LawByMomentsOfTheFlow.TelescopeOfAPointProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
section Torus
private theorem minSeparation_add_four_le {k N : ℕ} [NeZero N] (A : Fin k → Finset (TorusFields.TorusSite N)) {i j : Fin k}
    (hij : i ≠ j) {y y' : TorusFields.TorusSite N} (hy : y ∈ A i) (hy' : y' ∈ A j)
    (h8 : 8 < LevelTestFunctions.minSeparation A) :
    LevelTestFunctions.minSeparation A + 4 ≤ TorusFields.supDist y y' := by
  classical
  have mem : ∀ {l : Fin k} {z z' : TorusFields.TorusSite N}, z' ∈ A l → TorusFields.supDist z z' ≤ 2 →
      z ∈ TorusLumps.thickening 2 (A l) := by
    intro l z z' hz' h
    simp only [TorusLumps.thickening, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨z', hz', h⟩
  have hle : ∀ z ∈ TorusLumps.thickening 2 (A i), ∀ z' ∈ TorusLumps.thickening 2 (A j),
      LevelTestFunctions.minSeparation A ≤ TorusFields.supDist z z' := fun z hz z' hz' =>
    Nat.sInf_le ⟨i, j, hij, z, hz, z', hz', rfl⟩
  have he : LevelTestFunctions.minSeparation A ≤ TorusFields.supDist y y' :=
    hle y (mem hy (by rw [TorusFields.supDist_self]; exact Nat.zero_le _)) y'
      (mem hy' (by rw [TorusFields.supDist_self]; exact Nat.zero_le _))
  obtain ⟨d, hd, hb⟩ := TorusFields.exists_offset_of_supDist y y'
  let c : Fin 4 → ℤ := fun a => max (-2) (min 2 (d a))
  let c' : Fin 4 → ℤ := fun a => - c a
  let e : Fin 4 → ℤ := fun a => d a - 2 * c a
  have hc : ∀ a, (c a).natAbs ≤ 2 := fun a => by
    simp only [c]
    omega
  have hc' : ∀ a, (c' a).natAbs ≤ 2 := fun a => by
    have := hc a
    simp only [c']
    omega
  have hz : TorusFields.supDist (y + TorusFields.siteOfInt c) y ≤ 2 := by
    rw [TorusFields.supDist_comm]
    exact TorusFields.supDist_add_siteOfInt_le y c 2 hc
  have hz' : TorusFields.supDist (y' + TorusFields.siteOfInt c') y' ≤ 2 := by
    rw [TorusFields.supDist_comm]
    exact TorusFields.supDist_add_siteOfInt_le y' c' 2 hc'
  have hzz : y' + TorusFields.siteOfInt c' = (y + TorusFields.siteOfInt c) + TorusFields.siteOfInt e := by
    rw [hd]
    funext a
    simp only [Pi.add_apply, TorusFields.siteOfInt, c', e]
    push_cast
    ring
  have hdist : TorusFields.supDist (y + TorusFields.siteOfInt c) (y' + TorusFields.siteOfInt c') ≤
      TorusFields.supDist y y' - 4 := by
    rw [hzz]
    refine TorusFields.supDist_add_siteOfInt_le _ e _ fun a => ?_
    have := hb a
    simp only [e, c]
    omega
  have := hle _ (mem hy hz) _ (mem hy' hz')
  omega
end Torus
section Rewriting
private theorem fineWeight_heq (f : FreeEnergies.FinePlaquetteFunction) {m m' : ℕ} (h : m = m') :
    HEq (FreeEnergies.fineWeight f m) (FreeEnergies.fineWeight f m') := by
  subst h
  rfl
private theorem weightSupportSites_depth_congr {L : ℕ} [NeZero L] (f : FreeEnergies.FinePlaquetteFunction) {t s : ℕ}
    (n : ℕ) [NeZero n] (h : t = s) :
    ResponseInTheExpansion.weightSupportSites L t n (FreeEnergies.fineWeight f (WeightedResponses.fineSide L t n)) =
      ResponseInTheExpansion.weightSupportSites L s n (FreeEnergies.fineWeight f (WeightedResponses.fineSide L s n)) := by
  subst h
  rfl
private theorem card_weightSupportSites_congr {L : ℕ} [NeZero L] (f : FreeEnergies.FinePlaquetteFunction) (t : ℕ)
    {N M : ℕ} [NeZero N] [NeZero M] (h : N = M) :
    (ResponseInTheExpansion.weightSupportSites L t N (FreeEnergies.fineWeight f (WeightedResponses.fineSide L t N))).card =
      (ResponseInTheExpansion.weightSupportSites L t M (FreeEnergies.fineWeight f (WeightedResponses.fineSide L t M))).card := by
  subst h
  rfl
private theorem with_responseParams_eq {R : StepSettings.StepSetup} (A : WeightedResponses.ResponseSetup R)
    {K : WeightedResponses.ResponseParameters} (h : A.responseParams = K) :
    ({ A with responseParams := K } : WeightedResponses.ResponseSetup R) = A := by
  subst h
  rfl
private theorem nextStage_components {ℓ : TorusLumps.StepParameters}
    (hL : ∀ c : WeightedResponses.ChainStage ℓ, ClusterExpansionOfAStep.CoarseLabelFacts c.toStepSetup) (lam x'' : ℝ)
    (c c' : WeightedResponses.ChainStage ℓ) (A : WeightedResponses.ResponseSetup c.toStepSetup)
    (A' : WeightedResponses.ResponseSetup c'.toStepSetup) (z : ResponseInTheExpansion.StageWithResponse ℓ)
    (h : (⟨c, A⟩ : ResponseInTheExpansion.StageWithResponse ℓ) = z)
    (h' : (⟨c', A'⟩ : ResponseInTheExpansion.StageWithResponse ℓ) = ResponseInTheExpansion.nextStageWithResponse hL lam x'' z) :
    HEq A'.cold A.coldStep ∧ HEq A'.hull A.hullStep ∧
      HEq A'.score (WeightedResponses.coarseLabelScore (L := ℓ.side) A.responseParams.s₁ A.score) := by apply _root_.YangMills.SharedProofs.p59553 <;> assumption
private theorem sideAt_succ_mul {k : ℕ} (P : LevelTestFunctions.LevelData k) (L v : ℕ) (hv : v + 1 ≤ P.windowLevel) :
    P.sideAt L (v + 1) * L = P.sideAt L v := by apply _root_.YangMills.SharedProofs.p32891 <;> assumption
end Rewriting
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private def scoredTower : FreeEnergies.ScoredStageTower S.tower :=
  ⟨Λ.response, fun u => { S.resp u with responseParams := Λ.response }⟩
private def barycentreFunction (i : Fin Λ.k) : FreeEnergies.FinePlaquetteFunction := fun b =>
  S.data.fn i (WithLp.toLp 2 fun a => (Λ.stepParams.side : ℝ) ^ S.data.windowLevel /
    (Λ.stepParams.side : ℝ) ^ S.data.scaleLevel *
    LevelTestFunctions.circleRep (S.data.period Λ.stepParams.side)
      (b a / (Λ.stepParams.side : ℝ) ^ S.data.windowLevel - S.data.center a))
private theorem stage_onFlow {u : ℕ} (hu : u ≤ S.data.windowLevel) :
    ResponseInTheExpansion.StageOnFlow Λ.table Λ.response Λ.floor S.β u
      (⟨S.tower.stage u, S.resp u⟩ : ResponseInTheExpansion.StageWithResponse Λ.stepParams) := by apply _root_.YangMills.SharedProofs.p21183 <;> assumption
private theorem stage_depth {u : ℕ} (hu : u ≤ S.data.windowLevel) : (S.tower.stage u).depth = u :=
  (stage_onFlow S hu).depth_eq
private theorem scoredTower_setup {u : ℕ} (hu : u ≤ S.data.windowLevel) : (scoredTower S).setup u = S.resp u :=
  with_responseParams_eq _ (stage_onFlow S hu).params_eq
private theorem resp_succ_components {u : ℕ} (hu : u + 1 ≤ S.data.windowLevel) :
    HEq (S.resp (u + 1)).cold (S.resp u).coldStep ∧ HEq (S.resp (u + 1)).hull (S.resp u).hullStep ∧
      HEq (S.resp (u + 1)).score
        (WeightedResponses.coarseLabelScore (L := Λ.stepParams.side) (S.resp u).responseParams.s₁ (S.resp u).score) :=
  nextStage_components S.labelFacts Λ.table.lam _ _ _ _ _ _ (S.stage_eq u (by omega)) (S.stage_eq (u + 1) hu)
private theorem scoredTower_followsFlow {tp : ℕ} (htp : tp ≤ S.data.windowLevel) :
    (scoredTower S).FollowsFlow S.β tp := by apply _root_.YangMills.DeltaSharedProofs.p502274 <;> assumption
private theorem couplingsAboveFloor_of_le {t : ℕ} (ht : t ≤ S.data.windowLevel) :
    FreeEnergies.CouplingsAboveFloor (Λ.table.stepParameters Λ.floor) S.β t := fun j hj => by
  have h := stage_onFlow S (hj.trans ht)
  exact le_of_le_of_eq h.onFamily.onFamily.le_coupling h.coupling_eq
private theorem isBlockTorusSide_levelSide (hn : 3 ≤ Λ.stepParams.n₀) (t : ℕ) :
    TorusLumps.IsBlockTorusSide Λ.stepParams (S.levelSide t) := by apply _root_.YangMills.SharedProofs.p33093 <;> assumption
private theorem kappa_zero (n : ℕ) [NeZero n] (i : Fin Λ.k) : S.kappa 0 n i = 0 := by apply _root_.YangMills.SharedProofs.p41593 <;> assumption
private def StepIdentityHolds : Prop :=
  ∀ u < S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n →
    ∀ f : WeightedResponses.PlaquetteWeight
      (WeightedResponses.fineSide Λ.stepParams.side ((S.tower.stage u).depth + 1) n),
    ∑ Y ∈ ResponseInTheExpansion.weightSupportSites Λ.stepParams.side ((S.tower.stage u).depth + 1) n f,
        (S.resp u).coldStep n Y (TorusFields.trivialField n) f =
      ∑ y ∈ ResponseInTheExpansion.weightSupportSites Λ.stepParams.side (S.tower.stage u).depth (n * Λ.stepParams.side) f,
          (S.resp u).cold (n * Λ.stepParams.side) y (TorusFields.trivialField (n * Λ.stepParams.side)) f +
        WeightedResponses.caseMean (S.tower.stage u).toStepSetup ∅ (TorusFields.trivialField n)
          (StepGas.emptyCoarseState _)
          (ResponseInTheExpansion.supportResponseSum (S.resp u) (TorusFields.trivialField n) f)
private theorem centering_eq_kappa (hadd : StepIdentityHolds S) : ∀ s ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n],
    Λ.stepParams.n₀ ≤ n → ∀ i,
    FreeEnergies.centering (scoredTower S) (barycentreFunction S i) s n = S.kappa s n i := by
  intro s
  induction s with
  | zero =>
    intro _ n _ _ i
    rw [kappa_zero]
    rfl
  | succ s ih =>
    intro hs n _ hn i
    have hs' : s ≤ S.data.windowLevel := by omega
    have ht := stage_depth S hs'
    have hP : (S.resp (s + 1)).cold = (S.resp s).coldStep := eq_of_heq (resp_succ_components S hs).1
    have h := hadd s (by omega) n hn (FreeEnergies.fineWeight (barycentreFunction S i) _)
    have hLpos : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
    have hnL : Λ.stepParams.n₀ ≤ n * Λ.stepParams.side := hn.trans (Nat.le_mul_of_pos_right _ hLpos)
    have hk1 : S.kappa (s + 1) n i =
        ∑ Y ∈ ResponseInTheExpansion.weightSupportSites Λ.stepParams.side ((S.tower.stage s).depth + 1) n
            (FreeEnergies.fineWeight (barycentreFunction S i) _),
          (S.resp s).coldStep n Y (TorusFields.trivialField n) (FreeEnergies.fineWeight (barycentreFunction S i) _) := by
      unfold MomentPoint.kappa MomentPoint.supportAt
      rw [hP]
      exact Finset.sum_congr (weightSupportSites_depth_congr (barycentreFunction S i) n (by rw [ht])).symm
        fun _ _ => rfl
    have hk0 : S.kappa s (n * Λ.stepParams.side) i =
        ∑ y ∈ ResponseInTheExpansion.weightSupportSites Λ.stepParams.side (S.tower.stage s).depth (n * Λ.stepParams.side)
            (FreeEnergies.fineWeight (barycentreFunction S i) _),
          (S.resp s).cold (n * Λ.stepParams.side) y (TorusFields.trivialField (n * Λ.stepParams.side))
            (FreeEnergies.fineWeight (barycentreFunction S i) _) := by
      unfold MomentPoint.kappa MomentPoint.supportAt
      exact Finset.sum_congr (weightSupportSites_depth_congr (barycentreFunction S i) _ ht).symm fun _ _ => rfl
    have hc : FreeEnergies.centering (scoredTower S) (barycentreFunction S i) (s + 1) n =
        FreeEnergies.centering (scoredTower S) (barycentreFunction S i) s (n * Λ.stepParams.side) +
          WeightedResponses.caseMean (S.tower.stage s).toStepSetup ∅ (TorusFields.trivialField n)
            (StepGas.emptyCoarseState _)
            (ResponseInTheExpansion.supportResponseSum (S.resp s) (TorusFields.trivialField n)
              (FreeEnergies.fineWeight (barycentreFunction S i) _)) := by
      show _ + WeightedResponses.caseMean (S.tower.stage s).toStepSetup ∅ (TorusFields.trivialField n)
        (StepGas.emptyCoarseState _)
        (ResponseInTheExpansion.supportResponseSum ((scoredTower S).setup s) (TorusFields.trivialField n)
          (FreeEnergies.fineWeight (barycentreFunction S i) _)) = _
      rw [scoredTower_setup S hs']
    rw [hc, ih hs' (n * Λ.stepParams.side) hnL i, hk1, hk0]
    exact h.symm
private theorem separatedAlongTower_of_separatedBelow {p : ℕ} (idx : Fin p → Fin Λ.k) (hidx : Function.Injective idx) :
    ∀ v ≤ S.data.windowLevel, ∀ (N : ℕ) [NeZero N],
    N = S.data.sideAt Λ.stepParams.side v → S.data.SeparatedBelow Λ.stepParams S.β v →
    TransfersOffTheWalk.SeparatedAlongTower Λ.stepParams (ClusterExpansionOfAStep.flowCoupling Λ.stepParams S.β)
      (fun u => (S.data.separation Λ.stepParams.side u : ℝ)) v N
      (fun j => FreeEnergies.fineWeight (barycentreFunction S (idx j))
        (WeightedResponses.fineSide Λ.stepParams.side v N)) := by
  intro v
  induction v with
  | zero =>
    intro _ N _ _ _
    exact trivial
  | succ v ih =>
    intro hv N _ hN hfar
    have hfv := hfar v (Nat.lt_succ_self v)
    refine ⟨⟨?_, ?_, ?_⟩, ih (by omega) (N * Λ.stepParams.side)
      (by rw [hN]; exact sideAt_succ_mul _ _ _ hv) fun u hu => hfar u (by omega)⟩
    · have h := hfv.1
      show (2 : ℝ) ^ 10 * (TorusLumps.clusterRange (TorusLumps.couplingFlow Λ.stepParams S.β v).1 : ℝ) ≤
        (S.data.separation Λ.stepParams.side v : ℝ)
      exact_mod_cast h
    · have h := hfv.2
      show (8 : ℝ) < (S.data.separation Λ.stepParams.side v : ℝ)
      exact_mod_cast h
    · subst hN
      intro i j hij y hy y' hy'
      have h := minSeparation_add_four_le (fun l => S.data.supportSites Λ.stepParams.side (v + 1) l)
        (hidx.ne hij) hy hy' hfv.2
      show (S.data.separation Λ.stepParams.side v : ℝ) + 4 ≤ (TorusFields.supDist y y' : ℝ)
      exact_mod_cast h
private theorem separationError_eq {p : ℕ} (idx : Fin p → Fin Λ.k) (B : Finset (Fin Λ.k))
    (hsum : ∀ g : Fin Λ.k → ℝ, ∑ i ∈ B, g i = ∑ j, g (idx j))
    (hprod : ∀ g : Fin Λ.k → ℝ, ∏ i ∈ B, g i = ∏ j, g (idx j))
    (Cp : ℝ) : ∀ v ≤ S.data.windowLevel, ∀ (N : ℕ) [NeZero N], N = S.data.sideAt Λ.stepParams.side v →
    TransfersOffTheWalk.separationError Λ.stepParams Cp Λ.response.C₀
      (fun u => (S.data.separation Λ.stepParams.side u : ℝ)) v N
      (fun j => FreeEnergies.fineWeight (barycentreFunction S (idx j))
        (WeightedResponses.fineSide Λ.stepParams.side v N)) = S.separationError Cp v B := by
  intro v
  induction v with
  | zero =>
    intro _ N _ _
    simp [TransfersOffTheWalk.separationError, MomentPoint.separationError]
  | succ v ih =>
    intro hv N _ hN
    have hN' : N * Λ.stepParams.side = S.data.sideAt Λ.stepParams.side v := by
      rw [hN]
      exact sideAt_succ_mul _ _ _ hv
    have ih' := ih (by omega) (N * Λ.stepParams.side) hN'
    have hcard : ∀ j, ((ResponseInTheExpansion.weightSupportSites Λ.stepParams.side v (N * Λ.stepParams.side)
        (FreeEnergies.fineWeight (barycentreFunction S (idx j))
          (WeightedResponses.fineSide Λ.stepParams.side v (N * Λ.stepParams.side)))).card : ℝ) =
        ((S.data.supportSites Λ.stepParams.side v (idx j)).card : ℝ) := fun j => by
      exact_mod_cast card_weightSupportSites_congr (barycentreFunction S (idx j)) v hN'
    show TransfersOffTheWalk.separationError Λ.stepParams Cp Λ.response.C₀
        (fun u => (S.data.separation Λ.stepParams.side u : ℝ)) v (N * Λ.stepParams.side)
        (fun j => FreeEnergies.fineWeight (barycentreFunction S (idx j))
          (WeightedResponses.fineSide Λ.stepParams.side v (N * Λ.stepParams.side))) +
      Cp * (∑ j, ((ResponseInTheExpansion.weightSupportSites Λ.stepParams.side v (N * Λ.stepParams.side)
          (FreeEnergies.fineWeight (barycentreFunction S (idx j))
            (WeightedResponses.fineSide Λ.stepParams.side v (N * Λ.stepParams.side)))).card : ℝ)) ^ 2 *
        Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side v : ℝ) / 2 ^ 8)) *
        ∏ j, (4 * Λ.response.C₀ * ((ResponseInTheExpansion.weightSupportSites Λ.stepParams.side v (N * Λ.stepParams.side)
          (FreeEnergies.fineWeight (barycentreFunction S (idx j))
            (WeightedResponses.fineSide Λ.stepParams.side v (N * Λ.stepParams.side)))).card : ℝ)) = _
    rw [ih']
    simp only [hcard]
    unfold MomentPoint.separationError
    rw [Finset.sum_range_succ, mul_add, hsum fun i => ((S.data.supportSites Λ.stepParams.side v i).card : ℝ),
      hprod fun i => 4 * (Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side v i).card : ℝ))]
    simp only [mul_assoc]
private theorem fittedResponse_eq (i : Fin Λ.k) {u : ℕ} (hu : u ≤ S.data.windowLevel) (n : ℕ) [NeZero n]
    (q : WeightedResponses.StageState S.tower u n) :
    FreeEnergies.fittedResponse (scoredTower S) (barycentreFunction S i) u n q = S.supportTotal u n i q := by
  unfold FreeEnergies.fittedResponse FreeEnergies.functionSites MomentPoint.supportTotal
    ResponseInTheExpansion.supportResponseTotal
  exact Finset.sum_congr (weightSupportSites_depth_congr (barycentreFunction S i) n (stage_depth S hu)).symm
    fun _ _ => rfl
private theorem product_bound_of_separated (hn : 3 ≤ Λ.stepParams.n₀) (hadd : StepIdentityHolds S) {Cp : ℝ}
    (B : Finset (Fin Λ.k))
    (M : ∀ (s n : ℕ) [NeZero n] (D : ℕ → ℝ) (f : Fin B.card → FreeEnergies.FinePlaquetteFunction),
      (scoredTower S).params = Λ.response → (scoredTower S).FollowsFlow S.β s →
      FreeEnergies.CouplingsAboveFloor (Λ.table.stepParameters Λ.floor) S.β s →
      TorusLumps.IsBlockTorusSide (Λ.table.stepParameters Λ.floor) n →
      (∀ i, WeightedResponses.weightNorm (Λ.table.stepParameters Λ.floor).side s
        (FreeEnergies.fineWeight (f i) (WeightedResponses.fineSide (Λ.table.stepParameters Λ.floor).side s n)) ≤ 1) →
      TransfersOffTheWalk.SeparatedAlongTower (Λ.table.stepParameters Λ.floor)
        (ClusterExpansionOfAStep.flowCoupling (Λ.table.stepParameters Λ.floor) S.β) D s n
        (fun i => FreeEnergies.fineWeight (f i) _) →
      FreeEnergies.HasConditionalMean S.tower S.β s n
        (fun u => ∏ i, FreeEnergies.completedCentered (scoredTower S) (f i) s n u) ∧
      ∀ᵐ u ∂(WeightedResponses.markedSampleLaw S.tower S.β s n),
        |FreeEnergies.conditionalProduct (scoredTower S) S.β f Finset.univ s n u -
            ∏ i, FreeEnergies.fittedResponse (scoredTower S) (f i) s n (WeightedResponses.stageState S.tower s n u)| ≤
          TransfersOffTheWalk.separationError (Λ.table.stepParameters Λ.floor) Cp Λ.response.C₀ D s n
              (fun i => FreeEnergies.fineWeight (f i) _) *
            ∏ i, FreeEnergies.scoreMeanOver (scoredTower S) (f i) s n (WeightedResponses.stageState S.tower s n u))
    {t' : ℕ} (ht' : t' ≤ S.data.windowLevel)
    (hsz : ∀ u ≤ t', ∀ i : Fin Λ.k, WeightedResponses.weightNorm Λ.stepParams.side u
      (S.weight i (WeightedResponses.fineSide Λ.stepParams.side u (S.levelSide u))) ≤ 1)
    (hfar : S.data.SeparatedBelow Λ.stepParams S.β t') :
    ∀ᵐ w ∂(S.law t' (S.levelSide t')),
      |WeightedResponses.conditionalCenteredProduct S.tower S.β S.coeff t' (S.levelSide t') (fun i => S.weight i _) B
          (fun i => S.kappa t' (S.levelSide t') i) w -
          ∏ i ∈ B, S.supportTotal t' (S.levelSide t') i (S.state t' (S.levelSide t') w)| ≤
        S.separationError Cp t' B * ∏ i ∈ B, S.meanScore t' (S.levelSide t') i (S.state t' (S.levelSide t') w) := by
  classical
  let e : Fin B.card ≃ {i // i ∈ B} := B.equivFin.symm
  let idx : Fin B.card → Fin Λ.k := fun j => (e j).1
  have hidx : Function.Injective idx := fun a b h => e.injective (Subtype.ext h)
  have hprod : ∀ g : Fin Λ.k → ℝ, ∏ i ∈ B, g i = ∏ j, g (idx j) := by
    intro g
    rw [← Finset.prod_coe_sort B g]
    exact (Equiv.prod_comp e fun i : {i // i ∈ B} => g i.1).symm
  have hsum : ∀ g : Fin Λ.k → ℝ, ∑ i ∈ B, g i = ∑ j, g (idx j) := by
    intro g
    rw [← Finset.sum_coe_sort B g]
    exact (Equiv.sum_comp e fun i : {i // i ∈ B} => g i.1).symm
  have hblock := isBlockTorusSide_levelSide S hn t'
  obtain ⟨-, hae⟩ := M t' (S.levelSide t') (fun u => (S.data.separation Λ.stepParams.side u : ℝ))
    (fun j => barycentreFunction S (idx j)) rfl (scoredTower_followsFlow S ht') (couplingsAboveFloor_of_le S ht')
    hblock (fun j => hsz t' le_rfl (idx j))
    (separatedAlongTower_of_separatedBelow S idx hidx t' ht' (S.levelSide t') rfl hfar)
  have hn₀ : Λ.stepParams.n₀ ≤ S.levelSide t' := by
    have hL : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
    exact (Nat.le_mul_of_pos_left _ hL).trans hblock.2
  have hkp := centering_eq_kappa S hadd t' ht' (S.levelSide t') hn₀
  filter_upwards [hae] with w hw
  have e1 : FreeEnergies.conditionalProduct (scoredTower S) S.β (fun j => barycentreFunction S (idx j)) Finset.univ t'
      (S.levelSide t') =
      WeightedResponses.conditionalCenteredProduct S.tower S.β S.coeff t' (S.levelSide t') (fun i => S.weight i _) B
        (fun i => S.kappa t' (S.levelSide t') i) := by
    unfold FreeEnergies.conditionalProduct WeightedResponses.conditionalCenteredProduct
    congr 1
    funext u
    rw [hprod]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold FreeEnergies.completedCentered
    rw [hkp]
    rfl
  have e2 : ∏ j, FreeEnergies.fittedResponse (scoredTower S) (barycentreFunction S (idx j)) t' (S.levelSide t')
      (WeightedResponses.stageState S.tower t' (S.levelSide t') w) =
      ∏ i ∈ B, S.supportTotal t' (S.levelSide t') i (S.state t' (S.levelSide t') w) := by
    rw [hprod]
    exact Finset.prod_congr rfl fun j _ => fittedResponse_eq S _ ht' _ _
  have e3 := separationError_eq S idx B hsum hprod Cp t' ht' (S.levelSide t') rfl
  have e4 : ∏ j, FreeEnergies.scoreMeanOver (scoredTower S) (barycentreFunction S (idx j)) t' (S.levelSide t')
      (WeightedResponses.stageState S.tower t' (S.levelSide t') w) =
      ∏ i ∈ B, S.meanScore t' (S.levelSide t') i (S.state t' (S.levelSide t') w) := by
    rw [hprod]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold FreeEnergies.scoreMeanOver
    rw [scoredTower_setup S ht']
    rfl
  rw [e1, e2, e4] at hw
  have hw' := hw
  rw [show TransfersOffTheWalk.separationError (Λ.table.stepParameters Λ.floor) Cp Λ.response.C₀
      (fun u => (S.data.separation Λ.stepParams.side u : ℝ)) t' (S.levelSide t')
      (fun i => FreeEnergies.fineWeight (barycentreFunction S (idx i)) _) = S.separationError Cp t' B from e3] at hw'
  exact hw'
theorem productApproxAtSeparatedLevel (hM : TransfersOffTheWalk.separatedProductsStatement)
    (hA : responsesAtTrivialFieldSumStatement) : productApproxAtSeparatedLevelStatement := by
  intro a ha
  obtain ⟨L₀, rt₁, C₀, hrt₁, H₁⟩ := hM a ha
  obtain ⟨rt₂, hrt₂, H₂⟩ := hA
  refine ⟨L₀, fun c => min (rt₁ c) (rt₂ c), C₀, fun c => lt_min (hrt₁ c) (hrt₂ c), ?_⟩
  intro L hL hL₀ Tb hTa hTL hD hCS hCH hrt hCd Kr _
  obtain ⟨y₁, Y₁⟩ := H₁ L hL hL₀ Tb hTa hTL hD hCS hCH (hrt.trans (min_le_left _ _)) hCd Kr
  obtain ⟨y₂, Y₂⟩ := H₂ Tb hD (hrt.trans (min_le_right _ _)) Kr
  refine ⟨max y₁ (max y₂ Tb.floorMin), ?_⟩
  intro y hy hret hwil g _ _ k _ _ _ R d _
  have hstand : FreeEnergies.ExpansionHolds (Tb.stepParameters y) := ⟨hret, hwil⟩
  have Hy := Y₁ y ((le_max_left _ _).trans hy) hstand
  choose Cf _ Hf using Hy
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y ((le_max_right _ _).trans ((le_max_right _ _).trans hy))
  refine ⟨Cf, 1, y, one_pos, le_rfl, ?_⟩
  intro S t' ht' hsz hfar B
  have hn : 3 ≤ (Tb.stepParameters y).n₀ := le_trans (by norm_num) hfit.n₀_ge
  have hadd : StepIdentityHolds S := fun u hu n _ hn' f =>
    Y₂ y ((le_max_left _ _).trans ((le_max_right _ _).trans hy)) _ (S.resp u) (stage_onFlow S hu.le).params_eq
      (stage_onFlow S hu.le).onFamily n hn' f
  exact product_bound_of_separated S hn hadd B
    (fun s n _ D f h₁ h₂ h₃ h₄ h₅ h₆ => Hf B.card S.tower (scoredTower S) S.β s n D f h₁ h₂ h₃ h₄ h₅ h₆) ht' hsz hfar
end YangMills.Construction.MomentLaw
end

import YangMills.Construction.FreeEnergiesOfTheFlow.CompletedObservablesAreBoundedProof
import YangMills.Construction.FreeEnergiesOfTheFlow.FittedResponsesAreMeansProof
import YangMills.Construction.ResponseInTheExpansion.ColdResponsesOfAScoredTowerAreTheChain
import YangMills.Construction.ResponseInTheExpansion.MeansGivenAStateAreMeansOverItsCases
import YangMills.Construction.ResponseInTheExpansion.MomentsAlongTheLevelsProof
import YangMills.Construction.ResponseInTheExpansion.NumbersOfAScoredTowerAreTheChainProof
import YangMills.Construction.ResponseInTheExpansion.ResponseAlongTheChainForgets
import YangMills.Construction.ResponseInTheExpansion.StoredScoresOfAGround
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses TorusFields TorusLumps StepSettings StepGas RenormalizationStepParameters StepCosts StepFloors FreeEnergies
  FreeEnergiesOfTheFlow LevelTestFunctions
section Fine
private theorem barycenter_injective {m : ℕ} [NeZero m] (p p' : OrientedPlaquette m)
    (e : barycenterCoord p.1 = barycenterCoord p'.1) : p = p' := by apply _root_.YangMills.SharedProofs.p53598 <;> assumption
open Classical in
private def fineOf {m : ℕ} (h : PlaquetteWeight m) : FinePlaquetteFunction := fun b =>
  if hb : ∃ p : OrientedPlaquette m, barycenterCoord p.1 = b then h hb.choose.1 else 0
private theorem fineOf_eq {m : ℕ} [NeZero m] (h : PlaquetteWeight m) (p : TorusPlaquette m) (hp : p.2.1 < p.2.2) :
    fineWeight (fineOf h) m p = h p := by apply _root_.YangMills.DeltaSharedProofs.p501682 <;> assumption
private theorem curvature_congr {m : ℕ} [NeZero m] (W : TorusField m) (h h' : PlaquetteWeight m)
    (e : ∀ p : TorusPlaquette m, p.2.1 < p.2.2 → h p = h' p) : curvatureObservable h W = curvatureObservable h' W := by
  unfold curvatureObservable
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [e p (Finset.mem_filter.mp hp).2.1]
private theorem blockMean_congr (L : ℕ) [NeZero L] (t : ℕ) : ∀ (n : ℕ) [NeZero n] (z : TorusSite n)
    (h h' : PlaquetteWeight (fineSide L t n)),
    (∀ p : TorusPlaquette (fineSide L t n), p.2.1 < p.2.2 → h p = h' p) → blockMean L t n z h = blockMean L t n z h' := by
  induction t with
  | zero =>
    intro n _ z h h' e
    show (1 / 24) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity z p * h p =
      (1 / 24) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity z p * h' p
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [e p (Finset.mem_filter.mp hp).2.1]
  | succ t ih =>
    intro n _ z h h' e
    show ((L : ℝ) ^ 4)⁻¹ * ∑ y ∈ sitesInBlocks L {z}, blockMean L t (n * L) y h =
      ((L : ℝ) ^ 4)⁻¹ * ∑ y ∈ sitesInBlocks L {z}, blockMean L t (n * L) y h'
    congr 1
    exact Finset.sum_congr rfl fun y _ => ih (n * L) y h h' e
private theorem weightNorm_congr {L t m : ℕ} (h h' : PlaquetteWeight m) (e : ∀ p : TorusPlaquette m, p.2.1 < p.2.2 → h p = h' p) :
    weightNorm L t h = weightNorm L t h' := by
  have e1 : weightLipschitz L t h = weightLipschitz L t h' := by
    unfold weightLipschitz
    congr 1
    funext pp
    rw [e _ pp.1.2, e _ pp.2.2]
  have e2 : weightSup h = weightSup h' := by
    unfold weightSup
    congr 1
    funext p
    rw [e _ p.2]
  unfold weightNorm
  rw [e1, e2]
private theorem fine_norm (L : ℕ) [NeZero L] {t k : ℕ} (ht : t = k) (n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide L k n)) :
    weightNorm L t (fineWeight (fineOf h) (fineSide L t n)) = weightNorm L k h := by
  subst ht
  exact weightNorm_congr _ _ fun p hp => fineOf_eq h p hp
private theorem fine_off (L : ℕ) [NeZero L] {t k : ℕ} (ht : t = k) (n : ℕ) [NeZero n] (z : TorusSite n)
    (h : PlaquetteWeight (fineSide L k n)) (hz : z ∉ weightSupportSites L k n h) :
    ∀ p : TorusPlaquette (fineSide L t n), IsPlaquetteAt L t z p →
      fineWeight (fineOf h) (fineSide L t n) p = (0 : PlaquetteWeight (fineSide L t n)) p := by
  subst ht
  intro p hp
  rw [fineOf_eq h p hp.1]
  by_contra hne
  apply hz
  simp only [weightSupportSites, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨p, hp, hne⟩
private theorem fine_agree (L : ℕ) [NeZero L] {t k : ℕ} (ht : t = k) {n n' : ℕ} [NeZero n] [NeZero n'] (z : TorusSite n)
    (z' : TorusSite n') (h : PlaquetteWeight (fineSide L k n)) (h' : PlaquetteWeight (fineSide L k n'))
    (hA : WeightsAgreeAt L k z z' h h') :
    WeightsAgreeAt L t z z' (fineWeight (fineOf h) (fineSide L t n)) (fineWeight (fineOf h') (fineSide L t n')) := by
  subst ht
  intro v μ ν hv hat
  exact (fineOf_eq h _ hat.1).trans ((hA v μ ν hv hat).trans (fineOf_eq h' _ hat.1).symm)
end Fine
section Sums
private theorem siteResponse_total {n : ℕ} [NeZero n] (h : PlaquetteWeight n) (W : TorusField n) :
    ∑ z : TorusSite n, siteResponse z W h = curvatureObservable h W := by apply _root_.YangMills.SharedProofs.p40351 <;> assumption
private theorem sum_over_blocks {n : ℕ} [NeZero n] (L : ℕ) [NeZero L] (f : TorusSite (n * L) → ℝ) :
    ∑ Y : TorusSite n, ∑ y ∈ sitesInBlocks L {Y}, f y = ∑ y, f y := by apply _root_.YangMills.Construction.FreeBonds.sum_sitesInBlocks_singleton <;> assumption
private theorem coarseLabelScore_bound {Ω : Type} {L : ℕ} (s₁ : ℝ) (s : Ω → ℝ) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ w, |s w| ≤ B)
    (w : CoarseLabel Ω L) : |coarseLabelScore s₁ s w| ≤ |s₁| + (Fintype.card (BlockOffset L) : ℝ) * B := by
  rcases w with u | st
  · show |s₁| ≤ _
    have : 0 ≤ (Fintype.card (BlockOffset L) : ℝ) * B := by positivity
    linarith
  · show |s₁ + ∑ o : BlockOffset L, Sum.elim (fun _ => 0) s (st.siteLabel o)| ≤ _
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ o : BlockOffset L, |Sum.elim (fun _ => 0) s (st.siteLabel o)| ≤ ∑ _o : BlockOffset L, B :=
          Finset.sum_le_sum fun o _ => by
            rcases st.siteLabel o with u | v
            · simpa using hB0
            · simpa using hB v
      _ = _ := by simp
end Sums
section Sigma
variable {X A : Type} [MeasurableSpace X] {β : A → Type} [∀ a, MeasurableSpace (β a)]
private theorem measurable_of_prod_sigma [DecidableEq A] [Countable A] {g : X × Sigma β → ℝ}
    (h : ∀ a, Measurable fun p : X × β a => g (p.1, ⟨a, p.2⟩)) : Measurable g := by apply _root_.YangMills.SharedProofs.p67771 <;> assumption
end Sigma
section Outcomes
variable {ℓ : StepParameters}
private theorem measurable_outcome {X : Type} [MeasurableSpace X] {n : ℕ} [NeZero n] {f : X × StepOutcome ℓ n → ℝ}
    (h : ∀ (b : BaseChoice ℓ.side n) (bad : BondSet (n * ℓ.side)),
      Measurable fun p : X × TorusField n => f (p.1, (b, p.2, bad))) : Measurable f := by apply _root_.YangMills.SharedProofs.p21057 <;> assumption
private theorem measurable_bondScoresAtSite (hSc : BondScoreProperties) (hf : ℓ.Admissible) (x : ℝ) {n : ℕ} [NeZero n]
    (Y : TorusSite n) :
    Measurable fun p : TorusField (n * ℓ.side) × StepOutcome ℓ n => bondScoresAtSite ℓ x p.1 p.2.2.1 p.2.1 Y := by
  refine measurable_outcome (f := fun p : TorusField (n * ℓ.side) × StepOutcome ℓ n =>
    bondScoresAtSite ℓ x p.1 p.2.2.1 p.2.1 Y) fun b bad => ?_
  show Measurable fun p : TorusField (n * ℓ.side) × TorusField n => bondScoresAtSite ℓ x p.1 p.2 b Y
  unfold bondScoresAtSite
  exact Finset.measurable_sum _ fun i _ =>
    ((hSc ℓ hf x n b (Y, i)).2.2.2.2).add ((hSc ℓ hf x n b (Y - unitStep n i, i)).2.2.2.2)
private theorem bondScoresAtSite_bound (hSc : BondScoreProperties) (hf : ℓ.Admissible) (x : ℝ) {n : ℕ} [NeZero n]
    (W : TorusField (n * ℓ.side)) (V : TorusField n) (b : BaseChoice ℓ.side n) (Y : TorusSite n) :
    |bondScoresAtSite ℓ x W V b Y| ≤ 16 := by
  unfold bondScoresAtSite
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hc : ∀ c : TorusBond n, |bondScore ℓ x W V b c| ≤ 2 := fun c => (hSc ℓ hf x n b c).2.2.1 W V
  have : ∀ i : Fin 4, |bondScore ℓ x W V b (Y, i) + bondScore ℓ x W V b (Y - unitStep n i, i)| ≤ 4 := fun i =>
    (abs_add_le _ _).trans (by linarith [hc (Y, i), hc (Y - unitStep n i, i)])
  calc _ ≤ ∑ _i : Fin 4, (4 : ℝ) := Finset.sum_le_sum fun i _ => this i
    _ = 16 := by norm_num
private theorem stageState_fst (T : StageTower ℓ) (s n : ℕ) [NeZero n] (a : MarkedSample ℓ s n) :
    (stageState T s n a).1 = topField ℓ s n a := by apply _root_.YangMills.SharedProofs.p2480 <;> assumption
private theorem blockMean_depth (L : ℕ) [NeZero L] (f : FinePlaquetteFunction) {t s : ℕ} (ht : t = s) (m : ℕ) [NeZero m]
    (Y : TorusSite m) :
    blockMean L t m Y (fineWeight f (fineSide L t m)) = blockMean L s m Y (fineWeight f (fineSide L s m)) := by
  subst ht
  rfl
private theorem response_congr (T : StageTower ℓ) (β : ℝ) (al : ℕ → ℝ) (s : ℕ) : ∀ (n : ℕ) [NeZero n]
    (h h' : PlaquetteWeight (fineSide ℓ.side s n)),
    (∀ p : TorusPlaquette (fineSide ℓ.side s n), p.2.1 < p.2.2 → h p = h' p) →
      response T β al s n h = response T β al s n h' := by
  induction s with
  | zero =>
    intro n _ h h' e
    funext W
    exact curvature_congr W h h' e
  | succ s ih =>
    intro n _ h h' e
    have hh : ∀ Y : TorusSite n, blockMean ℓ.side (s + 1) n Y h = blockMean ℓ.side (s + 1) n Y h' := fun Y =>
      blockMean_congr ℓ.side (s + 1) n Y h h' e
    have e1 : (fun u : MarkedSample ℓ (s + 1) n => response T β al s (n * ℓ.side) h u.1 + sourceTerm T al s n h u) =
        fun u => response T β al s (n * ℓ.side) h' u.1 + sourceTerm T al s n h' u := by
      funext u
      rw [ih (n * ℓ.side) h h' e]
      congr 1
      unfold sourceTerm stepSourceTerm
      simp only [hh]
    funext u
    show ((markedSampleLaw T β (s + 1) n)[fun u : MarkedSample ℓ (s + 1) n =>
        response T β al s (n * ℓ.side) h u.1 + sourceTerm T al s n h u | stageSigma T (s + 1) n]) u =
      ((markedSampleLaw T β (s + 1) n)[fun u : MarkedSample ℓ (s + 1) n =>
        response T β al s (n * ℓ.side) h' u.1 + sourceTerm T al s n h' u | stageSigma T (s + 1) n]) u
    rw [e1]
end Outcomes
private theorem isWellPosed_of_onParameters {T : ParameterAssignment} (hT : T.Admissible) {y : ℝ} (hy₀ : T.floorMin ≤ y) (hy₁ : 1 ≤ y)
    {R : StepSetup} (hon : R.OnParameters T y) (hmoved : |R.nextCoupling - R.coupling| ≤ 2 * T.B) (hArr : R.IsSymmetricWeight)
    (hF : T.FloorConditions (2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17) 1 R.coupling) : R.IsWellPosed := by apply _root_.YangMills.SharedProofs.p3707 <;> assumption
section Core
variable {ℓ : StepParameters} {T : StageTower ℓ}
open Classical in
private def liveHull (S : ScoredStageTower T) (f : FinePlaquetteFunction) (s n : ℕ) [NeZero n] (y : TorusSite n)
    (q : StageState T s n) : ℝ :=
  if IsLiveState ℓ (T.stage s).coupling (T.stage s).labelWeight q.1 q.2.1 q.2.2 then
    (S.setup s).hull n y q.1 q.2.1 q.2.2 (fineWeight f _) else 0
private structure StageFacts (S : ScoredStageTower T) (β : ℝ) (k : ℕ) : Prop where
  fits : ℓ.Admissible
  cutoff : ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn
  marks : T.MarksMeasurable
  start : StageTower.StartsAtWilson T β
  expansions : ∀ s ≤ k, (T.stage s).toStepSetup.HasExpansions
  admissible : ∀ s ≤ k, (S.setup s).IsAdmissible
  scoreBounded : ∀ s ≤ k, ∃ B : ℝ, 0 ≤ B ∧ ∀ w, |(S.setup s).score w| ≤ B
  depth : ∀ u, (T.stage u).depth = u
  hull_zero : ∀ (n : ℕ) [NeZero n] (z : TorusSite n) (W : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → (T.stage 0).labels.Ω) (f : FinePlaquetteFunction),
    (S.setup 0).hull n z W Y ω (fineWeight f _) = siteResponse z W (fineWeight f n)
  hull_succ : ∀ u < k, (S.setup (u + 1)).hull = (S.setup u).hullStep
  wellPosed : ∀ u < k, (T.stage u).toStepSetup.IsWellPosed
  condMean : ∀ u < k, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n →
    ∀ F : TorusField n → CaseFunction (T.stage u).toStepSetup n,
    Measurable (caseLift T u n F) → (∃ C : ℝ, ∀ x, |caseLift T u n F x| ≤ C) →
    (markedSampleLaw T β (u + 1) n)[caseLift T u n F | stageSigma T (u + 1) n] =ᵐ[markedSampleLaw T β (u + 1) n]
      caseMeanAtSample T u n F
private theorem isLive_zero {S : ScoredStageTower T} {β : ℝ} {k : ℕ} (hF : StageFacts S β k) (n : ℕ) [NeZero n]
    (hbs : IsBlockTorusSide ℓ n) (W : TorusField n) :
    IsLiveState ℓ (T.stage 0).coupling (T.stage 0).labelWeight W
      (thickening (2 * clusterRange T.base.coupling) (torusHotSites ℓ W)) (fun _ => T.basePoint) := by
  classical
  have hd := hF.start.labelWeight_eq n W
  have hpos : 0 < wilsonWeight β n W := by
    unfold wilsonWeight
    rw [dif_neg (NeZero.ne n)]
    exact Real.exp_pos _
  have hD : 0 < (T.stage 0).labelWeight n W (thickening (2 * clusterRange T.base.coupling) (torusHotSites ℓ W))
      (fun _ => T.basePoint) := by
    refine lt_of_lt_of_eq hpos ?_
    exact ((hd _ _).trans (if_pos rfl)).symm
  refine ⟨?_, hD⟩
  by_contra hn
  have hs := (hF.expansions 0 (Nat.zero_le _)).2.sum n hbs W
  have h0 : ENNReal.ofReal ((T.stage 0).toStepSetup.functional n W) = 0 := by
    refine hs.symm.trans ?_
    refine Finset.sum_eq_zero fun Y hY => ?_
    have hne : Y ≠ thickening (2 * clusterRange T.base.coupling) (torusHotSites ℓ W) :=
      fun e => hn (e ▸ (Finset.mem_filter.mp hY).2)
    have hz : ∀ ω : Y → (T.stage 0).labels.Ω, ENNReal.ofReal ((T.stage 0).toStepSetup.labelWeight n W Y ω) = 0 := fun ω => by
      have : (T.stage 0).toStepSetup.labelWeight n W Y ω = 0 := (hd Y ω).trans (if_neg hne)
      rw [this, ENNReal.ofReal_zero]
    simp only [hz, lintegral_zero]
  have hDe : (T.stage 0).toStepSetup.functional n W = wilsonWeight β n W := congrFun (congrFun hF.start.functional_eq n) W
  rw [hDe] at h0
  exact absurd h0 (ENNReal.ofReal_pos.mpr hpos).ne'
private theorem isLive_ae (hSt : StageStatesMeasurableStatement) (hT : TwoPointByTotalCovarianceStatement)
    (hImg : CoarseHullIsHullState) {S : ScoredStageTower T} {β : ℝ} {k : ℕ} (hF : StageFacts S β k) (s : ℕ) (hs : s ≤ k)
    (n : ℕ) [NeZero n] (hbs : IsBlockTorusSide ℓ n) : ∀ᵐ a ∂(markedSampleLaw T β s n),
      IsLiveState ℓ (T.stage s).coupling (T.stage s).labelWeight (stageState T s n a).1 (stageState T s n a).2.1
        (stageState T s n a).2.2 := by
  cases s with
  | zero => exact ae_of_all _ fun W => isLive_zero hF n hbs W
  | succ u =>
    have hu : u < k := hs
    have hfit := hF.fits
    have hforms := hF.wellPosed u hu
    have hmg := hF.condMean u hu n hbs (fun _ _ _ _ _ _ => 1)
      (measurable_const : Measurable fun _ : MarkedSample ℓ (u + 1) n => (1 : ℝ)) ⟨1, fun _ => (abs_one (α := ℝ)).le⟩
    have hP : IsProbabilityMeasure (markedSampleLaw T β (u + 1) n) :=
      (hT _ hfit hfit.depth_lt T hF.cutoff hF.marks β (fun _ => 0) (u + 1) n).1
    have hField : stageSigma T (u + 1) n ≤ markedSampleMeasurableSpace ℓ (u + 1) n := (hSt _ hfit T (u + 1) n).comap_le
    have hone := condExp_const (μ := markedSampleLaw T β (u + 1) n) hField (1 : ℝ)
    filter_upwards [hmg] with x hx
    have hm1 : caseMean (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup x.2.2.1) x.2.2.1
        (stageState T (u + 1) n x).2 (fun _ _ _ _ _ => 1) = 1 := by
      refine hx.symm.trans ?_
      exact congrFun hone x
    have hne : coarseStateWeight (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup x.2.2.1) x.2.2.1
        (stageState T (u + 1) n x).2 ≠ 0 := by
      intro h0
      unfold caseMean at hm1
      rw [h0, div_zero] at hm1
      exact zero_ne_one hm1
    have hhull : IsHullState ℓ (T.stage u).toStepSetup.nextRange x.2.2.1 (stageState T (u + 1) n x).2.1 :=
      hImg _ hfit _ _ hforms.range_le hforms.nextRange_ge n hbs.1 x.2.2.1 _ _
    refine ⟨hhull, ?_⟩
    show 0 < coarseWeightExpansion (T.stage u).toStepSetup n x.2.2.1 (stageState T (u + 1) n x).2.1 (stageState T (u + 1) n x).2.2
    unfold coarseWeightExpansion
    rw [dif_neg (NeZero.ne n)]
    exact lt_of_le_of_ne ENNReal.toReal_nonneg hne.symm
private theorem liveHull_bound {S : ScoredStageTower T} {β : ℝ} {k : ℕ} (hF : StageFacts S β k) (f : FinePlaquetteFunction)
    {s : ℕ} (hs : s ≤ k) (n : ℕ) [NeZero n] (hbs : IsBlockTorusSide ℓ n) (hn₀ : ℓ.n₀ ≤ n) (y : TorusSite n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q, |liveHull S f s n y q| ≤ C := by
  classical
  obtain ⟨B, hB0, hB⟩ := hF.scoreBounded s hs
  have hr := (hF.admissible s hs).bounds
  refine ⟨|(S.setup s).cold n y (trivialField n) (fineWeight f _)| +
    (|(S.setup s).responseParams.C₀| + B) * |weightNorm ℓ.side (T.stage s).depth (fineWeight f (fineSide ℓ.side (T.stage s).depth n))|,
    by positivity, fun q => ?_⟩
  unfold liveHull
  split_ifs with hl
  · have h1 := hr.size_hull n hbs y q.1 q.2.1 q.2.2 hl (fineWeight f _)
    have h2 : |siteScore (S.setup s).score q.2.1 q.2.2 y| ≤ B := by
      unfold siteScore
      split_ifs
      · exact hB _
      · simpa using hB0
    have h3 : ((S.setup s).responseParams.C₀ + siteScore (S.setup s).score q.2.1 q.2.2 y) *
          weightNorm ℓ.side (T.stage s).depth (fineWeight f (fineSide ℓ.side (T.stage s).depth n)) ≤
        (|(S.setup s).responseParams.C₀| + B) * |weightNorm ℓ.side (T.stage s).depth (fineWeight f (fineSide ℓ.side (T.stage s).depth n))| := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans (add_le_add le_rfl h2)) (abs_nonneg _)
    unfold centeredHullResponse at h1
    have h5 := abs_sub_abs_le_abs_sub ((S.setup s).hull n y q.1 q.2.1 q.2.2 (fineWeight f _))
      ((S.setup s).cold n y (trivialField n) (fineWeight f _))
    linarith
  · rw [abs_zero]
    positivity
private def blockCase (S : ScoredStageTower T) (f : FinePlaquetteFunction) {s n : ℕ} [NeZero n] (Y : TorusSite n) :
    TorusField n → CaseFunction (T.stage s).toStepSetup n :=
  fun V W Yt ωt _ b => ∑ y ∈ sitesInBlocks ℓ.side {Y}, liveHull S f s (n * ℓ.side) y (W, ⟨Yt, ωt⟩) +
    ℓ.coupling / 2 * (S.setup s).coeff * blockMean ℓ.side ((T.stage s).depth + 1) n Y (fineWeight f _) *
      bondScoresAtSite ℓ (T.stage s).coupling W V b Y
private theorem blockCase_of_live (S : ScoredStageTower T) (f : FinePlaquetteFunction) {s n : ℕ} [NeZero n] (Y : TorusSite n)
    (V : TorusField n) (W : TorusField (n * ℓ.side)) (Yt : Finset (TorusSite (n * ℓ.side))) (ωt : Yt → (T.stage s).labels.Ω)
    (bad : Finset (TorusBond (n * ℓ.side))) (b : BaseChoice ℓ.side n)
    (hl : IsLiveState ℓ (T.stage s).coupling (T.stage s).labelWeight W Yt ωt) :
    blockCase S f Y V W Yt ωt bad b = caseResponse (S.setup s) V Y (fineWeight f _) W Yt ωt bad b := by
  have e : ∑ y ∈ sitesInBlocks ℓ.side {Y}, liveHull S f s (n * ℓ.side) y (W, ⟨Yt, ωt⟩) =
      ∑ y ∈ sitesInBlocks ℓ.side {Y}, (S.setup s).hull (n * ℓ.side) y W Yt ωt (fineWeight f _) :=
    Finset.sum_congr rfl fun y _ => if_pos hl
  unfold blockCase caseResponse
  rw [e]
  rfl
private theorem caseTerm_blockCase (S : ScoredStageTower T) (f : FinePlaquetteFunction) {s n : ℕ} [NeZero n]
    (hrow : (T.stage s).toStepSetup.HasExpansions) (hbs : IsBlockTorusSide ℓ (n * ℓ.side)) (Y : TorusSite n)
    (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState (T.stage s).toStepSetup n)
    (bad : Finset (TorusBond (n * ℓ.side))) (Yt : Finset (TorusSite (n * ℓ.side))) (b : BaseChoice ℓ.side n)
    (W : TorusField (n * ℓ.side)) (ν : q.unlabelled Yt → (T.stage s).labels.Ω) :
    caseTerm (T.stage s).toStepSetup C V q (blockCase S f Y V) bad Yt b W ν =
      caseTerm (T.stage s).toStepSetup C V q (caseResponse (S.setup s) V Y (fineWeight f _)) bad Yt b W ν := by
  classical
  unfold caseTerm
  split_ifs with hc
  · have hD : 0 ≤ (T.stage s).labelWeight (n * ℓ.side) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) :=
      hrow.2.nonneg _ hbs _ Yt _ hc.1
    rcases hD.eq_or_lt with h0 | hpos
    · have hw : stepWeight (T.stage s).toStepSetup C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = 0 := by
        unfold stepWeight
        show (T.stage s).labelWeight (n * ℓ.side) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) * _ * _ * _ = 0
        rw [← h0]
        ring
      rw [hw, mul_zero, mul_zero]
    · rw [blockCase_of_live S f Y V _ Yt _ bad b ⟨hc.1, hpos⟩]
  · rfl
private theorem caseMean_blockCase (S : ScoredStageTower T) (f : FinePlaquetteFunction) {s n : ℕ} [NeZero n]
    (hrow : (T.stage s).toStepSetup.HasExpansions) (hbs : IsBlockTorusSide ℓ (n * ℓ.side)) (Y : TorusSite n)
    (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState (T.stage s).toStepSetup n) :
    caseMean (T.stage s).toStepSetup C V q (blockCase S f Y V) =
      caseMean (T.stage s).toStepSetup C V q (caseResponse (S.setup s) V Y (fineWeight f _)) := by
  have e : caseIntegral (T.stage s).toStepSetup C V q (blockCase S f Y V) =
      caseIntegral (T.stage s).toStepSetup C V q (caseResponse (S.setup s) V Y (fineWeight f _)) := by
    unfold caseIntegral
    simp only [caseTerm_blockCase S f hrow hbs Y C V q]
  unfold caseMean
  rw [e]
private theorem caseLift_blockCase (S : ScoredStageTower T) (f : FinePlaquetteFunction) {s n : ℕ} [NeZero n]
    (ht : (T.stage s).depth = s) (Y : TorusSite n) (x : MarkedSample ℓ (s + 1) n) :
    caseLift T s n (blockCase S f Y) x =
      ∑ y ∈ sitesInBlocks ℓ.side {Y}, liveHull S f s (n * ℓ.side) y (stageState T s (n * ℓ.side) x.1) +
        ℓ.coupling / 2 * (S.setup s).coeff * blockMean ℓ.side (s + 1) n Y (fineWeight f _) *
          bondScoresAtSite ℓ (T.stage s).coupling (topField ℓ s (n * ℓ.side) x.1) x.2.2.1 x.2.1 Y := by
  have e : ((topField ℓ s (n * ℓ.side) x.1,
      ⟨(stageState T s (n * ℓ.side) x.1).2.1, (stageState T s (n * ℓ.side) x.1).2.2⟩) :
      StageState T s (n * ℓ.side)) = stageState T s (n * ℓ.side) x.1 := by
    rw [← stageState_fst]
  show ∑ y ∈ sitesInBlocks ℓ.side {Y}, liveHull S f s (n * ℓ.side) y
      (topField ℓ s (n * ℓ.side) x.1, ⟨(stageState T s (n * ℓ.side) x.1).2.1, (stageState T s (n * ℓ.side) x.1).2.2⟩) +
    ℓ.coupling / 2 * (S.setup s).coeff * blockMean ℓ.side ((T.stage s).depth + 1) n Y (fineWeight f _) *
      bondScoresAtSite ℓ (T.stage s).coupling (topField ℓ s (n * ℓ.side) x.1) x.2.2.1 x.2.1 Y = _
  rw [e, blockMean_depth ℓ.side f (congrArg (· + 1) ht) n Y]
private theorem sum_caseLift_blockCase (S : ScoredStageTower T) (f : FinePlaquetteFunction) {s n : ℕ} [NeZero n]
    (ht : (T.stage s).depth = s) (x : MarkedSample ℓ (s + 1) n) :
    ∑ Y : TorusSite n, caseLift T s n (blockCase S f Y) x =
      ∑ y : TorusSite (n * ℓ.side), liveHull S f s (n * ℓ.side) y (stageState T s (n * ℓ.side) x.1) +
        sourceTerm T S.coeffs s n (fineWeight f _) x := by
  rw [Finset.sum_congr rfl fun Y _ => caseLift_blockCase S f ht Y x, Finset.sum_add_distrib,
    sum_over_blocks ℓ.side fun y => liveHull S f s (n * ℓ.side) y (stageState T s (n * ℓ.side) x.1)]
  congr 1
  show _ = ℓ.coupling / 2 * (S.setup s).coeff * ∑ Y : TorusSite n, blockMean ℓ.side (s + 1) n Y (fineWeight f _) *
    ∑ i : Fin 4, (bondScore ℓ (T.stage s).coupling (topField ℓ s (n * ℓ.side) x.1) x.2.2.1 x.2.1 (Y, i) +
      bondScore ℓ (T.stage s).coupling (topField ℓ s (n * ℓ.side) x.1) x.2.2.1 x.2.1 (Y - unitStep n i, i))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  unfold bondScoresAtSite
  ring
private theorem response_ae_eq_sum (hSt : StageStatesMeasurableStatement) (hT : TwoPointByTotalCovarianceStatement)
    (hPast : MarkovPropertyOfStageStates) (hSc : BondScoreProperties) (hImg : CoarseHullIsHullState)
    {S : ScoredStageTower T} {β : ℝ} {k : ℕ} (hF : StageFacts S β k) (f : FinePlaquetteFunction) (s : ℕ) :
    s ≤ k → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n →
      response T β S.coeffs s n (fineWeight f _) =ᵐ[markedSampleLaw T β s n]
        fun a => ∑ y : TorusSite n, liveHull S f s n y (stageState T s n a) := by
  induction s with
  | zero =>
    intro _ n _ hbs
    refine ae_of_all _ fun W => ?_
    have hl := isLive_zero hF n hbs W
    have e : ∀ y : TorusSite n, liveHull S f 0 n y (stageState T 0 n W) = siteResponse y W (fineWeight f n) := fun y =>
      (if_pos hl).trans (hF.hull_zero n y W _ _ f)
    have hw := (siteResponse_total (fineWeight f n) (show TorusField n from W)).symm.trans
      (Finset.sum_congr rfl fun y _ => (e y).symm)
    exact hw
  | succ s ih =>
    intro hs n _ hbs
    classical
    have hlt : s < k := hs
    have hf := hF.fits
    have hLpos : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne _)
    have hbsL : IsBlockTorusSide ℓ (n * ℓ.side) := ⟨Dvd.intro_left _ rfl, hbs.2.trans (Nat.le_mul_of_pos_right _ hLpos)⟩
    have hn₀ : ℓ.n₀ ≤ n * ℓ.side := (Nat.le_mul_of_pos_left _ hLpos).trans hbsL.2
    have hP : IsProbabilityMeasure (markedSampleLaw T β (s + 1) n) :=
      (hT ℓ hf hf.depth_lt T hF.cutoff hF.marks β (fun _ => 0) (s + 1) n).1
    have hτ : Measurable (stageState T s (n * ℓ.side)) := hSt ℓ hf T s (n * ℓ.side)
    have hπ := (hPast ℓ hf hf.depth_lt T hF.cutoff hF.marks β s n).1
    have ht := hF.depth s
    have hlive := isLive_ae hSt hT hImg hF (s + 1) hs n hbs
    have hih := hπ.quasiMeasurePreserving.ae (ih hlt.le (n * ℓ.side) hbsL)
    have hlm : ∀ y : TorusSite (n * ℓ.side), Measurable (liveHull S f s (n * ℓ.side) y) := fun y =>
      measurable_of_prod_sigma fun Yt => (hF.admissible s hlt.le).bounds.hull_borel _ hbsL y Yt _
    have hfst : Measurable fun x : MarkedSample ℓ (s + 1) n => stageState T s (n * ℓ.side) x.1 := hτ.comp hπ.measurable
    have htop : Measurable (topField ℓ s (n * ℓ.side)) := by
      have e : topField ℓ s (n * ℓ.side) = fun a => (stageState T s (n * ℓ.side) a).1 :=
        funext fun a => (stageState_fst T s _ a).symm
      rw [e]
      exact measurable_fst.comp hτ
    have hdraw : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
        ((topField ℓ s (n * ℓ.side) u.1, u.2) : TorusField (n * ℓ.side) × StepOutcome ℓ n) :=
      (htop.comp measurable_fst).prodMk measurable_snd
    have hm : ∀ Y : TorusSite n, Measurable (caseLift T s n (blockCase S f Y)) := fun Y => by
      have e : caseLift T s n (blockCase S f Y) = fun x =>
          ∑ y ∈ sitesInBlocks ℓ.side {Y}, liveHull S f s (n * ℓ.side) y (stageState T s (n * ℓ.side) x.1) +
            ℓ.coupling / 2 * (S.setup s).coeff * blockMean ℓ.side (s + 1) n Y (fineWeight f _) *
              bondScoresAtSite ℓ (T.stage s).coupling (topField ℓ s (n * ℓ.side) x.1) x.2.2.1 x.2.1 Y :=
        funext (caseLift_blockCase S f ht Y)
      rw [e]
      have h3 := (measurable_bondScoresAtSite hSc hf (T.stage s).coupling (n := n) Y).comp hdraw
      have h2 : Measurable fun x : MarkedSample ℓ (s + 1) n =>
          bondScoresAtSite ℓ (T.stage s).coupling (topField ℓ s (n * ℓ.side) x.1) x.2.2.1 x.2.1 Y := h3
      exact (Finset.measurable_sum _ fun y _ => (hlm y).comp hfst).add (h2.const_mul _)
    have hb : ∀ Y : TorusSite n, ∃ C : ℝ, ∀ x, |caseLift T s n (blockCase S f Y) x| ≤ C := fun Y => by
      choose Cf _ hCf using fun y : TorusSite (n * ℓ.side) => liveHull_bound hF f hlt.le (n * ℓ.side) hbsL hn₀ y
      refine ⟨∑ y ∈ sitesInBlocks ℓ.side {Y}, Cf y +
        |ℓ.coupling / 2 * (S.setup s).coeff * blockMean ℓ.side (s + 1) n Y (fineWeight f _)| * 16, fun x => ?_⟩
      rw [caseLift_blockCase S f ht Y x]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => hCf y _)
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (bondScoresAtSite_bound hSc hf _ _ _ _ _) (abs_nonneg _)
    have hI : ∀ Y : TorusSite n, Integrable (caseLift T s n (blockCase S f Y)) (markedSampleLaw T β (s + 1) n) := fun Y => by
      obtain ⟨C, hC⟩ := hb Y
      exact Integrable.of_bound (hm Y).aestronglyMeasurable C (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hC x)
    have hread : ∀ᵐ x ∂(markedSampleLaw T β (s + 1) n), ∀ Y : TorusSite n,
        ((markedSampleLaw T β (s + 1) n)[caseLift T s n (blockCase S f Y) | stageSigma T (s + 1) n]) x =
          caseMeanAtSample T s n (blockCase S f Y) x :=
      ae_all_iff.2 fun Y => hF.condMean s hlt n hbs _ (hm Y) (hb Y)
    have hsum := condExp_finsetSum (μ := markedSampleLaw T β (s + 1) n) (s := Finset.univ)
      (f := fun Y : TorusSite n => caseLift T s n (blockCase S f Y)) (fun Y _ => hI Y) (stageSigma T (s + 1) n)
    have hX : (fun u : MarkedSample ℓ (s + 1) n => response T β S.coeffs s (n * ℓ.side) (fineWeight f _) u.1 +
        sourceTerm T S.coeffs s n (fineWeight f _) u) =ᵐ[markedSampleLaw T β (s + 1) n]
        ∑ Y : TorusSite n, caseLift T s n (blockCase S f Y) := hih.mono fun x hx => by
      rw [Finset.sum_apply, sum_caseLift_blockCase S f ht x]
      exact congrArg (· + sourceTerm T S.coeffs s n (fineWeight f _) x) hx
    have hc := condExp_congr_ae (m := stageSigma T (s + 1) n) hX
    filter_upwards [hc, hsum, hread, hlive] with x h1 h2 h3 h4
    show ((markedSampleLaw T β (s + 1) n)[fun u : MarkedSample ℓ (s + 1) n =>
        response T β S.coeffs s (n * ℓ.side) (fineWeight f _) u.1 + sourceTerm T S.coeffs s n (fineWeight f _) u |
        stageSigma T (s + 1) n]) x = _
    rw [h1, h2, Finset.sum_apply]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [h3 Y]
    show caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup x.2.2.1) x.2.2.1 (stageState T (s + 1) n x).2
      (blockCase S f Y x.2.2.1) = _
    refine (caseMean_blockCase S f (hF.expansions s hlt.le) hbsL Y _ _ _).trans ?_
    show _ = if IsLiveState ℓ (T.stage (s + 1)).coupling (T.stage (s + 1)).labelWeight (stageState T (s + 1) n x).1
      (stageState T (s + 1) n x).2.1 (stageState T (s + 1) n x).2.2 then
        (S.setup (s + 1)).hull n Y (stageState T (s + 1) n x).1 (stageState T (s + 1) n x).2.1
          (stageState T (s + 1) n x).2.2 (fineWeight f _) else 0
    rw [if_pos h4, hF.hull_succ s hlt]
    rfl
end Core
private theorem FollowsFlow.of_le {Tb : ParameterAssignment} {y : ℝ} {T : StageTower (Tb.stepParameters y)}
    {S : ScoredStageTower T} {β : ℝ} {k tp : ℕ} (h : S.FollowsFlow β tp) (hk : k ≤ tp) : S.FollowsFlow β k :=
  ⟨fun u hu => h.isFlowStep u (hu.trans hk), h.startsAtWilson, h.bottom_coupling, h.isCutoff_bottom, h.marksMeasurable,
    h.params_eq, h.N₀_eq, h.coeff_zero, h.score_zero, h.cold_zero, h.hull_zero,
    fun u hu => h.score_succ u (lt_of_lt_of_le hu hk), fun u hu => h.cold_succ u (lt_of_lt_of_le hu hk),
    fun u hu => h.hull_succ u (lt_of_lt_of_le hu hk), fun u hu => h.isAdmissible u (hu.trans hk),
    fun u hu => h.coeff_near_one u (hu.trans hk)⟩
theorem chainResponseLocality_holds (hC : scoredTowerColdResponseEq) (hG : conditionalMeanIsCaseMeanStatement)
    (hT : TwoPointByTotalCovarianceStatement) (hSt : StageStatesMeasurableStatement)
    (hPast : MarkovPropertyOfStageStates) (hSc : BondScoreProperties) (hImg : CoarseHullIsHullState)
    (hFl : EventuallyFloorConditions) (hRow : expansionAlongFlow) : chainResponseLocalityStatement := by
  intro a ha
  obtain ⟨L₁, r₁, c₁, hr₁, H₁⟩ := hC a ha
  obtain ⟨L₂, r₂, hr₂, H₂⟩ := hG a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), c₁, fun c => lt_min (hr₁ c) (hr₂ c),
    fun L hL hL₀ Tb hTa hTL hD hCS hCH hr hCd => ?_⟩
  obtain ⟨y₁, Y₁⟩ := H₁ L hL ((le_max_left _ _).trans hL₀) Tb hTa hTL hD hCS hCH (hr.trans (min_le_left _ _)) hCd
  obtain ⟨y₂, Y₂⟩ := H₂ L hL ((le_max_right _ _).trans hL₀) Tb hTa hTL hD (hr.trans (min_le_right _ _))
  have hCpos : (0 : ℝ) < 2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 17 := by positivity
  obtain ⟨y₃, Y₃⟩ := hFl Tb hD _ 1 hCpos one_pos
  refine ⟨max (max y₁ y₂) (max y₃ (max Tb.floorMin 1)), fun y hy hret hW => ?_⟩
  have hy₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy₂ : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy₃ : y₃ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy₀ : Tb.floorMin ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hy1 : 1 ≤ y := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y hy₀
  have hRS : ExpansionHolds (Tb.stepParameters y) := ⟨hret, fun β hβ => hW β hβ⟩
  intro Kr hKr
  refine ⟨(Tb.stepParameters y).decayRate, 0, ?_, ?_⟩
  · have := hfit.rt_pos
    unfold StepParameters.decayRate
    positivity
  intro T S β k tp hk hSK hOR hfl hx₀ n _ hbs h
  have hS : S.FollowsFlow β k := FollowsFlow.of_le hOR hk
  have hRR : CouplingsAboveFloor (Tb.stepParameters y) β k := fun j hj => by
    have h1 := (hS.isFlowStep j hj).onFamily.le_coupling
    rw [(hS.isFlowStep j hj).coupling_eq] at h1
    exact h1
  have hdepth : ∀ u, (T.stage u).depth = u := by
    intro u
    induction u with
    | zero => exact hS.startsAtWilson.depth_eq
    | succ u ih =>
      show (T.stage u).depth + 1 = u + 1
      rw [ih]
  have hforms : ∀ u < k, (T.stage u).toStepSetup.IsWellPosed := fun u hu => by
    have hst := hS.isFlowStep u hu.le
    have hmoved : |(T.stage u).toStepSetup.nextCoupling - (T.stage u).toStepSetup.coupling| ≤ 2 * Tb.B := by
      rw [hst.nextCoupling_eq, hst.coupling_eq]
      exact (hRow _ hRS β k hRR).2 u hu
    have harr : (T.stage u).toStepSetup.IsSymmetricWeight := by
      have h1 := (hRow _ hRS β u (fun j hj => hRR j (by omega))).1.1
      show ∀ (n : ℕ) [NeZero n], (T.stage u).toStepSetup.params.n₀ ≤ n → _
      rw [hst.functional_eq]
      exact h1
    exact isWellPosed_of_onParameters hD hy₀ hy1 hst.onFamily hmoved harr (Y₃ _ (hy₃.trans hst.onFamily.le_coupling))
  have hscore : ∀ s ≤ k, ∃ B : ℝ, 0 ≤ B ∧ ∀ w, |(S.setup s).score w| ≤ B := by
    intro s
    induction s with
    | zero =>
      intro _
      refine ⟨0, le_rfl, fun w => ?_⟩
      rw [hS.score_zero w, abs_zero]
    | succ s ih =>
      intro hs
      obtain ⟨B, hB0, hB⟩ := ih (by omega)
      refine ⟨|S.params.s₁| + (Fintype.card (BlockOffset (Tb.stepParameters y).side) : ℝ) * B, by positivity, fun w => ?_⟩
      have e := congrFun (hS.score_succ s hs) w
      rw [e]
      exact coarseLabelScore_bound S.params.s₁ (S.setup s).score B hB0 hB w
  have hF : StageFacts S β k :=
    { fits := hfit
      cutoff := hS.isCutoff_bottom
      marks := hS.marksMeasurable
      start := hS.startsAtWilson
      expansions := fun u hu => (hS.isFlowStep u hu).onFamily.isStep.1
      admissible := hS.isAdmissible
      scoreBounded := hscore
      depth := hdepth
      hull_zero := hS.hull_zero
      hull_succ := hS.hull_succ
      wellPosed := hforms
      condMean := fun u hu n _ hbs F hm hb => Y₂ y hy₂ hret hW T β u n
        ⟨hS.startsAtWilson, fun j hj => (hS.isFlowStep j (by omega)).coupling_eq,
          fun j hj => (hS.isFlowStep j (by omega)).onFamily⟩
        hS.isCutoff_bottom hS.marksMeasurable (hforms u hu)
        ⟨Dvd.intro_left _ rfl, hbs.2.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne _)))⟩ hbs.1 F hm hb }
  have hLpos : 0 < (Tb.stepParameters y).side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn₀ : (Tb.stepParameters y).n₀ ≤ n := (Nat.le_mul_of_pos_left _ hLpos).trans hbs.2
  have hσ : 0 < (Tb.stepParameters y).threshold := hD.σ_pos
  have hcoldFlat : ∀ (m : ℕ) [NeZero m], IsCold (Tb.stepParameters y).threshold (trivialField m) :=
    fun m _ => isCold_trivialField m hσ
  have hTie := Y₁ y hy₁ hret hW β k T S hS
  have hrr := (hS.isAdmissible k le_rfl).bounds
  have hA : response T β S.coeffs k n h = response T β S.coeffs k n (fineWeight (fineOf h) _) :=
    response_congr T β _ k n _ _ fun p hp => (fineOf_eq h p hp).symm
  have hflat : ∀ z : TorusSite n, (S.setup k).cold n z (trivialField n) (fineWeight (fineOf h) _) =
      coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) S.coeffs k n z (trivialField n) h :=
    fun z => hTie n hn₀ z _ (hcoldFlat n) (fineOf h) h fun p hp => fineOf_eq h p hp
  filter_upwards [response_ae_eq_sum hSt hT hPast hSc hImg hF (fineOf h) k le_rfl n hbs,
    isLive_ae hSt hT hImg hF k le_rfl n hbs] with u h1 h2
  refine ⟨fun z => (S.setup k).hull n z (stageState T k n u).1 (stageState T k n u).2.1 (stageState T k n u).2.2
      (fineWeight (fineOf h) _) -
    coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) S.coeffs k n z (trivialField n) h,
    ?_, ?_, ?_⟩
  · rw [hA, h1, Finset.sum_sub_distrib, sub_add_cancel]
    exact Finset.sum_congr rfl fun z _ => if_pos h2
  · intro z hz
    have hz0 := fine_off (Tb.stepParameters y).side (hdepth k) n z h hz
    have hQ : (S.setup k).hull n z (stageState T k n u).1 (stageState T k n u).2.1 (stageState T k n u).2.2
        (fineWeight (fineOf h) _) = 0 := by
      have r1 := hrr.hull_reads n hbs z _ _ _ h2 _
        (0 : PlaquetteWeight (fineSide (Tb.stepParameters y).side (T.stage k).depth n)) hz0
      have r2 := hrr.hull_linear n hbs z _ _ _ h2 (-1)
        (0 : PlaquetteWeight (fineSide (Tb.stepParameters y).side (T.stage k).depth n)) 0
      have e : ((-1 : ℝ) • (0 : PlaquetteWeight (fineSide (Tb.stepParameters y).side (T.stage k).depth n)) + 0) = 0 := by
        simp
      rw [e] at r2
      rw [r1]
      linarith
    have hPz : coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) S.coeffs k n z
        (trivialField n) h = 0 := by
      rw [← hflat z]
      have r1 := hrr.cold_reads n hn₀ z (trivialField n) (hcoldFlat n) _
        (0 : PlaquetteWeight (fineSide (Tb.stepParameters y).side (T.stage k).depth n)) hz0
      have r2 := hrr.cold_linear n hn₀ z (trivialField n) (hcoldFlat n) (-1)
        (0 : PlaquetteWeight (fineSide (Tb.stepParameters y).side (T.stage k).depth n)) 0
      have e : ((-1 : ℝ) • (0 : PlaquetteWeight (fineSide (Tb.stepParameters y).side (T.stage k).depth n)) + 0) = 0 := by
        simp
      rw [e] at r2
      rw [r1]
      linarith
    show _ - _ = (0 : ℝ)
    rw [hQ, hPz, sub_zero]
  · intro z n' _ W' z' m ω' h' hn' hcold hm hagree hwa
    have hx : (T.stage k).coupling = flowCouplings (Tb.stepParameters y) β k := (hS.isFlowStep k le_rfl).coupling_eq
    have hm' : (clusterRange (T.stage k).coupling : ℝ) / 64 ≤ m := by
      rw [hx]
      exact hm
    have hzY : z ∉ (stageState T k n u).2.1 := by
      intro hzY
      have hin : OffsetInBox m (0 : Fin 4 → ℤ) := fun i => by simp
      have e0 : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite n) = 0 := by
        funext i
        simp [siteOfInt]
      have := (hagree.2.2.2.1 0 hin).1 (by rw [e0, add_zero]; exact hzY)
      simp at this
    have hfc := hrr.forget_cold n n' hbs hn' (stageState T k n u).1 W' (stageState T k n u).2.1 (stageState T k n u).2.2 ω'
      z z' m (fineWeight (fineOf h) _) (fineWeight (fineOf h') _) h2 hcold hm' hagree
      (fine_agree (Tb.stepParameters y).side (hdepth k) z z' h h' hwa)
    have e1 : centeredHullResponse (S.setup k).cold (S.setup k).hull n z (stageState T k n u).1 (stageState T k n u).2.1
        (stageState T k n u).2.2 (fineWeight (fineOf h) _) =
        (S.setup k).hull n z (stageState T k n u).1 (stageState T k n u).2.1 (stageState T k n u).2.2
          (fineWeight (fineOf h) _) -
        coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) S.coeffs k n z (trivialField n) h := by
      unfold centeredHullResponse
      rw [hflat z]
    have e2 : centeredResponse (S.setup k).cold n' z' W' (fineWeight (fineOf h') _) =
        centeredResponse (coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) S.coeffs k)
          n' z' W' h' := by
      unfold centeredResponse
      rw [hTie n' hn' z' W' hcold (fineOf h') h' fun p hp => fineOf_eq h' p hp,
        hTie n' hn' z' (trivialField n') (hcoldFlat n') (fineOf h') h' fun p hp => fineOf_eq h' p hp]
    have e3 : siteScore (S.setup k).score (stageState T k n u).2.1 (stageState T k n u).2.2 z = 0 := by
      unfold siteScore
      rw [dif_neg hzY]
    have e4 := fine_norm (Tb.stepParameters y).side (hdepth k) n h
    rw [e1, e2, e3, e4, add_zero, one_mul, neg_mul] at hfc
    exact hfc
end YangMills.Construction.ResponseInTheExpansion
end

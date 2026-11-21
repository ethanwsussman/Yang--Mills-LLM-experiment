import YangMills.Construction.CellOfTheFlow.TheDrawsStandOnGroundsProof
import YangMills.Construction.FreeEnergiesOfTheFlow.CompletedObservablesAreBounded
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.MeansOfTheVariablesAreBorel
import YangMills.Construction.LawByMomentsOfTheFlow.FunctionsOfTheLimitField
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.TelescopeDefs
import Mathlib
import YangMills.Construction.LawByMomentsOfTheFlow.ScoresUnderTheSizesOfTheHull
import YangMills.Construction.LawByMomentsOfTheFlow.SizesAlongTheTelescope
import YangMills.Construction.LawByMomentsOfTheFlow.TelescopeOfAPoint
import YangMills.Construction.LawByMomentsOfTheFlow.VariablesOfAPointSplit
import YangMills.Construction.LawByMomentsOfTheFlow.WeightsAndSitesBelowTheScale
set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open ChainNoise MomentMethod
def telescopeMomentsStatement : Prop :=
  ForAllHullParameters fun Λ => ∀ (S : MomentPoint Λ) (rule : NoiseRule Λ.stepParams) (ms : ℕ → ℕ)
    (Sq : ℕ → MomentPoint Λ) (p : ℕ),
    rule.IsAdmissible S.tower → 1 ≤ p → StrictMono ms → (∀ i, ∃ hp hs, Sq i = S.withSideExponent (ms i) hp hs) →
    (∀ u ≤ S.data.scaleLevel, ∀ i : Fin Λ.k,
      TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (responseAtLevel u i))) ∧
    (∀ u < S.data.scaleLevel, ∀ i : Fin Λ.k,
      TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (centredStepScore u i))) ∧
    (∀ u < S.data.scaleLevel, ∀ J : Finset (Fin Λ.k),
      TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (variableProduct u J))) ∧
    (∀ u ≤ S.data.windowLevel, ∀ (z : Fin 4 → ℤ) (k : ℕ),
      TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (hullSizePower u z k))) ∧
    (∀ u, (∀ m, u < (Sq m).lastSeparated) → ∀ J : Finset (Fin Λ.k), J.Nonempty →
      TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (variableMean u J))) ∧
    ∀ (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)),
      TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (completedProduct c B))
end YangMills.Construction.MomentLaw
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open TorusLumps TorusFields StepSettings RenormalizationStepParameters WeightedResponses ResponseInTheExpansion HullTrees ChainNoise MomentMethod LevelTestFunctions
section Moments
variable {T : TranslatedLaws}
private theorem mul_pow_le_pow_add_pow (x y : ℝ) (_hx : 0 ≤ x) (_hy : 0 ≤ y) (q : ℕ) : (x * y) ^ q ≤ x ^ (2 * q) + y ^ (2 * q) := by
  have h1 : x ^ (2 * q) = (x ^ q) ^ 2 := by rw [← pow_mul, mul_comm]
  have h2 : y ^ (2 * q) = (y ^ q) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [mul_pow, h1, h2]
  nlinarith [sq_nonneg (x ^ q - y ^ q), sq_nonneg (x ^ q), sq_nonneg (y ^ q)]
private theorem add_pow_le_two_pow_mul (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (q : ℕ) : (x + y) ^ q ≤ 2 ^ q * x ^ q + 2 ^ q * y ^ q := by
  have h2 : (0 : ℝ) ≤ 2 ^ q := by positivity
  rcases le_total x y with h | h
  · calc (x + y) ^ q ≤ (2 * y) ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
      _ = 2 ^ q * y ^ q := mul_pow _ _ _
      _ ≤ _ := by nlinarith [mul_nonneg h2 (pow_nonneg hx q)]
  · calc (x + y) ^ q ≤ (2 * x) ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
      _ = 2 ^ q * x ^ q := mul_pow _ _ _
      _ ≤ _ := by nlinarith [mul_nonneg h2 (pow_nonneg hy q)]
abbrev _root_.YangMills.SharedProofs.p63544 := @add_pow_le_two_pow_mul
private theorem aemeasurable_ofReal_mul_abs_pow {X : T.Family} (hX : TranslatedLaws.HasBoundedMoments X) (i : ℕ) (q : ℕ) (c : ℝ) :
    AEMeasurable (fun ω => ENNReal.ofReal (c * |X i ω| ^ q)) (T.μ i) :=
  ENNReal.measurable_ofReal.comp_aemeasurable (((hX.aemeasurable i).abs.pow_const q).const_mul c)
private theorem hasBoundedMoments_mul {X Y : T.Family} (hX : TranslatedLaws.HasBoundedMoments X) (hY : TranslatedLaws.HasBoundedMoments Y) :
    TranslatedLaws.HasBoundedMoments (T := T) (fun i ω => X i ω * Y i ω) where
  aemeasurable i := (hX.aemeasurable i).mul (hY.aemeasurable i)
  moment_bound q := by
    obtain ⟨C₁, h₁⟩ := hX.moment_bound (2 * q)
    obtain ⟨C₂, h₂⟩ := hY.moment_bound (2 * q)
    refine ⟨|C₁| + |C₂|, fun i => ?_⟩
    calc ∫⁻ ω, ENNReal.ofReal (|X i ω * Y i ω| ^ q) ∂(T.μ i)
        ≤ ∫⁻ ω, (ENNReal.ofReal (|X i ω| ^ (2 * q)) + ENNReal.ofReal (|Y i ω| ^ (2 * q))) ∂(T.μ i) := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), abs_mul]
          exact ENNReal.ofReal_le_ofReal (mul_pow_le_pow_add_pow _ _ (abs_nonneg _) (abs_nonneg _) q)
      _ = ∫⁻ ω, ENNReal.ofReal (|X i ω| ^ (2 * q)) ∂(T.μ i) + ∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ (2 * q)) ∂(T.μ i) := by
          refine lintegral_add_left' ?_ _
          simpa using aemeasurable_ofReal_mul_abs_pow hX i (2 * q) 1
      _ ≤ ENNReal.ofReal C₁ + ENNReal.ofReal C₂ := add_le_add (h₁ i) (h₂ i)
      _ ≤ ENNReal.ofReal |C₁| + ENNReal.ofReal |C₂| :=
          add_le_add (ENNReal.ofReal_le_ofReal (le_abs_self _)) (ENNReal.ofReal_le_ofReal (le_abs_self _))
      _ = _ := (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)).symm
private theorem hasBoundedMoments_add {X Y : T.Family} (hX : TranslatedLaws.HasBoundedMoments X) (hY : TranslatedLaws.HasBoundedMoments Y) :
    TranslatedLaws.HasBoundedMoments (T := T) (fun i ω => X i ω + Y i ω) where
  aemeasurable i := (hX.aemeasurable i).add (hY.aemeasurable i)
  moment_bound q := by
    obtain ⟨C₁, h₁⟩ := hX.moment_bound q
    obtain ⟨C₂, h₂⟩ := hY.moment_bound q
    refine ⟨2 ^ q * |C₁| + 2 ^ q * |C₂|, fun i => ?_⟩
    have h2 : (0 : ℝ) ≤ 2 ^ q := by positivity
    have e : ∀ Z : T.Family, ∫⁻ ω, ENNReal.ofReal (2 ^ q * |Z i ω| ^ q) ∂(T.μ i) =
        ENNReal.ofReal (2 ^ q) * ∫⁻ ω, ENNReal.ofReal (|Z i ω| ^ q) ∂(T.μ i) := by
      intro Z
      simp_rw [ENNReal.ofReal_mul h2]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    calc ∫⁻ ω, ENNReal.ofReal (|X i ω + Y i ω| ^ q) ∂(T.μ i)
        ≤ ∫⁻ ω, (ENNReal.ofReal (2 ^ q * |X i ω| ^ q) + ENNReal.ofReal (2 ^ q * |Y i ω| ^ q)) ∂(T.μ i) := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          exact (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) q).trans (add_pow_le_two_pow_mul _ _ (abs_nonneg _) (abs_nonneg _) q)
      _ = ∫⁻ ω, ENNReal.ofReal (2 ^ q * |X i ω| ^ q) ∂(T.μ i) + ∫⁻ ω, ENNReal.ofReal (2 ^ q * |Y i ω| ^ q) ∂(T.μ i) :=
          lintegral_add_left' (aemeasurable_ofReal_mul_abs_pow hX i q _) _
      _ = ENNReal.ofReal (2 ^ q) * ∫⁻ ω, ENNReal.ofReal (|X i ω| ^ q) ∂(T.μ i) +
            ENNReal.ofReal (2 ^ q) * ∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ q) ∂(T.μ i) := by rw [e X, e Y]
      _ ≤ ENNReal.ofReal (2 ^ q) * ENNReal.ofReal |C₁| + ENNReal.ofReal (2 ^ q) * ENNReal.ofReal |C₂| := by
          gcongr
          · exact (h₁ i).trans (ENNReal.ofReal_le_ofReal (le_abs_self _))
          · exact (h₂ i).trans (ENNReal.ofReal_le_ofReal (le_abs_self _))
      _ = _ := by
          rw [← ENNReal.ofReal_mul h2, ← ENNReal.ofReal_mul h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
private theorem hasBoundedMoments_const (hT : T.IsPreserving) (a : ℕ → ℝ) (b : ℝ) (ha : ∀ i, |a i| ≤ b) :
    TranslatedLaws.HasBoundedMoments (T := T) (fun i _ => a i) where
  aemeasurable _ := aemeasurable_const
  moment_bound q := by
    refine ⟨b ^ q, fun i => ?_⟩
    have := hT.isProbability i
    calc ∫⁻ _, ENNReal.ofReal (|a i| ^ q) ∂(T.μ i) = ENNReal.ofReal (|a i| ^ q) := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) (ha i) q)
private theorem hasBoundedMoments_sum (hT : T.IsPreserving) {ι : Type} (s : Finset ι) {X : ι → T.Family}
    (hX : ∀ a ∈ s, TranslatedLaws.HasBoundedMoments (X a)) :
    TranslatedLaws.HasBoundedMoments (T := T) (fun i ω => ∑ a ∈ s, X a i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasBoundedMoments_const hT (fun _ => 0) 0 (fun _ => by simp)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact hasBoundedMoments_add (hX a (Finset.mem_insert_self _ _)) (ih fun b hb => hX b (Finset.mem_insert_of_mem hb))
abbrev _root_.YangMills.SharedProofs.p71872 := @hasBoundedMoments_sum
private theorem hasBoundedMoments_prod (hT : T.IsPreserving) {ι : Type} (s : Finset ι) {X : ι → T.Family}
    (hX : ∀ a ∈ s, TranslatedLaws.HasBoundedMoments (X a)) :
    TranslatedLaws.HasBoundedMoments (T := T) (fun i ω => ∏ a ∈ s, X a i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasBoundedMoments_const hT (fun _ => 1) 1 (fun _ => by simp)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact hasBoundedMoments_mul (hX a (Finset.mem_insert_self _ _)) (ih fun b hb => hX b (Finset.mem_insert_of_mem hb))
abbrev _root_.YangMills.SharedProofs.p24142 := @hasBoundedMoments_prod
private theorem hasBoundedMoments_of_abs_le {X Y : T.Family} (hY : TranslatedLaws.HasBoundedMoments Y)
    (hX : ∀ i, AEMeasurable (X i) (T.μ i))
    (hb : ∀ i, ∀ᵐ ω ∂(T.μ i), |X i ω| ≤ |Y i ω|) : TranslatedLaws.HasBoundedMoments X where
  aemeasurable := hX
  moment_bound q := by
    obtain ⟨C, h⟩ := hY.moment_bound q
    refine ⟨C, fun i => (lintegral_mono_ae ?_).trans (h i)⟩
    filter_upwards [hb i] with ω hω
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) hω q)
private theorem hasBoundedMoments_abs {X : T.Family} (hX : TranslatedLaws.HasBoundedMoments X) :
    TranslatedLaws.HasBoundedMoments (T := T) (fun i ω => |X i ω|) :=
  hasBoundedMoments_of_abs_le hX (fun i => (hX.aemeasurable i).abs) fun i => Eventually.of_forall fun ω => by simp
private theorem hasBoundedMoments_congr {X Y : T.Family} (hY : TranslatedLaws.HasBoundedMoments Y)
    (h : ∀ i, ∀ᵐ ω ∂(T.μ i), X i ω = Y i ω) : TranslatedLaws.HasBoundedMoments X :=
  hasBoundedMoments_of_abs_le hY (fun i => (hY.aemeasurable i).congr ((h i).mono fun _ hω => hω.symm))
    fun i => (h i).mono fun ω hω => by rw [hω]
end Moments
section Point
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem next_density_siteDensity_eq {ℓ : TorusLumps.StepParameters} {c : ChainStage ℓ}
    {h h' : ClusterExpansionOfAStep.CoarseLabelFacts c.toStepSetup} {x x' : ℝ} {f f' : LocalDensity}
    {φ φ' : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → CoarseLabel c.labels.Ω ℓ.side) → ℝ}
    (e : c.next h x f φ = c.next h' x' f' φ') : f = f' ∧ φ = φ' := by
  have hφ : ∀ {c₁ c₂ : ChainStage ℓ}, c₁ = c₂ → HEq c₁.siteDensity c₂.siteDensity := by
    rintro _ _ rfl
    rfl
  exact ⟨congrArg ChainStage.density e, eq_of_heq (hφ e)⟩
private theorem stage_eq_flowStages {t : ℕ} (ht : t ≤ S.data.windowLevel) :
    S.tower.stage t = (flowStages Λ.table Λ.floor S.β S.labelFacts S.initial t).1 :=
  congrArg Sigma.fst (S.stage_eq t ht)
private theorem stageOnFlow_of_le {t : ℕ} (ht : t ≤ S.data.windowLevel) :
    StageOnFlow Λ.table Λ.response Λ.floor S.β t ⟨S.tower.stage t, S.resp t⟩ := by apply _root_.YangMills.SharedProofs.p6811 <;> assumption
private theorem stage_succ_eq_nextStage {j : ℕ} (hj : j + 1 ≤ S.data.windowLevel) :
    S.tower.stage (j + 1) = nextStage S.labelFacts Λ.table.lam
      (couplingsAlongFlow (Λ.table.stepParameters Λ.floor) S.β (j + 2)) (S.tower.stage j) := by
  rw [stage_eq_flowStages S hj, stage_eq_flowStages S (Nat.le_of_succ_le hj)]
  rfl
private theorem stage_coupling_eq {j : ℕ} (hj : j ≤ S.data.windowLevel + 1) :
    (S.tower.stage j).coupling = (couplingFlow (Λ.table.stepParameters Λ.floor) S.β j).1 := by apply _root_.YangMills.DeltaSharedProofs.p500739 <;> assumption
abbrev _root_.YangMills.SharedProofs.p30777 := @stage_coupling_eq
private theorem hullChain (hg : 0 < Λ.g) (hy : Λ.floor ≤ (Λ.g ^ 2)⁻¹) :
    HullChain Λ.table Λ.floor Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower := by
  have htable : ∀ j ≤ S.data.windowLevel, (S.tower.stage j).toStepSetup.OnParameters Λ.table Λ.floor := fun j hj =>
    (stageOnFlow_of_le S hj).onFamily.onFamily
  have hparts : ∀ j < S.data.windowLevel, S.tower.densities j = (S.tower.stage j).toStepSetup.renormalizedDensity Λ.table.lam ∧
      S.tower.siteDensities (S.tower.stage j).toStepSetup = (S.tower.stage j).toStepSetup.stateDensity Λ.table.lam := fun j hj =>
    next_density_siteDensity_eq (stage_succ_eq_nextStage S hj)
  exact
    { g_pos := hg
      le_inv_sq := hy
      upper_le := S.window_le
      isFirst := S.passage
      volume_le := S.side_le
      follows := fun j hj => stage_coupling_eq S hj
      depth_bottom := S.startsAtWilson.depth_eq
      functional_bottom := S.startsAtWilson.functional_eq
      anchor_bottom := (congrArg ChainStage.anchorRadius (stage_eq_flowStages S (Nat.zero_le _))).trans S.isInitial.anchorRadius_eq
      cutoff_bottom := S.isCutoff
      marks := S.marksMeasurable
      expansions := fun j hj => (htable j hj).isStep.1
      reads_flow :=
        { startsAtWilson := S.startsAtWilson
          coupling_eq := fun j hj => stage_coupling_eq S hj
          onFamily := htable
          siteDensities_eq := fun j hj => (hparts j hj).2
          densities_eq := fun j hj => (hparts j hj).1 } }
abbrev _root_.YangMills.SharedProofs.p4319 := @hullChain
private theorem hullChainAtLevel (hg : 0 < Λ.g) (hy : Λ.floor ≤ (Λ.g ^ 2)⁻¹) {u : ℕ} (hu : u ≤ S.data.windowLevel) :
    HullChainAtLevel Λ.table Λ.floor Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower u (S.sideAtLevel u) :=
  ⟨hullChain S hg hy, hu, rfl⟩
private theorem side_dvd_period (hf : Λ.stepParams.Admissible) :
    Λ.stepParams.side ∣ S.data.period Λ.stepParams.side ∧ 64 ≤ S.data.period Λ.stepParams.side := by apply _root_.YangMills.SharedProofs.p32373 <;> assumption
private theorem isBlockTorusSide_sideAtLevel (hf : Λ.stepParams.Admissible) (u : ℕ) :
    IsBlockTorusSide Λ.stepParams (S.sideAtLevel u) := by apply _root_.YangMills.SharedProofs.p591 <;> assumption
end Point
section Draws
variable {ℓ : TorusLumps.StepParameters}
private theorem sampleBelow_measurable_map (hfit : ℓ.Admissible) (hgt : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side)
    (hLaw : sampleBelowLawStatement)
    (T : StageTower ℓ) (hcut : ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (hco : T.MarksMeasurable)
    (β : ℝ) {K u d : ℕ} (hd : u + d = K) (n : ℕ) [NeZero n] :
    Measurable (fun w : MarkedSample ℓ K n => sampleBelow ℓ u d n (hd.symm ▸ w)) ∧
      (markedSampleLaw T β K n).map (fun w : MarkedSample ℓ K n => sampleBelow ℓ u d n (hd.symm ▸ w)) =
        markedSampleLaw T β u (fineSide ℓ.side d n) := by apply _root_.YangMills.SharedProofs.p37385 <;> assumption
private theorem siteSize_nonneg (T : StageTower ℓ) {s₁ : ℝ} (h₁ : 0 ≤ s₁) (u n : ℕ) [NeZero n]
    (w : MarkedSample ℓ u n) (y : TorusSite n) : 0 ≤ HullTrees.siteSize T s₁ u n w y := by apply _root_.YangMills.SharedProofs.p9879 <;> assumption
private theorem measurable_prod_sigma {X A : Type} [MeasurableSpace X] [Countable A] {B : A → Type}
    [∀ a, MeasurableSpace (B a)] {Z : Type} [MeasurableSpace Z] {f : X × Sigma B → Z}
    (h : ∀ a, Measurable fun p : X × B a => f (p.1, ⟨a, p.2⟩)) : Measurable f := by apply _root_.YangMills.SharedProofs.p5842 <;> assumption
open Classical in
private theorem measurable_sum_responses (T : StageTower ℓ) (u n : ℕ) [NeZero n] (A : ResponseSetup (T.stage u).toStepSetup)
    (hb : IsBlockTorusSide ℓ n) (hrow : A.IsAdmissible) (f : PlaquetteWeight (fineSide ℓ.side (T.stage u).depth n))
    (B : Finset (TorusSite n)) :
    Measurable fun q : StageState T u n => ∑ y ∈ B,
      ((if IsLiveState ℓ (T.stage u).coupling (T.stage u).labelWeight q.1 q.2.1 q.2.2 then A.hull n y q.1 q.2.1 q.2.2 f else 0) -
        A.cold n y (trivialField n) f) := by
  refine Finset.measurable_sum _ fun y _ => ?_
  refine Measurable.sub ?_ measurable_const
  exact measurable_prod_sigma fun Y => hrow.bounds.hull_borel n hb y Y f
end Draws
section Family
variable {Λ : MomentParameters}
private structure TelescopeHypotheses (Λ : MomentParameters) (CW CV Cs : ℝ) : Prop where
  admissible : Λ.stepParams.Admissible
  side_gt : 11 * 2 ^ 12 * Λ.stepParams.baseDepth < Λ.stepParams.side
  C₀_nonneg : 0 ≤ Λ.response.C₀
  s₁_nonneg : 0 ≤ Λ.response.s₁
  g_pos : 0 < Λ.g
  floor_le : Λ.floor ≤ (Λ.g ^ 2)⁻¹
  drawsChain : ruleDrawsChainStatement
  sampleBelowLaw : sampleBelowLawStatement
  forgetLastStep : forgetLastStepStatement
  statesMeasurable : StageStatesMeasurableStatement
  completedBounded : FreeEnergies.completedObservablesBounded
  sitesBound : ∀ S : MomentPoint Λ, ∀ u ≤ S.data.scaleLevel, ∀ i : Fin Λ.k,
    weightNorm Λ.stepParams.side u (S.weight i (fineSide Λ.stepParams.side u (S.levelSide u))) ≤ 1 ∧
      ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) ≤ CW * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u))
  telescope : ∀ S : MomentPoint Λ, (∀ (i : Fin Λ.k) (t' : ℕ) (ht : t' ≤ S.data.windowLevel),
      ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)),
      completedObservable S.tower S.coeff t' (S.sideAtLevel t') (S.weight i _) (S.sampleAtLevel t' ht w) - S.kappa t' (S.sideAtLevel t') i =
        responseAtLevel 0 i S w + ∑ j ∈ Finset.range t', centredStepScore j i S w) ∧
    ∀ (u : ℕ), u < S.data.windowLevel → ∀ J : Finset (Fin Λ.k), ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)),
      variableProduct u J S w = ∏ i ∈ J, (responseAtLevel u i S w + centredStepScore u i S w)
  meanSplit : ∀ S : MomentPoint Λ, ∀ u < S.lastSeparated, ∀ J : Finset (Fin Λ.k), J.Nonempty →
    ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)),
    |variableMean u J S w - ∏ i ∈ J, responseAtLevel (u + 1) i S w| ≤
      S.stepErrorBound CV u J * ∏ i ∈ J, meanScoreAtLevel (u + 1) i S w
  termBounds : ∀ S : MomentPoint Λ, (∀ u < S.data.scaleLevel, ∀ (i : Fin Λ.k)
      (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)),
      |centredStepScore u i S w| ≤ 2 * (Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ))) ∧
    ∀ u ≤ S.data.scaleLevel, ∀ i : Fin Λ.k, ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)),
      |responseAtLevel u i S w| ≤ Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) * meanScoreAtLevel u i S w
  scoreProduct : ∀ S : MomentPoint Λ, ∀ u ≤ S.data.scaleLevel,
    ∀ w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side),
    (∀ i : Fin Λ.k, 1 ≤ meanScoreAtLevel u i S w) ∧ ∀ J : Finset (Fin Λ.k), J.Nonempty →
      ∏ i ∈ J, meanScoreAtLevel u i S w ≤ 1 + 2 ^ J.card * (1 + ∑ z ∈ offsetCube (S.supportRadius u), hullSizePower u z J.card S w)
  liveStates : ∀ S : MomentPoint Λ, ∀ u ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide Λ.stepParams n →
    ∀ᵐ w ∂(S.law u n),
    IsLiveState Λ.stepParams (S.tower.stage u).coupling (S.tower.stage u).labelWeight (S.state u n w).1 (S.state u n w).2.1
      (S.state u n w).2.2
  kappaBounded : ∀ S : MomentPoint Λ, ∃ b : ℝ, ∀ (m : ℕ) hp hs (i : Fin Λ.k), |(S.withSideExponent m hp hs).kappaAtLast i| ≤ b
  preserving : ∀ (S : MomentPoint Λ) (rule : NoiseRule Λ.stepParams) (ms : ℕ → ℕ) (Sq : ℕ → MomentPoint Λ) (p : ℕ),
    rule.IsAdmissible S.tower → 1 ≤ p →
    StrictMono ms → (∀ i, ∃ hp hs, Sq i = S.withSideExponent (ms i) hp hs) → (translatedTori Sq p).IsPreserving
  siteSizeMoment : ∀ (β : ℝ) (K m : ℕ) (T : StageTower Λ.stepParams) (u n : ℕ) [NeZero n],
    HullChainAtLevel Λ.table Λ.floor Λ.g β K m T u n →
    ∀ (z : TorusSite n) (k : ℕ), 1 ≤ k →
      Integrable (fun w => siteSize T Λ.response.s₁ u n w z ^ k) (markedSampleLaw T β u n) ∧
      ∫ w, siteSize T Λ.response.s₁ u n w z ^ k ∂(markedSampleLaw T β u n) ≤
        Cs ^ k * (k.factorial : ℝ) ^ 6 * Real.exp (-(hullDecayRate Λ.table * stageCoupling T u / 4))
  meanAEMeasurable : ∀ (S : MomentPoint Λ) (u : ℕ), u < S.lastSeparated → ∀ J : Finset (Fin Λ.k), J.Nonempty →
    AEMeasurable (variableMean u J S) (S.law S.data.windowLevel (S.data.period Λ.stepParams.side))
variable {CW CV Cs : ℝ}
private theorem sampleOf_measurable_map (hF : TelescopeHypotheses Λ CW CV Cs) (S : MomentPoint Λ) {rule : NoiseRule Λ.stepParams}
    (hr : rule.IsAdmissible S.tower) :
    Measurable (S.sampleOf rule) ∧ S.sampleLaw.map (S.sampleOf rule) = S.law S.data.windowLevel (S.data.period Λ.stepParams.side) := by
  obtain ⟨h1, h2⟩ := side_dvd_period S hF.admissible
  exact hF.drawsChain Λ.stepParams hF.admissible S.tower rule S.β S.isCutoff S.marksMeasurable hr S.data.windowLevel
    (S.data.period Λ.stepParams.side) h1 h2
private theorem sampleAtLevel_measurable_map (hF : TelescopeHypotheses Λ CW CV Cs) (S : MomentPoint Λ)
    {rule : NoiseRule Λ.stepParams} (hr : rule.IsAdmissible S.tower) {u : ℕ} (hu : u ≤ S.data.windowLevel) :
    Measurable (fun ω => S.sampleAtLevel u hu (S.sampleOf rule ω)) ∧
      S.sampleLaw.map (fun ω => S.sampleAtLevel u hu (S.sampleOf rule ω)) = markedSampleLaw S.tower S.β u (S.sideAtLevel u) := by
  obtain ⟨h1, h2⟩ := sampleOf_measurable_map hF S hr
  obtain ⟨h3, h4⟩ := sampleBelow_measurable_map hF.admissible hF.side_gt hF.sampleBelowLaw S.tower S.isCutoff S.marksMeasurable S.β
    (Nat.add_sub_of_le hu) (S.data.period Λ.stepParams.side)
  refine ⟨h3.comp h1, ?_⟩
  have h5 := Measure.map_map (μ := S.sampleLaw) h3 h1
  rw [h2] at h5
  exact h5.symm.trans h4
private theorem ae_sampleOf (hF : TelescopeHypotheses Λ CW CV Cs) (S : MomentPoint Λ) {rule : NoiseRule Λ.stepParams}
    (hr : rule.IsAdmissible S.tower)
    {Q : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side) → Prop}
    (h : ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)), Q w) :
    ∀ᵐ ω ∂S.sampleLaw, Q (S.sampleOf rule ω) := by
  obtain ⟨h1, h2⟩ := sampleOf_measurable_map hF S hr
  exact ae_of_ae_map h1.aemeasurable (by rw [h2]; exact h)
private theorem ae_sampleAtLevel (hF : TelescopeHypotheses Λ CW CV Cs) (S : MomentPoint Λ) {rule : NoiseRule Λ.stepParams}
    (hr : rule.IsAdmissible S.tower) {u : ℕ} (hu : u ≤ S.data.windowLevel)
    {Q : MarkedSample Λ.stepParams u (S.sideAtLevel u) → Prop}
    (h : ∀ᵐ w ∂(markedSampleLaw S.tower S.β u (S.sideAtLevel u)), Q w) :
    ∀ᵐ ω ∂S.sampleLaw, Q (S.sampleAtLevel u hu (S.sampleOf rule ω)) := by
  obtain ⟨h1, h2⟩ := sampleAtLevel_measurable_map hF S hr hu
  exact ae_of_ae_map h1.aemeasurable (by rw [h2]; exact h)
private theorem hullSizePower_eq (S : MomentPoint Λ) {u : ℕ} (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ) (k : ℕ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    hullSizePower u z k S w =
      siteSize S.tower Λ.response.s₁ u (S.sideAtLevel u) (S.sampleAtLevel u hu w) (S.siteAt u z) ^ k := by
  unfold hullSizePower
  rw [dif_pos hu]
private theorem pow_le_one_add_pow_succ (s : ℝ) (hs : 0 ≤ s) (e : ℕ) : s ^ e ≤ 1 + s ^ (e + 1) := by
  rcases le_total s 1 with h | h
  · have h1 := pow_le_one₀ (n := e) hs h
    have h2 : 0 ≤ s ^ (e + 1) := pow_nonneg hs _
    linarith
  · have h1 : s ^ e ≤ s ^ (e + 1) := pow_le_pow_right₀ h (Nat.le_succ e)
    linarith
private theorem lintegral_hullSizePower_le (hF : TelescopeHypotheses Λ CW CV Cs) (S : MomentPoint Λ)
    {rule : NoiseRule Λ.stepParams} (hr : rule.IsAdmissible S.tower)
    {u : ℕ} (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ) (k q : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (|hullSizePower u z k S (S.sampleOf rule ω)| ^ q) ∂S.sampleLaw ≤
      ENNReal.ofReal (1 + Cs ^ (k * q + 1) * ((k * q + 1).factorial : ℝ) ^ 6 *
        Real.exp (-(hullDecayRate Λ.table * stageCoupling S.tower u / 4))) := by
  obtain ⟨hm, hmap⟩ := sampleAtLevel_measurable_map hF S hr hu
  obtain ⟨hI, hB⟩ := hF.siteSizeMoment S.β S.data.windowLevel S.data.sideExponent S.tower u (S.sideAtLevel u)
    (hullChainAtLevel S hF.g_pos hF.floor_le hu) (S.siteAt u z) (k * q + 1) (by omega)
  have hprob : IsProbabilityMeasure (markedSampleLaw S.tower S.β u (S.sideAtLevel u)) :=
    (hF.forgetLastStep Λ.stepParams hF.admissible hF.side_gt S.tower S.isCutoff S.marksMeasurable S.β u (S.sideAtLevel u)).1
  obtain ⟨G, hG⟩ : ∃ G : MarkedSample Λ.stepParams u (S.sideAtLevel u) → ℝ,
      G = fun w => siteSize S.tower Λ.response.s₁ u (S.sideAtLevel u) w (S.siteAt u z) ^ (k * q + 1) := ⟨_, rfl⟩
  have hs0 : ∀ w, 0 ≤ siteSize S.tower Λ.response.s₁ u (S.sideAtLevel u) w (S.siteAt u z) := fun w =>
    siteSize_nonneg _ hF.s₁_nonneg _ _ _ _
  have hG0 : ∀ w, 0 ≤ G w := fun w => by
    rw [hG]
    exact pow_nonneg (hs0 w) _
  have hGI : Integrable G (markedSampleLaw S.tower S.β u (S.sideAtLevel u)) := hG ▸ hI
  have hpt : ∀ ω, ENNReal.ofReal (|hullSizePower u z k S (S.sampleOf rule ω)| ^ q) ≤
      ENNReal.ofReal (1 + G (S.sampleAtLevel u hu (S.sampleOf rule ω))) := fun ω => by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hullSizePower_eq S hu, abs_of_nonneg (pow_nonneg (hs0 _) _), ← pow_mul, hG]
    exact pow_le_one_add_pow_succ _ (hs0 _) _
  have hae : AEMeasurable (fun w => ENNReal.ofReal (1 + G w))
      (S.sampleLaw.map (fun ω => S.sampleAtLevel u hu (S.sampleOf rule ω))) := by
    rw [hmap]
    exact ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_const.add hGI.aestronglyMeasurable.aemeasurable)
  calc ∫⁻ ω, ENNReal.ofReal (|hullSizePower u z k S (S.sampleOf rule ω)| ^ q) ∂S.sampleLaw
      ≤ ∫⁻ ω, ENNReal.ofReal (1 + G (S.sampleAtLevel u hu (S.sampleOf rule ω))) ∂S.sampleLaw := lintegral_mono hpt
    _ = ∫⁻ w, ENNReal.ofReal (1 + G w) ∂(S.sampleLaw.map (fun ω => S.sampleAtLevel u hu (S.sampleOf rule ω))) :=
        (lintegral_map' hae hm.aemeasurable).symm
    _ = ∫⁻ w, ENNReal.ofReal (1 + G w) ∂(markedSampleLaw S.tower S.β u (S.sideAtLevel u)) := by rw [hmap]
    _ = ENNReal.ofReal (∫ w, (1 + G w) ∂(markedSampleLaw S.tower S.β u (S.sideAtLevel u))) :=
        (ofReal_integral_eq_lintegral_ofReal ((integrable_const 1).add hGI)
          (Eventually.of_forall fun w => add_nonneg zero_le_one (hG0 w))).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_add (integrable_const 1) hGI, integral_const]
        simp only [probReal_univ, smul_eq_mul, mul_one]
        rw [hG]
        linarith
private theorem aemeasurable_hullSizePower (hF : TelescopeHypotheses Λ CW CV Cs) (S : MomentPoint Λ)
    {rule : NoiseRule Λ.stepParams} (hr : rule.IsAdmissible S.tower)
    {u : ℕ} (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ) {k : ℕ} (hk : 1 ≤ k) :
    AEMeasurable (fun ω => hullSizePower u z k S (S.sampleOf rule ω)) S.sampleLaw := by
  obtain ⟨hm, hmap⟩ := sampleAtLevel_measurable_map hF S hr hu
  obtain ⟨hI, -⟩ := hF.siteSizeMoment S.β S.data.windowLevel S.data.sideExponent S.tower u (S.sideAtLevel u)
    (hullChainAtLevel S hF.g_pos hF.floor_le hu) (S.siteAt u z) k hk
  have h1 := hI.aestronglyMeasurable.aemeasurable
  rw [← hmap] at h1
  exact (h1.comp_aemeasurable hm.aemeasurable).congr (Eventually.of_forall fun ω => (hullSizePower_eq S hu z k _).symm)
open Classical in
private theorem aemeasurable_responseAtLevel (hF : TelescopeHypotheses Λ CW CV Cs) (S : MomentPoint Λ)
    {rule : NoiseRule Λ.stepParams} (hr : rule.IsAdmissible S.tower)
    {u : ℕ} (hu : u ≤ S.data.windowLevel) (i : Fin Λ.k) :
    AEMeasurable (fun ω => responseAtLevel u i S (S.sampleOf rule ω)) S.sampleLaw := by
  obtain ⟨hm, -⟩ := sampleAtLevel_measurable_map hF S hr hu
  have hresp : (S.resp u).IsAdmissible := (stageOnFlow_of_le S hu).onFamily.admissible
  have hM := (measurable_sum_responses S.tower u (S.sideAtLevel u) (S.resp u) (isBlockTorusSide_sideAtLevel S hF.admissible u)
    hresp (S.weight i _)
    (weightSupportSites Λ.stepParams.side (S.tower.stage u).depth (S.sideAtLevel u) (S.weight i _))).comp
    (hF.statesMeasurable Λ.stepParams hF.admissible S.tower u (S.sideAtLevel u))
  have hlive := ae_sampleAtLevel hF S hr hu
    (hF.liveStates S u hu (S.sideAtLevel u) (isBlockTorusSide_sideAtLevel S hF.admissible u))
  refine ((hM.comp hm).aemeasurable).congr ?_
  filter_upwards [hlive] with ω hw
  show _ = responseAtLevel u i S (S.sampleOf rule ω)
  unfold responseAtLevel MomentPoint.supportTotal supportResponseTotal
  rw [dif_pos hu]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hw' : IsLiveState Λ.stepParams (S.tower.stage u).coupling (S.tower.stage u).labelWeight
      (stageState S.tower u (S.sideAtLevel u) (S.sampleAtLevel u hu (S.sampleOf rule ω))).1
      (stageState S.tower u (S.sideAtLevel u) (S.sampleAtLevel u hu (S.sampleOf rule ω))).2.1
      (stageState S.tower u (S.sideAtLevel u) (S.sampleAtLevel u hu (S.sampleOf rule ω))).2.2 := hw
  beta_reduce
  rw [if_pos hw']
  rfl
private theorem aemeasurable_centredStepScore (hF : TelescopeHypotheses Λ CW CV Cs) (S : MomentPoint Λ)
    {rule : NoiseRule Λ.stepParams} (hr : rule.IsAdmissible S.tower)
    {u : ℕ} (hu : u + 1 ≤ S.data.windowLevel) (i : Fin Λ.k) :
    AEMeasurable (fun ω => centredStepScore u i S (S.sampleOf rule ω)) S.sampleLaw := by
  obtain ⟨hm, -⟩ := sampleAtLevel_measurable_map hF S hr hu
  have h := ((hF.completedBounded Λ.stepParams hF.admissible S.tower S.coeff u (S.sideAtLevel (u + 1))).2.1 (S.weight i _)).1
  refine ((h.comp hm).sub_const (stepMeanShift (n := S.sideAtLevel (u + 1)) (S.resp u) (S.weight i _))).aemeasurable.congr
    (Eventually.of_forall fun ω => ?_)
  show _ = centredStepScore u i S (S.sampleOf rule ω)
  unfold centredStepScore
  rw [dif_pos hu]
  rfl
private theorem lastSeparated_le_scaleLevel (S : MomentPoint Λ) : S.lastSeparated ≤ S.data.scaleLevel :=
  @Nat.findGreatest_le (S.data.SeparatedBelow Λ.stepParams S.β) (fun _ => Classical.propDecidable _) S.data.scaleLevel
abbrev _root_.YangMills.SharedProofs.p10799 := @lastSeparated_le_scaleLevel
private theorem aemeasurable_completedObservable (hF : TelescopeHypotheses Λ CW CV Cs) (S : MomentPoint Λ)
    {rule : NoiseRule Λ.stepParams} (hr : rule.IsAdmissible S.tower) (i : Fin Λ.k) :
    AEMeasurable (fun ω => completedObservable S.tower S.coeff S.lastSeparated (S.sideAtLevel S.lastSeparated) (S.weight i _)
      (S.sampleAtLevel S.lastSeparated S.lastSeparated_le (S.sampleOf rule ω))) S.sampleLaw := by
  obtain ⟨hm, -⟩ := sampleAtLevel_measurable_map hF S hr S.lastSeparated_le
  exact (((hF.completedBounded Λ.stepParams hF.admissible S.tower S.coeff S.lastSeparated
    (S.sideAtLevel S.lastSeparated)).1 (S.weight i _)).1.comp hm).aemeasurable
private def supportCardBound (Λ : MomentParameters) (CW : ℝ) (s u : ℕ) : ℝ := |CW| * (Λ.stepParams.side : ℝ) ^ (4 * (s - u))
private theorem supportCardBound_nonneg (s u : ℕ) : 0 ≤ supportCardBound Λ CW s u := by
  unfold supportCardBound
  positivity
private def scoreProductBound (ρ u k : ℕ) : SampleObservable Λ := fun S w =>
  1 + 2 ^ k * (1 + ∑ z ∈ offsetCube ρ, hullSizePower u z k S w)
private structure TranslatedSequence (S : MomentPoint Λ) (rule : NoiseRule Λ.stepParams) (ms : ℕ → ℕ)
    (Sq : ℕ → MomentPoint Λ) (p : ℕ) : Prop where
  isAdmissible : rule.IsAdmissible S.tower
  one_le : 1 ≤ p
  strictMono : StrictMono ms
  eq_withSideExponent : ∀ i, ∃ hp hs, Sq i = S.withSideExponent (ms i) hp hs
variable {S : MomentPoint Λ} {rule : NoiseRule Λ.stepParams} {ms : ℕ → ℕ} {Sq : ℕ → MomentPoint Λ} {p : ℕ}
private theorem TranslatedSequence.data_eq (h : TranslatedSequence S rule ms Sq p) (i : ℕ) :
    (Sq i).data.windowLevel = S.data.windowLevel ∧ (Sq i).data.scaleLevel = S.data.scaleLevel ∧ (Sq i).tower = S.tower := by
  obtain ⟨hp, hs, e⟩ := h.eq_withSideExponent i
  rw [e]
  exact ⟨rfl, rfl, rfl⟩
private theorem TranslatedSequence.supportRadius_eq (h : TranslatedSequence S rule ms Sq p) (i u : ℕ) :
    (Sq i).supportRadius u = S.supportRadius u := by
  obtain ⟨hp, hs, e⟩ := h.eq_withSideExponent i
  rw [e]
  rfl
private theorem TranslatedSequence.isAdmissible_at (h : TranslatedSequence S rule ms Sq p) (i : ℕ) :
    rule.IsAdmissible (Sq i).tower := by
  rw [(h.data_eq i).2.2]
  exact h.isAdmissible
private theorem TranslatedSequence.isPreserving (hF : TelescopeHypotheses Λ CW CV Cs) (h : TranslatedSequence S rule ms Sq p) :
    (translatedTori Sq p).IsPreserving :=
  hF.preserving S rule ms Sq p h.isAdmissible h.one_le h.strictMono h.eq_withSideExponent
private theorem card_supportSites_le (hF : TelescopeHypotheses Λ CW CV Cs) (h : TranslatedSequence S rule ms Sq p) (j : ℕ)
    {u : ℕ} (hu : u ≤ S.data.scaleLevel) (i : Fin Λ.k) :
    (((Sq j).data.supportSites Λ.stepParams.side u i).card : ℝ) ≤ supportCardBound Λ CW S.data.scaleLevel u := by
  have hs := (h.data_eq j).2.1
  have h1 := (hF.sitesBound (Sq j) u (hs ▸ hu) i).2
  rw [hs] at h1
  refine h1.trans ?_
  unfold supportCardBound
  exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
private theorem hasBoundedMoments_hullSizePower (hF : TelescopeHypotheses Λ CW CV Cs) (h : TranslatedSequence S rule ms Sq p)
    {u : ℕ} (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ) (k : ℕ) :
    TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (hullSizePower u z k)) := by
  have hK := h.isPreserving hF
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine hasBoundedMoments_congr (hasBoundedMoments_const hK (fun _ => 1) 1 (by simp)) fun i =>
      Eventually.of_forall fun ω => ?_
    show hullSizePower u z 0 (Sq i) _ = 1
    unfold hullSizePower
    rw [dif_pos ((h.data_eq i).1 ▸ hu), pow_zero]
  · refine ⟨fun i => aemeasurable_hullSizePower hF (Sq i) (h.isAdmissible_at i) ((h.data_eq i).1 ▸ hu) z hk, fun q =>
      ⟨1 + Cs ^ (k * q + 1) * ((k * q + 1).factorial : ℝ) ^ 6 *
        Real.exp (-(hullDecayRate Λ.table * stageCoupling S.tower u / 4)), fun i => ?_⟩⟩
    have hb := lintegral_hullSizePower_le hF (Sq i) (h.isAdmissible_at i) ((h.data_eq i).1 ▸ hu) z k q
    have e : stageCoupling (Sq i).tower u = stageCoupling S.tower u := by rw [(h.data_eq i).2.2]
    rw [e] at hb
    exact hb
private theorem hasBoundedMoments_scoreProductBound (hF : TelescopeHypotheses Λ CW CV Cs) (h : TranslatedSequence S rule ms Sq p)
    {u : ℕ} (hu : u ≤ S.data.windowLevel) (ρ k : ℕ) :
    TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (scoreProductBound ρ u k)) := by
  have hK := h.isPreserving hF
  have h1 := hasBoundedMoments_add (hasBoundedMoments_const hK (fun _ => 1) 1 (by simp))
    (hasBoundedMoments_mul (hasBoundedMoments_const hK (fun _ => (2 : ℝ) ^ k) (2 ^ k) (by simp))
      (hasBoundedMoments_add (hasBoundedMoments_const hK (fun _ => 1) 1 (by simp))
        (hasBoundedMoments_sum hK (offsetCube ρ) fun z _ => hasBoundedMoments_hullSizePower hF h hu z k)))
  exact hasBoundedMoments_congr h1 fun i => Eventually.of_forall fun ω => rfl
private theorem hasBoundedMoments_responseAtLevel (hF : TelescopeHypotheses Λ CW CV Cs) (h : TranslatedSequence S rule ms Sq p)
    {u : ℕ} (hu : u ≤ S.data.scaleLevel) (i : Fin Λ.k) :
    TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (responseAtLevel u i)) := by
  have hK := h.isPreserving hF
  have huK : u ≤ S.data.windowLevel := hu.trans S.supAdmissible.scaleLevel_le
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Λ.response.C₀ * supportCardBound Λ CW S.data.scaleLevel u := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ mul_nonneg hF.C₀_nonneg (supportCardBound_nonneg _ _)
  refine hasBoundedMoments_of_abs_le (hasBoundedMoments_mul
    (hasBoundedMoments_const hK (fun _ => c) c (fun _ => (abs_of_nonneg hc0).le))
    (hasBoundedMoments_scoreProductBound hF h huK (S.supportRadius u) 1))
    (fun j => aemeasurable_responseAtLevel hF (Sq j) (h.isAdmissible_at j) ((h.data_eq j).1 ▸ huK) i) fun j => ?_
  have hus : u ≤ (Sq j).data.scaleLevel := (h.data_eq j).2.1 ▸ hu
  filter_upwards [ae_sampleOf hF (Sq j) (h.isAdmissible_at j) ((hF.termBounds (Sq j)).2 u hus i)] with ω hω
  obtain ⟨hN1, hN⟩ := hF.scoreProduct (Sq j) u hus ((Sq j).sampleOf rule ω)
  have hN2 := hN {i} (Finset.singleton_nonempty i)
  rw [Finset.prod_singleton, Finset.card_singleton, h.supportRadius_eq j u] at hN2
  refine hω.trans (le_trans ?_ (le_abs_self _))
  show _ ≤ c * scoreProductBound (S.supportRadius u) u 1 (Sq j) ((Sq j).sampleOf rule ω)
  have hA := card_supportSites_le hF h j hu i
  have hl : 0 ≤ meanScoreAtLevel u i (Sq j) ((Sq j).sampleOf rule ω) := zero_le_one.trans (hN1 i)
  calc Λ.response.C₀ * (((Sq j).data.supportSites Λ.stepParams.side u i).card : ℝ) *
        meanScoreAtLevel u i (Sq j) ((Sq j).sampleOf rule ω)
      ≤ c * meanScoreAtLevel u i (Sq j) ((Sq j).sampleOf rule ω) :=
        mul_le_mul_of_nonneg_right (hc ▸ mul_le_mul_of_nonneg_left hA hF.C₀_nonneg) hl
    _ ≤ _ := mul_le_mul_of_nonneg_left hN2 hc0
private theorem abs_centredStepScore_le (hF : TelescopeHypotheses Λ CW CV Cs) (h : TranslatedSequence S rule ms Sq p) (j : ℕ)
    {u : ℕ} (hu : u < S.data.scaleLevel) (i : Fin Λ.k)
    (w : MarkedSample Λ.stepParams (Sq j).data.windowLevel ((Sq j).data.period Λ.stepParams.side)) :
    |centredStepScore u i (Sq j) w| ≤ 2 * (Λ.response.C₀ * supportCardBound Λ CW S.data.scaleLevel u) := by
  have hus : u < (Sq j).data.scaleLevel := (h.data_eq j).2.1 ▸ hu
  refine ((hF.termBounds (Sq j)).1 u hus i w).trans ?_
  have hA := card_supportSites_le hF h j hu.le i
  have := mul_le_mul_of_nonneg_left hA hF.C₀_nonneg
  linarith
private theorem hasBoundedMoments_centredStepScore (hF : TelescopeHypotheses Λ CW CV Cs) (h : TranslatedSequence S rule ms Sq p)
    {u : ℕ} (hu : u < S.data.scaleLevel) (i : Fin Λ.k) :
    TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (centredStepScore u i)) := by
  have hK := h.isPreserving hF
  have huK : u + 1 ≤ S.data.windowLevel := hu.trans_le S.supAdmissible.scaleLevel_le
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 * (Λ.response.C₀ * supportCardBound Λ CW S.data.scaleLevel u) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hD ▸ mul_nonneg zero_le_two (mul_nonneg hF.C₀_nonneg (supportCardBound_nonneg _ _))
  refine hasBoundedMoments_of_abs_le (hasBoundedMoments_const hK (fun _ => D) D (fun _ => (abs_of_nonneg hD0).le))
    (fun j => aemeasurable_centredStepScore hF (Sq j) (h.isAdmissible_at j) ((h.data_eq j).1 ▸ huK) i) fun j =>
      Eventually.of_forall fun ω => ?_
  exact (hD ▸ abs_centredStepScore_le hF h j hu i _).trans (le_abs_self _)
private theorem hasBoundedMoments_variableProduct (hF : TelescopeHypotheses Λ CW CV Cs) (h : TranslatedSequence S rule ms Sq p)
    {u : ℕ} (hu : u < S.data.scaleLevel) (J : Finset (Fin Λ.k)) :
    TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (variableProduct u J)) := by
  have hK := h.isPreserving hF
  have huK : u < S.data.windowLevel := hu.trans_le S.supAdmissible.scaleLevel_le
  refine hasBoundedMoments_congr (hasBoundedMoments_prod hK J fun a _ =>
    hasBoundedMoments_add (hasBoundedMoments_responseAtLevel hF h hu.le a) (hasBoundedMoments_centredStepScore hF h hu a))
    fun j => ?_
  exact ae_sampleOf hF (Sq j) (h.isAdmissible_at j) ((hF.telescope (Sq j)).2 u ((h.data_eq j).1 ▸ huK) J)
private theorem abs_stepErrorBound_le (hF : TelescopeHypotheses Λ CW CV Cs) (h : TranslatedSequence S rule ms Sq p) (j : ℕ)
    {u : ℕ} (hu : u ≤ S.data.scaleLevel) (J : Finset (Fin Λ.k)) :
    |(Sq j).stepErrorBound CV u J| ≤ |CV| * ((J.card : ℝ) * supportCardBound Λ CW S.data.scaleLevel u) *
      (4 * (Λ.response.C₀ * supportCardBound Λ CW S.data.scaleLevel u)) ^ J.card := by
  have hA := supportCardBound_nonneg (Λ := Λ) (CW := CW) S.data.scaleLevel u
  have hC := hF.C₀_nonneg
  have hrt := hF.admissible.rt_pos
  unfold MomentPoint.stepErrorBound
  have h1 : ∑ i ∈ J, (((Sq j).data.supportSites Λ.stepParams.side u i).card : ℝ) ≤
      (J.card : ℝ) * supportCardBound Λ CW S.data.scaleLevel u := by
    have := Finset.sum_le_card_nsmul J (fun i => (((Sq j).data.supportSites Λ.stepParams.side u i).card : ℝ)) _
      fun i _ => card_supportSites_le hF h j hu i
    simpa using this
  have h0 : 0 ≤ ∑ i ∈ J, (((Sq j).data.supportSites Λ.stepParams.side u i).card : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have h2 : Real.exp (-(Λ.stepParams.rt * ((Sq j).data.separation Λ.stepParams.side u : ℝ) / 2 ^ 7)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    positivity
  have h3 : ∏ i ∈ J, (4 * (Λ.response.C₀ * (((Sq j).data.supportSites Λ.stepParams.side u i).card : ℝ))) ≤
      (4 * (Λ.response.C₀ * supportCardBound Λ CW S.data.scaleLevel u)) ^ J.card := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => ?_
    have := mul_le_mul_of_nonneg_left (card_supportSites_le hF h j hu i) hC
    linarith
  have h4 : 0 ≤ ∏ i ∈ J, (4 * (Λ.response.C₀ * (((Sq j).data.supportSites Λ.stepParams.side u i).card : ℝ))) :=
    Finset.prod_nonneg fun _ _ => by positivity
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg h4]
  have h5 : |CV| * ∑ i ∈ J, (((Sq j).data.supportSites Λ.stepParams.side u i).card : ℝ) ≤
      |CV| * ((J.card : ℝ) * supportCardBound Λ CW S.data.scaleLevel u) :=
    mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have h6 : (|CV| * ∑ i ∈ J, (((Sq j).data.supportSites Λ.stepParams.side u i).card : ℝ)) *
      Real.exp (-(Λ.stepParams.rt * ((Sq j).data.separation Λ.stepParams.side u : ℝ) / 2 ^ 7)) ≤
      |CV| * ((J.card : ℝ) * supportCardBound Λ CW S.data.scaleLevel u) := by
    refine le_trans ?_ h5
    exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) h0) h2
  exact mul_le_mul h6 h3 h4 (by positivity)
private theorem hasBoundedMoments_variableMean (hF : TelescopeHypotheses Λ CW CV Cs) (h : TranslatedSequence S rule ms Sq p)
    {u : ℕ} (hu : ∀ m, u < (Sq m).lastSeparated) (J : Finset (Fin Λ.k)) (hJ : J.Nonempty) :
    TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (variableMean u J)) := by
  have hK := h.isPreserving hF
  have hs : u < S.data.scaleLevel := (h.data_eq 0).2.1 ▸ (hu 0).trans_le (lastSeparated_le_scaleLevel (Sq 0))
  have hs1 : u + 1 ≤ S.data.scaleLevel := hs
  have huK : u + 1 ≤ S.data.windowLevel := hs1.trans S.supAdmissible.scaleLevel_le
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = |CV| * ((J.card : ℝ) * supportCardBound Λ CW S.data.scaleLevel u) *
      (4 * (Λ.response.C₀ * supportCardBound Λ CW S.data.scaleLevel u)) ^ J.card := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    have := supportCardBound_nonneg (Λ := Λ) (CW := CW) S.data.scaleLevel u
    have := hF.C₀_nonneg
    rw [hc]
    positivity
  refine hasBoundedMoments_of_abs_le (hasBoundedMoments_add
    (hasBoundedMoments_abs (hasBoundedMoments_prod hK J fun a _ => hasBoundedMoments_responseAtLevel hF h hs1 a))
    (hasBoundedMoments_mul (hasBoundedMoments_const hK (fun _ => c) c (fun _ => (abs_of_nonneg hc0).le))
      (hasBoundedMoments_scoreProductBound hF h huK (S.supportRadius (u + 1)) J.card))) (fun j => ?_) fun j => ?_
  · obtain ⟨hm, hmap⟩ := sampleOf_measurable_map hF (Sq j) (h.isAdmissible_at j)
    have h1 := hF.meanAEMeasurable (Sq j) u (hu j) J hJ
    rw [← hmap] at h1
    exact h1.comp_aemeasurable hm.aemeasurable
  · have hus : u + 1 ≤ (Sq j).data.scaleLevel := (h.data_eq j).2.1 ▸ hs1
    filter_upwards [ae_sampleOf hF (Sq j) (h.isAdmissible_at j) (hF.meanSplit (Sq j) u (hu j) J hJ)] with ω hω
    obtain ⟨hN1, hN⟩ := hF.scoreProduct (Sq j) (u + 1) hus ((Sq j).sampleOf rule ω)
    have hN2 := hN J hJ
    rw [h.supportRadius_eq j (u + 1)] at hN2
    have hp0 : 0 ≤ ∏ i ∈ J, meanScoreAtLevel (u + 1) i (Sq j) ((Sq j).sampleOf rule ω) :=
      Finset.prod_nonneg fun i _ => zero_le_one.trans (hN1 i)
    have he := hc ▸ abs_stepErrorBound_le hF h j hs.le J
    have h2 : (Sq j).stepErrorBound CV u J * ∏ i ∈ J, meanScoreAtLevel (u + 1) i (Sq j) ((Sq j).sampleOf rule ω) ≤
        c * scoreProductBound (S.supportRadius (u + 1)) (u + 1) J.card (Sq j) ((Sq j).sampleOf rule ω) :=
      (mul_le_mul_of_nonneg_right ((le_abs_self _).trans he) hp0).trans (mul_le_mul_of_nonneg_left hN2 hc0)
    refine le_trans ?_ (le_abs_self _)
    show |variableMean u J (Sq j) ((Sq j).sampleOf rule ω)| ≤
      |∏ i ∈ J, responseAtLevel (u + 1) i (Sq j) ((Sq j).sampleOf rule ω)| +
        c * scoreProductBound (S.supportRadius (u + 1)) (u + 1) J.card (Sq j) ((Sq j).sampleOf rule ω)
    have h3 := abs_sub_abs_le_abs_sub (variableMean u J (Sq j) ((Sq j).sampleOf rule ω))
      (∏ i ∈ J, responseAtLevel (u + 1) i (Sq j) ((Sq j).sampleOf rule ω))
    have h4 : |variableMean u J (Sq j) ((Sq j).sampleOf rule ω) -
        ∏ i ∈ J, responseAtLevel (u + 1) i (Sq j) ((Sq j).sampleOf rule ω)| ≤
        (Sq j).stepErrorBound CV u J * ∏ i ∈ J, meanScoreAtLevel (u + 1) i (Sq j) ((Sq j).sampleOf rule ω) := hω
    linarith
private def completedFactor (c : ℝ) (a : Fin Λ.k) : SampleObservable Λ := fun S w =>
  completedObservable S.tower S.coeff S.lastSeparated (S.sideAtLevel S.lastSeparated) (S.weight a _)
    (S.sampleAtLevel S.lastSeparated S.lastSeparated_le w) - c
private theorem hasBoundedMoments_completedFactor (hF : TelescopeHypotheses Λ CW CV Cs) (h : TranslatedSequence S rule ms Sq p)
    (c : ℝ) (a : Fin Λ.k) :
    TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (completedFactor c a)) := by
  have hK := h.isPreserving hF
  obtain ⟨b, hb⟩ := hF.kappaBounded S
  have hC := hF.C₀_nonneg
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, D = fun v => 2 * (Λ.response.C₀ * supportCardBound Λ CW S.data.scaleLevel v) := ⟨_, rfl⟩
  have hD0 : ∀ v, 0 ≤ D v := fun v => by
    have := supportCardBound_nonneg (Λ := Λ) (CW := CW) S.data.scaleLevel v
    rw [hD]
    positivity
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = |b| + |c| + ∑ v ∈ Finset.range S.data.scaleLevel, D v := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by
    rw [hE]
    have := Finset.sum_nonneg fun v (_ : v ∈ Finset.range S.data.scaleLevel) => hD0 v
    positivity
  refine hasBoundedMoments_of_abs_le (hasBoundedMoments_add
    (hasBoundedMoments_abs (hasBoundedMoments_responseAtLevel hF h (Nat.zero_le _) a))
    (hasBoundedMoments_const hK (fun _ => E) E (fun _ => (abs_of_nonneg hE0).le))) (fun j => ?_) fun j => ?_
  · exact (aemeasurable_completedObservable hF (Sq j) (h.isAdmissible_at j) a).sub_const c
  · filter_upwards [ae_sampleOf hF (Sq j) (h.isAdmissible_at j)
      ((hF.telescope (Sq j)).1 a (Sq j).lastSeparated (Sq j).lastSeparated_le)] with ω hω
    have hts : (Sq j).lastSeparated ≤ S.data.scaleLevel := (h.data_eq j).2.1 ▸ lastSeparated_le_scaleLevel (Sq j)
    obtain ⟨hp, hs, e⟩ := h.eq_withSideExponent j
    have hk : |(Sq j).kappa (Sq j).lastSeparated ((Sq j).sideAtLevel (Sq j).lastSeparated) a| ≤ |b| := by
      have h1 := hb (ms j) hp hs a
      rw [← e] at h1
      exact h1.trans (le_abs_self _)
    have hsum : |∑ v ∈ Finset.range (Sq j).lastSeparated, centredStepScore v a (Sq j) ((Sq j).sampleOf rule ω)| ≤
        ∑ v ∈ Finset.range S.data.scaleLevel, D v := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans (Finset.sum_le_sum fun v hv => ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hts) fun v _ _ => hD0 v))
      rw [hD]
      exact abs_centredStepScore_le hF h j ((Finset.mem_range.1 hv).trans_le hts) a _
    refine le_trans ?_ (le_abs_self _)
    show |completedObservable (Sq j).tower (Sq j).coeff (Sq j).lastSeparated ((Sq j).sideAtLevel (Sq j).lastSeparated)
        ((Sq j).weight a _) ((Sq j).sampleAtLevel (Sq j).lastSeparated (Sq j).lastSeparated_le ((Sq j).sampleOf rule ω)) - c| ≤
        |responseAtLevel 0 a (Sq j) ((Sq j).sampleOf rule ω)| + E
    have e1 : completedObservable (Sq j).tower (Sq j).coeff (Sq j).lastSeparated ((Sq j).sideAtLevel (Sq j).lastSeparated)
        ((Sq j).weight a _) ((Sq j).sampleAtLevel (Sq j).lastSeparated (Sq j).lastSeparated_le ((Sq j).sampleOf rule ω)) - c =
        responseAtLevel 0 a (Sq j) ((Sq j).sampleOf rule ω) +
          ∑ v ∈ Finset.range (Sq j).lastSeparated, centredStepScore v a (Sq j) ((Sq j).sampleOf rule ω) +
          (Sq j).kappa (Sq j).lastSeparated ((Sq j).sideAtLevel (Sq j).lastSeparated) a - c := by
      rw [← hω]
      ring
    rw [e1, hE]
    have h3 := abs_add_le (responseAtLevel 0 a (Sq j) ((Sq j).sampleOf rule ω))
      (∑ v ∈ Finset.range (Sq j).lastSeparated, centredStepScore v a (Sq j) ((Sq j).sampleOf rule ω))
    have h4 := abs_add_le (responseAtLevel 0 a (Sq j) ((Sq j).sampleOf rule ω) +
      ∑ v ∈ Finset.range (Sq j).lastSeparated, centredStepScore v a (Sq j) ((Sq j).sampleOf rule ω))
      ((Sq j).kappa (Sq j).lastSeparated ((Sq j).sideAtLevel (Sq j).lastSeparated) a)
    have h5 := abs_sub (responseAtLevel 0 a (Sq j) ((Sq j).sampleOf rule ω) +
      ∑ v ∈ Finset.range (Sq j).lastSeparated, centredStepScore v a (Sq j) ((Sq j).sampleOf rule ω) +
      (Sq j).kappa (Sq j).lastSeparated ((Sq j).sideAtLevel (Sq j).lastSeparated) a) c
    linarith
private theorem hasBoundedMoments_completedProduct (hF : TelescopeHypotheses Λ CW CV Cs) (h : TranslatedSequence S rule ms Sq p)
    (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)) :
    TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (completedProduct c B)) :=
  hasBoundedMoments_congr (hasBoundedMoments_prod (h.isPreserving hF) B fun a _ => hasBoundedMoments_completedFactor hF h (c a) a)
    fun _ => Eventually.of_forall fun _ => rfl
end Family
section Parameters
private theorem forAllHullParameters_of_forAllParameters {Q : MomentParameters → Prop} (h : ForAllParameters Q) :
    ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem forAllHullParameters_of_eventually {P : ParameterAssignment → ResponseParameters → ℝ → Prop}
    (h : EventuallyInParameters P) :
    ForAllHullParameters fun Λ => P Λ.table Λ.response Λ.floor := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, H⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, hrt, ?_⟩
  intro L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  obtain ⟨M, G⟩ := H L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  refine ⟨M, ?_⟩
  intro Kr k₁ k₂ k₃ k₄ k₅
  obtain ⟨y₀, Y⟩ := G Kr k₁ k₂ k₃ k₄ k₅
  refine ⟨y₀, ?_⟩
  intro y hy hrow hw g hg hgy k _ hk2 hk8 R d hd
  exact Y y hy hrow hw
private theorem ForAllHullParameters.and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁)
    (h₂ : ForAllHullParameters Q₂) :
    ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem ForAllHullParameters.mono {Q₁ Q₂ : MomentParameters → Prop} (h : ForAllHullParameters Q₁)
    (f : ∀ Λ : MomentParameters, Λ.table.Admissible → Λ.response.Admissible Λ.stepParams → Λ.stepParams.Admissible →
      0 < Λ.g → Λ.floor ≤ (Λ.g ^ 2)⁻¹ → Q₁ Λ → Q₂ Λ) :
    ForAllHullParameters Q₂ := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, H⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, hrt, ?_⟩
  intro L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  obtain ⟨M, G⟩ := H L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  refine ⟨M, ?_⟩
  intro Kr k₁ k₂ k₃ k₄ k₅
  obtain ⟨y₀, Y⟩ := G Kr k₁ k₂ k₃ k₄ k₅
  refine ⟨max y₀ Tb.floorMin, ?_⟩
  intro y hy hrow hw g hg hgy k _ hk2 hk8 R d hd
  have hfit : (Tb.stepParameters y).Admissible := d₁.fits y ((le_max_right _ _).trans hy)
  exact f ⟨Tb, Kr, y, g, k, R, d⟩ d₁ (k₄ y) hfit hg hgy (Y y ((le_max_left _ _).trans hy) hrow hw g hg hgy k hk2 hk8 R d hd)
end Parameters
theorem telescopeMoments (hAR : ruleDrawsChainStatement) (hLaw : sampleBelowLawStatement)
    (hDraw : forgetLastStepStatement) (hSt : StageStatesMeasurableStatement)
    (hCO : FreeEnergies.completedObservablesBounded) (hS : weightsSitesBelowScaleStatement)
    (hT : telescopeIdentityStatement) (hV : stepVariableMeanSplitStatement) (hZ : telescopeTermBoundsStatement)
    (hN : meanScoreProductBoundStatement) (hLv : liveStatesStatement) (hP : largerToriStatement)
    (hB : variableMeanAEMeasurableStatement) (hSz : siteSizeMomentStatement) :
    telescopeMomentsStatement := by
  unfold weightsSitesBelowScaleStatement ForAllPoints at hS
  unfold telescopeIdentityStatement ForAllPoints at hT
  unfold stepVariableMeanSplitStatement ForAllPoints at hV
  unfold telescopeTermBoundsStatement ForAllPoints at hZ
  unfold meanScoreProductBoundStatement ForAllPoints at hN
  unfold liveStatesStatement ForAllPoints at hLv
  have h := (forAllHullParameters_of_forAllParameters hS).and ((forAllHullParameters_of_forAllParameters hT).and
    ((forAllHullParameters_of_forAllParameters hV).and ((forAllHullParameters_of_forAllParameters hZ).and
    ((forAllHullParameters_of_forAllParameters hN).and ((forAllHullParameters_of_forAllParameters hLv).and
    (hP.and (hB.and (forAllHullParameters_of_eventually hSz))))))))
  refine h.mono fun Λ hDr hKf hf hg hy hh => ?_
  obtain ⟨⟨C₂, _, _, _, _, Q₂⟩, ⟨_, _, _, _, _, Q₃⟩, ⟨C₃, _, _, _, _, Q₄⟩, ⟨_, _, _, _, _, Q₅⟩, ⟨_, _, _, _, _, Q₆⟩,
    ⟨_, _, _, _, _, Q₇⟩, Q₈, Q₉, Q₁₀⟩ := hh
  obtain ⟨Cs, -, Q₁₁⟩ := Q₁₀ Λ.g
  have hC₀ : 0 ≤ Λ.response.C₀ := by
    rw [hKf.C₀_eq]
    linarith [hf.a_ge, hKf.N₀_nonneg, hKf.Kc_ge]
  have hs₁ : 0 ≤ Λ.response.s₁ := by
    rw [hKf.s₁_eq]
    have : 0 ≤ Λ.stepParams.coupling := by linarith [hf.a_ge]
    positivity
  have hF : TelescopeHypotheses Λ (C₂ 0) (C₃ 0) Cs :=
    { admissible := hf
      side_gt := hDr.L_gt
      C₀_nonneg := hC₀
      s₁_nonneg := hs₁
      g_pos := hg
      floor_le := hy
      drawsChain := hAR
      sampleBelowLaw := hLaw
      forgetLastStep := hDraw
      statesMeasurable := hSt
      completedBounded := hCO
      sitesBound := Q₂
      telescope := Q₃
      meanSplit := Q₄
      termBounds := Q₅
      scoreProduct := Q₆
      liveStates := Q₇
      kappaBounded := fun S => (Q₈ S).2.1
      preserving := fun S rule ms Sq p a b c d => ((Q₈ S).2.2.2 rule ms Sq p a b c d).1
      siteSizeMoment := Q₁₁
      meanAEMeasurable := Q₉ }
  intro S rule ms Sq p h1 h2 h3 h4
  have hA : TranslatedSequence S rule ms Sq p := ⟨h1, h2, h3, h4⟩
  exact ⟨fun u hu i => hasBoundedMoments_responseAtLevel hF hA hu i,
    fun u hu i => hasBoundedMoments_centredStepScore hF hA hu i,
    fun u hu J => hasBoundedMoments_variableProduct hF hA hu J,
    fun u hu z k => hasBoundedMoments_hullSizePower hF hA hu z k,
    fun u hu J hJ => hasBoundedMoments_variableMean hF hA hu J hJ,
    fun c B => hasBoundedMoments_completedProduct hF hA c B⟩
end YangMills.Construction.MomentLaw
end

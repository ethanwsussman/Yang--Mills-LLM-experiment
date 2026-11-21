import YangMills.Construction.CellOfTheFlow.TheDrawsStandOnGroundsProof
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.MeansOfTheVariablesAreBorel
import YangMills.Construction.ResponseInTheExpansion.MomentAlongIsBorelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps StepSettings StepCosts RenormalizationStepParameters WeightedResponses ResponseInTheExpansion FreeEnergies LevelTestFunctions
section Measurability
private theorem measurableSet_isLiveState {R : StepSetup} (hR : R.HasExpansions) {m : ℕ} [NeZero m]
    (hm : IsBlockTorusSide R.params m) (Y : Finset (TorusSite m)) :
    MeasurableSet {p : TorusField m × (Y → R.labels.Ω) | IsLiveState R.params R.coupling R.labelWeight p.1 Y p.2} := by apply _root_.YangMills.SharedProofs.p107331 <;> assumption
private theorem measurable_supportResponseTotal {R : StepSetup} {A : ResponseSetup R} (hR : R.HasExpansions) (hA : A.IsAdmissible) {m : ℕ} [NeZero m]
    (hm : IsBlockTorusSide R.params m) (Y : Finset (TorusSite m)) (w : PlaquetteWeight (fineSide R.params.side R.depth m)) :
    open Classical in Measurable fun p : TorusField m × (Y → R.labels.Ω) =>
      if IsLiveState R.params R.coupling R.labelWeight p.1 Y p.2 then supportResponseTotal A w p.1 Y p.2 else 0 := by apply _root_.YangMills.SharedProofs.p23502 <;> assumption
private theorem measurable_centeredStepScore (hS : BondScoreProperties) {R : StepSetup} (A : ResponseSetup R) (hR : R.params.Admissible) {n : ℕ}
    [NeZero n] (Y : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (w : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Y → R.labels.Ω) => centeredStepScore A p.1 w p.2.1 b := by apply _root_.YangMills.SharedProofs.p59899 <;> assumption
private theorem measurable_prod_sigma_of_fiberwise {X A : Type} [MeasurableSpace X] [Countable A] {B : A → Type}
    [∀ a, MeasurableSpace (B a)] {Z : Type} [MeasurableSpace Z] {f : X × Sigma B → Z}
    (h : ∀ a, Measurable fun p : X × B a => f (p.1, ⟨a, p.2⟩)) : Measurable f := by apply _root_.YangMills.SharedProofs.p5842 <;> assumption
private theorem sampleBelow_measurable_and_map {P : StepParameters} (hP : P.Admissible) (hside : 11 * 2 ^ 12 * P.baseDepth < P.side)
    (hLaw : sampleBelowLawStatement) (T : StageTower P) (hcut : ColdStepAtMirrorFrames.IsCutoff (P.threshold / 64) T.base.barrierFn)
    (hmarks : T.MarksMeasurable) (β : ℝ) {K u d : ℕ} (hd : u + d = K) (n : ℕ) [NeZero n] :
    Measurable (fun w : MarkedSample P K n => sampleBelow P u d n (hd.symm ▸ w)) ∧
      (markedSampleLaw T β K n).map (fun w : MarkedSample P K n => sampleBelow P u d n (hd.symm ▸ w)) =
        markedSampleLaw T β u (fineSide P.side d n) := by apply _root_.YangMills.SharedProofs.p37385 <;> assumption
end Measurability
section AtAPoint
variable {Θ : MomentParameters} (S : MomentPoint Θ)
private theorem stage_eq_flowStages {t : ℕ} (ht : t ≤ S.data.windowLevel) :
    S.tower.stage t = (flowStages Θ.table Θ.floor S.β S.labelFacts S.initial t).1 :=
  congrArg Sigma.fst (S.stage_eq t ht)
private theorem stageOnFlow_of_le {t : ℕ} (ht : t ≤ S.data.windowLevel) :
    StageOnFlow Θ.table Θ.response Θ.floor S.β t ⟨S.tower.stage t, S.resp t⟩ := by apply _root_.YangMills.SharedProofs.p6811 <;> assumption
private theorem isBlockTorusSide_sideAtLevel (hP : Θ.stepParams.Admissible) (u : ℕ) : IsBlockTorusSide Θ.stepParams (S.sideAtLevel u) := by apply _root_.YangMills.SharedProofs.p591 <;> assumption
open Classical in
private theorem measurable_variableCaseProduct_live (hS : BondScoreProperties) (hP : Θ.stepParams.Admissible) {u : ℕ} (hu : u ≤ S.data.windowLevel)
    (hR : (S.tower.stage u).toStepSetup.HasExpansions) (J : Finset (Fin Θ.k))
    (Y : Finset (TorusSite (S.sideAtLevel (u + 1) * Θ.stepParams.side))) (bad : Finset (TorusBond (S.sideAtLevel (u + 1) * Θ.stepParams.side)))
    (b : BaseChoice Θ.stepParams.side (S.sideAtLevel (u + 1))) :
    Measurable fun p : TorusField (S.sideAtLevel (u + 1)) × TorusField (S.sideAtLevel (u + 1) * Θ.stepParams.side) × (Y → (S.tower.stage u).toStepSetup.labels.Ω) =>
      if IsLiveState Θ.stepParams (S.tower.stage u).toStepSetup.coupling (S.tower.stage u).toStepSetup.labelWeight p.2.1 Y p.2.2 then
        S.variableCaseProduct u J p.1 p.2.1 Y p.2.2 bad b else 0 := by
  have hA : (S.resp u).IsAdmissible := (stageOnFlow_of_le S hu).onFamily.admissible
  have hm := isBlockTorusSide_sideAtLevel S hP (u + 1)
  have hL : 1 ≤ Θ.stepParams.side := by
    have := hP.L_ge
    omega
  have hmL : IsBlockTorusSide Θ.stepParams (S.sideAtLevel (u + 1) * Θ.stepParams.side) :=
    ⟨Dvd.intro_left _ rfl, hm.2.trans (Nat.le_mul_of_pos_right _ hL)⟩
  have hset : MeasurableSet {p : TorusField (S.sideAtLevel (u + 1)) × TorusField (S.sideAtLevel (u + 1) * Θ.stepParams.side) × (Y → (S.tower.stage u).toStepSetup.labels.Ω) |
      IsLiveState Θ.stepParams (S.tower.stage u).toStepSetup.coupling (S.tower.stage u).toStepSetup.labelWeight p.2.1 Y p.2.2} :=
    measurable_snd (measurableSet_isLiveState hR hmL Y)
  have e : (fun p : TorusField (S.sideAtLevel (u + 1)) × TorusField (S.sideAtLevel (u + 1) * Θ.stepParams.side) × (Y → (S.tower.stage u).toStepSetup.labels.Ω) =>
      if IsLiveState Θ.stepParams (S.tower.stage u).toStepSetup.coupling (S.tower.stage u).toStepSetup.labelWeight p.2.1 Y p.2.2 then
        S.variableCaseProduct u J p.1 p.2.1 Y p.2.2 bad b else 0) =
      fun p => if IsLiveState Θ.stepParams (S.tower.stage u).toStepSetup.coupling (S.tower.stage u).toStepSetup.labelWeight p.2.1 Y p.2.2 then
        ∏ i ∈ J, ((if IsLiveState Θ.stepParams (S.tower.stage u).toStepSetup.coupling (S.tower.stage u).toStepSetup.labelWeight p.2.1 Y p.2.2 then
            supportResponseTotal (S.resp u) (S.weight i _) p.2.1 Y p.2.2 else 0) +
          centeredStepScore (S.resp u) p.1 (S.weight i _) p.2.1 (clampBasesToBlocks b)) else 0 := by
    funext p
    by_cases hl : IsLiveState Θ.stepParams (S.tower.stage u).toStepSetup.coupling (S.tower.stage u).toStepSetup.labelWeight p.2.1 Y p.2.2
    · rw [if_pos hl, if_pos hl]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [if_pos hl]
      unfold liveCaseFunction
      rw [if_pos hl]
      exact add_sub_assoc _ _ _
    · rw [if_neg hl, if_neg hl]
  rw [e]
  exact Measurable.ite hset (Finset.measurable_prod _ fun i _ =>
    ((measurable_supportResponseTotal hR hA hmL Y (S.weight i _)).comp measurable_snd).add
      (measurable_centeredStepScore hS (S.resp u) hP Y (clampBasesToBlocks b) (S.weight i _))) measurable_const
end AtAPoint
section Parameters
private theorem forAllHullParameters_of_floor {P : ParameterAssignment → ℝ → Prop}
    (h : ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → P T y) :
    ForAllHullParameters fun Θ => P Θ.table Θ.floor := by apply _root_.YangMills.SharedProofs.p14065 <;> assumption
private theorem forAllHullParameters_of_forAllParameters {Q : MomentParameters → Prop} (h : ForAllParameters Q) : ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem ForAllHullParameters.and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁) (h₂ : ForAllHullParameters Q₂) :
    ForAllHullParameters fun Θ => Q₁ Θ ∧ Q₂ Θ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem ForAllHullParameters.mono {Q₁ Q₂ : MomentParameters → Prop} (h : ForAllHullParameters Q₁)
    (f : ∀ Θ : MomentParameters, Θ.table.Admissible → Θ.stepParams.Admissible → Q₁ Θ → Q₂ Θ) : ForAllHullParameters Q₂ := by
  intro a ha
  obtain ⟨L₀, r₀, C₀, hr, H⟩ := h a ha
  refine ⟨L₀, r₀, C₀, hr, ?_⟩
  intro L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  obtain ⟨M, G⟩ := H L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  refine ⟨M, ?_⟩
  intro Kr k₁ k₂ k₃ k₄ k₅
  obtain ⟨y₀, Y⟩ := G Kr k₁ k₂ k₃ k₄ k₅
  refine ⟨max y₀ Tb.floorMin, ?_⟩
  intro y hy hrow hw g hg hgy k _ hk2 hk8 R d hd
  exact f ⟨Tb, Kr, y, g, k, R, d⟩ d₁ (d₁.fits y ((le_max_right _ _).trans hy))
    (Y y ((le_max_left _ _).trans hy) hrow hw g hg hgy k hk2 hk8 R d hd)
end Parameters
theorem variableMean_aemeasurable (hMean : caseMeanMeasurableStatement) (hForm : StagesAreWellPosed)
    (hS : BondScoreProperties) (hLive : liveStatesStatement) (hStates : StageStatesMeasurableStatement)
    (hLaw : sampleBelowLawStatement) : variableMeanAEMeasurableStatement := by
  classical
  unfold liveStatesStatement ForAllPoints at hLive
  have h := ForAllHullParameters.and (forAllHullParameters_of_floor hMean)
    (ForAllHullParameters.and (forAllHullParameters_of_floor hForm) (forAllHullParameters_of_forAllParameters hLive))
  refine ForAllHullParameters.mono h fun Θ hT hP hh => ?_
  obtain ⟨H₁, H₂, ⟨_, _, _, _, _, H₃⟩⟩ := hh
  intro S u hu J _
  have hts : S.lastSeparated ≤ S.data.windowLevel := S.lastSeparated_le
  have hu1 : u + 1 ≤ S.data.windowLevel := by omega
  have hu0 : u ≤ S.data.windowLevel := by omega
  have hst := stageOnFlow_of_le S hu0
  have hst1 := stageOnFlow_of_le S hu1
  have hwp : (S.tower.stage u).toStepSetup.IsWellPosed := by
    rw [stage_eq_flowStages S hu0]
    exact H₂ Θ.response S.β S.labelFacts S.initial S.isInitial S.data.windowLevel S.onFlow u hu0
  have hm := isBlockTorusSide_sideAtLevel S hP (u + 1)
  have hH := fun Y bad b => measurable_variableCaseProduct_live S hS hP hu0 hwp.hasExpansions J Y bad b
  have hsum : Measurable fun q : StageState S.tower (u + 1) (S.sideAtLevel (u + 1)) =>
      if IsHullState Θ.stepParams (S.tower.stage u).toStepSetup.nextRange q.1 q.2.1 then
        caseMean (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup q.1) q.1 q.2 (S.variableCaseProduct u J q.1) else 0 :=
    measurable_prod_sigma_of_fiberwise fun Y => H₁ (S.tower.stage u).toStepSetup hst.onFamily.onFamily hwp (S.sideAtLevel (u + 1)) hm Y (S.variableCaseProduct u J) hH
  have hM := hsum.comp (hStates Θ.stepParams hP S.tower (u + 1) (S.sideAtLevel (u + 1)))
  have hx : (S.tower.stage (u + 1)).coupling = (S.tower.stage u).toStepSetup.nextCoupling := hst1.coupling_eq.trans hst.nextCoupling_eq.symm
  have hae : AEMeasurable (caseMeanAtSample S.tower u (S.sideAtLevel (u + 1)) (S.variableCaseProduct u J))
      (markedSampleLaw S.tower S.β (u + 1) (S.sideAtLevel (u + 1))) := by
    refine hM.aemeasurable.congr ?_
    filter_upwards [H₃ S (u + 1) hu1 (S.sideAtLevel (u + 1)) hm] with x hl
    have hhull : IsHullState Θ.stepParams (S.tower.stage u).toStepSetup.nextRange (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).1
        (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2.1 := by
      have h1 := hl.1
      rw [hx] at h1
      exact h1
    show (if _ then _ else _) = _
    rw [if_pos hhull]
    rfl
  obtain ⟨h3, h4⟩ := sampleBelow_measurable_and_map hP hT.L_gt hLaw S.tower S.isCutoff S.marksMeasurable S.β (Nat.add_sub_of_le hu1) (S.data.period Θ.stepParams.side)
  rw [← h4] at hae
  refine (hae.comp_aemeasurable h3.aemeasurable).congr (Filter.Eventually.of_forall fun w => ?_)
  show _ = variableMean u J S w
  unfold variableMean
  rw [dif_pos hu1]
  rfl
end YangMills.Construction.MomentLaw
end

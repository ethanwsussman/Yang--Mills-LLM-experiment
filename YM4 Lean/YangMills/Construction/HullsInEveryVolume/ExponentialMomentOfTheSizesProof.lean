import YangMills.Construction.CellOfTheFlow.MomentOfTheMajorantProof
import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfTheImage
import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasTheExpansionProof
import YangMills.Construction.HullsInEveryVolume.ExponentialMomentOfTheSizes
import YangMills.Construction.HullsInEveryVolume.FreeEnergyBeforeTheFloor
import YangMills.Construction.ResponseInTheExpansion.ScoredPriceReturnsProof
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import YangMills.Construction.SixteenPointsOnASmallTorus.MeanOfTheScoresOfTheCopiesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
open TorusLumps StepSettings RenormalizationStepParameters StepGas TorusFields WeightedResponses ResponseInTheExpansion ClusterExpansionOfAStep BlockAverages FreeEnergies BlockPlaces StepReturn
private theorem coarseLabelScore_nonneg {Ω : Type} {L : ℕ} {s₁ : ℝ} {s : Ω → ℝ} (h₁ : 0 ≤ s₁) (hs : ∀ w, 0 ≤ s w)
    (w : CoarseLabel Ω L) : 0 ≤ coarseLabelScore s₁ s w := by apply _root_.YangMills.Construction.ResponseInTheExpansion.CoarseScore.coarseLabelScore_nonneg <;> assumption
private theorem coarseLabelScore_measurable {Ω : Type} [MeasurableSpace Ω] {L : ℕ} (s₁ : ℝ) {s : Ω → ℝ}
    (hs : Measurable s) : Measurable (coarseLabelScore (L := L) s₁ s) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.CoarseScore.measurable_coarseLabelScore <;> assumption
private theorem coarseLabelScore_gauge {R : StepSetup} {n : ℕ} [NeZero n] [NeZero R.params.side] {s₁ : ℝ}
    {s : R.labels.Ω → ℝ}
    (hs : ∀ (m : ℕ) [NeZero m] (Y : Finset (TorusSite m)) (g : TorusSite m → UnitQuaternion) (ω : Y → R.labels.Ω)
      (y : Y), s (R.labels.act Y g ω y) = s (ω y))
    (Y : Finset (TorusSite n)) (g : TorusSite n → UnitQuaternion) (ω : Y → CoarseLabel R.labels.Ω R.params.side)
    (y : Y) :
    coarseLabelScore s₁ s (coarseGaugeAct (R := R) Y g ω y) = coarseLabelScore s₁ s (ω y) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.CoarseScore.coarseLabelScore_gauge <;> assumption
private theorem le_clusterRange {k : ℕ} {y : ℝ} (hy : (k : ℝ) ^ 100 ≤ y) : k ≤ clusterRange y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
private theorem sum_siteScore {n : ℕ} [NeZero n] {Ω : Type} (s : Ω → ℝ) (Y : Finset (TorusSite n)) (ω : Y → Ω) :
    ∑ z : TorusSite n, siteScore s Y ω z = ∑ y : Y, s (ω y) := by apply _root_.YangMills.SharedProofs.p15197 <;> assumption
private theorem measurable_of_sigma {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] {γ : Type}
    [MeasurableSpace γ] {f : Sigma β → γ} (h : ∀ a, Measurable fun y : β a => f ⟨a, y⟩) : Measurable f := by apply _root_.YangMills.SharedProofs.p3239 <;> assumption
private theorem exp_bound_of_log_bound {D Z C l E Cf N : ℝ} {M : ℕ} (hM : (M : ℝ) = N) (hN : 0 ≤ N) (hZ : 0 < Z)
    (hb : Real.log D - (C + 6 * l) * N ≤ Real.log Z) (hl : 0 ≤ l) (hE : 0 ≤ E)
    (hCf : Cf = |C| + Real.log 2 + 2 * E + 6) :
    D * 2 ^ M * Real.exp (2 * E * M) ≤ Z * Real.exp (Cf * (1 + l) * N) := by apply _root_.YangMills.SharedProofs.p49832 <;> assumption
private theorem clusterRange_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : clusterRange x ≤ clusterRange y := by apply _root_.YangMills.Construction.WilsonExpansion.clusterRange_mono <;> assumption
private theorem priceBoundsScore_zero {ℓ : StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional} {f : LocalDensity}
    {Λ : LabelSpace}
    {Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
    {Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ}
    {φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
    (h : HullExpansion ℓ t x D f Λ Dq Φ φ) {s : Λ.Ω → ℝ} (hs : ∀ w, s w = 0) : PriceBoundsScore ℓ x Λ Φ φ s := by
  have hs' : s = fun _ => 0 := funext hs
  subst hs'
  refine ⟨fun _ => le_rfl, measurable_const, fun _ _ _ _ _ _ => rfl, fun n _ hn W Y ω P hull hP hoff => ?_⟩
  simpa using h.price n hn W Y ω P hull hP hoff
private theorem priceBoundsScore_coarse (hb : scoredComponentPriceBound) (hsum : ClassExponentLePrice)
    (htab : ParameterChoiceMeetsClassSum) (hfl : StepFloors.EventuallyFloorConditions) :
    ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
      T.rt ≤ rt₀ T.toChainParameters →
      ∀ s₁ : ℝ, 0 ≤ s₁ → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.IsWellPosed →
        R.nextCoupling = R.shiftedCoupling T.lam → |R.nextCoupling - R.coupling| ≤ 2 * R.params.B →
        ∀ s : R.labels.Ω → ℝ,
        PriceBoundsScore R.params R.coupling R.labels R.clusterFactor R.siteDensity s → ∀ hL : CoarseLabelFacts R,
        PriceBoundsScore R.params R.nextCoupling (coarseLabelSpace R hL) (coarseFactorExpansion R)
          (R.stateDensity T.lam) (coarseLabelScore s₁ s) := by
  obtain ⟨rt₀, hrt₀, hb'⟩ := hb
  refine ⟨rt₀, hrt₀, fun T hT hrt s₁ hs₁ => ?_⟩
  obtain ⟨CE, y₀, hCE, hprice⟩ := hb' T hT hrt s₁ hs₁
  obtain ⟨y₂, hy₂⟩ := hfl T hT (2 ^ 18 * CE + 2 ^ 17) 1 (by positivity) one_pos
  refine ⟨max y₀ (max y₂ T.floorMin), fun y hy R hOn hwell hx' hmove s hsc hL => ?_⟩
  have hy0 : y₀ ≤ y := (le_max_left _ _).trans hy
  have hy2 : y₂ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hyT : T.floorMin ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hℓ := hOn.params_eq
  have hyp : ClassSumHypotheses R.params T.cE CE := by
    rw [hℓ]
    exact htab T hT CE 1 y hCE hyT fun x hx => hy₂ x (hy2.trans hx)
  have adm : R.params.Admissible := by
    rw [hℓ]
    exact hT.fits y hyT
  have hy1 : R.params.y₁ ≤ R.coupling := by
    rw [hℓ]
    exact hOn.le_coupling
  have : NeZero R.params.side := ⟨by have := adm.L_ge; omega⟩
  refine
    { nonneg := coarseLabelScore_nonneg hs₁ hsc.nonneg
      borel := coarseLabelScore_measurable _ hsc.borel
      gauge := fun n _ Y g ω y => coarseLabelScore_gauge hsc.gauge Y g ω y
      price := fun n _ hn V Y ω P hull hP hoff => ?_ }
  refine hprice y hy0 R hOn hwell hx' hmove s hsc n hn V Y ω P hull hP hoff _ ?_
  intro ν W Yt ωt bad b _ hst
  have hY : Y = coarseHull R.params.side R.range R.nextRange bad Yt (hotCoreSites R V) :=
    (congrArg Sigma.fst hst).symm
  have hP' : P ⊆ chainComponents R.nextRange
      (coarseHull R.params.side R.range R.nextRange bad Yt (hotCoreSites R V)) := hY ▸ hP
  exact hsum R.params T.cE CE adm hyp R.coupling R.nextCoupling hy1 hmove n hn.1 V W bad Yt P hP'
section Tower
variable {Tb : ParameterAssignment} {y β : ℝ} {T : StageTower (Tb.stepParameters y)} {K : ℕ}
private theorem hasExpansion_stage (hret : ExpansionReturnsAt (Tb.stepParameters y))
    (hwil : ∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β))
    (hr : IsImageTower Tb y T β K) :
    ∀ j ≤ K, HasExpansion (Tb.stepParameters y) (T.stage j).depth (T.stage j).coupling (T.stage j).functional := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : (T.stage 0).coupling = β := hr.coupling_eq 0 (Nat.zero_le _)
    have hy : y ≤ (T.stage 0).coupling := (hr.onFamily 0 (Nat.zero_le _)).le_coupling
    have h1 := hwil β (h0 ▸ hy)
    have h2 : (T.stage 0).depth = 0 := hr.startsAtWilson.depth_eq
    have h3 : (T.stage 0).functional = wilsonWeight β := hr.startsAtWilson.functional_eq
    rw [h0, h2, h3]
    exact h1
  | succ j ih =>
    intro hj
    have hj' : j ≤ K := by omega
    obtain ⟨x', ⟨hexp', -⟩, huniq⟩ := hret _ _ _ (hr.onFamily j hj').le_coupling (ih hj')
    have hc : ColdExpansion (Tb.stepParameters y) ((T.stage j).depth + 1) (T.stage (j + 1)).coupling
        (kernelImage (Tb.stepParameters y) (T.stage j).coupling (T.stage j).functional) (T.stage (j + 1)).density :=
      (hr.onFamily (j + 1) hj).isStep.1.1
    have := huniq _ _ hc
    show HasExpansion (Tb.stepParameters y) ((T.stage j).depth + 1) (T.stage (j + 1)).coupling
      (kernelImage (Tb.stepParameters y) (T.stage j).coupling (T.stage j).functional)
    rw [this]
    exact hexp'
private theorem functional_stage (hr : IsImageTower Tb y T β K) :
    ∀ j ≤ K + 1, (T.stage j).functional = (couplingFlow (Tb.stepParameters y) β j).2 := by
  intro j
  induction j with
  | zero => exact fun _ => hr.startsAtWilson.functional_eq
  | succ j ih =>
    intro hj
    show kernelImage (Tb.stepParameters y) (T.stage j).coupling (T.stage j).functional =
      kernelImage (Tb.stepParameters y) (couplingFlow (Tb.stepParameters y) β j).1
        (couplingFlow (Tb.stepParameters y) β j).2
    rw [ih (by omega), hr.coupling_eq j (by omega)]
private theorem labelSize_priceBounds {s₁ : ℝ} (hDr : Tb.Admissible) (hadm : (Tb.stepParameters y).Admissible)
    (hret : ExpansionReturnsAt (Tb.stepParameters y))
    (hwil : ∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β))
    (hcold : ∀ R : StepSetup, R.OnParameters Tb y → R.IsSymmetricWeight →
      ColdExpansion R.params (R.depth + 1) (R.shiftedCoupling Tb.lam) (kernelImage R.params R.coupling R.functional)
          (R.renormalizedDensity Tb.lam) ∧
        |R.shiftedCoupling Tb.lam - R.coupling| ≤ 2 * R.params.B)
    (hup : ∀ R : StepSetup, R.OnParameters Tb y → R.IsWellPosed → R.nextCoupling = R.shiftedCoupling Tb.lam →
      |R.nextCoupling - R.coupling| ≤ 2 * R.params.B →
      ∀ s : R.labels.Ω → ℝ, PriceBoundsScore R.params R.coupling R.labels R.clusterFactor R.siteDensity s →
        ∀ hL : CoarseLabelFacts R,
        PriceBoundsScore R.params R.nextCoupling (coarseLabelSpace R hL) (coarseFactorExpansion R)
          (R.stateDensity Tb.lam) (coarseLabelScore s₁ s))
    (hmoved : ∀ x : ℝ, y ≤ x → ∀ x' : ℝ, |x' - x| ≤ 2 * Tb.B → clusterRange x' ≤ clusterRange x + 1)
    (hrange : 2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 16 ≤ clusterRange y)
    (hr : IsImageTower Tb y T β K) (h0 : 0 ≤ y) :
    ∀ j ≤ K, PriceBoundsScore (Tb.stepParameters y) (T.stage j).coupling (T.stage j).labels
      (T.stage j).clusterFactor (T.stage j).siteDensity (labelSize T s₁ j) := by
  intro j
  induction j with
  | zero =>
    intro _
    exact priceBoundsScore_zero (hr.onFamily 0 (Nat.zero_le _)).isStep.1.2 fun _ => rfl
  | succ j ih =>
    intro hj
    have hj' : j ≤ K := by omega
    have hOn := hr.onFamily j hj'
    have hOn' := hr.onFamily (j + 1) hj
    have hexp := hasExpansion_stage hret hwil hr j hj'
    have hsym : (T.stage j).toStepSetup.IsSymmetricWeight := fun n _ h => hexp.1 n h
    obtain ⟨hc', hmv⟩ := hcold _ hOn hsym
    obtain ⟨x', -, huniq⟩ := hret _ _ _ hOn.le_coupling hexp
    have hc : ColdExpansion (Tb.stepParameters y) ((T.stage j).depth + 1) (T.stage (j + 1)).coupling
        (kernelImage (Tb.stepParameters y) (T.stage j).coupling (T.stage j).functional) (T.stage (j + 1)).density :=
      hOn'.isStep.1.1
    have hx' : (T.stage j).toStepSetup.nextCoupling = (T.stage j).toStepSetup.shiftedCoupling Tb.lam :=
      (huniq _ _ hc).trans (huniq _ _ hc').symm
    have hmove : |(T.stage j).toStepSetup.nextCoupling - (T.stage j).toStepSetup.coupling| ≤
        2 * (T.stage j).toStepSetup.params.B := by
      rw [hx']
      exact hmv
    have hxy : y ≤ (T.stage j).coupling := hOn.le_coupling
    have hxy' : y ≤ (T.stage j).nextCoupling := hOn'.le_coupling
    have hr1 : 2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 16 ≤ clusterRange (T.stage j).coupling :=
      hrange.trans (clusterRange_mono h0 hxy)
    have hr2 : 2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 16 ≤ clusterRange (T.stage j).nextCoupling :=
      hrange.trans (clusterRange_mono h0 hxy')
    have hwell : (T.stage j).toStepSetup.IsWellPosed :=
      { hasExpansions := hOn.isStep.1
        admissible := hadm
        isCutoff := by
          have h1 : (T.stage j).toStepSetup.barrierFn = Tb.cutoff := hOn.barrierFn_eq
          rw [h1]
          exact hDr.cut
        range_le := hOn.isStep.2.2
        nextRange_le := hmoved _ hxy _ hmove
        nextRange_ge := by
          show 2 ^ 16 ≤ clusterRange (T.stage j).nextCoupling
          omega
        range_ge_side := by
          show 2 ^ 40 * Tb.side ≤ clusterRange (T.stage j).coupling
          omega
        range_ge_base := by
          show 4 * Tb.n₀ + 2 ^ 16 ≤ clusterRange (T.stage j).coupling
          omega
        coupling_pos := lt_of_lt_of_le (by linarith [hadm.y₁_ge, show (Tb.stepParameters y).y₁ = y from rfl]) hxy
        functional_spec := hsym }
    have h1 := hup _ hOn hwell hx' hmove _ (ih hj') (T.labelFacts _ T.two_le_side)
    have himg : T.siteDensities (T.stage j).toStepSetup = (T.stage j).toStepSetup.stateDensity Tb.lam :=
      hr.siteDensities_eq j (by omega)
    show PriceBoundsScore (Tb.stepParameters y) (T.stage j).nextCoupling
      (coarseLabelSpace (T.stage j).toStepSetup (T.labelFacts _ T.two_le_side))
      (coarseFactorExpansion (T.stage j).toStepSetup) (T.siteDensities (T.stage j).toStepSetup)
      (coarseLabelScore s₁ (labelSize T s₁ j))
    rw [himg]
    exact h1
end Tower
theorem totalSizeExpMoment (hD : StageDensity.stageStateDensityStatement)
    (hS : ScoredMassStatement) (hB : freeEnergyLowerBoundStatement) (hM : flowFunctionalIntegral)
    (hBo : StageStatesMeasurableStatement) (hC : ImageColdExpansion.ImageHasColdExpansion)
    (hb : scoredComponentPriceBound) (hsum : ClassExponentLePrice)
    (htab : ParameterChoiceMeetsClassSum) (hfl : StepFloors.EventuallyFloorConditions) :
    totalSizeExpMomentStatement := by
  classical
  have hB' : ∀ Tb : ParameterAssignment, ∃ C : ℝ, Tb.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
      ExpansionHolds (Tb.stepParameters y) →
      ∀ (β : ℝ) (t : ℕ), CouplingsAboveFloor (Tb.stepParameters y) β t → ∀ (n : ℕ) [NeZero n],
        IsBlockTorusSide (Tb.stepParameters y) n →
        Real.log (flowFunctionalAtTrivial (Tb.stepParameters y) β t n) -
            (C + 6 * Real.log (flowCoupling (Tb.stepParameters y) β t)) * (n : ℝ) ^ 4 ≤
          Real.log (torusPartition (Tb.stepParameters y) β t n) := by
    intro Tb
    by_cases h : Tb.Admissible
    · obtain ⟨C, y₀, hC'⟩ := hB Tb h
      exact ⟨C, fun _ => ⟨y₀, hC'⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Cb hCb using hB'
  refine ⟨fun Tb => 2 * (|Cb Tb| + Real.log 2 + 2 * Tb.E + 6), ?_⟩
  intro a ha
  obtain ⟨L₁, rtD, hrtD, hD'⟩ := hD a ha
  obtain ⟨rtC, hrtC, hC'⟩ := hC
  obtain ⟨rtP, hrtP, hP'⟩ := priceBoundsScore_coarse hb hsum htab hfl
  refine ⟨L₁, fun c => min (rtD c) (min (rtC c) (rtP c)), 0,
    fun c => lt_min (hrtD c) (lt_min (hrtC c) (hrtP c)), ?_⟩
  intro L hL hLL Tb hTa hTL hDr hCold _ hrt _
  have hrtD' : Tb.rt ≤ rtD Tb.toChainParameters := hrt.trans (min_le_left _ _)
  have hrtC' : Tb.rt ≤ rtC Tb.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrtP' : Tb.rt ≤ rtP Tb.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨0, fun Kr _ _ _ hKadm _ => ?_⟩
  have hs₁ : 0 ≤ Kr.s₁ := by
    have hf0 := hKadm 0
    have h1 := hf0.Kc_ge
    have h2 := hf0.N₀_nonneg
    have h3 : 0 ≤ Kr.C₀ + 2 := by
      rw [hf0.C₀_eq]
      have : 1 ≤ (Tb.stepParameters 0).coupling := hDr.a_ge
      linarith
    rw [hf0.s₁_eq]
    have h4 : 0 ≤ 2 * ((Tb.stepParameters 0).side : ℝ) ^ 4 * (Kr.C₀ + 2) := by positivity
    have : 1 ≤ (Tb.stepParameters 0).coupling := hDr.a_ge
    linarith
  obtain ⟨yD, hyD⟩ := hD' L hL hLL Tb hTa hTL hDr hrtD'
  obtain ⟨yC, hyC⟩ := hC' Tb hDr hCold hrtC'
  obtain ⟨yP, hyP⟩ := hP' Tb hDr hrtP' Kr.s₁ hs₁
  obtain ⟨yB, hyB⟩ := hCb Tb hDr
  obtain ⟨yF, hyF⟩ := hfl Tb hDr 1 1 one_pos one_pos
  refine ⟨max (max (max yD yC) (max yP yB)) (max (max yF Tb.floorMin)
    (max 3 (((2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 16 : ℕ) : ℝ) ^ 100))), ?_⟩
  intro y hy hret hwil
  have hyD' : yD ≤ y := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hy
  have hyC' : yC ≤ y := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hy
  have hyP' : yP ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hy
  have hyB' : yB ≤ y := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hy
  have hyF' : yF ≤ y := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hy
  have hyT : Tb.floorMin ≤ y := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hy
  have hy3 : (3 : ℝ) ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hyk : ((2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 16 : ℕ) : ℝ) ^ 100 ≤ y :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hadm : (Tb.stepParameters y).Admissible := hDr.fits y hyT
  have hrange : 2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 16 ≤ clusterRange y := le_clusterRange hyk
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hmoved : ∀ x : ℝ, y ≤ x → ∀ x' : ℝ, |x' - x| ≤ 2 * Tb.B → clusterRange x' ≤ clusterRange x + 1 :=
    fun x hx x' hxx => ((hyF x (hyF'.trans hx)).stable_nearby.2 x' hxx).2.2.2
  have hholds : ExpansionHolds (Tb.stepParameters y) := ⟨hret, hwil⟩
  have hDens := hyD y hyD' hret hwil
  have hFree := hyB y hyB' hholds
  intro g β K m T u n _ hAt
  have hr : IsImageTower Tb y T β K := hAt.chain.reads_flow
  have hu : u ≤ K := hAt.le
  have hLge : 2 ^ 40 ≤ Tb.side := hDr.L_ge
  have hn₀ : 4096 ≤ Tb.n₀ := hDr.n₀_ge
  have hn : IsBlockTorusSide (Tb.stepParameters y) n := by
    have hv : Tb.side * Tb.n₀ ≤ 2 * Tb.side ^ m := hAt.chain.volume_le
    have hm : m ≠ 0 := by
      rintro rfl
      have : 2 ^ 40 * 4096 ≤ Tb.side * Tb.n₀ := Nat.mul_le_mul hLge hn₀
      simp only [pow_zero, mul_one] at hv
      omega
    have hne : n = 2 * Tb.side ^ m * Tb.side ^ (K - u) := by
      rw [hAt.side_eq, torusSideAtLevel, fineSide_eq]
    refine ⟨?_, ?_⟩
    · show Tb.side ∣ n
      rw [hne]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ hm) _) _
    · show Tb.side * Tb.n₀ ≤ n
      rw [hne]
      exact hv.trans (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
  have hReach : CouplingsAboveFloor (Tb.stepParameters y) β u := fun j hj => by
    have h1 : (T.stage j).coupling = (couplingFlow (Tb.stepParameters y) β j).1 := hr.coupling_eq j (by omega)
    have h2 : y ≤ (T.stage j).coupling := (hr.onFamily j (by omega)).le_coupling
    show y ≤ (couplingFlow (Tb.stepParameters y) β j).1
    rw [← h1]
    exact h2
  have hxu : (T.stage u).coupling = flowCoupling (Tb.stepParameters y) β u := hr.coupling_eq u (by omega)
  have hxy : y ≤ (T.stage u).coupling := (hr.onFamily u hu).le_coupling
  have hx0 : 0 < (T.stage u).coupling := by linarith
  have hbase : 4 * (Tb.stepParameters y).n₀ + 2 ^ 16 ≤ clusterRange (T.stage u).coupling := by
    have : 2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 16 ≤ clusterRange (T.stage u).coupling :=
      hrange.trans (clusterRange_mono hy0 hxy)
    show 4 * Tb.n₀ + 2 ^ 16 ≤ clusterRange (T.stage u).coupling
    omega
  obtain ⟨hc, hh⟩ := (hr.onFamily u hu).isStep.1
  have hprice : PriceBoundsScore (Tb.stepParameters y) (T.stage u).coupling (T.stage u).labels
      (T.stage u).clusterFactor (T.stage u).siteDensity (labelSize T Kr.s₁ u) :=
    labelSize_priceBounds hDr hadm hret hwil (hyC y hyC') (hyP y hyP') hmoved hrange hr hy0 u hu
  have hup := hS (Tb.stepParameters y) (T.stage u).depth (T.stage u).coupling (T.stage u).functional
    (T.stage u).density (T.stage u).labels (T.stage u).labelWeight (T.stage u).clusterFactor
    (T.stage u).siteDensity (labelSize T Kr.s₁ u) hadm hadm.E_ge hx0 hbase hc hh hprice n hn
  obtain ⟨-, -, -, -, hZ⟩ := hM (Tb.stepParameters y) hadm β u n
  have hZ0 : ENNReal.ofReal (torusPartition (Tb.stepParameters y) β u n) ≠ 0 := by
    simpa using hZ
  have hZt : ENNReal.ofReal (torusPartition (Tb.stepParameters y) β u n) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfun : (T.stage u).functional = flowFunctional (Tb.stepParameters y) β u :=
    functional_stage hr u (by omega)
  have htower : IsTowerAtParameters Tb y T β u :=
    ⟨hr.startsAtWilson, fun j hj => hr.coupling_eq j (by omega), fun j hj => hr.onFamily j (by omega)⟩
  have hsig : Measurable fun p : (Σ Y : Finset (TorusSite n), (Y → (T.stage u).labels.Ω)) =>
      ∑ z : TorusSite n, siteScore (labelSize T Kr.s₁ u) p.1 p.2 z := by
    refine measurable_of_sigma fun Y => ?_
    simp only [sum_siteScore]
    exact Finset.measurable_sum _ fun i _ => hprice.borel.comp (measurable_pi_apply i)
  have hsumm : Measurable fun q : StageState T u n => ∑ z : TorusSite n, siteScore (labelSize T Kr.s₁ u) q.2.1 q.2.2 z :=
    hsig.comp measurable_snd
  obtain ⟨G, hGdef⟩ : ∃ G : StageState T u n → ENNReal, ∀ q, G q =
      ENNReal.ofReal (Real.exp (∑ z : TorusSite n, siteScore (labelSize T Kr.s₁ u) q.2.1 q.2.2 z)) :=
    ⟨_, fun _ => rfl⟩
  have hG : Measurable G := by
    have : G = fun q => ENNReal.ofReal (Real.exp (∑ z : TorusSite n, siteScore (labelSize T Kr.s₁ u) q.2.1 q.2.2 z)) :=
      funext hGdef
    rw [this]
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hsumm)
  have hstate : Measurable (stageState T u n) := hBo _ hadm T u n
  have hf : Measurable fun w => Real.exp (totalSize T Kr.s₁ u n w) :=
    Real.measurable_exp.comp (hsumm.comp hstate)
  have hW : ∀ W : TorusField n, (open Classical in
      ∑ Y ∈ Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange (T.stage u).coupling) W),
        ∫⁻ ω, G (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage u).labelWeight n W Y ω)
          ∂(Measure.pi fun _ : Y => (T.stage u).labels.μ)) ≤
      ENNReal.ofReal ((T.stage u).functional n (trivialField n) * 2 ^ Fintype.card (TorusSite n) *
        Real.exp (2 * (Tb.stepParameters y).E * Fintype.card (TorusSite n))) := by
    intro W
    refine le_trans (le_of_eq ?_) (hup W)
    refine Finset.sum_congr rfl fun Y _ => lintegral_congr fun ω => ?_
    rw [hGdef]
    simp only [sum_siteScore]
    rw [ENNReal.ofReal_mul' (Real.exp_nonneg _), mul_comm]
  have hmain : ENNReal.ofReal (torusPartition (Tb.stepParameters y) β u n) *
      ∫⁻ w, G (stageState T u n w) ∂(markedSampleLaw T β u n) ≤
      ENNReal.ofReal ((T.stage u).functional n (trivialField n) * 2 ^ Fintype.card (TorusSite n) *
        Real.exp (2 * (Tb.stepParameters y).E * Fintype.card (TorusSite n))) := by
    refine (le_of_eq (hDens T β u n htower hAt.chain.marks hn G hG)).trans ?_
    refine (lintegral_mono hW).trans ?_
    simp
  have hcard : ((Fintype.card (TorusSite n) : ℕ) : ℝ) = (n : ℝ) ^ 4 := by
    simp [TorusSite, ZMod.card]
  have hl1 : 1 ≤ Real.log (flowCoupling (Tb.stepParameters y) β u) := by
    rw [← hxu, Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have hl : 0 ≤ Real.log (flowCoupling (Tb.stepParameters y) β u) := by linarith
  have hE0 : 0 ≤ (Tb.stepParameters y).E := by linarith [hadm.E_ge]
  have hnum := exp_bound_of_log_bound (Cf := |Cb Tb| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6) hcard
    (by positivity) hZ (hFree β u hReach n hn) hl hE0 rfl
  have htriv : (T.stage u).functional n (trivialField n) = flowFunctionalAtTrivial (Tb.stepParameters y) β u n := by
    rw [hfun]
    rfl
  rw [← htriv] at hnum
  have hI : ∫⁻ w, G (stageState T u n w) ∂(markedSampleLaw T β u n) ≤
      ENNReal.ofReal (Real.exp ((|Cb Tb| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6) *
        (1 + Real.log (flowCoupling (Tb.stepParameters y) β u)) * (n : ℝ) ^ 4)) := by
    have h2 : ENNReal.ofReal (torusPartition (Tb.stepParameters y) β u n) *
          ∫⁻ w, G (stageState T u n w) ∂(markedSampleLaw T β u n) ≤
        ENNReal.ofReal (torusPartition (Tb.stepParameters y) β u n) *
          ENNReal.ofReal (Real.exp ((|Cb Tb| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6) *
            (1 + Real.log (flowCoupling (Tb.stepParameters y) β u)) * (n : ℝ) ^ 4)) := by
      rw [← ENNReal.ofReal_mul hZ.le]
      exact hmain.trans (ENNReal.ofReal_le_ofReal hnum)
    have h3 := mul_le_mul_right h2 (ENNReal.ofReal (torusPartition (Tb.stepParameters y) β u n))⁻¹
    rwa [← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hZ0 hZt, one_mul, one_mul] at h3
  have hGf : ∀ w, ENNReal.ofReal (Real.exp (totalSize T Kr.s₁ u n w)) = G (stageState T u n w) := fun w => by
    rw [hGdef]
    rfl
  have hI' : ∫⁻ w, ENNReal.ofReal (Real.exp (totalSize T Kr.s₁ u n w)) ∂(markedSampleLaw T β u n) ≤
      ENNReal.ofReal (Real.exp ((|Cb Tb| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6) *
        (1 + Real.log (flowCoupling (Tb.stepParameters y) β u)) * (n : ℝ) ^ 4)) := by
    simp only [hGf]
    exact hI
  have hint : Integrable (fun w => Real.exp (totalSize T Kr.s₁ u n w)) (markedSampleLaw T β u n) := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun w => (Real.exp_pos _).le)]
    exact hI'.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => (Real.exp_pos _).le)
    hf.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _) (hI'.trans (ENNReal.ofReal_le_ofReal ?_))
  refine Real.exp_le_exp.mpr ?_
  have hCf0 : 0 ≤ |Cb Tb| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6 := by
    have h1 := abs_nonneg (Cb Tb)
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
    linarith
  have hcu : stageCoupling T u = flowCoupling (Tb.stepParameters y) β u := hxu
  rw [hcu]
  show (|Cb Tb| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6) *
      (1 + Real.log (flowCoupling (Tb.stepParameters y) β u)) * (n : ℝ) ^ 4 ≤
    2 * (|Cb Tb| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6) *
      Real.log (flowCoupling (Tb.stepParameters y) β u) * (n : ℝ) ^ 4
  have h1 : 1 + Real.log (flowCoupling (Tb.stepParameters y) β u) ≤
      2 * Real.log (flowCoupling (Tb.stepParameters y) β u) := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hCf0
  have h3 : 0 ≤ (n : ℝ) ^ 4 := by positivity
  have h4 := mul_le_mul_of_nonneg_right h2 h3
  calc _ ≤ _ := h4
    _ = _ := by ring
end YangMills.Construction.HullTrees
end

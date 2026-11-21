import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsAreTheGasProof
import YangMills.Construction.LawByMomentsOfTheFlow.FreeCoresAreRareGivenAState
import YangMills.Construction.ResponseInTheExpansion.FreeCoresOfAStepAreRareProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open WeightedResponses ResponseInTheExpansion ClusterExpansionOfAStep StepSettings StepGas StepCosts RenormalizationStepParameters TorusFields TorusLumps BlockAverages BlockPlaces LumpContours
namespace FreeCoresRare
section States
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem measurable_fieldWithStoredLinks (q : CoarseState R n) : Measurable q.fieldWithStoredLinks := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fieldWithStoredLinks <;> assumption
private theorem measurable_fillLabels (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable (q.fillLabels Yt) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fillLabels <;> assumption
private theorem coarseStateOf_const (q : CoarseState R n) (C : Finset (TorusSite n))
    (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) {W W' : TorusField (n * R.params.side)} {ν ν' : q.unlabelled Yt → R.labels.Ω}
    (h : coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) :
    coarseStateOf R C (q.fieldWithStoredLinks W') Yt (q.fillLabels Yt ν') bad b = q := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.coarseStateOf_fill <;> assumption
end States
section Sigma
variable {X : Type} [MeasurableSpace X]
theorem measurableSet_sigma_fst_eq {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
theorem measurable_of_measurableSet_fibres {D Z : Type} [Countable D] [MeasurableSpace Z] (f : X → D)
    (hf : ∀ d, MeasurableSet {x | f x = d}) (G : D → X → Z) (hG : ∀ d, Measurable (G d)) :
    Measurable fun x => G (f x) x := by apply _root_.YangMills.SharedProofs.p23008 <;> assumption
end Sigma
section Gas
variable {R : StepSetup} {n : ℕ} [NeZero n]
def unitCaseFunctional : CaseFunctional R n := fun _ _ _ _ _ => 1
theorem isCaseFunctional_unitCaseFunctional : IsCaseFunctional (unitCaseFunctional : CaseFunctional R n) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdGasIdentity.isCaseFunctional_unitFunctional <;> assumption
open Classical in
theorem gasIntegrand_unitCaseFunctional (G : GasGround R n) {off : G.GasSpin → Prop} {z : G.GasSpin → ℝ}
    (h : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff off) G.weight z) (σ : G.Config) :
    G.gasIntegrand unitCaseFunctional σ = G.pairConstraint.weightDensity G.weight σ := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FreeCoresRare.gasIntegrand_constOne <;> assumption
theorem gasMass_unitCaseFunctional (G : GasGround R n) {off : G.GasSpin → Prop} {z : G.GasSpin → ℝ}
    (h : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff off) G.weight z) (A : Finset (TorusSite n)) :
    G.gasMass A unitCaseFunctional = G.partitionFunction A := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FreeCoresRare.gasMass_constOne <;> assumption
theorem measurable_gasIntegrand_unitCaseFunctional (G : GasGround R n) {off : G.GasSpin → Prop} {z : G.GasSpin → ℝ}
    (h : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff off) G.weight z) :
    Measurable (G.gasIntegrand unitCaseFunctional) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FreeCoresRare.measurable_gasIntegrand_constOne <;> assumption
theorem xi_ratio_bounds (G : GasGround R n) {ε : ℝ} (hε : 0 ≤ ε) (hpos : ∀ A, 0 < G.xi A)
    (hb : ∀ A Y, 1 - ε ≤ G.xi (insert Y A) / G.xi A ∧ G.xi (insert Y A) / G.xi A ≤ 1) (A : Finset (TorusSite n)) :
    1 - (A.card : ℝ) * ε ≤ G.xi A / G.xi ∅ ∧ G.xi A / G.xi ∅ ≤ 1 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FreeCoresRare.xi_ratio_bounds <;> assumption
open Classical in
theorem coarseStateMass_eq_caseMass (G : GasGround R n) :
    coarseStateMass R G.cut G.coarse G.state = G.caseMass ∅ unitCaseFunctional := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FreeCoresRare.coarseStateMass_eq_caseMass <;> assumption
theorem stepWeight_nonneg (hR : R.IsWellPosed) (hS : StepTransitionDensityBounds) (hn : R.params.n₀ ≤ n)
    {C : Finset (TorusSite n)} {V : TorusField n} {W : TorusField (n * R.params.side)}
    {Yt : Finset (TorusSite (n * R.params.side))} (ω : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hh : IsHullState R.params R.range W Yt) :
    0 ≤ stepWeight R C V W Yt ω bad b := by apply _root_.YangMills.SharedProofs.p51114 <;> assumption
def configurationValue (C : Finset (TorusSite n)) (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (w : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : ℝ :=
  (configurationWeight R C V bad Yt b w.1 w.2).toReal
def configurationValueOver (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω)) : ℝ :=
  configurationValue C V bad Yt b (q.fieldWithStoredLinks p.1, q.fillLabels Yt p.2)
open Classical in
theorem caseIntegrand_unit_eq_ofReal (G : GasGround R n) {bad : Finset (TorusBond (n * R.params.side))}
    {Yt : Finset (TorusSite (n * R.params.side))} {b : BaseChoice R.params.side n} (W : TorusField (n * R.params.side))
    (ν : G.state.unlabelled Yt → R.labels.Ω)
    (hq : coarseStateOf R G.cut (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b = G.state) :
    G.caseIntegrand unitCaseFunctional bad Yt b W ν =
      ENNReal.ofReal (configurationValueOver G.cut G.coarse G.state bad Yt b (W, ν)) := by
  unfold GasGround.caseIntegrand configurationValueOver configurationValue configurationWeight
  by_cases hh : IsHullState R.params R.range (G.state.fieldWithStoredLinks W) Yt
  · rw [if_pos (And.intro hh hq)]
    dsimp only
    rw [if_pos hh, ENNReal.ofReal_toReal ENNReal.ofReal_ne_top]
    exact one_mul _
  · rw [if_neg fun x => hh x.1]
    dsimp only
    rw [if_neg hh]
    simp
open Classical in
theorem caseTerm_eq_mul_configurationValueOver (hR : R.IsWellPosed) (hS : StepTransitionDensityBounds)
    (hn : R.params.n₀ ≤ n) (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n)
    (f : Finset (TorusBond (n * R.params.side)) → Finset (TorusSite (n * R.params.side)) → ℝ)
    {bad : Finset (TorusBond (n * R.params.side))} {Yt : Finset (TorusSite (n * R.params.side))}
    {b : BaseChoice R.params.side n} (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω)
    (hq : coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) :
    caseTerm R C V q (fun _ Yt _ bad _ => f bad Yt) bad Yt b W ν =
      f bad Yt * configurationValueOver C V q bad Yt b (W, ν) := by
  unfold WeightedResponses.caseTerm configurationValueOver configurationValue configurationWeight
  by_cases hh : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt
  · rw [if_pos (And.intro hh hq)]
    dsimp only
    rw [if_pos hh, ENNReal.toReal_ofReal (stepWeight_nonneg hR hS hn _ bad b hh)]
  · rw [if_neg fun x => hh x.1]
    dsimp only
    rw [if_neg hh]
    simp
open Classical in
theorem caseTerm_eq_zero_of_ne (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n)
    (F : CaseFunction R n) {bad : Finset (TorusBond (n * R.params.side))} {Yt : Finset (TorusSite (n * R.params.side))}
    {b : BaseChoice R.params.side n} (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω)
    (hq : coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b ≠ q) :
    caseTerm R C V q F bad Yt b W ν = 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FreeCoresRare.caseTerm_eq_zero <;> assumption
open Classical in
theorem caseIntegrand_eq_zero_of_ne (G : GasGround R n) (F : CaseFunctional R n)
    {bad : Finset (TorusBond (n * R.params.side))} {Yt : Finset (TorusSite (n * R.params.side))}
    {b : BaseChoice R.params.side n} (W : TorusField (n * R.params.side)) (ν : G.state.unlabelled Yt → R.labels.Ω)
    (hq : coarseStateOf R G.cut (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b ≠ G.state) :
    G.caseIntegrand F bad Yt b W ν = 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FreeCoresRare.caseIntegrand_eq_zero <;> assumption
open Classical in
theorem caseMean_le_card_mul_exp (hR : R.IsWellPosed) (hS : StepTransitionDensityBounds)
    (hWB : ConfigurationWeightMeasurable) (hr : PartitionRatioBounds) (hn : R.params.n₀ ≤ n) (G : GasGround R n) (c : ℝ)
    (hcols : ∀ off : G.GasSpin → Prop,
      ∃ h : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff off) G.weight (G.spinActivity c),
        G.HasSmallColumns off c h)
    (K : ENNReal) (hKt : K ≠ ⊤) (hK0 : K ≠ 0)
    (hmass : ∀ A, G.caseMass A unitCaseFunctional = K * G.partitionFunction A)
    (hcold : 0 < G.coldWeight) (A : Finset (TorusSite n))
    (f : Finset (TorusBond (n * R.params.side)) → Finset (TorusSite (n * R.params.side)) → ℝ)
    (h01 : ∀ bad Yt, f bad Yt = 0 ∨ f bad Yt = 1)
    (hoff : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side)) (ν : G.state.unlabelled Yt → R.labels.Ω),
      coarseStateOf R G.cut (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b = G.state →
        f bad Yt = 1 → ¬ G.CaseAvoids A bad Yt) :
    caseMean R G.cut G.coarse G.state (fun _ Yt _ bad _ => f bad Yt) ≤
      (A.card : ℝ) * Real.exp (-(7 * c * R.coupling)) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FreeCoresRare.caseMean_le <;> assumption
open Classical in
theorem not_caseAvoids_of_not_freeCoresAvoid (hL : R.params.side ≤ 6 * R.range) (G : GasGround R n)
    {Z : Finset (TorusSite n)} {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))}
    {ωt : Yt → R.labels.Ω} {bad : Finset (TorusBond (n * R.params.side))} {b : BaseChoice R.params.side n}
    (hG : coarseStateOf R G.cut W Yt ωt bad b = G.state) (hmiss : ¬ FreeCoresAvoid R Yt bad G.cut Z) :
    ¬ G.CaseAvoids (blocksNearFreeCores R.params.side R.range Z) bad Yt := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FreeCoresRare.not_caseAvoids <;> assumption
end Gas
section Borel
open Classical in
theorem measurableSet_hotCoreSites_eq (R : StepSetup) {n : ℕ} [NeZero n] (C : Finset (TorusSite n)) :
    MeasurableSet {V : TorusField n | hotCoreSites R V = C} := by apply _root_.YangMills.SharedProofs.p5873 <;> assumption
end Borel
end FreeCoresRare
open FreeCoresRare in
open Classical in
theorem freeCoresRareGivenState_holds (hM : conditionalMeanIsCaseMeanStatement)
    (hCol₀ : GasColumnsSmall) (hRat : PartitionRatioBounds) (hImg₀ : coarseStateGasStatement)
    (hSum₀ : CaseMassEqGasMass) (hGr₀ : HullStateIsHotCase)
    (hZ : CoarseWeightZeroOfFactorZero) (hHull : CoarseHullIsHullState)
    (hWB : ConfigurationWeightMeasurable) (hSD : StepTransitionDensityBounds)
    (hSt : StageStatesMeasurableStatement) (hD : forgetLastStepStatement) :
    freeCoresRareGivenStateStatement := by
  obtain ⟨r1, hr1, hCol⟩ := hCol₀
  obtain ⟨r2, hr2, hImg⟩ := hImg₀
  intro a ha
  obtain ⟨L₀, r0, hr0, hM₀⟩ := hM a ha
  refine ⟨L₀, fun c => min (r0 c) (min (r1 c) (r2 c)),
    fun c => lt_min (hr0 c) (lt_min (hr1 c) (hr2 c)), fun L hodd hL Tb h1 h2 hTb hrt => ?_⟩
  obtain ⟨y0, hy0⟩ := hM₀ L hodd hL Tb h1 h2 hTb (hrt.trans (min_le_left _ _))
  obtain ⟨y1, hy1⟩ := hCol Tb hTb (hrt.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨y2, hy2⟩ := hImg Tb hTb (hrt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨y3, hy3⟩ := hSum₀ Tb hTb
  obtain ⟨y4, hy4⟩ := hGr₀ Tb hTb
  refine ⟨max y0 (max (max y1 y2) (max y3 (max y4 Tb.floorMin))),
    fun y hyy hret hwil T β s n _ hst hcut hco hF hx hb m o => ?_⟩
  have hMM := hy0 y ((le_max_left _ _).trans hyy) hret hwil
  have hy : max (max y1 y2) (max y3 (max y4 Tb.floorMin)) ≤ y := (le_max_right _ _).trans hyy
  have hon := hst.onFamily s le_rfl
  have e1 : y1 ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
  have e2 : y2 ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans hy)
  have e3 : y3 ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have e4 : y4 ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))
  have e5 : Tb.floorMin ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))
  have hfit : (Tb.stepParameters y).Admissible := hTb.fits y e5
  have hLam := hfit.depth_lt
  obtain ⟨hprob, hpres⟩ := hD (Tb.stepParameters y) hfit hLam T hcut hco β s n
  have : IsProbabilityMeasure (markedSampleLaw T β (s + 1) n) :=
    (hD (Tb.stepParameters y) hfit hLam T hcut hco β (s + 1) n).1
  set R := (T.stage s).toStepSetup with hRdef
  set Z := supBall o m with hZdef
  have hL6 : R.params.side ≤ 6 * R.range := by
    have h1 := hF.range_ge_side
    have h2 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
    omega
  have hn₀ : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne _))) hb.2
  let Fn : TorusField n → CaseFunction R n := fun V _ Yt _ bad _ =>
    if FreeCoresAvoid R Yt bad (hotCoreSites R V) Z then 0 else 1
  have hfst : Measurable (fun u : MarkedSample (Tb.stepParameters y) (s + 1) n => u.1) := hpres.measurable
  have hsnd : Measurable (fun u : MarkedSample (Tb.stepParameters y) (s + 1) n => u.2) := measurable_snd
  have hVm : Measurable (fun u : MarkedSample (Tb.stepParameters y) (s + 1) n => u.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp hsnd)
  have hBm : Measurable (fun u : MarkedSample (Tb.stepParameters y) (s + 1) n => u.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp hsnd)
  have hStm := (hSt (Tb.stepParameters y) hfit T s (n * (Tb.stepParameters y).side)).comp hfst
  have hg : Measurable fun u : MarkedSample (Tb.stepParameters y) (s + 1) n =>
      Fn u.2.2.1 (topField (Tb.stepParameters y) s (n * (Tb.stepParameters y).side) u.1)
        (stageState T s (n * (Tb.stepParameters y).side) u.1).2.1
        (stageState T s (n * (Tb.stepParameters y).side) u.1).2.2 u.2.2.2 u.2.1 := by
    refine _root_.YangMills.Construction.MomentLaw.FreeCoresRare.measurable_of_measurableSet_fibres
      (D := Finset (TorusSite (n * (Tb.stepParameters y).side)) × Finset (TorusBond (n * (Tb.stepParameters y).side)) ×
        Finset (TorusSite n))
      (fun u : MarkedSample (Tb.stepParameters y) (s + 1) n =>
        ((stageState T s (n * (Tb.stepParameters y).side) u.1).2.1,
          (u.2.2.2 : Finset (TorusBond (n * (Tb.stepParameters y).side))), hotCoreSites R u.2.2.1)) ?_
      (fun d _ => if FreeCoresAvoid R d.1 d.2.1 d.2.2 Z then (0 : ℝ) else 1) (fun d => measurable_const)
    rintro ⟨a, b, c⟩
    have s1 : MeasurableSet {u : MarkedSample (Tb.stepParameters y) (s + 1) n |
        (stageState T s (n * (Tb.stepParameters y).side) u.1).2.1 = a} :=
      hStm (measurable_snd (_root_.YangMills.Construction.MomentLaw.FreeCoresRare.measurableSet_sigma_fst_eq a))
    have s2 : MeasurableSet {u : MarkedSample (Tb.stepParameters y) (s + 1) n |
        (u.2.2.2 : Finset (TorusBond (n * (Tb.stepParameters y).side))) = b} :=
      hBm (MeasurableSpace.measurableSet_top (s := {b}))
    have s3 : MeasurableSet {u : MarkedSample (Tb.stepParameters y) (s + 1) n | hotCoreSites R u.2.2.1 = c} :=
      hVm (measurableSet_hotCoreSites_eq R c)
    refine (s1.inter (s2.inter s3)).congr (Set.ext fun u => ⟨fun h => Prod.ext h.1 (Prod.ext h.2.1 h.2.2),
      fun h => ⟨(Prod.mk.inj h).1, (Prod.mk.inj (Prod.mk.inj h).2).1, (Prod.mk.inj (Prod.mk.inj h).2).2⟩⟩)
  have hbL : IsBlockTorusSide (Tb.stepParameters y) (n * (Tb.stepParameters y).side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
  have hae := hMM T β s n hst hcut hco hF hbL hb.1 Fn hg
    ⟨1, fun u => by
      dsimp only [Fn]
      split_ifs <;> simp⟩
  have hae1 := hMM T β s n hst hcut hco hF hbL hb.1 (fun _ _ _ _ _ _ => (1 : ℝ)) measurable_const
    ⟨1, fun u => by simp⟩
  have hmle : stageSigma T (s + 1) n ≤ markedSampleMeasurableSpace (Tb.stepParameters y) (s + 1) n :=
    (hSt (Tb.stepParameters y) hfit T (s + 1) n).comap_le
  set bd := ((blocksNearFreeCores (Tb.stepParameters y).side R.range Z).card : ℝ) *
    Real.exp (-(7 * Tb.gasRate * (T.stage s).coupling)) with hbd
  set g : MarkedSample (Tb.stepParameters y) (s + 1) n → ℝ := fun u =>
      Fn u.2.2.1 (topField (Tb.stepParameters y) s (n * (Tb.stepParameters y).side) u.1)
        (stageState T s (n * (Tb.stepParameters y).side) u.1).2.1
        (stageState T s (n * (Tb.stepParameters y).side) u.1).2.2 u.2.2.2 u.2.1 with hgdef
  have hpt : ∀ᵐ u ∂(markedSampleLaw T β (s + 1) n),
      ((markedSampleLaw T β (s + 1) n)[g | stageSigma T (s + 1) n]) u ≤ bd := by
    filter_upwards [hae, hae1] with u h h1
    rw [h]
    have h1' : (1 : ℝ) = caseMean R (hotCoreSites R u.2.2.1) u.2.2.1 (stageState T (s + 1) n u).2
        (fun _ _ _ _ _ => (1 : ℝ)) := by
      rw [← h1]
      have e := condExp_const (μ := markedSampleLaw T β (s + 1) n) hmle (1 : ℝ)
      exact (congrFun e u).symm
    set q : CoarseState R n := (stageState T (s + 1) n u).2 with hq
    set V := u.2.2.1 with hV
    have hull : IsHullState R.params R.nextRange V q.1 :=
      hHull (Tb.stepParameters y) hfit R.range R.nextRange hF.range_le hF.nextRange_ge n hb.1 V u.2.2.2
        (stageState T s (n * (Tb.stepParameters y).side) u.1).2.1
    have hnz : coarseStateWeight R (hotCoreSites R V) V q ≠ 0 := fun h0 => by
      unfold caseMean at h1'
      rw [h0, div_zero] at h1'
      exact one_ne_zero h1'
    have hΦ : ∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0 := fun X hX h0 =>
      hnz (hZ R hF n hb V q hull ⟨X, hX, h0⟩)
    have hhot := hy4 y e4 R hon hF n hb V q hull hΦ
    have hG : (hotCaseGround R V q).IsAdmissibleGround := Or.inr hhot
    have cols := fun off => hy1 y e1 R hon hx n (hotCaseGround R V q) hG off
    obtain ⟨-, hcold, -, hms, -⟩ := hy2 y e2 R hon hx n (hotCaseGround R V q) hG
    obtain ⟨hw, -⟩ := cols fun _ => False
    set K := ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
      ENNReal.ofReal (∏ X ∈ chainComponents R.nextRange (hotCaseGround R V q).state.1,
        coarseFactor (hotCaseGround R V q).coarse (hotCaseGround R V q).state X) with hK
    have hKt : K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hK0 : K ≠ 0 := fun e => hnz (by
      unfold coarseStateWeight
      have e' : coarseStateMass R (hotCoreSites R V) V q = K * (hotCaseGround R V q).partitionFunction ∅ := hms
      rw [e', e, zero_mul]
      rfl)
    have hmass : ∀ A', (hotCaseGround R V q).caseMass A' unitCaseFunctional =
        K * (hotCaseGround R V q).partitionFunction A' := fun A' => by
      rw [hy3 y e3 R hon hx n (hotCaseGround R V q) hG A' unitCaseFunctional isCaseFunctional_unitCaseFunctional
        (measurable_gasIntegrand_unitCaseFunctional (hotCaseGround R V q) hw),
        gasMass_unitCaseFunctional (hotCaseGround R V q) hw]
    exact caseMean_le_card_mul_exp hF hSD hWB hRat hn₀ (hotCaseGround R V q) Tb.gasRate cols K hKt hK0 hmass hcold
      (blocksNearFreeCores R.params.side R.range Z)
      (fun bad Yt => if FreeCoresAvoid R Yt bad (hotCoreSites R V) Z then 0 else 1)
      (fun bad Yt => by
        split_ifs
        · exact Or.inl rfl
        · exact Or.inr rfl)
      (fun bad Yt b W ν hst hf1 => not_caseAvoids_of_not_freeCoresAvoid hL6 (hotCaseGround R V q) hst fun hm =>
        zero_ne_one ((if_pos hm : (if FreeCoresAvoid R Yt bad (hotCoreSites R V) Z then (0 : ℝ) else 1) = 0).symm.trans hf1))
  have hgE : g = {u | ¬ StepAvoids T s m o u}.indicator (fun _ => (1 : ℝ)) := by
    funext u
    by_cases hu : StepAvoids T s m o u
    · rw [Set.indicator_of_notMem (by simpa using hu)]
      exact if_pos hu
    · rw [Set.indicator_of_mem (by simpa using hu)]
      exact if_neg hu
  have hE : MeasurableSet {u | ¬ StepAvoids T s m o u} := by
    have e : {u | ¬ StepAvoids T s m o u} = g ⁻¹' {1} := by
      ext u
      rw [hgE]
      by_cases hu : StepAvoids T s m o u <;> simp [hu]
    rw [e]
    exact hg (measurableSet_singleton 1)
  rw [← hgE]
  exact ⟨hE, hpt⟩
end YangMills.Construction.MomentLaw
end

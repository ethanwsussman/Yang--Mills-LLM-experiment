import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsAreTheGasProof
import YangMills.Construction.CellOfTheFlow.LongClassesAtAllLevelsProof
import YangMills.Construction.ClusterExpansionOfAStep.AZeroFactorKillsTheState
import YangMills.Construction.ClusterExpansionOfAStep.HullStatesAreGrounds
import YangMills.Construction.ClusterExpansionOfAStep.ImageAtAGroundIsTheSumOverTheGas
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsAGas
import YangMills.Construction.ClusterExpansionOfAStep.RatiosOfXi
import YangMills.Construction.ResponseInTheExpansion.BoundedFunctionsOfTheCasesAreIntegrableProof
import YangMills.Construction.ResponseInTheExpansion.FreeCoresOfAStepAreRare
import YangMills.Construction.ResponseInTheExpansion.MeansGivenAStateAreMeansOverItsCases
import YangMills.Construction.ResponseInTheExpansion.TheDrawBelowHasItsLaw
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.ResponseInTheExpansion
open ClusterExpansionOfAStep StepSettings StepGas StepCosts TorusFields TorusLumps RenormalizationStepParameters WeightedResponses BlockAverages LumpContours
namespace FreeCoresRare
section States
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem measurable_fieldWithStoredLinks (q : CoarseState R n) : Measurable q.fieldWithStoredLinks := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fieldWithStoredLinks <;> assumption
private theorem measurable_fillLabels (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable (q.fillLabels Yt) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fillLabels <;> assumption
private theorem coarseStateOf_const (q : CoarseState R n) (C : Finset (TorusSite n))
    (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) {W W' : TorusField (n * R.params.side)}
    {ν ν' : q.unlabelled Yt → R.labels.Ω}
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
def constOneCase : CaseFunctional R n := fun _ _ _ _ _ => 1
theorem isCaseFunctional_constOne : IsCaseFunctional (constOneCase : CaseFunctional R n) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdGasIdentity.isCaseFunctional_unitFunctional <;> assumption
open Classical in
theorem gasIntegrand_constOne (G : GasGround R n) {off : G.GasSpin → Prop} {z : G.GasSpin → ℝ}
    (h : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff off) G.weight z) (σ : G.Config) :
    G.gasIntegrand constOneCase σ = G.pairConstraint.weightDensity G.weight σ := by
  unfold GasGround.gasIntegrand Dobrushin.PairConstraint.weightDensity
  by_cases hσ : G.pairConstraint.IsAdmissible σ
  · rw [if_pos hσ, if_pos hσ]
    have hp := h.pos_of_admissible σ hσ
    have hw : G.weight σ = (settingMass (G.settingOf (G.familyOf σ))).toReal := by
      unfold GasGround.weight
      rw [if_pos hσ]
    rw [hw] at hp ⊢
    have hne : settingMass (G.settingOf (G.familyOf σ)) ≠ ⊤ := fun e => by
      rw [e] at hp
      simp at hp
    rw [ENNReal.ofReal_toReal hne]
    unfold ChartSetting.settingIntegral settingMass constOneCase
    simp only [one_mul]
  · rw [if_neg hσ, if_neg hσ]
theorem gasMass_constOne (G : GasGround R n) {off : G.GasSpin → Prop} {z : G.GasSpin → ℝ}
    (h : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff off) G.weight z) (A : Finset (TorusSite n)) :
    G.gasMass A constOneCase = G.partitionFunction A :=
  lintegral_congr (gasIntegrand_constOne G h)
theorem measurable_gasIntegrand_constOne (G : GasGround R n) {off : G.GasSpin → Prop} {z : G.GasSpin → ℝ}
    (h : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff off) G.weight z) :
    Measurable (G.gasIntegrand constOneCase) := by
  have e : G.gasIntegrand constOneCase = G.pairConstraint.weightDensity G.weight := funext (gasIntegrand_constOne G h)
  rw [e]
  exact h.measurable_weightDensity
theorem xi_ratio_bounds (G : GasGround R n) {ε : ℝ} (hε : 0 ≤ ε) (hpos : ∀ A, 0 < G.xi A)
    (hb : ∀ A Y, 1 - ε ≤ G.xi (insert Y A) / G.xi A ∧ G.xi (insert Y A) / G.xi A ≤ 1) (A : Finset (TorusSite n)) :
    1 - (A.card : ℝ) * ε ≤ G.xi A / G.xi ∅ ∧ G.xi A / G.xi ∅ ≤ 1 := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    rw [div_self (hpos ∅).ne']
    simp
  | insert Y A hY ih =>
    obtain ⟨h1, h2⟩ := hb A Y
    have e : G.xi (insert Y A) / G.xi ∅ = (G.xi (insert Y A) / G.xi A) * (G.xi A / G.xi ∅) := by
      have e1 := (hpos A).ne'
      have e2 := (hpos ∅).ne'
      field_simp
    rw [e, Finset.card_insert_of_notMem hY]
    have ht0 : 0 < G.xi A / G.xi ∅ := div_pos (hpos _) (hpos _)
    have a1 := mul_le_mul_of_nonneg_right h1 ht0.le
    have a2 := mul_le_mul_of_nonneg_right h2 ht0.le
    have a3 : ε * (G.xi A / G.xi ∅) ≤ ε := by
      have := mul_le_mul_of_nonneg_left ih.2 hε
      linarith
    push_cast
    constructor
    · nlinarith [ih.1]
    · linarith [ih.2]
open Classical in
theorem coarseStateMass_eq_caseMass (G : GasGround R n) :
    coarseStateMass R G.cut G.coarse G.state = G.caseMass ∅ constOneCase := by
  unfold coarseStateMass GasGround.caseMass
  refine Finset.sum_congr rfl fun bad _ => Finset.sum_congr rfl fun Yt _ => ?_
  rw [if_pos ⟨fun _ _ _ => Finset.notMem_empty _, fun _ _ _ => Finset.notMem_empty _⟩]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold GasGround.caseIntegral GasGround.caseIntegrand constOneCase
  simp only [one_mul]
theorem stepWeight_nonneg (hR : R.IsWellPosed) (hS : StepTransitionDensityBounds) (hn : R.params.n₀ ≤ n)
    {C : Finset (TorusSite n)} {V : TorusField n} {W : TorusField (n * R.params.side)}
    {Yt : Finset (TorusSite (n * R.params.side))} (ω : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hh : IsHullState R.params R.range W Yt) :
    0 ≤ stepWeight R C V W Yt ω bad b := by apply _root_.YangMills.SharedProofs.p51114 <;> assumption
def pairWeightValue (C : Finset (TorusSite n)) (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (w : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : ℝ :=
  (configurationWeight R C V bad Yt b w.1 w.2).toReal
def caseWeightValue (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω)) : ℝ :=
  pairWeightValue C V bad Yt b (q.fieldWithStoredLinks p.1, q.fillLabels Yt p.2)
theorem measurable_caseWeightValue (hR : R.IsWellPosed) (hWB : ConfigurationWeightMeasurable) (hn : R.params.n₀ ≤ n)
    (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Measurable (caseWeightValue C V q bad Yt b) := by
  have h1 : Measurable (pairWeightValue C V bad Yt b) := (hWB R hR n hn C V bad Yt b).ennreal_toReal
  have a : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      q.fieldWithStoredLinks p.1 :=
    (measurable_fieldWithStoredLinks q).comp measurable_fst
  have c : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      q.fillLabels Yt p.2 :=
    (measurable_fillLabels q Yt).comp measurable_snd
  exact h1.comp (a.prodMk c)
open Classical in
theorem caseIntegrand_eq (G : GasGround R n) {bad : Finset (TorusBond (n * R.params.side))}
    {Yt : Finset (TorusSite (n * R.params.side))} {b : BaseChoice R.params.side n}
    (W : TorusField (n * R.params.side)) (ν : G.state.unlabelled Yt → R.labels.Ω)
    (hq : coarseStateOf R G.cut (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b = G.state) :
    G.caseIntegrand constOneCase bad Yt b W ν =
      ENNReal.ofReal (caseWeightValue G.cut G.coarse G.state bad Yt b (W, ν)) := by
  unfold GasGround.caseIntegrand caseWeightValue pairWeightValue configurationWeight
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
theorem caseTerm_eq_mul (hR : R.IsWellPosed) (hS : StepTransitionDensityBounds) (hn : R.params.n₀ ≤ n)
    (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n)
    (f : Finset (TorusBond (n * R.params.side)) → Finset (TorusSite (n * R.params.side)) → ℝ)
    {bad : Finset (TorusBond (n * R.params.side))} {Yt : Finset (TorusSite (n * R.params.side))}
    {b : BaseChoice R.params.side n} (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω)
    (hq : coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) :
    caseTerm R C V q (fun _ Yt _ bad _ => f bad Yt) bad Yt b W ν = f bad Yt * caseWeightValue C V q bad Yt b (W, ν) := by
  unfold WeightedResponses.caseTerm caseWeightValue pairWeightValue configurationWeight
  by_cases hh : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt
  · rw [if_pos (And.intro hh hq)]
    dsimp only
    rw [if_pos hh, ENNReal.toReal_ofReal (stepWeight_nonneg hR hS hn _ bad b hh)]
  · rw [if_neg fun x => hh x.1]
    dsimp only
    rw [if_neg hh]
    simp
open Classical in
theorem caseTerm_eq_zero (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) (F : CaseFunction R n)
    {bad : Finset (TorusBond (n * R.params.side))} {Yt : Finset (TorusSite (n * R.params.side))}
    {b : BaseChoice R.params.side n} (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω)
    (hq : coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b ≠ q) :
    caseTerm R C V q F bad Yt b W ν = 0 := by
  unfold WeightedResponses.caseTerm
  rw [if_neg fun x => hq x.2]
open Classical in
theorem caseIntegrand_eq_zero (G : GasGround R n) (F : CaseFunctional R n)
    {bad : Finset (TorusBond (n * R.params.side))} {Yt : Finset (TorusSite (n * R.params.side))}
    {b : BaseChoice R.params.side n} (W : TorusField (n * R.params.side)) (ν : G.state.unlabelled Yt → R.labels.Ω)
    (hq : coarseStateOf R G.cut (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b ≠ G.state) :
    G.caseIntegrand F bad Yt b W ν = 0 := by
  unfold GasGround.caseIntegrand
  rw [if_neg fun x => hq x.2]
theorem integral_caseTerm_eq (hR : R.IsWellPosed) (hS : StepTransitionDensityBounds)
    (hWB : ConfigurationWeightMeasurable) (hn : R.params.n₀ ≤ n) (G : GasGround R n)
    (f : Finset (TorusBond (n * R.params.side)) → Finset (TorusSite (n * R.params.side)) → ℝ)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (hfin : G.caseIntegral constOneCase bad Yt b ≠ ⊤) :
    ∫ W, ∫ ν, caseTerm R G.cut G.coarse G.state (fun _ Yt _ bad _ => f bad Yt) bad Yt b W ν
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      f bad Yt * (G.caseIntegral constOneCase bad Yt b).toReal := by
  by_cases hSt : ∃ (W₀ : TorusField (n * R.params.side)) (ν₀ : G.state.unlabelled Yt → R.labels.Ω),
      coarseStateOf R G.cut (G.state.fieldWithStoredLinks W₀) Yt (G.state.fillLabels Yt ν₀) bad b = G.state
  · obtain ⟨W₀, ν₀, h0⟩ := hSt
    have hq : ∀ (W : TorusField (n * R.params.side)) (ν : G.state.unlabelled Yt → R.labels.Ω),
        coarseStateOf R G.cut (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b = G.state :=
      fun W ν => coarseStateOf_const G.state G.cut Yt bad b h0
    have hvm := measurable_caseWeightValue hR hWB hn G.cut G.coarse G.state bad Yt b
    have hv0 : ∀ p, 0 ≤ caseWeightValue G.cut G.coarse G.state bad Yt b p := fun p => ENNReal.toReal_nonneg
    have hlint : G.caseIntegral constOneCase bad Yt b =
        ∫⁻ p, ENNReal.ofReal (caseWeightValue G.cut G.coarse G.state bad Yt b p)
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : G.state.unlabelled Yt => R.labels.μ)) := by
      rw [lintegral_prod _ hvm.ennreal_ofReal.aemeasurable]
      unfold GasGround.caseIntegral
      exact lintegral_congr fun W => lintegral_congr fun ν => caseIntegrand_eq G W ν (hq W ν)
    have hi : Integrable (caseWeightValue G.cut G.coarse G.state bad Yt b)
        ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : G.state.unlabelled Yt => R.labels.μ)) := by
      refine ⟨hvm.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hv0), ← hlint]
      exact lt_top_iff_ne_top.mpr hfin
    calc ∫ W, ∫ ν, caseTerm R G.cut G.coarse G.state (fun _ Yt _ bad _ => f bad Yt) bad Yt b W ν
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
        = ∫ W, ∫ ν, f bad Yt * caseWeightValue G.cut G.coarse G.state bad Yt b (W, ν)
            ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) :=
          integral_congr_ae (Filter.Eventually.of_forall fun W => integral_congr_ae
            (Filter.Eventually.of_forall fun ν =>
              caseTerm_eq_mul hR hS hn G.cut G.coarse G.state f W ν (hq W ν)))
      _ = ∫ p, f bad Yt * caseWeightValue G.cut G.coarse G.state bad Yt b p
            ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : G.state.unlabelled Yt => R.labels.μ)) :=
          (integral_prod _ (hi.const_mul _)).symm
      _ = f bad Yt * ∫ p, caseWeightValue G.cut G.coarse G.state bad Yt b p
            ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : G.state.unlabelled Yt => R.labels.μ)) :=
          integral_const_mul _ _
      _ = f bad Yt * (G.caseIntegral constOneCase bad Yt b).toReal := by
          rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hv0) hvm.aestronglyMeasurable, hlint]
  · push Not at hSt
    have z2 : G.caseIntegral constOneCase bad Yt b = 0 := by
      unfold GasGround.caseIntegral
      refine Eq.trans (lintegral_congr (g := fun _ => 0) fun W => ?_) (by simp)
      exact Eq.trans (lintegral_congr (g := fun _ => 0) fun ν =>
        caseIntegrand_eq_zero G _ W ν (hSt W ν)) (by simp)
    rw [z2, ENNReal.toReal_zero, mul_zero]
    refine Eq.trans (integral_congr_ae (g := fun _ => 0) (Filter.Eventually.of_forall fun W => ?_)) (by simp)
    exact Eq.trans (integral_congr_ae (g := fun _ => 0) (Filter.Eventually.of_forall fun ν =>
      caseTerm_eq_zero G.cut G.coarse G.state _ W ν (hSt W ν))) (by simp)
open Classical in
theorem caseMean_le (hR : R.IsWellPosed) (hS : StepTransitionDensityBounds) (hWB : ConfigurationWeightMeasurable)
    (hr : PartitionRatioBounds) (hn : R.params.n₀ ≤ n) (G : GasGround R n) (c : ℝ)
    (hcols : ∀ off : G.GasSpin → Prop,
      ∃ h : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff off) G.weight (G.spinActivity c),
      G.HasSmallColumns off c h)
    (K : ENNReal) (hKt : K ≠ ⊤) (hK0 : K ≠ 0)
    (hmass : ∀ A, G.caseMass A constOneCase = K * G.partitionFunction A)
    (hcold : 0 < G.coldWeight) (A : Finset (TorusSite n))
    (f : Finset (TorusBond (n * R.params.side)) → Finset (TorusSite (n * R.params.side)) → ℝ)
    (h01 : ∀ bad Yt, f bad Yt = 0 ∨ f bad Yt = 1)
    (hoff : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side))
      (ν : G.state.unlabelled Yt → R.labels.Ω),
      coarseStateOf R G.cut (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b = G.state →
        f bad Yt = 1 → ¬ G.CaseAvoids A bad Yt) :
    caseMean R G.cut G.coarse G.state (fun _ Yt _ bad _ => f bad Yt) ≤
      (A.card : ℝ) * Real.exp (-(7 * c * R.coupling)) := by
  obtain ⟨-, hpos, -, -, hbd⟩ := hr R n G c hcols
  set ε := Real.exp (-(7 * c * R.coupling)) with hε
  have hε0 : 0 ≤ ε := (Real.exp_pos _).le
  have hrat := xi_ratio_bounds G hε0 hpos (fun A Y => hbd A Y) A
  have hxi : ∀ A', G.xi A' = (G.partitionFunction A').toReal / G.coldWeight := fun _ => rfl
  have hP : ∀ A', 0 < (G.partitionFunction A').toReal := fun A' => by
    have h := hpos A'
    rw [hxi] at h
    exact (div_pos_iff_of_pos_right hcold).mp h
  have hPfin : ∀ A', G.partitionFunction A' ≠ ⊤ := fun A' e => by
    have h := hP A'
    rw [e] at h
    simp at h
  have hKr : 0 < K.toReal := ENNReal.toReal_pos hK0 hKt
  have hTot : G.caseMass ∅ constOneCase ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.mul_ne_top hKt (hPfin ∅)
  have hAvoidE : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))),
      G.CaseAvoids ∅ bad Yt :=
    fun _ _ => ⟨fun _ _ _ => Finset.notMem_empty _, fun _ _ _ => Finset.notMem_empty _⟩
  have hTm : ∀ bad ∈ (markedBonds R G.cut).powerset, ∀ Yt : Finset (TorusSite (n * R.params.side)),
      ∑ b : BaseChoice R.params.side n, G.caseIntegral constOneCase bad Yt b ≠ ⊤ := by
    intro bad hb Yt
    unfold GasGround.caseMass at hTot
    have h1 := (ENNReal.sum_ne_top.1 hTot) bad hb
    have h2 := (ENNReal.sum_ne_top.1 h1) Yt (Finset.mem_univ _)
    rwa [if_pos (hAvoidE bad Yt)] at h2
  have hTb : ∀ bad ∈ (markedBonds R G.cut).powerset, ∀ (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n), G.caseIntegral constOneCase bad Yt b ≠ ⊤ := fun bad hb Yt b =>
    (ENNReal.sum_ne_top.1 (hTm bad hb Yt)) b (Finset.mem_univ _)
  set t : Finset (TorusBond (n * R.params.side)) → Finset (TorusSite (n * R.params.side)) → ℝ :=
    fun bad Yt => (∑ b : BaseChoice R.params.side n, G.caseIntegral constOneCase bad Yt b).toReal with ht
  have ht0 : ∀ bad Yt, 0 ≤ t bad Yt := fun _ _ => ENNReal.toReal_nonneg
  have hI : caseIntegral R G.cut G.coarse G.state (fun _ Yt _ bad _ => f bad Yt) =
      ∑ bad ∈ (markedBonds R G.cut).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)), f bad Yt * t bad Yt := by
    unfold caseIntegral
    refine Finset.sum_congr rfl fun bad hb => Finset.sum_congr rfl fun Yt _ => ?_
    rw [ht]
    simp only
    rw [ENNReal.toReal_sum fun b _ => hTb bad hb Yt b, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => integral_caseTerm_eq hR hS hWB hn G f bad Yt b (hTb bad hb Yt b)
  have hSum : ∀ A', (G.caseMass A' constOneCase).toReal =
      ∑ bad ∈ (markedBonds R G.cut).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
        if G.CaseAvoids A' bad Yt then t bad Yt else 0 := by
    intro A'
    have hfin : ∀ bad ∈ (markedBonds R G.cut).powerset, ∀ Yt : Finset (TorusSite (n * R.params.side)),
        (if G.CaseAvoids A' bad Yt then ∑ b : BaseChoice R.params.side n, G.caseIntegral constOneCase bad Yt b
          else 0) ≠ ⊤ := by
      intro bad hb Yt
      split_ifs
      · exact hTm bad hb Yt
      · exact ENNReal.zero_ne_top
    unfold GasGround.caseMass
    rw [ENNReal.toReal_sum fun bad hb => ENNReal.sum_ne_top.2 fun Yt _ => hfin bad hb Yt]
    refine Finset.sum_congr rfl fun bad hb => ?_
    rw [ENNReal.toReal_sum fun Yt _ => hfin bad hb Yt]
    refine Finset.sum_congr rfl fun Yt _ => ?_
    split_ifs
    · rfl
    · rfl
  set S := (G.caseMass ∅ constOneCase).toReal with hSdef
  set Off := (G.caseMass A constOneCase).toReal with hOffdef
  have hSpos : 0 < S := by
    rw [hSdef, hmass, ENNReal.toReal_mul]
    exact mul_pos hKr (hP ∅)
  have himg : coarseStateWeight R G.cut G.coarse G.state = S := by
    unfold coarseStateWeight
    rw [coarseStateMass_eq_caseMass]
  have hle : caseIntegral R G.cut G.coarse G.state (fun _ Yt _ bad _ => f bad Yt) ≤ S - Off := by
    have e1 : S = ∑ bad ∈ (markedBonds R G.cut).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
        t bad Yt := by
      rw [hSdef, hSum ∅]
      refine Finset.sum_congr rfl fun bad _ => Finset.sum_congr rfl fun Yt _ => ?_
      rw [if_pos (hAvoidE bad Yt)]
    rw [hI, e1, hOffdef, hSum A, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun bad hb => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun Yt _ => ?_
    by_cases hO : G.CaseAvoids A bad Yt
    · rw [if_pos hO, sub_self]
      rcases h01 bad Yt with h | h
      · rw [h, zero_mul]
      · have hz : t bad Yt = 0 := by
          have : ∑ b : BaseChoice R.params.side n, G.caseIntegral constOneCase bad Yt b = 0 := by
            refine Finset.sum_eq_zero fun b _ => ?_
            unfold GasGround.caseIntegral
            refine Eq.trans (lintegral_congr (g := fun _ => 0) fun W => ?_) (by simp)
            refine Eq.trans (lintegral_congr (g := fun _ => 0) fun ν => ?_) (by simp)
            unfold GasGround.caseIntegrand
            rw [if_neg fun x => hoff bad Yt b W ν x.2 h hO]
          rw [ht]
          simp only [this, ENNReal.toReal_zero]
        rw [hz, mul_zero]
    · rw [if_neg hO, sub_zero]
      rcases h01 bad Yt with h | h
      · rw [h, zero_mul]
        exact ht0 _ _
      · rw [h, one_mul]
  have hOffS : Off / S = G.xi A / G.xi ∅ := by
    rw [hOffdef, hSdef, hmass, hmass, ENNReal.toReal_mul, ENNReal.toReal_mul, hxi, hxi]
    have e1 := hKr.ne'
    have e2 := (hP ∅).ne'
    have e3 := hcold.ne'
    field_simp
  unfold caseMean
  rw [himg]
  calc caseIntegral R G.cut G.coarse G.state (fun _ Yt _ bad _ => f bad Yt) / S ≤ (S - Off) / S :=
        div_le_div_of_nonneg_right hle hSpos.le
    _ = 1 - Off / S := by
        rw [sub_div, div_self hSpos.ne']
    _ ≤ (A.card : ℝ) * ε := by
        rw [hOffS]
        linarith [hrat.1]
open Classical in
theorem not_caseAvoids (hL : R.params.side ≤ 6 * R.range) (G : GasGround R n) {Z : Finset (TorusSite n)}
    {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω}
    {bad : Finset (TorusBond (n * R.params.side))} {b : BaseChoice R.params.side n}
    (hG : coarseStateOf R G.cut W Yt ωt bad b = G.state) (hmiss : ¬ FreeCoresAvoid R Yt bad G.cut Z) :
    ¬ G.CaseAvoids (blocksNearFreeCores R.params.side R.range Z) bad Yt := by
  intro hoff
  unfold FreeCoresAvoid at hmiss
  push Not at hmiss
  obtain ⟨X, hX, hfree, hdis⟩ := hmiss
  obtain ⟨y, hyc, hyZ⟩ := Finset.not_disjoint_iff.mp hdis
  obtain ⟨v, hv⟩ := (Finset.mem_filter.mp hyc).2
  obtain ⟨hv1, hv2⟩ := Finset.mem_inter.mp hv
  obtain ⟨z, hz, hvz⟩ := (mem_thickening _ _ _).mp hv2
  have hvb : parentBlock R.params.side v = y := Finset.mem_singleton.mp (ClusterExpansionOfAStep.mem_sitesInBlocks.mp hv1)
  have hzA : parentBlock R.params.side z ∈ blocksNearFreeCores R.params.side R.range Z :=
    Finset.mem_image.mpr ⟨z, (mem_thickening _ _ _).mpr ⟨v, ClusterExpansionOfAStep.mem_sitesInBlocks.mpr (hvb ▸ hyZ), by
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
      exact hvz⟩, rfl⟩
  have hzS : z ∈ clusterSites (L := R.params.side) bad Yt G.cut := subset_of_mem_chainComponents hX hz
  have hzN : z ∉ attachedSites R.params.side R.range bad Yt G.cut := by
    intro h
    obtain ⟨X', hX', hzX', hne⟩ := (mem_attachedSites_iff (L := R.params.side) R.range bad Yt G.cut).mp h
    have e : X = X' := eq_of_chainConnected_of_mem_chainComponents hX hX' hz hzX' Relation.ReflTransGen.refl
    exact (e ▸ hne).ne_empty hfree
  have hzB : parentBlock R.params.side z ∉ storedBlocks R.params.side R.range bad Yt G.cut :=
    fun h => hzN (mem_attachedSites_of_parentBlock_mem (L := R.params.side) R.range bad Yt G.cut hL hzS h)
  have hstore : G.state.markAt (parentBlock R.params.side z) = none := by
    rw [← hG, markAt_coarseStateOf, if_neg hzB]
  rcases Finset.mem_union.mp hzS with h | h
  · rcases Finset.mem_union.mp h with h | h
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h
      refine hoff.1 c hc ?_ hzA
      intro hcs
      obtain ⟨s, hs, -⟩ := (Finset.mem_filter.mp hcs).2
      rw [hstore] at hs
      cases hs
    · refine hoff.2 z h ?_ hzA
      intro hzs
      have h2 := (Finset.mem_filter.mp hzs).2
      simp [CoarseState.labelAt, hstore] at h2
  · exact Finset.eq_empty_iff_forall_notMem.mp hfree z (Finset.mem_inter.mpr ⟨hz, h⟩)
end Gas
section Borel
open Classical in
theorem measurableSet_hotCoreSites (R : StepSetup) {n : ℕ} [NeZero n] (C : Finset (TorusSite n)) :
    MeasurableSet {V : TorusField n | hotCoreSites R V = C} := by apply _root_.YangMills.SharedProofs.p5873 <;> assumption
end Borel
end FreeCoresRare
open FreeCoresRare in
open Classical in
theorem FreeCoresRare.freeCoresRareStatement_holds (hM : conditionalMeanIsCaseMeanStatement)
    (hCol₀ : GasColumnsSmall) (hRat : PartitionRatioBounds) (hImg₀ : coarseStateGasStatement)
    (hSum₀ : CaseMassEqGasMass) (hGr₀ : HullStateIsHotCase)
    (hZ : CoarseWeightZeroOfFactorZero) (hHull : CoarseHullIsHullState)
    (hWB : ConfigurationWeightMeasurable) (hSD : StepTransitionDensityBounds)
    (hSt : StageStatesMeasurableStatement) (hD : forgetLastStepStatement) :
    freeCoresRareStatement := by
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
    refine measurable_of_measurableSet_fibres
      (D := Finset (TorusSite (n * (Tb.stepParameters y).side)) × Finset (TorusBond (n * (Tb.stepParameters y).side)) ×
        Finset (TorusSite n))
      (fun u : MarkedSample (Tb.stepParameters y) (s + 1) n =>
        ((stageState T s (n * (Tb.stepParameters y).side) u.1).2.1,
          (u.2.2.2 : Finset (TorusBond (n * (Tb.stepParameters y).side))), hotCoreSites R u.2.2.1)) ?_
      (fun d _ => if FreeCoresAvoid R d.1 d.2.1 d.2.2 Z then (0 : ℝ) else 1) (fun d => measurable_const)
    rintro ⟨a, b, c⟩
    have s1 : MeasurableSet {u : MarkedSample (Tb.stepParameters y) (s + 1) n |
        (stageState T s (n * (Tb.stepParameters y).side) u.1).2.1 = a} :=
      hStm (measurable_snd (measurableSet_sigma_fst_eq a))
    have s2 : MeasurableSet {u : MarkedSample (Tb.stepParameters y) (s + 1) n |
        (u.2.2.2 : Finset (TorusBond (n * (Tb.stepParameters y).side))) = b} :=
      hBm (MeasurableSpace.measurableSet_top (s := {b}))
    have s3 : MeasurableSet {u : MarkedSample (Tb.stepParameters y) (s + 1) n | hotCoreSites R u.2.2.1 = c} :=
      hVm (measurableSet_hotCoreSites R c)
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
    have hmass : ∀ A', (hotCaseGround R V q).caseMass A' constOneCase =
        K * (hotCaseGround R V q).partitionFunction A' := fun A' => by
      rw [hy3 y e3 R hon hx n (hotCaseGround R V q) hG A' constOneCase isCaseFunctional_constOne
        (measurable_gasIntegrand_constOne (hotCaseGround R V q) hw), gasMass_constOne (hotCaseGround R V q) hw]
    exact caseMean_le hF hSD hWB hRat hn₀ (hotCaseGround R V q) Tb.gasRate cols K hKt hK0 hmass hcold
      (blocksNearFreeCores R.params.side R.range Z)
      (fun bad Yt => if FreeCoresAvoid R Yt bad (hotCoreSites R V) Z then 0 else 1)
      (fun bad Yt => by
        split_ifs
        · exact Or.inl rfl
        · exact Or.inr rfl)
      (fun bad Yt b W ν hst hf1 => not_caseAvoids hL6 (hotCaseGround R V q) hst fun hm =>
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
  calc (markedSampleLaw T β (s + 1) n).real {u | ¬ StepAvoids T s m o u}
      = ∫ u, g u ∂(markedSampleLaw T β (s + 1) n) := by
        rw [hgE, integral_indicator_const _ hE]
        simp
    _ = ∫ u, ((markedSampleLaw T β (s + 1) n)[g | stageSigma T (s + 1) n]) u ∂(markedSampleLaw T β (s + 1) n) :=
        (integral_condExp hmle).symm
    _ ≤ ∫ _, bd ∂(markedSampleLaw T β (s + 1) n) :=
        integral_mono_ae integrable_condExp (integrable_const _) hpt
    _ = bd := by simp
end YangMills.Construction.ResponseInTheExpansion
end

import YangMills.Construction.ResponseInTheExpansion.BoundedFunctionsOfTheCasesAreIntegrable
import YangMills.Construction.ResponseInTheExpansion.MeanOverAStepOfTheStatesProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepSettings StepGas StepCosts BlockPlaces ColdStepAtMirrorFrames ClusterExpansionOfAStep
namespace BoundedCaseIntegrability
section Marks
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem markProduct_nonneg (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (bad : Finset (TorusBond (n * R.params.side))) :
    0 ≤ markProduct R C V W bad := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.markProduct_nonneg <;> assumption
private theorem stepWeight_eq_mul (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    stepWeight R C V W Yt ωt bad b =
      R.labelWeight (n * R.params.side) W Yt ωt * stepTransitionDensity R.params R.coupling W b V *
        markProduct R C V W bad := by apply _root_.YangMills.SharedProofs.p15525 <;> assumption
end Marks
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
section Cases
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem stepWeight_nonneg (hR : R.IsWellPosed) (hS : StepTransitionDensityBounds) (hn : R.params.n₀ ≤ n)
    {C : Finset (TorusSite n)} {V : TorusField n} {W : TorusField (n * R.params.side)}
    {Yt : Finset (TorusSite (n * R.params.side))} (ω : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hh : IsHullState R.params R.range W Yt) :
    0 ≤ stepWeight R C V W Yt ω bad b := by
  obtain ⟨Cd, hC⟩ := (hS R.params R.coupling n).2
  have hb : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  rw [stepWeight_eq_mul]
  exact mul_nonneg (mul_nonneg (hR.hasExpansions.2.nonneg _ hb W Yt ω hh) (hC W b V).1)
    (markProduct_nonneg hR C V W bad)
abbrev _root_.YangMills.SharedProofs.p51114 := @stepWeight_nonneg
def caseWeightValue (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n)
    (p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω)) : ℝ :=
  (configurationWeight R C V bad Yt b (q.fieldWithStoredLinks p.1) (q.fillLabels Yt p.2)).toReal
private theorem measurable_caseWeightValue (hR : R.IsWellPosed) (hWB : ConfigurationWeightMeasurable)
    (hn : R.params.n₀ ≤ n) (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) : Measurable (caseWeightValue C V q bad Yt b) := by
  have h1 : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      (configurationWeight R C V bad Yt b p.1 p.2).toReal :=
    (hWB R hR n hn C V bad Yt b).ennreal_toReal
  have h2 : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      ((q.fieldWithStoredLinks p.1, q.fillLabels Yt p.2) : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) :=
    ((measurable_fieldWithStoredLinks q).comp measurable_fst).prodMk
      ((measurable_fillLabels q Yt).comp measurable_snd)
  have h3 := h1.comp h2
  have e : caseWeightValue C V q bad Yt b =
      (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => (configurationWeight R C V bad Yt b p.1 p.2).toReal) ∘
      (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
        ((q.fieldWithStoredLinks p.1, q.fillLabels Yt p.2) : TorusField (n * R.params.side) × (Yt → R.labels.Ω))) := by
    funext p
    simp only [caseWeightValue, Function.comp]
  rw [e]
  exact h3
end Cases
end BoundedCaseIntegrability
open BoundedCaseIntegrability in
theorem boundedCaseFunctionIntegrable (hS : StepTransitionDensityBounds) (hWB : ConfigurationWeightMeasurable) :
    boundedCaseFunctionIntegrableStatement := by
  classical
  intro R hR n _ hn C V q hfin F K hFm hK bad hbad Yt b
  by_cases hSt : ∃ (W₀ : TorusField (n * R.params.side)) (ν₀ : q.unlabelled Yt → R.labels.Ω),
      coarseStateOf R C (q.fieldWithStoredLinks W₀) Yt (q.fillLabels Yt ν₀) bad b = q
  · obtain ⟨W₀, ν₀, h0⟩ := hSt
    have hq : ∀ (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω),
        coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q :=
      fun W ν => coarseStateOf_const q C Yt bad b h0
    have hvm := measurable_caseWeightValue hR hWB hn C V q bad Yt b
    have hv0 : ∀ p, 0 ≤ caseWeightValue C V q bad Yt b p := fun p => ENNReal.toReal_nonneg
    have hterm : ∫⁻ p, ENNReal.ofReal (caseWeightValue C V q bad Yt b p)
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : q.unlabelled Yt => R.labels.μ)) ≤
        coarseStateMass R C V q := by
      rw [lintegral_prod _ hvm.ennreal_ofReal.aemeasurable]
      refine le_trans (le_of_eq ?_) (le_trans (Finset.single_le_sum (f := fun b' => ∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
        (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
            coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b' = q then
          ENNReal.ofReal (stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b') else 0)
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))) (fun _ _ => zero_le) (Finset.mem_univ b))
        (le_trans (Finset.single_le_sum (f := fun Y' => ∑ b' : BaseChoice R.params.side n,
          ∫⁻ W, ∫⁻ ν : q.unlabelled Y' → R.labels.Ω,
        (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Y' ∧
            coarseStateOf R C (q.fieldWithStoredLinks W) Y' (q.fillLabels Y' ν) bad b' = q then
          ENNReal.ofReal (stepWeight R C V (q.fieldWithStoredLinks W) Y' (q.fillLabels Y' ν) bad b') else 0)
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))) (fun _ _ => zero_le) (Finset.mem_univ Yt))
        (Finset.single_le_sum (f := fun bad' => ∑ Y' : Finset (TorusSite (n * R.params.side)),
          ∑ b' : BaseChoice R.params.side n,
          ∫⁻ W, ∫⁻ ν : q.unlabelled Y' → R.labels.Ω,
        (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Y' ∧
            coarseStateOf R C (q.fieldWithStoredLinks W) Y' (q.fillLabels Y' ν) bad' b' = q then
          ENNReal.ofReal (stepWeight R C V (q.fieldWithStoredLinks W) Y' (q.fillLabels Y' ν) bad' b') else 0)
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))) (fun _ _ => zero_le) hbad)))
      refine lintegral_congr fun W => lintegral_congr fun ν => ?_
      unfold caseWeightValue configurationWeight
      by_cases hh : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt
      · rw [if_pos hh, if_pos (And.intro hh (hq W ν)), ENNReal.ofReal_toReal ENNReal.ofReal_ne_top]
      · rw [if_neg hh, if_neg fun x => hh x.1]
        simp
    have hi : Integrable (caseWeightValue C V q bad Yt b)
        ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : q.unlabelled Yt => R.labels.μ)) := by
      refine ⟨hvm.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hv0)]
      exact lt_of_le_of_lt hterm (lt_top_iff_ne_top.mpr hfin)
    have e : (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
        caseTerm R C V q F bad Yt b p.1 p.2) =
        fun p => F (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b * caseWeightValue C V q bad Yt b p := by
      funext p
      unfold caseTerm caseWeightValue configurationWeight
      by_cases hh : IsHullState R.params R.range (q.fieldWithStoredLinks p.1) Yt
      · rw [if_pos (And.intro hh (hq p.1 p.2)), if_pos hh,
          ENNReal.toReal_ofReal (stepWeight_nonneg hR hS hn _ bad b hh)]
      · rw [if_neg fun x => hh x.1, if_neg hh]
        simp
    rw [e]
    have hFm' : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
        F (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b :=
      (hFm Yt bad b).comp (((measurable_fieldWithStoredLinks q).comp measurable_fst).prodMk
        ((measurable_fillLabels q Yt).comp measurable_snd))
    exact hi.bdd_mul hFm'.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact hK _ _ _ _ _)
  · push Not at hSt
    have e : (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
        caseTerm R C V q F bad Yt b p.1 p.2) = fun _ => 0 := by
      funext p
      unfold caseTerm
      rw [if_neg fun x => hSt _ _ x.2]
    rw [e]
    exact integrable_zero _ _ _
end YangMills.Construction.WeightedResponses
end

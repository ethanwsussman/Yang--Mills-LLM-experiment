import YangMills.Construction.ResponseInTheExpansion.LawOfTheDrawsBelowProof
import YangMills.Construction.ResponseInTheExpansion.AStepOfTheStateIsBorel
import YangMills.Construction.ResponseInTheExpansion.TwoPointFunctionByTotalCovarianceProofForm
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.ResponseInTheExpansion.ResponseConditionalExpectation
open WeightedResponses StepSettings TorusFields TorusLumps StepCosts BlockAverages ColdStepAtMirrorFrames
section Abstract
variable {A D : Type} [MeasurableSpace A] [MeasurableSpace D] {μ : Measure A} {ρ : Measure D}
  [SFinite ρ] [IsProbabilityMeasure μ] {w : A × D → ℝ}
omit [IsProbabilityMeasure μ] in
private theorem withDensity_fst_preserving (hw : Measurable w) (h1 : ∀ a, ∫⁻ d, ENNReal.ofReal (w (a, d)) ∂ρ = 1) :
    MeasurePreserving (Prod.fst : A × D → A) ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)) μ := by apply _root_.YangMills.Construction.WeightedResponses.TwoPointCovariance.measurePreserving_fst_withDensity_prod <;> assumption
private theorem integral_withDensity_prod (hw : Measurable w) (h0 : ∀ u, 0 ≤ w u) {g : A × D → ℝ}
    (hg : Integrable g ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u))) :
    ∫ u, g u ∂((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)) =
      ∫ a, ∫ d, w (a, d) * g (a, d) ∂ρ ∂μ := by apply _root_.YangMills.SharedProofs.p3265 <;> assumption
private theorem integrable_mul_of_bounded {ν : Measure A} {φ g : A → ℝ} (hφ : Integrable φ ν) (hg : Measurable g)
    {C : ℝ} (hC : ∀ a, |g a| ≤ C) : Integrable (fun a => φ a * g a) ν := by
  refine (hφ.norm.mul_const C).mono' (hφ.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun a => ?_)
  rw [norm_mul, Real.norm_eq_abs (g a)]
  exact mul_le_mul_of_nonneg_left (hC a) (norm_nonneg _)
end Abstract
section Marks
variable (R : StepSetup) {n : ℕ} [NeZero n]
private theorem markLaw_le_one (hc : IsCutoff R.ballRadius R.barrierFn) (W : TorusField (n * R.params.side))
    (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side))) : markLaw R W V bad ≤ 1 := by apply _root_.YangMills.SharedProofs.p42074 <;> assumption
end Marks
section Outcomes
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters}
private instance bondSet_fintype (m : ℕ) [NeZero m] : Fintype (BondSet m) :=
  inferInstanceAs (Fintype (Finset (TorusBond m)))
private theorem measurable_of_outcome {X : Type} [MeasurableSpace X] {n : ℕ} [NeZero n]
    {f : X × StepOutcome ℓ n → ℝ}
    (h : ∀ (b : BaseChoice ℓ.side n) (bad : BondSet (n * ℓ.side)),
      Measurable fun p : X × TorusField n => f (p.1, (b, p.2, bad))) : Measurable f := by apply _root_.YangMills.SharedProofs.p21057 <;> assumption
private instance stepReferenceMeasure_finite (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (n : ℕ) [NeZero n] :
    IsFiniteMeasure (stepReferenceMeasure ℓ n) := by
  unfold stepReferenceMeasure
  infer_instance
private theorem stepSourceTerm_eq_sum_bonds (x al : ℝ) (s : ℕ) {n : ℕ} [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) (W : TorusField (n * ℓ.side)) (d : StepOutcome ℓ n) :
    stepSourceTerm ℓ x al s h W d =
      ∑ c : TorusBond n, ℓ.coupling * al * bondBlockMean ℓ.side (s + 1) n h c * bondScore ℓ x W d.2.1 d.1 c := by apply _root_.YangMills.SharedProofs.p51313 <;> assumption
end Outcomes
section OneStep
variable (R : StepSetup) {n : ℕ} [NeZero n]
private theorem measurable_stepOutcomeDensity (hS : StepTransitionDensityBounds)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad) :
    Measurable fun p : TorusField (n * R.params.side) × StepOutcome R.params n => stepOutcomeDensity R p.1 p.2 :=
  measurable_of_outcome fun b bad => ((hS R.params R.coupling n).1 b).mul (hB bad)
private theorem stepOutcomeDensity_nonneg (hS : StepTransitionDensityBounds)
    (hc : IsCutoff R.ballRadius R.barrierFn)
    (W : TorusField (n * R.params.side)) (d : StepOutcome R.params n) : 0 ≤ stepOutcomeDensity R W d := by apply _root_.YangMills.SharedProofs.p6753 <;> assumption
private theorem stepOutcomeDensity_le (hc : IsCutoff R.ballRadius R.barrierFn) {C₀ : ℝ}
    (hC₀ : ∀ (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) (V : TorusField n),
      0 ≤ stepTransitionDensity R.params R.coupling W b V ∧ stepTransitionDensity R.params R.coupling W b V ≤ C₀)
    (W : TorusField (n * R.params.side)) (d : StepOutcome R.params n) : stepOutcomeDensity R W d ≤ C₀ := by
  have hs := hC₀ W d.1 d.2.1
  have hk := markLaw_le_one R hc W d.2.1 d.2.2
  calc stepOutcomeDensity R W d ≤ stepTransitionDensity R.params R.coupling W d.1 d.2.1 * 1 :=
        mul_le_mul_of_nonneg_left hk hs.1
    _ ≤ C₀ := by rw [mul_one]; exact hs.2
private theorem lintegral_stepOutcomeDensity (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
    (hf : R.params.Admissible) (hfl : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side)
    (hc : IsCutoff R.ballRadius R.barrierFn)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (W : TorusField (n * R.params.side)) :
    ∫⁻ d, ENNReal.ofReal (stepOutcomeDensity R W d) ∂(stepReferenceMeasure R.params n) = 1 := by apply _root_.YangMills.SharedProofs.p27860 <;> assumption
private theorem measurable_stepSourceTerm (hSc : BondScoreProperties) (hf : R.params.Admissible) (al : ℝ)
    (s : ℕ) (h : PlaquetteWeight (fineSide R.params.side (s + 1) n)) :
    Measurable fun p : TorusField (n * R.params.side) × StepOutcome R.params n =>
      stepSourceTerm R.params R.coupling al s h p.1 p.2 := by
  refine measurable_of_outcome fun b bad => ?_
  have e : (fun p : TorusField (n * R.params.side) × TorusField n =>
      stepSourceTerm R.params R.coupling al s h p.1 (b, p.2, bad)) =
      fun p => ∑ c : TorusBond n, R.params.coupling * al * bondBlockMean R.params.side (s + 1) n h c *
        bondScore R.params R.coupling p.1 p.2 b c := by
    funext p
    exact stepSourceTerm_eq_sum_bonds R.coupling al s h p.1 (b, p.2, bad)
  rw [e]
  exact Finset.measurable_sum _ fun c _ => ((hSc R.params hf R.coupling n b c).2.2.2.2).const_mul _
private theorem abs_stepSourceTerm_le (hSc : BondScoreProperties) (hf : R.params.Admissible) (al : ℝ) (s : ℕ)
    (h : PlaquetteWeight (fineSide R.params.side (s + 1) n)) (W : TorusField (n * R.params.side))
    (d : StepOutcome R.params n) :
    |stepSourceTerm R.params R.coupling al s h W d| ≤
      ∑ c : TorusBond n, |R.params.coupling * al * bondBlockMean R.params.side (s + 1) n h c| * 2 := by
  rw [stepSourceTerm_eq_sum_bonds]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((hSc R.params hf R.coupling n d.1 c).2.2.1 W d.2.1) (abs_nonneg _)
end OneStep
section ChainMarks
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters}
private theorem measurable_topField (s n : ℕ) : Measurable (topField ℓ s n) := by apply _root_.YangMills.SharedProofs.p12845 <;> assumption
private theorem measurable_forgetMarks (s : ℕ) : ∀ n : ℕ, Measurable (forgetMarks ℓ s n) := by apply _root_.YangMills.SharedProofs.p23598 <;> assumption
private theorem finalField_forgetMarks (s n : ℕ) (u : MarkedSample ℓ s n) :
    finalField ℓ s n (forgetMarks ℓ s n u) = topField ℓ s n u := by apply _root_.YangMills.SharedProofs.p8091 <;> assumption
private theorem continuous_curvatureObservable {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    Continuous (curvatureObservable h) := by apply _root_.YangMills.SharedProofs.p1196 <;> assumption
private theorem curvatureObservable_bounded {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    ∃ C : ℝ, ∀ W : TorusField m, |curvatureObservable h W| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (continuous_curvatureObservable h).continuousOn
  exact ⟨C, fun W => by simpa [Real.norm_eq_abs] using hC W (Set.mem_univ _)⟩
private theorem measurable_bondScore_sample (hSc : BondScoreProperties) (hf : ℓ.Admissible) (y : ℝ)
    (s n : ℕ) [NeZero n] (c : TorusBond n) :
    Measurable fun u : ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n =>
      bondScore ℓ y (finalField ℓ s (n * ℓ.side) u.1) u.2.2 u.2.1 c := by apply _root_.YangMills.SharedProofs.p68546 <;> assumption
private theorem chainMark_measurable_bounded (hSc : BondScoreProperties) (hf : ℓ.Admissible) (x al : ℕ → ℝ)
    (s : ℕ) :
    ∀ (n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side s n)),
      Measurable (chainMark ℓ x al s n h) ∧ ∃ C : ℝ, ∀ u, |chainMark ℓ x al s n h u| ≤ C := by
  induction s with
  | zero =>
    intro n _ h
    exact ⟨(continuous_curvatureObservable h).measurable, curvatureObservable_bounded h⟩
  | succ s ih =>
    intro n _ h
    obtain ⟨hm, C, hC⟩ := ih (n * ℓ.side) h
    constructor
    · have h1 : Measurable fun u : ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n =>
          chainMark ℓ x al s (n * ℓ.side) h u.1 +
            ∑ c : TorusBond n, ℓ.coupling * al s * bondBlockMean ℓ.side (s + 1) n h c *
              bondScore ℓ (x s) (finalField ℓ s (n * ℓ.side) u.1) u.2.2 u.2.1 c :=
        (hm.comp measurable_fst).add (Finset.measurable_sum _ fun c _ =>
          (measurable_bondScore_sample hSc hf (x s) s n c).const_mul _)
      exact h1
    · refine ⟨C + ∑ c : TorusBond n, |ℓ.coupling * al s * bondBlockMean ℓ.side (s + 1) n h c| * 2,
        fun u => ?_⟩
      have h2 : |∑ c : TorusBond n, ℓ.coupling * al s * bondBlockMean ℓ.side (s + 1) n h c *
          bondScore ℓ (x s) (finalField ℓ s (n * ℓ.side) u.1) u.2.2 u.2.1 c| ≤
          ∑ c : TorusBond n, |ℓ.coupling * al s * bondBlockMean ℓ.side (s + 1) n h c| * 2 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((hSc ℓ hf (x s) n u.2.1 c).2.2.1 _ _) (abs_nonneg _)
      have h3 := abs_add_le (chainMark ℓ x al s (n * ℓ.side) h u.1) (∑ c : TorusBond n, ℓ.coupling * al s *
        bondBlockMean ℓ.side (s + 1) n h c *
          bondScore ℓ (x s) (finalField ℓ s (n * ℓ.side) u.1) u.2.2 u.2.1 c)
      have h4 := hC u.1
      exact h3.trans (add_le_add h4 h2)
end ChainMarks
section Conditioning
private theorem integral_condExp_mul_measurable {Ω : Type} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ m0) {f g : Ω → ℝ} (hf : Integrable f μ) (hg : StronglyMeasurable[m] g) {C : ℝ}
    (hC : ∀ u, |g u| ≤ C) : ∫ u, (μ[f|m]) u * g u ∂μ = ∫ u, f u * g u ∂μ := by
  have hg' : Measurable g := (hg.mono hm).measurable
  have hfg : Integrable (f * g) μ := @integrable_mul_of_bounded Ω m0 μ f g hf hg' C hC
  have e : μ[f * g|m] =ᵐ[μ] μ[f|m] * g := condExp_mul_of_stronglyMeasurable_right hg hfg hf
  calc ∫ u, (μ[f|m]) u * g u ∂μ = ∫ u, (μ[f * g|m]) u ∂μ :=
        integral_congr_ae (e.symm.mono fun u hu => by simpa using hu)
    _ = ∫ u, (f * g) u ∂μ := integral_condExp hm
    _ = ∫ u, f u * g u ∂μ := rfl
end Conditioning
section TowerProperty
variable {A D Q Q' : Type} [MeasurableSpace A] [MeasurableSpace D] [MeasurableSpace Q] [MeasurableSpace Q']
private theorem condExp_condExp_through_kernel {μ : Measure A} [IsProbabilityMeasure μ] {ρ : Measure D}
    [IsFiniteMeasure ρ]
    {q : A → Q} (hq : Measurable q) {w : Q × D → ℝ} (hw : Measurable w) (h0 : ∀ p, 0 ≤ w p) {C₀ : ℝ}
    (hC₀ : ∀ p, w p ≤ C₀) {w' : A × D → ℝ} (hw' : ∀ u, w' u = w (q u.1, u.2))
    (h1 : ∀ a, ∫⁻ d, ENNReal.ofReal (w' (a, d)) ∂ρ = 1)
    {F : Q × D → Q'} (hF : Measurable F) {r : A × D → Q'} (hr : ∀ u, r u = F (q u.1, u.2))
    {M : A → ℝ} (hM : Integrable M μ) :
    ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w' u))[fun u =>
        (μ[M | MeasurableSpace.comap q inferInstance]) u.1 | MeasurableSpace.comap r inferInstance]
      =ᵐ[(μ.prod ρ).withDensity fun u => ENNReal.ofReal (w' u)]
    ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w' u))[fun u => M u.1 |
      MeasurableSpace.comap r inferInstance] := by
  have hw'm : Measurable w' := by
    have e : w' = fun u => w (q u.1, u.2) := funext hw'
    rw [e]
    exact hw.comp ((hq.comp measurable_fst).prodMk measurable_snd)
  have hw'0 : ∀ u, 0 ≤ w' u := fun u => by rw [hw']; exact h0 _
  have hπ := withDensity_fst_preserving (μ := μ) (ρ := ρ) hw'm h1
  set ν : Measure (A × D) := (μ.prod ρ).withDensity fun u => ENNReal.ofReal (w' u) with hν
  have hprob : IsProbabilityMeasure ν := by
    constructor
    have e := hπ.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
    rw [Set.preimage_univ] at e
    rw [e]
    exact measure_univ
  have hrm : Measurable r := by
    have e : r = fun u => F (q u.1, u.2) := funext hr
    rw [e]
    exact hF.comp ((hq.comp measurable_fst).prodMk measurable_snd)
  have hG' : MeasurableSpace.comap r inferInstance ≤ (inferInstance : MeasurableSpace (A × D)) := hrm.comap_le
  have hG : MeasurableSpace.comap q inferInstance ≤ (inferInstance : MeasurableSpace A) := hq.comap_le
  have hZ : Integrable (μ[M | MeasurableSpace.comap q inferInstance]) μ := integrable_condExp
  have hZc : Integrable (fun u : A × D => (μ[M | MeasurableSpace.comap q inferInstance]) u.1) ν :=
    (hπ.integrable_comp hZ.aestronglyMeasurable).2 hZ
  have hMc : Integrable (fun u : A × D => M u.1) ν := (hπ.integrable_comp hM.aestronglyMeasurable).2 hM
  refine ae_eq_condExp_of_forall_setIntegral_eq hG' hMc (fun B _ _ => integrable_condExp.integrableOn)
    (fun B hB _ => ?_) stronglyMeasurable_condExp.aestronglyMeasurable
  rw [setIntegral_condExp hG' hZc hB]
  obtain ⟨C, hC, rfl⟩ := hB
  have hBm : MeasurableSet (r ⁻¹' C) := hrm hC
  have hind : Measurable fun p : Q × D => C.indicator (1 : Q' → ℝ) (F p) :=
    (measurable_one.indicator hC).comp hF
  have hFull : Measurable fun p : Q × D => w p * C.indicator (1 : Q' → ℝ) (F p) := hw.mul hind
  let ψ : Q → ℝ := fun x => ∫ d, w (x, d) * C.indicator (1 : Q' → ℝ) (F (x, d)) ∂ρ
  have hψm : Measurable ψ := (hFull.stronglyMeasurable.integral_prod_right (ν := ρ)).measurable
  have hψb : ∀ x, |ψ x| ≤ C₀ * ρ.real Set.univ := fun x => by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun d => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h0 _)]
    have hi : |C.indicator (1 : Q' → ℝ) (F (x, d))| ≤ 1 := by
      by_cases hin : F (x, d) ∈ C <;> simp [hin]
    calc w (x, d) * |C.indicator (1 : Q' → ℝ) (F (x, d))| ≤ w (x, d) * 1 :=
          mul_le_mul_of_nonneg_left hi (h0 _)
      _ ≤ C₀ := by rw [mul_one]; exact hC₀ _
  have key : ∀ φ : A → ℝ, Integrable φ μ → ∫ u in r ⁻¹' C, φ u.1 ∂ν = ∫ a, φ a * ψ (q a) ∂μ := by
    intro φ hφ
    have hφc : Integrable (fun u : A × D => φ u.1) ν := (hπ.integrable_comp hφ.aestronglyMeasurable).2 hφ
    rw [← integral_indicator hBm]
    refine (integral_withDensity_prod hw'm hw'0 (hφc.indicator hBm)).trans
      (integral_congr_ae (Filter.Eventually.of_forall fun a => ?_))
    show ∫ d, w' (a, d) * (r ⁻¹' C).indicator (fun u : A × D => φ u.1) (a, d) ∂ρ =
      φ a * ∫ d, w (q a, d) * C.indicator (1 : Q' → ℝ) (F (q a, d)) ∂ρ
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun d => ?_)
    show w' (a, d) * (r ⁻¹' C).indicator (fun u : A × D => φ u.1) (a, d) =
      φ a * (w (q a, d) * C.indicator (1 : Q' → ℝ) (F (q a, d)))
    have hw1 : w' (a, d) = w (q a, d) := hw' (a, d)
    by_cases hin : F (q a, d) ∈ C
    · have hm : (a, d) ∈ r ⁻¹' C := by
        show r (a, d) ∈ C
        rw [hr]
        exact hin
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hin, hw1]
      simp only [Pi.one_apply]
      ring
    · have hm : (a, d) ∉ r ⁻¹' C := by
        show ¬ r (a, d) ∈ C
        rw [hr]
        exact hin
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hin]
      ring
  rw [key _ hZ, key _ hM]
  have hs : StronglyMeasurable[MeasurableSpace.comap q inferInstance] (fun a => ψ (q a)) :=
    (hψm.comp (comap_measurable q)).stronglyMeasurable
  exact integral_condExp_mul_measurable hG hM hs (fun a => hψb (q a))
end TowerProperty
section Tower
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters}
private theorem stage_isCutoff (T : StageTower ℓ) (h : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (t : ℕ) :
    IsCutoff (T.stage t).toStepSetup.ballRadius (T.stage t).toStepSetup.barrierFn := by apply _root_.YangMills.SharedProofs.p16 <;> assumption
private def sampleKernel (T : StageTower ℓ) (s n : ℕ) [NeZero n]
    (u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n) : ℝ :=
  stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2
private def stateKernel (T : StageTower ℓ) (s n : ℕ) [NeZero n]
    (p : StageState T s (n * ℓ.side) × StepOutcome ℓ n) : ℝ :=
  stepOutcomeDensity (T.stage s).toStepSetup p.1.1 p.2
private def stateAbove (T : StageTower ℓ) (s n : ℕ) [NeZero n] (p : StageState T s (n * ℓ.side) × StepOutcome ℓ n) :
    StageState T (s + 1) n :=
  (p.2.2.1, coarseStateOf (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup p.2.2.1) p.1.1 p.1.2.1
    p.1.2.2 p.2.2.2 p.2.1)
private theorem stageState_fst (T : StageTower ℓ) (s n : ℕ) [NeZero n] (u : MarkedSample ℓ s n) :
    (stageState T s n u).1 = topField ℓ s n u := by apply _root_.YangMills.SharedProofs.p2480 <;> assumption
variable (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
  (hSc : BondScoreProperties) (hSt : StageStatesMeasurableStatement)
  (hUp : CoarseStateMeasurable)
  (hf : ℓ.Admissible) (hfl : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side) (T : StageTower ℓ)
  (hcut : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (hcoin : T.MarksMeasurable) (β : ℝ) (al : ℕ → ℝ)
  (hp : ∀ (s n : ℕ) [NeZero n], IsProbabilityMeasure (markedSampleLaw T β s n))
include hS hcoin in
private theorem measurable_sampleKernel (s n : ℕ) [NeZero n] : Measurable (sampleKernel T s n) := by apply _root_.YangMills.DeltaSharedProofs.p500627 <;> assumption
include hS hcoin in
private theorem measurable_stateKernel (s n : ℕ) [NeZero n] : Measurable (stateKernel T s n) := by
  have h1 := measurable_stepOutcomeDensity (T.stage s).toStepSetup (n := n) hS (fun bad => hcoin s n bad)
  have h2 : Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n =>
      ((p.1.1, p.2) : TorusField (n * ℓ.side) × StepOutcome ℓ n) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have h3 := h1.comp h2
  exact h3
include hUp in
private theorem measurable_stateAbove (s n : ℕ) [NeZero n] : Measurable (stateAbove T s n) := by
  have hV : Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n => p.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hW : Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n => p.1.1 :=
    measurable_fst.comp measurable_fst
  have hq : Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n => p.1.2 :=
    measurable_snd.comp measurable_fst
  have hb : ∀ a : Finset (TorusBond (n * ℓ.side)), MeasurableSet
      {p : StageState T s (n * ℓ.side) × StepOutcome ℓ n | (p.2.2.2 : Finset (TorusBond (n * ℓ.side))) = a} := by
    intro a
    have hm : Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n => p.2.2.2 :=
      measurable_snd.comp (measurable_snd.comp measurable_snd)
    have hs : MeasurableSet ({a} : Set (BondSet (n * ℓ.side))) := MeasurableSpace.measurableSet_top
    exact hm hs
  have hc : ∀ a : BaseChoice ℓ.side n, MeasurableSet
      {p : StageState T s (n * ℓ.side) × StepOutcome ℓ n | p.2.1 = a} := by
    intro a
    have hm : Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n => p.2.1 :=
      measurable_fst.comp measurable_snd
    have hs : MeasurableSet ({a} : Set (BaseChoice ℓ.side n)) := MeasurableSpace.measurableSet_top
    exact hm hs
  have h2 := hUp (T.stage s).toStepSetup n (StageState T s (n * ℓ.side) × StepOutcome ℓ n) _ _ _ _ _
    hV hW hq hb hc
  exact hV.prodMk h2
include hS hM hf hfl hcut hcoin in
private theorem lintegral_sampleKernel (s n : ℕ) [NeZero n] (a : MarkedSample ℓ s (n * ℓ.side)) :
    ∫⁻ d, ENNReal.ofReal (sampleKernel T s n (a, d)) ∂(stepReferenceMeasure ℓ n) = 1 := by apply _root_.YangMills.DeltaSharedProofs.p501759 <;> assumption
include hS hM hf hfl hcut hcoin hp in
private theorem fst_measurePreserving (s n : ℕ) [NeZero n] :
    MeasurePreserving (fun u : MarkedSample ℓ (s + 1) n => u.1) (markedSampleLaw T β (s + 1) n)
      (markedSampleLaw T β s (n * ℓ.side)) := by
  have := hp s (n * ℓ.side)
  exact withDensity_fst_preserving (μ := markedSampleLaw T β s (n * ℓ.side)) (ρ := stepReferenceMeasure ℓ n)
    (w := sampleKernel T s n)
    (measurable_sampleKernel hS T hcoin s n) (lintegral_sampleKernel hS hM hf hfl T hcut hcoin s n)
include hSc hf in
private theorem measurable_sourceTerm (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) :
    Measurable (sourceTerm T al s n h) := by
  have h1 := measurable_stepSourceTerm (T.stage s).toStepSetup (n := n) hSc hf (al s) s h
  have h2 : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
      ((topField ℓ s (n * ℓ.side) u.1, u.2) : TorusField (n * ℓ.side) × StepOutcome ℓ n) :=
    ((measurable_topField s (n * ℓ.side)).comp measurable_fst).prodMk measurable_snd
  have h3 := h1.comp h2
  exact h3
include hSc hf in
private theorem abs_sourceTerm_le (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n))
    (u : MarkedSample ℓ (s + 1) n) :
    |sourceTerm T al s n h u| ≤
      ∑ c : TorusBond n, |ℓ.coupling * al s * bondBlockMean ℓ.side (s + 1) n h c| * 2 :=
  abs_stepSourceTerm_le (T.stage s).toStepSetup hSc hf (al s) s h _ _
private theorem response_succ (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) :
    response T β al (s + 1) n h =
      (markedSampleLaw T β (s + 1) n)[stepSum T β al s n h | stageSigma T (s + 1) n] := by
  funext u
  rfl
include hp in
private theorem integrable_response (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side s n)) :
    Integrable (response T β al s n h) (markedSampleLaw T β s n) := by
  have := hp s n
  cases s with
  | zero =>
    obtain ⟨C, hC⟩ := curvatureObservable_bounded (m := n) h
    exact Integrable.of_bound (continuous_curvatureObservable h).measurable.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun W => by rw [Real.norm_eq_abs]; exact hC W)
  | succ s =>
    rw [response_succ]
    exact integrable_condExp
private theorem chainMark_succ (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n))
    (u : MarkedSample ℓ (s + 1) n) :
    chainMark ℓ (fun j => (T.stage j).coupling) al (s + 1) n h (forgetMarks ℓ (s + 1) n u) =
      chainMark ℓ (fun j => (T.stage j).coupling) al s (n * ℓ.side) h (forgetMarks ℓ s (n * ℓ.side) u.1) +
        sourceTerm T al s n h u := by
  show _ + ∑ c : TorusBond n, ℓ.coupling * al s * bondBlockMean ℓ.side (s + 1) n h c *
      bondScore ℓ (T.stage s).coupling (finalField ℓ s (n * ℓ.side) (forgetMarks ℓ s (n * ℓ.side) u.1))
        u.2.2.1 u.2.1 c =
    _ + stepSourceTerm ℓ (T.stage s).coupling (al s) s h (topField ℓ s (n * ℓ.side) u.1) u.2
  rw [stepSourceTerm_eq_sum_bonds, finalField_forgetMarks]
  rfl
include hS hM hSt hUp hf hfl hcut hcoin hp in
private theorem condExp_stageSigma_condExp (s n : ℕ) [NeZero n] {M : MarkedSample ℓ s (n * ℓ.side) → ℝ}
    (hMi : Integrable M (markedSampleLaw T β s (n * ℓ.side))) :
    (markedSampleLaw T β (s + 1) n)[fun u : MarkedSample ℓ (s + 1) n =>
        ((markedSampleLaw T β s (n * ℓ.side))[M | stageSigma T s (n * ℓ.side)]) u.1 | stageSigma T (s + 1) n]
      =ᵐ[markedSampleLaw T β (s + 1) n]
    (markedSampleLaw T β (s + 1) n)[fun u : MarkedSample ℓ (s + 1) n => M u.1 | stageSigma T (s + 1) n] := by
  have := hp s (n * ℓ.side)
  obtain ⟨C₀, hC₀⟩ := (hS ℓ (T.stage s).coupling n).2
  exact condExp_condExp_through_kernel (μ := markedSampleLaw T β s (n * ℓ.side)) (ρ := stepReferenceMeasure ℓ n)
    (q := stageState T s (n * ℓ.side)) (hSt ℓ hf T s (n * ℓ.side)) (w := stateKernel T s n)
    (measurable_stateKernel hS T hcoin s n)
    (fun p => stepOutcomeDensity_nonneg (T.stage s).toStepSetup hS (stage_isCutoff T hcut s) _ _) (C₀ := C₀)
    (fun p => stepOutcomeDensity_le (T.stage s).toStepSetup (stage_isCutoff T hcut s) hC₀ _ _)
    (w' := sampleKernel T s n) (fun u => by
      show stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2 =
        stepOutcomeDensity (T.stage s).toStepSetup (stageState T s (n * ℓ.side) u.1).1 u.2
      rw [stageState_fst])
    (lintegral_sampleKernel hS hM hf hfl T hcut hcoin s n) (F := stateAbove T s n)
    (measurable_stateAbove hUp T s n)
    (r := fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => stageState T (s + 1) n u) (fun _ => rfl) hMi
include hS hM hSc hSt hUp hf hfl hcut hcoin hp in
private theorem response_ae_eq_condExp_chainMark (s : ℕ) :
    ∀ (n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side s n)),
      response T β al s n h =ᵐ[markedSampleLaw T β s n]
        (markedSampleLaw T β s n)[fun u => chainMark ℓ (fun j => (T.stage j).coupling) al s n h
          (forgetMarks ℓ s n u) | stageSigma T s n] := by
  induction s with
  | zero =>
    intro n _ h
    have hp0 := hp 0 n
    have hle : stageSigma T 0 n ≤ markedSampleMeasurableSpace ℓ 0 n := (hSt ℓ hf T 0 n).comap_le
    have hm : StronglyMeasurable[stageSigma T 0 n]
        (fun u => chainMark ℓ (fun j => (T.stage j).coupling) al 0 n h (forgetMarks ℓ 0 n u)) := by
      have h1 : Measurable[stageSigma T 0 n] (stageState T 0 n) := comap_measurable _
      have h2 : Measurable fun q : StageState T 0 n => curvatureObservable h q.1 :=
        (continuous_curvatureObservable h).measurable.comp measurable_fst
      have h3 := h2.comp h1
      exact h3.stronglyMeasurable
    have hi : Integrable (fun u => chainMark ℓ (fun j => (T.stage j).coupling) al 0 n h (forgetMarks ℓ 0 n u))
        (markedSampleLaw T β 0 n) := integrable_response T β al hp 0 n h
    rw [condExp_of_stronglyMeasurable hle hm hi]
    rfl
  | succ s ih =>
    intro n _ h
    have hp1 := hp (s + 1) n
    have hp0 := hp s (n * ℓ.side)
    have hπ := fst_measurePreserving hS hM hf hfl T hcut hcoin β hp s n
    have hR := integrable_response T β al hp s (n * ℓ.side) h
    obtain ⟨hmk, Cm, hCm⟩ := chainMark_measurable_bounded hSc hf (fun j => (T.stage j).coupling) al s
      (n * ℓ.side) h
    have hMk : Integrable (fun a => chainMark ℓ (fun j => (T.stage j).coupling) al s (n * ℓ.side) h
        (forgetMarks ℓ s (n * ℓ.side) a)) (markedSampleLaw T β s (n * ℓ.side)) :=
      Integrable.of_bound (hmk.comp (measurable_forgetMarks s (n * ℓ.side))).aestronglyMeasurable Cm
        (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hCm _)
    have hRc : Integrable (fun u : MarkedSample ℓ (s + 1) n => response T β al s (n * ℓ.side) h u.1)
        (markedSampleLaw T β (s + 1) n) := (hπ.integrable_comp hR.aestronglyMeasurable).2 hR
    have hMc : Integrable (fun u : MarkedSample ℓ (s + 1) n =>
        chainMark ℓ (fun j => (T.stage j).coupling) al s (n * ℓ.side) h
          (forgetMarks ℓ s (n * ℓ.side) u.1)) (markedSampleLaw T β (s + 1) n) :=
      (hπ.integrable_comp hMk.aestronglyMeasurable).2 hMk
    have hSr : Integrable (sourceTerm T al s n h) (markedSampleLaw T β (s + 1) n) :=
      Integrable.of_bound (measurable_sourceTerm hSc hf T al s n h).aestronglyMeasurable _
        (Filter.Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs]; exact abs_sourceTerm_le hSc hf T al s n h u)
    have e1 : (fun u : MarkedSample ℓ (s + 1) n => response T β al s (n * ℓ.side) h u.1)
        =ᵐ[markedSampleLaw T β (s + 1) n]
        fun u => ((markedSampleLaw T β s (n * ℓ.side))[fun a =>
          chainMark ℓ (fun j => (T.stage j).coupling) al s (n * ℓ.side) h
            (forgetMarks ℓ s (n * ℓ.side) a) | stageSigma T s (n * ℓ.side)]) u.1 :=
      hπ.quasiMeasurePreserving.ae (ih (n * ℓ.side) h)
    have e2 := condExp_congr_ae (m := stageSigma T (s + 1) n) e1
    have e3 := condExp_stageSigma_condExp hS hM hSt hUp hf hfl T hcut hcoin β hp s n hMk
    have a1 := condExp_add hRc hSr (stageSigma T (s + 1) n)
    have a2 := condExp_add hMc hSr (stageSigma T (s + 1) n)
    have f1 : stepSum T β al s n h = (fun u : MarkedSample ℓ (s + 1) n =>
        response T β al s (n * ℓ.side) h u.1) + sourceTerm T al s n h := rfl
    have f2 : (fun u : MarkedSample ℓ (s + 1) n => chainMark ℓ (fun j => (T.stage j).coupling) al (s + 1) n h
        (forgetMarks ℓ (s + 1) n u)) = (fun u : MarkedSample ℓ (s + 1) n =>
          chainMark ℓ (fun j => (T.stage j).coupling) al s (n * ℓ.side) h
            (forgetMarks ℓ s (n * ℓ.side) u.1)) +
        sourceTerm T al s n h := funext fun u => chainMark_succ T al s n h u
    rw [response_succ, f1, f2]
    filter_upwards [a1, a2, e2, e3] with u h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, Pi.add_apply, h3, h4]
end Tower
theorem responseIsConditionalExpectation_holds (hTP : TwoPointByTotalCovarianceStatement)
    (hSt : StageStatesMeasurableStatement) (hUp : CoarseStateMeasurable) (hM : ScoreProductStepMean)
    (hS : StepTransitionDensityBounds) (hSc : BondScoreProperties) : ResponseIsConditionalExpectation := by
  intro ℓ hf hfl T hcut hcoin β al s n _ h
  exact response_ae_eq_condExp_chainMark hS hM hSc hSt hUp hf hfl T hcut hcoin β al
    (fun s n _ => (hTP ℓ hf hfl T hcut hcoin β al s n).1) s n h
end YangMills.Construction.ResponseInTheExpansion.ResponseConditionalExpectation
end

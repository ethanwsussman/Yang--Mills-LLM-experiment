import YangMills.Construction.FreeEnergiesOfTheFlow.ThePastIsFreeGivenTheStateProof
import YangMills.Construction.ResponseInTheExpansion.ChainIsMarkovBackwards
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings TorusLumps TorusFields WeightedResponses ColdStepAtMirrorFrames StepCosts
section ProductDensity
variable {A D E : Type} {m mA : MeasurableSpace A} {mD : MeasurableSpace D} {mE : MeasurableSpace E}
  {μ : Measure A} {ρ : Measure D} [SFinite ρ]
private theorem isProbabilityMeasure_withDensity_prod [IsProbabilityMeasure μ] {w : A × D → ℝ} (hw : Measurable w)
    (hmass : ∀ a, ∫⁻ d, ENNReal.ofReal (w (a, d)) ∂ρ = 1) :
    IsProbabilityMeasure ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)) := by apply _root_.YangMills.SharedProofs.p11113 <;> assumption
private theorem measurePreserving_fst_withDensity_prod [IsProbabilityMeasure μ] {w : A × D → ℝ} (hw : Measurable w)
    (hmass : ∀ a, ∫⁻ d, ENNReal.ofReal (w (a, d)) ∂ρ = 1) :
    MeasurePreserving (Prod.fst : A × D → A) ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)) μ := by apply _root_.YangMills.SharedProofs.p1188 <;> assumption
private theorem integral_withDensity_prod_eq {μ₀ : Measure A} [SFinite μ₀] {ρ₀ : Measure D} [SFinite ρ₀]
    {w : A × D → ℝ} (hw : Measurable w) (hnn : ∀ u, 0 ≤ w u) {g : A × D → ℝ}
    (hg : Integrable g ((μ₀.prod ρ₀).withDensity fun u => ENNReal.ofReal (w u))) :
    ∫ u, g u ∂((μ₀.prod ρ₀).withDensity fun u => ENNReal.ofReal (w u)) =
      ∫ a, ∫ d, w (a, d) * g (a, d) ∂ρ₀ ∂μ₀ := by
  have hm : Measurable fun u => (w u).toNNReal := hw.real_toNNReal
  have hν : ((μ₀.prod ρ₀).withDensity fun u => ENNReal.ofReal (w u)) =
      (μ₀.prod ρ₀).withDensity fun u => ((w u).toNNReal : ENNReal) := rfl
  rw [hν] at hg ⊢
  have hint := (integrable_withDensity_iff_integrable_smul hm).1 hg
  rw [integral_withDensity_eq_integral_smul hm g, integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun d => ?_)
  show (w (a, d)).toNNReal • g (a, d) = w (a, d) * g (a, d)
  rw [NNReal.smul_def, Real.coe_toNNReal _ (hnn _), smul_eq_mul]
private theorem setIntegral_prod_withDensity_fst [SFinite μ] {w : A × D → ℝ} (hw : Measurable w)
    (hnn : ∀ u, 0 ≤ w u) {F : A → ℝ}
    (hF : Integrable (fun u : A × D => F u.1) ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)))
    {S : Set A} {B : Set D} (hS : MeasurableSet S) (hB : MeasurableSet B) :
    ∫ u in S ×ˢ B, F u.1 ∂((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)) =
      ∫ a in S, (∫ d in B, w (a, d) ∂ρ) * F a ∂μ := by
  have e : ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)).restrict (S ×ˢ B) =
      ((μ.restrict S).prod (ρ.restrict B)).withDensity fun u => ENNReal.ofReal (w u) := by
    rw [restrict_withDensity (hS.prod hB), Measure.prod_restrict]
  have hI := hF.integrableOn (s := S ×ˢ B)
  rw [IntegrableOn, e] at hI
  rw [e, integral_withDensity_prod_eq hw hnn hI]
  simp only [integral_mul_const]
private theorem condExp_withDensity_prod_fst [IsProbabilityMeasure μ] (hm : m ≤ mA) {w : E × D → ℝ}
    {top : A → E} (hw : Measurable w) (hnn : ∀ p, 0 ≤ w p)
    (hmass : ∀ e, ∫⁻ d, ENNReal.ofReal (w (e, d)) ∂ρ = 1)
    (htop : Measurable[m] top) {g h : A → ℝ} (hg : Integrable g μ) (hh : StronglyMeasurable[m] h)
    (hgh : μ[g|m] =ᵐ[μ] h) :
    ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w (top u.1, u.2)))[fun u => g u.1 |
        m.comap Prod.fst ⊔ mD.comap Prod.snd] =ᵐ[(μ.prod ρ).withDensity fun u =>
        ENNReal.ofReal (w (top u.1, u.2))] fun u => h u.1 := by
  have htop' : Measurable top := htop.mono hm le_rfl
  have hw₁ : Measurable fun u : A × D => w (top u.1, u.2) :=
    hw.comp ((htop'.comp measurable_fst).prodMk measurable_snd)
  have hnn₁ : ∀ u : A × D, 0 ≤ w (top u.1, u.2) := fun u => hnn _
  have hmass₁ : ∀ a, ∫⁻ d, ENNReal.ofReal (w (top a, d)) ∂ρ = 1 := fun a => hmass (top a)
  have := isProbabilityMeasure_withDensity_prod (μ := μ) hw₁ hmass₁
  have hfst := measurePreserving_fst_withDensity_prod (μ := μ) hw₁ hmass₁
  set ν : Measure (A × D) := (μ.prod ρ).withDensity fun u => ENNReal.ofReal (w (top u.1, u.2)) with hν
  have hhi : Integrable h μ := integrable_condExp.congr hgh
  have hgi : Integrable (fun u : A × D => g u.1) ν := hfst.integrable_comp_of_integrable hg
  have hhi' : Integrable (fun u : A × D => h u.1) ν := hfst.integrable_comp_of_integrable hhi
  have hle : m.comap Prod.fst ⊔ mD.comap Prod.snd ≤ (inferInstance : MeasurableSpace (A × D)) :=
    sup_le_sup (MeasurableSpace.comap_mono hm) le_rfl
  have hrect : ∀ (S : Set A) (B : Set D), MeasurableSet[m] S → MeasurableSet B →
      ∫ u in S ×ˢ B, h u.1 ∂ν = ∫ u in S ×ˢ B, g u.1 ∂ν := by
    intro S B hS hB
    rw [setIntegral_prod_withDensity_fst hw₁ hnn₁ hhi' (hm S hS) hB,
      setIntegral_prod_withDensity_fst hw₁ hnn₁ hgi (hm S hS) hB]
    have hψ : StronglyMeasurable fun e : E => ∫ d in B, w (e, d) ∂ρ :=
      hw.stronglyMeasurable.integral_prod_right'
    have hψm : StronglyMeasurable[m] fun a : A => ∫ d in B, w (top a, d) ∂ρ := hψ.comp_measurable htop
    have hbd : ∀ e : E, ‖∫ d in B, w (e, d) ∂ρ‖ ≤ 1 := by
      intro e
      have hpos : 0 ≤ ∫ d in B, w (e, d) ∂ρ := integral_nonneg fun d => hnn _
      rw [Real.norm_eq_abs, abs_of_nonneg hpos,
        integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun d => hnn _)
          (hw.comp measurable_prodMk_left).aestronglyMeasurable]
      have hle1 : ∫⁻ d in B, ENNReal.ofReal (w (e, d)) ∂ρ ≤ 1 :=
        (setLIntegral_le_lintegral _ _).trans (hmass e).le
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle1
    have hint : Integrable ((fun a : A => ∫ d in B, w (top a, d) ∂ρ) * g) μ :=
      hg.bdd_mul (hψm.mono hm).aestronglyMeasurable (Filter.Eventually.of_forall fun a => hbd (top a))
    have hpull := condExp_mul_of_stronglyMeasurable_left hψm hint hg
    calc ∫ a in S, (∫ d in B, w (top a, d) ∂ρ) * h a ∂μ
        = ∫ a in S, ((fun a : A => ∫ d in B, w (top a, d) ∂ρ) * μ[g|m]) a ∂μ := by
          refine integral_congr_ae (ae_restrict_of_ae ?_)
          filter_upwards [hgh] with a ha
          simp only [Pi.mul_apply, ha]
      _ = ∫ a in S, (μ[(fun a : A => ∫ d in B, w (top a, d) ∂ρ) * g|m]) a ∂μ :=
          integral_congr_ae (ae_restrict_of_ae hpull.symm)
      _ = ∫ a in S, ((fun a : A => ∫ d in B, w (top a, d) ∂ρ) * g) a ∂μ := setIntegral_condExp hm hint hS
      _ = ∫ a in S, (∫ d in B, w (top a, d) ∂ρ) * g a ∂μ := rfl
  have hall : ∀ S, MeasurableSet[m.comap Prod.fst ⊔ mD.comap Prod.snd] S →
      ∫ u in S, h u.1 ∂ν = ∫ u in S, g u.1 ∂ν := by
    intro S hS
    induction S, hS using MeasurableSpace.induction_on_inter
        (h_eq := (@generateFrom_prod A D m mD).symm) (h_inter := @isPiSystem_prod A D m mD) with
    | empty => simp
    | basic t ht =>
      obtain ⟨S, hS, B, hB, rfl⟩ := ht
      exact hrect S B hS hB
    | compl t htm ih =>
      have hu := hrect Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
      rw [Set.univ_prod_univ, Measure.restrict_univ] at hu
      rw [setIntegral_compl (hle _ htm) hhi', setIntegral_compl (hle _ htm) hgi, hu, ih]
    | iUnion f hd hfm ih =>
      have hf : ∀ i, MeasurableSet (f i) := fun i => hle _ (hfm i)
      rw [integral_iUnion hf hd hhi'.integrableOn, integral_iUnion hf hd hgi.integrableOn]
      exact tsum_congr ih
  have hh' : StronglyMeasurable[m.comap Prod.fst ⊔ mD.comap Prod.snd] fun u : A × D => h u.1 :=
    hh.comp_measurable ((comap_measurable Prod.fst).mono le_sup_left le_rfl)
  exact (ae_eq_condExp_of_forall_setIntegral_eq hle hgi (fun s _ _ => hhi'.integrableOn)
    (fun s hs _ => hall s hs) hh'.aestronglyMeasurable).symm
end ProductDensity
section Outcomes
variable {ℓ : TorusLumps.StepParameters}
private instance (m : ℕ) [NeZero m] : Fintype (BondSet m) := inferInstanceAs (Fintype (Finset (TorusBond m)))
private theorem measurable_of_stepOutcome {X : Type} [MeasurableSpace X] {n : ℕ} [NeZero n]
    {f : X × StepOutcome ℓ n → ℝ}
    (h : ∀ (b : BaseChoice ℓ.side n) (bad : BondSet (n * ℓ.side)),
      Measurable fun p : X × TorusField n => f (p.1, (b, p.2, bad))) : Measurable f := by apply _root_.YangMills.SharedProofs.p21057 <;> assumption
private instance (ℓ : TorusLumps.StepParameters) (n : ℕ) [NeZero n] :
    IsFiniteMeasure (stepReferenceMeasure ℓ n) := by
  unfold stepReferenceMeasure
  infer_instance
end Outcomes
section SingleStep
variable (R : StepSetup) {n : ℕ} [NeZero n]
private theorem measurable_stepOutcomeDensity (hS : StepTransitionDensityBounds)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad) :
    Measurable fun p : TorusField (n * R.params.side) × StepOutcome R.params n => stepOutcomeDensity R p.1 p.2 :=
  measurable_of_stepOutcome fun b bad => ((hS R.params R.coupling n).1 b).mul (hB bad)
private theorem stepOutcomeDensity_nonneg (hS : StepTransitionDensityBounds)
    (hc : IsCutoff R.ballRadius R.barrierFn)
    (W : TorusField (n * R.params.side)) (d : StepOutcome R.params n) : 0 ≤ stepOutcomeDensity R W d := by apply _root_.YangMills.SharedProofs.p6753 <;> assumption
private theorem lintegral_stepOutcomeDensity (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
    (hf : R.params.Admissible) (hfl : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side)
    (hc : IsCutoff R.ballRadius R.barrierFn)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (W : TorusField (n * R.params.side)) :
    ∫⁻ d, ENNReal.ofReal (stepOutcomeDensity R W d) ∂(stepReferenceMeasure R.params n) = 1 := by apply _root_.YangMills.SharedProofs.p27860 <;> assumption
end SingleStep
section Tower
variable {ℓ : TorusLumps.StepParameters}
private theorem stage_isCutoff (T : StageTower ℓ) (h : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (t : ℕ) :
    IsCutoff (T.stage t).toStepSetup.ballRadius (T.stage t).toStepSetup.barrierFn := by apply _root_.YangMills.SharedProofs.p16 <;> assumption
private theorem measurable_sampleBelow (s : ℕ) : ∀ d n : ℕ, Measurable (sampleBelow ℓ s d n)
  | 0, _ => measurable_id
  | d + 1, n => (measurable_sampleBelow s d (n * ℓ.side)).comp measurable_fst
private theorem stageState_fst (T : StageTower ℓ) : ∀ (s n : ℕ) [NeZero n] (u : MarkedSample ℓ s n),
    (stageState T s n u).1 = topField ℓ s n u
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem measurable_topField_upperSigma (T : StageTower ℓ) (t : ℕ) : ∀ (d n : ℕ) [NeZero n],
    Measurable[upperSigma T t d n] (topField ℓ (t + d) n)
  | 0, n, _ => by
    have e : topField ℓ t n = Prod.fst ∘ stageState T t n := funext fun u => (stageState_fst T t n u).symm
    show Measurable[stageSigma T t n] (topField ℓ t n)
    rw [e]
    exact measurable_fst.comp (comap_measurable _)
  | d + 1, n, _ => by
    have h : Measurable[upperSigma T t (d + 1) n] fun u : MarkedSample ℓ (t + d + 1) n => u.2 :=
      (comap_measurable _).mono le_sup_right le_rfl
    exact (measurable_fst.comp measurable_snd).comp h
private theorem comap_stageSigma_le_upperSigma (T : StageTower ℓ) (t : ℕ) : ∀ (d n : ℕ) [NeZero n],
    (stageSigma T t (fineSide ℓ.side d n)).comap (sampleBelow ℓ t d n) ≤ upperSigma T t d n
  | 0, n, _ => by
    rintro s ⟨s', hs', rfl⟩
    exact hs'
  | d + 1, n, _ => by
    have h := MeasurableSpace.comap_mono (g := fun u : MarkedSample ℓ (t + d + 1) n => u.1)
      (comap_stageSigma_le_upperSigma T t d (n * ℓ.side))
    rw [MeasurableSpace.comap_comp] at h
    exact h.trans le_sup_left
private theorem upperSigma_le (T : StageTower ℓ) (t : ℕ)
    (hst : ∀ (n : ℕ) [NeZero n], stageSigma T t n ≤ markedSampleMeasurableSpace ℓ t n) :
    ∀ (d n : ℕ) [NeZero n], upperSigma T t d n ≤ markedSampleMeasurableSpace ℓ (t + d) n
  | 0, n, _ => hst n
  | d + 1, n, _ => sup_le_sup (MeasurableSpace.comap_mono (upperSigma_le T t hst d (n * ℓ.side))) le_rfl
private theorem condExp_next_stage (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
    (hf : ℓ.Admissible) (hfl : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side) (T : StageTower ℓ)
    (hcut : IsCutoff (ℓ.threshold / 64) T.base.barrierFn)
    (hmark : T.MarksMeasurable) (β : ℝ) (s n : ℕ) [NeZero n]
    {m : MeasurableSpace (MarkedSample ℓ s (n * ℓ.side))}
    (hm : m ≤ markedSampleMeasurableSpace ℓ s (n * ℓ.side)) (htop : Measurable[m] (topField ℓ s (n * ℓ.side)))
    [IsProbabilityMeasure (markedSampleLaw T β s (n * ℓ.side))] {g h : MarkedSample ℓ s (n * ℓ.side) → ℝ}
    (hg : Integrable g (markedSampleLaw T β s (n * ℓ.side))) (hh : StronglyMeasurable[m] h)
    (hgh : (markedSampleLaw T β s (n * ℓ.side))[g|m] =ᵐ[markedSampleLaw T β s (n * ℓ.side)] h) :
    (markedSampleLaw T β (s + 1) n)[fun u => g u.1 | m.comap (fun u : MarkedSample ℓ (s + 1) n => u.1) ⊔
        (inferInstance : MeasurableSpace (StepOutcome ℓ n)).comap (fun u : MarkedSample ℓ (s + 1) n => u.2)]
      =ᵐ[markedSampleLaw T β (s + 1) n] fun u => h u.1 :=
  condExp_withDensity_prod_fst (ρ := stepReferenceMeasure ℓ n) hm
    (w := fun p : TorusField (n * ℓ.side) × StepOutcome ℓ n => stepOutcomeDensity (T.stage s).toStepSetup p.1 p.2)
    (measurable_stepOutcomeDensity (T.stage s).toStepSetup hS (fun bad => hmark s n bad))
    (fun p => stepOutcomeDensity_nonneg (T.stage s).toStepSetup hS (stage_isCutoff T hcut s) p.1 p.2)
    (fun e => lintegral_stepOutcomeDensity (T.stage s).toStepSetup hS hM hf hfl (stage_isCutoff T hcut s)
      (fun bad => hmark s n bad) e)
    htop hg hh hgh
private theorem condExp_upperSigma (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
    (hf : ℓ.Admissible) (hfl : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side) (T : StageTower ℓ)
    (hcut : IsCutoff (ℓ.threshold / 64) T.base.barrierFn)
    (hmark : T.MarksMeasurable) (β : ℝ) (t : ℕ)
    (hlaw : ∀ (s n : ℕ) [NeZero n], IsProbabilityMeasure (markedSampleLaw T β s n))
    (hst : ∀ (n : ℕ) [NeZero n], stageSigma T t n ≤ markedSampleMeasurableSpace ℓ t n) (d : ℕ) :
    ∀ (n : ℕ) [NeZero n] (G H : MarkedSample ℓ t (fineSide ℓ.side d n) → ℝ) (B : ℝ), Measurable G →
      (∀ v, |G v| ≤ B) →
      StronglyMeasurable[stageSigma T t (fineSide ℓ.side d n)] H →
      (markedSampleLaw T β t (fineSide ℓ.side d n))[G | stageSigma T t (fineSide ℓ.side d n)]
        =ᵐ[markedSampleLaw T β t (fineSide ℓ.side d n)] H →
      (markedSampleLaw T β (t + d) n)[fun u => G (sampleBelow ℓ t d n u) | upperSigma T t d n]
        =ᵐ[markedSampleLaw T β (t + d) n] fun u => H (sampleBelow ℓ t d n u) := by
  induction d with
  | zero =>
    intro n _ G H B _ _ _ hGH
    exact hGH
  | succ d ih =>
    intro n _ G H B hG hB hH hGH
    have ih' := ih (n * ℓ.side) G H B hG hB hH hGH
    have := hlaw (t + d) (n * ℓ.side)
    have hdb := measurable_sampleBelow (ℓ := ℓ) t d (n * ℓ.side)
    have hgi : Integrable (fun u => G (sampleBelow ℓ t d (n * ℓ.side) u))
        (markedSampleLaw T β (t + d) (n * ℓ.side)) :=
      Integrable.of_bound (hG.comp hdb).aestronglyMeasurable B
        (Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hB _)
    have hHm : StronglyMeasurable[upperSigma T t d (n * ℓ.side)]
        fun u => H (sampleBelow ℓ t d (n * ℓ.side) u) :=
      hH.comp_measurable ((comap_measurable _).mono (comap_stageSigma_le_upperSigma T t d (n * ℓ.side)) le_rfl)
    have key := condExp_next_stage hS hM hf hfl T hcut hmark β (t + d) n (m := upperSigma T t d (n * ℓ.side))
      (g := fun u => G (sampleBelow ℓ t d (n * ℓ.side) u)) (h := fun u => H (sampleBelow ℓ t d (n * ℓ.side) u))
      (upperSigma_le T t hst d (n * ℓ.side)) (measurable_topField_upperSigma T t d (n * ℓ.side)) hgi hHm ih'
    exact key
end Tower
theorem chainMarkovBackwards (hTP : TwoPointByTotalCovarianceStatement)
    (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean) :
    chainMarkovBackwardsStatement := by
  intro ℓ hf hfl T hcut hmark β t d n _ G B hG hB
  have hlaw : ∀ (s n : ℕ) [NeZero n], IsProbabilityMeasure (markedSampleLaw T β s n) := fun s n _ =>
    (hTP ℓ hf hfl T hcut hmark β (fun _ => 0) s n).1
  have hst : ∀ (n : ℕ) [NeZero n], stageSigma T t n ≤ markedSampleMeasurableSpace ℓ t n := fun n _ =>
    (hTP ℓ hf hfl T hcut hmark β (fun _ => 0) t n).2.1
  have := hlaw (t + d) n
  have hHs : StronglyMeasurable[stageSigma T t (fineSide ℓ.side d n)]
      ((markedSampleLaw T β t (fineSide ℓ.side d n))[G | stageSigma T t (fineSide ℓ.side d n)]) :=
    stronglyMeasurable_condExp
  have key := condExp_upperSigma hS hM hf hfl T hcut hmark β t hlaw hst d n G _ B hG hB hHs
    (Filter.EventuallyEq.refl _ _)
  have hsu := comap_stageSigma_le_upperSigma T t d n
  have hup := upperSigma_le T t hst d n
  have hInt : Integrable (fun u => G (sampleBelow ℓ t d n u)) (markedSampleLaw T β (t + d) n) :=
    Integrable.of_bound (hG.comp (measurable_sampleBelow t d n)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hB _)
  have hHint := (integrable_condExp (m := upperSigma T t d n) (μ := markedSampleLaw T β (t + d) n)
    (f := fun u => G (sampleBelow ℓ t d n u))).congr key
  have t1 := condExp_condExp_of_le (f := fun u => G (sampleBelow ℓ t d n u))
    (μ := markedSampleLaw T β (t + d) n) hsu hup
  have t2 := condExp_congr_ae (m := (stageSigma T t (fineSide ℓ.side d n)).comap (sampleBelow ℓ t d n)) key
  have t3 : (markedSampleLaw T β (t + d) n)[fun u => ((markedSampleLaw T β t (fineSide ℓ.side d n))[G |
        stageSigma T t (fineSide ℓ.side d n)]) (sampleBelow ℓ t d n u) |
        (stageSigma T t (fineSide ℓ.side d n)).comap (sampleBelow ℓ t d n)] =
      fun u => ((markedSampleLaw T β t (fineSide ℓ.side d n))[G | stageSigma T t (fineSide ℓ.side d n)])
        (sampleBelow ℓ t d n u) :=
    condExp_of_stronglyMeasurable (hsu.trans hup)
      (hHs.comp_measurable (comap_measurable (sampleBelow ℓ t d n))) hHint
  refine key.trans ?_
  rw [t3] at t2
  exact (t1.symm.trans t2).symm
end YangMills.Construction.ResponseInTheExpansion
end

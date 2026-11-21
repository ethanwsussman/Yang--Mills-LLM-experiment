import YangMills.Construction.InfiniteLattice.AlmostEveryConditionalMeasureIsAPeriodicGibbsStateProof
import YangMills.Construction.InfiniteLattice.TestExistenceVersionsAndIntegralOfRegularConditionalProbabilities
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory YangMills.Construction.InfiniteLattice
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticePhases.InvariantConditionalFamilies
variable {a : ℝ}
theorem shiftInvariantSigma_le :
    shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
  fun _ hs => hs.1
theorem integrable_of_isBoundedObservable {μ : Measure (GaugeField a)} [IsFiniteMeasure μ]
    {f : GaugeField a → ℂ} (hf : IsBoundedObservable f) : Integrable f μ := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.integrable_of_isBoundedObservable <;> assumption
theorem norm_eval_le (ρ : ProbMeasure (GaugeField a)) {f : GaugeField a → ℂ} {B : ℝ}
    (hB : ∀ x, ‖f x‖ ≤ B) : ‖ρ.eval f‖ ≤ B := by apply _root_.YangMills.Construction.LatticePhases.ConditionalGibbsProof.norm_eval_le <;> assumption
theorem integral_indicator_one_eq_measureReal (ρ : Measure (GaugeField a))
    {E : Set (GaugeField a)} (hE : MeasurableSet E) :
    ∫ x, E.indicator (1 : GaugeField a → ℂ) x ∂ρ = ((ρ.real E : ℝ) : ℂ) := by
  have hind := integral_indicator_const (μ := ρ) (1 : ℂ) hE
  simpa [Pi.one_def] using hind
theorem integral_indicator_one_mul_eq_setIntegral (μ : Measure (GaugeField a))
    {S : Set (GaugeField a)} (hS : MeasurableSet S) (g : GaugeField a → ℂ) :
    ∫ x, S.indicator (1 : GaugeField a → ℂ) x * g x ∂μ = ∫ x in S, g x ∂μ := by
  rw [← integral_indicator hS]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ S <;> simp [hx]
theorem integral_mul_eq_integral_mul_of_ae_eq_condExp {μ : Measure (GaugeField a)}
    [IsFiniteMeasure μ] {f g j : GaugeField a → ℂ} (hf : IsBoundedObservable f)
    (hg : g =ᵐ[μ] μ[f | shiftInvariantSigma a])
    (hj : Measurable[shiftInvariantSigma a] j) (hjb : ∃ B : ℝ, ∀ x, ‖j x‖ ≤ B) :
    ∫ x, j x * g x ∂μ = ∫ x, j x * f x ∂μ := by
  have hle := shiftInvariantSigma_le (a := a)
  obtain ⟨B, hB⟩ := hjb
  obtain ⟨B', hB'⟩ := hf.2
  have hjf : Integrable (fun x => j x * f x) μ :=
    integrable_of_isBoundedObservable ⟨(hj.mono hle le_rfl).mul hf.1, B * B', fun x => by
      rw [norm_mul]
      exact mul_le_mul (hB x) (hB' x) (norm_nonneg _) ((norm_nonneg _).trans (hB x))⟩
  have hjf' : Integrable (fun x => ContinuousLinearMap.mul ℝ ℂ (j x) (f x)) μ := hjf
  have hpull := condExp_bilin_of_stronglyMeasurable_left (m := shiftInvariantSigma a) (μ := μ)
    (ContinuousLinearMap.mul ℝ ℂ) hj.stronglyMeasurable hjf'
    (integrable_of_isBoundedObservable hf)
  calc ∫ x, j x * g x ∂μ
        = ∫ x, ContinuousLinearMap.mul ℝ ℂ (j x) ((μ[f | shiftInvariantSigma a]) x) ∂μ :=
        integral_congr_ae (hg.mono fun x hx => by simp [hx])
    _ = ∫ x, (μ[fun x => ContinuousLinearMap.mul ℝ ℂ (j x) (f x) | shiftInvariantSigma a]) x ∂μ :=
        (integral_congr_ae hpull).symm
    _ = ∫ x, j x * f x ∂μ := integral_condExp hle
theorem ae_eq_condExp_of_isCondExpRepresentative {μ : Measure (GaugeField a)} [IsFiniteMeasure μ]
    {f y : GaugeField a → ℂ} (hf : IsBoundedObservable f)
    (hy : IsIntegrableCondExpRepresentative μ f y) : y =ᵐ[μ] μ[f | shiftInvariantSigma a] := by
  have hle := shiftInvariantSigma_le (a := a)
  have hyi : Integrable y μ := ⟨(hy.1.mono hle le_rfl).aestronglyMeasurable, hy.2.1⟩
  refine ae_eq_condExp_of_forall_setIntegral_eq hle (integrable_of_isBoundedObservable hf)
    (fun s _ _ => hyi.integrableOn) (fun s hs _ => ?_) hy.1.stronglyMeasurable.aestronglyMeasurable
  have hs' := hy.2.2 (s.indicator 1)
    (Measurable.indicator (@measurable_const ℂ _ _ (shiftInvariantSigma a) (1 : ℂ)) hs)
    ⟨1, fun x => by by_cases hx : x ∈ s <;> simp [hx]⟩
  exact (integral_indicator_one_mul_eq_setIntegral μ (hle s hs) y).symm.trans
    (hs'.trans (integral_indicator_one_mul_eq_setIntegral μ (hle s hs) f))
section FamilyCriterion
variable {μ : Measure (GaugeField a)} [IsFiniteMeasure μ]
  {κ : GaugeField a → ProbMeasure (GaugeField a)}
theorem measurable_measure_apply_of_eval_indicator
    (hκ : ∀ E : Set (GaugeField a), MeasurableSet E →
      Measurable[shiftInvariantSigma a]
        (fun x => (κ x).eval (E.indicator (1 : GaugeField a → ℂ))))
    {E : Set (GaugeField a)} (hE : MeasurableSet E) :
    Measurable[shiftInvariantSigma a] (fun x => (κ x).toMeasure E) := by
  have hre := Complex.measurable_re.comp (hκ E hE)
  have e : (Complex.re ∘ fun x => (κ x).eval (E.indicator (1 : GaugeField a → ℂ))) =
      fun x => (κ x).toMeasure.real E := by
    funext x
    simp [ProbMeasure.eval, integral_indicator_one_eq_measureReal _ hE]
  rw [e] at hre
  have e2 : (fun x => (κ x).toMeasure E) =
      fun x => ENNReal.ofReal ((κ x).toMeasure.real E) := by
    funext x
    simp [ofReal_measureReal]
  rw [e2]
  exact ENNReal.measurable_ofReal.comp hre
theorem measurable_toMeasure_family
    (hκ : ∀ E : Set (GaugeField a), MeasurableSet E →
      Measurable[shiftInvariantSigma a]
        (fun x => (κ x).eval (E.indicator (1 : GaugeField a → ℂ)))) :
    Measurable[shiftInvariantSigma a] (fun x => (κ x).toMeasure) :=
  @Measure.measurable_of_measurable_coe _ _ _ (shiftInvariantSigma a) (fun x => (κ x).toMeasure)
    (fun _ hs => measurable_measure_apply_of_eval_indicator hκ hs)
theorem setIntegral_eval_eq
    (hκ : ∀ E : Set (GaugeField a), MeasurableSet E →
      Measurable[shiftInvariantSigma a]
        (fun x => (κ x).eval (E.indicator (1 : GaugeField a → ℂ))))
    (hint : ∀ E : Set (GaugeField a), MeasurableSet E →
      ∀ S : Set (GaugeField a), MeasurableSet[shiftInvariantSigma a] S →
        ∫ x, S.indicator (1 : GaugeField a → ℂ) x *
            (κ x).eval (E.indicator (1 : GaugeField a → ℂ)) ∂μ =
          ∫ x, S.indicator (1 : GaugeField a → ℂ) x *
            E.indicator (1 : GaugeField a → ℂ) x ∂μ)
    {f : GaugeField a → ℂ} (hf : IsBoundedObservable f)
    {S : Set (GaugeField a)} (hS : MeasurableSet[shiftInvariantSigma a] S) :
    ∫ x in S, (κ x).eval f ∂μ = ∫ x in S, f x ∂μ := by
  have hle := shiftInvariantSigma_le (a := a)
  have hSb : MeasurableSet S := hle S hS
  let K : Kernel (GaugeField a) (GaugeField a) :=
    ⟨fun x => (κ x).toMeasure, (measurable_toMeasure_family hκ).mono hle le_rfl⟩
  have : IsMarkovKernel K := ⟨fun x => by
    show IsProbabilityMeasure (κ x).toMeasure
    infer_instance⟩
  have hbind : K ∘ₘ (μ.restrict S) = μ.restrict S := by
    ext E hE
    rw [Measure.bind_apply hE K.aemeasurable]
    have hreal : ∫ x, (K x).real E ∂(μ.restrict S) = (μ.restrict S).real E := by
      have e : ∀ x, (κ x).eval (E.indicator (1 : GaugeField a → ℂ)) =
          (((K x).real E : ℝ) : ℂ) := fun x => integral_indicator_one_eq_measureReal _ hE
      have hc := (integral_indicator_one_mul_eq_setIntegral μ hSb _).symm.trans
        ((hint E hE S hS).trans (integral_indicator_one_mul_eq_setIntegral μ hSb _))
      rw [integral_indicator_one_eq_measureReal _ hE] at hc
      simp only [e] at hc
      rw [integral_complex_ofReal] at hc
      exact_mod_cast hc
    have h2 : ∫ x, (K x).real E ∂(μ.restrict S) = (∫⁻ x, K x E ∂(μ.restrict S)).toReal :=
      integral_toReal (K.measurable_coe hE).aemeasurable (ae_of_all _ fun x => measure_lt_top _ _)
    have hfin : ∫⁻ x, K x E ∂(μ.restrict S) ≠ ∞ := by
      refine ne_top_of_le_ne_top (measure_ne_top (μ.restrict S) Set.univ) ?_
      calc ∫⁻ x, K x E ∂(μ.restrict S) ≤ ∫⁻ _, 1 ∂(μ.restrict S) :=
            lintegral_mono fun x => prob_le_one
        _ = (μ.restrict S) Set.univ := by simp
    exact (ENNReal.toReal_eq_toReal_iff' hfin (measure_ne_top _ _)).1 (h2.symm.trans hreal)
  obtain ⟨B, hB⟩ := hf.2
  have hfb : Integrable (fun p : GaugeField a × GaugeField a => f p.2)
      ((μ.restrict S) ⊗ₘ K) :=
    Integrable.of_bound (hf.1.comp measurable_snd).aestronglyMeasurable B
      (ae_of_all _ fun p => hB p.2)
  calc ∫ x in S, (κ x).eval f ∂μ = ∫ x, ∫ y, f y ∂K x ∂(μ.restrict S) := rfl
    _ = ∫ p, f p.2 ∂((μ.restrict S) ⊗ₘ K) := (Measure.integral_compProd hfb).symm
    _ = ∫ y, f y ∂((μ.restrict S) ⊗ₘ K).snd :=
        (integral_map measurable_snd.aemeasurable hf.1.aestronglyMeasurable).symm
    _ = ∫ x in S, f x ∂μ := by rw [Measure.snd_compProd, hbind]
theorem measurable_and_integral_of_criterion
    (hκ : ∀ E : Set (GaugeField a), MeasurableSet E →
      Measurable[shiftInvariantSigma a]
        (fun x => (κ x).eval (E.indicator (1 : GaugeField a → ℂ))))
    (hint : ∀ E : Set (GaugeField a), MeasurableSet E →
      ∀ S : Set (GaugeField a), MeasurableSet[shiftInvariantSigma a] S →
        ∫ x, S.indicator (1 : GaugeField a → ℂ) x *
            (κ x).eval (E.indicator (1 : GaugeField a → ℂ)) ∂μ =
          ∫ x, S.indicator (1 : GaugeField a → ℂ) x *
            E.indicator (1 : GaugeField a → ℂ) x ∂μ)
    {f : GaugeField a → ℂ} (hf : IsBoundedObservable f) :
    Measurable[shiftInvariantSigma a] (fun x => (κ x).eval f) ∧
      ∀ j : GaugeField a → ℂ, Measurable[shiftInvariantSigma a] j →
        (∃ B : ℝ, ∀ x, ‖j x‖ ≤ B) →
          ∫ x, j x * (κ x).eval f ∂μ = ∫ x, j x * f x ∂μ := by
  have hle := shiftInvariantSigma_le (a := a)
  have hg : Measurable[shiftInvariantSigma a] (fun x => (κ x).eval f) :=
    (StronglyMeasurable.integral_kernel
      (κ := @Kernel.mk _ _ (shiftInvariantSigma a) _ (fun x => (κ x).toMeasure)
        (measurable_toMeasure_family hκ))
      hf.1.stronglyMeasurable).measurable
  obtain ⟨B, hB⟩ := hf.2
  have hgi : Integrable (fun x => (κ x).eval f) μ :=
    Integrable.of_bound (hg.mono hle le_rfl).aestronglyMeasurable B
      (ae_of_all _ fun x => norm_eval_le (κ x) hB)
  have hae : (fun x => (κ x).eval f) =ᵐ[μ] μ[f | shiftInvariantSigma a] :=
    ae_eq_condExp_of_forall_setIntegral_eq hle (integrable_of_isBoundedObservable hf)
      (fun s _ _ => hgi.integrableOn) (fun s hs _ => setIntegral_eval_eq hκ hint hf hs)
      hg.stronglyMeasurable.aestronglyMeasurable
  exact ⟨hg, fun j hj hjb => integral_mul_eq_integral_mul_of_ae_eq_condExp hf hae hj hjb⟩
end FamilyCriterion
theorem standardBorelSpace_gaugeField (D : Setup) (hD : TopologyDensity D) :
    StandardBorelSpace (GaugeField D.mesh) := by
  have := hD.compact
  have := hD.metrizable
  let := TopologicalSpace.metrizableSpaceMetric (GaugeField D.mesh)
  infer_instance
theorem exists_conditional_family [StandardBorelSpace (GaugeField a)]
    (μ : Measure (GaugeField a)) [IsProbabilityMeasure μ] :
    ∃ κ : GaugeField a → ProbMeasure (GaugeField a), ∀ f : GaugeField a → ℂ,
      IsBoundedObservable f →
      Measurable[shiftInvariantSigma a] (fun x => (κ x).eval f) ∧
        ∀ j : GaugeField a → ℂ, Measurable[shiftInvariantSigma a] j →
          (∃ B : ℝ, ∀ x, ‖j x‖ ≤ B) →
            ∫ x, j x * (κ x).eval f ∂μ = ∫ x, j x * f x ∂μ := by
  have hle := shiftInvariantSigma_le (a := a)
  refine ⟨fun x => ⟨condExpKernel μ (shiftInvariantSigma a) x, inferInstance⟩, fun f hf => ?_⟩
  refine ⟨hf.1.stronglyMeasurable.integral_condExpKernel.measurable, fun j hj hjb => ?_⟩
  exact integral_mul_eq_integral_mul_of_ae_eq_condExp hf
    (condExp_ae_eq_integral_condExpKernel hle (integrable_of_isBoundedObservable hf)).symm hj hjb
theorem isCondExpRepresentative_of_family {μ : Measure (GaugeField a)} [IsFiniteMeasure μ]
    {κ : GaugeField a → ProbMeasure (GaugeField a)} {f : GaugeField a → ℂ}
    (hf : IsBoundedObservable f)
    (hκ : Measurable[shiftInvariantSigma a] (fun x => (κ x).eval f) ∧
      ∀ j : GaugeField a → ℂ, Measurable[shiftInvariantSigma a] j →
        (∃ B : ℝ, ∀ x, ‖j x‖ ≤ B) →
          ∫ x, j x * (κ x).eval f ∂μ = ∫ x, j x * f x ∂μ) :
    IsIntegrableCondExpRepresentative μ f (fun x => (κ x).eval f) ∧
      ∀ y : GaugeField a → ℂ, IsIntegrableCondExpRepresentative μ f y →
        ∀ᵐ x ∂μ, (κ x).eval f = y x := by
  have hle := shiftInvariantSigma_le (a := a)
  obtain ⟨hg, hj⟩ := hκ
  obtain ⟨B, hB⟩ := hf.2
  have hv : IsIntegrableCondExpRepresentative μ f (fun x => (κ x).eval f) :=
    ⟨hg, (Integrable.of_bound (hg.mono hle le_rfl).aestronglyMeasurable B
      (ae_of_all _ fun x => norm_eval_le (κ x) hB)).2, hj⟩
  exact ⟨hv, fun y hy =>
    (ae_eq_condExp_of_isCondExpRepresentative hf hv).trans (ae_eq_condExp_of_isCondExpRepresentative hf hy).symm⟩
theorem isFiniteMeasure_of_isProbabilityMeasure {μ : Measure (GaugeField a)}
    (hμ : IsProbabilityMeasure μ) : IsFiniteMeasure μ :=
  inferInstance
theorem holds (hTop : TopologyDensityHolds) : InvariantConditionalFamilies.Statement := by
  intro D ν
  have hP : @IsProbabilityMeasure (GaugeField D.mesh) _ ν.1 := ν.2.1.1
  have hFin : @IsFiniteMeasure (GaugeField D.mesh) _ ν.1 :=
    isFiniteMeasure_of_isProbabilityMeasure hP
  have hSB := standardBorelSpace_gaugeField D (hTop D)
  refine ⟨fun κ hκ f hf => ?_, ?_, fun κ hκ f hf => ?_, fun κ hκ f hf => ?_⟩
  · exact @measurable_and_integral_of_criterion D.mesh ν.1 hFin κ
      (fun E hE => (hκ E hE).1) (fun E hE => (hκ E hE).2) f hf
  · exact @exists_conditional_family D.mesh hSB ν.1 hP
  · exact @isCondExpRepresentative_of_family D.mesh ν.1 hFin κ f hf (hκ f hf)
  · have hc := (hκ f hf).2 (fun _ => 1) measurable_const ⟨1, fun x => by simp⟩
    simp only [one_mul] at hc
    exact hc.symm
end YangMills.Construction.LatticePhases.InvariantConditionalFamilies

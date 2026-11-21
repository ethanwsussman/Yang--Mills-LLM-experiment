import YangMills.Construction.InfiniteLattice.FunctionsOfTheBondsOfASetAndSupports
import YangMills.Construction.InfiniteLattice.PropertiesOfTheKernelsOfBonds
import YangMills.Construction.InfiniteLattice.TheSpaceOfConfigurationsAndTheSpaceOfMeasures
import YangMills.Construction.Matrices.HaarExpChartDensity
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice Set Filter
open scoped ComplexOrder ENNReal Topology
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing.LinkKernels
variable {a : ℝ}
theorem secondCountable_specialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact TopologicalSpace.Subtype.secondCountableTopology
    (Matrices.ComplexMatrix2.specialUnitary : Set Matrices.ComplexMatrix2)
attribute [local instance] secondCountable_specialUnitary
theorem isProbabilityMeasure_haarMeasure (ι : Type) [Countable ι] :
    IsProbabilityMeasure (LinkVariables.haarMeasure ι) :=
  inferInstanceAs (IsProbabilityMeasure
    (Measure.infinitePi fun _ : ι => Matrices.ComplexMatrix2.haarProb))
attribute [local instance] isProbabilityMeasure_haarMeasure
theorem norm_le_supNorm {F : GaugeField a → ℂ} (hF : ∃ C : ℝ, ∀ U, ‖F U‖ ≤ C)
    (U : GaugeField a) : ‖F U‖ ≤ observableSupNorm F := by
  obtain ⟨C, hC⟩ := hF
  exact le_ciSup (f := fun U => ‖F U‖) ⟨C, by rintro _ ⟨U, rfl⟩; exact hC U⟩ U
theorem supNorm_nonneg (F : GaugeField a → ℂ) : 0 ≤ observableSupNorm F :=
  Real.iSup_nonneg fun _ => norm_nonneg _
instance instNonemptyGaugeField : Nonempty (GaugeField a) := ⟨trivialField a⟩
section FixedSet
variable {𝓛 : Finset (Link a)} {h : HasNoOppositePairs (𝓛 : Set (Link a))}
  {W : GaugeField a → ℝ} {N : ℝ}
theorem overwriteLinks_apply_of_mem (V : LinkVariables (𝓛 : Set (Link a))) (U : GaugeField a)
    {b : Link a} (hb : b ∈ (𝓛 : Set (Link a))) : (overwriteLinks h V U) b = V ⟨b, hb⟩ := by
  simp only [overwriteLinks, dif_pos hb]
theorem overwriteLinks_apply_of_opposite_mem (V : LinkVariables (𝓛 : Set (Link a)))
    (U : GaugeField a) {b : Link a} (hb : b ∉ (𝓛 : Set (Link a)))
    (hr : b.opposite ∈ (𝓛 : Set (Link a))) :
    (overwriteLinks h V U) b = (V ⟨b.opposite, hr⟩)⁻¹ := by
  simp only [overwriteLinks, dif_neg hb, dif_pos hr]
theorem overwriteLinks_apply_of_not_mem (V : LinkVariables (𝓛 : Set (Link a))) (U : GaugeField a)
    {b : Link a} (hb : b ∉ (𝓛 : Set (Link a))) (hr : b.opposite ∉ (𝓛 : Set (Link a))) :
    (overwriteLinks h V U) b = U b := by
  simp only [overwriteLinks, dif_neg hb, dif_neg hr]
theorem overwriteLinks_overwriteLinks (V V' : LinkVariables (𝓛 : Set (Link a)))
    (U : GaugeField a) :
    overwriteLinks h V (overwriteLinks h V' U) = overwriteLinks h V U := by
  apply Subtype.ext
  funext b
  by_cases hb : b ∈ (𝓛 : Set (Link a))
  · change (overwriteLinks h V _) b = (overwriteLinks h V _) b
    rw [overwriteLinks_apply_of_mem V _ hb, overwriteLinks_apply_of_mem V _ hb]
  · by_cases hr : b.opposite ∈ (𝓛 : Set (Link a))
    · change (overwriteLinks h V _) b = (overwriteLinks h V _) b
      rw [overwriteLinks_apply_of_opposite_mem V _ hb hr,
        overwriteLinks_apply_of_opposite_mem V _ hb hr]
    · change (overwriteLinks h V _) b = (overwriteLinks h V _) b
      rw [overwriteLinks_apply_of_not_mem V _ hb hr, overwriteLinks_apply_of_not_mem V _ hb hr,
        overwriteLinks_apply_of_not_mem V' _ hb hr]
def JointlyMeasurable (h : HasNoOppositePairs (𝓛 : Set (Link a))) : Prop :=
  Measurable fun q : GaugeField a × LinkVariables (𝓛 : Set (Link a)) => overwriteLinks h q.2 q.1
theorem JointlyMeasurable.slice (hm : JointlyMeasurable h) (U : GaugeField a) :
    Measurable fun V : LinkVariables (𝓛 : Set (Link a)) => overwriteLinks h V U :=
  Measurable.comp (g := fun q : GaugeField a × LinkVariables (𝓛 : Set (Link a)) =>
    overwriteLinks h q.2 q.1) hm measurable_prodMk_left
theorem exp_neg_bounds (hN : ∀ U, |W U| ≤ N) (U : GaugeField a) :
    Real.exp (-N) ≤ Real.exp (-W U) ∧ Real.exp (-W U) ≤ Real.exp N := by
  have := abs_le.mp (hN U)
  exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩
theorem integrable_boltzmann (hm : JointlyMeasurable h) (hWm : Measurable W)
    (hN : ∀ U, |W U| ≤ N) (U : GaugeField a) :
    Integrable (fun V => Real.exp (-W (overwriteLinks h V U)))
      (LinkVariables.haarMeasure (𝓛 : Set (Link a))) := by
  refine Integrable.of_bound (C := Real.exp N)
    (Real.measurable_exp.comp (hWm.comp (hm.slice U)).neg).aestronglyMeasurable
    (ae_of_all _ fun V => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (exp_neg_bounds hN _).2
theorem integrable_kernelNumerator_integrand (hm : JointlyMeasurable h) (hWm : Measurable W)
    (hN : ∀ U, |W U| ≤ N) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (U : GaugeField a) :
    Integrable (fun V => F (overwriteLinks h V U) * (Real.exp (-W (overwriteLinks h V U)) : ℂ))
      (LinkVariables.haarMeasure (𝓛 : Set (Link a))) := by
  obtain ⟨hFm, C, hC⟩ := hF
  refine Integrable.of_bound (C := C * Real.exp N) ?_ (ae_of_all _ fun V => ?_)
  · exact ((hFm.comp (hm.slice U)).mul (Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp (hWm.comp (hm.slice U)).neg))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC U)
    exact mul_le_mul (hC _) (exp_neg_bounds hN _).2 (Real.exp_pos _).le hC0
theorem exp_neg_le_kernelDenominator (hm : JointlyMeasurable h) (hWm : Measurable W)
    (hN : ∀ U, |W U| ≤ N) (U : GaugeField a) :
    Real.exp (-N) ≤ kernelDenominator 𝓛 h W U := by
  have h1 : ∫ _V : LinkVariables (𝓛 : Set (Link a)), Real.exp (-N)
      ∂LinkVariables.haarMeasure (𝓛 : Set (Link a)) = Real.exp (-N) := by simp
  rw [← h1]
  exact integral_mono (integrable_const _) (integrable_boltzmann hm hWm hN U)
    fun V => (exp_neg_bounds hN _).1
theorem kernelDenominator_pos (hm : JointlyMeasurable h) (hWm : Measurable W)
    (hN : ∀ U, |W U| ≤ N) (U : GaugeField a) : 0 < kernelDenominator 𝓛 h W U :=
  (Real.exp_pos _).trans_le (exp_neg_le_kernelDenominator hm hWm hN U)
def boltzmannDensity (h : HasNoOppositePairs (𝓛 : Set (Link a))) (W : GaugeField a → ℝ)
    (U : GaugeField a) (V : LinkVariables (𝓛 : Set (Link a))) : ℝ :=
  Real.exp (-W (overwriteLinks h V U)) / kernelDenominator 𝓛 h W U
theorem boltzmannDensity_pos (hm : JointlyMeasurable h) (hWm : Measurable W)
    (hN : ∀ U, |W U| ≤ N) (U : GaugeField a) (V : LinkVariables (𝓛 : Set (Link a))) :
    0 < boltzmannDensity h W U V :=
  div_pos (Real.exp_pos _) (kernelDenominator_pos hm hWm hN U)
theorem integrable_boltzmannDensity (hm : JointlyMeasurable h) (hWm : Measurable W)
    (hN : ∀ U, |W U| ≤ N) (U : GaugeField a) :
    Integrable (boltzmannDensity h W U) (LinkVariables.haarMeasure (𝓛 : Set (Link a))) :=
  (integrable_boltzmann hm hWm hN U).div_const _
theorem integral_boltzmannDensity (hm : JointlyMeasurable h) (hWm : Measurable W)
    (hN : ∀ U, |W U| ≤ N) (U : GaugeField a) :
    ∫ V, boltzmannDensity h W U V ∂LinkVariables.haarMeasure (𝓛 : Set (Link a)) = 1 := by
  have h0 := kernelDenominator_pos hm hWm hN U
  simp only [boltzmannDensity]
  rw [integral_div]
  exact div_self h0.ne'
theorem linkKernel_eq_integral_density (F : GaugeField a → ℂ) (U : GaugeField a) :
    linkKernel 𝓛 h W F U =
      ∫ V, F (overwriteLinks h V U) * (boltzmannDensity h W U V : ℂ)
        ∂LinkVariables.haarMeasure (𝓛 : Set (Link a)) := by
  rw [linkKernel_eq_div, kernelNumerator, ← integral_div]
  congr 1
  funext V
  simp only [boltzmannDensity]
  push_cast
  rw [mul_div_assoc]
theorem integrable_mul_boltzmannDensity (hm : JointlyMeasurable h) (hWm : Measurable W)
    (hN : ∀ U, |W U| ≤ N) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (U : GaugeField a) :
    Integrable (fun V => F (overwriteLinks h V U) * (boltzmannDensity h W U V : ℂ))
      (LinkVariables.haarMeasure (𝓛 : Set (Link a))) := by
  have := (integrable_kernelNumerator_integrand hm hWm hN hF U).div_const
    ((kernelDenominator 𝓛 h W U : ℝ) : ℂ)
  refine this.congr (ae_of_all _ fun V => ?_)
  simp only [boltzmannDensity]
  push_cast
  rw [mul_div_assoc]
theorem measurable_integral_prod_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : GaugeField a × LinkVariables (𝓛 : Set (Link a)) → E} (hf : Measurable f) :
    Measurable fun U => ∫ V, f (U, V) ∂LinkVariables.haarMeasure (𝓛 : Set (Link a)) :=
  (hf.stronglyMeasurable.integral_prod_right').measurable
theorem measurable_kernelDenominator (hm : JointlyMeasurable h) (hWm : Measurable W) :
    Measurable (kernelDenominator 𝓛 h W) :=
  measurable_integral_prod_right (f := fun q => Real.exp (-W (overwriteLinks h q.2 q.1)))
    (Real.measurable_exp.comp (hWm.comp hm).neg)
theorem measurable_kernelNumerator (hm : JointlyMeasurable h) (hWm : Measurable W)
    {F : GaugeField a → ℂ} (hF : Measurable F) :
    Measurable (kernelNumerator 𝓛 h W F) :=
  measurable_integral_prod_right
    (f := fun q => F (overwriteLinks h q.2 q.1) * (Real.exp (-W (overwriteLinks h q.2 q.1)) : ℂ))
    ((hF.comp hm).mul (Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp (hWm.comp hm).neg)))
theorem isBoundedObservable_kernelNumerator (hm : JointlyMeasurable h) (hWm : Measurable W)
    (hN : ∀ U, |W U| ≤ N) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable (kernelNumerator 𝓛 h W F) := by
  refine ⟨measurable_kernelNumerator hm hWm hF.1, ?_⟩
  obtain ⟨C, hC⟩ := hF.2
  refine ⟨C * Real.exp N, fun U => ?_⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC U)
  have := norm_integral_le_of_norm_le_const (μ := LinkVariables.haarMeasure (𝓛 : Set (Link a)))
    (f := fun V => F (overwriteLinks h V U) * (Real.exp (-W (overwriteLinks h V U)) : ℂ))
    (C := C * Real.exp N) (ae_of_all _ fun V => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (hC _) (exp_neg_bounds hN _).2 (Real.exp_pos _).le hC0)
  simpa [kernelNumerator] using this
theorem isBoundedObservable_kernelDenominator (hm : JointlyMeasurable h) (hWm : Measurable W)
    (hN : ∀ U, |W U| ≤ N) :
    IsBoundedObservable fun U => (kernelDenominator 𝓛 h W U : ℂ) := by
  refine ⟨Complex.measurable_ofReal.comp (measurable_kernelDenominator hm hWm), Real.exp N,
    fun U => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h1 := norm_integral_le_of_norm_le_const (μ := LinkVariables.haarMeasure (𝓛 : Set (Link a)))
    (f := fun V => Real.exp (-W (overwriteLinks h V U))) (C := Real.exp N)
    (ae_of_all _ fun V => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (exp_neg_bounds hN _).2)
  simpa [kernelDenominator] using h1
theorem norm_linkKernel_le (hm : JointlyMeasurable h) (hWm : Measurable W) (hN : ∀ U, |W U| ≤ N)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) (U : GaugeField a) :
    ‖linkKernel 𝓛 h W F U‖ ≤ observableSupNorm F := by
  rw [linkKernel_eq_integral_density]
  have h1 := norm_integral_le_of_norm_le
    (μ := LinkVariables.haarMeasure (𝓛 : Set (Link a)))
    (f := fun V => F (overwriteLinks h V U) * (boltzmannDensity h W U V : ℂ))
    ((integrable_boltzmannDensity hm hWm hN U).const_mul (observableSupNorm F))
    (ae_of_all _ fun V => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (boltzmannDensity_pos hm hWm hN U V)]
      exact mul_le_mul_of_nonneg_right (norm_le_supNorm hF.2 _)
        (boltzmannDensity_pos hm hWm hN U V).le)
  rwa [integral_const_mul, integral_boltzmannDensity hm hWm hN, mul_one] at h1
theorem isBoundedObservable_linkKernel (hm : JointlyMeasurable h) (hWm : Measurable W)
    (hN : ∀ U, |W U| ≤ N) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable (linkKernel 𝓛 h W F) := by
  refine ⟨?_, observableSupNorm F, norm_linkKernel_le hm hWm hN hF⟩
  have := (measurable_kernelNumerator (h := h) hm hWm hF.1).div
    (isBoundedObservable_kernelDenominator (h := h) hm hWm hN).1
  exact this
theorem isIndependentOfLinks_linkKernel (F : GaugeField a → ℂ) :
    IsIndependentOfLinks h (linkKernel 𝓛 h W F) := by
  intro V' U
  simp only [linkKernel, overwriteLinks_overwriteLinks]
theorem linkKernel_nonneg (hm : JointlyMeasurable h) (hWm : Measurable W) (hN : ∀ U, |W U| ≤ N)
    {F : GaugeField a → ℂ} (hF : ∀ U, 0 ≤ F U) (U : GaugeField a) :
    0 ≤ linkKernel 𝓛 h W F U := by
  have hre : ∀ U, F U = ((F U).re : ℂ) := fun U => by
    apply Complex.ext
    · simp
    · simpa using (Complex.nonneg_iff.mp (hF U)).2.symm
  rw [linkKernel_eq_integral_density]
  have e : ∀ V, F (overwriteLinks h V U) * (boltzmannDensity h W U V : ℂ) =
      (((F (overwriteLinks h V U)).re * boltzmannDensity h W U V : ℝ) : ℂ) := fun V => by
    rw [hre (overwriteLinks h V U)]
    simp
  simp only [e]
  rw [integral_complex_ofReal]
  refine Complex.zero_le_real.mpr (integral_nonneg fun V => ?_)
  exact mul_nonneg (Complex.nonneg_iff.mp (hF _)).1 (boltzmannDensity_pos hm hWm hN U V).le
theorem linkKernel_linear (hm : JointlyMeasurable h) (hWm : Measurable W) (hN : ∀ U, |W U| ≤ N)
    (c c' : ℂ) {F F' : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hF' : IsBoundedObservable F') :
    linkKernel 𝓛 h W (fun U => c * F U + c' * F' U) =
      fun U => c * linkKernel 𝓛 h W F U + c' * linkKernel 𝓛 h W F' U := by
  funext U
  simp only [linkKernel_eq_integral_density]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((integrable_mul_boltzmannDensity hm hWm hN hF U).const_mul c)
    ((integrable_mul_boltzmannDensity hm hWm hN hF' U).const_mul c')]
  congr 1
  funext V
  ring
theorem linkKernel_one (hm : JointlyMeasurable h) (hWm : Measurable W) (hN : ∀ U, |W U| ≤ N) :
    linkKernel 𝓛 h W (fun _ => 1) = fun _ => 1 := by
  funext U
  rw [linkKernel_eq_integral_density]
  simp only [one_mul]
  rw [integral_complex_ofReal, integral_boltzmannDensity hm hWm hN]
  simp
theorem linkKernel_mul_left {H : GaugeField a → ℂ} (hH : IsIndependentOfLinks h H)
    (F : GaugeField a → ℂ) :
    linkKernel 𝓛 h W (fun U => H U * F U) = fun U => H U * linkKernel 𝓛 h W F U := by
  funext U
  simp only [linkKernel_eq_integral_density, hH _ U, mul_assoc]
  rw [integral_const_mul]
theorem dependsOnlyOnLinks_linkKernel {S : Set (Link a)} {F : GaugeField a → ℂ}
    (hW : DependsOnlyOnLinks S W) (hF : DependsOnlyOnLinks S F) :
    DependsOnlyOnLinks S (linkKernel 𝓛 h W F) := by
  intro U U' hUU
  have key : ∀ V : LinkVariables (𝓛 : Set (Link a)),
      restrictField (overwriteLinks h V U) S = restrictField (overwriteLinks h V U') S := by
    intro V
    funext b
    change (overwriteLinks h V U) b.1 = (overwriteLinks h V U') b.1
    by_cases hb : b.1 ∈ (𝓛 : Set (Link a))
    · rw [overwriteLinks_apply_of_mem V _ hb, overwriteLinks_apply_of_mem V _ hb]
    · by_cases hr : b.1.opposite ∈ (𝓛 : Set (Link a))
      · rw [overwriteLinks_apply_of_opposite_mem V _ hb hr,
          overwriteLinks_apply_of_opposite_mem V _ hb hr]
      · rw [overwriteLinks_apply_of_not_mem V _ hb hr, overwriteLinks_apply_of_not_mem V _ hb hr]
        exact congrFun hUU b
  have e1 : ∀ V, F (overwriteLinks h V U) = F (overwriteLinks h V U') := fun V => hF _ _ (key V)
  have e2 : ∀ V, W (overwriteLinks h V U) = W (overwriteLinks h V U') := fun V => hW _ _ (key V)
  simp only [linkKernel, e1, e2]
theorem continuous_linkKernel [FirstCountableTopology (GaugeField a)]
    (hc : ∀ V : LinkVariables (𝓛 : Set (Link a)), Continuous fun U => overwriteLinks h V U)
    (hm : JointlyMeasurable h) (hWc : Continuous W) (hN : ∀ U, |W U| ≤ N)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) (hFc : Continuous F) :
    Continuous (linkKernel 𝓛 h W F) := by
  have hWm : Measurable W := hWc.measurable
  obtain ⟨C, hC⟩ := hF.2
  have hnum : Continuous (kernelNumerator 𝓛 h W F) := by
    refine continuous_of_dominated (bound := fun _ => C * Real.exp N)
      (fun U => (integrable_kernelNumerator_integrand hm hWm hN hF U).aestronglyMeasurable)
      (fun U => ae_of_all _ fun V => ?_) (integrable_const _) (ae_of_all _ fun V => ?_)
    · have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC U)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (hC _) (exp_neg_bounds hN _).2 (Real.exp_pos _).le hC0
    · exact (hFc.comp (hc V)).mul (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (hWc.comp (hc V)).neg))
  have hden : Continuous (kernelDenominator 𝓛 h W) := by
    refine continuous_of_dominated (bound := fun _ => Real.exp N)
      (fun U => (integrable_boltzmann hm hWm hN U).aestronglyMeasurable)
      (fun U => ae_of_all _ fun V => ?_) (integrable_const _) (ae_of_all _ fun V => ?_)
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (exp_neg_bounds hN _).2
    · exact Real.continuous_exp.comp (hWc.comp (hc V)).neg
  refine hnum.div (Complex.continuous_ofReal.comp hden) fun U => ?_
  exact Complex.ofReal_ne_zero.mpr (kernelDenominator_pos hm hWm hN U).ne'
end FixedSet
theorem borelProb_ext (μ μ' : BorelProb a)
    (hμ : ∀ F : GaugeField a → ℂ, IsBoundedObservable F → μ.integral F = μ'.integral F) :
    μ = μ' := by
  have hprob : IsProbabilityMeasure (μ.1 : Measure (GaugeField a)) := μ.2
  have hprob' : IsProbabilityMeasure (μ'.1 : Measure (GaugeField a)) := μ'.2
  have hmeas : (μ.1 : Measure (GaugeField a)) = μ'.1 := by
    refine Measure.ext fun B hB => ?_
    have hobs : IsBoundedObservable (B.indicator fun _ => (1 : ℂ)) := by
      refine ⟨measurable_const.indicator hB, 1, fun U => ?_⟩
      by_cases hU : U ∈ B <;> simp [hU]
    have e := hμ _ hobs
    change ∫ U, B.indicator (fun _ => (1 : ℂ)) U ∂μ.1 =
      ∫ U, B.indicator (fun _ => (1 : ℂ)) U ∂μ'.1 at e
    rw [integral_indicator_const _ hB, integral_indicator_const _ hB] at e
    have e' : (μ.1 : Measure (GaugeField a)).real B = (μ'.1 : Measure (GaugeField a)).real B := by
      simpa using e
    exact (measureReal_eq_measureReal_iff).mp e'
  exact Subtype.ext hmeas
section Pushforward
variable {𝓛 : Finset (Link a)} {h : HasNoOppositePairs (𝓛 : Set (Link a))}
  {W : GaugeField a → ℝ} {N : ℝ}
theorem existsUnique_composition (hm : JointlyMeasurable h) (hWm : Measurable W)
    (hN : ∀ U, |W U| ≤ N) (ν : BorelProb a) :
    ∃! μ : BorelProb a, ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      μ.integral F = ν.integral (linkKernel 𝓛 h W F) := by
  have hν : IsProbabilityMeasure (ν.1 : Measure (GaugeField a)) := ν.2
  set ν₀ : Measure (GaugeField a) := ν.1 with hν₀
  set P := LinkVariables.haarMeasure (𝓛 : Set (Link a)) with hP
  let dens : GaugeField a × LinkVariables (𝓛 : Set (Link a)) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (boltzmannDensity h W q.1 q.2)
  have hd : Measurable fun q : GaugeField a × LinkVariables (𝓛 : Set (Link a)) =>
      boltzmannDensity h W q.1 q.2 :=
    (Real.measurable_exp.comp (hWm.comp hm).neg).div
      ((measurable_kernelDenominator (h := h) hm hWm).comp measurable_fst)
  have hdens : Measurable dens := ENNReal.measurable_ofReal.comp hd
  let ρ := (ν₀.prod P).withDensity dens
  let μ₀ : Measure (GaugeField a) := ρ.map fun q => overwriteLinks h q.2 q.1
  have hone : ∀ U, ∫⁻ V, dens (U, V) ∂P = 1 := by
    intro U
    have := ofReal_integral_eq_lintegral_ofReal
      (integrable_boltzmannDensity (h := h) hm hWm hN U)
      (ae_of_all _ fun V => (boltzmannDensity_pos hm hWm hN U V).le)
    rw [integral_boltzmannDensity hm hWm hN, ENNReal.ofReal_one] at this
    exact this.symm
  have hprob : IsProbabilityMeasure μ₀ := by
    constructor
    change (ρ.map fun q => overwriteLinks h q.2 q.1) univ = 1
    rw [Measure.map_apply hm MeasurableSet.univ, preimage_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_prod _ hdens.aemeasurable, lintegral_congr hone]
    simp
  have hint : ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      ∫ U, F U ∂μ₀ = ∫ U, linkKernel 𝓛 h W F U ∂ν₀ := by
    intro F hF
    have hfin : Integrable (fun q : GaugeField a × LinkVariables (𝓛 : Set (Link a)) =>
        (dens q).toReal • F (overwriteLinks h q.2 q.1)) (ν₀.prod P) := by
      obtain ⟨C, hC⟩ := hF.2
      refine Integrable.of_bound (C := Real.exp N / Real.exp (-N) * C) ?_
        (ae_of_all _ fun q => ?_)
      · exact ((hdens.ennreal_toReal).smul (hF.1.comp hm)).aestronglyMeasurable
      · have hpos := boltzmannDensity_pos (h := h) hm hWm hN q.1 q.2
        simp only [dens]
        rw [ENNReal.toReal_ofReal hpos.le, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
        refine mul_le_mul ?_ (hC _) (norm_nonneg _) (by positivity)
        exact div_le_div₀ (Real.exp_pos _).le (exp_neg_bounds hN _).2 (Real.exp_pos _)
          (exp_neg_le_kernelDenominator hm hWm hN q.1)
    change ∫ U, F U ∂(ρ.map fun q => overwriteLinks h q.2 q.1) = _
    rw [integral_map hm.aemeasurable hF.1.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hdens
        (ae_of_all _ fun q => ENNReal.ofReal_lt_top),
      integral_prod _ hfin]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    rw [linkKernel_eq_integral_density]
    refine integral_congr_ae (ae_of_all _ fun V => ?_)
    have hpos := boltzmannDensity_pos (h := h) hm hWm hN U V
    simp only [dens]
    rw [ENNReal.toReal_ofReal hpos.le, Complex.real_smul, mul_comm]
  let μ : BorelProb a := ⟨μ₀, hprob⟩
  have hμ : ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      μ.integral F = ν.integral (linkKernel 𝓛 h W F) := hint
  refine ⟨μ, hμ, fun μ' hμ' => borelProb_ext _ _ fun F hF => ?_⟩
  rw [hμ' F hF, hμ F hF]
end Pushforward
theorem div_le_div_mul_div {x y X Y c d : ℝ} (hX : 0 < X) (hY : 0 < Y) (hd : 0 < d)
    (hc : 0 ≤ c) (hy : 0 ≤ y) (hx : x ≤ c * y) (hXY : d * Y ≤ X) :
    x / X ≤ c / d * (y / Y) := by
  rw [div_le_iff₀ hX]
  have h0 : 0 ≤ c / d * (y / Y) := by positivity
  calc x ≤ c * y := hx
    _ = c / d * (y / Y) * (d * Y) := by field_simp
    _ ≤ c / d * (y / Y) * X := mul_le_mul_of_nonneg_left hXY h0
section Comparison
variable {𝓛 : Finset (Link a)} {h : HasNoOppositePairs (𝓛 : Set (Link a))}
  {W W' : GaugeField a → ℝ} {N N' : ℝ}
theorem boltzmannDensity_ratio_bounds (hm : JointlyMeasurable h) (hWm : Measurable W)
    (hW'm : Measurable W') (hN : ∀ U, |W U| ≤ N) (hN' : ∀ U, |W' U| ≤ N') (U : GaugeField a)
    (V : LinkVariables (𝓛 : Set (Link a))) :
    boltzmannDensity h W U V ≤
        Real.exp (oscillation fun U => W U - W' U) * boltzmannDensity h W' U V ∧
      boltzmannDensity h W' U V ≤
        Real.exp (oscillation fun U => W U - W' U) * boltzmannDensity h W U V := by
  set D : GaugeField a → ℝ := fun U => W U - W' U with hD
  have hbd : ∀ U, |D U| ≤ N + N' := fun U =>
    (abs_sub _ _).trans (add_le_add (hN U) (hN' U))
  have hup : BddAbove (range D) :=
    ⟨N + N', by rintro _ ⟨U, rfl⟩; exact (abs_le.mp (hbd U)).2⟩
  have hlo : BddBelow (range D) :=
    ⟨-(N + N'), by rintro _ ⟨U, rfl⟩; exact (abs_le.mp (hbd U)).1⟩
  set s₁ := ⨆ U, D U with hs₁
  set s₀ := ⨅ U, D U with hs₀
  have h1 : ∀ U, D U ≤ s₁ := fun U => le_ciSup hup U
  have h0 : ∀ U, s₀ ≤ D U := fun U => ciInf_le hlo U
  have hosc : oscillation D = s₁ - s₀ := rfl
  rw [hosc]
  have hw1 : ∀ V : LinkVariables (𝓛 : Set (Link a)), Real.exp (-W (overwriteLinks h V U)) ≤
      Real.exp (-s₀) * Real.exp (-W' (overwriteLinks h V U)) := fun V => by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr
      (by have := h0 (overwriteLinks h V U); simp only [hD] at this; linarith)
  have hw2 : ∀ V : LinkVariables (𝓛 : Set (Link a)), Real.exp (-W' (overwriteLinks h V U)) ≤
      Real.exp s₁ * Real.exp (-W (overwriteLinks h V U)) := fun V => by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr
      (by have := h1 (overwriteLinks h V U); simp only [hD] at this; linarith)
  have hZ1 : Real.exp (-s₁) * kernelDenominator 𝓛 h W' U ≤ kernelDenominator 𝓛 h W U := by
    have e : kernelDenominator 𝓛 h W' U ≤ Real.exp s₁ * kernelDenominator 𝓛 h W U := by
      simp only [kernelDenominator]
      rw [← integral_const_mul]
      exact integral_mono (integrable_boltzmann hm hW'm hN' U)
        ((integrable_boltzmann hm hWm hN U).const_mul _) hw2
    have hE : Real.exp (-s₁) * Real.exp s₁ = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp (-s₁) * kernelDenominator 𝓛 h W' U
        ≤ Real.exp (-s₁) * (Real.exp s₁ * kernelDenominator 𝓛 h W U) :=
          mul_le_mul_of_nonneg_left e (Real.exp_pos _).le
      _ = kernelDenominator 𝓛 h W U := by rw [← mul_assoc, hE, one_mul]
  have hZ2 : Real.exp s₀ * kernelDenominator 𝓛 h W U ≤ kernelDenominator 𝓛 h W' U := by
    have e : kernelDenominator 𝓛 h W U ≤ Real.exp (-s₀) * kernelDenominator 𝓛 h W' U := by
      simp only [kernelDenominator]
      rw [← integral_const_mul]
      exact integral_mono (integrable_boltzmann hm hWm hN U)
        ((integrable_boltzmann hm hW'm hN' U).const_mul _) hw1
    have hE : Real.exp s₀ * Real.exp (-s₀) = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp s₀ * kernelDenominator 𝓛 h W U
        ≤ Real.exp s₀ * (Real.exp (-s₀) * kernelDenominator 𝓛 h W' U) :=
          mul_le_mul_of_nonneg_left e (Real.exp_pos _).le
      _ = kernelDenominator 𝓛 h W' U := by rw [← mul_assoc, hE, one_mul]
  have hZ := kernelDenominator_pos (h := h) hm hWm hN U
  have hZ' := kernelDenominator_pos (h := h) hm hW'm hN' U
  constructor
  · have := div_le_div_mul_div hZ hZ' (Real.exp_pos (-s₁)) (Real.exp_pos (-s₀)).le
      (Real.exp_pos (-W' (overwriteLinks h V U))).le (hw1 V) hZ1
    rwa [← Real.exp_sub, neg_sub_neg] at this
  · have := div_le_div_mul_div hZ' hZ (Real.exp_pos s₀) (Real.exp_pos s₁).le
      (Real.exp_pos (-W (overwriteLinks h V U))).le (hw2 V) hZ2
    rwa [← Real.exp_sub] at this
theorem oscillation_sub_nonneg (hN : ∀ U, |W U| ≤ N) (hN' : ∀ U, |W' U| ≤ N') :
    0 ≤ oscillation fun U => W U - W' U := by
  have hbd : ∀ U, |W U - W' U| ≤ N + N' := fun U =>
    (abs_sub _ _).trans (add_le_add (hN U) (hN' U))
  have hup : BddAbove (range fun U => W U - W' U) :=
    ⟨N + N', by rintro _ ⟨U, rfl⟩; exact (abs_le.mp (hbd U)).2⟩
  have hlo : BddBelow (range fun U => W U - W' U) :=
    ⟨-(N + N'), by rintro _ ⟨U, rfl⟩; exact (abs_le.mp (hbd U)).1⟩
  have h1 := le_ciSup hup (trivialField a)
  have h0 := ciInf_le hlo (trivialField a)
  exact sub_nonneg.mpr (h0.trans h1)
theorem norm_linkKernel_sub_le (hm : JointlyMeasurable h) (hWm : Measurable W)
    (hW'm : Measurable W') (hN : ∀ U, |W U| ≤ N) (hN' : ∀ U, |W' U| ≤ N')
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) (U : GaugeField a) :
    ‖linkKernel 𝓛 h W F U - linkKernel 𝓛 h W' F U‖ ≤
      observableSupNorm F * (Real.exp (oscillation fun U => W U - W' U) - 1) := by
  set t := Real.exp (oscillation fun U => W U - W' U) with ht
  have ht0 : 0 < t := Real.exp_pos _
  rw [linkKernel_eq_integral_density, linkKernel_eq_integral_density,
    ← integral_sub (integrable_mul_boltzmannDensity hm hWm hN hF U)
      (integrable_mul_boltzmannDensity hm hW'm hN' hF U)]
  have hb : ∀ V : LinkVariables (𝓛 : Set (Link a)),
      |boltzmannDensity h W U V - boltzmannDensity h W' U V| ≤
        (t - 1) * boltzmannDensity h W' U V := by
    intro V
    obtain ⟨h1, h2⟩ := boltzmannDensity_ratio_bounds hm hWm hW'm hN hN' U V
    rw [← ht] at h1 h2
    have hp := boltzmannDensity_pos (h := h) hm hW'm hN' U V
    have h3 : 2 - t ≤ 1 / t := by
      rw [le_div_iff₀ ht0]
      nlinarith [sq_nonneg (t - 1)]
    have h4 : boltzmannDensity h W' U V * (1 / t) ≤ boltzmannDensity h W U V := by
      rw [mul_one_div, div_le_iff₀ ht0]
      linarith
    have h5 : boltzmannDensity h W' U V * (2 - t) ≤ boltzmannDensity h W' U V * (1 / t) :=
      mul_le_mul_of_nonneg_left h3 hp.le
    rw [abs_le]
    constructor <;> nlinarith
  have h1 := norm_integral_le_of_norm_le
    (μ := LinkVariables.haarMeasure (𝓛 : Set (Link a)))
    (f := fun V => F (overwriteLinks h V U) * (boltzmannDensity h W U V : ℂ) -
      F (overwriteLinks h V U) * (boltzmannDensity h W' U V : ℂ))
    (((integrable_boltzmannDensity (h := h) hm hW'm hN' U).const_mul (t - 1)).const_mul
      (observableSupNorm F))
    (ae_of_all _ fun V => by
      rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (norm_le_supNorm hF.2 _) (hb V) (abs_nonneg _)
        (supNorm_nonneg F))
  rwa [integral_const_mul, integral_const_mul, integral_boltzmannDensity hm hW'm hN',
    mul_one] at h1
theorem linkKernel_eq_of_independent (hD : IsIndependentOfLinks h fun U => W U - W' U)
    (F : GaugeField a → ℂ) : linkKernel 𝓛 h W F = linkKernel 𝓛 h W' F := by
  funext U
  have e : ∀ V : LinkVariables (𝓛 : Set (Link a)), Real.exp (-W (overwriteLinks h V U)) =
      Real.exp (-W' (overwriteLinks h V U)) * Real.exp (-(W U - W' U)) := fun V => by
    have hd : W (overwriteLinks h V U) - W' (overwriteLinks h V U) = W U - W' U := hD V U
    rw [← Real.exp_add]
    congr 1
    linarith
  have hc : ((Real.exp (-(W U - W' U)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have num : ∫ V, F (overwriteLinks h V U) * (Real.exp (-W (overwriteLinks h V U)) : ℂ)
        ∂LinkVariables.haarMeasure (𝓛 : Set (Link a)) =
      (∫ V, F (overwriteLinks h V U) * (Real.exp (-W' (overwriteLinks h V U)) : ℂ)
        ∂LinkVariables.haarMeasure (𝓛 : Set (Link a))) *
          ((Real.exp (-(W U - W' U)) : ℝ) : ℂ) := by
    rw [← integral_mul_const]
    congr 1
    funext V
    rw [e V, Complex.ofReal_mul, mul_assoc]
  have den : ∫ V, Real.exp (-W (overwriteLinks h V U))
        ∂LinkVariables.haarMeasure (𝓛 : Set (Link a)) =
      (∫ V, Real.exp (-W' (overwriteLinks h V U))
        ∂LinkVariables.haarMeasure (𝓛 : Set (Link a))) * Real.exp (-(W U - W' U)) := by
    rw [← integral_mul_const]
    exact integral_congr_ae (ae_of_all _ e)
  simp only [linkKernel]
  rw [num, den, Complex.ofReal_mul, mul_div_mul_right _ _ hc]
end Comparison
section Reorientation
variable {𝓛 𝓛' : Finset (Link a)}
theorem mem_reoriented_iff {R : Set (Link a)}
    (hL : (𝓛' : Set (Link a)) = ((𝓛 : Set (Link a)) \ R) ∪ Link.opposite '' R) (b : Link a) :
    (b ∈ (𝓛' : Set (Link a)) ↔ (b ∈ (𝓛 : Set (Link a)) ∧ b ∉ R) ∨ b.opposite ∈ R) := by
  rw [hL]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨c, hc, rfl⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr hc
  · rintro (⟨h1, h2⟩ | h1)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨b.opposite, h1, rfl⟩
theorem hasNoOppositePairs_reoriented (h : HasNoOppositePairs (𝓛 : Set (Link a)))
    {R : Set (Link a)} (hR : R ⊆ (𝓛 : Set (Link a)))
    (hL : (𝓛' : Set (Link a)) = ((𝓛 : Set (Link a)) \ R) ∪ Link.opposite '' R) :
    HasNoOppositePairs (𝓛' : Set (Link a)) := by
  intro b hb hr
  have f := fun c => mem_reoriented_iff hL c
  rcases (f b).mp hb with ⟨h1, h2⟩ | h1 <;> rcases (f b.opposite).mp hr with ⟨h3, h4⟩ | h3
  · exact h b h1 h3
  · exact h2 h3
  · exact h4 h1
  · exact h _ (hR h1) (hR h3)
theorem mem_or_opposite_mem_reoriented_iff (h : HasNoOppositePairs (𝓛 : Set (Link a)))
    {R : Set (Link a)} (hR : R ⊆ (𝓛 : Set (Link a)))
    (hL : (𝓛' : Set (Link a)) = ((𝓛 : Set (Link a)) \ R) ∪ Link.opposite '' R) (b : Link a) :
    (b ∈ 𝓛' ∨ b.opposite ∈ 𝓛') ↔ (b ∈ 𝓛 ∨ b.opposite ∈ 𝓛) := by
  have f := fun c => mem_reoriented_iff hL c
  have hc : ∀ c : Link a, c ∈ 𝓛 ↔ c ∈ (𝓛 : Set (Link a)) := fun c => Finset.mem_coe.symm
  have hc' : ∀ c : Link a, c ∈ 𝓛' ↔ c ∈ (𝓛' : Set (Link a)) := fun c => Finset.mem_coe.symm
  rw [hc, hc, hc', hc', f b, f b.opposite, Link.opposite_opposite]
  constructor
  · rintro ((⟨h1, -⟩ | h1) | (⟨h1, -⟩ | h1))
    · exact Or.inl h1
    · exact Or.inr (hR h1)
    · exact Or.inr h1
    · exact Or.inl (hR h1)
  · rintro (h1 | h1)
    · by_cases h2 : b ∈ R
      · exact Or.inr (Or.inr h2)
      · exact Or.inl (Or.inl ⟨h1, h2⟩)
    · by_cases h2 : b.opposite ∈ R
      · exact Or.inl (Or.inr h2)
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
theorem plaquettesTouching_reoriented (h : HasNoOppositePairs (𝓛 : Set (Link a)))
    {R : Set (Link a)} (hR : R ⊆ (𝓛 : Set (Link a)))
    (hL : (𝓛' : Set (Link a)) = ((𝓛 : Set (Link a)) \ R) ∪ Link.opposite '' R) :
    plaquettesTouching 𝓛' = plaquettesTouching 𝓛 := by
  ext p
  simp only [plaquettesTouching, mem_ofPred_eq, mem_or_opposite_mem_reoriented_iff h hR hL]
open Classical in
def reorientLink (h : HasNoOppositePairs (𝓛 : Set (Link a))) {R : Set (Link a)}
    (hR : R ⊆ (𝓛 : Set (Link a)))
    (hL : (𝓛' : Set (Link a)) = ((𝓛 : Set (Link a)) \ R) ∪ Link.opposite '' R)
    (b : (𝓛 : Set (Link a))) : (𝓛' : Set (Link a)) :=
  if hb : b.1 ∈ R then
    ⟨b.1.opposite, (mem_reoriented_iff hL _).mpr (Or.inr hb)⟩
  else ⟨b.1, (mem_reoriented_iff hL _).mpr (Or.inl ⟨b.2, hb⟩)⟩
theorem reorientLink_bijective (h : HasNoOppositePairs (𝓛 : Set (Link a)))
    {R : Set (Link a)} (hR : R ⊆ (𝓛 : Set (Link a)))
    (hL : (𝓛' : Set (Link a)) = ((𝓛 : Set (Link a)) \ R) ∪ Link.opposite '' R) :
    Function.Bijective (reorientLink h hR hL) := by
  constructor
  · rintro ⟨b, hb⟩ ⟨c, hc⟩ e
    have e' := congrArg Subtype.val e
    simp only [reorientLink] at e'
    apply Subtype.ext
    by_cases h1 : b ∈ R <;> by_cases h2 : c ∈ R
    · simp only [dif_pos h1, dif_pos h2] at e'
      exact congrArg Link.opposite e'
    · simp only [dif_pos h1, dif_neg h2] at e'
      exact absurd (e' ▸ hc) (h b hb)
    · simp only [dif_neg h1, dif_pos h2] at e'
      exact absurd (e' ▸ hb) (h c hc)
    · simpa only [dif_neg h1, dif_neg h2] using e'
  · rintro ⟨c, hc⟩
    rcases (mem_reoriented_iff hL c).mp hc with ⟨h1, h2⟩ | h1
    · refine ⟨⟨c, h1⟩, Subtype.ext ?_⟩
      simp only [reorientLink, dif_neg h2]
    · refine ⟨⟨c.opposite, hR h1⟩, Subtype.ext ?_⟩
      simp only [reorientLink, dif_pos h1]
      rfl
def reorientLinkEquiv (h : HasNoOppositePairs (𝓛 : Set (Link a))) {R : Set (Link a)}
    (hR : R ⊆ (𝓛 : Set (Link a)))
    (hL : (𝓛' : Set (Link a)) = ((𝓛 : Set (Link a)) \ R) ∪ Link.opposite '' R) :
    (𝓛 : Set (Link a)) ≃ (𝓛' : Set (Link a)) :=
  Equiv.ofBijective _ (reorientLink_bijective h hR hL)
open Classical in
def invertOn (R : Set (Link a)) (b : (𝓛 : Set (Link a)))
    (g : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2.specialUnitary :=
  if b.1 ∈ R then g⁻¹ else g
theorem invertOn_invertOn (R : Set (Link a)) (b : (𝓛 : Set (Link a)))
    (g : Matrices.ComplexMatrix2.specialUnitary) : invertOn R b (invertOn R b g) = g := by
  by_cases hb : b.1 ∈ R <;> simp [invertOn, hb]
theorem measurable_invertOn (R : Set (Link a)) (b : (𝓛 : Set (Link a))) :
    Measurable (invertOn (𝓛 := 𝓛) R b) := by
  by_cases hb : b.1 ∈ R
  · have e : invertOn (𝓛 := 𝓛) R b = fun g => g⁻¹ := by
      funext g
      simp [invertOn, hb]
    rw [e]
    exact continuous_inv.measurable
  · have e : invertOn (𝓛 := 𝓛) R b = fun g => g := by
      funext g
      simp [invertOn, hb]
    rw [e]
    exact measurable_id
def invertOnEquiv (R : Set (Link a)) :
    LinkVariables (𝓛 : Set (Link a)) ≃ᵐ LinkVariables (𝓛 : Set (Link a)) where
  toFun V b := invertOn R b (V b)
  invFun V b := invertOn R b (V b)
  left_inv V := funext fun b => invertOn_invertOn R b (V b)
  right_inv V := funext fun b => invertOn_invertOn R b (V b)
  measurable_toFun := measurable_pi_lambda _ fun b =>
    (measurable_invertOn R b).comp (measurable_pi_apply b)
  measurable_invFun := measurable_pi_lambda _ fun b =>
    (measurable_invertOn R b).comp (measurable_pi_apply b)
def reorientVariables (h : HasNoOppositePairs (𝓛 : Set (Link a))) {R : Set (Link a)}
    (hR : R ⊆ (𝓛 : Set (Link a)))
    (hL : (𝓛' : Set (Link a)) = ((𝓛 : Set (Link a)) \ R) ∪ Link.opposite '' R) :
    LinkVariables (𝓛 : Set (Link a)) ≃ᵐ LinkVariables (𝓛' : Set (Link a)) :=
  (invertOnEquiv R).trans
    (MeasurableEquiv.piCongrLeft (fun _ => Matrices.ComplexMatrix2.specialUnitary)
      (reorientLinkEquiv h hR hL))
theorem reorientVariables_reorientLink (h : HasNoOppositePairs (𝓛 : Set (Link a)))
    {R : Set (Link a)} (hR : R ⊆ (𝓛 : Set (Link a)))
    (hL : (𝓛' : Set (Link a)) = ((𝓛 : Set (Link a)) \ R) ∪ Link.opposite '' R)
    (V : LinkVariables (𝓛 : Set (Link a))) (b : (𝓛 : Set (Link a))) :
    reorientVariables h hR hL V (reorientLink h hR hL b) = invertOn R b (V b) :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => Matrices.ComplexMatrix2.specialUnitary)
    (reorientLinkEquiv h hR hL) (invertOnEquiv R V) b
theorem measurePreserving_reorientVariables
    (hinv : Measure.map (fun U : Matrices.ComplexMatrix2.specialUnitary => U⁻¹)
      Matrices.ComplexMatrix2.haarProb = Matrices.ComplexMatrix2.haarProb)
    (h : HasNoOppositePairs (𝓛 : Set (Link a))) {R : Set (Link a)}
    (hR : R ⊆ (𝓛 : Set (Link a)))
    (hL : (𝓛' : Set (Link a)) = ((𝓛 : Set (Link a)) \ R) ∪ Link.opposite '' R) :
    MeasurePreserving (reorientVariables h hR hL) (LinkVariables.haarMeasure (𝓛 : Set (Link a)))
      (LinkVariables.haarMeasure (𝓛' : Set (Link a))) := by
  refine ⟨(reorientVariables h hR hL).measurable, ?_⟩
  have h1 : Measure.map (invertOnEquiv (𝓛 := 𝓛) R)
      (LinkVariables.haarMeasure (𝓛 : Set (Link a))) =
      LinkVariables.haarMeasure (𝓛 : Set (Link a)) := by
    have e := Measure.infinitePi_map_pi
      (X := fun _ : (𝓛 : Set (Link a)) => Matrices.ComplexMatrix2.specialUnitary)
      (μ := fun _ => Matrices.ComplexMatrix2.haarProb) (f := fun b => invertOn (𝓛 := 𝓛) R b)
      (fun b => measurable_invertOn R b)
    have e2 : ∀ b : (𝓛 : Set (Link a)),
        Measure.map (invertOn (𝓛 := 𝓛) R b) Matrices.ComplexMatrix2.haarProb =
          Matrices.ComplexMatrix2.haarProb := by
      intro b
      by_cases hb : b.1 ∈ R
      · have e3 : invertOn (𝓛 := 𝓛) R b = fun g => g⁻¹ := by
          funext g
          simp [invertOn, hb]
        rw [e3, hinv]
      · have e3 : invertOn (𝓛 := 𝓛) R b = id := by
          funext g
          simp [invertOn, hb]
        rw [e3, Measure.map_id]
    simp only [e2] at e
    exact e
  have h2 := Measure.infinitePi_map_piCongrLeft
    (X := fun _ : (𝓛' : Set (Link a)) => Matrices.ComplexMatrix2.specialUnitary)
    (fun _ => Matrices.ComplexMatrix2.haarProb) (reorientLinkEquiv h hR hL)
  have h3 : (reorientVariables h hR hL : LinkVariables (𝓛 : Set (Link a)) → _) =
      (MeasurableEquiv.piCongrLeft (fun _ => Matrices.ComplexMatrix2.specialUnitary)
        (reorientLinkEquiv h hR hL)) ∘ (invertOnEquiv (𝓛 := 𝓛) R) := rfl
  rw [h3, ← Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _), h1]
  exact h2
theorem overwriteLinks_reorientVariables (h : HasNoOppositePairs (𝓛 : Set (Link a)))
    (h' : HasNoOppositePairs (𝓛' : Set (Link a))) {R : Set (Link a)}
    (hR : R ⊆ (𝓛 : Set (Link a)))
    (hL : (𝓛' : Set (Link a)) = ((𝓛 : Set (Link a)) \ R) ∪ Link.opposite '' R)
    (V : LinkVariables (𝓛 : Set (Link a))) (U : GaugeField a) :
    overwriteLinks h' (reorientVariables h hR hL V) U = overwriteLinks h V U := by
  have f := fun c => mem_reoriented_iff hL c
  have hT := reorientVariables_reorientLink h hR hL V
  apply Subtype.ext
  funext c
  change (overwriteLinks h' (reorientVariables h hR hL V) U) c = (overwriteLinks h V U) c
  by_cases hc : c ∈ (𝓛 : Set (Link a))
  · rw [overwriteLinks_apply_of_mem V U hc]
    by_cases hcR : c ∈ R
    · have h1 : c.opposite ∈ (𝓛' : Set (Link a)) := (f _).mpr (Or.inr hcR)
      have h2 : c ∉ (𝓛' : Set (Link a)) := fun h3 => h' _ h3 h1
      rw [overwriteLinks_apply_of_opposite_mem _ U h2 h1]
      have e : (⟨c.opposite, h1⟩ : (𝓛' : Set (Link a))) = reorientLink h hR hL ⟨c, hc⟩ := by
        apply Subtype.ext
        simp only [reorientLink, dif_pos hcR]
      rw [e, hT]
      simp [invertOn, hcR]
    · have h1 : c ∈ (𝓛' : Set (Link a)) := (f c).mpr (Or.inl ⟨hc, hcR⟩)
      rw [overwriteLinks_apply_of_mem _ U h1]
      have e : (⟨c, h1⟩ : (𝓛' : Set (Link a))) = reorientLink h hR hL ⟨c, hc⟩ := by
        apply Subtype.ext
        simp only [reorientLink, dif_neg hcR]
      rw [e, hT]
      simp [invertOn, hcR]
  · by_cases hr : c.opposite ∈ (𝓛 : Set (Link a))
    · rw [overwriteLinks_apply_of_opposite_mem V U hc hr]
      by_cases hrR : c.opposite ∈ R
      · have h1 : c ∈ (𝓛' : Set (Link a)) := (f c).mpr (Or.inr hrR)
        rw [overwriteLinks_apply_of_mem _ U h1]
        have e : (⟨c, h1⟩ : (𝓛' : Set (Link a))) =
            reorientLink h hR hL ⟨c.opposite, hr⟩ := by
          apply Subtype.ext
          simp only [reorientLink, dif_pos hrR]
          rfl
        rw [e, hT]
        simp [invertOn, hrR]
      · have h1 : c.opposite ∈ (𝓛' : Set (Link a)) := (f _).mpr (Or.inl ⟨hr, hrR⟩)
        have h2 : c ∉ (𝓛' : Set (Link a)) := fun h3 => h' _ h3 h1
        rw [overwriteLinks_apply_of_opposite_mem _ U h2 h1]
        have e : (⟨c.opposite, h1⟩ : (𝓛' : Set (Link a))) =
            reorientLink h hR hL ⟨c.opposite, hr⟩ := by
          apply Subtype.ext
          simp only [reorientLink, dif_neg hrR]
        rw [e, hT]
        simp [invertOn, hrR]
    · have h1 : c ∉ (𝓛' : Set (Link a)) := fun h3 => by
        rcases (f c).mp h3 with ⟨h4, -⟩ | h4
        · exact hc h4
        · exact hr (hR h4)
      have h2 : c.opposite ∉ (𝓛' : Set (Link a)) := fun h3 => by
        rcases (f _).mp h3 with ⟨h4, -⟩ | h4
        · exact hr h4
        · exact hc (hR h4)
      rw [overwriteLinks_apply_of_not_mem V U hc hr, overwriteLinks_apply_of_not_mem _ U h1 h2]
theorem linkKernel_reoriented
    (hinv : Measure.map (fun U : Matrices.ComplexMatrix2.specialUnitary => U⁻¹)
      Matrices.ComplexMatrix2.haarProb = Matrices.ComplexMatrix2.haarProb)
    (h : HasNoOppositePairs (𝓛 : Set (Link a)))
    (h' : HasNoOppositePairs (𝓛' : Set (Link a))) {R : Set (Link a)}
    (hR : R ⊆ (𝓛 : Set (Link a)))
    (hL : (𝓛' : Set (Link a)) = ((𝓛 : Set (Link a)) \ R) ∪ Link.opposite '' R)
    (W : GaugeField a → ℝ) (F : GaugeField a → ℂ) :
    linkKernel 𝓛' h' W F = linkKernel 𝓛 h W F := by
  funext U
  have hmp := measurePreserving_reorientVariables hinv h hR hL
  have e1 := hmp.integral_comp'
    (fun V' => F (overwriteLinks h' V' U) * (Real.exp (-W (overwriteLinks h' V' U)) : ℂ))
  have e2 := hmp.integral_comp' (fun V' => Real.exp (-W (overwriteLinks h' V' U)))
  simp only [overwriteLinks_reorientVariables h h' hR hL] at e1 e2
  simp only [linkKernel]
  rw [e1, e2]
end Reorientation
theorem dependsOnlyOnLinks_mono {E : Type*} {S T : Set (Link a)} {F : GaugeField a → E}
    (hST : S ⊆ T) (hF : DependsOnlyOnLinks S F) : DependsOnlyOnLinks T F :=
  fun U U' e => hF U U' (funext fun b => congrFun e ⟨b.1, hST b.2⟩)
theorem continuous_of_isRealLocalContinuous {W : GaugeField a → ℝ}
    (hW : IsRealLocalContinuous W) : Continuous W := by
  have := Complex.continuous_re.comp hW.1
  simpa [Function.comp_def] using this
theorem abs_le_supNorm_of_isRealLocalContinuous {W : GaugeField a → ℝ}
    (hW : IsRealLocalContinuous W) (U : GaugeField a) :
    |W U| ≤ observableSupNorm fun U' => (W U' : ℂ) := by
  have := norm_le_supNorm hW.2.1.2 U
  rwa [Complex.norm_real, Real.norm_eq_abs] at this
theorem linkKernelProperties_holds (hHaar : Matrices.ComplexMatrix2.HaarExpChartProperties)
    (hFactor : LinkFunctions.Assertion)
    (hTop : SpacesOfFieldsAndMeasures.FieldAndMeasureSpaceProperties) :
    LinkKernelProperties := by
  intro a ha 𝓛 h W W' hW hW'
  have hinv := hHaar.2.2.2
  obtain ⟨hConf, -, hLocal, -⟩ := hFactor a ha
  have hMet : TopologicalSpace.MetrizableSpace (GaugeField a) := (hTop a ha).1.2.2
  have hCont := hConf.2.1 (𝓛 : Set (Link a)) h
  have hm : JointlyMeasurable h := (hCont.comp continuous_swap).measurable
  have hc : ∀ V : LinkVariables (𝓛 : Set (Link a)), Continuous fun U => overwriteLinks h V U :=
    fun V => hCont.comp (continuous_const.prodMk continuous_id)
  have hWc := continuous_of_isRealLocalContinuous hW
  have hW'c := continuous_of_isRealLocalContinuous hW'
  have hWm : Measurable W := hWc.measurable
  have hW'm : Measurable W' := hW'c.measurable
  have hN := abs_le_supNorm_of_isRealLocalContinuous hW
  have hN' := abs_le_supNorm_of_isRealLocalContinuous hW'
  have hLocalIff := hLocal.2.2.1
  refine ⟨⟨fun F hF => ⟨fun U => ⟨integrable_kernelNumerator_integrand hm hWm hN hF U,
      integrable_boltzmann hm hWm hN U⟩, isBoundedObservable_kernelNumerator hm hWm hN hF,
      isBoundedObservable_kernelDenominator hm hWm hN, exp_neg_le_kernelDenominator hm hWm hN,
      isBoundedObservable_linkKernel hm hWm hN hF, isIndependentOfLinks_linkKernel F,
      fun hpos U => linkKernel_nonneg hm hWm hN hpos U, ?_⟩,
      fun c c' F F' hF hF' => linkKernel_linear hm hWm hN c c' hF hF', linkKernel_one hm hWm hN⟩,
    fun H F _ _ hH => linkKernel_mul_left hH F,
    ⟨fun S F _ _ hWS hFS => dependsOnlyOnLinks_linkKernel hWS hFS,
      fun F hF hFc => continuous_linkKernel hc hm hWc hN hF hFc, ?_⟩,
    fun ν => existsUnique_composition hm hWm hN ν,
    fun F hF => ?_,
    fun hD F _ => linkKernel_eq_of_independent hD F, ?_⟩
  · exact ciSup_le fun U => norm_linkKernel_le hm hWm hN hF U
  · rintro F ⟨hFc, hFo, hFl⟩
    obtain ⟨S₁, f₁, s₁, hS₁⟩ := (hLocalIff F hFo).mp hFl
    obtain ⟨S₂, f₂, s₂, hS₂⟩ := (hLocalIff _ hW.2.1).mp hW.2.2
    have hS₂' : DependsOnlyOnLinks S₂ W :=
      fun U U' e => Complex.ofReal_injective (hS₂ U U' e)
    have hobs := isBoundedObservable_linkKernel (h := h) hm hWm hN hFo
    exact ⟨continuous_linkKernel hc hm hWc hN hFo hFc, hobs, (hLocalIff _ hobs).mpr
      ⟨S₁ ∪ S₂, f₁.union f₂, union_subset s₁ s₂, dependsOnlyOnLinks_linkKernel
        (dependsOnlyOnLinks_mono subset_union_right hS₂')
        (dependsOnlyOnLinks_mono subset_union_left hS₁)⟩⟩
  · refine ciSup_le fun U => ?_
    exact norm_linkKernel_sub_le hm hWm hW'm hN hN' hF U
  · rintro 𝓛' ⟨R, hR, hL⟩
    have h' := hasNoOppositePairs_reoriented h hR hL
    refine ⟨h', fun F _ => linkKernel_reoriented hinv h h' hR hL W F,
      plaquettesTouching_reoriented h hR hL, fun β _ F _ => ?_⟩
    have e : wilsonLinkEnergy β 𝓛' = wilsonLinkEnergy β 𝓛 := by
      funext U
      simp only [wilsonLinkEnergy, plaquettesTouching_reoriented h hR hL]
    funext U
    simp only [wilsonLinkKernel]
    rw [e, linkKernel_reoriented hinv h h' hR hL]
end YangMills.Construction.GibbsAtFixedSpacing.LinkKernels

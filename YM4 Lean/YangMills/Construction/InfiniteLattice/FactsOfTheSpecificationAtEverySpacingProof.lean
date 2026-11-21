import YangMills.Construction.InfiniteLattice.ConfigurationsAreFamiliesOnTheBondsAtEverySpacing
import YangMills.Construction.InfiniteLattice.FactsOfThePlaquettesAtEverySpacing
import YangMills.Construction.InfiniteLattice.FactsOfTheSpecificationAtEverySpacing
import YangMills.Construction.InfiniteLattice.IntegralsOverFiniteProductsAreObservablesAtEverySpacing
import YangMills.Construction.InfiniteLattice.MeasurabilityIsDependenceOnVariablesAtEverySpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ComplexOrder NNReal ENNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice.WilsonKernelFacts
variable {a : ℝ}
theorem secondCountableTopology_specialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
  haveI : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _
attribute [local instance] secondCountableTopology_specialUnitary
theorem countable_link : Countable (Link a) := by
  have hs : Countable (LatticePoint a) :=
    Function.Surjective.countable
      (f := fun n : Fin 4 → ℤ => (⟨fun μ => (n μ : ℝ) * a, n, fun _ => rfl⟩ : LatticePoint a))
      fun x => by
        obtain ⟨n, hn⟩ := x.2
        exact ⟨n, Subtype.ext (funext fun μ => (hn μ).symm)⟩
  exact Function.Injective.countable (f := fun ℓ : Link a => (ℓ.initial, ℓ.terminal))
    fun ℓ ℓ' h => Link.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
attribute [local instance] countable_link
theorem secondCountableTopology_gaugeField : SecondCountableTopology (GaugeField a) :=
  TopologicalSpace.Subtype.secondCountableTopology
    {U : Link a → Matrices.ComplexMatrix2.specialUnitary | ∀ ℓ, U ℓ.opposite = (U ℓ)⁻¹}
attribute [local instance] secondCountableTopology_gaugeField
theorem nonempty_gaugeField : Nonempty (GaugeField a) :=
  ⟨⟨fun _ => 1, fun _ => by simp⟩⟩
theorem isProbabilityMeasure_haarProd (W : LinkWindow a) : IsProbabilityMeasure W.haarProd := by
  unfold LinkWindow.haarProd Matrices.ComplexMatrix2.haarPi
  infer_instance
attribute [local instance] isProbabilityMeasure_haarProd
theorem borel_prod_eq (W : LinkWindow a) :
    borel (W.Assignments × GaugeField a) = Prod.instMeasurableSpace :=
  BorelSpace.measurable_eq.symm
theorem norm_le_supNorm {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (U : GaugeField a) : ‖F U‖ ≤ observableSupNorm F := by
  obtain ⟨C, hC⟩ := hF.2
  exact le_ciSup (f := fun U => ‖F U‖) ⟨C, by rintro _ ⟨U, rfl⟩; exact hC U⟩ U
theorem isPositivelyOriented_or_opposite (ℓ : Link a) :
    ℓ.IsPositivelyOriented ∨ ℓ.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h | h⟩ := ℓ.isAdjacent
  · exact Or.inl ⟨μ, h⟩
  · refine Or.inr ⟨μ, ?_⟩
    change ℓ.initial - ℓ.terminal = axisStep a μ
    rw [← neg_sub, h, neg_neg]
theorem glue_apply_of_not_mem (W : LinkWindow a) (ha : 0 < a) (V : W.Assignments)
    (U : GaugeField a) {ℓ : Link a} (hℓ : ℓ.IsPositivelyOriented) (hm : ℓ ∉ W.links) :
    W.glue ha V U ℓ = U ℓ := by
  have hr : ℓ.opposite ∉ W.links := fun h =>
    Link.opposite_not_isPositivelyOriented ha hℓ (W.isPositive _ h)
  simp [LinkWindow.glue, hm, hr]
theorem glue_apply_congr (W : LinkWindow a) (ha : 0 < a) (V : W.Assignments)
    {U U' : GaugeField a} {ℓ : Link a} (hℓ : ℓ.IsPositivelyOriented)
    (h : ℓ ∉ W.links → U ℓ = U' ℓ) :
    W.glue ha V U ℓ = W.glue ha V U' ℓ := by
  by_cases hm : ℓ ∈ W.links
  · simp [LinkWindow.glue, hm]
  · rw [glue_apply_of_not_mem W ha V U hℓ hm, glue_apply_of_not_mem W ha V U' hℓ hm, h hm]
theorem glue_congr (W : LinkWindow a) (ha : 0 < a) (V : W.Assignments) {U U' : GaugeField a}
    (h : ∀ ℓ : Link a, ℓ.IsPositivelyOriented → ℓ ∉ W.links → U ℓ = U' ℓ) :
    W.glue ha V U = W.glue ha V U' := by
  apply Subtype.ext
  funext ℓ
  rcases isPositivelyOriented_or_opposite ℓ with hp | hp
  · exact glue_apply_congr W ha V hp (h ℓ hp)
  · have hopp := glue_apply_congr W ha V hp (h ℓ.opposite hp)
    have e₁ := (W.glue ha V U).2 ℓ
    have e₂ := (W.glue ha V U').2 ℓ
    have hopp' : (W.glue ha V U).1 ℓ.opposite = (W.glue ha V U').1 ℓ.opposite := hopp
    rw [e₁, e₂] at hopp'
    exact inv_injective hopp'
structure Hypotheses (ha : 0 < a) (β : ℝ) : Prop where
  beta_pos : 0 < β
  links : GaugeFieldsAreLinkFamilies ha
  faces : PlaquetteProperties a
  meas : MeasurableIffDependsOnly a
  integrals : FiniteHaarIntegralsBounded a
variable {ha : 0 < a} {β : ℝ}
theorem facesMeeting_finite (S : Hypotheses ha β) (W : LinkWindow a) :
    (facesMeeting (W.links : Set (Link a))).Finite :=
  S.faces.2.2.2.2.2 W
theorem continuous_faceEnergy (S : Hypotheses ha β) (p : ElementaryPlaquette a) :
    Continuous fun U : GaugeField a => faceEnergy U p := by
  have h := (S.faces.2.2.2.2.1 p).1.2.2
  have h' := Complex.continuous_re.comp h
  simpa [Function.comp_def] using h'
theorem localWeight_eq_exp (S : Hypotheses ha β) (W : LinkWindow a) (U : GaugeField a) :
    W.localWeight β U =
      Real.exp (-β * ∑ p ∈ (facesMeeting_finite S W).toFinset, faceEnergy U p) := by
  unfold LinkWindow.localWeight
  rw [finsum_mem_eq_finite_toFinset_sum _ (facesMeeting_finite S W)]
theorem continuous_localWeight (S : Hypotheses ha β) (W : LinkWindow a) :
    Continuous (W.localWeight β) := by
  have h : W.localWeight β = fun U : GaugeField a =>
      Real.exp (-β * ∑ p ∈ (facesMeeting_finite S W).toFinset, faceEnergy U p) :=
    funext (localWeight_eq_exp S W)
  rw [h]
  exact Real.continuous_exp.comp (continuous_const.mul
    (continuous_finsetSum _ fun p _ => continuous_faceEnergy S p))
theorem localWeight_pos (W : LinkWindow a) (U : GaugeField a) : 0 < W.localWeight β U :=
  Real.exp_pos _
theorem localWeight_le_one (S : Hypotheses ha β) (W : LinkWindow a) (U : GaugeField a) :
    W.localWeight β U ≤ 1 := by
  rw [localWeight_eq_exp S W, Real.exp_le_one_iff]
  have h : 0 ≤ ∑ p ∈ (facesMeeting_finite S W).toFinset, faceEnergy U p :=
    Finset.sum_nonneg fun p _ => (S.faces.1 p U).1
  nlinarith [S.beta_pos]
theorem exists_pos_le_localWeight (S : Hypotheses ha β) (W : LinkWindow a) :
    ∃ c : ℝ, 0 < c ∧ ∀ U, c ≤ W.localWeight β U := by
  refine ⟨Real.exp (-β * ∑ _p ∈ (facesMeeting_finite S W).toFinset, (2 : ℝ)), Real.exp_pos _,
    fun U => ?_⟩
  rw [localWeight_eq_exp S W, Real.exp_le_exp]
  have h : ∑ p ∈ (facesMeeting_finite S W).toFinset, faceEnergy U p ≤
      ∑ _p ∈ (facesMeeting_finite S W).toFinset, (2 : ℝ) :=
    Finset.sum_le_sum fun p _ => (S.faces.1 p U).2
  nlinarith [S.beta_pos]
theorem traceBoltzmannWeight_eq (S : Hypotheses ha β) (W : LinkWindow a) (U : GaugeField a) :
    W.traceBoltzmannWeight β U =
      Real.exp (β * ((facesMeeting (W.links : Set (Link a))).ncard : ℝ)) *
        W.localWeight β U := by
  rw [localWeight_eq_exp S W, ← Real.exp_add]
  unfold LinkWindow.traceBoltzmannWeight
  rw [finsum_mem_eq_finite_toFinset_sum _ (facesMeeting_finite S W)]
  congr 1
  rw [Set.ncard_eq_toFinset_card _ (facesMeeting_finite S W)]
  have h : ∀ p : ElementaryPlaquette a,
      (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
        (faceHolonomy U p : Matrices.ComplexMatrix2)).re = 1 - faceEnergy U p := fun p => by
    unfold faceEnergy
    ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  ring
theorem localWeight_congr (S : Hypotheses ha β) (W : LinkWindow a) {U U' : GaugeField a}
    (h : ∀ ℓ ∈ ⋃ p ∈ facesMeeting (W.links : Set (Link a)), p.linkSet, U ℓ = U' ℓ) :
    W.localWeight β U = W.localWeight β U' := by
  rw [localWeight_eq_exp S W, localWeight_eq_exp S W]
  congr 2
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p ∈ facesMeeting (W.links : Set (Link a)) := (Set.Finite.mem_toFinset _).mp hp
  have hdep := (S.faces.2.2.2.2.1 p).2 U U' fun ℓ hℓ => h ℓ (mem_iUnion₂.mpr ⟨p, hp', hℓ⟩)
  exact Complex.ofReal_injective hdep
def weightedIntegral (ha : 0 < a) (β : ℝ) (W : LinkWindow a) (F : GaugeField a → ℂ)
    (U : GaugeField a) : ℂ :=
  ∫ V, F (W.glue ha V U) * (W.localWeight β (W.glue ha V U) : ℂ) ∂W.haarProd
def partitionFunction (ha : 0 < a) (β : ℝ) (W : LinkWindow a) (U : GaugeField a) : ℝ :=
  ∫ V, W.localWeight β (W.glue ha V U) ∂W.haarProd
theorem conditionalExpectation_eq_div (W : LinkWindow a) (F : GaugeField a → ℂ)
    (U : GaugeField a) :
    W.conditionalExpectation ha β F U =
      weightedIntegral ha β W F U / (partitionFunction ha β W U : ℂ) := rfl
theorem continuous_glue (S : Hypotheses ha β) (W : LinkWindow a) :
    Continuous fun q : W.Assignments × GaugeField a => W.glue ha q.1 q.2 :=
  S.links.2.2 W
theorem measurable_glue_left (S : Hypotheses ha β) (W : LinkWindow a) (U : GaugeField a) :
    Measurable fun V : W.Assignments => W.glue ha V U :=
  ((continuous_glue S W).comp
    (by fun_prop : Continuous fun V : W.Assignments => (V, U))).measurable
theorem integrable_localWeight (S : Hypotheses ha β) (W : LinkWindow a) (U : GaugeField a) :
    Integrable (fun V => W.localWeight β (W.glue ha V U)) W.haarProd := by
  refine Integrable.of_bound
    ((continuous_localWeight S W).measurable.comp
      (measurable_glue_left S W U)).aestronglyMeasurable
    1 (ae_of_all _ fun V => ?_)
  rw [Real.norm_of_nonneg (localWeight_pos W _).le]
  exact localWeight_le_one S W _
theorem integrable_weightedIntegrand (S : Hypotheses ha β) (W : LinkWindow a)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) (U : GaugeField a) :
    Integrable (fun V => F (W.glue ha V U) * (W.localWeight β (W.glue ha V U) : ℂ))
      W.haarProd := by
  obtain ⟨C, hC⟩ := hF.2
  refine Integrable.of_bound
    ((hF.1.comp (measurable_glue_left S W U)).mul (Complex.measurable_ofReal.comp
      ((continuous_localWeight S W).measurable.comp
        (measurable_glue_left S W U)))).aestronglyMeasurable
    C (ae_of_all _ fun V => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (localWeight_pos W _).le]
  calc ‖F (W.glue ha V U)‖ * W.localWeight β (W.glue ha V U) ≤ C * 1 :=
        mul_le_mul (hC _) (localWeight_le_one S W _) (localWeight_pos W _).le
          ((norm_nonneg _).trans (hC U))
    _ = C := mul_one C
theorem exists_pos_le_partitionFunction (S : Hypotheses ha β) (W : LinkWindow a) :
    ∃ c : ℝ, 0 < c ∧ ∀ U, c ≤ partitionFunction ha β W U := by
  obtain ⟨c, hc, hw⟩ := exists_pos_le_localWeight S W
  refine ⟨c, hc, fun U => ?_⟩
  have h := integral_mono (integrable_const c) (integrable_localWeight S W U) fun V => hw _
  simpa [partitionFunction] using h
theorem partitionFunction_pos (S : Hypotheses ha β) (W : LinkWindow a) (U : GaugeField a) :
    0 < partitionFunction ha β W U := by
  obtain ⟨c, hc, h⟩ := exists_pos_le_partitionFunction S W
  exact hc.trans_le (h U)
theorem partitionFunction_ne_zero (S : Hypotheses ha β) (W : LinkWindow a)
    (U : GaugeField a) : ((partitionFunction ha β W U : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (partitionFunction_pos S W U).ne'
theorem weightedIntegral_one (W : LinkWindow a) (U : GaugeField a) :
    weightedIntegral ha β W (fun _ => 1) U = (partitionFunction ha β W U : ℂ) := by
  unfold weightedIntegral partitionFunction
  simp only [one_mul]
  exact integral_ofReal
theorem norm_weightedIntegral_le (S : Hypotheses ha β) (W : LinkWindow a)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) (U : GaugeField a) :
    ‖weightedIntegral ha β W F U‖ ≤ observableSupNorm F * partitionFunction ha β W U := by
  unfold partitionFunction
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrable_localWeight S W U).const_mul _)
    (ae_of_all _ fun V => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (localWeight_pos W _).le]
  exact mul_le_mul_of_nonneg_right (norm_le_supNorm hF _) (localWeight_pos W _).le
theorem norm_conditionalExpectation_le (S : Hypotheses ha β) (W : LinkWindow a)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) (U : GaugeField a) :
    ‖W.conditionalExpectation ha β F U‖ ≤ observableSupNorm F := by
  have hZ := partitionFunction_pos S W U
  rw [conditionalExpectation_eq_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le,
    div_le_iff₀ hZ]
  exact norm_weightedIntegral_le S W hF U
theorem measurable_weightedIntegrand (S : Hypotheses ha β) (W : LinkWindow a)
    {F : GaugeField a → ℂ} (hF : Measurable F) :
    Measurable fun q : W.Assignments × GaugeField a =>
      F (W.glue ha q.1 q.2) * (W.localWeight β (W.glue ha q.1 q.2) : ℂ) :=
  (hF.comp (continuous_glue S W).measurable).mul (Complex.measurable_ofReal.comp
    ((continuous_localWeight S W).measurable.comp (continuous_glue S W).measurable))
theorem norm_weightedIntegrand_le (S : Hypotheses ha β) (W : LinkWindow a)
    {F : GaugeField a → ℂ} {C : ℝ} (hC : ∀ U, ‖F U‖ ≤ C) (q : W.Assignments × GaugeField a) :
    ‖F (W.glue ha q.1 q.2) * (W.localWeight β (W.glue ha q.1 q.2) : ℂ)‖ ≤ C := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (localWeight_pos W _).le]
  calc ‖F (W.glue ha q.1 q.2)‖ * W.localWeight β (W.glue ha q.1 q.2) ≤ C * 1 :=
        mul_le_mul (hC _) (localWeight_le_one S W _) (localWeight_pos W _).le
          ((norm_nonneg _).trans (hC q.2))
    _ = C := mul_one C
theorem isBoundedObservable_weightedIntegral (S : Hypotheses ha β) (W : LinkWindow a)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable (weightedIntegral ha β W F) := by
  obtain ⟨C, hC⟩ := hF.2
  exact (S.integrals (↥W.links) _
    (by rw [borel_prod_eq]; exact measurable_weightedIntegrand S W hF.1)
    ⟨C, norm_weightedIntegrand_le S W hC⟩).1
theorem continuous_weightedIntegral (S : Hypotheses ha β) (W : LinkWindow a)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) (hc : Continuous F) :
    Continuous (weightedIntegral ha β W F) := by
  obtain ⟨C, hC⟩ := hF.2
  exact (S.integrals (↥W.links) _
    (by rw [borel_prod_eq]; exact measurable_weightedIntegrand S W hF.1)
    ⟨C, norm_weightedIntegrand_le S W hC⟩).2.2 ((hc.comp (continuous_glue S W)).mul
      (Complex.continuous_ofReal.comp ((continuous_localWeight S W).comp (continuous_glue S W))))
theorem isBoundedObservable_one : IsBoundedObservable (fun _ : GaugeField a => (1 : ℂ)) :=
  ⟨measurable_const, 1, fun _ => by simp⟩
theorem continuous_partitionFunction_complex (S : Hypotheses ha β) (W : LinkWindow a) :
    Continuous fun U => (partitionFunction ha β W U : ℂ) := by
  have h := continuous_weightedIntegral S W (isBoundedObservable_one (a := a)) continuous_const
  have e : weightedIntegral ha β W (fun _ => 1) = fun U => (partitionFunction ha β W U : ℂ) :=
    funext (weightedIntegral_one W)
  rwa [e] at h
theorem continuous_partitionFunction (S : Hypotheses ha β) (W : LinkWindow a) :
    Continuous (partitionFunction ha β W) := by
  have h := Complex.continuous_re.comp (continuous_partitionFunction_complex S W)
  simpa [Function.comp_def] using h
theorem isBoundedObservable_conditionalExpectation (S : Hypotheses ha β) (W : LinkWindow a)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable (W.conditionalExpectation ha β F) :=
  ⟨(isBoundedObservable_weightedIntegral S W hF).1.div
      (continuous_partitionFunction_complex S W).measurable,
    observableSupNorm F, norm_conditionalExpectation_le S W hF⟩
theorem continuous_conditionalExpectation (S : Hypotheses ha β) (W : LinkWindow a)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) (hc : Continuous F) :
    Continuous (W.conditionalExpectation ha β F) :=
  (continuous_weightedIntegral S W hF hc).div (continuous_partitionFunction_complex S W)
    (partitionFunction_ne_zero S W)
theorem conditionalExpectationTrace_eq (S : Hypotheses ha β) (W : LinkWindow a)
    (F : GaugeField a → ℂ) (U : GaugeField a) :
    W.conditionalExpectationTrace ha β F U = W.conditionalExpectation ha β F U := by
  have hk := traceBoltzmannWeight_eq S W
  have hK : ((Real.exp (β * ((facesMeeting (W.links : Set (Link a))).ncard : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  unfold LinkWindow.conditionalExpectationTrace LinkWindow.conditionalExpectation
  simp only [hk]
  generalize Real.exp (β * ((facesMeeting (W.links : Set (Link a))).ncard : ℝ)) = K at hK
  have e₁ : ∫ V, F (W.glue ha V U) * ((K * W.localWeight β (W.glue ha V U) : ℝ) : ℂ)
      ∂W.haarProd =
      (K : ℂ) * ∫ V, F (W.glue ha V U) * (W.localWeight β (W.glue ha V U) : ℂ) ∂W.haarProd := by
    rw [← integral_const_mul]
    congr 1
    funext V
    push_cast
    ring
  rw [e₁, integral_const_mul]
  push_cast
  rw [mul_div_mul_left _ _ hK]
theorem conditionalExpectation_add (S : Hypotheses ha β) (W : LinkWindow a)
    {F H : GaugeField a → ℂ} (hF : IsBoundedObservable F) (hH : IsBoundedObservable H) :
    W.conditionalExpectation ha β (F + H) =
      W.conditionalExpectation ha β F + W.conditionalExpectation ha β H := by
  funext U
  simp only [Pi.add_apply, conditionalExpectation_eq_div]
  rw [← add_div]
  congr 1
  unfold weightedIntegral
  rw [← integral_add (integrable_weightedIntegrand S W hF U)
    (integrable_weightedIntegrand S W hH U)]
  congr 1
  funext V
  simp only [Pi.add_apply]
  ring
theorem conditionalExpectation_smul (W : LinkWindow a) (c : ℂ) (F : GaugeField a → ℂ) :
    W.conditionalExpectation ha β (c • F) = c • W.conditionalExpectation ha β F := by
  funext U
  simp only [Pi.smul_apply, smul_eq_mul, conditionalExpectation_eq_div]
  rw [← mul_div_assoc]
  congr 1
  unfold weightedIntegral
  rw [← integral_const_mul]
  congr 1
  funext V
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
theorem conditionalExpectation_nonneg (W : LinkWindow a) (S : Hypotheses ha β)
    {F : GaugeField a → ℂ} (hF : ∀ U, 0 ≤ F U) (U : GaugeField a) :
    0 ≤ W.conditionalExpectation ha β F U := by
  have hre : ∀ U, F U = ((F U).re : ℂ) := fun U =>
    Complex.ext (by simp) (by simpa using (Complex.le_def.mp (hF U)).2.symm)
  have hn : weightedIntegral ha β W F U =
      ((∫ V, (F (W.glue ha V U)).re * W.localWeight β (W.glue ha V U) ∂W.haarProd : ℝ) : ℂ) := by
    unfold weightedIntegral
    refine Eq.trans ?_ integral_ofReal
    congr 1
    funext V
    rw [hre (W.glue ha V U)]
    simp
  rw [conditionalExpectation_eq_div, hn, ← Complex.ofReal_div]
  refine Complex.zero_le_real.mpr (div_nonneg (integral_nonneg fun V => ?_)
    (partitionFunction_pos S W U).le)
  exact mul_nonneg (Complex.le_def.mp (hF _)).1 (localWeight_pos W _).le
theorem conditionalExpectation_one (S : Hypotheses ha β) (W : LinkWindow a) :
    W.conditionalExpectation ha β (fun _ => 1) = fun _ => 1 := by
  funext U
  rw [conditionalExpectation_eq_div, weightedIntegral_one,
    div_self (partitionFunction_ne_zero S W U)]
def exteriorLinks (W : LinkWindow a) : Set (Link a) :=
  {ℓ | ℓ.IsPositivelyOriented ∧ ℓ ∉ W.links}
theorem conditionalExpectation_congr (W : LinkWindow a) (F : GaugeField a → ℂ)
    {U U' : GaugeField a} (h : ∀ V, W.glue ha V U = W.glue ha V U') :
    W.conditionalExpectation ha β F U = W.conditionalExpectation ha β F U' := by
  simp only [LinkWindow.conditionalExpectation, h]
theorem measurable_exterior_conditionalExpectation (S : Hypotheses ha β) (W : LinkWindow a)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    Measurable[W.exteriorSigma] (W.conditionalExpectation ha β F) := by
  refine (S.meas.1 (exteriorLinks W) _ (fun ℓ hℓ => hℓ.1)
    (isBoundedObservable_conditionalExpectation S W hF)).mpr ?_
  intro U U' h
  exact conditionalExpectation_congr W F fun V =>
    glue_congr W ha V fun ℓ hp hm => h ℓ ⟨hp, hm⟩
theorem conditionalExpectation_mul (S : Hypotheses ha β) (W : LinkWindow a)
    {F H : GaugeField a → ℂ} (hH : IsBoundedObservable H) (hm : Measurable[W.exteriorSigma] H) :
    W.conditionalExpectation ha β (F * H) = H * W.conditionalExpectation ha β F := by
  have hdep := (S.meas.1 (exteriorLinks W) H (fun ℓ hℓ => hℓ.1) hH).mp hm
  funext U
  have hv : ∀ V, H (W.glue ha V U) = H U := fun V =>
    hdep _ _ fun ℓ hℓ => glue_apply_of_not_mem W ha V U hℓ.1 hℓ.2
  simp only [Pi.mul_apply, conditionalExpectation_eq_div]
  rw [← mul_div_assoc]
  congr 1
  unfold weightedIntegral
  rw [← integral_const_mul]
  congr 1
  funext V
  simp only [Pi.mul_apply, hv]
  ring
theorem conditionalExpectation_tendsto (S : Hypotheses ha β) (W : LinkWindow a)
    {F : GaugeField a → ℂ} {Fs : ℕ → GaugeField a → ℂ} (hFs : ∀ n, IsBoundedObservable (Fs n))
    (hlim : ∀ U, Tendsto (fun n => Fs n U) atTop (𝓝 (F U)))
    (hb : BddAbove (range fun n => observableSupNorm (Fs n))) :
    (∀ U, Tendsto (fun n => W.conditionalExpectation ha β (Fs n) U) atTop
      (𝓝 (W.conditionalExpectation ha β F U))) ∧
    BddAbove (range fun n => observableSupNorm (W.conditionalExpectation ha β (Fs n))) := by
  obtain ⟨C, hC⟩ := hb
  have hC' : ∀ n, observableSupNorm (Fs n) ≤ C := fun n => hC ⟨n, rfl⟩
  constructor
  · intro U
    simp only [conditionalExpectation_eq_div]
    refine Tendsto.div_const ?_ _
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (integrable_weightedIntegrand S W (hFs n) U).aestronglyMeasurable)
      (integrable_const C) (fun n => ae_of_all _ fun V => ?_) (ae_of_all _ fun V => ?_)
    · exact norm_weightedIntegrand_le S W
        (fun U => (norm_le_supNorm (hFs n) U).trans (hC' n)) (V, U)
    · exact (hlim _).mul_const _
  · refine ⟨C, ?_⟩
    rintro _ ⟨n, rfl⟩
    have := nonempty_gaugeField (a := a)
    exact (ciSup_le (norm_conditionalExpectation_le S W (hFs n))).trans (hC' n)
theorem conditionalExpectation_mem_continuousLocalFunctions (S : Hypotheses ha β)
    (W : LinkWindow a) {F : GaugeField a → ℂ} (hF : F ∈ continuousLocalFunctions a) :
    W.conditionalExpectation ha β F ∈ continuousLocalFunctions a := by
  obtain ⟨hobs, hloc, hcont⟩ := hF
  refine ⟨isBoundedObservable_conditionalExpectation S W hobs, ?_,
    continuous_conditionalExpectation S W hobs hcont⟩
  obtain ⟨𝓜, hset, hfin, hdep⟩ := (S.meas.2.2.2 F hobs).mp hloc
  refine (S.meas.2.2.2 _ (isBoundedObservable_conditionalExpectation S W hobs)).mpr
    ⟨𝓜 ∪ ⋃ p ∈ facesMeeting (W.links : Set (Link a)), p.linkSet, ?_, ?_, ?_⟩
  · refine union_subset hset (iUnion₂_subset fun p _ ℓ hℓ => ?_)
    exact ((S.faces.2.2.1 p ℓ).mp hℓ).1
  · exact hfin.union ((facesMeeting_finite S W).biUnion fun p _ => List.finite_toSet p.edges)
  · intro U U' h
    have hpos : ∀ ℓ ∈ 𝓜 ∪ ⋃ p ∈ facesMeeting (W.links : Set (Link a)), p.linkSet,
        ℓ.IsPositivelyOriented := by
      intro ℓ hℓ
      rcases hℓ with hℓ | hℓ
      · exact hset hℓ
      · obtain ⟨p, _, hp⟩ := mem_iUnion₂.mp hℓ
        exact ((S.faces.2.2.1 p ℓ).mp hp).1
    have hagree : ∀ (V : W.Assignments) ℓ,
        ℓ ∈ 𝓜 ∪ ⋃ p ∈ facesMeeting (W.links : Set (Link a)), p.linkSet →
        W.glue ha V U ℓ = W.glue ha V U' ℓ := fun V ℓ hℓ =>
      glue_apply_congr W ha V (hpos ℓ hℓ) fun _ => h ℓ hℓ
    have hFeq : ∀ V : W.Assignments, F (W.glue ha V U) = F (W.glue ha V U') := fun V =>
      hdep _ _ fun ℓ hℓ => hagree V ℓ (Or.inl hℓ)
    have hweq : ∀ V : W.Assignments, W.localWeight β (W.glue ha V U) =
        W.localWeight β (W.glue ha V U') := fun V =>
      localWeight_congr S W fun ℓ hℓ => hagree V ℓ (Or.inr hℓ)
    simp only [LinkWindow.conditionalExpectation, hFeq, hweq]
def glueDensity (ha : 0 < a) (β : ℝ) (W : LinkWindow a) (q : GaugeField a × W.Assignments) : ℝ :=
  W.localWeight β (W.glue ha q.2 q.1) / partitionFunction ha β W q.1
def gluedMeasure (ha : 0 < a) (β : ℝ) (W : LinkWindow a) (ν : Measure (GaugeField a)) :
    Measure (GaugeField a) :=
  ((ν.prod W.haarProd).withDensity fun q => ((glueDensity ha β W q).toNNReal : ℝ≥0∞)).map
    fun q => W.glue ha q.2 q.1
theorem continuous_glue_swap (S : Hypotheses ha β) (W : LinkWindow a) :
    Continuous fun q : GaugeField a × W.Assignments => W.glue ha q.2 q.1 :=
  (continuous_glue S W).comp continuous_swap
theorem glueDensity_nonneg (S : Hypotheses ha β) (W : LinkWindow a)
    (q : GaugeField a × W.Assignments) : 0 ≤ glueDensity ha β W q :=
  div_nonneg (localWeight_pos W _).le (partitionFunction_pos S W _).le
theorem measurable_glueDensity (S : Hypotheses ha β) (W : LinkWindow a) :
    Measurable (glueDensity ha β W) :=
  ((continuous_localWeight S W).comp (continuous_glue_swap S W)).measurable.div
    ((continuous_partitionFunction S W).comp continuous_fst).measurable
theorem exists_glueDensity_le (S : Hypotheses ha β) (W : LinkWindow a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ q, glueDensity ha β W q ≤ D := by
  obtain ⟨c, hc, h⟩ := exists_pos_le_partitionFunction S W
  refine ⟨1 / c, (one_div_pos.mpr hc).le, fun q => ?_⟩
  exact div_le_div₀ zero_le_one (localWeight_le_one S W _) hc (h _)
theorem integral_gluedMeasure (S : Hypotheses ha β) (W : LinkWindow a)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) :
    ∫ U, F U ∂gluedMeasure ha β W ν = ∫ U, W.conditionalExpectation ha β F U ∂ν := by
  have hins := (continuous_glue_swap S W).measurable
  have hN : Measurable fun q => (glueDensity ha β W q).toNNReal :=
    (measurable_glueDensity S W).real_toNNReal
  unfold gluedMeasure
  rw [integral_map hins.aemeasurable hF.1.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul hN]
  have hsm : ∀ q : GaugeField a × W.Assignments,
      (glueDensity ha β W q).toNNReal • F (W.glue ha q.2 q.1) =
        (glueDensity ha β W q : ℂ) * F (W.glue ha q.2 q.1) := fun q => by
    rw [NNReal.smul_def, Real.coe_toNNReal _ (glueDensity_nonneg S W q), Complex.real_smul]
  simp only [hsm]
  obtain ⟨D, hD0, hD⟩ := exists_glueDensity_le S W
  obtain ⟨C, hC⟩ := hF.2
  have hint : Integrable (fun q : GaugeField a × W.Assignments =>
      (glueDensity ha β W q : ℂ) * F (W.glue ha q.2 q.1)) (ν.prod W.haarProd) := by
    refine Integrable.of_bound ((Complex.measurable_ofReal.comp (measurable_glueDensity S W)).mul
      (hF.1.comp hins)).aestronglyMeasurable (D * C) (ae_of_all _ fun q => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (glueDensity_nonneg S W q)]
    exact mul_le_mul (hD q) (hC _) (norm_nonneg _) hD0
  rw [integral_prod _ hint]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  change ∫ V, ((glueDensity ha β W (U, V) : ℝ) : ℂ) * F (W.glue ha V U) ∂W.haarProd = _
  rw [conditionalExpectation_eq_div, weightedIntegral, div_eq_mul_inv, ← integral_mul_const]
  congr 1
  funext V
  simp only [glueDensity]
  push_cast
  ring
theorem isProbabilityMeasure_gluedMeasure (S : Hypotheses ha β) (W : LinkWindow a)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (gluedMeasure ha β W ν) := by
  obtain ⟨D, hD0, hD⟩ := exists_glueDensity_le S W
  have hfin : IsFiniteMeasure
      ((ν.prod W.haarProd).withDensity fun q => ((glueDensity ha β W q).toNNReal : ℝ≥0∞)) := by
    refine isFiniteMeasure_withDensity_ofReal ?_
    exact (Integrable.of_bound (measurable_glueDensity S W).aestronglyMeasurable D
      (ae_of_all _ fun q => by
        rw [Real.norm_of_nonneg (glueDensity_nonneg S W q)]
        exact hD q)).2
  have h := integral_gluedMeasure S W ν (isBoundedObservable_one (a := a))
  have hν : ν.real univ = 1 := probReal_univ
  rw [conditionalExpectation_one S W, integral_const, integral_const, hν, one_smul,
    Complex.real_smul, mul_one] at h
  have h' : (gluedMeasure ha β W ν).real univ = 1 := by
    exact_mod_cast h
  exact ⟨(ENNReal.toReal_eq_one_iff _).mp h'⟩
theorem specificationProperties (S : Hypotheses ha β) : SpecificationProperties ha β := by
  intro W
  have := nonempty_gaugeField (a := a)
  refine ⟨fun F hF U => ⟨⟨integrable_weightedIntegrand S W hF U, integrable_localWeight S W U,
      (partitionFunction_pos S W U).ne'⟩, conditionalExpectationTrace_eq S W F U⟩,
    traceBoltzmannWeight_eq S W, fun F H hF hH => conditionalExpectation_add S W hF hH,
    fun c F _ => conditionalExpectation_smul W c F,
    fun F _ hF U => conditionalExpectation_nonneg W S hF U,
    conditionalExpectation_one S W,
    fun F hF => ⟨isBoundedObservable_conditionalExpectation S W hF,
      measurable_exterior_conditionalExpectation S W hF,
      ciSup_le (norm_conditionalExpectation_le S W hF)⟩,
    fun F H _ hH hm => conditionalExpectation_mul S W hH hm,
    fun F Fs _ hFs hlim hb => conditionalExpectation_tendsto S W hFs hlim hb,
    fun F hF => conditionalExpectation_mem_continuousLocalFunctions S W hF, fun ν hν => ?_⟩
  refine ⟨gluedMeasure ha β W ν, isProbabilityMeasure_gluedMeasure S W ν, fun E hE => ?_,
    fun F hF => ?_⟩
  · have hobs : IsBoundedObservable (E.indicator (1 : GaugeField a → ℂ)) :=
      ⟨measurable_one.indicator hE, 1, fun U => by
        by_cases h : U ∈ E <;> simp [h]⟩
    have h := integral_gluedMeasure S W ν hobs
    have h' : ∫ U, E.indicator (1 : GaugeField a → ℂ) U ∂gluedMeasure ha β W ν =
        (((gluedMeasure ha β W ν) E).toReal : ℂ) := by
      have := isProbabilityMeasure_gluedMeasure S W ν
      have e := integral_indicator_const (μ := gluedMeasure ha β W ν) (1 : ℂ) hE
      simpa [Measure.real, Pi.one_def] using e
    rw [← h', h]
    rfl
  · exact integral_gluedMeasure S W ν hF
theorem specificationProperties_atEveryMesh
    (h₁ : GaugeFieldsAreLinkFamiliesForAllSpacings)
    (h₂ : PlaquettePropertiesAllMeshes.Statement)
    (h₃ : MeasurableIffDependsOnlyAllSpacings)
    (h₄ : FiniteHaarIntegralsBoundedAtAllSpacings) :
    SpecificationPropertiesAtEveryMesh := fun a _ ha hβ =>
  specificationProperties ⟨hβ, h₁ a ha, h₂ a ha, h₃ a ha, h₄ a ha⟩
end YangMills.Construction.InfiniteLattice.WilsonKernelFacts

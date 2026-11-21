import YangMills.Construction.InfiniteLattice.FunctionsOfSomeOfTheBondsAndClassesStableUnderBoundedLimits
import YangMills.Construction.InfiniteLattice.OperatorsOfTheWilsonSpecification
import YangMills.Construction.InfiniteLattice.PropertiesOfTheWilsonKernelOnObservables
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslationProof
import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsProperty
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ComplexOrder
noncomputable section
namespace YangMills.Construction
open InfiniteLattice FieldsAtSpacing
namespace InfiniteLattice.WilsonOperatorPropertiesProof
open WilsonOperator
variable {a : ℝ}
theorem norm_le_supNorm {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (U : GaugeField a) : ‖F U‖ ≤ observableSupNorm F := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.norm_le_supNorm <;> assumption
theorem isBoundedObservable_const_one : IsBoundedObservable (fun _ : GaugeField a => (1 : ℂ)) :=
  ⟨measurable_const, 1, fun _ => by simp⟩
theorem compactSpace_gaugeField (ha : 0 < a) : CompactSpace (GaugeField a) :=
  (gaugeFieldHomeomorph ha).symm.compactSpace
theorem isBoundedObservable_of_continuous (ha : 0 < a) {F : GaugeField a → ℂ}
    (hc : Continuous F) : IsBoundedObservable F := by
  have := compactSpace_gaugeField ha
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨hc.measurable, C, fun U => hC U (mem_univ U)⟩
theorem dependsOnlyOnLinks_iff_fieldsAtSpacing {S : Set (Link a)} {F : GaugeField a → ℂ} :
    InfiniteLattice.DependsOnlyOnLinks S F ↔ FieldsAtSpacing.DependsOnlyOnLinks S F :=
  ⟨fun h U U' e => h U U' (funext fun l => e l l.2),
    fun h U U' e => h U U' fun l hl => congrFun e ⟨l, hl⟩⟩
@[reducible] def linkWindowOf {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) : LinkWindow a :=
  ⟨Λ, fun _ hl => mem_positiveLinks_iff.1 (hΛ hl)⟩
theorem glue_eq_splice (ha : 0 < a) {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) (V : Λ → Matrices.ComplexMatrix2.specialUnitary)
    (U : GaugeField a) : (linkWindowOf hΛ).glue ha V U = splice ha hΛ V U := by
  refine eq_splice ha hΛ V U _ (fun l => dif_pos l.2) fun l hl => ?_
  exact (dif_neg hl.2).trans
    (dif_neg fun h' => opposite_notMem_positiveLinks ha hl.1 (hΛ h'))
theorem haarProd_eq {Λ : Finset (Link a)} (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) :
    (linkWindowOf hΛ).haarProd = Matrices.ComplexMatrix2.haarPi Λ := rfl
theorem exp_windowAction_eq (β : ℝ) {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) (U : GaugeField a) :
    Real.exp (-β * (linkWindowOf hΛ).windowAction U) = WilsonOperator.localWeight β Λ U := rfl
theorem numeratorIntegrand_eq_splice (ha : 0 < a) (β : ℝ) {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) (F : GaugeField a → ℂ)
    (U : GaugeField a) :
    (linkWindowOf hΛ).numeratorIntegrand ha β F U =
      fun V => F (splice ha hΛ V U) * (WilsonOperator.localWeight β Λ (splice ha hΛ V U) : ℂ) := by
  funext V
  rw [LinkWindow.numeratorIntegrand, glue_eq_splice, exp_windowAction_eq]
theorem denominatorIntegrand_eq_splice (ha : 0 < a) (β : ℝ) {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) (U : GaugeField a) :
    (linkWindowOf hΛ).denominatorIntegrand ha β U =
      fun V => WilsonOperator.localWeight β Λ (splice ha hΛ V U) := by
  funext V
  rw [LinkWindow.denominatorIntegrand, glue_eq_splice, exp_windowAction_eq]
theorem localPartition_eq_partitionDenominator (ha : 0 < a) (β : ℝ) {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) (U : GaugeField a) :
    localPartition ha β hΛ U = (linkWindowOf hΛ).partitionDenominator ha β U := by
  rw [LinkWindow.partitionDenominator, denominatorIntegrand_eq_splice, haarProd_eq, localPartition]
theorem kernelOperator_eq_conditionalAverage (ha : 0 < a) (β : ℝ) {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) (F : GaugeField a → ℂ) :
    WilsonOperator.kernelOperator ha β hΛ F = (linkWindowOf hΛ).conditionalAverage ha β F := by
  funext U
  rw [LinkWindow.conditionalAverage_eq_div, numeratorIntegrand_eq_splice, haarProd_eq,
    ← localPartition_eq_partitionDenominator, div_eq_inv_mul, WilsonOperator.kernelOperator]
theorem localWeight_eq_exp_sum (β : ℝ) (Λ : Finset (Link a)) (U : GaugeField a) :
    WilsonOperator.localWeight β Λ U =
      Real.exp (-β * ∑ p ∈ (facesTouching_finite Λ).toFinset, faceEnergy U p) := by
  unfold WilsonOperator.localWeight
  rw [finsum_mem_eq_finite_toFinset_sum _ (facesTouching_finite Λ)]
theorem localWeight_dependsOnlyOn_thickenedLinks (β : ℝ) (Λ : Finset (Link a)) :
    InfiniteLattice.DependsOnlyOnLinks (thickenedLinks Λ) (WilsonOperator.localWeight β Λ) := by
  intro U U' h
  rw [localWeight_eq_exp_sum, localWeight_eq_exp_sum]
  congr 2
  refine Finset.sum_congr rfl fun p hp => faceEnergy_congr p fun l hl => ?_
  have hp' : p ∈ facesTouching Λ := (Set.Finite.mem_toFinset _).1 hp
  exact congrFun h ⟨l, Or.inr (mem_iUnion₂.2 ⟨p, hp', hl⟩)⟩
section Dependence
variable (hfun : FieldsAtSpacing.LinkFunctionsStatement) (ha : 0 < a)
include hfun ha
theorem dependsOnlyOnLinks_iff_measurable_linkSigmaAlgebra {S : Set (Link a)}
    (hS : S ⊆ positiveLinkSet a) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    InfiniteLattice.DependsOnlyOnLinks S F ↔ Measurable[linkSigmaAlgebra S] F :=
  dependsOnlyOnLinks_iff_fieldsAtSpacing.trans (((hfun a ha S hS).2.1 F hF).1.out 1 0)
theorem faceEnergy_mem_Icc (p : ElementaryPlaquette a) (U : GaugeField a) :
    faceEnergy U p ∈ Icc (0 : ℝ) 2 :=
  ((hfun a ha ∅ (empty_subset _)).2.2.2.2.2.1 p).2.1 U
theorem continuous_faceEnergy (p : ElementaryPlaquette a) :
    Continuous fun U : GaugeField a => faceEnergy U p := by
  have hc : Continuous (faceFunction p) :=
    ((hfun a ha ∅ (empty_subset _)).2.2.2.2.2.1 p).1.1
  exact Complex.continuous_re.comp hc
theorem mem_continuousCylinderFunctions_iff {F : GaugeField a → ℂ} :
    F ∈ continuousCylinderFunctions a ↔ F ∈ continuousFiniteLinkFunctions a := by
  constructor
  · rintro ⟨hc, W, hW, hWp, hF⟩
    have hO := isBoundedObservable_of_continuous ha hc
    have hforms := (hfun a ha W hWp).2.1 F hO
    obtain ⟨f, hf⟩ := (hforms.1.out 1 2).1 (dependsOnlyOnLinks_iff_fieldsAtSpacing.1 hF)
    exact ⟨hc, W, hW, hWp, f, ((hforms.2 f hf).2.2 hc), fun U => congrFun hf.2.2 U⟩
  · rintro ⟨hc, W, hW, hWp, f, -, hf⟩
    refine ⟨hc, W, hW, hWp, fun U U' h => ?_⟩
    rw [hf U, hf U']
    exact congrArg f h
theorem localWeight_mem_Icc {β : ℝ} (hβ : 0 < β) (Λ : Finset (Link a)) (U : GaugeField a) :
    Real.exp (-2 * β * touchingFaceCount Λ) ≤ WilsonOperator.localWeight β Λ U ∧
      WilsonOperator.localWeight β Λ U ≤ 1 := by
  rw [localWeight_eq_exp_sum]
  have h0 : 0 ≤ ∑ p ∈ (facesTouching_finite Λ).toFinset, faceEnergy U p :=
    Finset.sum_nonneg fun p _ => (faceEnergy_mem_Icc hfun ha p U).1
  have h2 : ∑ p ∈ (facesTouching_finite Λ).toFinset, faceEnergy U p ≤
      2 * (touchingFaceCount Λ : ℝ) := by
    calc ∑ p ∈ (facesTouching_finite Λ).toFinset, faceEnergy U p
        ≤ ∑ _p ∈ (facesTouching_finite Λ).toFinset, (2 : ℝ) :=
          Finset.sum_le_sum fun p _ => (faceEnergy_mem_Icc hfun ha p U).2
      _ = 2 * (touchingFaceCount Λ : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, touchingFaceCount,
            Set.ncard_eq_toFinset_card _ (facesTouching_finite Λ), mul_comm]
  have h3 := mul_le_mul_of_nonneg_left h2 hβ.le
  have h4 := mul_nonneg hβ.le h0
  exact ⟨Real.exp_le_exp.2 (by linarith), Real.exp_le_one_iff.2 (by linarith)⟩
theorem localWeight_mem_continuousCylinderFunctions (β : ℝ) {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) :
    (fun U => (WilsonOperator.localWeight β Λ U : ℂ)) ∈ continuousCylinderFunctions a := by
  refine ⟨?_, thickenedLinks Λ, thickenedLinks_finite Λ, thickenedLinks_subset hΛ,
    fun U U' h => congrArg _ (localWeight_dependsOnlyOn_thickenedLinks β Λ U U' h)⟩
  have hs : Continuous fun U : GaugeField a => WilsonOperator.localWeight β Λ U := by
    have he : (fun U : GaugeField a => WilsonOperator.localWeight β Λ U) =
        fun U : GaugeField a => Real.exp (-β * ∑ p ∈ (facesTouching_finite Λ).toFinset, faceEnergy U p) :=
      funext (localWeight_eq_exp_sum β Λ)
    rw [he]
    exact Real.continuous_exp.comp (continuous_const.mul
      (continuous_finsetSum _ fun p _ => continuous_faceEnergy hfun ha p))
  exact Complex.continuous_ofReal.comp hs
theorem ignoresLinksOf_iff_measurable {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) :
    IgnoresLinksOf (Λ : Set (Link a)) F ↔
      Measurable[linkSigmaAlgebra (positiveLinkSet a \ (Λ : Set (Link a)))] F := by
  refine Iff.trans ?_ (dependsOnlyOnLinks_iff_measurable_linkSigmaAlgebra hfun ha sdiff_subset hF)
  constructor
  · intro h U U' e
    refine h U U' (funext fun l => ?_)
    have hl := l.2
    rcases mem_positiveLinks_or_opposite_mem (l : Link a) with hp | hp
    · exact congrFun e ⟨l, hp, hl.1⟩
    · have h' := congrFun e ⟨(l : Link a).opposite, hp, hl.2⟩
      change U (l : Link a).opposite = U' (l : Link a).opposite at h'
      change U (l : Link a) = U' (l : Link a)
      rw [U.2 l, U'.2 l] at h'
      exact inv_injective h'
  · intro h U U' e
    refine h U U' (funext fun l => ?_)
    exact congrFun e ⟨l, l.2.2,
      fun hr => opposite_notMem_positiveLinks ha l.2.1 (hΛ hr)⟩
theorem dependenceIsMeasurability : DependenceIsMeasurability a where
  dependsOnlyOnLinks_iff_measurable S hS F hF :=
    dependsOnlyOnLinks_iff_measurable_linkSigmaAlgebra hfun ha hS hF
  regionMeasurable_iff S F := by
    refine and_congr_right fun hF => ?_
    have hc := (((hfun a ha ∅ (empty_subset _)).2.2.1).1 S).1
    have hm : IsRegionMeasurable S F ↔ Measurable[linkSigma (positiveLinksWithin a S)] F := by
      unfold IsRegionMeasurable
      rw [hc]
    have hsub : positiveLinksWithin a S ⊆ positiveLinkSet a := inter_subset_left
    refine hm.trans ((dependsOnlyOnLinks_iff_measurable_linkSigmaAlgebra hfun ha hsub hF).symm.trans ?_)
    constructor
    · intro h U U' e
      exact h U U' (funext fun l => congrFun e ⟨l, l.2.2⟩)
    · intro h U U' e
      refine h U U' (funext fun l => ?_)
      have hl := l.2
      rcases mem_positiveLinks_or_opposite_mem (l : Link a) with hp | hp
      · exact congrFun e ⟨l, hp, hl⟩
      · have hr : (l : Link a).opposite ∈ positiveLinksWithin a S :=
          ⟨hp, hl.2, hl.1⟩
        have h' := congrFun e ⟨(l : Link a).opposite, hr⟩
        change U (l : Link a).opposite = U' (l : Link a).opposite at h'
        change U (l : Link a) = U' (l : Link a)
        rw [U.2 l, U'.2 l] at h'
        exact inv_injective h'
end Dependence
section Kernel
variable (hfun : FieldsAtSpacing.LinkFunctionsStatement)
  (hops : ConditionalAverageProperties.claim) (ha : 0 < a) {β : ℝ} (hβ : 0 < β)
  {Λ : Finset (Link a)} (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a)
include hops hβ in
theorem localPartition_pos (U : GaugeField a) : 0 < localPartition ha β hΛ U := by
  have h := (hops a ha β hβ (linkWindowOf hΛ) _ _ isBoundedObservable_const_one
    isBoundedObservable_const_one).1
  rw [localPartition_eq_partitionDenominator]
  exact lt_of_lt_of_le h.2.1 (h.2.2 U).2.2.1
include hops hβ in
theorem kernelOperator_nonneg {F : GaugeField a → ℂ} (hF : ∀ U, 0 ≤ F U) (U : GaugeField a) :
    0 ≤ WilsonOperator.kernelOperator ha β hΛ F U := by
  have hre : ∀ U, F U = ((F U).re : ℂ) := fun U =>
    Complex.ext rfl (by simpa using (Complex.le_def.1 (hF U)).2.symm)
  have hint : (∫ V, F (splice ha hΛ V U) * (WilsonOperator.localWeight β Λ (splice ha hΛ V U) : ℂ)
        ∂Matrices.ComplexMatrix2.haarPi Λ) =
      ((∫ V, (F (splice ha hΛ V U)).re * WilsonOperator.localWeight β Λ (splice ha hΛ V U)
        ∂Matrices.ComplexMatrix2.haarPi Λ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun V => ?_)
    change F (splice ha hΛ V U) * _ = ((_ * _ : ℝ) : ℂ)
    rw [Complex.ofReal_mul, ← hre]
  unfold WilsonOperator.kernelOperator
  rw [hint, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  refine Complex.zero_le_real.2 (mul_nonneg (inv_nonneg.2 (localPartition_pos hops ha hβ hΛ U).le)
    (integral_nonneg fun V => mul_nonneg ?_ (Real.exp_pos _).le))
  have := (Complex.le_def.1 (hF (splice ha hΛ V U))).1
  simpa using this
include hfun hops hβ in
theorem weightAndKernelBounds : WeightAndKernelBounds ha β hΛ where
  localWeight_mem := localWeight_mem_continuousCylinderFunctions hfun ha β hΛ
  localWeight_dependsOnlyOn := localWeight_dependsOnlyOn_thickenedLinks β Λ
  integrable_kernel F hF U := by
    have h := (((hops a ha β hβ (linkWindowOf hΛ) F F hF hF).1).2.2 U).1
    rwa [numeratorIntegrand_eq_splice, haarProd_eq] at h
  integrable_localPartition U := by
    have h := (((hops a ha β hβ (linkWindowOf hΛ) _ _ isBoundedObservable_const_one
      isBoundedObservable_const_one).1).2.2 U).2.1
    rwa [denominatorIntegrand_eq_splice, haarProd_eq] at h
  localWeight_bounds U := localWeight_mem_Icc hfun ha hβ Λ U
  localPartition_bounds U := by
    rw [localPartition_eq_partitionDenominator]
    exact (((hops a ha β hβ (linkWindowOf hΛ) _ _ isBoundedObservable_const_one
      isBoundedObservable_const_one).1).2.2 U).2.2
  kernel_isBoundedObservable F hF := by
    rw [kernelOperator_eq_conditionalAverage]
    exact (hops a ha β hβ (linkWindowOf hΛ) F F hF hF).2.1.1
  kernel_ignoresLinksOf F hF := by
    have hO : IsBoundedObservable (WilsonOperator.kernelOperator ha β hΛ F) := by
      rw [kernelOperator_eq_conditionalAverage]
      exact (hops a ha β hβ (linkWindowOf hΛ) F F hF hF).2.1.1
    refine (ignoresLinksOf_iff_measurable hfun ha hΛ hO).2 ?_
    rw [kernelOperator_eq_conditionalAverage]
    exact (hops a ha β hβ (linkWindowOf hΛ) F F hF hF).2.1.2
  supNorm_kernel_le F hF := by
    rw [kernelOperator_eq_conditionalAverage]
    exact (hops a ha β hβ (linkWindowOf hΛ) F F hF hF).2.2.1
  kernel_add F G hF hG := by
    simp only [kernelOperator_eq_conditionalAverage]
    exact (hops a ha β hβ (linkWindowOf hΛ) F G hF hG).2.2.2.2.2.1
  kernel_smul c F hF := by
    simp only [kernelOperator_eq_conditionalAverage]
    exact (hops a ha β hβ (linkWindowOf hΛ) F F hF hF).2.2.2.2.2.2.1 c
  kernel_const_one := by
    rw [kernelOperator_eq_conditionalAverage]
    exact (hops a ha β hβ (linkWindowOf hΛ) _ _ isBoundedObservable_const_one
      isBoundedObservable_const_one).2.2.2.2.2.2.2.1
  kernel_nonneg F _ hF U := kernelOperator_nonneg hops ha hβ hΛ hF U
  kernel_tendsto G F hG hC hlim U := by
    obtain ⟨C, hC⟩ := hC
    have hF : IsBoundedObservable F := by
      refine ⟨measurable_of_tendsto_metrizable (fun k => (hG k).1) (tendsto_pi_nhds.2 hlim),
        C, fun U => ?_⟩
      exact le_of_tendsto (hlim U).norm
        (Eventually.of_forall fun k => (norm_le_supNorm (hG k) U).trans (hC k))
    simp only [kernelOperator_eq_conditionalAverage]
    exact (hops a ha β hβ (linkWindowOf hΛ) F F hF hF).2.2.2.2.2.2.2.2 G hG
      ⟨C, by rintro _ ⟨n, rfl⟩; exact hC n⟩ hlim U
include hfun hops hβ in
theorem kernelOnIgnoringObservables : KernelOnIgnoringObservables ha β hΛ := by
  have hmul : ∀ H : GaugeField a → ℂ, IsBoundedObservable H →
      IgnoresLinksOf (Λ : Set (Link a)) H → ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        WilsonOperator.kernelOperator ha β hΛ (H * F) = H * WilsonOperator.kernelOperator ha β hΛ F := by
    intro H hH hr F hF
    simp only [kernelOperator_eq_conditionalAverage]
    exact (hops a ha β hβ (linkWindowOf hΛ) F H hF hH).2.2.2.1
      ((ignoresLinksOf_iff_measurable hfun ha hΛ hH).1 hr)
  refine ⟨fun F hF => ignoresLinksOf_iff_measurable hfun ha hΛ hF, hmul, fun H hH hr => ?_⟩
  have h1 := hmul H hH hr _ isBoundedObservable_const_one
  have hone : WilsonOperator.kernelOperator ha β hΛ (fun _ => 1) = fun _ => 1 :=
    (weightAndKernelBounds hfun hops ha hβ hΛ).kernel_const_one
  rw [hone] at h1
  have e₁ : H * (fun _ => (1 : ℂ)) = H := funext fun U => mul_one _
  rwa [e₁] at h1
include hfun hops hβ in
theorem kernelDependence : KernelDependence ha β hΛ where
  kernel_dependsOnlyOn_diff S hS hSB F _ hFS := by
    intro U U' h
    have key : ∀ V : Λ → Matrices.ComplexMatrix2.specialUnitary, ∀ l ∈ S,
        splice ha hΛ V U l = splice ha hΛ V U' l := by
      intro V l hl
      by_cases hlΛ : l ∈ Λ
      · rw [splice_apply_of_mem ha hΛ V U ⟨l, hlΛ⟩, splice_apply_of_mem ha hΛ V U' ⟨l, hlΛ⟩]
      · rw [splice_apply_of_notMem ha hΛ V U ⟨hSB hl, hlΛ⟩,
          splice_apply_of_notMem ha hΛ V U' ⟨hSB hl, hlΛ⟩]
        exact congrFun h ⟨l, hl, hlΛ⟩
    have hFe : ∀ V, F (splice ha hΛ V U) = F (splice ha hΛ V U') := fun V =>
      hFS _ _ (funext fun l => key V l l.2)
    have hwe : ∀ V, WilsonOperator.localWeight β Λ (splice ha hΛ V U) =
        WilsonOperator.localWeight β Λ (splice ha hΛ V U') := fun V =>
      localWeight_dependsOnlyOn_thickenedLinks β Λ _ _ (funext fun l => key V l (hS l.2))
    unfold WilsonOperator.kernelOperator localPartition
    simp only [hFe, hwe]
  kernel_mem_continuousCylinderFunctions F hF := by
    have hF' := (mem_continuousCylinderFunctions_iff hfun ha).1 hF
    have hO := isBoundedObservable_of_continuous ha hF.1
    refine (mem_continuousCylinderFunctions_iff hfun ha).2 ?_
    rw [kernelOperator_eq_conditionalAverage]
    exact (hops a ha β hβ (linkWindowOf hΛ) F F hO hO).2.2.2.2.1 hF'
end Kernel
theorem gibbsPropertyEquivalences (hfun : FieldsAtSpacing.LinkFunctionsStatement)
    (hgibbs : GibbsCharacterizations) (ha : 0 < a) {β : ℝ} (hβ : 0 < β)
    (ν : GaugeFieldProbability a) : GibbsPropertyEquivalences ha β ν := by
  have t := hgibbs a ha β hβ ν
  have hsub : ∀ W : LinkWindow a, ((W.links : Finset (Link a)) : Set (Link a)) ⊆
      positiveLinkSet a := fun W _ hl =>
    mem_positiveLinks_iff.2 (W.isPositive _ hl)
  have hB : (∀ (W : LinkWindow a) (F : GaugeField a → ℂ), IsBoundedObservable F →
        GaugeFieldProbability.expect ν (W.conditionalAverage ha β F) =
          GaugeFieldProbability.expect ν F) ↔
      ∀ (Λ : Finset (Link a)) (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a)
        (F : GaugeField a → ℂ), IsBoundedObservable F →
          ν.expect (WilsonOperator.kernelOperator ha β hΛ F) = ν.expect F := by
    constructor
    · intro h Λ hΛ F hF
      rw [kernelOperator_eq_conditionalAverage]
      exact h _ F hF
    · intro h W F hF
      have h' := h W.links (hsub W) F hF
      rw [kernelOperator_eq_conditionalAverage] at h'
      exact h'
  have hC : (∀ W : LinkWindow a, ∀ F ∈ continuousFiniteLinkFunctions a,
        GaugeFieldProbability.expect ν (W.conditionalAverage ha β F) =
          GaugeFieldProbability.expect ν F) ↔
      ∀ (Λ : Finset (Link a)) (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a),
        ∀ F ∈ continuousCylinderFunctions a,
          ν.expect (WilsonOperator.kernelOperator ha β hΛ F) = ν.expect F := by
    constructor
    · intro h Λ hΛ F hF
      rw [kernelOperator_eq_conditionalAverage]
      exact h _ F ((mem_continuousCylinderFunctions_iff hfun ha).1 hF)
    · intro h W F hF
      have h' := h W.links (hsub W) F ((mem_continuousCylinderFunctions_iff hfun ha).2 hF)
      rw [kernelOperator_eq_conditionalAverage] at h'
      exact h'
  unfold GibbsPropertyEquivalences
  tfae_have 1 ↔ 2 := (t.out 0 1).trans hB
  tfae_have 1 ↔ 3 := (t.out 0 2).trans hC
  tfae_finish
theorem wilsonOperatorProperties (hfun : FieldsAtSpacing.LinkFunctionsStatement)
    (hops : ConditionalAverageProperties.claim)
    (hgibbs : GibbsCharacterizations) : WilsonOperatorProperties := by
  intro L K _ _ _ ha β hβ
  exact ⟨fun Λ hΛ => ⟨weightAndKernelBounds hfun hops ha hβ hΛ,
      kernelOnIgnoringObservables hfun hops ha hβ hΛ, kernelDependence hfun hops ha hβ hΛ⟩,
    dependenceIsMeasurability hfun ha, fun ν => gibbsPropertyEquivalences hfun hgibbs ha hβ ν⟩
end InfiniteLattice.WilsonOperatorPropertiesProof
end YangMills.Construction

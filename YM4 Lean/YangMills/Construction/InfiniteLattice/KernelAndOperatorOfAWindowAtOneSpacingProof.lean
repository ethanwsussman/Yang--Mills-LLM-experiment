import YangMills.Construction.InfiniteLattice.KernelAndOperatorOfAWindowAtOneSpacing
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsOnTheInfiniteLattice
import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicExtensions.WindowKernelOperator
open MeasureTheory
open YangMills.Construction.InfiniteLattice
open YangMills.Construction.InfiniteLattice.GaugeFieldSpace
variable {a : ℝ}
theorem isBoundedBorel_of_continuous {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {f : X → ℝ} (hf : Continuous f) : IsBoundedBorel f := by
  refine ⟨?_, ?_⟩
  · let _ : MeasurableSpace X := borel X
    have : BorelSpace X := ⟨rfl⟩
    exact hf.measurable
  · obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
    exact ⟨C, fun x => by simpa using hC x (Set.mem_univ x)⟩
theorem measurable_comp_mul_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {g : Y → ℝ} (hg : Measurable[borel Y] g) {c : X → Y} (hc : Continuous c) {k : X → ℝ}
    (hk : Continuous k) :
    Measurable[borel X] fun x => g (c x) * k x := by
  let _ : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  let _ : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  exact (hg.comp hc.measurable).mul hk.measurable
theorem measurableSpace_assignments_eq_borel (W : LinkWindow a) :
    (inferInstance : MeasurableSpace W.Assignments) = borel W.Assignments :=
  (borel_linkVariables (W.links : Set (Link a))).symm
section Window
variable (W : LinkWindow a)
theorem links_subset_positiveLinks :
    (W.links : Set (Link a)) ⊆ CutoffLattice.positiveLinks a :=
  fun e he => mem_positiveLinks_iff.mpr (W.isPositive e he)
instance finite_links : Finite (W.links : Set (Link a)) := W.links.finite_toSet.to_subtype
instance isProbabilityMeasure_haarProd : IsProbabilityMeasure W.haarProd := by
  unfold LinkWindow.haarProd Matrices.ComplexMatrix2.haarPi
  infer_instance
variable (ha : 0 < a) (β : ℝ)
theorem agreesOnAndOff_glue (V : W.Assignments) (U : GaugeField a) :
    AgreesOnAndOff (W.links : Set (Link a)) V U (W.glue ha V U) := by
  refine ⟨fun e => dif_pos e.2, fun e he => ?_⟩
  have hin : e ∉ W.links := he.2
  have hopp : e.opposite ∉ W.links := fun h' =>
    Link.opposite_not_isPositivelyOriented ha (mem_positiveLinks_iff.mp he.1)
      (W.isPositive _ h')
  simp [LinkWindow.glue, hin, hopp]
variable {W ha β}
theorem continuous_glue (hsp : FiniteLinkSplicing a) :
    Continuous fun q : W.Assignments × GaugeField a => W.glue ha q.1 q.2 :=
  (hsp (W.links : Set (Link a)) (links_subset_positiveLinks W)).2.1 (fun q => W.glue ha q.1 q.2)
    fun V U => agreesOnAndOff_glue W ha V U
theorem continuous_boltzmannWeight (hsp : FiniteLinkSplicing a) (hen : FaceEnergyProperties a) :
    Continuous fun q : W.Assignments × GaugeField a => W.boltzmannWeight ha β q.1 q.2 := by
  have hfin : W.faces.Finite := WilsonOperator.facesTouching_finite W.links
  have hsum : ∀ U : GaugeField a, ∑ᶠ f ∈ W.faces, faceEnergy U f =
      ∑ f ∈ hfin.toFinset, faceEnergy U f :=
    fun U => finsum_mem_eq_finite_toFinset_sum _ hfin
  simp only [LinkWindow.boltzmannWeight, hsum]
  refine Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun f _ => ?_))
  exact (hen f).1.comp (continuous_glue hsp)
theorem fubini_links (hfub : FiniteLinkFubini a) (Φ : W.Assignments × GaugeField a → ℝ)
    (hΦ : IsBoundedBorel Φ) :
    IsBoundedBorel (fun U => ∫ V, Φ (V, U) ∂W.haarProd) ∧
      (Continuous Φ → Continuous fun U => ∫ V, Φ (V, U) ∂W.haarProd) ∧
      ∀ ν : Measure (GaugeField a), IsProbabilityMeasure ν →
        IsBoundedBorel (fun V => ∫ U, Φ (V, U) ∂ν) ∧
        ∫ U, (∫ V, Φ (V, U) ∂W.haarProd) ∂ν = ∫ V, (∫ U, Φ (V, U) ∂ν) ∂W.haarProd := by
  have h := hfub (W.links : Set (Link a)) (links_subset_positiveLinks W) Φ hΦ
  exact ⟨h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
theorem integrable_haarProd_of_continuous {f : W.Assignments → ℝ} (hf : Continuous f) :
    Integrable f W.haarProd := by
  have := WilsonOperator.secondCountable_specialUnitary
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
theorem partitionFunction_pos (hsp : FiniteLinkSplicing a) (hen : FaceEnergyProperties a)
    (U : GaugeField a) : 0 < ∫ V, W.boltzmannWeight ha β V U ∂W.haarProd := by
  have hc : Continuous fun V : W.Assignments => W.boltzmannWeight ha β V U :=
    (continuous_boltzmannWeight (W := W) (ha := ha) (β := β) hsp hen).comp
      (f := fun V : W.Assignments => (V, U)) (by fun_prop)
  have hpos : ∀ V : W.Assignments, 0 < W.boltzmannWeight ha β V U := fun V => Real.exp_pos _
  refine (integral_pos_iff_support_of_nonneg (fun V => (hpos V).le)
    (integrable_haarProd_of_continuous hc)).mpr ?_
  have hsupp : Function.support (fun V : W.Assignments => W.boltzmannWeight ha β V U) =
      Set.univ :=
    Set.eq_univ_of_forall fun V => (hpos V).ne'
  rw [hsupp]
  simp
theorem integral_densityKernel (hsp : FiniteLinkSplicing a) (hen : FaceEnergyProperties a)
    (U : GaugeField a) : ∫ V, W.densityKernel ha β V U ∂W.haarProd = 1 := by
  simp only [LinkWindow.densityKernel]
  rw [integral_div, div_self (partitionFunction_pos hsp hen U).ne']
theorem densityKernel_nonneg (V : W.Assignments) (U : GaugeField a) :
    0 ≤ W.densityKernel ha β V U :=
  div_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)
theorem continuous_densityKernel (hprod : ProductStructure a) (hsp : FiniteLinkSplicing a)
    (hen : FaceEnergyProperties a) (hfub : FiniteLinkFubini a) :
    Continuous fun q : W.Assignments × GaugeField a => W.densityKernel ha β q.1 q.2 := by
  have : CompactSpace (GaugeField a) := hprod.2.2.2.2.1
  have hw := continuous_boltzmannWeight (W := W) (ha := ha) (β := β) hsp hen
  have hz : Continuous fun U : GaugeField a => ∫ V, W.boltzmannWeight ha β V U ∂W.haarProd :=
    (fubini_links hfub (fun q => W.boltzmannWeight ha β q.1 q.2)
      (isBoundedBorel_of_continuous hw)).2.1 hw
  exact hw.div (hz.comp continuous_snd) fun q => (partitionFunction_pos hsp hen q.2).ne'
theorem continuous_rimKernel (hprod : ProductStructure a) (hsp : FiniteLinkSplicing a)
    (hen : FaceEnergyProperties a) (hfub : FiniteLinkFubini a) :
    Continuous fun q : W.Assignments × GaugeField a =>
      W.rimKernel ha β q.1 (W.restrictRim q.2) := by
  simp only [LinkWindow.rimKernel_restrictRim]
  exact continuous_densityKernel hprod hsp hen hfub
theorem norm_realOperator_le (hprod : ProductStructure a) (hsp : FiniteLinkSplicing a)
    (hen : FaceEnergyProperties a) (hfub : FiniteLinkFubini a) {F : GaugeField a → ℝ}
    (hF : TestFunctions.IsBoundedFun F) (U : GaugeField a) :
    ‖W.realOperator ha β F U‖ ≤ TestFunctions.uniformNorm F := by
  obtain ⟨C, hC⟩ := hF
  have hbdd : BddAbove (Set.range fun x => ‖F x‖) := ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  have hle : ∀ x, ‖F x‖ ≤ TestFunctions.uniformNorm F := fun x => le_ciSup hbdd x
  have hkc : Continuous fun V : W.Assignments => W.densityKernel ha β V U :=
    (continuous_densityKernel (W := W) (ha := ha) (β := β) hprod hsp hen hfub).comp
      (f := fun V : W.Assignments => (V, U)) (by fun_prop)
  have hbound : ‖W.realOperator ha β F U‖ ≤
      ∫ V, TestFunctions.uniformNorm F * W.densityKernel ha β V U ∂W.haarProd := by
    refine norm_integral_le_of_norm_le ((integrable_haarProd_of_continuous hkc).const_mul _)
      (Filter.Eventually.of_forall fun V => ?_)
    rw [W.rimKernel_restrictRim ha β V U, norm_mul,
      Real.norm_eq_abs (W.densityKernel _ _ _ _), abs_of_nonneg (densityKernel_nonneg V U)]
    exact mul_le_mul_of_nonneg_right (hle _) (densityKernel_nonneg V U)
  rwa [integral_const_mul, integral_densityKernel hsp hen, mul_one] at hbound
theorem dependsOnlyOn_realOperator {F : GaugeField a → ℝ} {S : Set (Link a)}
    (hF : CutoffLattice.DependsOnlyOn F S) :
    CutoffLattice.DependsOnlyOn (W.realOperator ha β F)
      ((S \ (W.links : Set (Link a))) ∪ W.rim) := by
  refine ⟨Set.union_subset (Set.sdiff_subset.trans hF.1)
    W.rim_subset_positiveLinks, fun U U' hUU => ?_⟩
  have hr : W.restrictRim U = W.restrictRim U' := by
    funext e
    exact congrFun hUU ⟨e.1, Or.inr e.2⟩
  have hV : ∀ V : W.Assignments, F (W.glue ha V U) = F (W.glue ha V U') := by
    intro V
    refine hF.2 _ _ ?_
    funext e
    change W.glue ha V U e = W.glue ha V U' e
    by_cases hin : (e : Link a) ∈ W.links
    · simp [LinkWindow.glue, hin]
    by_cases hopp : (e : Link a).opposite ∈ W.links
    · simp [LinkWindow.glue, hin, hopp]
    have hU : U e = U' e := congrFun hUU ⟨e.1, Or.inl ⟨e.2, hin⟩⟩
    simpa [LinkWindow.glue, hin, hopp] using hU
  simp only [LinkWindow.realOperator, hr, hV]
theorem restrictInside_glue (V : W.Assignments) (U : GaugeField a) :
    W.restrictInside (W.glue ha V U) = V := by
  funext e
  exact dif_pos e.2
end Window
theorem of_links_eq_empty (W : LinkWindow a) (ha : 0 < a) (β : ℝ) (hW : W.links = ∅) :
    W.faceCount = 0 ∧ W.rim = ∅ ∧
      (∀ (V : W.Assignments) (η : LinkVariables W.rim), W.rimKernel ha β V η = 1) ∧
      ∀ F : GaugeField a → ℝ, W.realOperator ha β F = F := by
  have hP : W.faces = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro f ⟨e, -, he⟩
    rw [hW] at he
    simp at he
  have hR : W.rim = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro e ⟨⟨f, hf, -⟩, -⟩
    rw [hP] at hf
    exact hf
  have hw : ∀ (V : W.Assignments) (U : GaugeField a), W.boltzmannWeight ha β V U = 1 := by
    intro V U
    simp [LinkWindow.boltzmannWeight, hP]
  have hk : ∀ (V : W.Assignments) (U : GaugeField a), W.densityKernel ha β V U = 1 := by
    intro V U
    simp [LinkWindow.densityKernel, hw]
  have hkr : ∀ (V : W.Assignments) (η : LinkVariables W.rim),
      W.rimKernel ha β V η = 1 := fun V η => hk V _
  have hglue : ∀ (V : W.Assignments) (U : GaugeField a), W.glue ha V U = U := by
    intro V U
    refine Subtype.ext (funext fun e => ?_)
    simp [LinkWindow.glue, hW]
  refine ⟨by simp [LinkWindow.faceCount, hP], hR, hkr, fun F => funext fun U => ?_⟩
  simp [LinkWindow.realOperator, hkr, hglue]
theorem windowKernelOperatorProperties_holds (h : GaugeFieldSpace.Statement) :
    WindowKernelOperatorProperties := by
  intro d W
  obtain ⟨hprod, hsp, hen, -, hfub⟩ := h d
  have ha := d.spacing_pos
  have : CompactSpace (GaugeField d.spacing) := hprod.2.2.2.2.1
  have hkc := continuous_rimKernel (W := W) (ha := ha) (β := d.coupling) hprod hsp hen hfub
  have hborelC : ∀ F : GaugeField d.spacing → ℝ, Measurable F →
      Measurable[borel (GaugeField d.spacing)] F :=
    fun F hF => hF
  refine ⟨⟨fun η => integral_densityKernel hsp hen _, fun hW => ?_⟩, fun F hF hFb => ?_,
    fun ν => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := of_links_eq_empty W ha d.coupling hW
    exact ⟨h1, h2, h3, fun F _ _ => h4 F⟩
  · set Φ : W.Assignments × GaugeField d.spacing → ℝ := fun q =>
      F (W.glue ha q.1 q.2) * W.rimKernel ha d.coupling q.1 (W.restrictRim q.2) with hΦdef
    have hΦb : IsBoundedBorel Φ := by
      refine ⟨measurable_comp_mul_continuous (hborelC F hF) (continuous_glue hsp) hkc, ?_⟩
      obtain ⟨C, hC⟩ := hFb
      obtain ⟨D, hD⟩ := (isBoundedBorel_of_continuous hkc).2
      refine ⟨C * D, fun q => ?_⟩
      rw [abs_mul]
      exact mul_le_mul (hC _) (hD q) (abs_nonneg _)
        ((norm_nonneg _).trans (hC (W.glue ha q.1 q.2)))
    have hI := fubini_links hfub Φ hΦb
    have hle : ∀ U, ‖W.realOperator ha d.coupling F U‖ ≤ TestFunctions.uniformNorm F :=
      norm_realOperator_le hprod hsp hen hfub hFb
    refine ⟨hI.1.1, ⟨_, hle⟩, ?_, fun hFc => ?_, fun S hS => dependsOnlyOn_realOperator hS⟩
    · have : Nonempty (GaugeField d.spacing) := ⟨trivialField d.spacing⟩
      exact ciSup_le hle
    · exact hI.2.1 ((hFc.comp (continuous_glue hsp)).mul hkc)
  · set Φ₀ : W.Assignments × GaugeField d.spacing → ℝ := fun q =>
      W.rimKernel ha d.coupling q.1 (W.restrictRim q.2) with hΦ₀def
    have hΦ₀ := (fubini_links (W := W) hfub Φ₀ (isBoundedBorel_of_continuous hkc)).2.2
      ν.measure inferInstance
    refine ⟨?_, ?_, fun F hF hFb => ?_⟩
    · have hm := hΦ₀.1.1
      rw [← measurableSpace_assignments_eq_borel W] at hm
      exact hm
    · obtain ⟨C, hC⟩ := hΦ₀.1.2
      exact ⟨C, hC⟩
    · have hFborel : Measurable[borel W.Assignments] F := by
        rw [← measurableSpace_assignments_eq_borel W]
        exact hF
      set Φ₁ : W.Assignments × GaugeField d.spacing → ℝ := fun q => F q.1 * Φ₀ q with hΦ₁def
      have hΦ₁b : IsBoundedBorel Φ₁ := by
        refine ⟨measurable_comp_mul_continuous hFborel continuous_fst hkc, ?_⟩
        obtain ⟨C, hC⟩ := hFb
        obtain ⟨D, hD⟩ := (isBoundedBorel_of_continuous hkc).2
        refine ⟨C * D, fun q => ?_⟩
        rw [abs_mul]
        exact mul_le_mul (hC _) (hD q) (abs_nonneg _) ((norm_nonneg _).trans (hC q.1))
      have hswap := ((fubini_links (W := W) hfub Φ₁ hΦ₁b).2.2 ν.measure inferInstance).2
      have hop : (W.realOperator ha d.coupling fun U => F (W.restrictInside U)) =
          fun U => ∫ V, Φ₁ (V, U) ∂W.haarProd := by
        funext U
        simp only [LinkWindow.realOperator, hΦ₁def, hΦ₀def, restrictInside_glue]
      rw [hop]
      change ∫ U, (∫ V, Φ₁ (V, U) ∂W.haarProd) ∂ν.measure = _
      rw [hswap]
      refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
      change ∫ U, F V * Φ₀ (V, U) ∂ν.measure = F V * ∫ U, Φ₀ (V, U) ∂ν.measure
      rw [integral_const_mul]
end YangMills.Construction.InfiniteLattice.PeriodicExtensions.WindowKernelOperator

import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLattice
import YangMills.Construction.InfiniteLattice.CoveringOnBondsAndPlaquettes
import YangMills.Construction.InfiniteLattice.EquilibriumEquationOfThePeriodicExtensions
import YangMills.Construction.InfiniteLattice.KernelAndOperatorOfAWindowAtOneSpacing
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsOnTheInfiniteLattice
import YangMills.Construction.InfiniteLattice.WeakLimitPointsOfExtensionsAreNonEmptyAndClosed
import YangMills.Construction.InfiniteLattice.WeaklyConvergentSubsequencesOfStates
import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import YangMills.Construction.InfiniteLattice.WindowDensitiesAtOneSpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open YangMills.Construction.InfiniteLattice.PeriodicExtensions YangMills.Construction.InfiniteLattice
open YangMills.Construction.InfiniteLattice.GaugeFieldSpace
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction.WindowDensities
attribute [local instance] WilsonOperator.secondCountable_specialUnitary
theorem integral_bounds_of_forall {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {f : X → ℝ} (hf : Integrable f ν) {s t : ℝ}
    (h : ∀ x, s ≤ f x ∧ f x ≤ t) :
    s ≤ ∫ x, f x ∂ν ∧ ∫ x, f x ∂ν ≤ t := by
  constructor
  · have := integral_mono (integrable_const s) hf fun x => (h x).1
    simpa using this
  · have := integral_mono hf (integrable_const t) fun x => (h x).2
    simpa using this
theorem integrable_of_abs_le {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {f : X → ℝ} (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    Integrable f ν := by
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => hC x)
theorem continuous_uncurry_comp {A X Y Z : Type*} [TopologicalSpace A] [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y → Z}
    (hf : Continuous fun p : X × Y => f p.1 p.2) {g : A → X} {h : A → Y} (hg : Continuous g)
    (hh : Continuous h) : Continuous fun t => f (g t) (h t) :=
  hf.comp (hg.prodMk hh)
theorem continuous_linkValue {a : ℝ} (b : Link a) : Continuous fun U : GaugeField a => U b :=
  (continuous_apply b).comp
    (continuous_subtype_val :
      Continuous (Subtype.val :
        {U : Link a → Matrices.ComplexMatrix2.specialUnitary // ∀ b, U b.opposite = (U b)⁻¹} → _))
section Fixed
variable {a : ℝ} (W : LinkWindow a) (ha : 0 < a)
theorem isProbabilityMeasure_haarProd : IsProbabilityMeasure W.haarProd := by
  unfold LinkWindow.haarProd Matrices.ComplexMatrix2.haarPi
  infer_instance
attribute [local instance] isProbabilityMeasure_haarProd
theorem faces_finite : W.faces.Finite := WilsonOperator.facesTouching_finite W.links
theorem rim_finite : W.rim.Finite := by
  refine (WilsonOperator.thickenedLinks_finite W.links).subset ?_
  rintro b ⟨⟨p, hp, hb⟩, -⟩
  exact Or.inr (Set.mem_biUnion hp hb)
theorem links_subset_positiveLinks :
    (W.links : Set (Link a)) ⊆ CutoffLattice.positiveLinks a := by
  intro b hb
  exact InfiniteLattice.mem_positiveLinks_iff.mpr (W.isPositive b hb)
theorem rim_subset_positive : W.rim ⊆ CutoffLattice.positiveLinks a :=
  W.rim_subset_positiveLinks
include ha in
theorem glue_apply_of_mem (V : W.Assignments) (U : GaugeField a) (b : W.links) :
    W.glue ha V U b = V b :=
  dif_pos b.2
include ha in
theorem glue_apply_of_notMem (V : W.Assignments) (U : GaugeField a) {b : Link a}
    (hb : b ∈ CutoffLattice.positiveLinks a) (hW : b ∉ W.links) :
    W.glue ha V U b = U b := by
  have hpos : b.IsPositivelyOriented := InfiniteLattice.mem_positiveLinks_iff.mp hb
  have hrev : b.opposite ∉ W.links := fun h' =>
    Link.opposite_not_isPositivelyOriented ha hpos (W.isPositive _ h')
  simp [LinkWindow.glue, hW, hrev]
theorem restrictInside_glue (V : W.Assignments) (U : GaugeField a) :
    W.restrictInside (W.glue ha V U) = V :=
  funext fun b => (glue_apply_of_mem W) ha V U b
theorem continuous_restrictInside : Continuous (W.restrictInside) :=
  continuous_pi fun b => continuous_linkValue (b : Link a)
variable (hv : FiniteLinkSplicing a) (hp : FaceEnergyProperties a)
  (hm : TopologicalSpace.MetrizableSpace (GaugeField a))
include hv in
theorem continuous_glue :
    Continuous fun p : W.Assignments × GaugeField a => W.glue ha p.1 p.2 :=
  (hv (W.links : Set (Link a)) (links_subset_positiveLinks W)).2.1
    (fun p => W.glue ha p.1 p.2) fun V U =>
      ⟨fun b => (glue_apply_of_mem W) ha V U b,
        fun _ hb => (glue_apply_of_notMem W) ha V U hb.1 hb.2⟩
include hv in
theorem continuous_fieldOfRimValues :
    Continuous (W.fieldOfRimValues ha) := by
  have : Finite W.rim := (rim_finite W).to_subtype
  have h := (hv W.rim (rim_subset_positive W)).2.1
    (fun p => gluedField ha W.rim_subset_positiveLinks p.1 p.2) fun V U =>
      ⟨fun b => gluedField_apply_of_mem ha _ V U b, fun b hb =>
        gluedField_apply_of_notMem ha _ V U hb⟩
  exact h.comp (continuous_id.prodMk continuous_const)
include hp in
theorem faceEnergy_sum_bounds (U : GaugeField a) :
    0 ≤ ∑ᶠ p ∈ W.faces, faceEnergy U p ∧
      ∑ᶠ p ∈ W.faces, faceEnergy U p ≤ 2 * W.faceCount := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (faces_finite W)]
  have hcard : (W.faceCount : ℝ) = ((faces_finite W).toFinset.card : ℝ) := by
    rw [LinkWindow.faceCount, Set.ncard_eq_toFinset_card _ (faces_finite W)]
  refine ⟨Finset.sum_nonneg fun p _ => ((hp p).2.1 U).1, ?_⟩
  rw [hcard]
  calc ∑ p ∈ (faces_finite W).toFinset, faceEnergy U p
      ≤ ∑ _p ∈ (faces_finite W).toFinset, (2 : ℝ) :=
        Finset.sum_le_sum fun p _ => ((hp p).2.1 U).2
    _ = 2 * ((faces_finite W).toFinset.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
include hp in
theorem windowWeight_bounds {β : ℝ} (hβ : 0 < β) (V : W.Assignments) (U : GaugeField a) :
    Real.exp (-(2 * β * W.faceCount)) ≤ W.boltzmannWeight ha β V U ∧
      W.boltzmannWeight ha β V U ≤ 1 := by
  obtain ⟨h0, h2⟩ := (faceEnergy_sum_bounds W) hp (W.glue ha V U)
  unfold LinkWindow.boltzmannWeight
  constructor
  · apply Real.exp_le_exp.mpr
    nlinarith
  · apply Real.exp_le_one_iff.mpr
    nlinarith
include hv hp in
theorem continuous_windowWeight (β : ℝ) :
    Continuous fun p : W.Assignments × GaugeField a => W.boltzmannWeight ha β p.1 p.2 := by
  unfold LinkWindow.boltzmannWeight
  have hs : (fun p : W.Assignments × GaugeField a =>
      ∑ᶠ q ∈ W.faces, faceEnergy (W.glue ha p.1 p.2) q) =
      fun p => ∑ q ∈ (faces_finite W).toFinset, faceEnergy (W.glue ha p.1 p.2) q := by
    funext p
    exact finsum_mem_eq_finite_toFinset_sum _ _
  refine Real.continuous_exp.comp (continuous_const.mul ?_)
  rw [hs]
  exact continuous_finsetSum _ fun q _ => (hp q).1.comp ((continuous_glue W) ha hv)
include hv hp in
theorem integrable_windowWeight (β : ℝ) (U : GaugeField a) :
    Integrable (fun V => W.boltzmannWeight ha β V U) W.haarProd := by
  have hcont : Continuous fun V : W.Assignments => W.boltzmannWeight ha β V U :=
    continuous_uncurry_comp (f := W.boltzmannWeight ha β) ((continuous_windowWeight W) ha hv hp β)
      continuous_id continuous_const
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
include hv hp in
theorem partition_bounds {β : ℝ} (hβ : 0 < β) (U : GaugeField a) :
    Real.exp (-(2 * β * W.faceCount)) ≤ ∫ V, W.boltzmannWeight ha β V U ∂W.haarProd ∧
      ∫ V, W.boltzmannWeight ha β V U ∂W.haarProd ≤ 1 :=
  integral_bounds_of_forall W.haarProd ((integrable_windowWeight W) ha hv hp β U) fun V =>
    (windowWeight_bounds W) ha hp hβ V U
include hv hp hm in
theorem continuous_partition {β : ℝ} (hβ : 0 < β) :
    Continuous fun U : GaugeField a => ∫ V, W.boltzmannWeight ha β V U ∂W.haarProd := by
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ))
    (fun U => ((integrable_windowWeight W) ha hv hp β U).aestronglyMeasurable)
    (fun U => ae_of_all _ fun V => ?_) (integrable_const _) (ae_of_all _ fun V => ?_)
  · have h := (windowWeight_bounds W) ha hp hβ V U
    rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le (Real.exp_pos _) h.1)]
    exact h.2
  · exact continuous_uncurry_comp (f := W.boltzmannWeight ha β)
      ((continuous_windowWeight W) ha hv hp β) continuous_const continuous_id
include hv hp hm in
theorem continuous_densityKernel {β : ℝ} (hβ : 0 < β) :
    Continuous fun p : W.Assignments × GaugeField a => W.densityKernel ha β p.1 p.2 := by
  unfold LinkWindow.densityKernel
  refine ((continuous_windowWeight W) ha hv hp β).div
    (((continuous_partition W) ha hv hp hm hβ).comp continuous_snd) fun p => ?_
  exact (lt_of_lt_of_le (Real.exp_pos _) ((partition_bounds W) ha hv hp hβ p.2).1).ne'
include hv hp in
theorem densityKernel_bounds {β : ℝ} (hβ : 0 < β) (V : W.Assignments) (U : GaugeField a) :
    Real.exp (-(2 * β * W.faceCount)) ≤ W.densityKernel ha β V U ∧
      W.densityKernel ha β V U ≤ Real.exp (2 * β * W.faceCount) := by
  obtain ⟨hw0, hw1⟩ := (windowWeight_bounds W) ha hp hβ V U
  obtain ⟨hz0, hz1⟩ := (partition_bounds W) ha hv hp hβ U
  have hzp : 0 < ∫ V, W.boltzmannWeight ha β V U ∂W.haarProd :=
    lt_of_lt_of_le (Real.exp_pos _) hz0
  have hE : Real.exp (2 * β * W.faceCount) * Real.exp (-(2 * β * W.faceCount)) = 1 := by
    rw [← Real.exp_add]; simp
  unfold LinkWindow.densityKernel
  constructor
  · rw [le_div_iff₀ hzp]
    calc Real.exp (-(2 * β * W.faceCount)) * ∫ V, W.boltzmannWeight ha β V U ∂W.haarProd
        ≤ Real.exp (-(2 * β * W.faceCount)) * 1 :=
          mul_le_mul_of_nonneg_left hz1 (Real.exp_pos _).le
      _ ≤ W.boltzmannWeight ha β V U := by simpa using hw0
  · rw [div_le_iff₀ hzp]
    calc W.boltzmannWeight ha β V U ≤ 1 := hw1
      _ = Real.exp (2 * β * W.faceCount) * Real.exp (-(2 * β * W.faceCount)) := hE.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hz0 (Real.exp_pos _).le
end Fixed
theorem abs_le_uniformNorm {X : Type*} {f : X → ℝ} (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) (x : X) :
    |f x| ≤ TestFunctions.uniformNorm f := by
  obtain ⟨C, hC⟩ := hb
  exact le_ciSup (f := fun x => ‖f x‖) ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩ x
theorem exists_abs_le_of_continuous {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {f : X → ℝ} (hf : Continuous f) : ∃ C : ℝ, ∀ x, |f x| ≤ C :=
  ⟨‖(⟨f, hf⟩ : C(X, ℝ))‖, fun x => (⟨f, hf⟩ : C(X, ℝ)).norm_coe_le_norm x⟩
section OneSpacing
variable (d : CutoffLinks.CutoffData) (W : LinkWindow d.spacing)
  (hS : GaugeFieldSpace.Statement)
  (hOp : WindowKernelOperatorProperties)
attribute [local instance] isProbabilityMeasure_haarProd
theorem stateDensity_eq_integral (ν : RealWeakState d.spacing) (V : W.Assignments) :
    W.stateDensity d.spacing_pos d.coupling ν V =
      ∫ U, W.densityKernel d.spacing_pos d.coupling V U ∂ν.measure :=
  W.stateDensity_eq_marginalDensity d.spacing_pos d.coupling ν V
include hS
theorem compactSpace_gaugeField : CompactSpace (GaugeField d.spacing) := (hS d).1.2.2.2.2.1
theorem continuous_densityKernel_of_setup :
    Continuous fun p : W.Assignments × GaugeField d.spacing =>
      W.densityKernel d.spacing_pos d.coupling p.1 p.2 :=
  continuous_densityKernel W d.spacing_pos (hS d).2.1 (hS d).2.2.1 (hS d).1.2.2.2.2.2
    d.coupling_pos
theorem densityKernel_bounds_of_setup (V : W.Assignments) (U : GaugeField d.spacing) :
    Real.exp (-(2 * d.coupling * W.faceCount)) ≤ W.densityKernel d.spacing_pos d.coupling V U ∧
      W.densityKernel d.spacing_pos d.coupling V U ≤ Real.exp (2 * d.coupling * W.faceCount) :=
  densityKernel_bounds W d.spacing_pos (hS d).2.1 (hS d).2.2.1 d.coupling_pos V U
theorem integrable_densityKernel (ν : RealWeakState d.spacing) (V : W.Assignments) :
    Integrable (fun U => W.densityKernel d.spacing_pos d.coupling V U) ν.measure := by
  have := compactSpace_gaugeField d hS
  have hcont : Continuous fun U => W.densityKernel d.spacing_pos d.coupling V U :=
    continuous_uncurry_comp (f := W.densityKernel d.spacing_pos d.coupling)
      (continuous_densityKernel_of_setup d W hS) continuous_const continuous_id
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
theorem stateDensity_bounds (ν : RealWeakState d.spacing) (V : W.Assignments) :
    Real.exp (-(2 * d.coupling * W.faceCount)) ≤ W.stateDensity d.spacing_pos d.coupling ν V ∧
      W.stateDensity d.spacing_pos d.coupling ν V ≤ Real.exp (2 * d.coupling * W.faceCount) := by
  rw [stateDensity_eq_integral]
  exact integral_bounds_of_forall ν.measure (integrable_densityKernel d W hS ν V) fun U =>
    densityKernel_bounds_of_setup d W hS V U
theorem stateDensity_pos (ν : RealWeakState d.spacing) (V : W.Assignments) :
    0 < W.stateDensity d.spacing_pos d.coupling ν V :=
  lt_of_lt_of_le (Real.exp_pos _) (stateDensity_bounds d W hS ν V).1
theorem abs_stateDensity_le (ν : RealWeakState d.spacing) (V : W.Assignments) :
    |W.stateDensity d.spacing_pos d.coupling ν V| ≤ Real.exp (2 * d.coupling * W.faceCount) := by
  rw [abs_of_pos (stateDensity_pos d W hS ν V)]
  exact (stateDensity_bounds d W hS ν V).2
theorem exists_abs_stateDensity_sub_le (μ ν : RealWeakState d.spacing) :
    ∃ C : ℝ, ∀ V : W.Assignments,
      |W.stateDensity d.spacing_pos d.coupling ν V -
        W.stateDensity d.spacing_pos d.coupling μ V| ≤ C := by
  refine ⟨Real.exp (2 * d.coupling * W.faceCount), fun V => abs_le.mpr ?_⟩
  have h1 := stateDensity_pos d W hS μ V
  have h2 := stateDensity_pos d W hS ν V
  have h3 := (stateDensity_bounds d W hS μ V).2
  have h4 := (stateDensity_bounds d W hS ν V).2
  constructor <;> linarith
theorem kernelDensityBounds_holds : W.KernelDensityBounds d.spacing_pos d.coupling := by
  refine ⟨?_, fun V η => ?_, fun ν V => stateDensity_bounds d W hS ν V, fun μ ν => ?_⟩
  · exact continuous_uncurry_comp (f := W.densityKernel d.spacing_pos d.coupling)
      (continuous_densityKernel_of_setup d W hS) continuous_fst
      ((continuous_fieldOfRimValues W d.spacing_pos (hS d).2.1).comp continuous_snd)
  · exact densityKernel_bounds_of_setup d W hS V _
  · refine iSup_le fun V => ENNReal.ofReal_le_ofReal ?_
    have hμ := stateDensity_pos d W hS μ V
    have hlow := (stateDensity_bounds d W hS μ V).1
    have hsup := abs_le_uniformNorm (exists_abs_stateDensity_sub_le d W hS μ ν) V
    have hE : Real.exp (2 * d.coupling * W.faceCount) *
        Real.exp (-(2 * d.coupling * W.faceCount)) = 1 := by
      rw [← Real.exp_add]; simp
    have hC : 1 ≤ Real.exp (2 * d.coupling * W.faceCount) *
        W.stateDensity d.spacing_pos d.coupling μ V := by
      rw [← hE]
      exact mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
    have hS0 := le_trans (abs_nonneg _) hsup
    have e : W.stateDensity d.spacing_pos d.coupling ν V /
          W.stateDensity d.spacing_pos d.coupling μ V - 1 =
        (W.stateDensity d.spacing_pos d.coupling ν V -
          W.stateDensity d.spacing_pos d.coupling μ V) /
          W.stateDensity d.spacing_pos d.coupling μ V := by
      field_simp
    rw [e, abs_div, abs_of_pos hμ, div_le_iff₀ hμ]
    calc _ ≤ _ := hsup
      _ = _ * 1 := (mul_one _).symm
      _ ≤ _ * (Real.exp (2 * d.coupling * W.faceCount) *
          W.stateDensity d.spacing_pos d.coupling μ V) :=
        mul_le_mul_of_nonneg_left hC hS0
      _ = _ := by ring
omit hS in
theorem dependsOnlyOn_comp_restrictInside (f : W.Assignments → ℝ) :
    CutoffLattice.DependsOnlyOn (fun U => f (W.restrictInside U))
      (W.links : Set (Link d.spacing)) :=
  ⟨links_subset_positiveLinks W, fun _ _ h => congrArg f
    (funext fun b => congrFun h ⟨b.1, b.2⟩)⟩
include hOp
theorem measurable_stateDensity (ν : RealWeakState d.spacing) :
    Measurable (W.stateDensity d.spacing_pos d.coupling ν) := ((hOp d W).2.2 ν).1
theorem integrable_mul_stateDensity (ν : RealWeakState d.spacing) {f : W.Assignments → ℝ}
    (hf : Measurable f) (hb : ∃ C : ℝ, ∀ V, |f V| ≤ C) :
    Integrable (fun V => f V * W.stateDensity d.spacing_pos d.coupling ν V) W.haarProd := by
  obtain ⟨C, hC⟩ := hb
  refine integrable_of_abs_le W.haarProd (hf.mul (measurable_stateDensity d W hS hOp ν))
    ⟨C * Real.exp (2 * d.coupling * W.faceCount), fun V => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC V) (abs_stateDensity_le d W hS ν V) (abs_nonneg _)
    (le_trans (abs_nonneg _) (hC V))
theorem value_realOperator (ν : RealWeakState d.spacing) {f : W.Assignments → ℝ}
    (hf : Measurable f) (hb : ∃ C : ℝ, ∀ V, |f V| ≤ C) :
    ν.value (W.realOperator d.spacing_pos d.coupling fun U => f (W.restrictInside U)) =
      ∫ V, f V * W.stateDensity d.spacing_pos d.coupling ν V ∂W.haarProd :=
  ((hOp d W).2.2 ν).2.2 f hf hb
theorem value_of_marginalOn_eq (ν : RealWeakState d.spacing)
    (hν : CutoffLinks.marginalOn (W.links : Set (Link d.spacing)) ν.measure =
      haarWithDensity (W.links : Set (Link d.spacing))
        fun V => W.stateDensity d.spacing_pos d.coupling ν V)
    {f : W.Assignments → ℝ} (hf : Measurable f) :
    ν.value (fun U => f (W.restrictInside U)) =
      ∫ V, f V * W.stateDensity d.spacing_pos d.coupling ν V ∂W.haarProd := by
  have hν' : ν.measure.map W.restrictInside =
      W.haarProd.withDensity fun V =>
        ENNReal.ofReal (W.stateDensity d.spacing_pos d.coupling ν V) := hν
  have h1 : ν.value (fun U => f (W.restrictInside U)) =
      ∫ V, f V ∂(ν.measure.map W.restrictInside) :=
    (integral_map (continuous_restrictInside W).measurable.aemeasurable
      hf.aestronglyMeasurable).symm
  have hqm : Measurable fun V => ENNReal.ofReal (W.stateDensity d.spacing_pos d.coupling ν V) :=
    ENNReal.measurable_ofReal.comp (measurable_stateDensity d W hS hOp ν)
  rw [h1, hν', integral_withDensity_eq_integral_toReal_smul hqm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun V => ?_)
  simp only [ENNReal.toReal_ofReal (stateDensity_pos d W hS ν V).le, smul_eq_mul, mul_comm]
theorem marginalOn_eq_of_continuous (ν : RealWeakState d.spacing)
    (h : ∀ f : C(W.Assignments, ℝ), ν.value (fun U => f (W.restrictInside U)) =
      ∫ V, f V * W.stateDensity d.spacing_pos d.coupling ν V ∂W.haarProd) :
    CutoffLinks.marginalOn (W.links : Set (Link d.spacing)) ν.measure =
      haarWithDensity (W.links : Set (Link d.spacing))
        fun V => W.stateDensity d.spacing_pos d.coupling ν V := by
  show ν.measure.map W.restrictInside =
    W.haarProd.withDensity fun V => ENNReal.ofReal (W.stateDensity d.spacing_pos d.coupling ν V)
  have hrm : Measurable W.restrictInside := (continuous_restrictInside W).measurable
  have hqm : Measurable fun V => ENNReal.ofReal (W.stateDensity d.spacing_pos d.coupling ν V) :=
    ENNReal.measurable_ofReal.comp (measurable_stateDensity d W hS hOp ν)
  have hqi : Integrable (W.stateDensity d.spacing_pos d.coupling ν) W.haarProd :=
    integrable_of_abs_le W.haarProd (measurable_stateDensity d W hS hOp ν)
      ⟨_, fun V => abs_stateDensity_le d W hS ν V⟩
  have : IsProbabilityMeasure (ν.measure.map W.restrictInside) :=
    Measure.isProbabilityMeasure_map hrm.aemeasurable
  have : IsFiniteMeasure (W.haarProd.withDensity fun V =>
      ENNReal.ofReal (W.stateDensity d.spacing_pos d.coupling ν V)) :=
    isFiniteMeasure_withDensity_ofReal hqi.2
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map hrm.aemeasurable f.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hqm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine (h ⟨f, f.continuous⟩).trans (integral_congr_ae (ae_of_all _ fun V => ?_))
  simp only [ENNReal.toReal_ofReal (stateDensity_pos d W hS ν V).le, smul_eq_mul, mul_comm]
  rfl
theorem marginalOn_eq_of_isInvariantState (ν : RealWeakState d.spacing)
    (h : W.IsInvariantState d.spacing_pos d.coupling ν) :
    CutoffLinks.marginalOn (W.links : Set (Link d.spacing)) ν.measure =
      haarWithDensity (W.links : Set (Link d.spacing))
        fun V => W.stateDensity d.spacing_pos d.coupling ν V := by
  refine marginalOn_eq_of_continuous d W hS hOp ν fun f => ?_
  have hcont : Continuous fun U : GaugeField d.spacing => f (W.restrictInside U) :=
    f.continuous.comp (continuous_restrictInside W)
  have heq := h ⟨fun U => f (W.restrictInside U), hcont⟩ (dependsOnlyOn_comp_restrictInside d W f)
  exact heq.symm.trans (value_realOperator d W hS hOp ν f.continuous.measurable
    (exists_abs_le_of_continuous f.continuous))
theorem isInvariantState_of_marginalOn_eq (ν : RealWeakState d.spacing)
    (hν : CutoffLinks.marginalOn (W.links : Set (Link d.spacing)) ν.measure =
      haarWithDensity (W.links : Set (Link d.spacing))
        fun V => W.stateDensity d.spacing_pos d.coupling ν V) :
    W.IsInvariantState d.spacing_pos d.coupling ν := by
  intro F hF
  have hins : Continuous fun V : W.Assignments =>
      W.glue d.spacing_pos V (trivialField d.spacing) :=
    (continuous_glue W d.spacing_pos (hS d).2.1).comp (continuous_id.prodMk continuous_const)
  have hfc : Continuous fun V : W.Assignments =>
      F (W.glue d.spacing_pos V (trivialField d.spacing)) :=
    F.continuous.comp hins
  have hFf : (F : GaugeField d.spacing → ℝ) =
      fun U => F (W.glue d.spacing_pos (W.restrictInside U) (trivialField d.spacing)) := by
    funext U
    refine hF.2 _ _ (funext fun b => ?_)
    exact (glue_apply_of_mem W d.spacing_pos (W.restrictInside U) (trivialField d.spacing)
      ⟨b.1, b.2⟩).symm
  have h1 := value_realOperator d W hS hOp ν hfc.measurable (exists_abs_le_of_continuous hfc)
  have h2 := value_of_marginalOn_eq d W hS hOp ν hν hfc.measurable
  rw [hFf]
  exact h1.trans h2.symm
end OneSpacing
section Gibbs
variable (d : CutoffLinks.CutoffData) (W : LinkWindow d.spacing)
  (hS : GaugeFieldSpace.Statement)
  (hOp : WindowKernelOperatorProperties)
attribute [local instance] isProbabilityMeasure_haarProd
theorem boltzmannWeight_eq_window (U : GaugeField d.spacing) (V : W.Assignments) :
    boltzmannWeight d.coupling W.links U V = W.boltzmannWeight d.spacing_pos d.coupling V U := by
  have h : ∀ p : ElementaryPlaquette d.spacing, faceEnergy (patch W.links V U) p =
      faceEnergy (W.glue d.spacing_pos V U) p := fun p =>
    WilsonOperator.faceEnergy_congr p fun b hb => by
      classical
      have hpos := WilsonOperator.mem_positiveLinks_of_mem_edgeList p hb
      by_cases hW : b ∈ W.links
      · have := glue_apply_of_mem W d.spacing_pos V U ⟨b, hW⟩
        simp only [patch, dif_pos hW]
        exact this.symm
      · have := glue_apply_of_notMem W d.spacing_pos V U hpos hW
        simp only [patch, dif_neg hW]
        exact this.symm
  simp only [boltzmannWeight, LinkWindow.boltzmannWeight, h]
  rfl
theorem wilsonSpecification_toReal (U : GaugeField d.spacing) {B : Set W.Assignments}
    (hB : MeasurableSet B) :
    (wilsonSpecification d.coupling W.links U B).toReal =
      ∫ V, B.indicator (fun _ => (1 : ℝ)) V * W.densityKernel d.spacing_pos d.coupling V U
        ∂W.haarProd := by
  have hw : Measurable fun V : W.Assignments =>
      ENNReal.ofReal (boltzmannWeight d.coupling W.links U V) :=
    ENNReal.measurable_ofReal.comp
      (WilsonOperator.continuous_boltzmannWeight d.coupling U).measurable
  have hpos : ∀ V : W.Assignments, 0 ≤ boltzmannWeight d.coupling W.links U V :=
    fun V => (Real.exp_pos _).le
  have hZ : partitionFunction d.coupling W.links U =
      ∫ V, W.boltzmannWeight d.spacing_pos d.coupling V U ∂W.haarProd := by
    unfold partitionFunction
    simp only [boltzmannWeight_eq_window]
    rfl
  have hZ0 : 0 ≤ partitionFunction d.coupling W.links U := integral_nonneg hpos
  have h1 : (wilsonSpecification d.coupling W.links U B).toReal =
      ∫ V, B.indicator (fun _ => (1 : ℝ)) V ∂wilsonSpecification d.coupling W.links U := by
    rw [integral_indicator_const _ hB]
    simp [Measure.real]
  rw [h1]
  unfold wilsonSpecification
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hw
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ0,
    ← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun V => ?_)
  show _ • _ • _ = _ * (W.boltzmannWeight d.spacing_pos d.coupling V U /
    ∫ V', W.boltzmannWeight d.spacing_pos d.coupling V' U ∂W.haarProd)
  rw [ENNReal.toReal_ofReal (hpos V), boltzmannWeight_eq_window, hZ]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring
include hS hOp
theorem integral_wilsonSpecification (ν : RealWeakState d.spacing) {B : Set W.Assignments}
    (hB : MeasurableSet B) :
    ∫ U, (wilsonSpecification d.coupling W.links U B).toReal ∂ν.measure =
      ∫ V, B.indicator (fun _ => (1 : ℝ)) V * W.stateDensity d.spacing_pos d.coupling ν V
        ∂W.haarProd := by
  have hb : ∃ C : ℝ, ∀ V, |B.indicator (fun _ => (1 : ℝ)) V| ≤ C := by
    refine ⟨1, fun V => ?_⟩
    by_cases h : V ∈ B <;> simp [Set.indicator, h]
  rw [← value_realOperator d W hS hOp ν (measurable_const.indicator hB) hb]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  show (wilsonSpecification d.coupling W.links U B).toReal =
    W.realOperator d.spacing_pos d.coupling _ U
  rw [wilsonSpecification_toReal d W U hB]
  simp only [LinkWindow.realOperator, restrictInside_glue, LinkWindow.rimKernel_restrictRim]
theorem marginalOn_eq_of_isGibbs (ν : RealWeakState d.spacing)
    (hg : IsGibbs d.coupling ν.measure) :
    CutoffLinks.marginalOn (W.links : Set (Link d.spacing)) ν.measure =
      haarWithDensity (W.links : Set (Link d.spacing))
        fun V => W.stateDensity d.spacing_pos d.coupling ν V := by
  show ν.measure.map W.restrictInside =
    W.haarProd.withDensity fun V => ENNReal.ofReal (W.stateDensity d.spacing_pos d.coupling ν V)
  have hrm : Measurable W.restrictInside := (continuous_restrictInside W).measurable
  have hqm : Measurable fun V => ENNReal.ofReal (W.stateDensity d.spacing_pos d.coupling ν V) :=
    ENNReal.measurable_ofReal.comp (measurable_stateDensity d W hS hOp ν)
  have hqi : Integrable (W.stateDensity d.spacing_pos d.coupling ν) W.haarProd :=
    integrable_of_abs_le W.haarProd (measurable_stateDensity d W hS hOp ν)
      ⟨_, fun V => abs_stateDensity_le d W hS ν V⟩
  have : IsProbabilityMeasure (ν.measure.map W.restrictInside) :=
    Measure.isProbabilityMeasure_map hrm.aemeasurable
  have : IsFiniteMeasure (W.haarProd.withDensity fun V =>
      ENNReal.ofReal (W.stateDensity d.spacing_pos d.coupling ν V)) :=
    isFiniteMeasure_withDensity_ofReal hqi.2
  have hle : exteriorSigma W.links ≤ (inferInstance : MeasurableSpace (GaugeField d.spacing)) :=
    iSup₂_le fun b _ => (continuous_linkValue b).measurable.comap_le
  refine Measure.ext fun B hB => ?_
  have hae := hg.2 W.links W.isPositive B hB
  have hpre : MeasurableSet (restrictTo W.links ⁻¹' B) := hrm hB
  have h1 : ∫ U, (wilsonSpecification d.coupling W.links U B).toReal ∂ν.measure =
      (ν.measure (restrictTo W.links ⁻¹' B)).toReal := by
    rw [integral_congr_ae hae, integral_condExp hle, integral_indicator_const _ hpre]
    simp [Measure.real]
  have h2 := integral_wilsonSpecification d W hS hOp ν hB
  have h3 : ∫ V, B.indicator (fun _ => (1 : ℝ)) V *
        W.stateDensity d.spacing_pos d.coupling ν V ∂W.haarProd =
      ((W.haarProd.withDensity fun V =>
        ENNReal.ofReal (W.stateDensity d.spacing_pos d.coupling ν V)) B).toReal := by
    have h4 : ((W.haarProd.withDensity fun V =>
        ENNReal.ofReal (W.stateDensity d.spacing_pos d.coupling ν V)) B).toReal =
        ∫ V, B.indicator (fun _ => (1 : ℝ)) V ∂(W.haarProd.withDensity fun V =>
          ENNReal.ofReal (W.stateDensity d.spacing_pos d.coupling ν V)) := by
      rw [integral_indicator_const _ hB]
      simp [Measure.real]
    rw [h4, integral_withDensity_eq_integral_toReal_smul hqm
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun V => ?_)
    simp only [ENNReal.toReal_ofReal (stateDensity_pos d W hS ν V).le, smul_eq_mul, mul_comm]
  have h5 : ((ν.measure.map W.restrictInside) B).toReal = ((W.haarProd.withDensity fun V =>
      ENNReal.ofReal (W.stateDensity d.spacing_pos d.coupling ν V)) B).toReal := by
    rw [Measure.map_apply hrm hB]
    exact (h1.symm.trans h2).trans h3
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h5
theorem abs_value_sub_le_stateDistance (μ ν : RealWeakState d.spacing)
    (hμ : W.IsInvariantState d.spacing_pos d.coupling μ)
    (hν : W.IsInvariantState d.spacing_pos d.coupling ν)
    {F : W.Assignments → ℝ} (hF : Measurable F) (hB : ∃ C : ℝ, ∀ V, |F V| ≤ C) :
    ENNReal.ofReal |μ.value (fun U => F (W.restrictInside U)) -
        ν.value (fun U => F (W.restrictInside U))| ≤
      W.stateDistance d.spacing_pos d.coupling μ ν *
        ENNReal.ofReal (μ.value fun U => |F (W.restrictInside U)|) := by
  have hmμ := marginalOn_eq_of_isInvariantState d W hS hOp μ hμ
  have hmν := marginalOn_eq_of_isInvariantState d W hS hOp ν hν
  have habs : Measurable fun V => |F V| := continuous_abs.measurable.comp hF
  have hBabs : ∃ C : ℝ, ∀ V, |(fun V => |F V|) V| ≤ C := by
    obtain ⟨C, hC⟩ := hB
    exact ⟨C, fun V => by simpa using hC V⟩
  have h1 := value_of_marginalOn_eq d W hS hOp μ hmμ hF
  have h2 := value_of_marginalOn_eq d W hS hOp ν hmν hF
  have h3 : μ.value (fun U => |F (W.restrictInside U)|) =
      ∫ V, |F V| * W.stateDensity d.spacing_pos d.coupling μ V ∂W.haarProd :=
    value_of_marginalOn_eq d W hS hOp μ hmμ habs
  have hD : W.stateDistance d.spacing_pos d.coupling μ ν ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((kernelDensityBounds_holds d W hS).2.2.2 μ ν)
  have hd : ∀ V, |W.stateDensity d.spacing_pos d.coupling ν V /
        W.stateDensity d.spacing_pos d.coupling μ V - 1| ≤
      (W.stateDistance d.spacing_pos d.coupling μ ν).toReal := fun V =>
    (ENNReal.ofReal_le_iff_le_toReal hD).mp
      (le_iSup (fun V => ENNReal.ofReal
        |W.stateDensity d.spacing_pos d.coupling ν V /
          W.stateDensity d.spacing_pos d.coupling μ V - 1|) V)
  have i1 := integrable_mul_stateDensity d W hS hOp μ hF hB
  have i2 := integrable_mul_stateDensity d W hS hOp ν hF hB
  have i3 := integrable_mul_stateDensity d W hS hOp μ habs hBabs
  have main : |(∫ V, F V * W.stateDensity d.spacing_pos d.coupling μ V ∂W.haarProd) -
        ∫ V, F V * W.stateDensity d.spacing_pos d.coupling ν V ∂W.haarProd| ≤
      (W.stateDistance d.spacing_pos d.coupling μ ν).toReal *
        ∫ V, |F V| * W.stateDensity d.spacing_pos d.coupling μ V ∂W.haarProd := by
    rw [← integral_sub i1 i2, ← integral_const_mul]
    refine le_trans (le_of_eq (Real.norm_eq_abs _).symm)
      (norm_integral_le_of_norm_le (i3.const_mul _) (ae_of_all _ fun V => ?_))
    have hq := stateDensity_pos d W hS μ V
    have e : F V * W.stateDensity d.spacing_pos d.coupling μ V -
          F V * W.stateDensity d.spacing_pos d.coupling ν V =
        -F V * W.stateDensity d.spacing_pos d.coupling μ V *
          (W.stateDensity d.spacing_pos d.coupling ν V /
            W.stateDensity d.spacing_pos d.coupling μ V - 1) := by
      field_simp
      ring
    rw [Real.norm_eq_abs, e, abs_mul, abs_mul, abs_neg, abs_of_pos hq]
    calc |F V| * W.stateDensity d.spacing_pos d.coupling μ V *
          |W.stateDensity d.spacing_pos d.coupling ν V /
            W.stateDensity d.spacing_pos d.coupling μ V - 1|
        ≤ |F V| * W.stateDensity d.spacing_pos d.coupling μ V *
            (W.stateDistance d.spacing_pos d.coupling μ ν).toReal :=
          mul_le_mul_of_nonneg_left (hd V) (mul_nonneg (abs_nonneg _) hq.le)
      _ = _ := by ring
  rw [h1, h2, h3]
  calc _ ≤ ENNReal.ofReal ((W.stateDistance d.spacing_pos d.coupling μ ν).toReal *
        ∫ V, |F V| * W.stateDensity d.spacing_pos d.coupling μ V ∂W.haarProd) :=
        ENNReal.ofReal_le_ofReal main
    _ = _ := by rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hD]
omit hOp
theorem stateDensityContinuous_holds : W.StateDensityContinuous d.spacing_pos d.coupling := by
  intro ν ν₀ hconv
  have := compactSpace_gaugeField d hS
  let Φ : C(W.Assignments, C(GaugeField d.spacing, ℝ)) :=
    ContinuousMap.curry ⟨fun p => W.densityKernel d.spacing_pos d.coupling p.1 p.2,
      continuous_densityKernel_of_setup d W hS⟩
  have hq : ∀ (ρ : RealWeakState d.spacing) (V : W.Assignments),
      W.stateDensity d.spacing_pos d.coupling ρ V = ρ.value (Φ V) :=
    fun ρ V => stateDensity_eq_integral d W ρ V
  have hlip : ∀ (ρ : RealWeakState d.spacing) (G H : C(GaugeField d.spacing, ℝ)),
      |ρ.value G - ρ.value H| ≤ ‖G - H‖ := by
    intro ρ G H
    have iG : Integrable G ρ.measure :=
      G.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have iH : Integrable H ρ.measure :=
      H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    show |(∫ U, G U ∂ρ.measure) - ∫ U, H U ∂ρ.measure| ≤ _
    rw [← integral_sub iG iH]
    have h := norm_integral_le_of_norm_le_const (μ := ρ.measure) (f := fun U => G U - H U)
      (C := ‖G - H‖) (ae_of_all _ fun U => (G - H).norm_coe_le_norm U)
    simpa using h
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨t, -, htf, hcov⟩ :=
    (isCompact_range Φ.continuous).finite_cover_balls (show 0 < ε / 4 by linarith)
  have hev : ∀ᶠ i in atTop, ∀ x ∈ t, |(ν i).value x - ν₀.value x| < ε / 4 :=
    (eventually_all_finite htf).mpr fun x _ =>
      (Metric.tendsto_nhds.mp (hconv x) (ε / 4) (by linarith)).mono fun i hi => by
        rw [Real.dist_eq] at hi
        exact hi
  filter_upwards [hev] with i hi
  have hb : TestFunctions.uniformNorm (fun V : W.Assignments =>
      W.stateDensity d.spacing_pos d.coupling (ν i) V -
        W.stateDensity d.spacing_pos d.coupling ν₀ V) ≤ 3 * ε / 4 := by
    refine ciSup_le fun V => ?_
    obtain ⟨x, hx, hV⟩ := Set.mem_iUnion₂.mp (hcov (Set.mem_range_self V))
    have hdV : ‖Φ V - x‖ < ε / 4 := by
      rw [Metric.mem_ball, dist_eq_norm] at hV
      exact hV
    have h1 := abs_le.mp (hlip (ν i) (Φ V) x)
    have h2 := abs_le.mp (hlip ν₀ (Φ V) x)
    have h3 := abs_lt.mp (hi x hx)
    show ‖W.stateDensity d.spacing_pos d.coupling (ν i) V -
      W.stateDensity d.spacing_pos d.coupling ν₀ V‖ ≤ _
    rw [hq, hq, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  have h0 : 0 ≤ TestFunctions.uniformNorm (fun V : W.Assignments =>
      W.stateDensity d.spacing_pos d.coupling (ν i) V -
        W.stateDensity d.spacing_pos d.coupling ν₀ V) :=
    Real.iSup_nonneg fun V => norm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith
end Gibbs
section Sides
theorem torusSide_le_torusSide_iff {L m n : ℕ} (hL : 1 < L) :
    PeriodicLattice.torusSide L m ≤ PeriodicLattice.torusSide L n ↔ m ≤ n := by
  have h1 : (1 : ℝ) < L := by exact_mod_cast hL
  have h := pow_le_pow_iff_right₀ (a := (L : ℝ)) (n := m) (m := n) h1
  unfold PeriodicLattice.torusSide
  constructor
  · intro hle
    exact h.mp (by linarith)
  · intro hle
    have := h.mpr hle
    linarith
def cutoffDataOf (L K : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) (β : ℝ)
    (hβ : 0 < β) (m : ℕ+) : CutoffLinks.CutoffData :=
  { L := L, isAdmissible := hL, K := ⟨K, hK⟩, m := m, coupling := β, coupling_pos := hβ }
variable {L K : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) {β : ℝ}
  (hβ : 0 < β) (hCov : LatticeCovering.CoveringStatement)
include hCov hL hK hβ in
theorem isProbabilityMeasure_liftedWilsonMeasure {m : ℕ} (hm : 0 < m) :
    IsProbabilityMeasure (liftedWilsonMeasure L m K β) :=
  (hCov ⟨⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩, β, hβ⟩).2.2.1.2.2.2.2.2
variable (W : LinkWindow (PeriodicLattice.meshSize L (K : ℤ)))
  (ha : 0 < PeriodicLattice.meshSize L (K : ℤ))
  (hS : GaugeFieldSpace.Statement)
theorem mem_admissibleSides_iff {ε x : ℝ} : x ∈ W.admissibleSides ha β ε ↔
    ∃ mε : ℕ, 0 < mε ∧ x = PeriodicLattice.torusSide L mε ∧
      ∀ m : ℕ, 0 < m → x ≤ PeriodicLattice.torusSide L m →
        ∃ ρ : RealWeakState (PeriodicLattice.meshSize L (K : ℤ)),
          ρ.measure = liftedWilsonMeasure L m K β ∧
            W.infStateDistance ha β ρ (limitsOfLiftedMeasures L K β) ≤ ENNReal.ofReal ε :=
  Iff.rfl
include hL hK hβ hCov hS
theorem liftedWilsonInvariant_holds
    (hCB : Covering.CoveringProperties)
    (hEq : LiftedEquilibriumEquation.Statement) {m : ℕ} (hm : 0 < m) :
    W.LiftedWilsonInvariant ha β m := by
  intro hle
  have hpr := isProbabilityMeasure_liftedWilsonMeasure hL hK hβ hCov hm
  refine ⟨⟨liftedWilsonMeasure L m K β, hpr⟩, rfl, ?_⟩
  intro F hF
  have hL1 : 1 < L := by have := hL.2; omega
  have hcov : Covering.LeastTorusSideIsAttained W :=
    ((hCB ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩).2.2.2.2.2.2 W).2.1
  have hmem : PeriodicLattice.torusSide L m ∈ W.torusSidesOfInjection := by
    rw [hcov.2]
    exact ⟨⟨m, hm, rfl⟩, hle⟩
  obtain ⟨m', -, hside, hE⟩ := hmem
  have hmm : m' = m := le_antisymm ((torusSide_le_torusSide_iff hL1).mp hside.le)
    ((torusSide_le_torusSide_iff hL1).mp hside.ge)
  subst hmm
  have hcompact : CompactSpace (GaugeField (PeriodicLattice.meshSize L (K : ℤ))) :=
    compactSpace_gaugeField (cutoffDataOf L K hL hK β hβ 1) hS
  have hsub : ((W.links : Set (Link (PeriodicLattice.meshSize L (K : ℤ)))) ∪ W.rim) ⊆
      CutoffLattice.positiveLinks (PeriodicLattice.meshSize L (K : ℤ)) :=
    Set.union_subset (links_subset_positiveLinks W) (rim_subset_positive W)
  have hbd : ∃ C : ℝ, ∀ U, |F U| ≤ C := exists_abs_le_of_continuous F.continuous
  exact hEq (cutoffDataOf L K hL hK β hβ ⟨m', hm⟩) W _
    (W.links.finite_toSet.union (rim_finite W)) hsub Set.subset_union_left
    Set.subset_union_right hE F F.continuous.measurable hbd
    ⟨hsub, fun U U' h => hF.2 U U' (funext fun b => congrFun h ⟨b.1, Or.inl b.2⟩)⟩
theorem isLeast_admissibleSides
    (hCp : EveryStateSequenceHasWeaklyConvergentSubsequence.Statement)
    (hTor : LimitSetIsNonemptyClosed) {ε : ℝ} (hε : 0 < ε) :
    IsLeast (W.admissibleSides ha β ε) (W.leastAdmissibleSide ha β ε) := by
  have hL1 : 1 < L := by have := hL.2; omega
  have hpr : ∀ n : ℕ, IsProbabilityMeasure (liftedWilsonMeasure L (n + 1) K β) := fun n =>
    isProbabilityMeasure_liftedWilsonMeasure hL hK hβ hCov (Nat.succ_pos n)
  let ρ : ℕ → RealWeakState (PeriodicLattice.meshSize L (K : ℤ)) := fun n =>
    ⟨liftedWilsonMeasure L (n + 1) K β, hpr n⟩
  have hA := kernelDensityBounds_holds (cutoffDataOf L K hL hK β hβ 1) W hS
  have key : ∃ N : ℕ, ∀ n ≥ N, W.infStateDistance ha β (ρ n)
      (limitsOfLiftedMeasures L K β) ≤ ENNReal.ofReal ε := by
    by_contra hcon
    push Not at hcon
    have hfreq : ∃ᶠ n in atTop, ENNReal.ofReal ε < W.infStateDistance ha β (ρ n)
        (limitsOfLiftedMeasures L K β) := frequently_atTop.mpr hcon
    obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨i, ν, hi, hconv⟩ := hCp ⟨L, hL, ⟨K, hK⟩, 1⟩ (fun k : ℕ+ => ρ (φ k))
    let ψ : ℕ → ℕ := fun n => φ (i n.succPNat)
    have hψ : StrictMono ψ := fun a b hab =>
      hφ ((PNat.coe_lt_coe _ _).mpr (hi (Nat.succPNat_strictMono hab)))
    have htn : Tendsto Nat.succPNat atTop atTop :=
      tendsto_atTop.2 fun b => (eventually_ge_atTop (b : ℕ)).mono fun n hn => by
        rw [← PNat.coe_le_coe, Nat.succPNat_coe]
        omega
    have hcv : RealWeakState.TendstoWeakly (fun n => ρ (ψ n)) ν := fun F =>
      (hconv F).comp htn
    have hν : ν ∈ limitsOfLiftedMeasures L K β := by
      have h := (hTor ⟨L, hL, ⟨K, hK⟩, 1⟩ β hβ).1
      have hlim : ν ∈ subsequentialLimits L K β :=
        ⟨fun n => ψ n + 1, fun n => ρ (ψ n), fun a b hab => Nat.succ_lt_succ (hψ hab),
          fun n => Nat.succ_le_succ (Nat.zero_le _), fun n => rfl, hcv⟩
      exact (Set.ext_iff.mp h ν).mpr hlim
    have hdc := stateDensityContinuous_holds (cutoffDataOf L K hL hK β hβ 1) W hS
      (fun n => ρ (ψ n)) ν hcv
    have hlim : Tendsto (fun n => Real.exp (2 * β * W.faceCount) *
        TestFunctions.uniformNorm fun V : W.Assignments =>
          W.stateDensity ha β (ρ (ψ n)) V - W.stateDensity ha β ν V) atTop (𝓝 0) := by
      have h := hdc.const_mul (Real.exp (2 * β * W.faceCount))
      rw [mul_zero] at h
      exact h
    obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hε).exists
    have h1 : W.infStateDistance ha β (ρ (ψ n)) (limitsOfLiftedMeasures L K β) ≤
        W.stateDistance ha β (ρ (ψ n)) ν := iInf₂_le ν hν
    have h2 : W.stateDistance ha β (ρ (ψ n)) ν ≤
        ENNReal.ofReal (Real.exp (2 * β * W.faceCount) *
          TestFunctions.uniformNorm fun V : W.Assignments =>
            W.stateDensity ha β ν V - W.stateDensity ha β (ρ (ψ n)) V) :=
      hA.2.2.2 (ρ (ψ n)) ν
    have h3 : (TestFunctions.uniformNorm fun V : W.Assignments =>
          W.stateDensity ha β ν V - W.stateDensity ha β (ρ (ψ n)) V) =
        TestFunctions.uniformNorm fun V : W.Assignments =>
          W.stateDensity ha β (ρ (ψ n)) V - W.stateDensity ha β ν V := by
      unfold TestFunctions.uniformNorm
      simp only [norm_sub_rev]
    rw [h3] at h2
    exact absurd ((hP (i n.succPNat)).trans_le (h1.trans (h2.trans
      (ENNReal.ofReal_le_ofReal hn.le)))) (lt_irrefl _)
  obtain ⟨N, hN⟩ := key
  have hne : ∃ m : ℕ, 0 < m ∧ PeriodicLattice.torusSide L m ∈ W.admissibleSides ha β ε := by
    refine ⟨N + 1, Nat.succ_pos N, (mem_admissibleSides_iff W ha).mpr
      ⟨N + 1, Nat.succ_pos N, rfl, fun m hm hle => ?_⟩⟩
    have hmN : N + 1 ≤ m := (torusSide_le_torusSide_iff hL1).mp hle
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    exact ⟨ρ n, rfl, hN n (by omega)⟩
  classical
  have hmin := Nat.find_spec hne
  have hleast : IsLeast (W.admissibleSides ha β ε)
      (PeriodicLattice.torusSide L (Nat.find hne)) := by
    refine ⟨hmin.2, ?_⟩
    intro x hx
    obtain ⟨mx, hmx, rfl, hrest⟩ := (mem_admissibleSides_iff W ha).mp hx
    exact (torusSide_le_torusSide_iff hL1).mpr (Nat.find_min' hne ⟨hmx, hx⟩)
  rw [LinkWindow.leastAdmissibleSide, hleast.csInf_eq]
  exact hleast
end Sides
theorem statement_holds
    (hS : GaugeFieldSpace.Statement)
    (hOp : WindowKernelOperatorProperties)
    (hCB : Covering.CoveringProperties)
    (hEq : LiftedEquilibriumEquation.Statement)
    (hCp : EveryStateSequenceHasWeaklyConvergentSubsequence.Statement)
    (hTor : LimitSetIsNonemptyClosed)
    (hCov : LatticeCovering.CoveringStatement) : Statement := by
  intro L K hL hK β hβ W ha
  exact ⟨kernelDensityBounds_holds (cutoffDataOf L K hL hK β hβ 1) W hS,
    fun ν h => marginalOn_eq_of_isInvariantState (cutoffDataOf L K hL hK β hβ 1) W hS hOp ν h,
    fun ν hg => isInvariantState_of_marginalOn_eq (cutoffDataOf L K hL hK β hβ 1) W hS hOp ν
      (marginalOn_eq_of_isGibbs (cutoffDataOf L K hL hK β hβ 1) W hS hOp ν hg),
    fun m hm => liftedWilsonInvariant_holds hL hK hβ hCov W ha hS hCB hEq hm,
    fun μ ν hμ hν F hF hB => abs_value_sub_le_stateDistance (cutoffDataOf L K hL hK β hβ 1) W hS
      hOp μ ν hμ hν hF hB,
    stateDensityContinuous_holds (cutoffDataOf L K hL hK β hβ 1) W hS,
    fun ε hε => isLeast_admissibleSides hL hK hβ hCov W ha hS hCp hTor hε⟩
end YangMills.Construction.WindowDensities

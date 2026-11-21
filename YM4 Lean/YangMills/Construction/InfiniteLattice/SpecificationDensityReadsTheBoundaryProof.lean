import YangMills.Construction.InfiniteLattice.FactsOfOneLatticeAtOneSpacing
import YangMills.Construction.InfiniteLattice.SpecificationDensityReadsTheBoundary
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace FixedSpacing.ConditionalDensityDependsOnRim
attribute [local instance] WilsonOperator.secondCountable_specialUnitary
variable (hF : BasicFacts) (D : Setup) (W : LinkWindow D.mesh)
theorem isProbabilityMeasure_haarProd : IsProbabilityMeasure W.haarProd := by
  unfold LinkWindow.haarProd Matrices.ComplexMatrix2.haarPi
  infer_instance
theorem continuous_linkValue (b : Link D.mesh) : Continuous fun U : D.Fields => U b :=
  (continuous_apply b).comp
    (continuous_subtype_val :
      Continuous (Subtype.val : {U : Link D.mesh → Matrices.ComplexMatrix2.specialUnitary //
        ∀ b, U b.opposite = (U b)⁻¹} → _))
theorem windowGlue_apply_of_mem (V : W.Assignments) (U : D.Fields) (b : W.links) :
    W.glue D.mesh_pos V U b = V b :=
  dif_pos b.2
theorem windowGlue_apply_of_not_mem (V : W.Assignments) (U : D.Fields) {b : Link D.mesh}
    (hb : b ∈ D.links) (hW : b ∉ W.links) : W.glue D.mesh_pos V U b = U b := by
  have hpos : b.IsPositivelyOriented := InfiniteLattice.mem_positiveLinks_iff.mp hb
  have hopp : b.opposite ∉ W.links := fun h' =>
    Link.opposite_not_isPositivelyOriented D.mesh_pos hpos (W.isPositive _ h')
  simp [LinkWindow.glue, hW, hopp]
theorem isLinkSet_rim : IsLinkSet W.rim := by
  rintro b ⟨⟨p, -, hb⟩, -⟩
  exact WilsonOperator.mem_positiveLinks_of_mem_edgeList p hb
theorem rim_finite : W.rim.Finite := by
  refine (WilsonOperator.thickenedLinks_finite W.links).subset ?_
  rintro b ⟨⟨p, hp, hb⟩, -⟩
  exact Or.inr (mem_iUnion₂.mpr ⟨p, hp, hb⟩)
theorem localAction_congr_of_eqOn {U U' : D.Fields}
    (h : ∀ b ∈ (W.links : Set (Link D.mesh)) ∪ W.rim, U b = U' b) :
    D.localAction W U = D.localAction W U' := by
  unfold Setup.localAction
  congr 1
  refine finsum_mem_congr rfl fun p hp =>
    WilsonOperator.faceEnergy_congr p fun b hb => h b ?_
  by_cases hW : b ∈ W.links
  · exact Or.inl hW
  · exact Or.inr ⟨⟨p, hp, hb⟩, hW⟩
theorem localAction_windowGlue_congr (V : W.Assignments) {U U' : D.Fields}
    (h : ∀ b ∈ W.rim, U b = U' b) :
    D.localAction W (W.glue D.mesh_pos V U) =
      D.localAction W (W.glue D.mesh_pos V U') := by
  refine localAction_congr_of_eqOn D W fun b hb => ?_
  by_cases hW : b ∈ W.links
  · rw [windowGlue_apply_of_mem D W V U ⟨b, hW⟩, windowGlue_apply_of_mem D W V U' ⟨b, hW⟩]
  · rcases hb with hb | hb
    · exact absurd hb hW
    · have hpos := isLinkSet_rim D W hb
      rw [windowGlue_apply_of_not_mem D W V U hpos hW, windowGlue_apply_of_not_mem D W V U' hpos hW]
      exact h b hb
theorem localPartition_congr_of_eqOn {U U' : D.Fields} (h : ∀ b ∈ W.rim, U b = U' b) :
    D.localPartition W U = D.localPartition W U' := by
  unfold Setup.localPartition
  simp only [localAction_windowGlue_congr D W _ h]
theorem conditionalDensity_congr_of_eqOn (V : W.Assignments) {U U' : D.Fields}
    (h : ∀ b ∈ W.rim, U b = U' b) :
    D.conditionalDensity W V U = D.conditionalDensity W V U' := by
  unfold Setup.conditionalDensity
  rw [localAction_windowGlue_congr D W V h, localPartition_congr_of_eqOn D W h]
include hF in
theorem continuous_windowGlue :
    Continuous fun x : W.Assignments × D.Fields => W.glue D.mesh_pos x.1 x.2 := by
  obtain ⟨hu, c, hc, hE⟩ := (hF D).2.1.2.2.2.2.2 (W.links : Set (Link D.mesh)) W.links.finite_toSet
    (Setup.isLinkSet_window W)
  have key : ∀ x : W.Assignments × D.Fields, c x = W.glue D.mesh_pos x.1 x.2 := fun x =>
    (hu x.1 x.2).unique (hE x.1 x.2)
      ⟨fun b => windowGlue_apply_of_mem D W x.1 x.2 ⟨b.1, b.2⟩,
        fun b hb => windowGlue_apply_of_not_mem D W x.1 x.2 hb.1 hb.2⟩
  have e : (fun x : W.Assignments × D.Fields => W.glue D.mesh_pos x.1 x.2) = c :=
    funext fun x => (key x).symm
  rw [e]
  exact hc
include hF in
theorem continuous_faceEnergy_field (p : ElementaryPlaquette D.mesh) :
    Continuous fun U : D.Fields => faceEnergy U p := by
  obtain ⟨-, -, φ, hφ, he⟩ := ((hF D).2.2.2.2.2.1 p).1
  have hc : Continuous fun U : D.Fields => ((faceEnergy U p : ℝ) : ℂ) := by
    have e : (fun U : D.Fields => ((faceEnergy U p : ℝ) : ℂ)) =
        fun U => φ (restrictField U (CutoffLattice.faceLinks p)) := funext he
    rw [e]
    exact hφ.comp (continuous_pi fun b => continuous_linkValue D b.1)
  have := Complex.continuous_re.comp hc
  simpa [Function.comp_def] using this
theorem localAction_eq_finsetSum (U : D.Fields) :
    D.localAction W U =
      -D.β * ∑ p ∈ (Setup.finite_faces W).toFinset, faceEnergy U p := by
  unfold Setup.localAction
  rw [finsum_mem_eq_finite_toFinset_sum _ (Setup.finite_faces W)]
include hF in
theorem continuous_localAction : Continuous (D.localAction W) := by
  have e : D.localAction W = fun U : D.Fields =>
      -D.β * ∑ p ∈ (Setup.finite_faces W).toFinset, faceEnergy U p :=
    funext (localAction_eq_finsetSum D W)
  rw [e]
  exact continuous_const.mul (continuous_finsetSum _ fun p _ => continuous_faceEnergy_field hF D p)
include hF in
theorem localAction_mem_bounds (U : D.Fields) :
    -(2 * D.β * (W.faceCount : ℝ)) ≤ D.localAction W U ∧ D.localAction W U ≤ 0 := by
  have hβ := D.β_pos
  have hn : (W.faceCount : ℝ) = ((Setup.finite_faces W).toFinset.card : ℝ) := by
    rw [LinkWindow.faceCount, Set.ncard_eq_toFinset_card _ (Setup.finite_faces W)]
  have hb := fun p : ElementaryPlaquette D.mesh => ((hF D).2.2.2.2.2.1 p).2 U
  have h0 : 0 ≤ ∑ p ∈ (Setup.finite_faces W).toFinset, faceEnergy U p :=
    Finset.sum_nonneg fun p _ => (hb p).1
  have h2 : ∑ p ∈ (Setup.finite_faces W).toFinset, faceEnergy U p ≤
      2 * (W.faceCount : ℝ) := by
    rw [hn]
    calc ∑ p ∈ (Setup.finite_faces W).toFinset, faceEnergy U p
        ≤ ∑ _p ∈ (Setup.finite_faces W).toFinset, (2 : ℝ) :=
          Finset.sum_le_sum fun p _ => (hb p).2
      _ = 2 * ((Setup.finite_faces W).toFinset.card : ℝ) := by simp [mul_comm]
  rw [localAction_eq_finsetSum]
  constructor <;> nlinarith
include hF in
theorem continuous_glueWeight :
    Continuous fun x : W.Assignments × D.Fields =>
      Real.exp (D.localAction W (W.glue D.mesh_pos x.1 x.2)) :=
  Real.continuous_exp.comp ((continuous_localAction hF D W).comp (continuous_windowGlue hF D W))
include hF in
theorem continuous_glueWeight_fst (U' : D.Fields) :
    Continuous fun V : W.Assignments =>
      Real.exp (D.localAction W (W.glue D.mesh_pos V U')) := by
  have h : Continuous fun V : W.Assignments => W.glue D.mesh_pos V U' :=
    (continuous_windowGlue hF D W).comp (continuous_id.prodMk continuous_const)
  exact Real.continuous_exp.comp ((continuous_localAction hF D W).comp h)
include hF in
theorem integrable_glueWeight (U' : D.Fields) :
    Integrable (fun V : W.Assignments =>
      Real.exp (D.localAction W (W.glue D.mesh_pos V U'))) W.haarProd := by
  have := isProbabilityMeasure_haarProd D W
  refine Integrable.of_bound (continuous_glueWeight_fst hF D W U').measurable.aestronglyMeasurable 1
    (ae_of_all _ fun V => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (localAction_mem_bounds hF D W _).2
include hF in
theorem localPartition_mem_bounds (U' : D.Fields) :
    Real.exp (-(2 * D.β * (W.faceCount : ℝ))) ≤ D.localPartition W U' ∧
      D.localPartition W U' ≤ 1 := by
  have := isProbabilityMeasure_haarProd D W
  have hi := integrable_glueWeight hF D W U'
  constructor
  · have h := integral_mono (integrable_const (Real.exp (-(2 * D.β * (W.faceCount : ℝ))))) hi
      fun V => Real.exp_le_exp.mpr (localAction_mem_bounds hF D W (W.glue D.mesh_pos V U')).1
    simpa [Setup.localPartition] using h
  · have h := integral_mono hi (integrable_const (1 : ℝ))
      fun V => Real.exp_le_one_iff.mpr (localAction_mem_bounds hF D W (W.glue D.mesh_pos V U')).2
    simpa [Setup.localPartition] using h
include hF in
theorem localPartition_pos (U' : D.Fields) : 0 < D.localPartition W U' :=
  lt_of_lt_of_le (Real.exp_pos _) (localPartition_mem_bounds hF D W U').1
include hF in
theorem integral_over_window_of_continuous {Φ : W.Assignments × D.Fields → ℂ} (hΦ : Continuous Φ) :
    Continuous (fun U' : D.Fields => ∫ V, Φ (V, U') ∂W.haarProd) ∧
      ∀ 𝓜 : Set (Link D.mesh), 𝓜.Finite → IsLinkSet 𝓜 →
        (∀ (V : W.Assignments) (U' U'' : D.Fields),
          restrictField U' 𝓜 = restrictField U'' 𝓜 → Φ (V, U') = Φ (V, U'')) →
        FactorsThroughFinite 𝓜 (fun U' : D.Fields => ∫ V, Φ (V, U') ∂W.haarProd) := by
  obtain ⟨-, hc, -, -, -, hr⟩ := (hF D).2.2.2.2.1.2 (W.links : Set (Link D.mesh)) W.links.finite_toSet
    (Setup.isLinkSet_window W) Φ hΦ
  exact ⟨hc, hr⟩
theorem ofReal_localPartition (U' : D.Fields) :
    ((D.localPartition W U' : ℝ) : ℂ) =
      ∫ V, ((Real.exp (D.localAction W (W.glue D.mesh_pos V U')) : ℝ) : ℂ) ∂W.haarProd :=
  integral_ofReal.symm
include hF in
theorem continuous_complexGlueWeight :
    Continuous fun x : W.Assignments × D.Fields =>
      ((Real.exp (D.localAction W (W.glue D.mesh_pos x.1 x.2)) : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (continuous_glueWeight hF D W)
include hF in
theorem continuous_localPartition : Continuous (D.localPartition W) := by
  have h := (integral_over_window_of_continuous hF D W (continuous_complexGlueWeight hF D W)).1
  have e : (fun U' : D.Fields => ∫ V, ((Real.exp (D.localAction W
      (W.glue D.mesh_pos V U')) : ℝ) : ℂ) ∂W.haarProd) =
      fun U' => ((D.localPartition W U' : ℝ) : ℂ) :=
    funext fun U' => (ofReal_localPartition D W U').symm
  have h' : Continuous fun U' : D.Fields => ((D.localPartition W U' : ℝ) : ℂ) := by
    rw [← e]
    exact h
  have := Complex.continuous_re.comp h'
  simpa [Function.comp_def] using this
include hF in
theorem factorsThroughFinite_localPartition :
    FactorsThroughFinite W.rim (fun U' : D.Fields => ((D.localPartition W U' : ℝ) : ℂ)) := by
  have e : (fun U' : D.Fields => ((D.localPartition W U' : ℝ) : ℂ)) =
      fun U' => ∫ V, ((Real.exp (D.localAction W
        (W.glue D.mesh_pos V U')) : ℝ) : ℂ) ∂W.haarProd :=
    funext (ofReal_localPartition D W)
  rw [e]
  refine (integral_over_window_of_continuous hF D W (continuous_complexGlueWeight hF D W)).2 W.rim
    (rim_finite D W) (isLinkSet_rim D W) fun V U' U'' h => ?_
  show ((Real.exp _ : ℝ) : ℂ) = ((Real.exp _ : ℝ) : ℂ)
  rw [localAction_windowGlue_congr D W V fun b hb => congrFun h ⟨b, hb⟩]
include hF in
theorem factorsThroughFinite_localAction :
    FactorsThroughFinite ((W.links : Set (Link D.mesh)) ∪ W.rim)
      (fun U : D.Fields => ((D.localAction W U : ℝ) : ℂ)) := by
  refine (hF D).2.2.2.2.1.1 _ (W.links.finite_toSet.union (rim_finite D W))
    (union_subset (Setup.isLinkSet_window W) (isLinkSet_rim D W)) _
    (Complex.continuous_ofReal.comp (continuous_localAction hF D W)) fun U U' h => ?_
  exact congrArg Complex.ofReal (localAction_congr_of_eqOn D W fun b hb => congrFun h ⟨b, hb⟩)
include hF in
theorem continuous_conditionalDensity :
    Continuous fun x : W.Assignments × D.Fields => D.conditionalDensity W x.1 x.2 := by
  show Continuous fun x : W.Assignments × D.Fields =>
    Real.exp (D.localAction W (W.glue D.mesh_pos x.1 x.2)) / D.localPartition W x.2
  exact (continuous_glueWeight hF D W).div ((continuous_localPartition hF D W).comp continuous_snd)
    fun x => (localPartition_pos hF D W x.2).ne'
include hF in
theorem exists_continuous_of_rim :
    ∃ φ : W.Assignments × LinkVariables W.rim → ℝ, Continuous φ ∧
      ∀ (V : W.Assignments) (U' : D.Fields),
        D.conditionalDensity W V U' = φ (V, restrictField U' W.rim) := by
  obtain ⟨-, c, hc, hE⟩ := (hF D).2.1.2.2.2.2.2 W.rim (rim_finite D W)
    (isLinkSet_rim D W)
  refine ⟨fun x => D.conditionalDensity W x.1 (c (x.2, trivialField D.mesh)), ?_,
    fun V U' => ?_⟩
  · have hext : Continuous fun ξ : LinkVariables W.rim => c (ξ, trivialField D.mesh) :=
      hc.comp (continuous_id.prodMk continuous_const)
    have hp : Continuous fun x : W.Assignments × LinkVariables W.rim =>
        ((x.1, c (x.2, trivialField D.mesh)) : W.Assignments × D.Fields) :=
      continuous_fst.prodMk (hext.comp continuous_snd)
    have h := (continuous_conditionalDensity hF D W).comp hp
    exact h
  · exact conditionalDensity_congr_of_eqOn D W V fun b hb =>
      ((hE (restrictField U' W.rim) (trivialField D.mesh)).1 ⟨b, hb⟩).symm
include hF in
theorem conditionalDensity_mem_bounds (V : W.Assignments) (U' : D.Fields) :
    Real.exp (-(2 * D.β * (W.faceCount : ℝ))) ≤ D.conditionalDensity W V U' ∧
      D.conditionalDensity W V U' ≤ Real.exp (2 * D.β * (W.faceCount : ℝ)) := by
  obtain ⟨hz1, hz2⟩ := localPartition_mem_bounds hF D W U'
  obtain ⟨he1, he2⟩ := localAction_mem_bounds hF D W (W.glue D.mesh_pos V U')
  have hz0 := localPartition_pos hF D W U'
  have e1 := Real.exp_le_exp.mpr he1
  have e2 := Real.exp_le_one_iff.mpr he2
  unfold Setup.conditionalDensity
  constructor
  · rw [le_div_iff₀ hz0]
    exact (mul_le_of_le_one_right (Real.exp_pos _).le hz2).trans e1
  · rw [div_le_iff₀ hz0]
    have h := mul_le_mul_of_nonneg_left hz1 (Real.exp_pos (2 * D.β * (W.faceCount : ℝ))).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
    exact e2.trans h
include hF in
theorem integral_conditionalDensity (U' : D.Fields) :
    ∫ V, D.conditionalDensity W V U' ∂W.haarProd = 1 := by
  have hz0 := localPartition_pos hF D W U'
  simp only [Setup.conditionalDensity]
  rw [integral_div]
  exact div_self hz0.ne'
theorem exp_localAction_windowGlue (V : W.Assignments) (U' : D.Fields) :
    Real.exp (D.localAction W (W.glue D.mesh_pos V U')) =
      boltzmannWeight D.β W.links U' V := by
  have h : ∀ p : ElementaryPlaquette D.mesh, faceEnergy (W.glue D.mesh_pos V U') p =
      faceEnergy (patch W.links V U') p := fun p =>
    WilsonOperator.faceEnergy_congr p fun b hb => by
      have hpos := WilsonOperator.mem_positiveLinks_of_mem_edgeList p hb
      by_cases hW : b ∈ W.links
      · rw [windowGlue_apply_of_mem D W V U' ⟨b, hW⟩]
        simp only [patch, dif_pos hW]
      · rw [windowGlue_apply_of_not_mem D W V U' hpos hW]
        simp only [patch, dif_neg hW]
  simp only [Setup.localAction, boltzmannWeight, LinkWindow.faces, h]
theorem localPartition_eq_partitionFunction (U' : D.Fields) :
    D.localPartition W U' = partitionFunction D.β W.links U' := by
  unfold Setup.localPartition partitionFunction
  simp only [exp_localAction_windowGlue]
  rfl
include hF in
theorem withDensity_conditionalDensity (U' : D.Fields) :
    W.haarProd.withDensity (fun V => ENNReal.ofReal (D.conditionalDensity W V U')) =
      wilsonSpecification D.β W.links U' := by
  have hz0 := localPartition_pos hF D W U'
  have hm : Measurable fun V : W.links → Matrices.ComplexMatrix2.specialUnitary =>
      ENNReal.ofReal (boltzmannWeight D.β W.links U' V) :=
    ENNReal.measurable_ofReal.comp (WilsonOperator.continuous_boltzmannWeight D.β U').measurable
  have e : (fun V => ENNReal.ofReal (D.conditionalDensity W V U')) =
      (ENNReal.ofReal (partitionFunction D.β W.links U'))⁻¹ •
        fun V => ENNReal.ofReal (boltzmannWeight D.β W.links U' V) := by
    funext V
    rw [← localPartition_eq_partitionFunction, Pi.smul_apply, smul_eq_mul,
      ← exp_localAction_windowGlue, Setup.conditionalDensity, div_eq_inv_mul,
      ENNReal.ofReal_mul (inv_nonneg.mpr hz0.le), ENNReal.ofReal_inv_of_pos hz0]
  rw [e, withDensity_smul _ hm]
  rfl
include hF in
theorem factorsThroughFinite_conditionalKernel {𝓕 : Set (Link D.mesh)} {F : D.Fields → ℂ}
    (hR : FactorsThroughFinite 𝓕 F) :
    FactorsThroughFinite (W.rim ∪ (𝓕 \ (W.links : Set (Link D.mesh)))) (D.conditionalKernel W F) := by
  obtain ⟨hfin, hset, φ, hφ, he⟩ := hR
  have hFc : Continuous F := by
    have e : F = fun U => φ (restrictField U 𝓕) := funext he
    rw [e]
    exact hφ.comp (continuous_pi fun b => continuous_linkValue D b.1)
  have hΦ : Continuous fun x : W.Assignments × D.Fields =>
      F (W.glue D.mesh_pos x.1 x.2) * ((D.conditionalDensity W x.1 x.2 : ℝ) : ℂ) :=
    (hFc.comp (continuous_windowGlue hF D W)).mul
      (Complex.continuous_ofReal.comp (continuous_conditionalDensity hF D W))
  refine (integral_over_window_of_continuous hF D W hΦ).2 _
    ((rim_finite D W).union (hfin.subset sdiff_subset))
    (union_subset (isLinkSet_rim D W) (sdiff_subset.trans hset)) fun V U' U'' h => ?_
  have hb : ∀ b ∈ W.rim ∪ (𝓕 \ (W.links : Set (Link D.mesh))), U' b = U'' b :=
    fun b hb => congrFun h ⟨b, hb⟩
  have h1 : F (W.glue D.mesh_pos V U') = F (W.glue D.mesh_pos V U'') := by
    rw [he, he]
    congr 1
    funext b
    show W.glue D.mesh_pos V U' b.1 = W.glue D.mesh_pos V U'' b.1
    by_cases hW : b.1 ∈ W.links
    · rw [windowGlue_apply_of_mem D W V U' ⟨b.1, hW⟩, windowGlue_apply_of_mem D W V U'' ⟨b.1, hW⟩]
    · rw [windowGlue_apply_of_not_mem D W V U' (hset b.2) hW,
        windowGlue_apply_of_not_mem D W V U'' (hset b.2) hW]
      exact hb _ (Or.inr ⟨b.2, hW⟩)
  have h2 := conditionalDensity_congr_of_eqOn D W V (U := U') (U' := U'') fun b hb' => hb b (Or.inl hb')
  show F _ * _ = F _ * _
  rw [h1, h2]
theorem holds (hF : BasicFacts) : Statement := fun D W =>
  ⟨⟨factorsThroughFinite_localAction hF D W, factorsThroughFinite_localPartition hF D W,
      exists_continuous_of_rim hF D W, conditionalDensity_mem_bounds hF D W,
      integral_conditionalDensity hF D W⟩,
    withDensity_conditionalDensity hF D W,
    fun _ ⟨_, hR⟩ => ⟨_, factorsThroughFinite_conditionalKernel hF D W hR⟩,
    fun _ _ hR => by
      simpa using factorsThroughFinite_conditionalKernel hF D W hR⟩
end FixedSpacing.ConditionalDensityDependsOnRim
end YangMills.Construction

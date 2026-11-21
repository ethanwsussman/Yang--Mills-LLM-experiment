import YangMills.Construction.InfiniteLattice.FactsOfOneLatticeAtOneSpacing
import YangMills.Construction.InfiniteLattice.ObjectsAtOneSpacingAndThoseOfTheDefinitionsProof
import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsAtACutoffProof
import YangMills.Construction.Matrices.FunctionsAndOperatorsOfSeveralVariablesOnG
import YangMills.Construction.Matrices.UnitaryLogarithmClosedForm
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open YangMills.Construction.InfiniteLattice YangMills.Construction.GibbsAtFixedSpacing
open YangMills.Construction.Matrices
open scoped Topology
noncomputable section
namespace YangMills.Construction.FixedSpacing.BasicFactsProof
variable {a : ℝ}
theorem continuous_eval_link (b : Link a) : Continuous fun U : GaugeField a => U b := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.continuous_eval_link <;> assumption
theorem continuous_of_forall_link {X : Type*} [TopologicalSpace X] {f : X → GaugeField a}
    (h : ∀ b, Continuous fun x => f x b) : Continuous f := by apply _root_.YangMills.Construction.InfiniteLattice.FieldSpace.continuous_of_forall_link <;> assumption
instance instT2SpaceGaugeField : T2Space (GaugeField a) :=
  inferInstanceAs
    (T2Space {U : Link a → ComplexMatrix2.specialUnitary // ∀ b, U b.opposite = (U b)⁻¹})
instance instSecondCountableGaugeField : SecondCountableTopology (GaugeField a) :=
  TopologicalSpace.Subtype.secondCountableTopology
    {U : Link a → ComplexMatrix2.specialUnitary | ∀ b, U b.opposite = (U b)⁻¹}
instance instCompactSpaceGaugeField : CompactSpace (GaugeField a) := by
  have hclosed :
      IsClosed {U : Link a → ComplexMatrix2.specialUnitary | ∀ b, U b.opposite = (U b)⁻¹} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun b => isClosed_eq (continuous_apply _) (continuous_apply b).inv
  exact isCompact_iff_compactSpace.mp hclosed.isCompact
theorem continuous_gluedField (ha : 0 < a) {S : Set (Link a)} (hS : S ⊆ positiveLinkSet a) :
    Continuous fun q : LinkVariables S × GaugeField a => gluedField ha hS q.1 q.2 := by
  refine continuous_of_forall_link fun b => ?_
  classical
  by_cases hb : b ∈ S
  · have e : (fun q : LinkVariables S × GaugeField a => gluedField ha hS q.1 q.2 b) =
        fun q => q.1 ⟨b, hb⟩ := funext fun q => dif_pos hb
    rw [e]
    exact (continuous_apply _).comp continuous_fst
  · by_cases hb' : b.opposite ∈ S
    · have e : (fun q : LinkVariables S × GaugeField a => gluedField ha hS q.1 q.2 b) =
          fun q => (q.1 ⟨b.opposite, hb'⟩)⁻¹ :=
        funext fun q => (dif_neg hb).trans (dif_pos hb')
      rw [e]
      exact ((continuous_apply _).comp continuous_fst).inv
    · have e : (fun q : LinkVariables S × GaugeField a => gluedField ha hS q.1 q.2 b) =
          fun q => q.2 b := funext fun q => (dif_neg hb).trans (dif_neg hb')
      rw [e]
      exact (continuous_eval_link b).comp continuous_snd
theorem restrictField_positiveLinks_injective (ha : 0 < a) :
    Function.Injective fun U : GaugeField a =>
      restrictField U (positiveLinkSet a) := by
  intro U U' h
  have h' : restrictField U (positiveLinkSet a) =
      restrictField U' (positiveLinkSet a) := h
  have hS : positiveLinkSet a ⊆ positiveLinkSet a := subset_refl _
  have e₁ := eq_gluedField ha hS (restrictField U (positiveLinkSet a)) U U
    (fun _ => rfl) (fun b hb => absurd hb.1 hb.2)
  have e₂ := eq_gluedField ha hS (restrictField U' (positiveLinkSet a)) U U'
    (fun _ => rfl) (fun b hb => absurd hb.1 hb.2)
  calc U = _ := e₁
    _ = _ := by rw [h']
    _ = U' := e₂.symm
theorem isHomeomorph_restrictField (ha : 0 < a) :
    IsHomeomorph fun U : GaugeField a => restrictField U (positiveLinkSet a) := by
  refine isHomeomorph_iff_continuous_bijective.2
    ⟨continuous_pi fun b => continuous_eval_link b.1,
      restrictField_positiveLinks_injective ha, fun V => ?_⟩
  exact ⟨gluedField ha (subset_refl _) V (trivialField a),
    funext fun b => gluedField_apply_of_mem ha (subset_refl _) V _ b⟩
theorem factorsThroughFinite_mono {𝓕 𝓕' : Set (Link a)} {F : GaugeField a → ℂ}
    (h : FactorsThroughFinite 𝓕 F) (hs : 𝓕 ⊆ 𝓕') (hf : 𝓕'.Finite) (hb : IsLinkSet 𝓕') :
    FactorsThroughFinite 𝓕' F := by
  obtain ⟨-, -, φ, hφ, hF⟩ := h
  exact ⟨hf, hb, fun V => φ fun b => V ⟨b.1, hs b.2⟩,
    hφ.comp (continuous_pi fun b => continuous_apply _), fun U => hF U⟩
theorem finiteLinkFunctions_map₂_mem (op : ℂ → ℂ → ℂ)
    (hop : Continuous fun z : ℂ × ℂ => op z.1 z.2)
    {F F' : GaugeField a → ℂ} (hF : F ∈ finiteLinkFunctions a)
    (hF' : F' ∈ finiteLinkFunctions a) :
    (fun U => op (F U) (F' U)) ∈ finiteLinkFunctions a := by
  obtain ⟨𝓕, h⟩ := hF
  obtain ⟨𝓕', h'⟩ := hF'
  have hfin : (𝓕 ∪ 𝓕').Finite := h.1.union h'.1
  have hset : IsLinkSet (𝓕 ∪ 𝓕') := union_subset h.2.1 h'.2.1
  obtain ⟨-, -, φ, hφ, hF⟩ := factorsThroughFinite_mono h subset_union_left hfin hset
  obtain ⟨-, -, φ', hφ', hF'⟩ := factorsThroughFinite_mono h' subset_union_right hfin hset
  exact ⟨𝓕 ∪ 𝓕', hfin, hset, fun V => op (φ V) (φ' V), hop.comp (hφ.prodMk hφ'), fun U => by
    simp only [hF U, hF' U]⟩
def localSubalgebra (a : ℝ) : Subalgebra ℂ (GaugeField a → ℂ) where
  carrier := finiteLinkFunctions a
  mul_mem' := fun hF hF' => finiteLinkFunctions_map₂_mem (· * ·) continuous_mul hF hF'
  add_mem' := fun hF hF' => finiteLinkFunctions_map₂_mem (· + ·) continuous_add hF hF'
  algebraMap_mem' := fun c =>
    ⟨∅, finite_empty, empty_subset _, fun _ => c, continuous_const, fun _ => rfl⟩
theorem continuous_of_mem_finiteLinkFunctions {F : GaugeField a → ℂ}
    (hF : F ∈ finiteLinkFunctions a) : Continuous F := by
  obtain ⟨𝓕, -, -, φ, hφ, hF⟩ := hF
  have e : F = fun U => φ (restrictField U 𝓕) := funext hF
  rw [e]
  exact hφ.comp (continuous_pi fun b => continuous_eval_link b.1)
def localStarSubalgebra (a : ℝ) : StarSubalgebra ℂ C(GaugeField a, ℂ) where
  carrier := {f | ⇑f ∈ finiteLinkFunctions a}
  mul_mem' := fun hF hF' => finiteLinkFunctions_map₂_mem (· * ·) continuous_mul hF hF'
  add_mem' := fun hF hF' => finiteLinkFunctions_map₂_mem (· + ·) continuous_add hF hF'
  algebraMap_mem' := fun c =>
    ⟨∅, finite_empty, empty_subset _, fun _ => c, continuous_const, fun _ => rfl⟩
  star_mem' := by
    rintro f ⟨𝓕, h₁, h₂, φ, hφ, hf⟩
    exact ⟨𝓕, h₁, h₂, fun V => star (φ V), continuous_star.comp hφ, fun U => by
      simp only [ContinuousMap.star_apply, hf U]⟩
theorem localStarSubalgebra_separatesPoints (ha : 0 < a) :
    (localStarSubalgebra a).SeparatesPoints := by
  intro U U' hne
  obtain ⟨b, hb⟩ : ∃ b : positiveLinkSet a, U b ≠ U' b := by
    by_contra hc
    push Not at hc
    exact hne (restrictField_positiveLinks_injective ha (funext hc))
  obtain ⟨i, j, hij⟩ : ∃ i j, (U b : ComplexMatrix2) i j ≠ (U' b : ComplexMatrix2) i j := by
    by_contra hc
    push Not at hc
    exact hb (Subtype.ext (Matrix.ext hc))
  have hval : Continuous fun g : ComplexMatrix2.specialUnitary =>
      ((g : ComplexMatrix2.specialUnitary) : ComplexMatrix2) i j :=
    continuous_subtype_val.matrix_elem i j
  have hcont : Continuous fun W : GaugeField a =>
      ((W b : ComplexMatrix2.specialUnitary) : ComplexMatrix2) i j :=
    hval.comp (continuous_eval_link b.1)
  refine ⟨_, ⟨⟨_, hcont⟩, ?_, rfl⟩, hij⟩
  refine ⟨{b.1}, finite_singleton _, singleton_subset_iff.2 b.2, fun V =>
    ((V ⟨b.1, rfl⟩ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) i j, ?_, fun W => rfl⟩
  exact hval.comp (continuous_apply _)
theorem exists_local_uniform_approx (ha : 0 < a) {F : GaugeField a → ℂ} (hF : Continuous F)
    {ε : ℝ} (hε : 0 < ε) : ∃ F' ∈ finiteLinkFunctions a, ∀ U, ‖F U - F' U‖ ≤ ε := by
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (localStarSubalgebra a) (localStarSubalgebra_separatesPoints ha)
  have hmem : (⟨F, hF⟩ : C(GaugeField a, ℂ)) ∈
      closure (localStarSubalgebra a : Set C(GaugeField a, ℂ)) := by
    exact show (⟨F, hF⟩ : C(GaugeField a, ℂ)) ∈ (localStarSubalgebra a).topologicalClosure from by
      rw [htop]
      exact StarSubalgebra.mem_top
  obtain ⟨g, hg, hd⟩ := Metric.mem_closure_iff.1 hmem ε hε
  refine ⟨g, hg, fun U => ?_⟩
  have h := ContinuousMap.dist_apply_le_dist (f := ⟨F, hF⟩) (g := g) U
  rw [dist_eq_norm] at h
  exact h.trans hd.le
abbrev toMeasure (ν : BorelProb a) : Measure (GaugeField a) :=
  Subtype.val (p := fun ν : Measure (GaugeField a) => IsProbabilityMeasure ν) ν
instance instIsProbabilityMeasureToMeasure (ν : BorelProb a) :
    IsProbabilityMeasure (toMeasure ν) :=
  Subtype.property (p := fun ν : Measure (GaugeField a) => IsProbabilityMeasure ν) ν
theorem exists_norm_bound_of_continuous {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : X → ℂ} (hF : Continuous F) : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  exact ⟨C, fun x => hC x (mem_univ x)⟩
theorem norm_integral_sub_integral_le (ν : BorelProb a) {F F' : GaugeField a → ℂ}
    (hF : Continuous F) (hF' : Continuous F') {ε : ℝ} (h : ∀ U, ‖F U - F' U‖ ≤ ε) :
    ‖ν.integral F - ν.integral F'‖ ≤ ε := by apply _root_.YangMills.Construction.InfiniteLattice.FixedSpacing.norm_integral_sub_le_of_pointwise <;> assumption
theorem tendstoWeak_of_local (ha : 0 < a) (ν : ℕ → BorelProb a) (ν₀ : BorelProb a)
    (h : ∀ F ∈ finiteLinkFunctions a,
      Tendsto (fun i => (ν i).integral F) atTop (𝓝 (ν₀.integral F))) :
    BorelProb.TendstoWeak ν ν₀ := by
  intro F hF
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨F', hF', hnear⟩ := exists_local_uniform_approx ha hF (half_pos (half_pos hε))
  have hc' := continuous_of_mem_finiteLinkFunctions hF'
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (h F' hF') (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have h₁ := norm_integral_sub_integral_le (ν n) hF hc' hnear
  have h₂ := norm_integral_sub_integral_le ν₀ hF hc' hnear
  have h₃ := hN n hn
  rw [dist_eq_norm] at h₃ ⊢
  have e : (ν n).integral F - ν₀.integral F = ((ν n).integral F - (ν n).integral F') +
      ((ν n).integral F' - ν₀.integral F') - (ν₀.integral F - ν₀.integral F') := by ring
  rw [e]
  have := norm_sub_le (((ν n).integral F - (ν n).integral F') +
      ((ν n).integral F' - ν₀.integral F')) (ν₀.integral F - ν₀.integral F')
  have := norm_add_le ((ν n).integral F - (ν n).integral F') ((ν n).integral F' - ν₀.integral F')
  linarith
theorem ext_of_continuous (ν ν' : BorelProb a)
    (h : ∀ F : GaugeField a → ℂ, Continuous F → ν.integral F = ν'.integral F) : ν = ν' := by
  refine Subtype.ext (ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_))
  have hc : Continuous fun U => ((f U : ℝ) : ℂ) := Complex.continuous_ofReal.comp f.continuous
  have e := h _ hc
  have e₁ : ν.integral (fun U => ((f U : ℝ) : ℂ)) = ((∫ U, f U ∂toMeasure ν : ℝ) : ℂ) :=
    integral_complex_ofReal
  have e₂ : ν'.integral (fun U => ((f U : ℝ) : ℂ)) = ((∫ U, f U ∂toMeasure ν' : ℝ) : ℂ) :=
    integral_complex_ofReal
  rw [e₁, e₂] at e
  exact_mod_cast e
theorem ext_of_local (ha : 0 < a) (ν ν' : BorelProb a)
    (h : ∀ F ∈ finiteLinkFunctions a, ν.integral F = ν'.integral F) : ν = ν' := by
  refine ext_of_continuous ν ν' fun F hF => ?_
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨F', hF', hnear⟩ := exists_local_uniform_approx ha hF (half_pos hε)
  have hc' := continuous_of_mem_finiteLinkFunctions hF'
  have h₁ := norm_integral_sub_integral_le ν hF hc' hnear
  have h₂ := norm_integral_sub_integral_le ν' hF hc' hnear
  rw [dist_eq_norm]
  have e : ν.integral F - ν'.integral F = (ν.integral F - ν.integral F') -
      (ν'.integral F - ν'.integral F') := by rw [h F' hF']; ring
  rw [e]
  have := norm_sub_le (ν.integral F - ν.integral F') (ν'.integral F - ν'.integral F')
  linarith
theorem continuous_integral_apply {F : GaugeField a → ℂ} (hF : Continuous F) :
    Continuous fun ν : BorelProb a => ν.integral F :=
  continuous_iInf_dom (i := ⟨F, hF⟩) continuous_induced_dom
instance instT2SpaceBorelProb : T2Space (BorelProb a) := by
  have hinj : Function.Injective fun (ν : BorelProb a) (F : continuousFns a) => ν.integral F.1 :=
    fun ν ν' h => ext_of_continuous ν ν' fun F hF => congrFun h ⟨F, hF⟩
  exact T2Space.of_injective_continuous hinj
    (continuous_pi fun F => continuous_integral_apply F.2)
def ofProbabilityMeasure (ν : ProbabilityMeasure (GaugeField a)) : BorelProb a :=
  ⟨(ν : Measure (GaugeField a)), ν.2⟩
theorem continuous_ofProbabilityMeasure : Continuous (ofProbabilityMeasure (a := a)) := by
  refine continuous_iInf_rng.2 fun F => continuous_induced_rng.2 ?_
  exact continuous_iff_continuousAt.2 fun _ =>
    (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 tendsto_id
      (BoundedContinuousFunction.mkOfCompact ⟨F.1, F.2⟩)
theorem isHomeomorph_ofProbabilityMeasure : IsHomeomorph (ofProbabilityMeasure (a := a)) := by
  refine isHomeomorph_iff_continuous_bijective.2 ⟨continuous_ofProbabilityMeasure, ?_, ?_⟩
  · intro ν ν' h
    exact Subtype.ext (congrArg (toMeasure (a := a)) h)
  · intro ν
    exact ⟨⟨toMeasure ν, instIsProbabilityMeasureToMeasure ν⟩, rfl⟩
instance instCompactSpaceBorelProb : CompactSpace (BorelProb a) :=
  isHomeomorph_ofProbabilityMeasure.homeomorph.compactSpace
instance instMetrizableSpaceBorelProb : TopologicalSpace.MetrizableSpace (BorelProb a) :=
  isHomeomorph_ofProbabilityMeasure.homeomorph.symm.isEmbedding.metrizableSpace
theorem tendsto_nhds_iff_tendstoWeak (ν : ℕ → BorelProb a) (ν₀ : BorelProb a) :
    Tendsto ν atTop (𝓝 ν₀) ↔ BorelProb.TendstoWeak ν ν₀ := by apply _root_.YangMills.Construction.InfiniteLattice.FixedSpacing.tendsto_iff_tendstoWeak <;> assumption
theorem frequently_mem_iff_isSubseqWeakLimit (ν : ℕ → BorelProb a) (ν₀ : BorelProb a) :
    (∀ N ∈ 𝓝 ν₀, {i : ℕ | 1 ≤ i ∧ ν i ∈ N}.Infinite) ↔ BorelProb.IsSubseqWeakLimit ν ν₀ := by
  constructor
  · intro h
    have hcl : MapClusterPt ν₀ atTop ν := by
      refine mapClusterPt_iff_frequently.2 fun N hN => ?_
      exact Nat.frequently_atTop_iff_infinite.2 ((h N hN).mono fun i hi => hi.2)
    obtain ⟨φ, hφ, ht⟩ := hcl.tendsto_subseq
    exact ⟨fun k => φ (k + 1), fun i j hij => hφ (by omega),
      fun k => (Nat.succ_le_succ (Nat.zero_le k)).trans hφ.le_apply,
      (tendsto_nhds_iff_tendstoWeak _ _).1 (ht.comp (tendsto_add_atTop_nat 1))⟩
  · rintro ⟨φ, hφ, h1, hw⟩ N hN
    obtain ⟨k₀, hk⟩ :=
      eventually_atTop.1 (((tendsto_nhds_iff_tendstoWeak _ _).2 hw).eventually hN)
    refine ((Set.Ici_infinite k₀).image hφ.injective.injOn).mono ?_
    rintro _ ⟨k, hk', rfl⟩
    exact ⟨h1 k, hk k hk'⟩
theorem exists_isSubseqWeakLimit (ν : ℕ → BorelProb a) :
    ∃ ν₀ : BorelProb a, BorelProb.IsSubseqWeakLimit ν ν₀ := by
  obtain ⟨ν₀, -, φ, hφ, ht⟩ := isCompact_univ.tendsto_subseq (x := ν) fun _ => mem_univ _
  exact ⟨ν₀, fun k => φ (k + 1), fun i j hij => hφ (by omega),
    fun k => (Nat.succ_le_succ (Nat.zero_le k)).trans hφ.le_apply,
    (tendsto_nhds_iff_tendstoWeak _ _).1 (ht.comp (tendsto_add_atTop_nat 1))⟩
theorem exists_countable_uniformly_dense :
    ∃ 𝓓 : Set (GaugeField a → ℂ), 𝓓.Countable ∧ 𝓓 ⊆ continuousFns a ∧
      ∀ F ∈ continuousFns a, ∀ ε : ℝ, 0 < ε → ∃ F' ∈ 𝓓, ∀ U, ‖F U - F' U‖ ≤ ε := by
  refine ⟨range fun k => ⇑(TopologicalSpace.denseSeq C(GaugeField a, ℂ) k),
    countable_range _, ?_, ?_⟩
  · rintro _ ⟨k, rfl⟩
    exact ContinuousMap.continuous _
  · intro F hF ε hε
    obtain ⟨k, hk⟩ := (TopologicalSpace.denseRange_denseSeq C(GaugeField a, ℂ)).exists_dist_lt
      (⟨F, hF⟩ : C(GaugeField a, ℂ)) hε
    refine ⟨_, ⟨k, rfl⟩, fun U => ?_⟩
    have h := ContinuousMap.dist_apply_le_dist (f := ⟨F, hF⟩)
      (g := TopologicalSpace.denseSeq C(GaugeField a, ℂ) k) U
    rw [dist_eq_norm] at h
    exact h.trans hk.le
theorem factorsThroughFinite_of_continuous (ha : 0 < a) {𝓜 : Set (Link a)} (hfin : 𝓜.Finite)
    (hset : IsLinkSet 𝓜) {F : GaugeField a → ℂ} (hF : Continuous F)
    (hdep : DependsOnlyOnLinks 𝓜 F) : FactorsThroughFinite 𝓜 F :=
  ⟨hfin, hset, fun V => F (gluedField ha hset V (trivialField a)),
    hF.comp ((continuous_gluedField ha hset).comp (continuous_id.prodMk continuous_const)),
    fun _ => hdep _ _ (funext fun b => (gluedField_apply_of_mem ha hset _ _ b).symm)⟩
instance instIsProbabilityMeasureHaar (𝓛 : Set (Link a)) :
    IsProbabilityMeasure (LinkVariables.haarMeasure 𝓛) :=
  SpinHarmonics.haarPi_isProbabilityMeasure 𝓛
theorem haar_integral_facts (𝓛 : Set (Link a))
    (Φ : LinkVariables 𝓛 × GaugeField a → ℂ) (hΦ : Continuous Φ) :
    (∀ U' : GaugeField a, Integrable (fun V => Φ (V, U')) (LinkVariables.haarMeasure 𝓛)) ∧
    Continuous (fun U' : GaugeField a => ∫ V, Φ (V, U') ∂LinkVariables.haarMeasure 𝓛) ∧
    BddAbove (range fun z => ‖Φ z‖) ∧
    BddAbove (range fun U' : GaugeField a => ‖∫ V, Φ (V, U') ∂LinkVariables.haarMeasure 𝓛‖) ∧
    TestFunctions.uniformNorm
        (fun U' : GaugeField a => ∫ V, Φ (V, U') ∂LinkVariables.haarMeasure 𝓛) ≤
      TestFunctions.uniformNorm Φ := by
  obtain ⟨C, hC⟩ := exists_norm_bound_of_continuous hΦ
  have hbdd : BddAbove (range fun z => ‖Φ z‖) := ⟨C, by rintro _ ⟨z, rfl⟩; exact hC z⟩
  have hsec : ∀ U' : GaugeField a, Continuous fun V : LinkVariables 𝓛 => Φ (V, U') :=
    fun U' => hΦ.comp (continuous_id.prodMk continuous_const)
  have hle : ∀ U' : GaugeField a,
      ‖∫ V, Φ (V, U') ∂LinkVariables.haarMeasure 𝓛‖ ≤ TestFunctions.uniformNorm Φ := fun U' => by
    simpa using norm_integral_le_of_norm_le_const (μ := LinkVariables.haarMeasure 𝓛)
      (f := fun V => Φ (V, U')) (C := TestFunctions.uniformNorm Φ)
      (ae_of_all _ fun V => le_ciSup hbdd (V, U'))
  refine ⟨fun U' => Integrable.of_bound (hsec U').aestronglyMeasurable C
      (ae_of_all _ fun V => hC _), ?_, hbdd, ⟨_, by rintro _ ⟨U', rfl⟩; exact hle U'⟩, ?_⟩
  · refine continuous_of_dominated (F := fun U' V => Φ (V, U')) (bound := fun _ => C)
      (fun U' => (hsec U').aestronglyMeasurable) (fun _ => ae_of_all _ fun _ => hC _)
      (integrable_const C) (ae_of_all _ fun V => ?_)
    exact hΦ.comp (continuous_const.prodMk continuous_id)
  · have : Nonempty (GaugeField a) := ⟨trivialField a⟩
    exact ciSup_le hle
theorem factorsThroughFinite_faceEnergy (p : ElementaryPlaquette a) :
    FactorsThroughFinite (CutoffLattice.faceLinks p)
      (fun U : GaugeField a => ((faceEnergy U p : ℝ) : ℂ)) := by
  have h₁ : Link.forwardFrom p.corner p.lowAxis ∈ CutoffLattice.faceLinks p := by
    simp [CutoffLattice.faceLinks, ElementaryPlaquette.edges]
  have h₂ : Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis ∈
      CutoffLattice.faceLinks p := by
    simp [CutoffLattice.faceLinks, ElementaryPlaquette.edges]
  have h₃ : Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis ∈
      CutoffLattice.faceLinks p := by
    simp [CutoffLattice.faceLinks, ElementaryPlaquette.edges]
  have h₄ : Link.forwardFrom p.corner p.highAxis ∈ CutoffLattice.faceLinks p := by
    simp [CutoffLattice.faceLinks, ElementaryPlaquette.edges]
  refine ⟨List.finite_toSet _, ?_, fun V => ((1 - (1 / 2) * (ComplexMatrix2.fullTrace
      ((V ⟨_, h₁⟩ * V ⟨_, h₂⟩ * (V ⟨_, h₃⟩)⁻¹ * (V ⟨_, h₄⟩)⁻¹ :
        ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re : ℝ) : ℂ),
    ?_, fun U => rfl⟩
  · intro b hb
    simp only [CutoffLattice.faceLinks, ElementaryPlaquette.edges, List.mem_cons,
      List.not_mem_nil, or_false, mem_ofPred_eq] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  · have htr : Continuous fun g : ComplexMatrix2.specialUnitary =>
        (ComplexMatrix2.fullTrace (g : ComplexMatrix2)).re :=
      Complex.continuous_re.comp (continuous_subtype_val.matrix_trace)
    have hv : ∀ b : CutoffLattice.faceLinks p,
        Continuous fun V : LinkVariables (CutoffLattice.faceLinks p) => V b :=
      fun b => continuous_apply b
    have hprod : Continuous fun V : LinkVariables (CutoffLattice.faceLinks p) =>
        (V ⟨_, h₁⟩ * V ⟨_, h₂⟩ * (V ⟨_, h₃⟩)⁻¹ * (V ⟨_, h₄⟩)⁻¹ :
          ComplexMatrix2.specialUnitary) :=
      (((hv ⟨_, h₁⟩).mul (hv ⟨_, h₂⟩)).mul (hv ⟨_, h₃⟩).inv).mul (hv ⟨_, h₄⟩).inv
    exact Complex.continuous_ofReal.comp
      (continuous_const.sub (continuous_const.mul (htr.comp hprod)))
theorem faceEnergy_mem_Icc (hLog : ComplexMatrix2.UnitaryLogarithmProperties)
    (U : Link a → ComplexMatrix2.specialUnitary) (p : ElementaryPlaquette a) :
    0 ≤ faceEnergy U p ∧ faceEnergy U p ≤ 2 := by
  obtain ⟨⟨t, ht, e⟩, -⟩ := hLog.2.1 _ (faceHolonomy U p).2
  have h : (1 / 2) * (ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2)).re = t := by
    have := congrArg Complex.re e
    simpa [ComplexMatrix2.halfTrace] using this
  simp only [faceEnergy, h]
  constructor <;> linarith [ht.1, ht.2]
theorem finite_center_mem (ha : 0 < a) {S : Set AmbientSpace} (hS : Bornology.IsBounded S) :
    {p : ElementaryPlaquette a | p.center ∈ S}.Finite := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.finite_center_mem_of_isBounded <;> assumption
theorem smearedEnergy_eq_sum {f : AmbientSpace → ℝ} {P : Finset (ElementaryPlaquette a)}
    (hP : ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → p ∈ P) (U : GaugeField a) :
    smearedEnergy f U = ∑ p ∈ P, f p.center * faceEnergy U p := by
  rw [smearedEnergy, finsum_eq_sum_of_support_subset (s := P)]
  · exact Finset.sum_congr rfl fun p _ => by rw [smul_eq_mul, mul_comm]
  · intro p hp
    refine Finset.mem_coe.2 (hP p fun h => ?_)
    simp [Function.mem_support, h] at hp
theorem exists_finset_support (ha : 0 < a) {f : AmbientSpace → ℝ}
    (hf : f ∈ compactTestFunctions) :
    ∃ P : Finset (ElementaryPlaquette a), ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → p ∈ P := by
  have hb : Bornology.IsBounded (tsupport f) := hf.2.2.isCompact.isBounded
  refine ⟨(finite_center_mem ha hb).toFinset, fun p hp => ?_⟩
  exact (Set.Finite.mem_toFinset _).2 (subset_tsupport f hp)
def compactTestSubmodule : Submodule ℝ (AmbientSpace → ℝ) where
  carrier := compactTestFunctions
  add_mem' := by
    rintro f g ⟨hf, ⟨C, hC⟩, hfc⟩ ⟨hg, ⟨C', hC'⟩, hgc⟩
    exact ⟨hf.add hg, ⟨C + C', fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hC' x))⟩,
      hfc.add hgc⟩
  zero_mem' := ⟨measurable_const, ⟨0, fun x => by simp⟩, HasCompactSupport.zero⟩
  smul_mem' := by
    rintro c f ⟨hf, ⟨C, hC⟩, hfc⟩
    refine ⟨hf.const_smul c, ⟨‖c‖ * C, fun x => ?_⟩,
      hfc.mono (Function.support_const_smul_subset c f)⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)
theorem smearedEnergy_linear (ha : 0 < a) {f f' : AmbientSpace → ℝ}
    (hf : f ∈ compactTestFunctions) (hf' : f' ∈ compactTestFunctions) (t t' : ℝ)
    (U : GaugeField a) :
    smearedEnergy (t • f + t' • f') U = t * smearedEnergy f U + t' * smearedEnergy f' U := by
  classical
  obtain ⟨P, hP⟩ := exists_finset_support (a := a) ha hf
  obtain ⟨P', hP'⟩ := exists_finset_support (a := a) ha hf'
  have h₁ : ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → p ∈ P ∪ P' :=
    fun p hp => Finset.mem_union_left _ (hP p hp)
  have h₂ : ∀ p : ElementaryPlaquette a, f' p.center ≠ 0 → p ∈ P ∪ P' :=
    fun p hp => Finset.mem_union_right _ (hP' p hp)
  have h₃ : ∀ p : ElementaryPlaquette a, (t • f + t' • f') p.center ≠ 0 → p ∈ P ∪ P' := by
    intro p hp
    by_contra hc
    have e₁ : f p.center = 0 := by
      by_contra h
      exact hc (h₁ p h)
    have e₂ : f' p.center = 0 := by
      by_contra h
      exact hc (h₂ p h)
    exact hp (by simp [e₁, e₂])
  rw [smearedEnergy_eq_sum h₃, smearedEnergy_eq_sum h₁, smearedEnergy_eq_sum h₂,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem smearedEnergy_mem (ha : 0 < a) {f : AmbientSpace → ℝ} (hf : f ∈ compactTestFunctions) :
    (fun U : GaugeField a => ((smearedEnergy f U : ℝ) : ℂ)) ∈ finiteLinkFunctions a := by
  obtain ⟨P, hP⟩ := exists_finset_support (a := a) ha hf
  have e : (fun U : GaugeField a => ((smearedEnergy f U : ℝ) : ℂ)) =
      ∑ p ∈ P, algebraMap ℂ (GaugeField a → ℂ) ((f p.center : ℝ) : ℂ) *
        fun U : GaugeField a => ((faceEnergy U p : ℝ) : ℂ) := by
    funext U
    rw [smearedEnergy_eq_sum hP U, Finset.sum_apply]
    push_cast
    exact Finset.sum_congr rfl fun p _ => rfl
  rw [e]
  exact (localSubalgebra a).sum_mem fun p _ =>
    (localSubalgebra a).mul_mem ((localSubalgebra a).algebraMap_mem _)
      ⟨_, factorsThroughFinite_faceEnergy p⟩
theorem mesh_pos (D : Setup) : 0 < D.mesh := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.mesh_pos <;> assumption
theorem meshAndAxisCounts (hLat : PeriodicLattice.CoordinateDescription)
    (D : Setup) : D.MeshAndAxisCounts := by
  have hL13 : 13 ≤ D.L := D.admissible.2
  have hLr : (13 : ℝ) ≤ (D.L : ℝ) := by exact_mod_cast hL13
  have hLone : (1 : ℝ) ≤ (D.L : ℝ) := by linarith
  have hPow : (1 : ℝ) ≤ (D.L : ℝ) ^ D.level := one_le_pow₀ hLone
  have hmesh : D.mesh = ((D.L : ℝ) ^ D.level)⁻¹ := by
    rw [Setup.mesh, PeriodicLattice.meshSize, zpow_neg, zpow_natCast]
  have hratio : D.side / D.mesh = 2 * (D.L : ℝ) ^ ((D.m : ℕ) + D.level) := by
    rw [hmesh, Setup.side, PeriodicLattice.torusSide, pow_add]
    field_simp
  have hCoords : PeriodicLattice.SublatticeCoordinates D.L D.m (D.level : ℤ) :=
    (hLat D.L D.m D.admissible.1 hL13 D.m.pos).1 (D.level : ℤ) (by omega)
  have hExp : (((D.m : ℕ) : ℤ) + (D.level : ℤ)).toNat = (D.m : ℕ) + D.level := by omega
  have hGe : (D.L : ℝ) ≤ (D.L : ℝ) ^ ((D.m : ℕ) + D.level) :=
    le_self_pow₀ hLone (by have := D.m.pos; omega)
  refine ⟨?_, hratio, ⟨2 * (D.L : ℤ) ^ ((D.m : ℕ) + D.level), ?_⟩, ?_, ?_⟩
  · rw [hmesh]
    exact inv_le_one_of_one_le₀ hPow
  · rw [hratio]
    push_cast
    ring
  · rw [hratio]
    linarith
  · intro y μ
    rw [hCoords.2.2.2.2.2.1 y μ, hratio, PeriodicLattice.halfPeriod, hExp]
    push_cast
    ring
theorem fieldsFormProduct (D : Setup) : D.FieldsFormProduct := by
  have ha := mesh_pos D
  refine ⟨inferInstance, inferInstance, Set.to_countable _,
    fun b => xor_mem_positiveLinks ha b, isHomeomorph_restrictField ha,
    fun 𝓛 _ h𝓛 => ⟨fun V U' => ⟨gluedField ha h𝓛 V U',
      ⟨fun b => gluedField_apply_of_mem ha h𝓛 V U' b,
        fun b hb => gluedField_apply_of_notMem ha h𝓛 V U' hb⟩,
      fun W hW => eq_gluedField ha h𝓛 V U' W hW.1 hW.2⟩,
      fun q => gluedField ha h𝓛 q.1 q.2, continuous_gluedField ha h𝓛, fun V U' =>
      ⟨fun b => gluedField_apply_of_mem ha h𝓛 V U' b,
        fun b hb => gluedField_apply_of_notMem ha h𝓛 V U' hb⟩⟩⟩
theorem localFunctionsDense (D : Setup) : D.LocalFunctionsDense := by
  have ha := mesh_pos D
  refine ⟨fun F hF => continuous_of_mem_finiteLinkFunctions hF, ⟨localSubalgebra D.mesh, rfl⟩,
    fun F hF ε hε => exists_local_uniform_approx ha hF hε, tendstoWeak_of_local ha,
    ext_of_local ha⟩
theorem weakTopologyFacts (D : Setup) : D.WeakTopologyFacts := by
  exact ⟨exists_countable_uniformly_dense, inferInstance, inferInstance,
    tendsto_nhds_iff_tendstoWeak, exists_isSubseqWeakLimit,
    frequently_mem_iff_isSubseqWeakLimit⟩
theorem partialIntegralFacts (D : Setup) : D.PartialIntegralFacts := by
  have ha := mesh_pos D
  refine ⟨fun 𝓜 hfin hset F hF hdep => factorsThroughFinite_of_continuous ha hfin hset hF hdep,
    fun 𝓛 _ _ Φ hΦ => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := haar_integral_facts 𝓛 Φ hΦ
  refine ⟨h₁, h₂, h₃, h₄, h₅, fun 𝓜 hfin hset hdep =>
    factorsThroughFinite_of_continuous ha hfin hset h₂ ?_⟩
  intro U' U'' h
  exact integral_congr_ae (ae_of_all _ fun V => hdep V U' U'' h)
theorem faceEnergyFacts (hLog : ComplexMatrix2.UnitaryLogarithmProperties) (D : Setup) :
    D.FaceEnergyFacts := by
  have ha := mesh_pos D
  refine ⟨fun p => ⟨factorsThroughFinite_faceEnergy p, fun U => faceEnergy_mem_Icc hLog U p⟩,
    fun S hS => finite_center_mem ha hS, fun f hf => ⟨?_, smearedEnergy_mem ha hf⟩,
    ⟨compactTestSubmodule, rfl⟩, fun f hf f' hf' t t' U => smearedEnergy_linear ha hf hf' t t' U⟩
  obtain ⟨P, hP⟩ := exists_finset_support (a := D.mesh) ha hf
  exact ⟨P, fun p => f p.center, fun U => smearedEnergy_eq_sum hP U⟩
theorem basicFacts (hLat : PeriodicLattice.CoordinateDescription)
    (hLog : ComplexMatrix2.UnitaryLogarithmProperties) : BasicFacts := fun D =>
  ⟨meshAndAxisCounts hLat D, fieldsFormProduct D, localFunctionsDense D, weakTopologyFacts D,
    partialIntegralFacts D, faceEnergyFacts hLog D⟩
end YangMills.Construction.FixedSpacing.BasicFactsProof

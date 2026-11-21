import YangMills.Construction.InfiniteLattice.FactsOfTheLocalFunctionsAtEverySpacingProof
import YangMills.Construction.InfiniteLattice.PropertiesOfTheWilsonKernelOnObservablesProof
import YangMills.Construction.InfiniteLattice.RationalPolynomialsAndTheBorelSetsOfTheStates
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter YangMills.Construction.InfiniteLattice.WilsonOperator
open scoped Topology BoundedContinuousFunction ENNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice.RatPolyStates
variable {a : ℝ}
instance : T2Space (GaugeField a) :=
  inferInstanceAs (T2Space {U : Link a → Matrices.ComplexMatrix2.specialUnitary //
    ∀ b, U b.opposite = (U b)⁻¹})
instance : Nonempty (GaugeField a) := ⟨trivialField a⟩
theorem compactSpace_gaugeField (ha : 0 < a) : CompactSpace (GaugeField a) :=
  (gaugeFieldHomeomorph ha).symm.compactSpace
theorem continuous_matrixEntry (b : Link a) (i k : Fin 2) :
    Continuous fun U : GaugeField a => ((U b : Matrices.ComplexMatrix2) i k) := by apply _root_.YangMills.Construction.InfiniteLattice.LocalFunctions.continuous_matrixEntry <;> assumption
theorem continuous_entryCoord (g : LinkEntry a ⊕ LinkEntry a) :
    Continuous (entryCoord g : GaugeField a → ℝ) := by
  rcases g with e | e
  · exact Complex.continuous_re.comp (continuous_matrixEntry e.1.1 e.2.1 e.2.2)
  · exact Complex.continuous_im.comp (continuous_matrixEntry e.1.1 e.2.1 e.2.2)
def polyEval (p : MvPolynomial (LinkEntry a ⊕ LinkEntry a) ℚ) (U : GaugeField a) : ℝ :=
  MvPolynomial.aeval (fun g => entryCoord g U) p
theorem mem_ratPolyObservables_iff {F : GaugeField a → ℝ} :
    F ∈ ratPolyObservables a ↔ ∃ p, F = polyEval p :=
  ⟨fun ⟨p, hp⟩ => ⟨p, funext hp⟩, fun ⟨p, hp⟩ => ⟨p, fun U => by rw [hp]; rfl⟩⟩
instance instCountableLinkEntry : Countable (LinkEntry a) :=
  have : Countable (Link a) := countable_link
  inferInstance
theorem countable_ratPolyObservables : (ratPolyObservables a).Countable := by
  have hrange : (ratPolyObservables a) = range polyEval := by
    ext F
    rw [mem_ratPolyObservables_iff]
    exact ⟨fun ⟨p, hp⟩ => ⟨p, hp.symm⟩, fun ⟨p, hp⟩ => ⟨p, hp.symm⟩⟩
  rw [hrange]
  have hc : Countable (MvPolynomial (LinkEntry a ⊕ LinkEntry a) ℚ) := by
    classical
    refine Function.Injective.countable
      (f := fun p : MvPolynomial (LinkEntry a ⊕ LinkEntry a) ℚ =>
        Finsupp.onFinset p.support (fun m => MvPolynomial.coeff m p)
          fun m hm => MvPolynomial.mem_support_iff.mpr hm) fun p p' h => ?_
    refine MvPolynomial.ext _ _ fun m => ?_
    simpa using DFunLike.congr_fun h m
  exact countable_range _
theorem polyEval_continuous_cylinder (p : MvPolynomial (LinkEntry a ⊕ LinkEntry a) ℚ) :
    Continuous (polyEval p) ∧ IsCylinderFunction (polyEval p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C q =>
    have e : polyEval (MvPolynomial.C q) = fun _ : GaugeField a => (q : ℝ) := by
      funext U; simp [polyEval]
    rw [e]
    exact ⟨continuous_const, ∅, finite_empty, empty_subset _, fun U U' _ => rfl⟩
  | add p p' h h' =>
    obtain ⟨hc, W, hW, hWp, hF⟩ := h
    obtain ⟨hc', W', hW', hWp', hF'⟩ := h'
    have e : polyEval (p + p') =
        fun U : GaugeField a => polyEval p U + polyEval p' U := by
      funext U; simp [polyEval]
    rw [e]
    refine ⟨hc.add hc', W ∪ W', hW.union hW', union_subset hWp hWp', fun U U' h => ?_⟩
    change polyEval p U + polyEval p' U = polyEval p U' + polyEval p' U'
    rw [hF U U' (funext fun b => congrFun h ⟨b.1, Or.inl b.2⟩),
      hF' U U' (funext fun b => congrFun h ⟨b.1, Or.inr b.2⟩)]
  | mul_X p g h =>
    obtain ⟨hc, W, hW, hWp, hF⟩ := h
    have e : polyEval (p * MvPolynomial.X g) =
        fun U : GaugeField a => polyEval p U * entryCoord g U := by
      funext U; simp [polyEval]
    rw [e]
    have hb : ∃ b : positiveLinkSet a, ∀ U U' : GaugeField a, U b.1 = U' b.1 →
        entryCoord g U = entryCoord g U' := by
      rcases g with d | d
      · exact ⟨d.1, fun U U' h => by simp [entryCoord, entryRe, h]⟩
      · exact ⟨d.1, fun U U' h => by simp [entryCoord, entryIm, h]⟩
    obtain ⟨b, hb⟩ := hb
    refine ⟨hc.mul (continuous_entryCoord g), W ∪ {b.1}, hW.union (finite_singleton _),
      union_subset hWp (singleton_subset_iff.mpr b.2), fun U U' h => ?_⟩
    change polyEval p U * entryCoord g U = polyEval p U' * entryCoord g U'
    rw [hF U U' (funext fun c => congrFun h ⟨c.1, Or.inl c.2⟩),
      hb U U' (congrFun h ⟨b.1, Or.inr rfl⟩)]
def entryContinuousMap (g : LinkEntry a ⊕ LinkEntry a) : C(GaugeField a, ℝ) :=
  ⟨entryCoord g, continuous_entryCoord g⟩
def polyContinuousMap : MvPolynomial (LinkEntry a ⊕ LinkEntry a) ℚ →ₐ[ℚ] C(GaugeField a, ℝ) :=
  MvPolynomial.aeval entryContinuousMap
theorem polyContinuousMap_apply (p : MvPolynomial (LinkEntry a ⊕ LinkEntry a) ℚ)
    (U : GaugeField a) : polyContinuousMap p U = polyEval p U := by
  induction p using MvPolynomial.induction_on with
  | C q => simp [polyContinuousMap, polyEval]
  | add p p' h h' =>
    have e : polyEval (p + p') U = polyEval p U + polyEval p' U := by
      simp [polyEval]
    rw [map_add, e, ContinuousMap.add_apply, h, h']
  | mul_X p g h =>
    have e : polyEval (p * MvPolynomial.X g) U =
        polyEval p U * entryCoord g U := by
      simp [polyEval]
    have e' : polyContinuousMap (MvPolynomial.X g : MvPolynomial (LinkEntry a ⊕ LinkEntry a) ℚ) =
        entryContinuousMap g := by
      simp [polyContinuousMap]
    rw [map_mul, e, ContinuousMap.mul_apply, h, e']
    rfl
theorem exists_entryCoord_ne (ha : 0 < a) {U U' : GaugeField a} (h : U ≠ U') :
    ∃ g : LinkEntry a ⊕ LinkEntry a, entryCoord g U ≠ entryCoord g U' := by
  have hne : gaugeFieldHomeomorph ha U ≠ gaugeFieldHomeomorph ha U' :=
    fun e => h ((gaugeFieldHomeomorph ha).injective e)
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hne
  have hb' : (U b.1 : Matrices.ComplexMatrix2) ≠ (U' b.1 : Matrices.ComplexMatrix2) :=
    fun e => hb (Subtype.ext e)
  have hik : ∃ i k : Fin 2, (U b.1 : Matrices.ComplexMatrix2) i k ≠
      (U' b.1 : Matrices.ComplexMatrix2) i k := by
    by_contra hc
    exact hb' (funext fun i => funext fun k => by_contra fun hne => hc ⟨i, k, hne⟩)
  obtain ⟨i, k, hik⟩ := hik
  by_cases hre : ((U b.1 : Matrices.ComplexMatrix2) i k).re =
      ((U' b.1 : Matrices.ComplexMatrix2) i k).re
  · refine ⟨Sum.inr (b, i, k), fun him => hik (Complex.ext hre him)⟩
  · exact ⟨Sum.inl (b, i, k), hre⟩
def polyClosureSubalgebra (ha : 0 < a) : Subalgebra ℝ C(GaugeField a, ℝ) :=
  have := compactSpace_gaugeField ha
  { (polyContinuousMap (a := a)).range.topologicalClosure.toSubsemiring with
    algebraMap_mem' := fun r => by
      refine Metric.mem_closure_iff.mpr fun ε hε => ?_
      obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show r < r + ε by linarith)
      refine ⟨polyContinuousMap (MvPolynomial.C q), ⟨_, rfl⟩, ?_⟩
      refine (ContinuousMap.dist_lt_iff hε).mpr fun U => ?_
      have e : polyContinuousMap (a := a) (MvPolynomial.C q) U = (q : ℝ) := by
        rw [polyContinuousMap_apply]; simp [polyEval]
      rw [e, Real.dist_eq, abs_lt]
      have e' : (algebraMap ℝ C(GaugeField a, ℝ) r) U = r := rfl
      rw [e']
      constructor <;> linarith }
theorem mem_closure_polyRange (ha : 0 < a) (f : C(GaugeField a, ℝ)) :
    have := compactSpace_gaugeField ha
    f ∈ closure (((polyContinuousMap (a := a)).range : Subalgebra ℚ C(GaugeField a, ℝ)) :
      Set C(GaugeField a, ℝ)) := by
  have := compactSpace_gaugeField ha
  have hsep : (polyClosureSubalgebra ha).SeparatesPoints := by
    intro U U' h
    obtain ⟨g, hg⟩ := exists_entryCoord_ne ha h
    refine ⟨entryCoord g, ⟨entryContinuousMap g, ?_, rfl⟩, hg⟩
    exact subset_closure ⟨MvPolynomial.X g, by simp [polyContinuousMap]⟩
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  have h1 : f ∈ (polyClosureSubalgebra ha).topologicalClosure := by
    rw [htop]; exact Algebra.mem_top
  have h2 : f ∈ closure (closure (((polyContinuousMap (a := a)).range :
      Subalgebra ℚ C(GaugeField a, ℝ)) : Set C(GaugeField a, ℝ))) := h1
  rwa [closure_closure] at h2
theorem exists_polyEval_near (ha : 0 < a) (f : C(GaugeField a, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p, ∀ U, |f U - polyEval p U| ≤ ε := by
  have := compactSpace_gaugeField ha
  obtain ⟨g, ⟨p, rfl⟩, hd⟩ := Metric.mem_closure_iff.mp (mem_closure_polyRange ha f) ε hε
  refine ⟨p, fun U => ?_⟩
  rw [← polyContinuousMap_apply, ← Real.dist_eq]
  exact (ContinuousMap.dist_apply_le_dist U).trans hd.le
theorem supNorm_le {A : GaugeField a → ℂ} {C : ℝ} (h : ∀ U, ‖A U‖ ≤ C) :
    observableSupNorm A ≤ C :=
  ciSup_le h
theorem norm_le_supNorm {A : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (U : GaugeField a) : ‖A U‖ ≤ observableSupNorm A := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.norm_le_supNorm <;> assumption
theorem exists_complexRatPoly_near (ha : 0 < a) {F : GaugeField a → ℂ} (hF : Continuous F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F' ∈ complexRatPolyObservables a, ∀ U, ‖F U - F' U‖ ≤ ε := by
  obtain ⟨p₁, h₁⟩ := exists_polyEval_near ha ⟨fun U => (F U).re, Complex.continuous_re.comp hF⟩
    (half_pos hε)
  obtain ⟨p₂, h₂⟩ := exists_polyEval_near ha ⟨fun U => (F U).im, Complex.continuous_im.comp hF⟩
    (half_pos hε)
  refine ⟨fun U => (polyEval p₁ U : ℂ) + Complex.I * (polyEval p₂ U : ℂ),
    ⟨_, mem_ratPolyObservables_iff.mpr ⟨p₁, rfl⟩, _, mem_ratPolyObservables_iff.mpr ⟨p₂, rfl⟩,
      fun _ => rfl⟩, fun U => ?_⟩
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hr : (F U - ((polyEval p₁ U : ℂ) + Complex.I * (polyEval p₂ U : ℂ))).re =
      (F U).re - polyEval p₁ U := by simp
  have hi : (F U - ((polyEval p₁ U : ℂ) + Complex.I * (polyEval p₂ U : ℂ))).im =
      (F U).im - polyEval p₂ U := by simp
  rw [hr, hi]
  have := h₁ U
  have := h₂ U
  simp only [ContinuousMap.coe_mk] at *
  linarith
theorem ratPolyDense (ha : 0 < a) : RatPolyDense a := by
  refine ⟨countable_ratPolyObservables, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F hF
    obtain ⟨p, rfl⟩ := mem_ratPolyObservables_iff.mp hF
    obtain ⟨hc, W, hW, hWp, hr⟩ := polyEval_continuous_cylinder p
    exact ⟨Complex.continuous_ofReal.comp hc, W, hW, hWp, fun U U' h => by
      simp only [hr U U' h]⟩
  · intro q
    exact ⟨MvPolynomial.C q, fun U => by simp⟩
  · rintro F ⟨p, hp⟩ F' ⟨p', hp'⟩
    exact ⟨⟨p + p', fun U => by simp [hp, hp']⟩, ⟨p * p', fun U => by simp [hp, hp']⟩⟩
  · rintro q F ⟨p, hp⟩
    exact ⟨MvPolynomial.C q * p, fun U => by simp [hp]⟩
  · intro F hF ε hε
    obtain ⟨p, hp⟩ := exists_polyEval_near ha ⟨F, hF⟩ hε
    refine ⟨polyEval p, mem_ratPolyObservables_iff.mpr ⟨p, rfl⟩,
      supNorm_le fun U => ?_⟩
    rw [Complex.norm_real]
    exact hp U
  · intro F hF ε hε
    obtain ⟨F', hF', h⟩ := exists_complexRatPoly_near ha hF hε
    exact ⟨F', hF', supNorm_le h⟩
theorem complexRatPoly_mem_continuousCylinder (F : GaugeField a → ℂ)
    (hF : F ∈ complexRatPolyObservables a) : F ∈ continuousCylinderFunctions a := by
  obtain ⟨F₁, h₁, F₂, h₂, h⟩ := hF
  obtain ⟨p₁, rfl⟩ := mem_ratPolyObservables_iff.mp h₁
  obtain ⟨p₂, rfl⟩ := mem_ratPolyObservables_iff.mp h₂
  obtain ⟨hc₁, W₁, hW₁, hp₁, hr₁⟩ := polyEval_continuous_cylinder p₁
  obtain ⟨hc₂, W₂, hW₂, hp₂, hr₂⟩ := polyEval_continuous_cylinder p₂
  have e : F = fun U => (polyEval p₁ U : ℂ) + Complex.I * (polyEval p₂ U : ℂ) :=
    funext h
  rw [e]
  refine ⟨(Complex.continuous_ofReal.comp hc₁).add
      (continuous_const.mul (Complex.continuous_ofReal.comp hc₂)), W₁ ∪ W₂, hW₁.union hW₂,
    union_subset hp₁ hp₂, fun U U' hU => ?_⟩
  simp only [hr₁ U U' (funext fun b => congrFun hU ⟨b.1, Or.inl b.2⟩),
    hr₂ U U' (funext fun b => congrFun hU ⟨b.1, Or.inr b.2⟩)]
theorem secondCountable_gaugeField (ha : 0 < a) :
    SecondCountableTopology (GaugeField a) := by
  have := secondCountable_specialUnitary
  have : Countable (Link a) := countable_link
  exact (gaugeFieldHomeomorph ha).secondCountableTopology
theorem metrizable_gaugeField (ha : 0 < a) :
    TopologicalSpace.MetrizableSpace (GaugeField a) := by
  have := compactSpace_gaugeField ha
  have := secondCountable_gaugeField ha
  infer_instance
theorem boundedPointwiseClosure_contains (ha : 0 < a) :
    BoundedPointwiseClosureContainsObservables a := by
  intro H _ hloc hlim
  have := compactSpace_gaugeField ha
  have := metrizable_gaugeField ha
  let _ := TopologicalSpace.metrizableSpaceMetric (GaugeField a)
  have hcont : ∀ G : GaugeField a → ℂ, Continuous G → G ∈ H := by
    intro G hG
    have hpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
    choose F' hF' hnear using fun k : ℕ => exists_complexRatPoly_near ha hG (hpos k)
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hG.continuousOn
    refine hlim F' G (fun k => hloc _ (complexRatPoly_mem_continuousCylinder _ (hF' k)))
      ⟨C + 1, fun k => ?_⟩ fun U => ?_
    · refine supNorm_le fun U => ?_
      have h₁ := hnear k U
      have h₂ := hC U (mem_univ U)
      have h₃ : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (0 : ℝ) ≤ k := k.cast_nonneg
        linarith
      have h₄ : ‖F' k U‖ ≤ ‖G U‖ + ‖G U - F' k U‖ := by
        have := norm_sub_le (G U) (G U - F' k U)
        simpa using this
      linarith
    · rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      rw [norm_sub_rev]
      exact hnear k U
  have hclosed : ∀ C : Set (GaugeField a), IsClosed C →
      C.indicator (fun _ => (1 : ℂ)) ∈ H := by
    intro C hC
    refine hlim (fun k U => (((hC.apprSeq k U : NNReal) : ℝ) : ℂ)) _ (fun k => hcont _ ?_)
      ⟨1, fun k => supNorm_le fun U => ?_⟩ fun U => ?_
    · exact Complex.continuous_ofReal.comp
        (NNReal.continuous_coe.comp (hC.apprSeq k).continuous)
    · rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hC k U
    · have h := tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hC) U
      have h' := (Complex.continuous_ofReal.comp NNReal.continuous_coe).continuousAt.tendsto.comp h
      have e : C.indicator (fun _ => (1 : ℂ)) U =
          (Complex.ofReal ∘ NNReal.toReal) (C.indicator (fun _ => (1 : NNReal)) U) := by
        by_cases hU : U ∈ C <;> simp [hU]
      rw [e]
      exact h'
  have hborel : ∀ E : Set (GaugeField a), MeasurableSet E →
      E.indicator (fun _ => (1 : ℂ)) ∈ H := by
    intro E hE
    have hone : (fun _ : GaugeField a => (1 : ℂ)) ∈ H := hcont _ continuous_const
    refine MeasurableSpace.induction_on_inter
      (C := fun E _ => E.indicator (fun _ => (1 : ℂ)) ∈ H)
      (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed)
      isPiSystem_isClosed ?_ (fun t ht => hclosed t ht) (fun t _ ih => ?_)
      (fun f hd _ ih => ?_) E hE
    · rw [indicator_empty]
      exact H.zero_mem
    · rw [indicator_compl]
      exact H.sub_mem hone ih
    · refine hlim (fun n => (⋃ i ∈ Finset.range n, f i).indicator fun _ => (1 : ℂ)) _
        (fun n => ?_) ⟨1, fun n => supNorm_le fun U => ?_⟩ fun U => ?_
      · rw [Finset.indicator_biUnion _ _ fun i _ j _ hij => hd hij]
        have e : (fun U => ∑ i ∈ Finset.range n, (f i).indicator (fun _ => (1 : ℂ)) U) =
            ∑ i ∈ Finset.range n, (f i).indicator fun _ => (1 : ℂ) := by
          funext U; simp [Finset.sum_apply]
        rw [e]
        exact H.sum_mem fun i _ => ih i
      · by_cases hU : U ∈ ⋃ i ∈ Finset.range n, f i <;> simp only [indicator, hU] <;> simp
      · exact ((tendsto_indicator_biUnion_finset f _ U).comp tendsto_finset_range).mono_right
          (pure_le_nhds _)
  have hsimple : ∀ s : SimpleFunc (GaugeField a) ℂ, (s : GaugeField a → ℂ) ∈ H := by
    intro s
    induction s using SimpleFunc.induction with
    | const c hs =>
      rename_i t
      have e : ((SimpleFunc.piecewise t hs (SimpleFunc.const _ c) (SimpleFunc.const _ 0) :
          SimpleFunc (GaugeField a) ℂ) : GaugeField a → ℂ) =
          c • t.indicator fun _ => (1 : ℂ) := by
        funext U
        by_cases hU : U ∈ t <;> simp [hU]
      rw [e]
      exact H.smul_mem c (hborel t hs)
    | add _ hf hg =>
      rw [SimpleFunc.coe_add]
      exact H.add_mem hf hg
  intro F hF
  obtain ⟨C, hC⟩ := hF.2
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (trivialField a))
  have hs := hF.1.stronglyMeasurable
  exact hlim (fun n => hs.approxBounded C n) F (fun n => hsimple _)
    ⟨C, fun n => supNorm_le (hs.norm_approxBounded_le hC0 n)⟩
    fun U => hs.tendsto_approxBounded_of_norm_le (hC U)
theorem isBoundedObservable_of_continuous (ha : 0 < a) {F : GaugeField a → ℂ}
    (hF : Continuous F) : IsBoundedObservable F := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperatorPropertiesProof.isBoundedObservable_of_continuous <;> assumption
theorem continuous_of_mem_ratPoly {F : GaugeField a → ℝ}
    (hF : F ∈ ratPolyObservables a) : Continuous F := by
  obtain ⟨p, rfl⟩ := mem_ratPolyObservables_iff.mp hF
  exact (polyEval_continuous_cylinder p).1
theorem integrable_of_isBoundedObservable {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (ρ : GaugeFieldProbability a) : Integrable F ρ.1 := by
  have := ρ.2
  obtain ⟨C, hC⟩ := hF.2
  exact Integrable.of_bound hF.1.aestronglyMeasurable C (ae_of_all _ hC)
theorem integrable_real_of_continuous (ha : 0 < a) {F : GaugeField a → ℝ} (hF : Continuous F)
    (ρ : GaugeFieldProbability a) : Integrable F ρ.1 := by
  have := ρ.2
  have := compactSpace_gaugeField ha
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  exact Integrable.of_bound hF.measurable.aestronglyMeasurable C
    (ae_of_all _ fun U => hC U (mem_univ U))
theorem memLp_of_isBoundedObservable {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (ρ : GaugeFieldProbability a) (p : ℝ≥0∞) : MemLp F p ρ.1 := by
  have := ρ.2
  obtain ⟨C, hC⟩ := hF.2
  exact MemLp.of_bound hF.1.aestronglyMeasurable C (ae_of_all _ hC)
theorem norm_expect_sub_le {F G : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) (ρ : GaugeFieldProbability a) {ε : ℝ}
    (h : ∀ U, ‖F U - G U‖ ≤ ε) : ‖ρ.expect F - ρ.expect G‖ ≤ ε := by
  have := ρ.2
  unfold GaugeFieldProbability.expect
  rw [← integral_sub (integrable_of_isBoundedObservable hF ρ)
    (integrable_of_isBoundedObservable hG ρ)]
  simpa using norm_integral_le_of_norm_le_const (μ := ρ.1) (ae_of_all _ h)
theorem stateL2Norm_eq_eLpNorm (ν : GaugeFieldProbability a) {φ : GaugeField a → ℂ}
    (h : MemLp φ 2 ν.1) : stateL2Norm ν φ = (eLpNorm φ 2 ν.1).toReal := by
  rw [h.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat, stateL2Norm, one_div]
theorem integral_norm_le_stateL2Norm (ν : GaugeFieldProbability a) {φ : GaugeField a → ℂ}
    (h : MemLp φ 2 ν.1) : ∫ U, ‖φ U‖ ∂ν.1 ≤ stateL2Norm ν φ := by
  have := ν.2
  have h₁ : eLpNorm φ 1 ν.1 ≤ eLpNorm φ 2 ν.1 :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) h.aestronglyMeasurable
  have hm : MemLp φ 1 ν.1 := h.mono_exponent (by norm_num)
  have e : ∫ U, ‖φ U‖ ∂ν.1 = (eLpNorm φ 1 ν.1).toReal := by
    rw [hm.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _)]
    simp
  rw [e, stateL2Norm_eq_eLpNorm ν h]
  exact ENNReal.toReal_mono h.eLpNorm_ne_top h₁
theorem ratPolyApproximates (ha : 0 < a) : RatPolyApproximatesInEveryState a := by
  intro ν F hF ε hε
  have := ν.2
  have := compactSpace_gaugeField ha
  have := metrizable_gaugeField ha
  let _ := TopologicalSpace.metrizableSpaceMetric (GaugeField a)
  obtain ⟨g, hg, -⟩ := (memLp_of_isBoundedObservable hF ν 2).exists_boundedContinuous_eLpNorm_sub_le
    (by norm_num) (ε := ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
  obtain ⟨ψ, hψ, hn⟩ := exists_complexRatPoly_near ha g.continuous (half_pos hε)
  have hψo : IsBoundedObservable ψ :=
    isBoundedObservable_of_continuous ha (complexRatPoly_mem_continuousCylinder ψ hψ).1
  have hgo : IsBoundedObservable (g : GaugeField a → ℂ) :=
    isBoundedObservable_of_continuous ha g.continuous
  have hm : MemLp (F - ψ) 2 ν.1 :=
    (memLp_of_isBoundedObservable hF ν 2).sub (memLp_of_isBoundedObservable hψo ν 2)
  have h₂ : eLpNorm ((g : GaugeField a → ℂ) - ψ) 2 ν.1 ≤ ENNReal.ofReal (ε / 2) := by
    have := eLpNorm_le_of_ae_bound (μ := ν.1) (p := 2)
      (f := (g : GaugeField a → ℂ) - ψ) (C := ε / 2) (ae_of_all _ hn)
    simpa using this
  have hs : eLpNorm (F - ψ) 2 ν.1 ≤ ENNReal.ofReal ε := by
    have e : F - ψ = (F - (g : GaugeField a → ℂ)) + ((g : GaugeField a → ℂ) - ψ) := by
      funext U; simp
    calc eLpNorm (F - ψ) 2 ν.1
        = eLpNorm ((F - (g : GaugeField a → ℂ)) + ((g : GaugeField a → ℂ) - ψ)) 2 ν.1 := by
          rw [← e]
      _ ≤ eLpNorm (F - (g : GaugeField a → ℂ)) 2 ν.1 +
          eLpNorm ((g : GaugeField a → ℂ) - ψ) 2 ν.1 :=
          eLpNorm_add_le (hF.1.sub hgo.1).aestronglyMeasurable
            (hgo.1.sub hψo.1).aestronglyMeasurable (by norm_num)
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hg h₂
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
  have hb : stateL2Norm ν (F - ψ) ≤ ε := by
    rw [stateL2Norm_eq_eLpNorm ν hm]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hs
  exact ⟨ψ, hψ, hb, (integral_norm_le_stateL2Norm ν hm).trans hb⟩
theorem continuous_expect (ha : 0 < a) {G : GaugeField a → ℂ} (hG : Continuous G) :
    Continuous fun ρ : GaugeFieldProbability a => ρ.expect G := by
  have := compactSpace_gaugeField ha
  exact continuous_iInf_dom (i := BoundedContinuousFunction.mkOfCompact ⟨G, hG⟩)
    continuous_induced_dom
theorem expect_ofReal (ρ : GaugeFieldProbability a) (F : GaugeField a → ℝ) :
    ρ.expect (fun U => (F U : ℂ)) = (realExpectation ρ F : ℂ) :=
  integral_complex_ofReal
theorem continuous_realExpectation (ha : 0 < a) {F : GaugeField a → ℝ} (hF : Continuous F) :
    Continuous fun ρ : GaugeFieldProbability a => realExpectation ρ F := by
  have h := Complex.continuous_re.comp
    (continuous_expect ha (Complex.continuous_ofReal.comp hF))
  refine h.congr fun ρ => ?_
  have e := expect_ofReal ρ F
  simp only [Function.comp_def]
  rw [e, Complex.ofReal_re]
theorem abs_realExpectation_sub_le (ha : 0 < a) {F G : GaugeField a → ℝ} (hF : Continuous F)
    (hG : Continuous G) (ρ : GaugeFieldProbability a) {ε : ℝ} (h : ∀ U, |F U - G U| ≤ ε) :
    |realExpectation ρ F - realExpectation ρ G| ≤ ε := by
  have := ρ.2
  unfold realExpectation
  rw [← integral_sub (integrable_real_of_continuous ha hF ρ)
    (integrable_real_of_continuous ha hG ρ)]
  simpa using norm_integral_le_of_norm_le_const (μ := ρ.1) (f := fun U => F U - G U)
    (ae_of_all _ h)
theorem ext_of_realExpectation_ratPoly (ha : 0 < a) (ν ν' : GaugeFieldProbability a)
    (h : ∀ F ∈ ratPolyObservables a,
      realExpectation ν F = realExpectation ν' F) : ν = ν' := by
  have := ν.2
  have := ν'.2
  have := compactSpace_gaugeField ha
  have := metrizable_gaugeField ha
  let _ := TopologicalSpace.metrizableSpaceMetric (GaugeField a)
  refine Subtype.ext (ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_)
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨p, hp⟩ := exists_polyEval_near ha ⟨f, f.continuous⟩ (half_pos hε)
  have hpc := (polyEval_continuous_cylinder p).1
  have h₁ := abs_realExpectation_sub_le ha f.continuous hpc ν hp
  have h₂ := abs_realExpectation_sub_le ha f.continuous hpc ν' hp
  rw [h _ (mem_ratPolyObservables_iff.mpr ⟨p, rfl⟩)] at h₁
  rw [Real.dist_eq]
  have e₁ := abs_le.mp h₁
  have e₂ := abs_le.mp h₂
  simp only [realExpectation] at e₁ e₂
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [e₁.1, e₁.2, e₂.1, e₂.2]
@[instance_reducible] def ratPolyTopology (a : ℝ) : TopologicalSpace (GaugeFieldProbability a) :=
  ⨅ F : ratPolyObservables a,
    TopologicalSpace.induced (fun ρ => realExpectation ρ F.1) inferInstance
theorem continuous_of_uniform_approx {X : Type*} [TopologicalSpace X] {f : ℕ → X → ℂ}
    {g : X → ℂ} (hf : ∀ k, Continuous (f k)) (h : ∀ k x, ‖g x - f k x‖ ≤ 1 / ((k : ℝ) + 1)) :
    Continuous g := by
  refine TendstoUniformly.continuous (F := f) (p := atTop) ?_
    (Eventually.of_forall hf).frequently
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop N] with k hk x
  rw [dist_eq_norm]
  have hk' : (N : ℝ) + 1 ≤ (k : ℝ) + 1 := by
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  calc ‖g x - f k x‖ ≤ 1 / ((k : ℝ) + 1) := h k x
    _ ≤ 1 / ((N : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) hk'
    _ < ε := hN
theorem continuous_re_add_I_mul {X : Type*} [TopologicalSpace X] {u v : X → ℝ}
    (hu : Continuous u) (hv : Continuous v) :
    Continuous fun x => (u x : ℂ) + Complex.I * (v x : ℂ) :=
  (Complex.continuous_ofReal.comp hu).add
    (continuous_const.mul (Complex.continuous_ofReal.comp hv))
theorem weak_eq_ratPolyTopology (ha : 0 < a) :
    (inferInstance : TopologicalSpace (GaugeFieldProbability a)) = ratPolyTopology a := by
  apply le_antisymm
  · exact le_iInf fun F => continuous_iff_le_induced.mp
      (continuous_realExpectation ha (continuous_of_mem_ratPoly F.2))
  · change ratPolyTopology a ≤ ⨅ F : GaugeField a →ᵇ ℂ,
      TopologicalSpace.induced (fun ν => ν.expect F) inferInstance
    refine le_iInf fun G => continuous_iff_le_induced.mp ?_
    have hpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
    choose Fk hFk hnear using fun k : ℕ => exists_complexRatPoly_near ha G.continuous (hpos k)
    refine @continuous_of_uniform_approx _ (ratPolyTopology a)
      (fun k ρ => ρ.expect (Fk k)) _ (fun k => ?_) fun k ρ => ?_
    · obtain ⟨F₁, h₁, F₂, h₂, h⟩ := hFk k
      have c₁ : @Continuous _ _ (ratPolyTopology a) _
          (fun ρ => realExpectation ρ F₁) :=
        continuous_iInf_dom (i := ⟨F₁, h₁⟩) continuous_induced_dom
      have c₂ : @Continuous _ _ (ratPolyTopology a) _
          (fun ρ => realExpectation ρ F₂) :=
        continuous_iInf_dom (i := ⟨F₂, h₂⟩) continuous_induced_dom
      have e : (fun ρ : GaugeFieldProbability a => ρ.expect (Fk k)) =
          fun ρ => (realExpectation ρ F₁ : ℂ) + Complex.I * (realExpectation ρ F₂ : ℂ) := by
        funext ρ
        have i₁ : IsBoundedObservable fun U => (F₁ U : ℂ) := isBoundedObservable_of_continuous ha
          (Complex.continuous_ofReal.comp (continuous_of_mem_ratPoly h₁))
        have i₂ : IsBoundedObservable fun U => (F₂ U : ℂ) := isBoundedObservable_of_continuous ha
          (Complex.continuous_ofReal.comp (continuous_of_mem_ratPoly h₂))
        rw [← expect_ofReal, ← expect_ofReal]
        unfold GaugeFieldProbability.expect
        simp only [h]
        rw [integral_add (integrable_of_isBoundedObservable i₁ ρ)
          ((integrable_of_isBoundedObservable i₂ ρ).const_mul _), integral_const_mul]
      rw [e]
      exact @continuous_re_add_I_mul _ (ratPolyTopology a) _ _ c₁ c₂
    · exact norm_expect_sub_le (isBoundedObservable_of_continuous ha G.continuous)
        (isBoundedObservable_of_continuous ha
          (complexRatPoly_mem_continuousCylinder _ (hFk k)).1) ρ (hnear k)
theorem isOpen_statesInInterval (ha : 0 < a) {F : GaugeField a → ℝ} (hF : Continuous F)
    (p q : ℚ) : IsOpen (statesInInterval F p q) := by
  have hc := continuous_realExpectation ha hF
  exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
theorem rationalIntervalBasis_isBasis (ha : 0 < a) :
    TopologicalSpace.IsTopologicalBasis (rationalIntervalBasis a) := by
  classical
  have hb0 := IsTopologicalBasis.iInf_induced
    (ι := ratPolyObservables a) (X := fun _ => ℝ)
    (T := fun _ => ⋃ (p : ℚ) (q : ℚ) (_ : p < q), {Ioo (p : ℝ) q})
    (fun _ => Real.isTopologicalBasis_Ioo_rat)
    (fun F (ρ : GaugeFieldProbability a) => realExpectation ρ F.1)
  change @TopologicalSpace.IsTopologicalBasis _ (ratPolyTopology a) _ at hb0
  rw [← weak_eq_ratPolyTopology ha] at hb0
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro O ⟨T, hT, hT', rfl⟩
    refine hT.isOpen_sInter fun O' hO' => ?_
    obtain ⟨F, hF, p, q, rfl⟩ := hT' O' hO'
    exact isOpen_statesInInterval ha (continuous_of_mem_ratPoly hF) p q
  · intro ρ O hρ hO
    obtain ⟨S, ⟨U, Fs, hU, rfl⟩, hρS, hSO⟩ := hb0.exists_subset_of_mem_open hρ hO
    have hpq : ∀ i ∈ Fs, ∃ p q : ℚ, U i = Ioo (p : ℝ) q := by
      intro i hi
      have := hU i hi
      simp only [mem_iUnion, mem_singleton_iff] at this
      obtain ⟨p, q, -, h⟩ := this
      exact ⟨p, q, h⟩
    choose! P Q hPQ using hpq
    let T : Set (Set (GaugeFieldProbability a)) :=
      (fun i : ratPolyObservables a => statesInInterval i.1 (P i) (Q i)) '' (Fs : Set _)
    have hS : ⋂₀ T = ⋂ (i) (_ : i ∈ Fs), (fun ρ : GaugeFieldProbability a =>
          realExpectation ρ i.1) ⁻¹' U i := by
      rw [sInter_image]
      refine iInter₂_congr fun i hi => ?_
      rw [hPQ i hi]
      rfl
    refine ⟨⋂₀ T, ⟨T, (Fs.finite_toSet).image _, ?_, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨i, -, rfl⟩
      exact ⟨i.1, i.2, _, _, rfl⟩
    · rw [hS]; exact hρS
    · rw [hS]; exact hSO
theorem countable_rationalIntervalBasis : (rationalIntervalBasis a).Countable := by
  have hS : {O' : Set (GaugeFieldProbability a) |
      ∃ F ∈ ratPolyObservables a, ∃ p q : ℚ, O' = statesInInterval F p q}.Countable := by
    refine ((countable_ratPolyObservables.prod (countable_univ (α := ℚ × ℚ))).image
      fun x => statesInInterval x.1 x.2.1 x.2.2).mono ?_
    rintro _ ⟨F, hF, p, q, rfl⟩
    exact ⟨(F, p, q), ⟨hF, mem_univ _⟩, rfl⟩
  refine ((countable_ofPred_finite_subset hS).image fun T => ⋂₀ T).mono ?_
  rintro O ⟨T, hT, hT', rfl⟩
  exact ⟨T, ⟨hT, hT'⟩, rfl⟩
theorem borel_eq_iSup_comap_ratPoly (ha : 0 < a) :
    (inferInstance : MeasurableSpace (GaugeFieldProbability a)) =
      ⨆ F ∈ ratPolyObservables a,
        MeasurableSpace.comap (fun ρ : GaugeFieldProbability a => realExpectation ρ F)
          inferInstance := by
  have hb := rationalIntervalBasis_isBasis ha
  have := hb.secondCountableTopology countable_rationalIntervalBasis
  apply le_antisymm
  · change borel _ ≤ _
    rw [hb.borel_eq_generateFrom]
    refine MeasurableSpace.generateFrom_le ?_
    rintro O ⟨T, hT, hT', rfl⟩
    refine MeasurableSet.sInter hT.countable fun O' hO' => ?_
    obtain ⟨F, hF, p, q, rfl⟩ := hT' O' hO'
    have hm := measurable_iff_comap_le.mpr (le_iSup₂_of_le (f := fun F _ =>
      MeasurableSpace.comap (fun ρ : GaugeFieldProbability a => realExpectation ρ F)
        inferInstance) F hF le_rfl)
    exact hm (measurableSet_Ioo (a := (p : ℝ)) (b := (q : ℝ)))
  · exact iSup₂_le fun F hF =>
      (continuous_realExpectation ha (continuous_of_mem_ratPoly hF)).measurable.comap_le
theorem measurable_expect (ha : 0 < a) (F : GaugeField a → ℂ) (hF : IsBoundedObservable F) :
    Measurable fun ρ : GaugeFieldProbability a => ρ.expect F := by
  let H : Submodule ℂ (GaugeField a → ℂ) :=
    { carrier := {F | IsBoundedObservable F ∧ Measurable fun ρ : GaugeFieldProbability a =>
        ρ.expect F}
      add_mem' := by
        rintro A B ⟨hA, mA⟩ ⟨hB, mB⟩
        obtain ⟨C, hC⟩ := hA.2
        obtain ⟨D, hD⟩ := hB.2
        refine ⟨⟨hA.1.add hB.1, C + D, fun U => (norm_add_le _ _).trans
          (add_le_add (hC U) (hD U))⟩, ?_⟩
        have e : (fun ρ : GaugeFieldProbability a => ρ.expect (A + B)) =
            fun ρ => ρ.expect A + ρ.expect B := by
          funext ρ
          exact integral_add (integrable_of_isBoundedObservable hA ρ)
            (integrable_of_isBoundedObservable hB ρ)
        rw [e]
        exact mA.add mB
      zero_mem' := by
        refine ⟨⟨measurable_const, 0, fun U => by simp⟩, ?_⟩
        have e : (fun ρ : GaugeFieldProbability a => ρ.expect 0) = fun _ => 0 := by
          funext ρ
          simp [GaugeFieldProbability.expect]
        rw [e]
        exact measurable_const
      smul_mem' := by
        rintro c A ⟨hA, mA⟩
        obtain ⟨C, hC⟩ := hA.2
        refine ⟨⟨hA.1.const_smul c, ‖c‖ * C, fun U => ?_⟩, ?_⟩
        · rw [Pi.smul_apply, norm_smul]
          exact mul_le_mul_of_nonneg_left (hC U) (norm_nonneg _)
        · have e : (fun ρ : GaugeFieldProbability a => ρ.expect (c • A)) =
              fun ρ => c * ρ.expect A := by
            funext ρ
            exact integral_const_mul c A
          rw [e]
          exact mA.const_mul c }
  refine (boundedPointwiseClosure_contains ha H (fun _ h => h.1) (fun G hG =>
    ⟨isBoundedObservable_of_continuous ha hG.1, (continuous_expect ha hG.1).measurable⟩) ?_
    F hF).2
  rintro A G hA ⟨C, hC⟩ hconv
  have hb : ∀ k U, ‖A k U‖ ≤ C := fun k U => (norm_le_supNorm (hA k).1 U).trans (hC k)
  have hGm : Measurable G :=
    measurable_of_tendsto_metrizable (fun k => (hA k).1.1) (tendsto_pi_nhds.mpr hconv)
  have hGb : ∀ U, ‖G U‖ ≤ C := fun U =>
    le_of_tendsto (hconv U).norm (Eventually.of_forall fun k => hb k U)
  refine ⟨⟨hGm, C, hGb⟩, measurable_of_tendsto_metrizable (fun k => (hA k).2)
    (tendsto_pi_nhds.mpr fun ρ => ?_)⟩
  have := ρ.2
  exact tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun k => (hA k).1.1.aestronglyMeasurable) (integrable_const C)
    (fun k => ae_of_all _ (hb k)) (ae_of_all _ hconv)
theorem ratPolyAndStateBorelSets_holds : RatPolyAndStateBorelSets := by
  intro L K _ hL _
  have ha : 0 < PeriodicLattice.meshSize L (K : ℤ) := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    exact zpow_pos this _
  exact ⟨ratPolyDense ha, ratPolyApproximates ha,
    ⟨ext_of_realExpectation_ratPoly ha, countable_rationalIntervalBasis,
      rationalIntervalBasis_isBasis ha, borel_eq_iSup_comap_ratPoly ha, measurable_expect ha⟩,
    boundedPointwiseClosure_contains ha⟩
end YangMills.Construction.InfiniteLattice.RatPolyStates

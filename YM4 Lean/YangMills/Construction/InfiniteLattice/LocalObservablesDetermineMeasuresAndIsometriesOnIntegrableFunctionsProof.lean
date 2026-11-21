import YangMills.Construction.InfiniteLattice.ContinuousLocalFunctionsAreDenseAndTestMeasuresProof
import YangMills.Construction.InfiniteLattice.FunctionsOfTheBondsOfASet
import YangMills.Construction.InfiniteLattice.LocalObservablesDetermineMeasuresAndIsometriesOnIntegrableFunctions
import YangMills.Construction.Measures.DenseFunctionsInLp
import YangMills.Construction.ReflectionPositivity.ActionOfTheLatticeIsometriesTheTwoFieldsAndTheReflections
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped Classical ComplexOrder ENNReal NNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace LocalDetermination
def closedCylinderSets : Set (Set (GaugeField 1)) :=
  {Q | ∃ (S : Finset (Link 1)) (K : Set (S → Matrices.ComplexMatrix2.specialUnitary)),
    IsClosed K ∧ Q = restrictTo S ⁻¹' K}
theorem continuous_eval_link (e : Link 1) : Continuous fun A : GaugeField 1 => A e := by apply _root_.YangMills.Construction.InfiniteLattice.ContinuousLocalDensity.continuous_eval_link <;> assumption
theorem continuous_restrictTo (S : Finset (Link 1)) : Continuous (restrictTo S) :=
  continuous_pi fun e => continuous_eval_link e.1
theorem measurable_restrictTo_regionSigma (S : Finset (Link 1)) (R : Set AmbientSpace)
    (hS : ∀ e ∈ S, e ∈ (linksWithin R : Set (Link 1))) :
    Measurable[regionSigma R] (restrictTo S) := by
  refine @measurable_pi_lambda _ _ _ (regionSigma R) _ _ fun e => ?_
  exact measurable_iff_comap_le.mpr (le_iSup₂_of_le e.1 (hS e.1 e.2) le_rfl)
def linkEndpoints (S : Finset (Link 1)) : Set AmbientSpace :=
  (fun e : Link 1 => (e.initial : AmbientSpace)) '' (S : Set (Link 1)) ∪
    (fun e : Link 1 => (e.terminal : AmbientSpace)) '' (S : Set (Link 1))
theorem isLocalObservable_comp_restrictTo (S : Finset (Link 1))
    {φ : (S → Matrices.ComplexMatrix2.specialUnitary) → ℂ}
    [BorelSpace (S → Matrices.ComplexMatrix2.specialUnitary)] (hφ : Measurable φ) :
    IsLocalObservable (φ ∘ restrictTo S) := by
  refine ⟨linkEndpoints S, ?_, ?_⟩
  · exact (((S.finite_toSet).image _).union ((S.finite_toSet).image _)).isBounded
  · refine hφ.comp (measurable_restrictTo_regionSigma S _ fun e he => ?_)
    exact ⟨Or.inl ⟨e, he, rfl⟩, Or.inr ⟨e, he, rfl⟩⟩
section Cylinders
theorem closedCylinderSets_inter_mem {Q Q' : Set (GaugeField 1)} (hQ : Q ∈ closedCylinderSets)
    (hQ' : Q' ∈ closedCylinderSets) : Q ∩ Q' ∈ closedCylinderSets := by
  obtain ⟨S, K, hK, rfl⟩ := hQ
  obtain ⟨S', K', hK', rfl⟩ := hQ'
  let π₁ : (↥(S ∪ S') → Matrices.ComplexMatrix2.specialUnitary) →
      S → Matrices.ComplexMatrix2.specialUnitary :=
    fun v e => v ⟨e.1, Finset.mem_union_left _ e.2⟩
  let π₂ : (↥(S ∪ S') → Matrices.ComplexMatrix2.specialUnitary) →
      S' → Matrices.ComplexMatrix2.specialUnitary :=
    fun v e => v ⟨e.1, Finset.mem_union_right _ e.2⟩
  have hπ₁ : Continuous π₁ := continuous_pi fun e => continuous_apply _
  have hπ₂ : Continuous π₂ := continuous_pi fun e => continuous_apply _
  exact ⟨S ∪ S', π₁ ⁻¹' K ∩ π₂ ⁻¹' K', (hK.preimage hπ₁).inter (hK'.preimage hπ₂), rfl⟩
theorem isPiSystem_closedCylinderSets : IsPiSystem closedCylinderSets :=
  fun _ hQ _ hQ' _ => closedCylinderSets_inter_mem hQ hQ'
theorem generateFrom_closedCylinderSets_eq_borel
    [SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary] :
    MeasurableSpace.generateFrom closedCylinderSets = borel (GaugeField 1) := by
  have : Countable (Link (1 : ℝ)) := WilsonOperator.countable_link
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨S, K, hK, rfl⟩
    have hclosed : IsClosed (restrictTo S ⁻¹' K) := hK.preimage (continuous_restrictTo S)
    rw [← BorelSpace.measurable_eq]
    exact hclosed.measurableSet
  · have h1 : borel (GaugeField 1) =
        (MeasurableSpace.pi : MeasurableSpace
          (Link (1 : ℝ) → Matrices.ComplexMatrix2.specialUnitary)).comap Subtype.val := by
      rw [BorelSpace.measurable_eq (α := Link (1 : ℝ) → Matrices.ComplexMatrix2.specialUnitary)]
      exact borel_comap
    rw [h1, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun e => ?_
    rw [MeasurableSpace.comap_comp]
    refine measurable_iff_comap_le.mp ?_
    refine @measurable_of_isClosed _ _ _ _ _ (MeasurableSpace.generateFrom closedCylinderSets) _ ?_
    intro F hF
    refine MeasurableSpace.measurableSet_generateFrom ⟨{e},
      (fun v => v ⟨e, Finset.mem_singleton_self e⟩) ⁻¹' F, hF.preimage (by fun_prop), rfl⟩
end Cylinders
theorem measure_eq_of_integral_local_eq
    [SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary]
    (μ μ' : Measure (GaugeField 1)) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (h : ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F → IsLocalObservable F →
      ∫ A, F A ∂μ' = ∫ A, F A ∂μ) : μ' = μ := by
  refine ext_of_generate_finite closedCylinderSets
    ((BorelSpace.measurable_eq).trans generateFrom_closedCylinderSets_eq_borel.symm)
    isPiSystem_closedCylinderSets ?_ (by simp)
  rintro _ ⟨S, K, hK, rfl⟩
  have hKm : MeasurableSet K := hK.measurableSet
  have hQ : MeasurableSet (restrictTo S ⁻¹' K) := (continuous_restrictTo S).measurable hKm
  have hobs : IsBoundedObservable ((restrictTo S ⁻¹' K).indicator fun _ => (1 : ℂ)) := by
    refine ⟨measurable_const.indicator hQ, 1, fun A => ?_⟩
    by_cases hA : A ∈ restrictTo S ⁻¹' K <;> simp [hA]
  have hloc : IsLocalObservable ((restrictTo S ⁻¹' K).indicator fun _ => (1 : ℂ)) := by
    have := isLocalObservable_comp_restrictTo S (φ := K.indicator fun _ => (1 : ℂ))
      (measurable_const.indicator hKm)
    convert this using 1
    funext A
    by_cases hA : restrictTo S A ∈ K <;> simp [Set.indicator, hA]
  have hi := h _ hobs hloc
  rw [integral_indicator_const _ hQ, integral_indicator_const _ hQ] at hi
  have hr : μ'.real (restrictTo S ⁻¹' K) = μ.real (restrictTo S ⁻¹' K) := by
    simpa using hi
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hr
theorem pullbackField_pullbackField_of_isInverse {t r : UnitLatticeSymmetry} (h : t.IsInverse r)
    (A : GaugeField 1) : r.pullbackField (t.pullbackField A) = A := by
  refine Subtype.ext (funext fun e => ?_)
  have he : t.linkMap (r.linkMap e) = e := by
    apply Link.ext <;> apply Subtype.ext
    · exact h.1 _
    · exact h.1 _
  change A.1 (t.linkMap (r.linkMap e)) = A.1 e
  rw [he]
theorem compactSpace_metrizableSpace_gaugeField_one :
    CompactSpace (GaugeField 1) ∧ TopologicalSpace.MetrizableSpace (GaugeField 1) := by
  have := WilsonOperator.secondCountable_specialUnitary
  have : Countable (Link (1 : ℝ)) := WilsonOperator.countable_link
  have ha : (0 : ℝ) < 1 := one_pos
  have hc : CompactSpace (GaugeField 1) :=
    (WilsonOperator.gaugeFieldHomeomorph ha).symm.compactSpace
  have hs : SecondCountableTopology (GaugeField 1) :=
    (WilsonOperator.gaugeFieldHomeomorph ha).secondCountableTopology
  have ht : T2Space (GaugeField 1) := (WilsonOperator.gaugeFieldHomeomorph ha).symm.t2Space
  exact ⟨hc, inferInstance⟩
theorem invariantMeasure_consequences (μ : Measure (GaugeField 1)) [IsProbabilityMeasure μ]
    (r t : UnitLatticeSymmetry) (hinv : t.IsInverse r)
    (hr : MeasurePreserving r.pullbackField μ μ)
    (ht : MeasurePreserving t.pullbackField μ μ) :
    (∀ F : GaugeField 1 → ℂ, Measurable F → (∀ A, 0 ≤ F A) →
      ∫⁻ A, ‖r.actOn F A‖ₑ ∂μ = ∫⁻ A, ‖F A‖ₑ ∂μ) ∧
    (∀ F : GaugeField 1 → ℂ, Measurable F → Integrable F μ →
      Integrable (r.actOn F) μ ∧
      ∫ A, r.actOn F A ∂μ = ∫ A, F A ∂μ ∧
      eLpNorm (r.actOn F) 1 μ = eLpNorm F 1 μ) ∧
    (∀ F F' : GaugeField 1 → ℂ, Measurable F → Measurable F' → F =ᵐ[μ] F' →
      r.actOn F =ᵐ[μ] r.actOn F') ∧
    ∃ U : Lp ℂ 2 μ ≃ₗ[ℂ] Lp ℂ 2 μ,
      FormHilbert.IsUnitaryLinearMap (U : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) ∧
      (∀ F : Lp ℂ 2 μ, ⇑(U F) =ᵐ[μ] r.actOn ⇑F) ∧
      ∀ t' : UnitLatticeSymmetry, t'.IsInverse r →
        ∀ F : Lp ℂ 2 μ, ⇑(U.symm F) =ᵐ[μ] t'.actOn ⇑F := by
  refine ⟨fun F hF _ => ?_, fun F hF hi => ⟨?_, ?_, ?_⟩, fun F F' _ _ h => ?_, ?_⟩
  · exact hr.lintegral_comp (f := fun A => ‖F A‖ₑ) hF.enorm
  · exact hr.integrable_comp_of_integrable hi
  · change ∫ A, F (r.pullbackField A) ∂μ = _
    rw [← integral_map hr.measurable.aemeasurable (by rw [hr.map_eq]; exact hF.aestronglyMeasurable),
      hr.map_eq]
  · exact eLpNorm_comp_measurePreserving hF.aestronglyMeasurable hr
  · exact hr.quasiMeasurePreserving.ae_eq_comp h
  · let P : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ := Lp.compMeasurePreservingₗᵢ ℂ _ hr
    let Q : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ := Lp.compMeasurePreservingₗᵢ ℂ _ ht
    have hP : ∀ F : Lp ℂ 2 μ, ⇑(P F) =ᵐ[μ] ⇑F ∘ r.pullbackField :=
      fun F => Lp.coeFn_compMeasurePreserving F hr
    have hQ : ∀ F : Lp ℂ 2 μ, ⇑(Q F) =ᵐ[μ] ⇑F ∘ t.pullbackField :=
      fun F => Lp.coeFn_compMeasurePreserving F ht
    have hPQ : ∀ F : Lp ℂ 2 μ, P (Q F) = F := fun F => by
      refine Lp.ext ((hP (Q F)).trans ?_)
      refine (hr.quasiMeasurePreserving.ae_eq_comp (hQ F)).trans (Eventually.of_forall fun A => ?_)
      change F (t.pullbackField (r.pullbackField A)) = F A
      rw [pullbackField_pullbackField_of_isInverse (t := r) (r := t) ⟨hinv.2, hinv.1⟩]
    have hQP : ∀ F : Lp ℂ 2 μ, Q (P F) = F := fun F => by
      refine Lp.ext ((hQ (P F)).trans ?_)
      refine (ht.quasiMeasurePreserving.ae_eq_comp (hP F)).trans (Eventually.of_forall fun A => ?_)
      change F (r.pullbackField (t.pullbackField A)) = F A
      rw [pullbackField_pullbackField_of_isInverse hinv]
    let U : Lp ℂ 2 μ ≃ₗ[ℂ] Lp ℂ 2 μ :=
      LinearEquiv.ofLinearMap P.toLinearMap Q.toLinearMap (LinearMap.ext hPQ) (LinearMap.ext hQP)
    refine ⟨U, ⟨U.bijective, fun ψ ψ' => P.inner_map_map ψ ψ'⟩, hP, fun t' ht' F => ?_⟩
    have htt : t' = t := by
      have hfun : t'.toFun = t.toFun := funext fun x => by
        have h1 := ht'.1 (t.toFun x)
        rw [hinv.2 x] at h1
        exact h1
      cases t'
      cases t
      cases hfun
      rfl
    subst htt
    exact hQ F
end LocalDetermination
open LocalDetermination in
theorem localDeterminationAndIntegrableAction_proof
    (hDense : Measures.DenseInLp.boundedConvergence_dense)
    (hLocal : LinkLocalFunctions.Statement)
    (hMirrors : ReflectionPositivity.MirrorHyperplanes.SymmetryActionAndReflections)
    (hAction : SymmetryActionOnObservables) :
    LocalDeterminationAndIntegrableAction := by
  intro μ _ r
  have hsc : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    WilsonOperator.secondCountable_specialUnitary
  obtain ⟨hcompact, hmetric⟩ : CompactSpace (GaugeField 1) ∧
      TopologicalSpace.MetrizableSpace (GaugeField 1) :=
    compactSpace_metrizableSpace_gaugeField_one
  have hborel : ∀ (S : Finset (Link 1)), BorelSpace (S → Matrices.ComplexMatrix2.specialUnitary) :=
    fun S => inferInstance
  have hmeas : ∀ s : UnitLatticeSymmetry, Measurable s.pullbackField := fun s =>
    (hMirrors.2.2.2.1 s).2.1.continuous.measurable
  have hact := hAction ⟨1, one_pos⟩
  have hinverses : LatticeSymmetryInverses (1 : ℝ) := hact.2.2.2.2.2.2.2.2.2.1
  have hcomps : SymmetricUnderCompAndMultiples (1 : ℝ) :=
    hact.2.2.2.2.2.2.2.2.2.2
  have hmap : ∀ s : UnitLatticeSymmetry, IsSymmetricUnder μ s →
      MeasurePreserving s.pullbackField μ μ := fun s hs => by
    refine ⟨hmeas s, ?_⟩
    have : IsProbabilityMeasure (μ.map s.pullbackField) :=
      Measure.isProbabilityMeasure_map (hmeas s).aemeasurable
    refine measure_eq_of_integral_local_eq μ _ fun F hF _ => ?_
    rw [integral_map (hmeas s).aemeasurable hF.1.aestronglyMeasurable]
    exact hs F hF
  refine ⟨⟨fun μ' _ h => measure_eq_of_integral_local_eq μ μ' h, fun h => ?_⟩, ?_,
    ⟨?_, ?_, ?_⟩, fun hinv => ?_⟩
  · have : IsProbabilityMeasure (μ.map r.pullbackField) :=
      Measure.isProbabilityMeasure_map (hmeas r).aemeasurable
    have hm : μ.map r.pullbackField = μ := measure_eq_of_integral_local_eq μ _ fun F hF hL => by
      rw [integral_map (hmeas r).aemeasurable hF.1.aestronglyMeasurable]
      exact h F hF hL
    intro G hG
    change ∫ A, G (r.pullbackField A) ∂μ = _
    rw [← integral_map (hmeas r).aemeasurable (by rw [hm]; exact hG.1.aestronglyMeasurable), hm]
  · intro p hp F ε hε
    obtain ⟨⟨M, hM⟩, -⟩ := hLocal.2.2.2.2.1
    have hmem : ∀ f, f ∈ M ↔ IsBoundedObservable f ∧ IsLocalObservable f := fun f => by
      rw [← SetLike.mem_coe, hM]
      rfl
    let 𝒜 : Submodule ℂ (GaugeField 1 → ℂ) :=
      { carrier := {f | Continuous f ∧ IsBoundedObservable f ∧ IsLocalObservable f}
        add_mem' := fun {f g} hf hg => ⟨hf.1.add hg.1,
          (hmem _).mp (M.add_mem ((hmem f).mpr hf.2) ((hmem g).mpr hg.2))⟩
        zero_mem' := ⟨continuous_const, (hmem _).mp M.zero_mem⟩
        smul_mem' := fun c f hf => ⟨hf.1.const_smul c,
          (hmem _).mp (M.smul_mem c ((hmem f).mpr hf.2))⟩ }
    have happrox := (hDense (GaugeField 1) μ inferInstance).1 𝒜 closedCylinderSets
      (fun f hf => ⟨hf.2.1.1, hf.2.1.2⟩) ?_ ?_ ?_ generateFrom_closedCylinderSets_eq_borel ?_
    · obtain ⟨f, hf, hfL, hle⟩ := happrox p hp F ε hε
      refine ⟨f, hf.1, hf.2.1, hf.2.2, ?_⟩
      have he : eLpNorm (⇑F - f) p μ = eLpNorm (⇑(F - hfL.toLp f)) p μ :=
        eLpNorm_congr_ae (((Lp.coeFn_sub F (hfL.toLp f)).trans
          ((Filter.EventuallyEq.refl _ _).sub hfL.coeFn_toLp)).symm)
      rw [he, ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      exact ENNReal.ofReal_le_ofReal hle
    · rintro _ ⟨S, K, hK, rfl⟩
      exact (continuous_restrictTo S).measurable hK.measurableSet
    · intro Q hQ Q' hQ'
      exact closedCylinderSets_inter_mem hQ hQ'
    · exact ⟨∅, Set.univ, isClosed_univ, rfl⟩
    · rintro _ ⟨S, K, hK, rfl⟩
      obtain ⟨fs, h1, -, h3⟩ := HasOuterApproxClosed.exAppr K hK
      let g : ℕ → (S → Matrices.ComplexMatrix2.specialUnitary) → ℂ :=
        fun k v => (((fs k v : ℝ≥0) : ℝ) : ℂ)
      have hgc : ∀ k, Continuous (g k) := fun k =>
        Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (fs k).continuous)
      have hg1 : ∀ k v, ‖g k v‖ ≤ 1 := fun k v => by
        simpa [g] using h1 k v
      refine ⟨fun k => g k ∘ restrictTo S, fun k _ => ⟨⟨(hgc k).comp (continuous_restrictTo S),
        ⟨((hgc k).comp (continuous_restrictTo S)).measurable, 1, fun A => hg1 k _⟩,
        isLocalObservable_comp_restrictTo S (hgc k).measurable⟩, fun A => hg1 k _⟩, fun A => ?_⟩
      have h4 := (tendsto_pi_nhds.mp h3) (restrictTo S A)
      have h5 : Tendsto (fun k => g k (restrictTo S A)) atTop
          (𝓝 (((K.indicator (fun _ => (1 : ℝ≥0)) (restrictTo S A) : ℝ≥0) : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.comp NNReal.continuous_coe).continuousAt.tendsto.comp h4
      have heq : (restrictTo S ⁻¹' K).indicator (1 : GaugeField 1 → ℂ) A =
          (((K.indicator (fun _ => (1 : ℝ≥0)) (restrictTo S A) : ℝ≥0) : ℝ) : ℂ) := by
        by_cases hA : restrictTo S A ∈ K
        · have hA' : A ∈ restrictTo S ⁻¹' K := hA
          rw [Set.indicator_of_mem hA', Set.indicator_of_mem hA]
          simp
        · have hA' : A ∉ restrictTo S ⁻¹' K := hA
          rw [Set.indicator_of_notMem hA', Set.indicator_of_notMem hA]
          simp
      rw [heq]
      exact h5
  · intro G hG
    rfl
  · exact fun r₁ r₂ h₁ h₂ => (hcomps μ inferInstance).1 r₁ r₂ h₁ h₂
  · exact fun r₁ h₁ => ⟨(hMirrors.2.2.2.1 r₁).2.2.1,
      fun t ht => ((hinverses r₁).2.2 t ht).2 μ inferInstance h₁⟩
  · obtain ⟨t, ht⟩ := (hMirrors.2.2.2.1 r).2.2.1
    exact invariantMeasure_consequences μ r t ht (hmap r hinv)
      (hmap t (((hinverses r).2.2 t ht).2 μ inferInstance hinv))
end YangMills.Construction.InfiniteLattice

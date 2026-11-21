import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsAreSmooth
import YangMills.Construction.InfiniteLattice.FactsFromTopologyMeasureAndFunctionTheory
import YangMills.Construction.InfiniteLattice.TorusStatesAreTheVolumeLimitPointsProof
import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import YangMills.Construction.Matrices.HaarExpChartDensity
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter TopologicalSpace
open scoped ComplexConjugate Topology BoundedContinuousFunction ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice.AmbientFacts.Proofs
open YangMills.Construction.FixedSpacing
open YangMills.Construction.Matrices
open YangMills.Construction.Coordinates
theorem metrizableSpace_specialUnitary : MetrizableSpace ComplexMatrix2.specialUnitary := by
  have h : MetrizableSpace ComplexMatrix2 := (inferInstance : MetrizableSpace (Fin 2 → Fin 2 → ℂ))
  exact (Topology.IsEmbedding.subtypeVal
    (p := fun U : ComplexMatrix2 => U ∈ ComplexMatrix2.specialUnitary)).metrizableSpace
theorem secondCountable_specialUnitary : SecondCountableTopology ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
theorem metrizableSpace_linkVariables (ι : Type) [Countable ι] :
    MetrizableSpace (LinkVariables ι) := by
  have := metrizableSpace_specialUnitary
  have := secondCountable_specialUnitary
  infer_instance
theorem isEmbedding_gaugeField_val (a : ℝ) :
    Topology.IsEmbedding (fun U : GaugeField a => (U.1 : Link a → ComplexMatrix2.specialUnitary)) :=
  ⟨⟨rfl⟩, Subtype.val_injective⟩
theorem compactSpace_gaugeField (a : ℝ) : CompactSpace (GaugeField a) := by apply _root_.YangMills.SharedProofs.p823 <;> assumption
theorem metrizableSpace_gaugeField (a : ℝ) : MetrizableSpace (GaugeField a) := by
  have := metrizableSpace_linkVariables (Link a)
  have : MetrizableSpace (Link a → ComplexMatrix2.specialUnitary) := this
  exact (isEmbedding_gaugeField_val a).metrizableSpace
theorem compactMetrizableProducts_holds (a : ℝ) : CompactMetrizableProducts a :=
  ⟨fun S _ => ⟨inferInstance, metrizableSpace_linkVariables S⟩, compactSpace_gaugeField a,
    metrizableSpace_gaugeField a⟩
section StoneWeierstrass
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
def toStarSubalgebra (A : Set (X → ℂ)) (hA : IsSeparatingStarSubalgebra A) :
    StarSubalgebra ℂ C(X, ℂ) where
  carrier := {f | (f : X → ℂ) ∈ A}
  mul_mem' := fun {f g} hf hg => (hA.2.1 f hf g hg).2
  add_mem' := fun {f g} hf hg => (hA.2.1 f hf g hg).1
  algebraMap_mem' := fun c => hA.2.2.2.1 c
  star_mem' := fun {f} hf => hA.2.2.2.2.1 f hf
theorem isSupDense_of_starSubalgebra (A : Set (X → ℂ)) (hA : IsSeparatingStarSubalgebra A) :
    IsSupDense A := by
  intro F hF ε hε
  have sep : (toStarSubalgebra A hA).SeparatesPoints := by
    intro x y hxy
    obtain ⟨Φ, hΦ, hne⟩ := hA.2.2.2.2.2 x y hxy
    refine ⟨Φ, ⟨⟨Φ, hA.1 hΦ⟩, hΦ, rfl⟩, hne⟩
  have top := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (toStarSubalgebra A hA) sep
  have mem : (⟨F, hF⟩ : C(X, ℂ)) ∈ closure ((toStarSubalgebra A hA : Set C(X, ℂ))) := by
    have : (⟨F, hF⟩ : C(X, ℂ)) ∈ (toStarSubalgebra A hA).topologicalClosure := by
      rw [top]; trivial
    exact this
  obtain ⟨H, hH, hd⟩ := Metric.mem_closure_iff.mp mem (ε / 2) (half_pos hε)
  refine ⟨H, hH, ?_⟩
  have bound : ∀ x, ‖(F - H) x‖ₑ ≤ ENNReal.ofReal (ε / 2) := by
    intro x
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    have := ContinuousMap.dist_apply_le_dist (f := (⟨F, hF⟩ : C(X, ℂ))) (g := H) x
    rw [dist_eq_norm] at this
    exact this.trans hd.le
  calc normSup (F - ⇑H) ≤ ENNReal.ofReal (ε / 2) := iSup_le bound
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε)
end StoneWeierstrass
theorem continuous_entry (i j : Fin 2) :
    Continuous fun U : ComplexMatrix2.specialUnitary => (U : ComplexMatrix2) i j :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
theorem exists_entry_ne_of_ne {U V : ComplexMatrix2.specialUnitary} (h : U ≠ V) :
    ∃ i j, (U : ComplexMatrix2) i j ≠ (V : ComplexMatrix2) i j := by
  by_contra hc
  push Not at hc
  exact h (Subtype.ext (Matrix.ext hc))
theorem isSeparatingStarSubalgebra_finiteCoord (ι : Type) :
    IsSeparatingStarSubalgebra (finiteCoordContinuous ι) := by
  refine ⟨fun Φ h => h.1, ?_, ?_, ?_, ?_, ?_⟩
  · rintro Φ ⟨c, I, fI, dI⟩ Φ' ⟨c', I', fI', dI'⟩
    have d₁ : ∀ V V' : LinkVariables ι, (∀ k ∈ I ∪ I', V k = V' k) → Φ V = Φ V' ∧ Φ' V = Φ' V' :=
      fun V V' h => ⟨dI V V' fun k hk => h k (Or.inl hk), dI' V V' fun k hk => h k (Or.inr hk)⟩
    refine ⟨⟨c.add c', I ∪ I', fI.union fI', fun V V' h => ?_⟩,
      ⟨c.mul c', I ∪ I', fI.union fI', fun V V' h => ?_⟩⟩
    · simp only [Pi.add_apply, (d₁ V V' h).1, (d₁ V V' h).2]
    · simp only [Pi.mul_apply, (d₁ V V' h).1, (d₁ V V' h).2]
  · rintro c Φ ⟨h, I, fI, dI⟩
    refine ⟨continuous_const.smul h, I, fI, fun V V' hV => ?_⟩
    simp only [Pi.smul_apply, dI V V' hV]
  · exact fun c => ⟨continuous_const, ∅, finite_empty, fun _ _ _ => rfl⟩
  · rintro Φ ⟨h, I, fI, dI⟩
    refine ⟨Complex.continuous_conj.comp h, I, fI, fun V V' hV => ?_⟩
    simp only [dI V V' hV]
  · intro x y hxy
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hxy
    obtain ⟨i, j, hij⟩ := exists_entry_ne_of_ne hk
    refine ⟨fun V => (V k : ComplexMatrix2) i j, ⟨(continuous_entry i j).comp (continuous_apply k),
      {k}, finite_singleton k, fun V V' h => ?_⟩, hij⟩
    simp only [h k (mem_singleton k)]
theorem isSeparatingStarSubalgebra_cylinder (a : ℝ) :
    IsSeparatingStarSubalgebra (continuousCylinderFunctions a) := by
  have mono : ∀ {W W' : Set (Link a)} {F : GaugeField a → ℂ}, W ⊆ W' → DependsOnlyOnLinks W F →
      DependsOnlyOnLinks W' F := fun {W W' F} hW hF U U' h => hF U U' (by
        funext e
        exact congrFun h ⟨e.1, hW e.2⟩)
  refine ⟨fun Φ h => h.1, ?_, ?_, ?_, ?_, ?_⟩
  · rintro Φ ⟨c, W, fW, sW, dW⟩ Φ' ⟨c', W', fW', sW', dW'⟩
    have d₁ := mono subset_union_left dW (W' := W ∪ W')
    have d₂ := mono subset_union_right dW' (W' := W ∪ W')
    refine ⟨⟨c.add c', W ∪ W', fW.union fW', union_subset sW sW', fun U U' h => ?_⟩,
      ⟨c.mul c', W ∪ W', fW.union fW', union_subset sW sW', fun U U' h => ?_⟩⟩
    · simp only [Pi.add_apply, d₁ U U' h, d₂ U U' h]
    · simp only [Pi.mul_apply, d₁ U U' h, d₂ U U' h]
  · rintro c Φ ⟨h, W, fW, sW, dW⟩
    refine ⟨continuous_const.smul h, W, fW, sW, fun U U' hU => ?_⟩
    simp only [Pi.smul_apply, dW U U' hU]
  · exact fun c => ⟨continuous_const, ∅, finite_empty, empty_subset _, fun _ _ _ => rfl⟩
  · rintro Φ ⟨h, W, fW, sW, dW⟩
    refine ⟨Complex.continuous_conj.comp h, W, fW, sW, fun U U' hU => ?_⟩
    simp only [dW U U' hU]
  · intro U U' hne
    have : ∃ e ∈ positiveLinkSet a, U e ≠ U' e := by
      by_contra hc
      push Not at hc
      apply hne
      apply Subtype.ext
      funext e
      rcases mem_positiveLinks_or_opposite_mem e with h | h
      · exact hc e h
      · have := hc _ h
        rw [U.2 e, U'.2 e] at this
        exact inv_injective this
    obtain ⟨e, he, hUe⟩ := this
    obtain ⟨i, j, hij⟩ := exists_entry_ne_of_ne hUe
    refine ⟨fun V => (V e : ComplexMatrix2) i j, ⟨?_, {e}, finite_singleton e, ?_, fun V V' h => ?_⟩, hij⟩
    · exact (continuous_entry i j).comp
        ((continuous_apply e).comp (isEmbedding_gaugeField_val a).continuous)
    · exact singleton_subset_iff.mpr he
    · have := congrFun h ⟨e, mem_singleton e⟩
      simp only [restrictField] at this
      simp only [this]
theorem cylinderFunctionsDense_holds (a : ℝ) : CylinderFunctionsDense a := by
  have := compactSpace_gaugeField a
  refine ⟨fun S _ => ⟨isSeparatingStarSubalgebra_finiteCoord S,
      isSupDense_of_starSubalgebra _ (isSeparatingStarSubalgebra_finiteCoord S)⟩,
    isSupDense_of_starSubalgebra _ (isSeparatingStarSubalgebra_cylinder a)⟩
section Determined
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] [MeasurableSpace X]
  [BorelSpace X]
omit [MetrizableSpace X] in
theorem integrable_of_continuous_of_compact (ν : Measure X) [IsProbabilityMeasure ν] {F : X → ℂ}
    (hF : Continuous F) : Integrable F ν :=
  (BoundedContinuousFunction.mkOfCompact (⟨F, hF⟩ : C(X, ℂ))).integrable ν
omit [CompactSpace X] in
theorem measure_eq_of_integral_continuous_eq (ν ν' : Measure X) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] (h : ∀ F : X → ℂ, Continuous F → ∫ x, F x ∂ν = ∫ x, F x ∂ν') :
    ν = ν' := by
  let := metrizableSpaceMetric X
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have := h (fun x => (f x : ℂ)) (Complex.continuous_ofReal.comp f.continuous)
  rw [integral_complex_ofReal, integral_complex_ofReal] at this
  exact_mod_cast this
omit [MetrizableSpace X] in
theorem integral_eq_of_supDenseSpan {𝒟 : Set (X → ℂ)} (hD : HasSupDenseSpan 𝒟)
    (ν ν' : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (h : ∀ F ∈ 𝒟, ∫ x, F x ∂ν = ∫ x, F x ∂ν') (F : X → ℂ) (hF : Continuous F) :
    ∫ x, F x ∂ν = ∫ x, F x ∂ν' := by
  have sp : ∀ H ∈ Submodule.span ℂ 𝒟, Continuous H ∧ ∫ x, H x ∂ν = ∫ x, H x ∂ν' := by
    intro H hH
    induction hH using Submodule.span_induction with
    | mem x hx => exact ⟨hD.1 hx, h x hx⟩
    | zero => exact ⟨continuous_const, by simp⟩
    | add x y _ _ hx hy =>
      refine ⟨hx.1.add hy.1, ?_⟩
      simp only [Pi.add_apply]
      rw [integral_add (integrable_of_continuous_of_compact ν hx.1)
          (integrable_of_continuous_of_compact ν hy.1),
        integral_add (integrable_of_continuous_of_compact ν' hx.1)
          (integrable_of_continuous_of_compact ν' hy.1),
        hx.2, hy.2]
    | smul c x _ hx =>
      refine ⟨continuous_const.smul hx.1, ?_⟩
      simp only [Pi.smul_apply, integral_smul, hx.2]
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨H, hH, hlt⟩ := hD.2 F hF (ε / 2) (half_pos hε)
  obtain ⟨cH, eH⟩ := sp H hH
  have bound : ∀ x, ‖F x - H x‖ ≤ ε / 2 := by
    intro x
    have h₁ : ‖(F - H) x‖ₑ ≤ normSup (F - H) := le_iSup (fun x => ‖(F - H) x‖ₑ) x
    have h₂ := h₁.trans hlt.le
    rw [← ofReal_norm] at h₂
    exact (ENNReal.ofReal_le_ofReal_iff (half_pos hε).le).mp h₂
  have est : ∀ (μ : Measure X) [IsProbabilityMeasure μ],
      ‖∫ x, F x ∂μ - ∫ x, H x ∂μ‖ ≤ ε / 2 := by
    intro μ _
    rw [← integral_sub (integrable_of_continuous_of_compact μ hF)
      (integrable_of_continuous_of_compact μ cH)]
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => F x - H x)
      (Eventually.of_forall bound)
    simpa using this
  rw [dist_eq_norm]
  have e₁ := est ν
  have e₂ := est ν'
  rw [← eH] at e₂
  calc ‖∫ x, F x ∂ν - ∫ x, F x ∂ν'‖
      = ‖(∫ x, F x ∂ν - ∫ x, H x ∂ν) - (∫ x, F x ∂ν' - ∫ x, H x ∂ν)‖ := by congr 1; ring
    _ ≤ ε / 2 + ε / 2 := (norm_sub_le _ _).trans (add_le_add e₁ e₂)
    _ = ε := add_halves ε
end Determined
theorem denseSpanDeterminesMeasure_holds (a : ℝ) : DenseSpanDeterminesMeasure a := by
  have := compactSpace_gaugeField a
  have := metrizableSpace_gaugeField a
  refine ⟨⟨fun F h => h.1, fun F hF ε hε => ?_⟩, fun 𝒟 hD ν ν' _ _ h =>
    measure_eq_of_integral_continuous_eq ν ν' (integral_eq_of_supDenseSpan hD ν ν' h)⟩
  obtain ⟨H, hH, hlt⟩ := (cylinderFunctionsDense_holds a).2 F hF ε hε
  exact ⟨H, Submodule.subset_span hH, hlt⟩
section Weak
variable (a : ℝ)
def probabilityMeasureEquiv : ProbabilityMeasure (GaugeField a) ≃ GaugeFieldProbability a where
  toFun μ := ⟨μ.1, μ.2⟩
  invFun ν := ⟨ν.1, ν.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem continuous_integral_complex (F : GaugeField a →ᵇ ℂ) :
    Continuous fun μ : ProbabilityMeasure (GaugeField a) =>
      ∫ U, F U ∂(μ : Measure (GaugeField a)) := by
  have := compactSpace_gaugeField a
  let Fr : GaugeField a →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun U => (F U).re, Complex.continuous_re.comp F.continuous⟩
  let Fi : GaugeField a →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun U => (F U).im, Complex.continuous_im.comp F.continuous⟩
  have e : (fun μ : ProbabilityMeasure (GaugeField a) =>
      ∫ U, F U ∂(μ : Measure (GaugeField a))) =
      fun μ : ProbabilityMeasure (GaugeField a) =>
        ((∫ U, Fr U ∂(μ : Measure (GaugeField a)) : ℝ) : ℂ) +
        ((∫ U, Fi U ∂(μ : Measure (GaugeField a)) : ℝ) : ℂ) * Complex.I := by
    funext μ
    have hi := F.integrable (μ : Measure (GaugeField a))
    exact (integral_re_add_im hi).symm
  rw [e]
  exact (Complex.continuous_ofReal.comp
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction Fr)).add
    ((Complex.continuous_ofReal.comp
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction Fi)).mul continuous_const)
theorem continuous_probabilityMeasureEquiv : Continuous (probabilityMeasureEquiv a) := by
  refine continuous_iInf_rng.2 fun F => continuous_induced_rng.2 ?_
  exact continuous_integral_complex a F
theorem t2Space_gaugeFieldProbability : T2Space (GaugeFieldProbability a) := by
  have := compactSpace_gaugeField a
  have := metrizableSpace_gaugeField a
  refine T2Space.of_injective_continuous
    (f := fun (ν : GaugeFieldProbability a) (F : GaugeField a →ᵇ ℂ) => ν.expect F) ?_ ?_
  · intro ν ν' h
    have := ν.2
    have := ν'.2
    refine Subtype.ext (measure_eq_of_integral_continuous_eq ν.1 ν'.1 fun F hF => ?_)
    exact congrFun h (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩)
  · refine continuous_pi fun F => ?_
    exact continuous_iInf_dom (i := F) continuous_induced_dom
theorem weakProbabilitiesCompactMetrizable_holds : WeakProbabilitiesCompactMetrizable a := by
  have := compactSpace_gaugeField a
  have := metrizableSpace_gaugeField a
  have := t2Space_gaugeFieldProbability a
  let := metrizableSpaceMetric (GaugeField a)
  let e := (continuous_probabilityMeasureEquiv a).homeoOfEquivCompactToT2
  exact ⟨e.compactSpace, e.symm.isEmbedding.metrizableSpace⟩
end Weak
theorem lintegral_enorm_sq_eq {𝒴 : Type} [MeasurableSpace 𝒴] (η : Measure 𝒴) (f : 𝒴 → ℂ) :
    ∫⁻ y, ‖f y‖ₑ ^ 2 ∂η = eLpNorm f 2 η ^ 2 := by
  have := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := η) (p := 2) two_ne_zero
  simpa using this.symm
theorem continuousDenseInMeanSquare_holds : ContinuousDenseInMeanSquare := by
  intro 𝒴 _ _ _ _ _ η _
  let := metrizableSpaceMetric 𝒴
  refine ⟨fun H hH => ⟨hH.measurable, ?_⟩, fun F hF ε hε => ?_⟩
  · obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hH.continuousOn
    calc ∫⁻ y, ‖H y‖ₑ ^ 2 ∂η ≤ ∫⁻ _, ENNReal.ofReal C ^ 2 ∂η := by
          refine lintegral_mono fun y => ?_
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hC y (mem_univ y))
      _ < ⊤ := by simp
  · have hm : MemLp F 2 η := by
      refine ⟨hF.1.aestronglyMeasurable, ?_⟩
      have h₂ := hF.2
      rw [lintegral_enorm_sq_eq] at h₂
      exact (ENNReal.pow_lt_top_iff.mp h₂).resolve_right (by norm_num)
    have hs : ENNReal.ofReal (Real.sqrt ε) ≠ 0 := by
      simpa using Real.sqrt_pos.mpr hε
    obtain ⟨g, hg, -⟩ := hm.exists_boundedContinuous_eLpNorm_sub_le (by simp) hs
    refine ⟨g, g.continuous, ?_⟩
    have e := lintegral_enorm_sq_eq η (F - ⇑g)
    simp only [Pi.sub_apply] at e
    rw [e]
    calc eLpNorm (F - ⇑g) 2 η ^ 2 ≤ ENNReal.ofReal (Real.sqrt ε) ^ 2 := by gcongr
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg ε), Real.sq_sqrt hε.le]
theorem haarInvariance_holds (hF2 : ComplexMatrix2.HaarExpChartProperties) :
    HaarInvariance := by
  have hl : ComplexMatrix2.haarProb.IsMulLeftInvariant := by
    unfold ComplexMatrix2.haarProb; infer_instance
  have transl := hF2.2.2.1
  have hinv := hF2.2.2.2
  refine ⟨hl, ⟨fun g => by simpa using transl 1 g⟩, ⟨hinv⟩, fun I _ => ?_⟩
  cases nonempty_fintype I
  classical
  have e : LinkVariables.haarMeasure I = Measure.pi fun _ : I => ComplexMatrix2.haarProb := by
    unfold LinkVariables.haarMeasure ComplexMatrix2.haarPi
    exact Measure.infinitePi_eq_pi _
  rw [e]
  have minv : MeasurePreserving (fun U : ComplexMatrix2.specialUnitary => U⁻¹)
      ComplexMatrix2.haarProb ComplexMatrix2.haarProb :=
    ⟨continuous_inv.measurable, hinv⟩
  have mleft : ∀ W : ComplexMatrix2.specialUnitary,
      MeasurePreserving (fun U : ComplexMatrix2.specialUnitary => W * U)
        ComplexMatrix2.haarProb ComplexMatrix2.haarProb :=
    fun W => ⟨(continuous_const.mul continuous_id).measurable, by simpa using transl W 1⟩
  refine ⟨fun σ => ?_, fun J => ?_, fun W => ?_⟩
  · have h := measurePreserving_piCongrLeft (fun _ : I => ComplexMatrix2.haarProb) σ.symm
    have fe : (MeasurableEquiv.piCongrLeft (fun _ : I => ComplexMatrix2.specialUnitary) σ.symm :
        LinkVariables I → _) = fun V : LinkVariables I => V ∘ σ := by
      funext V i
      have := Equiv.piCongrLeft_apply_apply (fun _ : I => ComplexMatrix2.specialUnitary) σ.symm V (σ i)
      simpa [MeasurableEquiv.coe_piCongrLeft] using this
    rw [fe] at h
    exact h
  · have h := measurePreserving_pi (fun _ : I => ComplexMatrix2.haarProb)
      (fun _ : I => ComplexMatrix2.haarProb)
      (f := fun i => if i ∈ J then (fun U : ComplexMatrix2.specialUnitary => U⁻¹) else id)
      (fun i => by
        by_cases hi : i ∈ J
        · simpa [hi] using minv
        · simpa [hi] using MeasurePreserving.id ComplexMatrix2.haarProb)
    have fe : (fun (V : LinkVariables I) (i : I) => if i ∈ J then (V i)⁻¹ else V i) =
        fun V i => (if i ∈ J then (fun U : ComplexMatrix2.specialUnitary => U⁻¹) else id) (V i) := by
      funext V i
      by_cases hi : i ∈ J <;> simp [hi]
    convert h using 1
  · exact measurePreserving_pi (fun _ : I => ComplexMatrix2.haarProb)
      (fun _ : I => ComplexMatrix2.haarProb)
      (f := fun i U => W i * U) fun i => mleft (W i)
section Cauchy
def ballPolydisc (n : ℕ) (t : ℝ) : Set (ComplexCoordinates n) := {z | ∀ j, ‖z j‖ < 2 * t}
theorem isOpen_ballPolydisc (n : ℕ) (t : ℝ) : IsOpen (ballPolydisc n t) := by
  have : ballPolydisc n t = ⋂ j, {z : ComplexCoordinates n | ‖z j‖ < 2 * t} := by
    ext z
    simp [ballPolydisc]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt (continuous_norm.comp (continuous_apply j)) continuous_const
def tailEmbedding (n : ℕ) : ComplexCoordinates n →L[ℂ] ComplexCoordinates (n + 1) :=
  ContinuousLinearMap.pi fun i => Fin.cases 0 (fun j => ContinuousLinearMap.proj j) i
theorem tailEmbedding_apply_zero (n : ℕ) (w : ComplexCoordinates n) : tailEmbedding n w 0 = 0 := by
  simp [tailEmbedding]
theorem tailEmbedding_apply_succ (n : ℕ) (w : ComplexCoordinates n) (j : Fin n) :
    tailEmbedding n w j.succ = w j := by
  simp [tailEmbedding]
theorem cons_eq_cons_zero_add (n : ℕ) (z : ℂ) (w : ComplexCoordinates n) :
    (Fin.cons z w : ComplexCoordinates (n + 1)) = (Fin.cons z 0 : ComplexCoordinates (n + 1)) +
      tailEmbedding n w := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [tailEmbedding_apply_zero]
  · simp [tailEmbedding_apply_succ]
theorem cons_zero_eq_smul_single (n : ℕ) (z : ℂ) :
    (Fin.cons z 0 : ComplexCoordinates (n + 1)) =
      z • (Pi.single 0 1 : ComplexCoordinates (n + 1)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp
theorem cons_mem_ballPolydisc {n : ℕ} {t : ℝ} {z : ℂ} {w : ComplexCoordinates n}
    (hz : ‖z‖ < 2 * t) (hw : w ∈ ballPolydisc n t) :
    (Fin.cons z w : ComplexCoordinates (n + 1)) ∈ ballPolydisc (n + 1) t := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hz
  · simpa using hw j
theorem zero_mem_ballPolydisc {n : ℕ} {t : ℝ} (ht : 0 < t) :
    (0 : ComplexCoordinates n) ∈ ballPolydisc n t :=
  fun j => by simpa using ht
theorem iteratedFDeriv_tail_slice {n : ℕ} {t : ℝ} {h : ComplexCoordinates (n + 1) → ℂ}
    (hh : ContDiffOn ℂ ∞ h (ballPolydisc (n + 1) t)) {c : ComplexCoordinates (n + 1)}
    (hc : c ∈ ballPolydisc (n + 1) t) (v : Fin n → ComplexCoordinates n) :
    iteratedFDeriv ℂ n (fun w => h (c + tailEmbedding n w)) 0 v =
      iteratedFDeriv ℂ n h c fun i => tailEmbedding n (v i) := by
  set s : Set (ComplexCoordinates (n + 1)) := (fun y => c + y) ⁻¹' ballPolydisc (n + 1) t with hs
  have so : IsOpen s := (isOpen_ballPolydisc _ _).preimage (continuous_const.add continuous_id)
  have f1 : ContDiffOn ℂ ∞ (fun y => h (c + y)) s :=
    hh.comp (contDiff_const.add contDiff_id).contDiffOn fun y hy => hy
  have s0 : (0 : ComplexCoordinates (n + 1)) ∈ s := by simpa [hs] using hc
  have so' : IsOpen (tailEmbedding n ⁻¹' s) := so.preimage (tailEmbedding n).continuous
  have s0' : (0 : ComplexCoordinates n) ∈ tailEmbedding n ⁻¹' s := by simpa using s0
  have key := (tailEmbedding n).iteratedFDerivWithin_comp_right f1 so.uniqueDiffOn
    so'.uniqueDiffOn (x := 0) (by simpa using s0) (i := n) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen n so' s0',
    iteratedFDerivWithin_of_isOpen n so (by simpa using s0)] at key
  have e := congrArg (fun A => A v) key
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at e
  have e' : iteratedFDeriv ℂ n (fun y => h (c + y)) (tailEmbedding n 0) =
      iteratedFDeriv ℂ n h c := by
    rw [iteratedFDeriv_comp_add_left n c (tailEmbedding n 0)]
    simp
  rw [e'] at e
  exact e
theorem iterCircleIntegral_const_mul (t : ℝ) (n : ℕ) (c : ℂ) (f : ComplexCoordinates n → ℂ) :
    iterCircleIntegral t n (fun w => c * f w) = c * iterCircleIntegral t n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iterCircleIntegral, ih]
    exact circleIntegral.integral_smul c
      (fun z => iterCircleIntegral t n fun w => f (Fin.cons z w)) 0 t
theorem iteratedFDeriv_eq_iterCircleIntegral {t : ℝ} (ht : 0 < t) (n : ℕ)
    (h : ComplexCoordinates n → ℂ) (hh : ContDiffOn ℂ ∞ h (ballPolydisc n t)) :
    iteratedFDeriv ℂ n h 0 (fun i => Pi.single i 1) =
      (2 * (Real.pi : ℂ) * Complex.I) ^ (-(n : ℤ)) *
        iterCircleIntegral t n fun z => h z * ∏ j, z j ^ (-2 : ℤ) := by
  induction n with
  | zero => simp [iterCircleIntegral]
  | succ n ih =>
    have cne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hcdef
    set u : Fin n → ComplexCoordinates (n + 1) :=
      fun i => tailEmbedding n (Pi.single i 1) with hu
    set e0 : ComplexCoordinates (n + 1) := Pi.single 0 1 with he0
    set A := iteratedFDeriv ℂ n h with hA
    set D : ℂ → ℂ := fun z => A (z • e0) u with hD
    have po := isOpen_ballPolydisc (n + 1) t
    have hAd : DifferentiableOn ℂ A (ballPolydisc (n + 1) t) := by
      have := hh.differentiableOn_iteratedFDerivWithin (m := n)
        (by exact_mod_cast WithTop.coe_lt_top _) po.uniqueDiffOn
      exact this.congr fun x hx => (iteratedFDerivWithin_of_isOpen n po hx).symm
    have mem : ∀ z : ℂ, ‖z‖ < 2 * t → z • e0 ∈ ballPolydisc (n + 1) t := by
      intro z hz
      rw [he0, ← cons_zero_eq_smul_single]
      exact cons_mem_ballPolydisc hz (zero_mem_ballPolydisc ht)
    have hDat : ∀ z : ℂ, ‖z‖ < 2 * t → HasDerivAt D
        ((fderiv ℂ A (z • e0)) e0 u) z := by
      intro z hz
      have hA' : HasFDerivAt A (fderiv ℂ A (z • e0)) (z • e0) :=
        ((hAd _ (mem z hz)).differentiableAt (po.mem_nhds (mem z hz))).hasFDerivAt
      have h₁ : HasDerivAt (fun z : ℂ => z • e0) e0 z := by
        simpa using (hasDerivAt_id z).smul_const e0
      have h₂ := hA'.comp_hasDerivAt z h₁
      exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => ComplexCoordinates (n + 1)) ℂ
        u).hasFDerivAt.comp_hasDerivAt z h₂)
    have hDd : DifferentiableOn ℂ D (Metric.ball 0 (2 * t)) := fun z hz =>
      (hDat z (by simpa using hz)).differentiableAt.differentiableWithinAt
    have slice : ∀ z : ℂ, ‖z‖ < 2 * t →
        iterCircleIntegral t n (fun w => h (Fin.cons z w) * ∏ j, w j ^ (-2 : ℤ)) =
          c ^ (n : ℤ) * D z := by
      intro z hz
      have g : ContDiffOn ℂ ∞ (fun w => h (z • e0 + tailEmbedding n w)) (ballPolydisc n t) := by
        refine hh.comp (contDiff_const.add (tailEmbedding n).contDiff).contDiffOn fun w hw => ?_
        have := cons_mem_ballPolydisc hz hw
        rwa [cons_eq_cons_zero_add, cons_zero_eq_smul_single] at this
      have := ih _ g
      rw [iteratedFDeriv_tail_slice hh (mem z hz)] at this
      have e : ∀ w : ComplexCoordinates n, z • e0 + tailEmbedding n w =
          (Fin.cons z w : ComplexCoordinates (n + 1)) := by
        intro w
        rw [cons_eq_cons_zero_add, cons_zero_eq_smul_single]
      simp only [e] at this
      have D' : D z = c ^ (-(n : ℤ)) *
          iterCircleIntegral t n (fun w => h (Fin.cons z w) * ∏ j, w j ^ (-2 : ℤ)) := this
      rw [D', ← mul_assoc, ← zpow_add₀ cne]
      simp
    have cd := Complex.cderiv_eq_deriv (f := D) (r := t) (z := 0) Metric.isOpen_ball hDd ht
      (Metric.closedBall_subset_ball (by simpa using by linarith))
    have left : iteratedFDeriv ℂ (n + 1) h 0 (fun i => Pi.single i 1) = deriv D 0 := by
      rw [iteratedFDeriv_succ_apply_left, (hDat 0 (by simpa using ht)).deriv]
      have tl : Fin.tail (fun i : Fin (n + 1) => (Pi.single i 1 : ComplexCoordinates (n + 1))) =
          u := by
        funext i k
        refine Fin.cases ?_ (fun j => ?_) k
        · simp [hu, tailEmbedding_apply_zero, Fin.tail]
        · simp [hu, tailEmbedding_apply_succ, Fin.tail, Pi.single_apply]
      rw [tl]
      simp [hA, he0]
    have right : iterCircleIntegral t (n + 1)
        (fun z => h z * ∏ j, z j ^ (-2 : ℤ)) =
        c ^ (n : ℤ) * ∮ z in C(0, t), ((z - 0) ^ 2)⁻¹ • D z := by
      have eq : Set.EqOn (fun z : ℂ => iterCircleIntegral t n fun w =>
            h (Fin.cons z w) * ∏ j, (Fin.cons z w : ComplexCoordinates (n + 1)) j ^ (-2 : ℤ))
          (fun z : ℂ => c ^ (n : ℤ) • (((z - 0) ^ 2)⁻¹ • D z)) (Metric.sphere 0 t) := by
        intro z hz
        have hz' : ‖z‖ < 2 * t := by
          have : ‖z‖ = t := by simpa using hz
          linarith
        have e : (fun w : ComplexCoordinates n =>
            h (Fin.cons z w) * ∏ j, (Fin.cons z w : ComplexCoordinates (n + 1)) j ^ (-2 : ℤ)) =
            fun w => (z ^ (-2 : ℤ)) * (h (Fin.cons z w) * ∏ j, w j ^ (-2 : ℤ)) := by
          funext w
          rw [Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          ring
        simp only [e]
        rw [iterCircleIntegral_const_mul, slice z hz']
        simp only [smul_eq_mul, sub_zero]
        rw [zpow_neg]
        norm_cast
        ring
      have := circleIntegral.integral_congr ht.le eq
      simp only [iterCircleIntegral]
      rw [this]
      exact circleIntegral.integral_smul (c ^ (n : ℤ))
        (fun z => ((z - 0) ^ 2)⁻¹ • D z) 0 t
    rw [left, right, ← cd, Complex.cderiv, ← hcdef]
    simp only [smul_eq_mul]
    rw [← mul_assoc, ← zpow_add₀ cne]
    congr 1
    rw [← zpow_neg_one]
    congr 1
    push_cast
    ring
end Cauchy
theorem cauchyMixedDerivative_holds
    (hS : SeveralComplexVariables.HolomorphicContDiff.Statement) :
    CauchyMixedDerivative := by
  intro n hn t ht h hh
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine iteratedFDeriv_eq_iterCircleIntegral ht n h (hS (Fin n) _ h ⟨hh.1, ?_, fun c hc q => ?_⟩)
  · exact (continuous_apply (0 : Fin 1)).comp_continuousOn hh.2.1
  · refine (hh.2.2 c hc q).mono fun ζ hζ => ?_
    have eq : SeveralComplexVariables.basisVector q = ComplexCoordinates.stdBasisVector q := by
      funext k
      simp [SeveralComplexVariables.basisVector, ComplexCoordinates.stdBasisVector, Pi.single_apply]
    rw [eq]
    exact differentiableAt_pi.mp hζ 0
theorem allFacts_holds (hF2 : ComplexMatrix2.HaarExpChartProperties)
    (hS : SeveralComplexVariables.HolomorphicContDiff.Statement) : AllFacts :=
  ⟨fun D => ⟨compactMetrizableProducts_holds D.mesh, cylinderFunctionsDense_holds D.mesh,
    weakProbabilitiesCompactMetrizable_holds D.mesh, denseSpanDeterminesMeasure_holds D.mesh⟩,
    continuousDenseInMeanSquare_holds, haarInvariance_holds hF2, cauchyMixedDerivative_holds hS⟩
end YangMills.Construction.InfiniteLattice.AmbientFacts.Proofs

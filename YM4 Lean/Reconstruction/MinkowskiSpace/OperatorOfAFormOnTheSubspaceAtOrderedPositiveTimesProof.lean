import YangMills.Construction.Continuum.FormIsSesquilinearAndPositiveSemiDefinite
import Reconstruction.Continuum.InvarianceOfSequenceOnTestFunctionSpaces
import Reconstruction.HilbertSpaces.UnitaryOperatorOfTwoFamiliesWithOneGramMatrix
import Reconstruction.MinkowskiSpace.OperatorOfAFormOnTheSubspaceAtOrderedPositiveTimes
import Reconstruction.MinkowskiSpace.ScalarProductsOfTheVectorsOfSmoothSequences
import Reconstruction.MinkowskiSpace.TimeTranslationOfTheVectorsOfSmoothSequences
import Reconstruction.MinkowskiSpace.VectorsOfSmoothSequencesAreTotalInTheClosedSubspace
import Reconstruction.MinkowskiSpace.VectorsOfSmoothSequencesLieInTheClosedSubspace
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction.MinkowskiSpace.IsometryConstruction
open YangMills.Construction.MinkowskiSpace YangMills.Construction.FieldForms YangMills.Construction.ConfigSpace YangMills.Construction.RealPointVectors YangMills.Construction.WightmanTheory YangMills.Construction.FieldFormHilbert YangMills.Construction.ProjectionMeasures YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert YangMills.Construction.FormReconstruction
theorem weakInt_eq_zero_of_eq_zero {H P : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace P] [MeasureTheory.MeasureSpace P] (C : Set P) (Ξ : P → H)
    (f : P → ℂ) (hf : f = 0) : ProjectionMeasures.weakInt C Ξ f = 0 := by
  subst hf
  have h0 : ProjectionMeasures.HasWeakIntegral C Ξ (0 : P → ℂ) 0 := fun v => by simp
  have h1 : ProjectionMeasures.HasWeakIntegral C Ξ (0 : P → ℂ)
      (ProjectionMeasures.weakInt C Ξ 0) :=
    Classical.epsilon_spec (p := ProjectionMeasures.HasWeakIntegral C Ξ (0 : P → ℂ)) ⟨0, h0⟩
  exact ext_inner_left ℂ fun v => (h1 v).trans (h0 v).symm
section SpanForm
variable {S : ConfigSpace.FlatSequence}
theorem exists_toAdmissibleSpan_eq (hV : ConfigSpace.SpanOfAdmissible.Statement)
    (x : ConfigSpace.admissibleSpan) : ∃ Φ, x = ConfigSpace.toAdmissibleSpan Φ := by
  obtain ⟨Φ, h⟩ := (hV x.1).1 x.2
  exact ⟨Φ, Subtype.ext h⟩
theorem isLinComb_of_toAdmissibleSpan_eq {a b : ℂ} {Φ Φ' Φ'' : ConfigSpace.AdmissibleSeq}
    (h : ConfigSpace.toAdmissibleSpan Φ'' =
      a • ConfigSpace.toAdmissibleSpan Φ + b • ConfigSpace.toAdmissibleSpan Φ') :
    ConfigSpace.IsLinComb a b Φ.1 Φ'.1 Φ''.1 := fun k => by
  have h1 := congrArg (fun x : ConfigSpace.admissibleSpan => x.1 k) h
  rw [← ConfigSpace.smul_add_smul_eq_linCombAt]
  exact h1
theorem spanForm_isPosSemidefHermitian (hV : ConfigSpace.SpanOfAdmissible.Statement)
    (hs : S.IsSesquilinear) (hp : S.IsPosSemidef) :
    FormCompletion.IsPosSemidefHermitianForm S.spanForm := by
  have hq : ∀ Φ Ψ : ConfigSpace.AdmissibleSeq,
      S.spanForm (ConfigSpace.toAdmissibleSpan Φ) (ConfigSpace.toAdmissibleSpan Ψ) =
        S.reflectionForm Φ Ψ := fun _ _ => rfl
  have hl : ∀ (a b : ℂ) (x x' y : ConfigSpace.admissibleSpan),
      S.spanForm (a • x + b • x') y = conj a * S.spanForm x y + conj b * S.spanForm x' y := by
    intro a b x x' y
    obtain ⟨Φ, rfl⟩ := exists_toAdmissibleSpan_eq hV x
    obtain ⟨Φ', rfl⟩ := exists_toAdmissibleSpan_eq hV x'
    obtain ⟨Ψ, rfl⟩ := exists_toAdmissibleSpan_eq hV y
    obtain ⟨Φ'', h⟩ := exists_toAdmissibleSpan_eq hV
      (a • ConfigSpace.toAdmissibleSpan Φ + b • ConfigSpace.toAdmissibleSpan Φ')
    rw [h, hq, hq, hq]
    exact hs.2.2.1 a b Φ Φ' Φ'' Ψ (isLinComb_of_toAdmissibleSpan_eq h.symm)
  have hr : ∀ (a b : ℂ) (x y y' : ConfigSpace.admissibleSpan),
      S.spanForm x (a • y + b • y') = a * S.spanForm x y + b * S.spanForm x y' := by
    intro a b x y y'
    obtain ⟨Φ, rfl⟩ := exists_toAdmissibleSpan_eq hV x
    obtain ⟨Ψ, rfl⟩ := exists_toAdmissibleSpan_eq hV y
    obtain ⟨Ψ', rfl⟩ := exists_toAdmissibleSpan_eq hV y'
    obtain ⟨Ψ'', h⟩ := exists_toAdmissibleSpan_eq hV
      (a • ConfigSpace.toAdmissibleSpan Ψ + b • ConfigSpace.toAdmissibleSpan Ψ')
    rw [h, hq, hq, hq]
    exact hs.2.2.2 a b Φ Ψ Ψ' Ψ'' (isLinComb_of_toAdmissibleSpan_eq h.symm)
  refine
    { add_left := fun u₁ u₂ v => ?_
      smul_left := fun z u v => ?_
      add_right := fun u v₁ v₂ => ?_
      smul_right := fun z u v => ?_
      hermitian := fun u v => ?_
      nonneg := fun u => ?_ }
  · simpa using hl 1 1 u₁ u₂ v
  · simpa using hl z 0 u u v
  · simpa using hr 1 1 u v₁ v₂
  · simpa using hr z 0 u v v
  · obtain ⟨Φ, rfl⟩ := exists_toAdmissibleSpan_eq hV u
    obtain ⟨Ψ, rfl⟩ := exists_toAdmissibleSpan_eq hV v
    exact hp.2.1 Φ Ψ
  · obtain ⟨Φ, rfl⟩ := exists_toAdmissibleSpan_eq hV u
    exact (hp.1 Φ).2
theorem inner_admClass (hC : FormCompletion.FormCompletionIsHilbertSpace)
    (hq : FormCompletion.IsPosSemidefHermitianForm S.spanForm) (Φ Ψ : ConfigSpace.AdmissibleSeq) :
    ⟪S.admClass Φ, S.admClass Ψ⟫_ℂ = S.reflectionForm Φ Ψ := by
  obtain ⟨-, ⟨-, -, -, -, -, -, hi, -⟩, -⟩ := hC _ _ hq
  exact hi _ _
end SpanForm
theorem reconstructionIsometryExists (hScal : MinkowskiSpace.SmoothSeqState_inner)
    (hTime : MinkowskiSpace.SmoothSeqStateTimeShift)
    (hUnit : GramUnitary.Claim)
    (hTotal : MinkowskiSpace.SmoothSeqStatesTotal)
    (hLie : MinkowskiSpace.SmoothSeqStateMemTensorHilbert)
    (hSemi : ConfigSpace.TimeShiftSemigroupStatement)
    (hInv : ConfigSpace.MotionInvarianceStatement)
    (hK : ConfigSpace.SesquilinearPosSemidefStatement)
    (hV : ConfigSpace.SpanOfAdmissible.Statement)
    (hC : FormCompletion.FormCompletionIsHilbertSpace) :
    MinkowskiSpace.ReconstructionIsometryExists := by
  intro S h0 h2 hE hR hP K _ _ _ E Ω A ℘ C hF hRep
  have hseq : ConfigSpace.IsCLMSequence S := ⟨h0.1, h2⟩
  have hs := hK S hseq
  have hq := spanForm_isPosSemidefHermitian hV hs.1 (hs.2 hR)
  have hG := hSemi S h0 h2 hR (hInv S hE hP).translation
  have hcl : ∀ Φ, FormReconstruction.IsSmoothPositiveTimeSeq Φ →
      S.admClass Φ ∈ S.positiveTimeSubspace := by
    intro Φ hΦ
    exact show S.admClass Φ ∈ (S.positiveTimeSubspace : Set S.HilbertCompletion) from by
      rw [hG.positiveTimeSubspace_eq_closure]
      exact ⟨fun _ => S.admClass Φ, fun _ => ⟨Φ, hΦ, rfl⟩, tendsto_const_nhds⟩
  let x : {Φ : ConfigSpace.AdmissibleSeq // FormReconstruction.IsSmoothPositiveTimeSeq Φ} →
      S.positiveTimeSubspace := fun i => ⟨S.admClass i.1, hcl i.1 i.2⟩
  let y : {Φ : ConfigSpace.AdmissibleSeq // FormReconstruction.IsSmoothPositiveTimeSeq Φ} →
      FieldFormHilbert.tensorHilbert E Ω A :=
    fun i => ⟨FormReconstruction.smoothSeqState E Ω A i.1, (hLie E Ω A ℘ C hF i.1 i.2).2⟩
  have hgram : ∀ i j, ⟪x i, x j⟫_ℂ = ⟪y i, y j⟫_ℂ := by
    intro i j
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact (inner_admClass hC hq i.1 j.1).trans
      (hScal S hP E Ω A ℘ C hF hRep i.1 j.1 i.2 j.2).symm
  have hdense : DenseRange x := by
    intro v
    have hv : (v : S.HilbertCompletion) ∈
        ComplexHilbert.seqClosureOf S.smoothPositiveTimeClasses := by
      rw [← hG.positiveTimeSubspace_eq_closure]
      exact v.2
    obtain ⟨u, hu, hlim⟩ := hv
    choose Φ hΦ hΦu using hu
    have hx : ∀ n, ((x ⟨Φ n, hΦ n⟩ : S.positiveTimeSubspace) : S.HilbertCompletion) = u n :=
      fun n => (hΦu n).symm
    refine mem_closure_of_tendsto (f := fun n => x ⟨Φ n, hΦ n⟩) (b := atTop) ?_
      (Eventually.of_forall fun n => ⟨_, rfl⟩)
    rw [tendsto_subtype_rng]
    simpa only [hx] using hlim
  have hdx : Dense (Submodule.span ℂ (Set.range x) : Set S.positiveTimeSubspace) :=
    Dense.mono Submodule.subset_span hdense
  have hdy : Dense (Submodule.span ℂ (Set.range y) :
      Set (FieldFormHilbert.tensorHilbert E Ω A)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro v hv
    have h1 : ∀ Φ : ConfigSpace.AdmissibleSeq, FormReconstruction.IsSmoothPositiveTimeSeq Φ →
        ⟪(v : K), FormReconstruction.smoothSeqState E Ω A Φ⟫_ℂ = 0 := by
      intro Φ hΦ
      have h3 := (Submodule.mem_orthogonal _ _).1 hv (y ⟨Φ, hΦ⟩)
        (Submodule.subset_span ⟨_, rfl⟩)
      rw [Submodule.coe_inner] at h3
      rw [← inner_conj_symm]
      exact (congrArg (starRingEnd ℂ) h3).trans (map_zero _)
    exact Subtype.ext (hTotal E Ω A ℘ C hF v.1 v.2 h1)
  obtain ⟨J, hJ⟩ := hUnit x y hgram hdx hdy
  refine ⟨J, ⟨?_, ?_, ?_⟩⟩
  · rintro v ⟨Φ, hΦ1, hΦc⟩
    have hz : ∀ k, FormReconstruction.succMember Φ k = 0 := fun k => congrFun hΦ1 (k + 1)
    have hsm : FormReconstruction.IsSmoothPositiveTimeSeq Φ := fun k => by
      rw [hz k]
      exact ⟨contDiff_const, HasCompactSupport.zero, by simp [tsupport]⟩
    have hv : v = x ⟨Φ, hsm⟩ := Subtype.ext hΦc
    have hnum : FormReconstruction.zerothScalar Φ = 1 := congrFun hΦ1 0
    have hw : ∀ k, ProjectionMeasures.weakInt (tsupport (FormReconstruction.succMember Φ k))
        (FormReconstruction.wickStateAt E Ω A k) (FormReconstruction.succMember Φ k) = 0 :=
      fun k => weakInt_eq_zero_of_eq_zero _ _ _ (hz k)
    rw [hv, hJ]
    show FormReconstruction.smoothSeqState E Ω A Φ = Ω
    simp only [FormReconstruction.smoothSeqState, hnum, hw, finsum_zero, one_smul, add_zero]
  · intro t ht v
    have hA := hG.shiftOp_spec t ht
    have hin : ∀ w : S.positiveTimeSubspace, S.timeShiftOp t w ∈ S.positiveTimeSubspace :=
      fun w => hG.mapsTo_positiveTimeSubspace ⟨t, ht⟩ w w.2
    refine ⟨hin v, ?_⟩
    let f : S.positiveTimeSubspace → K :=
      fun w => ((J ⟨_, hin w⟩ : FieldFormHilbert.tensorHilbert E Ω A) : K)
    let g : S.positiveTimeSubspace → K :=
      fun w => FieldForms.spectralTranslation E (FieldForms.imagTimeShift t)
        (J w : FieldFormHilbert.tensorHilbert E Ω A)
    have hf : Continuous f := continuous_subtype_val.comp (J.continuous.comp
      (Continuous.subtype_mk ((S.timeShiftOp t).continuous.comp continuous_subtype_val) _))
    have hg : Continuous g :=
      (FieldForms.spectralTranslation E (FieldForms.imagTimeShift t)).continuous.comp
        (continuous_subtype_val.comp J.continuous)
    have heq : f ∘ x = g ∘ x := by
      funext i
      obtain ⟨Φ', hm, hs', hsv⟩ := hTime E Ω A ℘ C hF i.1 i.2 t ht
      have hm' : ConfigSpace.timeShift t (ConfigSpace.seqValues i.1) ∈
          ConfigSpace.admissibleSpan := by
        rw [← hm]
        exact (ConfigSpace.toAdmissibleSpan Φ').2
      have e : S.timeShiftOp t (x i) = S.admClass Φ' := by
        refine (hA.apply_admClass i.1 hm').trans ?_
        exact congrArg S.spanClass (Subtype.ext hm.symm)
      have e2 : (⟨_, hin (x i)⟩ : S.positiveTimeSubspace) = x ⟨Φ', hs'⟩ := Subtype.ext e
      show ((J ⟨_, hin (x i)⟩ : FieldFormHilbert.tensorHilbert E Ω A) : K) =
        FieldForms.spectralTranslation E (FieldForms.imagTimeShift t)
          (J (x i) : FieldFormHilbert.tensorHilbert E Ω A)
      rw [e2, hJ, hJ]
      exact hsv
    exact congrFun (hdense.equalizer hf hg heq) v
  · intro Φ hΦ
    exact ⟨(hLie E Ω A ℘ C hF Φ hΦ).1, hcl Φ hΦ, congrArg Subtype.val (hJ ⟨Φ, hΦ⟩)⟩
end YangMills.Construction.MinkowskiSpace.IsometryConstruction
end

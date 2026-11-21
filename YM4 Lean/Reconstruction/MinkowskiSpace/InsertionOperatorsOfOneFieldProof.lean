import YangMills.Construction.ReflectionPositivity.PropertiesOfTheFormOfAFunctionalProof
import YangMills.Construction.ReflectionPositivity.TranslatesOfPositiveCombinationsAndTheirReflectedProductsProof
import Reconstruction.MinkowskiSpace.ClassesOfOneInsertedField
import Reconstruction.MinkowskiSpace.InsertionOperatorsOfOneField
import YangMills.Construction.ReflectionPositivity.FactsOnSeparatedTuplesOfFourSpace
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.InsertionOperators
open SeparatedTuples ReflectionPositivity.TupleForm ReflectionPositivity.FormProperties FieldFormConditions
  ProjectionMeasures HilbertToolkit OneLoopNotation ComplexHilbert FieldForms InsertedFieldForm
theorem spanIn_mono {O O' : Set (Fin 4 → ℝ)} (h : O ⊆ O') :
    spanIn O ≤ spanIn O' := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.spanIn_mono <;> assumption
theorem pushSpan_translate_mem (hPush : BasicFacts.PushSpanProperties) {v : Fin 4 → ℝ}
    (hv : 0 ≤ v TimeAxis.timeIdx) {G : FormalSpan}
    (hG : G ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan (translate v) G ∈ spanIn TimeAxis.upperHalfSpace := by apply _root_.YangMills.Construction.SeparatedTuples.PositiveTranslates.pushSpan_translate_mem_spanIn <;> assumption
theorem shiftedSpan_val (hPush : BasicFacts.PushSpanProperties) {v : Fin 4 → ℝ}
    (hv : 0 ≤ v TimeAxis.timeIdx) (F : PositiveSpan) :
    (shiftedSpan v F).1 = pushSpan (translate v) F.1 := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.coe_shiftedSpan <;> assumption
theorem supC1Norm_nonneg (f : (Fin 4 → ℝ) → ℂ) : 0 ≤ WightmanReconstruction.supC1Norm f :=
  add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _) (Real.iSup_nonneg fun _ => Real.sqrt_nonneg _)
theorem tsupport_finset_sum_smul_subset {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (f : ι → (Fin 4 → ℝ) → ℂ) :
    tsupport (∑ i ∈ s, c i • f i) ⊆ ⋃ i ∈ s, tsupport (f i) := by
  refine closure_minimal ?_ (isClosed_biUnion_finset fun i _ => isClosed_tsupport _)
  intro x hx
  by_contra hn
  refine (Function.mem_support.1 hx) ?_
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  have h0 : f i x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hn (Set.mem_biUnion hi h)
  simp [h0]
section Operators
variable (σ : TestSpaces.SepTuple → ℝ)
theorem pairing_isPosSemidefHermitian (hComp : CompletionPart) (hpos : PairingPosSemidef σ) :
    FormCompletion.IsPosSemidefHermitianForm (pairing σ) := by
  have hp : SesquilinearForms.IsPosSemidefForm (pairing σ) := hpos
  have hH := (hComp _ _ hp).1
  exact
    { add_left := hp.add_left
      smul_left := hp.smul_left
      add_right := hp.add_right
      smul_right := hp.smul_right
      hermitian := hH.conj_symm
      nonneg := fun F => (Complex.le_def.mp (hp.nonneg F)).1 }
theorem bddOp_ext_stateOf (hD : Dense (Set.range (stateOf σ)))
    {A B : BddOp (StateSpace σ)}
    (h : ∀ F, A (stateOf σ F) = B (stateOf σ F)) : A = B :=
  DFunLike.coe_injective (Continuous.ext_on hD A.continuous B.continuous (by
    rintro _ ⟨F, rfl⟩
    exact h F))
theorem exists_bddOp_of_bound (hC : FormCompletion.FormCompletionIsHilbertSpace)
    (hq : FormCompletion.IsPosSemidefHermitianForm (pairing σ))
    (hPush : BasicFacts.PushSpanProperties) {v : Fin 4 → ℝ} (hv : 0 ≤ v TimeAxis.timeIdx)
    (f : (Fin 4 → ℝ) → ℂ)
    (hmem : ∀ F : PositiveSpan,
      formalMul (WightmanReconstruction.complexTuple f) (shiftedSpan v F).1 ∈
        spanIn TimeAxis.upperHalfSpace)
    (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ F, ‖insertedState σ f v F‖ ≤ c * ‖stateOf σ F‖) :
    ∃ B : BddOp (StateSpace σ),
      (∀ F, B (stateOf σ F) = insertedState σ f v F) ∧ ‖B‖ ≤ c := by
  obtain ⟨hSharp, hHil, hMaps⟩ := hC PositiveSpan (pairing σ) hq
  obtain ⟨-, -, -, -, hadd, hsmul, hsemi, -⟩ := hSharp
  obtain ⟨-, -, -, -, hnorm, hmap, -, -, -⟩ := hHil
  let cl : PositiveSpan →ₗ[ℂ] StateSpace σ :=
    { toFun := stateOf σ
      map_add' := fun F F' => by
        apply FormCompletion.asMap_injective
        rw [FormCompletion.asMap_add]
        show FormCompletion.asMap (FormCompletion.classVec _ (F + F')) =
          FormCompletion.asMap (FormCompletion.classVec _ F) +
            FormCompletion.asMap (FormCompletion.classVec _ F')
        rw [hmap, hmap, hmap, hadd]
      map_smul' := fun z F => by
        apply FormCompletion.asMap_injective
        rw [RingHom.id_apply, FormCompletion.asMap_smul]
        show FormCompletion.asMap (FormCompletion.classVec _ (z • F)) =
          z • FormCompletion.asMap (FormCompletion.classVec _ F)
        rw [hmap, hmap, hsmul] }
  let P : PositiveSpan →ₗ[ℂ] PositiveSpan :=
    { toFun := fun F => ⟨_, hmem F⟩
      map_add' := fun F F' => Subtype.ext (by
        show formalMul _ (shiftedSpan v (F + F')).1 =
          formalMul _ (shiftedSpan v F).1 + formalMul _ (shiftedSpan v F').1
        rw [shiftedSpan_val hPush hv, shiftedSpan_val hPush hv, shiftedSpan_val hPush hv]
        simp only [Submodule.coe_add, map_add])
      map_smul' := fun z F => Subtype.ext (by
        show formalMul _ (shiftedSpan v (z • F)).1 =
          z • formalMul _ (shiftedSpan v F).1
        rw [shiftedSpan_val hPush hv, shiftedSpan_val hPush hv]
        simp only [Submodule.coe_smul, map_smul]) }
  have hR : ∀ F, (cl ∘ₗ P) F = insertedState σ f v F := fun F => by
    show stateOf σ ⟨_, hmem F⟩ = _
    rw [insertedState, dif_pos (hmem F)]
  have hclass : ∀ F, ‖stateOf σ F‖ =
      FormCompletion.seminormOfForm (pairing σ) F := fun F => by
    show ‖FormCompletion.classVec _ F‖ = _
    rw [hnorm, hmap, hsemi]
  obtain ⟨⟨B, hB, -⟩, hall⟩ := hMaps (StateSpace σ) c (cl ∘ₗ P) hc (fun F => by
    rw [hR, ← hclass]
    exact hb F)
  exact ⟨B, fun F => (hB F).trans (hR F), (hall B hB).1⟩
end Operators
theorem insertionOperatorBounds_holds (hHilbert : HilbertCompletionExtensionRiesz)
    (hCompletion : FormCompletion.FormCompletionIsHilbertSpace)
    (hFacts : BasicFacts.MainFacts)
    (hStates : InsertedStateProperties) : InsertionOperatorBounds := by
  intro σ E p C hcond η hη hη1
  obtain ⟨-, -, -, -, hPush, -⟩ := hFacts
  have hq := pairing_isPosSemidefHermitian σ hHilbert.1 hcond.posSemidef
  have hD : Dense (Set.range (stateOf σ)) :=
    (hCompletion PositiveSpan (pairing σ) hq).2.1.2.2.2.2.2.2.2.2
  have hst := hStates σ E p C hcond
  have htime : ((4 * η) • timeUnitVec) TimeAxis.timeIdx = 4 * η := by
    simp [timeUnitVec, PeriodicLattice.coordVec]
  have hv : 0 ≤ ((4 * η) • timeUnitVec) TimeAxis.timeIdx := by
    rw [htime]
    linarith
  have hbelow : ∀ {f : (Fin 4 → ℝ) → ℂ}, IsAdmissible η f →
      SupportedBelow ((4 * η) • timeUnitVec) f := fun {f} hf =>
    ⟨hf.mem, fun x hx => ⟨by linarith [(hf.tsupport_time x hx).1], by
      rw [htime]
      linarith [(hf.tsupport_time x hx).2]⟩⟩
  have hop : ∀ f : (Fin 4 → ℝ) → ℂ, IsAdmissible η f →
      IsInsertionOp σ η f (insertionOp σ η f) ∧
        opNormOf (insertionOp σ η f) ≤
          C * η ^ (-p) * WightmanReconstruction.supC1Norm f := by
    intro f hf
    have hmem := fun F => hst.1 _ f F (hbelow hf)
    have hc : 0 ≤ C * η ^ (-p) * WightmanReconstruction.supC1Norm f :=
      mul_nonneg (mul_nonneg (by linarith [hcond.one_le_const]) (Real.rpow_nonneg hη.le _))
        (supC1Norm_nonneg f)
    obtain ⟨B, hB, hBn⟩ := exists_bddOp_of_bound σ hCompletion hq hPush hv f hmem _ hc (fun F => by
      rw [insertedState, dif_pos (hmem F)]
      exact hcond.insertion_bound η hη hη1 f hf.mem hf.tsupport_time hf.diam_le F (hmem F))
    have hspec : IsInsertionOp σ η f (insertionOp σ η f) :=
      Classical.epsilon_spec (p := IsInsertionOp σ η f) ⟨B, hB⟩
    have heq : insertionOp σ η f = B :=
      bddOp_ext_stateOf σ hD fun F => (hspec F).trans (hB F).symm
    exact ⟨hspec, by rw [heq]; exact hBn⟩
  refine ⟨hop, ?_, ?_⟩
  · intro ι s c f D hadm hsupp hdiam
    have hsub : tsupport (∑ i ∈ s, c i • f i) ⊆ ⋃ i ∈ s, tsupport (f i) :=
      tsupport_finset_sum_smul_subset s c f
    have hD' : tsupport (∑ i ∈ s, c i • f i) ⊆ D := hsub.trans (Set.iUnion₂_subset hsupp)
    have hsum : IsAdmissible η (∑ i ∈ s, c i • f i) :=
      { mem := ⟨by
            have hfun : (∑ i ∈ s, c i • f i) = fun x => ∑ i ∈ s, c i • f i x := by
              funext x
              rw [Finset.sum_apply]
              rfl
            rw [hfun]
            exact ContDiff.sum fun i hi => (hadm i hi).mem.1.const_smul (c i),
          IsCompact.of_isClosed_subset (s.isCompact_biUnion fun i hi => (hadm i hi).mem.2.1)
            (isClosed_tsupport _) hsub, Set.subset_univ _⟩
        tsupport_time := fun x hx => by
          obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (hsub hx)
          exact (hadm i hi).tsupport_time x hxi
        diam_le := fun x hx y hy => hdiam x (hD' hx) y (hD' hy) }
    refine bddOp_ext_stateOf σ hD fun F => ?_
    rw [(hop _ hsum).1 F, hst.2.1 s c f _ F fun i hi => hbelow (hadm i hi),
      sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [smul_apply, (hop _ (hadm i hi)).1 F]
  · intro f a hf ha hsf
    refine bddOp_ext_stateOf σ hD fun F => ?_
    show insertionOp σ η (translateFun a f)
        (spectralTranslation E (realWickPoint a) (stateOf σ F)) =
      spectralTranslation E (realWickPoint a) (insertionOp σ η f (stateOf σ F))
    have hT : spectralTranslation E (realWickPoint a) (stateOf σ F) =
        stateOf σ (shiftedSpan a F) :=
      hcond.translationMeasure.translate_stateOf F a ha
    rw [hT, (hop _ hsf).1, (hop _ hf).1, hst.2.2.1 a _ f F ha (hbelow hf), add_comm,
      hst.2.2.2 _ a _ F ha (hbelow hsf)]
end YangMills.Construction.InsertionOperators
end

import Reconstruction.Continuum.CompositionTranslationsAndTensors
import YangMills.Construction.HilbertSpaces.CompletionsAdjointsAndWeakIntegralsAreWellDefined
import Reconstruction.MinkowskiSpace.ProductsOfABoundedFieldForm
import Reconstruction.MinkowskiSpace.TimeTranslationOfTheVectorsOfSmoothSequences
import Reconstruction.MinkowskiSpace.TranslationOperatorsOfABoundedFieldForm
import Reconstruction.MinkowskiSpace.VectorsOfSmoothSequencesLieInTheClosedSubspace
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.MinkowskiSpace.WickTimeShift
open FieldForms ConfigSpace ProjectionMeasures OneLoopNotation FormReconstruction
def diagTimeShift (n : ℕ) (s : ℝ) : TestSpaces.PointTuple n :=
  fun _ => s • SchwartzAxioms.timeUnitVector
theorem timeCoord_add_diagTimeShift {n : ℕ} (s : ℝ) (y : TestSpaces.PointTuple n) (j : Fin n) :
    TestSpaces.timeCoord (y + diagTimeShift n s) j = TestSpaces.timeCoord y j + s := by
  simp [TestSpaces.timeCoord, diagTimeShift, SchwartzAxioms.timeUnitVector, TimeAxis.timeIdx]
theorem add_diagTimeShift_mem {n : ℕ} {s : ℝ} (hs : 0 ≤ s) {y : TestSpaces.PointTuple n}
    (hy : y ∈ TestSpaces.increasingPositiveTimes n) :
    y + diagTimeShift n s ∈ TestSpaces.increasingPositiveTimes n := by
  refine ⟨fun a b hab => ?_, fun h => ?_⟩
  · rw [timeCoord_add_diagTimeShift, timeCoord_add_diagTimeShift]
    have := hy.1 hab
    linarith
  · rw [timeCoord_add_diagTimeShift]
    have := hy.2 h
    linarith
theorem shiftAct_timeUnit_eq_comp {n : ℕ} (s : ℝ) (f : TestSpaces.PointTuple n → ℂ) :
    ConfigSpace.shiftAct (s • SchwartzAxioms.timeUnitVector) f =
      f ∘ Homeomorph.subRight (diagTimeShift n s) := by
  funext y
  rw [ConfigSpace.shiftAct_apply]
  rfl
theorem tsupport_shiftAct_timeUnit {n : ℕ} (s : ℝ) (f : TestSpaces.PointTuple n → ℂ) :
    tsupport (ConfigSpace.shiftAct (s • SchwartzAxioms.timeUnitVector) f) =
      Homeomorph.subRight (diagTimeShift n s) ⁻¹' tsupport f := by
  rw [shiftAct_timeUnit_eq_comp, tsupport_comp_eq_preimage]
theorem imPart_imagTimeShift_mem {s : ℝ} (hs : 0 ≤ s) :
    MinkowskiSpace.imPart (imagTimeShift s) ∈ closedFutureCone := by
  have him : MinkowskiSpace.imPart (imagTimeShift s) = mkTimeSpace s 0 := by
    funext μ
    fin_cases μ <;>
      simp [MinkowskiSpace.imPart, imagTimeShift, toComplex, timeUnit, mkTimeSpace, Fin.cons]
    all_goals (change s * (0 : ℝ) = 0; simp)
  change coneGap _ ≥ 0
  rw [him]
  simpa [coneGap, spacePart, mkTimeSpace, spaceNorm] using hs
theorem wickMapTuple_mem_diffCoordsInTube {q : ℕ} {y : TestSpaces.PointTuple (q + 1)}
    (hy : y ∈ TestSpaces.increasingPositiveTimes (q + 1)) :
    wickMapTuple (tupleToComplex y) ∈ diffCoordsInTube (q + 1) := by
  intro k _
  refine Fin.cases ?_ (fun j => ?_) k
  · have hpos : 0 < y 0 3 := hy.2 (Nat.succ_pos q)
    have him : MinkowskiSpace.imPart (wickMap (tupleToComplex y 0)) =
        mkTimeSpace (y 0 3) 0 := by
      funext μ
      fin_cases μ <;>
        simp [MinkowskiSpace.imPart, tupleToComplex, wickMap, toComplex,
          mkTimeSpace, Fin.cons]
      all_goals rfl
    change coneGap (MinkowskiSpace.imPart (wickMap (tupleToComplex y 0))) > 0
    rw [him]
    simpa [coneGap, spacePart, mkTimeSpace, spaceNorm] using hpos
  · exact wickDiffs_mem_futureTube hy.1 j
theorem wickMapTuple_add_diagTimeShift {n : ℕ} (s : ℝ) (y : TestSpaces.PointTuple n) :
    wickMapTuple (tupleToComplex (y + diagTimeShift n s)) =
      fun k => wickMapTuple (tupleToComplex y) k + imagTimeShift s := by
  funext k μ
  fin_cases μ <;>
    simp [wickMapTuple, wickMap, tupleToComplex, toComplex, diagTimeShift,
      imagTimeShift, SchwartzAxioms.timeUnitVector, TimeAxis.timeIdx, timeUnit, mkTimeSpace,
      Fin.cons, mul_add]
  all_goals (right; rfl)
section FieldForm
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : FourBorelSet → BddOp H) (vac : H) (B : ℝ → BddOp H)
theorem spectralTranslation_wickStateAt (hI : StatesTranslateInner P vac B) {s : ℝ}
    (hs : 0 ≤ s) (q : ℕ) {y : TestSpaces.PointTuple (q + 1)}
    (hy : y ∈ TestSpaces.increasingPositiveTimes (q + 1)) :
    FieldForms.spectralTranslation P (imagTimeShift s)
        (wickStateAt P vac B q y) =
      wickStateAt P vac B q (y + diagTimeShift (q + 1) s) := by
  have h := (hI (q + 1) 0 _ Fin.elim0 (imagTimeShift s) (wickMapTuple_mem_diffCoordsInTube hy)
    (fun j => j.elim0) (imPart_imagTimeShift_mem hs)).1
  unfold wickStateAt
  rw [wickMapTuple_add_diagTimeShift]
  exact h
theorem hasWeakIntegral_shiftAct (hI : StatesTranslateInner P vac B) {s : ℝ} (hs : 0 ≤ s)
    (q : ℕ) {f : TestSpaces.PointTuple (q + 1) → ℂ}
    (hf : tsupport f ⊆ TestSpaces.increasingPositiveTimes (q + 1)) {w : H}
    (hw : HasWeakIntegral (tsupport f) (wickStateAt P vac B q) f w) :
    HasWeakIntegral (tsupport (ConfigSpace.shiftAct (s • SchwartzAxioms.timeUnitVector) f))
      (wickStateAt P vac B q)
      (ConfigSpace.shiftAct (s • SchwartzAxioms.timeUnitVector) f)
      (FieldForms.spectralTranslation P (imagTimeShift s) w) := by
  intro ψ
  set U := FieldForms.spectralTranslation P (imagTimeShift s) with hUdef
  set D := diagTimeShift (q + 1) s with hD
  set Ψ := wickStateAt P vac B q with hΨ
  have hleft : ⟪ψ, U w⟫_ℂ = ∫ y in tsupport f, f y * ⟪ψ, Ψ (y + D)⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hw]
    refine setIntegral_congr_fun (isClosed_tsupport f).measurableSet fun y hy => ?_
    show f y * _ = f y * _
    rw [ContinuousLinearMap.adjoint_inner_left, hUdef, hΨ,
      spectralTranslation_wickStateAt P vac B hI hs q (hf hy)]
  rw [hleft, tsupport_shiftAct_timeUnit]
  have hmp : MeasurePreserving (fun z : TestSpaces.PointTuple (q + 1) => z + (-D)) volume volume :=
    measurePreserving_add_right volume (-D)
  have hemb : MeasurableEmbedding (fun z : TestSpaces.PointTuple (q + 1) => z + (-D)) :=
    (Homeomorph.addRight (-D)).measurableEmbedding
  have hpre : (Homeomorph.subRight D : TestSpaces.PointTuple (q + 1) ≃ₜ _) ⁻¹' tsupport f =
      (fun z : TestSpaces.PointTuple (q + 1) => z + (-D)) ⁻¹' tsupport f := by
    ext z
    simp [sub_eq_add_neg]
  rw [hpre, ← hmp.setIntegral_preimage_emb hemb]
  refine setIntegral_congr_fun (hemb.measurable
    (isClosed_tsupport f).measurableSet) fun z _ => ?_
  simp only [shiftAct_timeUnit_eq_comp]
  show f (z + -D) * ⟪ψ, Ψ (z + -D + D)⟫_ℂ = f (z - D) * ⟪ψ, Ψ z⟫_ℂ
  rw [neg_add_cancel_right, sub_eq_add_neg]
end FieldForm
theorem shiftActAt_zeroOfDegree (v : Fin 4 → ℝ) (q : ℕ) :
    shiftActAt v (zeroOfDegree q) = zeroOfDegree q := by apply _root_.YangMills.Construction.ConditionDomains.shiftActAt_zeroOfDegree <;> assumption
theorem shiftActAt_mem_flatOffPosTimeAt (hT : MotionComposition.CompositionTranslationStatement)
    {s : ℝ} (hs : 0 ≤ s) {n : ℕ} {g : FnOrScalar n} (hg : g ∈ flatOffPosTimeAt n) :
    shiftActAt (s • SchwartzAxioms.timeUnitVector) g ∈ flatOffPosTimeAt n := by
  cases n with
  | zero => exact Set.mem_univ _
  | succ r =>
    have h := (hT.2.1 (r + 1) (Nat.succ_pos r)).1.1 s hs
    have key : ∀ f : TestSpaces.PointTuple (r + 1) → ℂ, f ∈ schwartzFlatOffPosTime (r + 1) →
        ConfigSpace.shiftAct (s • SchwartzAxioms.timeUnitVector) f ∈
          schwartzFlatOffPosTime (r + 1) := by
      intro f hf
      rw [← SchwartzAxioms.positiveTimeSchwartz_eq] at hf ⊢
      rw [← SmoothSeparatedTuples.translateFun_eq_shiftAct]
      exact h hf
    exact key g hg
def shiftedSeq (hT : MotionComposition.CompositionTranslationStatement) {s : ℝ} (hs : 0 ≤ s)
    (F : AdmissibleSeq) : AdmissibleSeq :=
  ⟨fun q => ⟨shiftActAt (s • SchwartzAxioms.timeUnitVector) (F.1 q).1,
    shiftActAt_mem_flatOffPosTimeAt hT hs (F.1 q).2⟩, by
    refine Set.Finite.subset F.2 fun q hq h0 => hq ?_
    show shiftActAt _ (F.1 q).1 = zeroOfDegree q
    rw [h0, shiftActAt_zeroOfDegree]⟩
theorem succMember_shiftedSeq (hT : MotionComposition.CompositionTranslationStatement) {s : ℝ}
    (hs : 0 ≤ s) (F : AdmissibleSeq) (q : ℕ) :
    succMember (shiftedSeq hT hs F) q =
      ConfigSpace.shiftAct (s • SchwartzAxioms.timeUnitVector) (succMember F q) :=
  rfl
theorem isSmoothPositiveTimeSeq_shiftedSeq (hT : MotionComposition.CompositionTranslationStatement)
    {s : ℝ} (hs : 0 ≤ s) {F : AdmissibleSeq} (hF : IsSmoothPositiveTimeSeq F) :
    IsSmoothPositiveTimeSeq (shiftedSeq hT hs F) := by
  intro q
  obtain ⟨hC, hcpt, hsub⟩ := hF q
  rw [succMember_shiftedSeq]
  refine ⟨?_, ?_, ?_⟩
  · rw [shiftAct_timeUnit_eq_comp]
    exact hC.comp (contDiff_id.sub contDiff_const)
  · show IsCompact (tsupport _)
    rw [tsupport_shiftAct_timeUnit]
    exact (Homeomorph.subRight (diagTimeShift (q + 1) s)).isCompact_preimage.mpr hcpt
  · rw [tsupport_shiftAct_timeUnit]
    intro z hz
    have h := add_diagTimeShift_mem hs (hsub hz)
    simpa using h
theorem smoothSeqStateTimeShift_holds (hT : MotionComposition.CompositionTranslationStatement)
    (hW : HilbertWellDefined.WellDefinedStatement)
    (hP : FieldForms.FieldProductProperties)
    (hO : FieldFormTranslations.TranslationOperatorFacts)
    (hS : MinkowskiSpace.SmoothSeqStateMemTensorHilbert) :
    MinkowskiSpace.SmoothSeqStateTimeShift := by
  intro H _ _ _ P vac B ρ C hform F hF s hs
  have hI : StatesTranslateInner P vac B :=
    (hP H P vac B ρ C hform).2.2.2.2.2.2.2.2.2.1
  have hvac : FieldForms.spectralTranslation P (imagTimeShift s) vac = vac :=
    ((hO H P vac B ρ C hform).1.1 _ _ (imPart_imagTimeShift_mem hs)
      (imPart_imagTimeShift_mem hs)).2.2.2.2
  refine ⟨shiftedSeq hT hs F, rfl, isSmoothPositiveTimeSeq_shiftedSeq hT hs hF, ?_⟩
  have hint := (hS P vac B ρ C hform F hF).1
  have hweak : ∀ q, HasWeakIntegral (tsupport (succMember F q))
      (wickStateAt P vac B q) (succMember F q)
      (weakInt (tsupport (succMember F q)) (wickStateAt P vac B q)
        (succMember F q)) :=
    fun q => (hW.2.2.2 H (TestSpaces.PointTuple (q + 1)) _ _ _ (hint q)).1
  have hfin : (Function.support fun q => weakInt (tsupport (succMember F q))
      (wickStateAt P vac B q) (succMember F q)).Finite := by
    refine Set.Finite.subset (F.2.preimage Nat.succ_injective.injOn) fun q hq h0 => hq ?_
    have hzero : ∀ y, succMember F q y = 0 := fun y => congrFun h0 y
    have h1 := hweak q (weakInt (tsupport (succMember F q))
      (wickStateAt P vac B q) (succMember F q))
    simp only [hzero, zero_mul, integral_zero] at h1
    exact inner_self_eq_zero.mp h1
  unfold smoothSeqState
  rw [map_add, map_smul, hvac]
  congr 1
  have hmap := (FieldForms.spectralTranslation P
    (imagTimeShift s)).toLinearMap.toAddMonoidHom.map_finsum hfin
  refine Eq.trans (finsum_congr fun q => ?_) hmap.symm
  have hsub : tsupport (succMember F q) ⊆ TestSpaces.increasingPositiveTimes (q + 1) :=
    (hF q).2.2
  have hw := hasWeakIntegral_shiftAct P vac B hI hs q hsub (hweak q)
  rw [succMember_shiftedSeq]
  have hspec := Classical.epsilon_spec (p := HasWeakIntegral _ _ _) ⟨_, hw⟩
  refine ext_inner_left ℂ fun ψ => ?_
  exact (hspec ψ).trans (hw ψ).symm
end YangMills.Construction.MinkowskiSpace.WickTimeShift
end

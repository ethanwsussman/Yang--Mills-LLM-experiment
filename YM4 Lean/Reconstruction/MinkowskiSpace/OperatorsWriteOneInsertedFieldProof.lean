import Reconstruction.MinkowskiSpace.ClassesOfOneInsertedField
import Reconstruction.MinkowskiSpace.OperatorsAtTheMiddleOfTheDensity
import Reconstruction.MinkowskiSpace.OperatorsWriteOneInsertedField
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.MidpointInsertion
open SeparatedTuples ReflectionPositivity.TupleForm ReflectionPositivity.FormProperties
  FieldFormConditions ProjectionMeasures HilbertToolkit OneLoopNotation ComplexHilbert
  MinkowskiSpace FieldForms InsertedFieldForm
theorem exists_norm_le_of_continuousOn_inner {H P : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace P] {K : Set P} (hK : IsCompact K)
    (Ξ : P → H) (hc : ∀ χ : H, ContinuousOn (fun x => ⟪χ, Ξ x⟫_ℂ) K) :
    ∃ b : ℝ, ∀ x ∈ K, ‖Ξ x‖ ≤ b := by
  have hp : ∀ χ : H, ∃ C : ℝ, ∀ i : K, ‖innerSL ℂ (Ξ i) χ‖ ≤ C := by
    intro χ
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc χ)
    refine ⟨C, fun i => ?_⟩
    rw [innerSL_apply_apply, ← inner_conj_symm, RCLike.norm_conj]
    exact hC i i.2
  obtain ⟨C, hC⟩ := banach_steinhaus hp
  refine ⟨C, fun x hx => ?_⟩
  have := hC ⟨x, hx⟩
  rwa [innerSL_apply_norm] at this
theorem midpointHasInsertionIntegral_holds (hMid : MidpointOperators.MidpointOperatorFacts)
    (hStates : InsertedStateProperties) : MidpointHasInsertionIntegral := by
  intro σ E p C hcond G hG c s hc hs hsc h hh hsupp F
  have htime : (c • timeUnitVec) TimeAxis.timeIdx = c := by
    simp [timeUnitVec, PeriodicLattice.coordVec]
  have hbelow : SupportedBelow (c • timeUnitVec) h :=
    ⟨hh, fun x hx => ⟨hs.trans (hsupp x hx).1, by
      rw [htime]; linarith [(hsupp x hx).2]⟩⟩
  have hm := (hStates σ E p C hcond).1 _ h F hbelow
  refine ⟨hm, ?_⟩
  set v := stateOf σ F with hv
  have hslab : tsupport h ⊆ timeSlab c := fun y hy =>
    ⟨hs.trans (hsupp y hy).1, by linarith [(hsupp y hy).2]⟩
  have hdens : ∀ y ∈ tsupport h,
      insertionDensity σ E (midpointField σ G) c s v y = G c y v := by
    intro y hy
    have hG' := (hMid σ E p C hcond G hG).2.2 c s y hs (hsupp y hy).1.le
      (by linarith [(hsupp y hy).2])
    rw [hG']
    rfl
  have hcompact : IsCompact (tsupport h) := hh.2.1
  have hcont : ∀ χ : StateSpace σ, ContinuousOn
      (fun y => ⟪χ, insertionDensity σ E (midpointField σ G) c s v y⟫_ℂ) (tsupport h) := by
    intro χ
    refine ((hG.continuousOn_inner c χ v hc).mono hslab).congr fun y hy => ?_
    simp only [hdens y hy]
  have hweak : HasWeakIntegrandData (tsupport h)
      (insertionDensity σ E (midpointField σ G) c s v) h :=
    { measurableSet := (isClosed_tsupport h).measurableSet
      norm_bdd := exists_norm_le_of_continuousOn_inner hcompact _ hcont
      continuousOn_inner := hcont
      integrableOn := (hh.1.continuous.integrable_of_hasCompactSupport hh.2.1).integrableOn }
  refine ⟨hweak, ?_⟩
  have hstate : HasWeakIntegral (tsupport h)
      (insertionDensity σ E (midpointField σ G) c s v) h (stateOf σ ⟨_, hm⟩) := by
    intro χ
    have hint := hG.inner_insertedState c h F χ hc hh hslab
    rw [insertedState, dif_pos hm] at hint
    rw [hint]
    refine MeasureTheory.setIntegral_congr_fun (isClosed_tsupport h).measurableSet fun y hy => ?_
    show h y * ⟪χ, G c y v⟫_ℂ = h y * ⟪χ, insertionDensity σ E (midpointField σ G) c s v y⟫_ℂ
    rw [hdens y hy]
  have hspec : HasWeakIntegral (tsupport h)
      (insertionDensity σ E (midpointField σ G) c s v) h
      (weakInt (tsupport h) (insertionDensity σ E (midpointField σ G) c s v) h) :=
    Classical.epsilon_spec (p := HasWeakIntegral (tsupport h)
      (insertionDensity σ E (midpointField σ G) c s v) h) ⟨_, hstate⟩
  exact ext_inner_left ℂ fun χ => (hstate χ).trans (hspec χ).symm
end YangMills.Construction.MidpointInsertion
end

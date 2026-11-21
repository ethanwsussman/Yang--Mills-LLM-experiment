import Reconstruction.MinkowskiSpace.SeparabilityAndFixedVectorsOfTheTensorVectorsProof
import Reconstruction.MinkowskiSpace.VectorsAtRealPointsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.MinkowskiSpace
open YangMills.Construction.FieldForms YangMills.Construction.ConfigSpace YangMills.Construction.RealPointVectors YangMills.Construction.WightmanTheory YangMills.Construction.FieldFormHilbert YangMills.Construction.ProjectionMeasures YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert YangMills.Construction.FormReconstruction
theorem continuous_wickMapTuple_toComplex (m : ℕ) :
    Continuous fun x : TestSpaces.PointTuple m => wickMapTuple (tupleToComplex x) := by apply _root_.YangMills.Construction.TensorHilbertSeparable.continuous_wickMapTuple_tupleToComplex <;> assumption
theorem wickMapTuple_mem_diffCoordsInTube {q : ℕ} {x : TestSpaces.PointTuple (q + 1)}
    (hx : x ∈ TestSpaces.increasingPositiveTimes (q + 1)) :
    wickMapTuple (tupleToComplex x) ∈ diffCoordsInTube (q + 1) := by apply _root_.YangMills.Construction.MinkowskiSpace.WickTimeShift.wickMapTuple_mem_diffCoordsInTube <;> assumption
theorem smoothSeqStateMemTensorHilbert_holds (hW : HilbertWellDefined.WellDefinedStatement)
    (hP : FieldForms.FieldProductProperties)
    (hR : RealPointVectors.BoundaryVectorsStatement) : SmoothSeqStateMemTensorHilbert := by
  intro K _ _ _ E Ω A ℘ C hform Φ hΦ
  have hcont : ∀ q : ℕ, ContinuousOn (wickStateAt E Ω A q)
      (tsupport (succMember Φ q)) := fun q =>
    (((hP K E Ω A ℘ C hform).2.2.2.2.2.2.2.1 q).2.2.2.2).comp
      (continuous_wickMapTuple_toComplex (q + 1)).continuousOn
      fun _ hx => wickMapTuple_mem_diffCoordsInTube ((hΦ q).2.2 hx)
  have hint : ∀ q : ℕ, HasWeakIntegrandData (tsupport (succMember Φ q))
      (wickStateAt E Ω A q) (succMember Φ q) := by
    intro q
    obtain ⟨hC, hcpt, -⟩ := hΦ q
    have hc : IsCompact (tsupport (succMember Φ q)) := hcpt
    refine ⟨(isClosed_tsupport _).measurableSet, ?_, fun χ => ?_, ?_⟩
    · obtain ⟨b, hb⟩ := hc.exists_bound_of_continuousOn (hcont q)
      exact ⟨b, hb⟩
    · exact (innerSL ℂ χ).continuous.comp_continuousOn (hcont q)
    · exact hC.continuous.continuousOn.integrableOn_compact hc
  have hmem : ∀ (m : ℕ) (x : TestSpaces.PointTuple m), x ∈ TestSpaces.increasingPositiveTimes m →
      stateVector E Ω A m (wickMapTuple (tupleToComplex x)) ∈ tensorHilbert E Ω A := by
    intro m x hx
    rw [← SetLike.mem_coe, coe_tensorHilbert, (hR E Ω A ℘ C hform).tensorDomainClosure_eq]
    unfold SesquilinearForms.closedLinSpan
    rw [seqClosureOf_eq_closure]
    exact subset_closure (Submodule.subset_span ⟨m, x, hx, rfl⟩)
  have hvac : Ω ∈ tensorHilbert E Ω A :=
    hmem 0 (fun i => i.elim0) ⟨fun a => a.elim0, fun h => absurd h (lt_irrefl 0)⟩
  have hvec : ∀ q : ℕ, weakInt (tsupport (succMember Φ q))
      (wickStateAt E Ω A q) (succMember Φ q) ∈ tensorHilbert E Ω A := by
    intro q
    rw [← Submodule.orthogonal_orthogonal (tensorHilbert E Ω A),
      Submodule.mem_orthogonal]
    intro w hw
    rw [(hW.2.2.2 K (TestSpaces.PointTuple (q + 1)) _ _ _ (hint q)).1 w,
      setIntegral_congr_fun (g := fun _ => (0 : ℂ)) (isClosed_tsupport _).measurableSet
        fun x hx => ?_]
    · simp
    · show succMember Φ q x * ⟪w, wickStateAt E Ω A q x⟫_ℂ = 0
      have h0 : ⟪w, wickStateAt E Ω A q x⟫_ℂ = 0 :=
        Submodule.inner_left_of_mem_orthogonal (hmem (q + 1) x ((hΦ q).2.2 hx)) hw
      rw [h0, mul_zero]
  refine ⟨hint, ?_⟩
  unfold smoothSeqState
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hvac)
    (finsum_induction (· ∈ tensorHilbert E Ω A) (Submodule.zero_mem _)
      (fun _ _ => Submodule.add_mem _) hvec)
end YangMills.Construction.MinkowskiSpace
end

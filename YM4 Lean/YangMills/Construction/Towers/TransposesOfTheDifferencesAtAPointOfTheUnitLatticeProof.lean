import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import YangMills.Construction.Towers.TransposesOfDifferencesAtScalarFunctions
import YangMills.Construction.Towers.TransposesOfTheCovariantDifferenceAndOfTheDifferences
import YangMills.Construction.Towers.TransposesOfTheDifferencesAtAPointOfTheUnitLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.UnitLatticeAdjoints
open InfiniteLattice (Link axisStep)
open Matrices (ComplexMatrix2)
open PairedFunctionSpace (linearOfValues transposeMap)
open CovDiffTransposes (HasTransposeKernel)
open FullSpace (forwardEdge)
def halfTraceWith (Y : ComplexMatrix2) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun X := ComplexMatrix2.halfTrace (X * Y)
  map_add' A B := by
    simp [ComplexMatrix2.halfTrace, add_mul, Matrix.trace_add, mul_add]
  map_smul' z A := by
    simp [ComplexMatrix2.halfTrace, Matrix.trace_smul]
    ring
theorem halfTraceWith_apply (Y X : ComplexMatrix2) :
    halfTraceWith Y X = ComplexMatrix2.halfTrace (X * Y) := rfl
theorem eq_of_halfTraceWith_eq {X X' : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hX' : X' ∈ ComplexMatrix2.traceless)
    (h : ∀ Y ∈ ComplexMatrix2.traceless, halfTraceWith Y X = halfTraceWith Y X') : X = X' := by
  have t : X 0 0 + X 1 1 = 0 := by
    have : Matrix.trace X = 0 := hX
    simpa [Matrix.trace_fin_two] using this
  have t' : X' 0 0 + X' 1 1 = 0 := by
    have : Matrix.trace X' = 0 := hX'
    simpa [Matrix.trace_fin_two] using this
  have m₁ : (!![0, 1; 0, 0] : ComplexMatrix2) ∈ ComplexMatrix2.traceless := by
    show Matrix.trace _ = 0
    simp [Matrix.trace_fin_two]
  have m₂ : (!![0, 0; 1, 0] : ComplexMatrix2) ∈ ComplexMatrix2.traceless := by
    show Matrix.trace _ = 0
    simp [Matrix.trace_fin_two]
  have m₃ : (!![1, 0; 0, -1] : ComplexMatrix2) ∈ ComplexMatrix2.traceless := by
    show Matrix.trace _ = 0
    simp [Matrix.trace_fin_two]
  have h₁ := h _ m₁
  have h₂ := h _ m₂
  have h₃ := h _ m₃
  simp only [halfTraceWith_apply, ComplexMatrix2.halfTrace, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two] at h₁ h₂ h₃
  simp at h₁ h₂ h₃
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (h₃ + t - t') / 2
  · exact h₂
  · exact h₁
  · linear_combination (t - t' - h₃) / 2
section Multiples
variable {ι : Type}
theorem traceFinsumPairing_smul_right (g : ι → ComplexMatrix2) (w : ι → ℂ) (Y : ComplexMatrix2) :
    traceFinsumPairing g (fun i => w i • Y) = ∑ᶠ i, halfTraceWith Y (g i) * w i := by
  unfold traceFinsumPairing
  refine finsum_congr fun i => ?_
  rw [mul_smul_comm, ← smul_mul_assoc]
  show halfTraceWith Y (w i • g i) = _
  rw [map_smul, smul_eq_mul, mul_comm]
theorem finsum_mul_piSingle_one [DecidableEq ι] (h : ι → ℂ) (x : ι) :
    ∑ᶠ i, h i * (Pi.single x 1 : ι → ℂ) i = h x := by
  rw [finsum_eq_single _ x (fun y hy => by simp [Pi.single_eq_of_ne hy])]
  simp
theorem finite_support_piSingle_one [DecidableEq ι] (x : ι) :
    (Function.support (Pi.single x 1 : ι → ℂ)).Finite := by
  refine (Set.finite_singleton x).subset fun y hy => ?_
  by_contra hne
  exact (Function.mem_support.1 hy) (Pi.single_eq_of_ne hne _)
theorem hasFiniteSupp_smul_const {w : ι → ℂ} (hw : (Function.support w).Finite)
    (Y : ComplexMatrix2) : HasFiniteSupp fun i => w i • Y := by
  refine hw.subset fun i hi => ?_
  by_contra h
  simp only [Function.mem_support, not_not] at h
  exact (Function.mem_support.1 hi) (by simp [h])
end Multiples
variable {L : ℕ}
theorem exists_vertexCoboundaryAdjoint_spec
    (mw : HasTransposeKernel (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.edgePauliCoordinates L 0 0)
      FullSpace.vertexCoboundary)
    {b : FullSpace.Edge L 0 0 → ComplexMatrix2} (hb : b ∈ FullSpace.complexEdgeForms (meshAt L 0 0)) :
    ∃ t : FullSpace.Vertex L 0 0 → ComplexMatrix2, vertexCoboundaryAdjoint L b = t ∧
      (∀ x, t x ∈ ComplexMatrix2.traceless) ∧
      ∀ l ∈ Matrices.GroupLieProduct.tracelessFunctions (FullSpace.Vertex L 0 0), HasFiniteSupp l →
        traceFinsumPairing t l = FullSpace.finiteEdgePairing b (FullSpace.vertexCoboundary l) := by
  classical
  refine ⟨(transposeMap (linearOfValues (pairedFunctions (FullSpace.Vertex L 0 0))
    (FullSpace.edgePairedSpace (meshAt L 0 0)) (FullSpace.vertexCoboundary (a := meshAt L 0 0)))
    ⟨b, hb⟩).1, ?_, fun x => Subtype.prop (transposeMap (linearOfValues
      (pairedFunctions (FullSpace.Vertex L 0 0)) (FullSpace.edgePairedSpace (meshAt L 0 0))
      (FullSpace.vertexCoboundary (a := meshAt L 0 0))) ⟨b, hb⟩) x (Set.mem_univ x),
    fun l hl hfin => ?_⟩
  · unfold vertexCoboundaryAdjoint PairedFunctionSpace.transposeOfValues
    exact dif_pos hb
  · exact (mw.isTranspose ⟨b, hb⟩ ⟨l, hl⟩ hfin).trans
      (congrArg (FullSpace.finiteEdgePairing b) (mw.coe_linear ⟨l, hl⟩))
theorem vertexCoboundaryAdjoint_apply (hS : FullSpace.VertexAdjointProperties ℂ (meshAt L 0 0))
    (mw : HasTransposeKernel (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.edgePauliCoordinates L 0 0)
      FullSpace.vertexCoboundary)
    {b : FullSpace.Edge L 0 0 → ComplexMatrix2} (hb : b ∈ FullSpace.complexEdgeForms (meshAt L 0 0))
    (x : FullSpace.Vertex L 0 0) :
    vertexCoboundaryAdjoint L b x =
      ∑ μ : Fin 4,
        (b (Link.forwardFrom (x - axisStep (meshAt L 0 0) μ) μ) - b (Link.forwardFrom x μ)) := by
  classical
  have fwd : ∀ (y : FullSpace.Vertex L 0 0) (μ : Fin 4),
      b (Link.forwardFrom y μ) ∈ ComplexMatrix2.traceless :=
    fun y μ => hb.1 _ ⟨μ, by simp [Link.forwardFrom]⟩
  obtain ⟨t, ht, hmem, key⟩ := exists_vertexCoboundaryAdjoint_spec mw hb
  rw [ht]
  refine eq_of_halfTraceWith_eq (hmem x)
    (Submodule.sum_mem _ fun μ _ => Submodule.sub_mem _ (fwd _ μ) (fwd _ μ)) fun Y hY => ?_
  let v : FullSpace.Vertex L 0 0 → ℂ := Pi.single x 1
  have hv : (Function.support v).Finite := finite_support_piSingle_one x
  have hl : (fun y => v y • Y) ∈ Matrices.GroupLieProduct.tracelessFunctions (FullSpace.Vertex L 0 0) :=
    fun y _ => Submodule.smul_mem _ _ hY
  have hcancelled' := key _ hl (hasFiniteSupp_smul_const hv Y)
  let c : FullSpace.PositiveEdge (meshAt L 0 0) → ℂ := fun β => halfTraceWith Y (b β.1)
  have e₁ : traceFinsumPairing t (fun y => v y • Y) = halfTraceWith Y (t x) := by
    rw [traceFinsumPairing_smul_right]
    exact finsum_mul_piSingle_one (fun i => halfTraceWith Y (t i)) x
  have e₂ : FullSpace.finiteEdgePairing b (FullSpace.vertexCoboundary fun y => v y • Y) =
      ∑ᶠ β, c β * FullSpace.vertexDifference v β := by
    have e : FullSpace.restrictToPositiveEdges (FullSpace.vertexCoboundary fun y => v y • Y) =
        fun β => FullSpace.vertexDifference v β • Y := by
      funext β
      simp [FullSpace.restrictToPositiveEdges, FullSpace.vertexCoboundary,
        FullSpace.vertexDifference, sub_smul]
    unfold FullSpace.finiteEdgePairing
    rw [e, traceFinsumPairing_smul_right]
    rfl
  have e₃ : FullSpace.vertexAdjoint c x = ∑ᶠ β, c β * FullSpace.vertexDifference v β := by
    rw [← hS.2.2.1 c v hv]
    exact (finsum_mul_piSingle_one _ x).symm
  rw [← e₁, hcancelled', e₂, ← e₃, hS.2.2.2.2 c x, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sub]
  rfl
def scaledEdgeForm {a : ℝ} (c : FullSpace.PositiveEdge a → ℂ) (Y : ComplexMatrix2) :
    Link a → ComplexMatrix2 :=
  open Classical in
  FullSpace.extendOddly fun β => if h : β.IsPositivelyOriented then c ⟨β, h⟩ • Y else 0
section Forms
variable {a : ℝ} (c : FullSpace.PositiveEdge a → ℂ) (Y : ComplexMatrix2)
theorem scaledEdgeForm_of_isPositivelyOriented {β : Link a} (h : β.IsPositivelyOriented) :
    scaledEdgeForm c Y β = c ⟨β, h⟩ • Y := by
  classical
  simp [scaledEdgeForm, FullSpace.extendOddly, h]
theorem scaledEdgeForm_forwardFrom (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    scaledEdgeForm c Y (Link.forwardFrom x μ) = c (forwardEdge x μ) • Y :=
  scaledEdgeForm_of_isPositivelyOriented c Y _
theorem scaledEdgeForm_mem (ha : 0 < a) (hY : Y ∈ ComplexMatrix2.traceless) :
    scaledEdgeForm c Y ∈ FullSpace.complexEdgeForms a := by
  classical
  show FullSpace.IsEdgeFormIn PeriodicLattice.complexLieAlgebra _
  refine ⟨fun β h => ?_, fun β => ?_⟩
  · rw [scaledEdgeForm_of_isPositivelyOriented c Y h]
    exact Submodule.smul_mem _ _ hY
  · by_cases h : β.IsPositivelyOriented
    · have hr : ¬ β.opposite.IsPositivelyOriented := fun h' =>
        InfiniteLattice.opposite_notMem_positiveLinks ha
          (InfiniteLattice.mem_positiveLinks_iff.2 h)
          (InfiniteLattice.mem_positiveLinks_iff.2 h')
      simp [scaledEdgeForm, FullSpace.extendOddly, h, hr, Link.opposite_opposite]
    · have hr : β.opposite.IsPositivelyOriented := by
        rcases InfiniteLattice.mem_positiveLinks_or_opposite_mem β with h' | h'
        · exact absurd (InfiniteLattice.mem_positiveLinks_iff.1 h') h
        · exact InfiniteLattice.mem_positiveLinks_iff.1 h'
      simp [scaledEdgeForm, FullSpace.extendOddly, h, hr]
theorem restrictToPositiveEdges_scaledEdgeForm :
    FullSpace.restrictToPositiveEdges (scaledEdgeForm c Y) = fun β => c β • Y :=
  funext fun β => scaledEdgeForm_of_isPositivelyOriented c Y β.2
theorem edgeCoboundary_scaledEdgeForm :
    FullSpace.edgeCoboundary (scaledEdgeForm c Y) =
      fun p => FullSpace.edgeDifference c p • Y := by
  funext p
  simp only [FullSpace.edgeCoboundary, FullSpace.edgeDifference, scaledEdgeForm_forwardFrom,
    add_smul, sub_smul]
end Forms
theorem exists_edgeCoboundaryAdjoint_spec
    (mw : HasTransposeKernel (FullSpace.edgePauliCoordinates L 0 0) (vertexCoordinate (FullSpace.Face L 0 0))
      FullSpace.edgeCoboundary)
    {f : FullSpace.Face L 0 0 → ComplexMatrix2}
    (hf : f ∈ Matrices.GroupLieProduct.tracelessFunctions (FullSpace.Face L 0 0)) :
    ∃ t : FullSpace.Edge L 0 0 → ComplexMatrix2, edgeCoboundaryAdjoint L f = t ∧
      t ∈ FullSpace.complexEdgeForms (meshAt L 0 0) ∧
      ∀ B ∈ FullSpace.complexEdgeForms (meshAt L 0 0),
        HasFiniteSupp (FullSpace.restrictToPositiveEdges B) →
        FullSpace.finiteEdgePairing t B = traceFinsumPairing f (FullSpace.edgeCoboundary B) := by
  classical
  refine ⟨(transposeMap (linearOfValues (FullSpace.edgePairedSpace (meshAt L 0 0))
    (pairedFunctions (FullSpace.Face L 0 0))
    (FullSpace.edgeCoboundary (a := meshAt L 0 0))) ⟨f, hf⟩).1, ?_,
    Subtype.prop (transposeMap (linearOfValues (FullSpace.edgePairedSpace (meshAt L 0 0))
      (pairedFunctions (FullSpace.Face L 0 0))
      (FullSpace.edgeCoboundary (a := meshAt L 0 0))) ⟨f, hf⟩),
    fun B hB hfin => ?_⟩
  · unfold edgeCoboundaryAdjoint PairedFunctionSpace.transposeOfValues
    exact dif_pos hf
  · exact (mw.isTranspose ⟨f, hf⟩ ⟨B, hB⟩ hfin).trans
      (congrArg (traceFinsumPairing f) (mw.coe_linear ⟨B, hB⟩))
theorem edgeCoboundaryAdjoint_forwardFrom (ha : 0 < meshAt L 0 0)
    (hS : FullSpace.FaceAdjointProperties ℂ (meshAt L 0 0))
    (mw : HasTransposeKernel (FullSpace.edgePauliCoordinates L 0 0) (vertexCoordinate (FullSpace.Face L 0 0))
      FullSpace.edgeCoboundary)
    {f : FullSpace.Face L 0 0 → ComplexMatrix2}
    (hf : f ∈ Matrices.GroupLieProduct.tracelessFunctions (FullSpace.Face L 0 0))
    (x : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    edgeCoboundaryAdjoint L f (Link.forwardFrom x μ) =
      (∑ ν : {ν : Fin 4 // μ < ν},
        (f ⟨x, μ, ν.1, ν.2⟩ - f ⟨x - axisStep (meshAt L 0 0) ν.1, μ, ν.1, ν.2⟩)) -
      ∑ ν : {ν : Fin 4 // ν < μ},
        (f ⟨x, ν.1, μ, ν.2⟩ - f ⟨x - axisStep (meshAt L 0 0) ν.1, ν.1, μ, ν.2⟩) := by
  classical
  have val : ∀ p : FullSpace.Face L 0 0, f p ∈ ComplexMatrix2.traceless :=
    fun p => hf p (Set.mem_univ p)
  obtain ⟨t, ht, hmem, key⟩ := exists_edgeCoboundaryAdjoint_spec mw hf
  rw [ht]
  refine eq_of_halfTraceWith_eq (hmem.1 _ ⟨μ, by simp [Link.forwardFrom]⟩)
    (Submodule.sub_mem _ (Submodule.sum_mem _ fun ν _ => Submodule.sub_mem _ (val _) (val _))
      (Submodule.sum_mem _ fun ν _ => Submodule.sub_mem _ (val _) (val _))) fun Y hY => ?_
  let w : FullSpace.PositiveEdge (meshAt L 0 0) → ℂ := Pi.single (forwardEdge x μ) 1
  have hw : (Function.support w).Finite := finite_support_piSingle_one _
  have hB := scaledEdgeForm_mem w Y ha hY
  have hfin : HasFiniteSupp (FullSpace.restrictToPositiveEdges (scaledEdgeForm w Y)) := by
    rw [restrictToPositiveEdges_scaledEdgeForm]
    exact hasFiniteSupp_smul_const hw Y
  have hcancelled' := key _ hB hfin
  let g : FullSpace.Face L 0 0 → ℂ := fun p => halfTraceWith Y (f p)
  have e₁ : FullSpace.finiteEdgePairing t (scaledEdgeForm w Y) =
      halfTraceWith Y (t (Link.forwardFrom x μ)) := by
    unfold FullSpace.finiteEdgePairing
    rw [restrictToPositiveEdges_scaledEdgeForm, traceFinsumPairing_smul_right]
    exact finsum_mul_piSingle_one
      (fun β => halfTraceWith Y (FullSpace.restrictToPositiveEdges t β)) (forwardEdge x μ)
  have e₂ : traceFinsumPairing f (FullSpace.edgeCoboundary (scaledEdgeForm w Y)) =
      ∑ᶠ p, g p * FullSpace.edgeDifference w p := by
    rw [edgeCoboundary_scaledEdgeForm, traceFinsumPairing_smul_right]
  have e₃ : FullSpace.faceAdjoint g (forwardEdge x μ) =
      ∑ᶠ p, g p * FullSpace.edgeDifference w p := by
    rw [← hS.2.2.1 g w hw]
    exact (finsum_mul_piSingle_one _ _).symm
  rw [← e₁, hcancelled', e₂, ← e₃, hS.2.2.2.2 g x μ, map_sub, map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun ν _ => ?_
    rw [map_sub]
  · refine Finset.sum_congr rfl fun ν _ => ?_
    rw [map_sub]
theorem adjointFormulas_holds (hS : ScalarDifferenceAdjoints)
    (hK : CovDiffTransposes.Claim) : AdjointFormulas := by
  intro L hL
  have ha : 0 < meshAt L 0 0 := by
    have h0 : 0 < L := by
      have := hL.2
      omega
    exact zpow_pos (by exact_mod_cast h0) _
  have hU : (fun _ => 1) ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup := by
    refine ⟨fun _ => ?_, fun _ => by simp⟩
    show (1 : ComplexMatrix2).det = 1
    simp
  have cl := ((hK L hL 0 0 le_rfl).2 _ hU).1
  exact ⟨fun b hb x => vertexCoboundaryAdjoint_apply (hS L hL).1 cl.vertexCoboundary hb x,
    fun f hf x μ =>
      edgeCoboundaryAdjoint_forwardFrom ha (hS L hL).2.1 cl.edgeCoboundary hf x μ⟩
end YangMills.Construction.Tower.UnitLatticeAdjoints
end

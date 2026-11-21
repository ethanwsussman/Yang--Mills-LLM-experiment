import YangMills.Construction.Towers.CovariantShiftsOfAnAbelianFieldProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.InfiniteLattice.TorusOfAPeriodLatticeIsFaithfulProof
import YangMills.Construction.Towers.EntriesOfTheAbelianKernelsProof
import YangMills.Construction.Towers.TransposesOfDifferencesAtScalarFunctionsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.UnitGaugeDirections
open Matrices
open PeriodicOperators (Represents RowFinite KernelMatrix ApplySummable ApplySummableAt
  applyKernel compKernel swapKernel ColumnFinite)
open CovDiffTransposes (LatticeTransposeData matrixKernel transposeComp compTranspose)
section Kernels
variable {N N' N'' : Type}
theorem applyKernel_basisFunction (T : KernelMatrix N N) (j i : N) :
    applyKernel T (basisFunction i) j = T j i := by apply _root_.YangMills.Construction.Tower.AbelianKernelEntries.applyKernel_basisFunction <;> assumption
theorem isUniqueRowFiniteKernelAction_of_represents {M : (N → ℂ) → N → ℂ} {T : KernelMatrix N N}
    (hT : Represents T M) (hR : RowFinite T) : IsUniqueRowFiniteKernelAction M := by
  refine ⟨T, hT, fun T' hT' => ?_, fun j i => ?_, hR⟩
  · funext j i
    rw [← applyKernel_basisFunction T' j i, ← applyKernel_basisFunction T j i,
      (hT' _).2, (hT _).2]
  · rw [← (hT _).2, applyKernel_basisFunction]
theorem applySummable_of_rowFinite {T : KernelMatrix N N'} (h : RowFinite T) (f : N → ℂ) :
    ApplySummable T f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applySummable_of_rowFinite <;> assumption
theorem rowFinite_compKernel {T : KernelMatrix N' N''} {S : KernelMatrix N N'}
    (hT : RowFinite T) (hS : RowFinite S) : RowFinite (compKernel T S) := by apply _root_.YangMills.Construction.Tower.RescaledKernels.rowFinite_compKernel <;> assumption
theorem rowFinite_add {T S : KernelMatrix N N'} (hT : RowFinite T)
    (hS : RowFinite S) : RowFinite (fun j i => T j i + S j i) := by
  intro j
  refine ((hT j).union (hS j)).subset fun i hi => ?_
  by_contra hn
  apply hi
  have h₁ : T j i = 0 := by
    by_contra h
    exact hn (Or.inl h)
  have h₂ : S j i = 0 := by
    by_contra h
    exact hn (Or.inr h)
  simp [h₁, h₂]
theorem applyKernel_add {T S : KernelMatrix N N'} (hT : RowFinite T) (hS : RowFinite S)
    (f : N → ℂ) (j : N') :
    applyKernel (fun j i => T j i + S j i) f j =
      applyKernel T f j + applyKernel S f j := by
  have s₁ : Summable fun i => T j i * f i :=
    (applySummable_of_rowFinite hT f j).of_norm
  have s₂ : Summable fun i => S j i * f i :=
    (applySummable_of_rowFinite hS f j).of_norm
  show ∑' i, (T j i + S j i) * f i = ∑' i, T j i * f i + ∑' i, S j i * f i
  rw [← s₁.tsum_add s₂]
  exact tsum_congr fun i => add_mul _ _ _
end Kernels
section Coefficients
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem pauliCoeff_add (a : Fin 3) {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p106 <;> assumption
theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (i : σ) :
    ofPauliCoeffs c i ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem toPauliCoeffs_ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
end Coefficients
section Steps
open InfiniteLattice
variable {a : ℝ}
theorem axisStep_injective (ha : a ≠ 0) : Function.Injective (axisStep a) := by apply _root_.YangMills.Construction.Tower.DifferenceAdjoints.axisStep_injective <;> assumption
theorem axisStep_ne_zero (ha : a ≠ 0) (μ : Fin 4) : axisStep a μ ≠ 0 := by apply _root_.YangMills.Construction.InfiniteLattice.QuotientTorusFaithful.axisStep_ne_zero <;> assumption
theorem extendOddly_of_positive (f : InfiniteLattice.Link a → ComplexMatrix2)
    {e : InfiniteLattice.Link a} (he : e.IsPositivelyOriented) :
    FullSpace.extendOddly f e = f e := if_pos he
end Steps
section UnitLattice
variable {L : ℕ}
theorem meshAt_zero_pos (L : ℕ) : 0 < meshAt L 0 0 := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.meshAt_zero_pos <;> assumption
theorem incomingEdge_isPositivelyOriented (x : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    (incomingEdge x μ).IsPositivelyOriented :=
  ⟨μ, by
    show x - InfiniteLattice.axisStep _ μ + InfiniteLattice.axisStep _ μ -
      (x - InfiniteLattice.axisStep _ μ) = _
    abel⟩
theorem outgoingEdge_isPositivelyOriented (x : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    (outgoingEdge x μ).IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.forwardFrom_isPositivelyOriented <;> assumption
theorem incomingEdge_injective (x : FullSpace.Vertex L 0 0) :
    Function.Injective (incomingEdge x) := by
  intro μ ν h
  have e : x - InfiniteLattice.axisStep _ μ = x - InfiniteLattice.axisStep _ ν :=
    congrArg InfiniteLattice.Link.initial h
  exact axisStep_injective (meshAt_zero_pos L).ne' (sub_right_inj.mp e)
theorem outgoingEdge_injective (x : FullSpace.Vertex L 0 0) :
    Function.Injective (outgoingEdge x) := by
  intro μ ν h
  have e : x + InfiniteLattice.axisStep _ μ = x + InfiniteLattice.axisStep _ ν :=
    congrArg InfiniteLattice.Link.terminal h
  exact axisStep_injective (meshAt_zero_pos L).ne' (add_left_cancel e)
theorem eightIncidentEdges (L : ℕ) : EightIncidentEdges L := by
  intro x
  refine ⟨?_, ?_⟩
  · ext e
    constructor
    · rintro ⟨⟨μ, hμ⟩, h | h⟩
      · refine Or.inl ⟨μ, InfiniteLattice.Link.ext ?_ ?_⟩
        · show x - InfiniteLattice.axisStep _ μ = e.initial
          rw [← h, ← hμ]
          abel
        · show x - InfiniteLattice.axisStep _ μ + InfiniteLattice.axisStep _ μ = e.terminal
          rw [h]
          abel
      · refine Or.inr ⟨μ, InfiniteLattice.Link.ext h.symm ?_⟩
        show x + InfiniteLattice.axisStep _ μ = e.terminal
        rw [← h, ← hμ]
        abel
    · rintro (⟨μ, rfl⟩ | ⟨μ, rfl⟩)
      · refine ⟨incomingEdge_isPositivelyOriented x μ, Or.inl ?_⟩
        show x - InfiniteLattice.axisStep _ μ + InfiniteLattice.axisStep _ μ = x
        abel
      · exact ⟨outgoingEdge_isPositivelyOriented x μ, Or.inr rfl⟩
  · have hd : Disjoint (range (incomingEdge x)) (range (outgoingEdge x)) := by
      rw [Set.disjoint_left]
      rintro _ ⟨μ, rfl⟩ ⟨ν, h⟩
      have e : x = x - InfiniteLattice.axisStep _ μ := congrArg InfiniteLattice.Link.initial h
      exact axisStep_ne_zero (meshAt_zero_pos L).ne' μ (sub_eq_self.mp e.symm)
    have c₁ : (range (incomingEdge x)).ncard = 4 := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ (incomingEdge_injective x)]
      simp [Set.ncard_univ]
    have c₂ : (range (outgoingEdge x)).ncard = 4 := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ (outgoingEdge_injective x)]
      simp [Set.ncard_univ]
    unfold incidentEdges
    rw [Set.ncard_union_eq hd (Set.finite_range _) (Set.finite_range _), c₁, c₂]
theorem vertex_ofCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) :
    (vertexCoordinate σ).ofCoeffs c ∈ (vertexCoordinate σ).space.complexSubmodule :=
  fun i _ => ofPauliCoeffs_mem c i
theorem vertex_coeffs_ofCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    (vertexCoordinate σ).coeffs ((vertexCoordinate σ).ofCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
theorem edge_ofCoeffs_mem (c : (FullSpace.edgePauliCoordinates L 0 0).Index → ℂ) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c ∈
      (FullSpace.edgePauliCoordinates L 0 0).space.complexSubmodule := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.edge_ofCoeffs_mem <;> assumption
theorem edge_coeffs_ofCoeffs (c : (FullSpace.edgePauliCoordinates L 0 0).Index → ℂ) :
    (FullSpace.edgePauliCoordinates L 0 0).coeffs ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.edge_coeffs_ofCoeffs <;> assumption
abbrev TransposeDataAt (U : FullSpace.Edge L 0 0 → ComplexMatrix2) : Prop :=
  LatticeTransposeData (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.edgePauliCoordinates L 0 0)
    (vertexCoordinate (FullSpace.Face L 0 0)) (FullSpace.covDiff U)
    FullSpace.vertexCoboundary FullSpace.edgeCoboundary
    (FullSpace.complexHessianOperator U) (FullSpace.complexHessianKernel U)
theorem covDiffAndAdjoint {U : FullSpace.Edge L 0 0 → ComplexMatrix2} (hC : TransposeDataAt U) :
    CovDiffAndAdjoint U := by
  refine ⟨fun l _ l' _ e he h₁ h₂ => ?_, hC.covDiff.coe_linear,
    hC.covDiff.preserves_finite_support, hC.covDiff.isTranspose,
    fun B => ?_⟩
  · simp only [FullSpace.covDiff, extendOddly_of_positive _ he, h₁, h₂]
  · show PairedFunctionSpace.transposeOfValues _ _ _ _ = _
    unfold PairedFunctionSpace.transposeOfValues
    rw [dif_pos B.2]
    rfl
theorem covDiff_ofPauliCoeffs_eq_zero (U : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (c : Fin 3 × FullSpace.Vertex L 0 0 → ℂ) {e : FullSpace.Edge L 0 0}
    (he : e.IsPositivelyOriented)
    (h₁ : ∀ a, c (a, e.terminal) = 0) (h₂ : ∀ a, c (a, e.initial) = 0) :
    FullSpace.covDiff U (ofPauliCoeffs c) e = 0 := by
  have e₁ : ofPauliCoeffs c e.terminal = 0 := by simp [ofPauliCoeffs, h₁]
  have e₂ : ofPauliCoeffs c e.initial = 0 := by simp [ofPauliCoeffs, h₂]
  simp only [FullSpace.covDiff, extendOddly_of_positive _ he, e₁, e₂]
  simp [ComplexMatrix2.conjugateBy]
theorem matrixKernel_eq_zero_of_not_incident (U : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (x : FullSpace.Vertex L 0 0) (a : Fin 3)
    (p : (FullSpace.edgePauliCoordinates L 0 0).Index) (hp : p.2.1 ∉ incidentEdges x) :
    matrixKernel (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.edgePauliCoordinates L 0 0)
      (FullSpace.covDiff U) p (a, x) = 0 := by
  have ht : p.2.1.terminal ≠ x := fun h => hp (by
    rw [← ((eightIncidentEdges L) x).1]
    exact ⟨p.2.2, Or.inl h⟩)
  have hs : p.2.1.initial ≠ x := fun h => hp (by
    rw [← ((eightIncidentEdges L) x).1]
    exact ⟨p.2.2, Or.inr h⟩)
  show pauliCoeff p.1 (FullSpace.covDiff U (ofPauliCoeffs _) p.2.1) = 0
  refine (congrArg (pauliCoeff p.1) (covDiff_ofPauliCoeffs_eq_zero U _ p.2.2
    (fun a' => if_neg fun h => ht (congrArg Prod.snd h))
    (fun a' => if_neg fun h => hs (congrArg Prod.snd h)))).trans (pauliCoeff_zero _)
theorem adjointIsLocal {U : FullSpace.Edge L 0 0 → ComplexMatrix2} (hC : TransposeDataAt U) :
    AdjointIsLocal U := by
  intro B hB B' hB' x hagree
  have hmem : ∀ B'' ∈ (unitEdgeSpace L).complexSubmodule,
      FullSpace.covDiffAdjoint U B'' x ∈ ComplexMatrix2.traceless := fun B'' h =>
    (hC.compTranspose_mem B'' h).1 x (mem_univ x)
  have hco : ∀ a, pauliCoeff a (FullSpace.covDiffAdjoint U B x) =
      pauliCoeff a (FullSpace.covDiffAdjoint U B' x) := by
    intro a
    have e := (hC.covDiff.transpose_represents B hB (a, x)).2
    have e' := (hC.covDiff.transpose_represents B' hB' (a, x)).2
    refine e.trans (Eq.trans (tsum_congr fun p => ?_) e'.symm)
    by_cases hp : p.2.1 ∈ incidentEdges x
    · have h : (FullSpace.edgePauliCoordinates L 0 0).coeffs B p =
          (FullSpace.edgePauliCoordinates L 0 0).coeffs B' p := by
        show pauliCoeff p.1 (B p.2.1) = pauliCoeff p.1 (B' p.2.1)
        rw [hagree _ hp]
      rw [h]
    · have hz : swapKernel (matrixKernel (vertexCoordinate (FullSpace.Vertex L 0 0))
          (FullSpace.edgePauliCoordinates L 0 0) (FullSpace.covDiff U)) (a, x) p = 0 :=
        matrixKernel_eq_zero_of_not_incident U x a p hp
      rw [hz, zero_mul, zero_mul]
  calc FullSpace.covDiffAdjoint U B x
      = ∑ a, pauliCoeff a (FullSpace.covDiffAdjoint U B x) • ComplexMatrix2.pauliFamily a :=
        (sum_pauliCoeff_smul (hmem B hB)).symm
    _ = ∑ a, pauliCoeff a (FullSpace.covDiffAdjoint U B' x) • ComplexMatrix2.pauliFamily a :=
        Finset.sum_congr rfl fun a _ => by rw [hco a]
    _ = FullSpace.covDiffAdjoint U B' x := sum_pauliCoeff_smul (hmem B' hB')
theorem compositesDefined {U : FullSpace.Edge L 0 0 → ComplexMatrix2} (hC : TransposeDataAt U) :
    CompositesDefined U := by
  refine ⟨fun l hl => hC.transposeComp_mem l hl, fun B hB => ?_⟩
  obtain ⟨h₁, h₂⟩ := hC.compTranspose_mem B hB
  obtain ⟨h₃, _, h₅⟩ := hC.operator_mem B hB
  exact ⟨h₁, h₂, h₃, h₅⟩
theorem gaugeLaplacian_isKernelAction {U : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hC : TransposeDataAt U) :
    IsUniqueRowFiniteKernelAction
      (PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L 0 0))
        (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.gaugeLaplacian U)) := by
  have hrows : RowFinite (compKernel
      (swapKernel (matrixKernel (vertexCoordinate (FullSpace.Vertex L 0 0))
        (FullSpace.edgePauliCoordinates L 0 0) (FullSpace.covDiff U)))
      (matrixKernel (vertexCoordinate (FullSpace.Vertex L 0 0))
        (FullSpace.edgePauliCoordinates L 0 0) (FullSpace.covDiff U))) :=
    rowFinite_compKernel hC.covDiff.column_finite hC.covDiff.row_finite
  refine isUniqueRowFiniteKernelAction_of_represents
    (fun f => ⟨applySummable_of_rowFinite hrows f, funext fun p => ?_⟩) hrows
  have e := (hC.transposeComp_represents.2 ((vertexCoordinate (FullSpace.Vertex L 0 0)).ofCoeffs f)
    (vertex_ofCoeffs_mem f) p).2
  have hc : (vertexCoordinate (FullSpace.Vertex L 0 0)).coeffs
      ((vertexCoordinate (FullSpace.Vertex L 0 0)).ofCoeffs f) = f := vertex_coeffs_ofCoeffs f
  rw [hc] at e
  exact e.symm
theorem massiveHessian_isKernelAction {U : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hC : TransposeDataAt U) (hA : RowFinite (FullSpace.complexHessianKernel U)) :
    IsUniqueRowFiniteKernelAction
      (PauliComponentsOfSymmetricKernel.mapOnCoeffs (FullSpace.edgePauliCoordinates L 0 0) (FullSpace.edgePauliCoordinates L 0 0)
        (FullSpace.massiveHessian U)) := by
  have hP : RowFinite (compKernel
      (matrixKernel (vertexCoordinate (FullSpace.Vertex L 0 0))
        (FullSpace.edgePauliCoordinates L 0 0) (FullSpace.covDiff U))
      (swapKernel (matrixKernel (vertexCoordinate (FullSpace.Vertex L 0 0))
        (FullSpace.edgePauliCoordinates L 0 0) (FullSpace.covDiff U)))) :=
    rowFinite_compKernel hC.covDiff.row_finite hC.covDiff.column_finite
  have hT := rowFinite_add hA hP
  refine isUniqueRowFiniteKernelAction_of_represents
    (fun f => ⟨applySummable_of_rowFinite hT f, funext fun p => ?_⟩) hT
  refine (applyKernel_add hA hP f p).trans ?_
  have hB := edge_ofCoeffs_mem f
  have e₂ := (hC.compTranspose_represents.2 _ hB p).2
  rw [edge_coeffs_ofCoeffs] at e₂
  have e₁ : FullSpace.complexHessianOperator U ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs f) p.2.1 =
      ofPauliCoeffs (applyKernel (FullSpace.complexHessianKernel U) f) p.2 := by
    have e : toPauliCoeffs (FullSpace.restrictToPositiveEdges
        ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs f)) = f :=
      edge_coeffs_ofCoeffs f
    have e₀ : FullSpace.complexHessianOperator U ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs f) p.2.1 =
        ofPauliCoeffs (applyKernel (FullSpace.complexHessianKernel U)
          (toPauliCoeffs (FullSpace.restrictToPositiveEdges
            ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs f)))) p.2 := by
      show FullSpace.extendOddly _ _ = _
      rw [extendOddly_of_positive _ p.2.2]
      exact dif_pos p.2.2
    rw [e₀, e]
  have m₁ : FullSpace.complexHessianOperator U ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs f) p.2.1 ∈
      ComplexMatrix2.traceless := by
    rw [e₁]
    exact ofPauliCoeffs_mem _ _
  have m₂ := (hC.compTranspose_mem _ hB).2.1 p.2.1 p.2.2
  have e₃ : pauliCoeff p.1 (FullSpace.complexHessianOperator U
      ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs f) p.2.1) =
      applyKernel (FullSpace.complexHessianKernel U) f p := by
    rw [e₁]
    exact congrFun (toPauliCoeffs_ofPauliCoeffs _) p
  exact (congrArg₂ (· + ·) e₃.symm e₂.symm).trans (pauliCoeff_add p.1 m₁ m₂).symm
end UnitLattice
theorem claim_holds (hX : CovDiffTransposes.Claim)
    (hA : HessianKernel.KernelProperties) : Claim := by
  intro L hL
  refine ⟨eightIncidentEdges L, fun U hU => ?_⟩
  have hC : TransposeDataAt U := ((hX L hL 0 0 le_rfl).2 U hU).1
  have hR : RowFinite (FullSpace.complexHessianKernel U) :=
    ((hA L hL 0 0 le_rfl).2 U hU).2.2.1
  exact ⟨covDiffAndAdjoint hC, adjointIsLocal hC, compositesDefined hC,
    gaugeLaplacian_isKernelAction hC, massiveHessian_isKernelAction hC hR⟩
end YangMills.Construction.Tower.UnitGaugeDirections
end

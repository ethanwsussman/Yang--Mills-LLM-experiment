import YangMills.Construction.Towers.EntriesOfTheAbelianKernelsProof
import YangMills.Construction.Towers.TheAbelianOperatorsAsValuesOfTheOperatorFunctions
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.AbelianFieldDensity
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.OpFunValues
open YangMills.Construction.PeriodicOperators (Represents colourVertices colourEdges idKernel)
open AbelianFieldFacts UnitGaugeDirections YangMills.Construction.OneLoopNotation
section PauliCoeffs
theorem toPauliCoeffs_ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
end PauliCoeffs
section LinkField
variable {L : ℕ}
theorem ofPauliCoeffs_thirdPauliField (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    ofPauliCoeffs (thirdPauliField (L := L) θ) b =
      (θ b : ℂ) • Matrices.ComplexMatrix2.pauliFamily 2 := by
  simp [ofPauliCoeffs, thirdPauliField]
theorem edgePauliCoordinates_thirdPauliField_of_positive (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    (b : FullSpace.Edge L 0 0) (h : b.IsPositivelyOriented) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (thirdPauliField (L := L) θ) b =
      (θ ⟨b, h⟩ : ℂ) • Matrices.ComplexMatrix2.pauliFamily 2 := by
  simp only [FullSpace.edgePauliCoordinates, FullSpace.extendOddly, if_pos h, dif_pos h]
  exact ofPauliCoeffs_thirdPauliField θ ⟨b, h⟩
theorem edgePauliCoordinates_thirdPauliField_opposite_of_not_positive
    (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    (b : FullSpace.Edge L 0 0) (h : ¬ b.IsPositivelyOriented)
    (h' : ¬ b.opposite.IsPositivelyOriented) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (thirdPauliField (L := L) θ) b.opposite = 0 := by
  simp only [FullSpace.edgePauliCoordinates, FullSpace.extendOddly, if_neg h']
  rw [dif_neg (show ¬ b.opposite.opposite.IsPositivelyOriented from h), neg_zero]
theorem expField_thirdPauliField (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) :
    FullSpace.expField (L := L) (thirdPauliField (L := L) θ) =
      FullSpace.abelianLinkField θ := by
  funext b
  show FullSpace.expTwist _ _ b = _
  by_cases h : b.IsPositivelyOriented
  · simp only [FullSpace.expTwist, FullSpace.abelianLinkField, if_pos h, dif_pos h, mul_one]
    rw [edgePauliCoordinates_thirdPauliField_of_positive θ b h]
  · by_cases h' : b.opposite.IsPositivelyOriented
    · simp only [FullSpace.expTwist, FullSpace.abelianLinkField, if_neg h, dif_neg h, dif_pos h',
        mul_one]
      rw [edgePauliCoordinates_thirdPauliField_of_positive θ b.opposite h']
    · simp only [FullSpace.expTwist, FullSpace.abelianLinkField, if_neg h, dif_neg h, dif_neg h',
        mul_one]
      rw [edgePauliCoordinates_thirdPauliField_opposite_of_not_positive θ b h h']
      simp [NormedSpace.exp_zero]
end LinkField
section MatrixEntries
variable {L : ℕ}
theorem kernelOfMap_apply {N : Type} {M : (N → ℂ) → N → ℂ}
    (h : IsUniqueRowFiniteKernelAction M) (i' i : N) :
    PeriodicOperators.kernelOfMap M i' i = M (basisFunction i) i' := by apply _root_.YangMills.Construction.Tower.AbelianKernelEntries.kernelOfMap_apply <;> assumption
theorem coe_basisVec {J : Type} (i : J) :
    ((basisVec i : lp (fun _ : J => ℂ) 2) : J → ℂ) = basisFunction i := by apply _root_.YangMills.Construction.Tower.AbelianOperatorsLocalSelfAdjointProof.basisVec_coe <;> assumption
theorem matrixEntry_laplacianOp {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
    (hO : AbelianOperators θ) (hK : CompositesAreKernels (FullSpace.abelianLinkField θ))
    (i' i : VertexIndex L) :
    matrixEntry (laplacianOp θ) i' i = abelianLaplacianKernel θ i' i := by
  have h₁ : abelianLaplacianKernel θ i' i = _ := kernelOfMap_apply hK.1 i' i
  rw [h₁]
  have h₂ := hO.laplacian_apply (basisVec i)
  have h₃ : ofCoords (basisVec i : lp (fun _ : VertexIndex L => ℂ) 2) =
      ofPauliCoeffs (basisFunction i) := by
    rw [coe_basisVec]
    rfl
  rw [h₃] at h₂
  show laplacianOp θ (basisVec i) i' =
    toPauliCoeffs (FullSpace.gaugeLaplacian (FullSpace.abelianLinkField θ)
      (ofPauliCoeffs (basisFunction i))) i'
  have h₄ : FullSpace.gaugeLaplacian (FullSpace.abelianLinkField θ)
      (ofPauliCoeffs (basisFunction i)) =
      ofPauliCoeffs (laplacianOp θ (basisVec i)) := h₂.symm
  rw [h₄, toPauliCoeffs_ofPauliCoeffs]
theorem matrixEntry_massiveOp {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
    (hO : AbelianOperators θ) (hK : CompositesAreKernels (FullSpace.abelianLinkField θ))
    (i' i : EdgeIndex L) :
    matrixEntry (AbelianFieldDensity.massiveOp θ) i' i = abelianHessianKernel θ i' i := by
  have h₁ : abelianHessianKernel θ i' i = _ := kernelOfMap_apply hK.2 i' i
  rw [h₁]
  have h₂ := hO.hessian_apply (basisVec i)
  have h₃ : ofCoords (basisVec i : lp (fun _ : EdgeIndex L => ℂ) 2) =
      ofPauliCoeffs (basisFunction i) := by
    rw [coe_basisVec]
    rfl
  rw [h₃] at h₂
  show AbelianFieldDensity.massiveOp θ (basisVec i) i' =
    toPauliCoeffs (FullSpace.restrictToPositiveEdges
      (FullSpace.massiveHessian (FullSpace.abelianLinkField θ)
        (formOfPositiveValues (ofPauliCoeffs (basisFunction i))))) i'
  have h₄ : FullSpace.restrictToPositiveEdges
      (FullSpace.massiveHessian (FullSpace.abelianLinkField θ)
        (formOfPositiveValues (ofPauliCoeffs (basisFunction i)))) =
      ofPauliCoeffs (AbelianFieldDensity.massiveOp θ (basisVec i)) := h₂.symm
  rw [h₄, toPauliCoeffs_ofPauliCoeffs]
theorem matrixEntry_addScalar {J : Type} (T : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2)
    (s : ℝ) (i' i : J) :
    matrixEntry (addScalar T s) i' i = matrixEntry T i' i + (s : ℂ) * basisFunction i i' := by
  have e := congrFun (coe_basisVec i) i'
  show (T (basisVec i) + (s : ℂ) • basisVec i : lp (fun _ : J => ℂ) 2) i' = _
  rw [lp.coeFn_add, lp.coeFn_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e]
  rfl
end MatrixEntries
theorem abelianOperatorsAreOpFunValues_holds (hOperators : AbelianOperatorsLocalSelfAdjoint)
    (hPlaquettes : AbelianFieldPlaquettes.Claim)
    (hGauge : UnitGaugeDirections.Claim) :
    AbelianOperatorsAreOpFunValues := by
  intro L hL z _ θ
  have hU : FullSpace.abelianLinkField θ ∈
      FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup := by
    have h := (hPlaquettes L hL θ).abelianLinkField_mem
    exact ⟨fun b => (Matrix.mem_specialUnitaryGroup_iff.1 (h.1 b)).2, h.2⟩
  have hK : CompositesAreKernels (FullSpace.abelianLinkField θ) := ((hGauge L hL).2 _ hU).2.2.2
  have hO := hOperators L hL θ
  have hC := expField_thirdPauliField θ
  refine ⟨fun i' i => ?_, fun i' i => ?_⟩
  · have e := (matrixEntry_addScalar (laplacianOp θ) z i' i).trans
      (congrArg (· + (z : ℂ) * basisFunction i i') (matrixEntry_laplacianOp hO hK i' i))
    refine Eq.trans ?_ e.symm
    show FullSpace.gaugeLaplacianKernel (FullSpace.expField (thirdPauliField θ)) i' i +
        (z : ℂ) * idKernel (colourVertices L 0 0) i' i = _
    rw [hC]
    rfl
  · have e := (matrixEntry_addScalar (AbelianFieldDensity.massiveOp θ) z i' i).trans
      (congrArg (· + (z : ℂ) * basisFunction i i') (matrixEntry_massiveOp hO hK i' i))
    refine Eq.trans ?_ e.symm
    show FullSpace.massiveHessianKernel (FullSpace.expField (thirdPauliField θ)) i' i +
        (z : ℂ) * idKernel (colourEdges L 0 0) i' i = _
    rw [hC]
    rfl
end YangMills.Construction.Tower.MassiveOpFunctions.OpFunValues
end

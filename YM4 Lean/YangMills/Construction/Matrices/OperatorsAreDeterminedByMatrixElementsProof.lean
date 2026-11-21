import YangMills.Construction.Matrices.ExpansionInThePeterWeylBasis
import YangMills.Construction.Matrices.OperatorsAreDeterminedByMatrixElementsForm
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2 YangMills.Construction.HilbertSpaceBasics
noncomputable section
namespace YangMills.Construction.SpinHarmonics.MatrixEntries
open SeveralVariables
theorem allOpsDeterminedByEntries_of_expansion (hExp : PeterWeylExpansionHolds) :
    AllOpsDeterminedByEntries := by
  intro J _ _ A A' h
  have hx : PeterWeylExpansion J := hExp J
  have hvec : ∀ β : PeterWeylIndex J,
      A (peterWeylVec β) = A' (peterWeylVec β) := by
    intro β
    have h1 := (hx (A (peterWeylVec β))).1
    have h2 := (hx (A' (peterWeylVec β))).1
    have e : (fun α : PeterWeylIndex J =>
        (inner ℂ (peterWeylVec α) (A (peterWeylVec β)) : ℂ) • peterWeylVec α) =
        fun α : PeterWeylIndex J =>
        (inner ℂ (peterWeylVec α) (A' (peterWeylVec β)) : ℂ) • peterWeylVec α := by
      funext α
      have hα : (inner ℂ (peterWeylVec α) (A (peterWeylVec β)) : ℂ) =
          inner ℂ (peterWeylVec α) (A' (peterWeylVec β)) := h α β
      rw [hα]
    rw [e] at h1
    exact h1.unique h2
  refine ContinuousLinearMap.ext fun F => ?_
  have h0 := (hx F).1
  have h1 := A.hasSum h0
  have h2 := A'.hasSum h0
  have e : (fun α : PeterWeylIndex J =>
      A ((inner ℂ (peterWeylVec α) F : ℂ) • peterWeylVec α)) =
      fun α : PeterWeylIndex J =>
      A' ((inner ℂ (peterWeylVec α) F : ℂ) • peterWeylVec α) := by
    funext α
    rw [map_smul, map_smul, hvec α]
  rw [e] at h1
  exact h1.unique h2
end YangMills.Construction.SpinHarmonics.MatrixEntries
end

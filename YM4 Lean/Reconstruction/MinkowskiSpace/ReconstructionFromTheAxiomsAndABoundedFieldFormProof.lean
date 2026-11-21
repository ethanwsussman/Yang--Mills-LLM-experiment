import Reconstruction.Continuum.InvarianceOfSequenceOnTestFunctionSpaces
import Reconstruction.MinkowskiSpace.EuclideanFormOfAnInvariantRepresentedSequence
import Reconstruction.MinkowskiSpace.ImageOfATheoryUnderAUnitaryOperator
import Reconstruction.MinkowskiSpace.OperatorOfAFormOnTheSubspaceAtOrderedPositiveTimes
import Reconstruction.MinkowskiSpace.ReconstructionFromTheAxiomsAndABoundedFieldForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MinkowskiSpace
open YangMills.Construction.FieldForms YangMills.Construction.ConfigSpace YangMills.Construction.RealPointVectors YangMills.Construction.WightmanTheory YangMills.Construction.FieldFormHilbert YangMills.Construction.ProjectionMeasures YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert YangMills.Construction.FormReconstruction
theorem reconstructionFromBoundedForm_holds
    (hEucl : EuclideanOfInvariantRepresented)
    (hInvar : ConfigSpace.MotionInvarianceStatement)
    (hImg : UnitaryImageExists)
    (hIsom : ReconstructionIsometryExists)
    (hWight : FieldFormHilbert.WightmanFromEuclideanForm)
    (hSchw : FieldForms.EuclideanSchwingerProperties)
    (hShift : ConfigSpace.TimeShiftSemigroupStatement) : ReconstructionFromBoundedForm := by
  intro S h0 hC h1 h2 h3 K _ _ _ E Ω A p C hF hR
  have hEu := hEucl S h1 h3 E Ω A p C hF hR
  have hInv := hInvar S h1 h3
  have hSemi := hShift S h0 hC h2 hInv.translation
  obtain ⟨T, hT⟩ := (hWight E Ω A p C hF hEu).exists_theory
  have hCont : IsCLMSequence S := ⟨h0.1, hC⟩
  have hVal := fun m =>
    (hSchw K E Ω A p C hF hEu m).2.2.2.1 S hR (hInv.orthogonal m) (hInv.perm m)
  have hSeq : IsTheoryOf T S :=
    ⟨(hT.schwinger S hCont hVal).1, hT.covariant, hT.spectrum, hT.local_field⟩
  obtain ⟨J, hJ⟩ := hIsom S h0 hC h1 h2 h3 E Ω A p C hF hR
  obtain ⟨T', hT'⟩ := hImg J.symm T
  obtain ⟨F, -, hFs, hFt⟩ := hT.exists_energyMomentum
  obtain ⟨F', hF's, hF't⟩ := hT'.energyMomentum_image F hFs
  have hVac : IsVacuumClass S T'.vacuum := by
    obtain ⟨Φ, hΦ, hmem, -, -⟩ := hSemi.vacuum
    have hJΦ : J ⟨_, hmem⟩ = T.vacuum := Subtype.ext
      ((hJ.map_vacuumClass ⟨_, hmem⟩ ⟨Φ, hΦ, rfl⟩).trans hT.isFormTheory.vacuum_eq.symm)
    have hv : T'.vacuum = ⟨_, hmem⟩ := by
      rw [hT'.isUnitaryImage.vacuum_eq, ← hJΦ]
      exact J.symm_apply_apply _
    exact ⟨Φ, hΦ, by rw [hv]⟩
  have hRestr : HamiltonianSemigroupRestricts S T' := by
    refine ⟨F', hF's, fun t ht χ => ?_⟩
    obtain ⟨hmem, heq⟩ := hJ.map_timeShift t ht χ
    have hJt : J ⟨_, hmem⟩ = HermitianScalarTheory.hamiltonianSemigroup F t (J χ) :=
      Subtype.ext (heq.trans (hFt t ht (J χ)).symm)
    have hχ : J.symm (J χ) = χ := J.symm_apply_apply χ
    have hstep := hF't t (J χ) ht
    rw [hχ, ← hJt, J.symm_apply_apply] at hstep
    rw [hstep]
  exact
    { exists_theory := ⟨_, inferInstance, inferInstance, inferInstance, T, hSeq⟩
      nonexpanding := hSemi.nonexpanding
      shiftOp_spec := hSemi.shiftOp_spec
      semigroup := hSemi.semigroup
      strongCont := hSemi.strongCont
      symmetric := hSemi.symmetric
      contractive := hSemi.contractive
      mapsTo_positiveTimeSubspace := fun t ht χ hχ => hSemi.mapsTo_positiveTimeSubspace ⟨t, ht⟩ χ hχ
      exists_subspaceTheory := ⟨T', J, T, hT'.isTheoryOf_image S hSeq, hVac, hRestr, hJ,
        hT.isFormTheory, hT'.isUnitaryImage⟩ }
end YangMills.Construction.MinkowskiSpace
end

import YangMills.Construction.Continuum.ClusteringFromTuplesToSchwartzFunctions
import Reconstruction.MinkowskiSpace.FieldFormOfAFunctionalDefs
import Reconstruction.MinkowskiSpace.TheoriesOfASequenceImagesOfTheoriesAndTheOperatorOfAForm
import Reconstruction.MinkowskiSpace.WightmanTheoryOfAEuclideanFieldForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BoundedFieldWightman
variable (sigma : TestSpaces.SepTuple → ℝ)
def OnlyVacuumTimeInvariant
    (E : ProjectionMeasures.FourBorelSet →
      OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma)) : Prop :=
  ∀ χ : FieldFormConditions.StateSpace sigma,
    (∀ t : ℝ, 0 ≤ t → FieldForms.spectralTranslation E (FieldForms.imagTimeShift t) χ = χ) →
      ∃ c : ℂ, χ = c • FieldFormConditions.vacuumState sigma
structure FormSequenceProperties
    (E : ProjectionMeasures.FourBorelSet →
      OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma))
    (A : ℝ → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma))
    (S : ConfigSpace.FlatSequence) : Prop where
  euclid_invariant : ConfigSpace.IsEuclidInvariant S
  os_positive : ConfigSpace.IsOSPositive S
  perm_symmetric : ConfigSpace.IsPermSymmetric S
  reflection_real : ConfigSpace.IsReflectionReal S
  im_eq_zero_of_real : ∀ (m : ℕ) (φ : ConfigSpace.schwartzFlatOffDiagonal (m + 1)),
    (∀ x, (φ.1 x).im = 0) → (S.atSucc m φ).im = 0
  represents : FieldForms.RepresentsSequence E (FieldFormConditions.vacuumState sigma) A S
  eq_integralSchwinger : ∀ (m : ℕ) (φ : TestSpaces.PointTuple (m + 1) → ℂ),
    φ ∈ (TestSpaces.smoothCompactSupp (TestSpaces.distinctLocus (m + 1)) :
      Set (TestSpaces.PointTuple (m + 1) → ℂ)) →
    ∀ h : φ ∈ ConfigSpace.schwartzFlatOffDiagonal (m + 1),
      S.atSucc m ⟨φ, h⟩ =
        FieldForms.integralSchwinger E (FieldFormConditions.vacuumState sigma) A m φ
  linear_seq : ConfigSpace.IsLinearFunctionalSeq S
  continuous_seq : ConfigSpace.IsContinuousSeq S
  bounded_form : ∃ p C : ℝ,
    FieldForms.IsBoundedFieldForm E (FieldFormConditions.vacuumState sigma) A p C
  timeShift_spec : S.TimeShiftNonexpanding ∧ ∀ t : ℝ, 0 ≤ t →
    S.IsTimeShiftContraction t (S.timeShiftOp t)
  separable : TopologicalSpace.SeparableSpace S.positiveTimeSubspace
  exists_theory : ∃ (T' : WightmanTheory.HermitianScalarTheory S.positiveTimeSubspace)
    (J : FormsOperators.UnitaryMap S.positiveTimeSubspace
      (FieldFormHilbert.tensorHilbert E (FieldFormConditions.vacuumState sigma) A))
    (T : WightmanTheory.HermitianScalarTheory
      (FieldFormHilbert.tensorHilbert E (FieldFormConditions.vacuumState sigma) A)),
    FormReconstruction.IsTheoryOf T' S ∧ FormReconstruction.IsVacuumClass S T'.vacuum ∧
      FormReconstruction.HamiltonianSemigroupRestricts S T' ∧
      FormReconstruction.IsReconstructionIsometry E (FieldFormConditions.vacuumState sigma) A S J ∧
      FieldFormHilbert.IsFormTheory E (FieldFormConditions.vacuumState sigma) A T ∧
      FormReconstruction.IsUnitaryImage J.symm T T' ∧
      (OnlyVacuumTimeInvariant sigma E → T'.UniqueVacuum)
def WightmanFromBoundedFieldFunctional : Prop :=
  ∀ sigma : TestSpaces.SepTuple → ℝ, TestSpaces.IsSepFunctional sigma →
    FieldFormConditions.IsSymmetricInvariant sigma → FieldFormConditions.PairingPosSemidef sigma →
    ∀ E : ProjectionMeasures.FourBorelSet →
        OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma),
      FieldFormConditions.IsTranslationMeasure sigma E →
    FieldFormConditions.ExistsInsertionBound sigma →
    ∀ A : ℝ → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma),
      InsertedFieldForm.HasInsertionIntegral sigma E A →
    ∀ S : ConfigSpace.FlatSequence, (∀ c : ConfigSpace.flatOffDiagonalAt 0, S 0 c = c.1) →
      TestSpaces.IsSchwingerFamily sigma (WightmanReconstruction.flatSequenceAsMaps S) →
      FormSequenceProperties sigma E A S
end YangMills.Construction.BoundedFieldWightman
end

import Reconstruction.Continuum.TimeTranslationsOfASequence
import Reconstruction.MinkowskiSpace.HilbertSpaceOfTheTensorsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FormReconstruction
section Theories
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
structure IsUnitaryImage (L : FormsOperators.UnitaryMap H H')
    (T : WightmanTheory.HermitianScalarTheory H) (T' : WightmanTheory.HermitianScalarTheory H') :
    Prop where
  rep_eq : ∀ (g : WightmanTheory.PoincareElt) (ψ : H),
    T'.rep g (L ψ) = L (T.rep g ψ)
  vacuum_eq : T'.vacuum = L T.vacuum
  domain_eq : T'.domain = T.domain.map (L.toLinearEquiv : H →ₗ[ℂ] H')
  field_eq : ∀ (f : WightmanTheory.TestFn) (Ψ : T.domain) (Ψ' : T'.domain), (Ψ' : H') = L Ψ →
    (T'.field f Ψ' : H') = L (T.field f Ψ)
structure IsTheoryOf (T : WightmanTheory.HermitianScalarTheory H) (S : ConfigSpace.FlatSequence) :
    Prop where
  schwinger : T.IsSchwingerSequence S
  covariant : T.IsPoincareCovariant
  spectrum : T.SpectrumCondition
  localField : T.IsLocalField
end Theories
section Subspace
variable (S : ConfigSpace.FlatSequence)
instance instCompletePositiveTimeSubspace : CompleteSpace S.positiveTimeSubspace :=
  Submodule.topologicalClosure.completeSpace _
def IsVacuumClass (χ : S.HilbertCompletion) : Prop :=
  ∃ Φ : ConfigSpace.AdmissibleSeq, ConfigSpace.seqValues Φ = ConfigSpace.vacuumSeq ∧
    χ = S.admClass Φ
def HamiltonianSemigroupRestricts
    (T : WightmanTheory.HermitianScalarTheory S.positiveTimeSubspace) : Prop :=
  ∃ F : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp S.positiveTimeSubspace,
    T.IsEnergyMomentumMeasure F ∧ ∀ t : ℝ, 0 ≤ t → ∀ χ : S.positiveTimeSubspace,
      ((WightmanTheory.HermitianScalarTheory.hamiltonianSemigroup F t χ : S.positiveTimeSubspace) :
        S.HilbertCompletion) = S.timeShiftOp t χ
def succMember (Φ : ConfigSpace.AdmissibleSeq) (q : ℕ) : TestSpaces.PointTuple (q + 1) → ℂ :=
  TestSpaces.succComponent (ConfigSpace.gradedMembers (ConfigSpace.seqValues Φ)) q
def zerothScalar (Φ : ConfigSpace.AdmissibleSeq) : ℂ :=
  WightmanReconstruction.scalarOfOrderZero (ConfigSpace.gradedMembers (ConfigSpace.seqValues Φ) 0)
end Subspace
section Form
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp K) (Ω : K)
  (A : ℝ → OneLoopNotation.BddOp K)
def wickStateAt (q : ℕ) (x : TestSpaces.PointTuple (q + 1)) : K :=
  FieldForms.stateVector E Ω A (q + 1)
    (MinkowskiSpace.wickMapTuple (MinkowskiSpace.tupleToComplex x))
def IsSmoothPositiveTimeSeq (Φ : ConfigSpace.AdmissibleSeq) : Prop :=
  ∀ q : ℕ, succMember Φ q ∈
    TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes (q + 1))
def smoothSeqState (Φ : ConfigSpace.AdmissibleSeq) : K :=
  zerothScalar Φ • Ω + ∑ᶠ q : ℕ, ProjectionMeasures.weakInt (tsupport (succMember Φ q))
    (wickStateAt E Ω A q) (succMember Φ q)
structure IsReconstructionIsometry (S : ConfigSpace.FlatSequence)
    (J : FormsOperators.UnitaryMap S.positiveTimeSubspace (FieldFormHilbert.tensorHilbert E Ω A)) :
    Prop where
  map_vacuumClass : ∀ χ : S.positiveTimeSubspace,
    IsVacuumClass S χ → ((J χ : FieldFormHilbert.tensorHilbert E Ω A) : K) = Ω
  map_timeShift : ∀ t : ℝ, 0 ≤ t → ∀ χ : S.positiveTimeSubspace,
    ∃ h : S.timeShiftOp t χ ∈ S.positiveTimeSubspace,
      ((J ⟨_, h⟩ : FieldFormHilbert.tensorHilbert E Ω A) : K) =
        FieldForms.spectralTranslation E (FieldForms.imagTimeShift t)
          (J χ : FieldFormHilbert.tensorHilbert E Ω A)
  map_admClass : ∀ Φ : ConfigSpace.AdmissibleSeq, IsSmoothPositiveTimeSeq Φ →
    (∀ q : ℕ, ProjectionMeasures.HasWeakIntegrandData (tsupport (succMember Φ q))
      (wickStateAt E Ω A q) (succMember Φ q)) ∧
    ∃ h : S.admClass Φ ∈ S.positiveTimeSubspace,
      ((J ⟨_, h⟩ : FieldFormHilbert.tensorHilbert E Ω A) : K) =
        smoothSeqState E Ω A Φ
end Form
end YangMills.Construction.FormReconstruction
end

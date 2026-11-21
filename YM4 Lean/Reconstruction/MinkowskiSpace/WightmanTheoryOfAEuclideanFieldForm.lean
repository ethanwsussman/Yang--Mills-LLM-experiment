import Reconstruction.MinkowskiSpace.HilbertSpaceOfTheTensorsOfABoundedFieldForm
import Reconstruction.MinkowskiSpace.SchwingerFunctionsOfAEuclideanFieldForm
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.FieldFormHilbert
section Form
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp K) (Ω : K)
  (A : ℝ → OneLoopNotation.BddOp K)
structure IsFormTheory
    (T : WightmanTheory.HermitianScalarTheory (tensorHilbert E Ω A)) : Prop where
  rep_eq : ∀ g, IsPoincareOp E Ω A g (T.rep g)
  vacuum_eq : (T.vacuum : K) = Ω
  domain_eq : T.domain = tensorDomainIn E Ω A
  field_eq : ∀ f, IsFieldOp E Ω A T.domain f (T.field f)
structure FormTheoryProperties
    (T : WightmanTheory.HermitianScalarTheory (tensorHilbert E Ω A)) : Prop where
  isFormTheory : IsFormTheory E Ω A T
  covariant : T.IsPoincareCovariant
  spectrum : T.SpectrumCondition
  local_field : T.IsLocalField
  rep_translation : ∀ (a : MinkowskiSpace.RealVec4) (χ : tensorHilbert E Ω A),
    ((T.rep (WightmanTheory.pureTranslation a) χ : tensorHilbert E Ω A) : K) =
      FieldForms.spectralTranslation E (MinkowskiSpace.toComplex a) χ
  exists_energyMomentum : ∃ F : ProjectionMeasures.FourBorelSet →
      OneLoopNotation.BddOp (tensorHilbert E Ω A),
    IsMeasureRestriction E Ω A F ∧ T.IsEnergyMomentumMeasure F ∧
      ∀ t : ℝ, 0 ≤ t → ∀ χ : tensorHilbert E Ω A,
        ((WightmanTheory.HermitianScalarTheory.hamiltonianSemigroup F t χ :
            tensorHilbert E Ω A) : K) =
          FieldForms.spectralTranslation E (FieldForms.imagTimeShift t) χ
  wightmanFn_eq : ∀ (m : ℕ) (f : Fin (m + 1) → WightmanTheory.TestFn),
    T.wightmanFn f =
      RealPointVectors.wightmanFunctional E Ω A (m + 1)
        (RealPointVectors.tensorVal fun i => (f i).1)
  schwinger : ∀ S : ConfigSpace.FlatSequence,
    ConfigSpace.IsCLMSequence S →
    (∀ (m : ℕ) (φ : TestSpaces.PointTuple (m + 1) → ℂ),
      φ ∈ (TestSpaces.smoothCompactSupp (TestSpaces.distinctLocus (m + 1)) :
        Set (TestSpaces.PointTuple (m + 1) → ℂ)) →
      ∀ h : φ ∈ ConfigSpace.schwartzFlatOffDiagonal (m + 1),
        S.atSucc m ⟨φ, h⟩ = FieldForms.integralSchwinger E Ω A m φ) →
    T.IsSchwingerSequence S ∧
      ∀ m : ℕ, ∃ (q : ℕ) (c : ℝ),
        WightmanTheory.IsAnalyticContinuationData T S m
          (FieldForms.vacuumExpectation E Ω A (m + 1)) q c (FieldForms.schwinger E Ω A m)
  uniqueVacuum : (∀ χ : K,
      (∀ t : ℝ, 0 ≤ t → FieldForms.spectralTranslation E (FieldForms.imagTimeShift t) χ = χ) →
      ∃ c : ℂ, χ = c • Ω) → T.UniqueVacuum
structure WightmanReconstruction : Prop where
  poincareAct_mem : ∀ (g : WightmanTheory.PoincareElt) (f : WightmanTheory.TestFn),
    poincareActR4 g f.1 ∈ WightmanTheory.schwartzR4
  existsUnique_field : ∀ f : WightmanTheory.TestFn, ∃! L : tensorDomainIn E Ω A →ₗ[ℂ]
    tensorDomainIn E Ω A, IsFieldOp E Ω A (tensorDomainIn E Ω A) f L
  existsUnique_rep : ∀ g : WightmanTheory.PoincareElt,
    ∃! U : FormsOperators.UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A),
      IsPoincareOp E Ω A g U
  exists_theory : ∃ T : WightmanTheory.HermitianScalarTheory (tensorHilbert E Ω A),
    FormTheoryProperties E Ω A T
  separable : TopologicalSpace.SeparableSpace (tensorHilbert E Ω A)
end Form
def WightmanFromEuclideanForm : Prop :=
  ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp K) (Ω : K)
    (A : ℝ → OneLoopNotation.BddOp K) (p C : ℝ),
    FieldForms.IsBoundedFieldForm E Ω A p C → FieldForms.IsEuclidean E Ω A →
      WightmanReconstruction E Ω A
end YangMills.Construction.FieldFormHilbert

import Reconstruction.MinkowskiSpace.VectorsAtRealPointsDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.RealPointVectors
section States
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (vac : H)
  (T : ℝ → OneLoopNotation.BddOp H)
structure BoundaryVectorFacts (p c : ℝ) : Prop where
  hasWeakIntegrandData : ∀ (m : ℕ) (f : TestSpaces.PointTuple (m + 1) → ℂ),
    f ∈ TestSpaces.schwartzSet (m + 1) →
    ∀ Y ∈ futureConeTuples (m + 1),
      ProjectionMeasures.HasWeakIntegrandData Set.univ (shiftedStateVector P vac T Y) f
  isBoundaryLimit_testState : ∀ (m : ℕ) (f : TestSpaces.PointTuple (m + 1) → ℂ),
    f ∈ TestSpaces.schwartzSet (m + 1) →
    IsBoundaryLimit P vac T f (testState P vac T (m + 1) f)
  eq_testState_of_isBoundaryLimit : ∀ (m : ℕ) (f : TestSpaces.PointTuple (m + 1) → ℂ),
    f ∈ TestSpaces.schwartzSet (m + 1) →
    ∀ v : H, IsBoundaryLimit P vac T f v → v = testState P vac T (m + 1) f
  testState_linear : ∀ (m : ℕ) (f g : TestSpaces.PointTuple (m + 1) → ℂ),
    f ∈ TestSpaces.schwartzSet (m + 1) → g ∈ TestSpaces.schwartzSet (m + 1) → ∀ a b : ℂ,
      testState P vac T (m + 1) (a • f + b • g) =
        a • testState P vac T (m + 1) f + b • testState P vac T (m + 1) g
  norm_testState_le : ∀ (m : ℕ) (f : TestSpaces.PointTuple (m + 1) → ℂ),
    f ∈ TestSpaces.schwartzSet (m + 1) →
    ‖testState P vac T (m + 1) f‖ ≤ 4 * ((2 : ℝ) ^ p * c) ^ (m + 1) * fieldFormNorm p f
  wightmanFunctional_zero : ∀ a : ℂ, wightmanFunctional P vac T 0 a = a
  integrable_vacuumIntegrand : ∀ (m : ℕ) (f : TestSpaces.PointTuple (m + 1) → ℂ),
    f ∈ TestSpaces.schwartzSet (m + 1) →
    ∀ Y ∈ futureConeTuples m, Integrable (vacuumIntegrand P vac T f Y)
  exists_continuousOn_extension : ∀ (m : ℕ) (f : TestSpaces.PointTuple (m + 1) → ℂ),
    f ∈ TestSpaces.schwartzSet (m + 1) →
    ∃ F : TestSpaces.PointTuple m → ℂ, ContinuousOn F (closedFutureConeTuples m) ∧
      (∀ Y ∈ futureConeTuples m, F Y = ∫ x, vacuumIntegrand P vac T f Y x) ∧
      F 0 = wightmanFunctional P vac T (m + 1) f
  norm_wightmanFunctional_le : ∀ (m : ℕ) (f : TestSpaces.PointTuple (m + 1) → ℂ),
    f ∈ TestSpaces.schwartzSet (m + 1) →
    ‖wightmanFunctional P vac T (m + 1) f‖ ≤ 4 * ((2 : ℝ) ^ p * c) ^ (m + 1) * fieldFormNorm p f
  starVal_mem : ∀ (m : ℕ) (g : Motions.TensorVal ℂ m),
    g ∈ WightmanReconstruction.schwartzOfOrder m →
    starVal g ∈ WightmanReconstruction.schwartzOfOrder m
  tensorVal_starVal_mem : ∀ (k m : ℕ) (g : Motions.TensorVal ℂ k) (f : Motions.TensorVal ℂ m),
    g ∈ WightmanReconstruction.schwartzOfOrder k → f ∈ WightmanReconstruction.schwartzOfOrder m →
      HyperplaneReflection.tensorVal (starVal g) f ∈ WightmanReconstruction.schwartzOfOrder (k + m)
  inner_testState_eq : ∀ (k m : ℕ) (g : Motions.TensorVal ℂ k) (f : Motions.TensorVal ℂ m),
    g ∈ WightmanReconstruction.schwartzOfOrder k → f ∈ WightmanReconstruction.schwartzOfOrder m →
      ⟪testState P vac T k g, testState P vac T m f⟫_ℂ =
        wightmanFunctional P vac T (k + m) (HyperplaneReflection.tensorVal (starVal g) f)
  translateVal_mem : ∀ (m : ℕ) (f : Motions.TensorVal ℂ m) (a : MinkowskiSpace.RealVec4),
    f ∈ WightmanReconstruction.schwartzOfOrder m →
    translateVal a f ∈ WightmanReconstruction.schwartzOfOrder m
  spectralTranslation_testState : ∀ (m : ℕ) (f : Motions.TensorVal ℂ m)
    (a : MinkowskiSpace.RealVec4), f ∈ WightmanReconstruction.schwartzOfOrder m →
    FieldForms.spectralTranslation P (MinkowskiSpace.toComplex a) (testState P vac T m f) =
      testState P vac T m (translateVal a f)
  tensorVal_mem : ∀ (m : ℕ) (u : Fin m → (Fin 4 → ℝ) → ℂ),
    (∀ i, u i ∈ WightmanTheory.schwartzR4) → tensorVal u ∈ WightmanReconstruction.schwartzOfOrder m
  fieldFormNorm_tensorProd_le : ∀ (m : ℕ) (u : Fin (m + 1) → (Fin 4 → ℝ) → ℂ),
    (∀ i, u i ∈ WightmanTheory.schwartzR4) →
      fieldFormNorm p (TestSpaces.tensorProd u) ≤
        ((m + 1 : ℕ) : ℝ) ^ (2 * (FieldForms.boundOrder p (m + 1)).toNat) *
          ∏ i, maxPartialL1 (FieldForms.boundOrder p (m + 1)).toNat (u i)
  maxPartialL1_le : ∀ (k : ℕ) (u : (Fin 4 → ℝ) → ℂ),
    u ∈ WightmanTheory.schwartzR4 →
      ENNReal.ofReal (maxPartialL1 k u) ≤
        ENNReal.ofReal (Real.pi ^ 2) * WightmanTheory.schwartzNorm (k + 6) u
  tensorDomainClosure_eq : tensorDomainClosure P vac T =
    SesquilinearForms.closedLinSpan (euclideanStates P vac T)
  testState_mem : ∀ (m : ℕ) (f : Motions.TensorVal ℂ m),
    f ∈ WightmanReconstruction.schwartzOfOrder m →
    testState P vac T m f ∈ tensorDomainClosure P vac T
  stateVector_mem : ∀ (m : ℕ) (z : Fin (m + 1) → MinkowskiSpace.ComplexVec4),
    (∀ i, MinkowskiSpace.diffCoords z i ∈ MinkowskiSpace.futureTube) →
    FieldForms.stateVector P vac T (m + 1) z ∈ tensorDomainClosure P vac T
  spectralTranslation_mem : ∀ w : MinkowskiSpace.ComplexVec4,
    MinkowskiSpace.imPart w ∈ MinkowskiSpace.closedFutureCone →
    ∀ v ∈ tensorDomainClosure P vac T,
      FieldForms.spectralTranslation P w v ∈ tensorDomainClosure P vac T
  proj_mem : ∀ B : ProjectionMeasures.FourBorelSet, ∀ v ∈ tensorDomainClosure P vac T,
    P B v ∈ tensorDomainClosure P vac T
end States
def BoundaryVectorsStatement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (vac : H)
    (T : ℝ → OneLoopNotation.BddOp H) (p c : ℝ),
    FieldForms.IsBoundedFieldForm P vac T p c → BoundaryVectorFacts P vac T p c
end YangMills.Construction.RealPointVectors

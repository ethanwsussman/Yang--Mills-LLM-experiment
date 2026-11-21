import Reconstruction.MinkowskiSpace.WightmanTheoriesOfOneHermitianScalarField
import YangMills.Construction.Continuum.ReflectionOfTestFunctionsInAHyperplane
import YangMills.Construction.Continuum.SchwartzTestsAndMollifiers
import Reconstruction.MinkowskiSpace.FunctionsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.RealPointVectors
def timeWeightedDeriv {m : ℕ} (φ : TestSpaces.PointTuple m → ℂ) : TestSpaces.PointTuple m → ℂ :=
  fun x => ∑ i : Fin m, (((i : ℕ) + 1 : ℕ) : ℂ) * TestSpaces.coordDeriv i 0 φ x
def maxTimeDerivL1 {m : ℕ} (k : ℕ) (φ : TestSpaces.PointTuple m → ℂ) : ℝ :=
  (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one
    fun j => WightmanReconstruction.lOneNorm (timeWeightedDeriv^[j] φ)
def fieldFormNorm (p : ℝ) {m : ℕ} (φ : TestSpaces.PointTuple m → ℂ) : ℝ :=
  maxTimeDerivL1 (FieldForms.boundOrder p m).toNat φ
def maxPartialL1 (k : ℕ) (h : (Fin 4 → ℝ) → ℂ) : ℝ :=
  (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one
    fun j => WightmanReconstruction.lOneNorm ((TestFunctions.partialDerivR4 0)^[j] h)
def futureConeTuples (m : ℕ) : Set (TestSpaces.PointTuple m) :=
  {Y | ∀ i, Y i ∈ MinkowskiSpace.futureCone}
def closedFutureConeTuples (m : ℕ) : Set (TestSpaces.PointTuple m) :=
  {Y | ∀ i, Y i ∈ MinkowskiSpace.closedFutureCone}
def starFun {m : ℕ} (ψ : TestSpaces.PointTuple m → ℂ) : TestSpaces.PointTuple m → ℂ :=
  fun y => conj (ψ fun i => y (Fin.rev i))
def starScalar (c : ℂ) : ℂ := conj c
def starVal : {m : ℕ} → Motions.TensorVal ℂ m → Motions.TensorVal ℂ m
  | 0, c => starScalar c
  | _ + 1, ψ => starFun ψ
def translateVal (a : MinkowskiSpace.RealVec4) :
    {m : ℕ} → Motions.TensorVal ℂ m → Motions.TensorVal ℂ m
  | 0, c => MinkowskiSpace.poincareScalar (a, 1) c
  | _ + 1, φ => MinkowskiSpace.poincarePullback (a, 1) φ
def tensorVal {m : ℕ} (f : Fin m → (Fin 4 → ℝ) → ℂ) : Motions.TensorVal ℂ m :=
  HyperplaneReflection.funToVal (TestSpaces.tensorProd f)
def diffCoords {m : ℕ} (φ : TestSpaces.PointTuple (m + 1) → ℂ) :
    TestSpaces.PointTuple (m + 1) → ℂ :=
  fun x => φ (MinkowskiSpace.cumulativeSums x)
section States
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (Ω : H)
  (A : ℝ → OneLoopNotation.BddOp H)
def tubeMatrixElement (χ : H) {m : ℕ} (ζ : Fin (m + 1) → MinkowskiSpace.ComplexVec4) : ℂ :=
  ⟪χ, FieldForms.fieldProduct E A (m + 1)
    (FieldForms.snocPoint ζ (FieldForms.imagTimeShift 1)) Ω⟫_ℂ
def shiftedStateVector {m : ℕ} (Y x : TestSpaces.PointTuple (m + 1)) : H :=
  FieldForms.stateVector E Ω A (m + 1)
    (MinkowskiSpace.tupleToComplex x +
      Complex.I • MinkowskiSpace.tupleToComplex (MinkowskiSpace.cumulativeSums Y))
def smearedState {m : ℕ} (Y : TestSpaces.PointTuple (m + 1))
    (φ : TestSpaces.PointTuple (m + 1) → ℂ) : H :=
  ProjectionMeasures.weakInt Set.univ (shiftedStateVector E Ω A Y) φ
def IsBoundaryLimit {m : ℕ} (φ : TestSpaces.PointTuple (m + 1) → ℂ) (v : H) : Prop :=
  ∀ χ : H, Tendsto (fun Y => ⟪χ, smearedState E Ω A Y φ⟫_ℂ)
    (𝓝[futureConeTuples (m + 1)] 0) (𝓝 ⟪χ, v⟫_ℂ)
def testState : (m : ℕ) → Motions.TensorVal ℂ m → H
  | 0, c => WightmanReconstruction.scalarOfOrderZero c • Ω
  | _ + 1, φ => Classical.epsilon (IsBoundaryLimit E Ω A φ)
def wightmanFunctional (m : ℕ) (φ : Motions.TensorVal ℂ m) : ℂ :=
  ⟪Ω, testState E Ω A m φ⟫_ℂ
def vacuumIntegrand {m : ℕ} (φ : TestSpaces.PointTuple (m + 1) → ℂ)
    (Y' : TestSpaces.PointTuple m) (x : TestSpaces.PointTuple (m + 1)) : ℂ :=
  FieldForms.vacuumExpectation E Ω A (m + 1)
    (MinkowskiSpace.successiveDiffs (MinkowskiSpace.tupleToComplex x) +
      Complex.I • MinkowskiSpace.tupleToComplex Y') * φ x
def tensorStates : Set H :=
  {v | ∃ (m : ℕ) (f : Fin m → (Fin 4 → ℝ) → ℂ), (∀ i, f i ∈ WightmanTheory.schwartzR4) ∧
    v = testState E Ω A m (tensorVal f)}
def tensorDomain : Submodule ℂ H := Submodule.span ℂ (tensorStates E Ω A)
def tensorDomainClosure : Set H :=
  ComplexHilbert.seqClosureOf (tensorDomain E Ω A : Set H)
def euclideanStates : Set H :=
  {v | ∃ (m : ℕ), ∃ x ∈ TestSpaces.increasingPositiveTimes m,
    v = FieldForms.stateVector E Ω A m
      (MinkowskiSpace.wickMapTuple (MinkowskiSpace.tupleToComplex x))}
end States
end YangMills.Construction.RealPointVectors

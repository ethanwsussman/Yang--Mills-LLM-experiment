import YangMills.Construction.PeriodicLattice.TriplesOnFiniteBondSets
import YangMills.Construction.Towers.AveragingMapNearTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Tower
section FiniteSide
variable {L n k j : ℕ}
def smallComplexFields (L n k j : ℕ) : Set (Edge L n k j → Matrices.ComplexMatrix2) :=
  {V | V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup ∧
    ∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L}
def complexSmoothingDeriv (V B : Edge L n k j → Matrices.ComplexMatrix2) :
    Edge L n k (j + 1) → Matrices.ComplexMatrix2 :=
  holLeftDifferential (PeriodicLattice.complexBlockAverageStep j) V B
def contourLogDrift (V B : Edge L n k j → Matrices.ComplexMatrix2) :
    Vertex L n k (j + 1) → Matrices.ComplexMatrix2 :=
  fun y => PeriodicLattice.inverseFourthPowerWeight L •
    ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
        (PeriodicLattice.complexMeanContourHolonomy V y x) B
def adjointCubeAverage (V : Edge L n k j → Matrices.ComplexMatrix2)
    (l : Vertex L n k j → Matrices.ComplexMatrix2) :
    Vertex L n k (j + 1) → Matrices.ComplexMatrix2 :=
  fun y => PeriodicLattice.inverseFourthPowerWeight L •
    ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      Matrices.ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy V y x) (l x)
def covariantSmoothingDeriv (V B : Edge L n k j → Matrices.ComplexMatrix2) :
    Edge L n k (j + 1) → Matrices.ComplexMatrix2 :=
  complexSmoothingDeriv V B +
    covDiff (PeriodicLattice.complexBlockAverageStep j V) (contourLogDrift V B)
def smallIterateFields (L n k : ℕ) : Set (Edge L n k 0 → Matrices.ComplexMatrix2) :=
  {U | U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup ∧
    ∀ j < k, PeriodicLattice.complexBlockFieldAtLevel j U ∈ smallComplexFields L n k j}
def complexIterDeriv (L n k j : ℕ) (U B : Edge L n k 0 → Matrices.ComplexMatrix2) :
    Edge L n k j → Matrices.ComplexMatrix2 :=
  holLeftDifferential (PeriodicLattice.complexBlockFieldAtLevel j) U B
def iterCovariantDeriv (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    (j : ℕ) → (Edge L n k 0 → Matrices.ComplexMatrix2) → Edge L n k j → Matrices.ComplexMatrix2
  | 0, B => B
  | j + 1, B => covariantSmoothingDeriv (PeriodicLattice.complexBlockFieldAtLevel j U)
      (iterCovariantDeriv L n k U j B)
def iterAdjointCubeAverage (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    (j : ℕ) → (Vertex L n k 0 → Matrices.ComplexMatrix2) → Vertex L n k j → Matrices.ComplexMatrix2
  | 0, l => l
  | j + 1, l => adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j U)
      (iterAdjointCubeAverage L n k U j l)
def iterContourLogDrift (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    (j : ℕ) → (Edge L n k 0 → Matrices.ComplexMatrix2) → Vertex L n k j → Matrices.ComplexMatrix2
  | 0, _ => 0
  | j + 1, B =>
      adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j U)
          (iterContourLogDrift L n k U j B) +
        contourLogDrift (PeriodicLattice.complexBlockFieldAtLevel j U)
          (complexIterDeriv L n k j U B)
end FiniteSide
namespace FullSpace
section Tower
variable {L k j : ℕ}
def smallComplexFields (L k j : ℕ) : Set (Edge L k j → Matrices.ComplexMatrix2) :=
  {V | V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup ∧
    ∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L}
def complexSmoothingDeriv (V B : Edge L k j → Matrices.ComplexMatrix2) :
    Edge L k (j + 1) → Matrices.ComplexMatrix2 :=
  holLeftDifferential OneLoop.pauliBasis (smallComplexFields L k j)
    (smoothingMap L k j) V B
def contourLogDrift (V B : Edge L k j → Matrices.ComplexMatrix2) :
    Vertex L k (j + 1) → Matrices.ComplexMatrix2 :=
  fun y => PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ cubeVertices L (meshAt L k j) y,
    logDirectionalDeriv ℂ (fun X => complexContourMean L (expTwist X V) y x)
      (complexContourMean L V y x) B
def adjointCubeAverage (V : Edge L k j → Matrices.ComplexMatrix2)
    (l : Vertex L k j → Matrices.ComplexMatrix2) :
    Vertex L k (j + 1) → Matrices.ComplexMatrix2 :=
  fun y => PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ cubeVertices L (meshAt L k j) y,
    Matrices.ComplexMatrix2.conjugateBy (complexContourMean L V y x) (l x)
def covariantSmoothingDeriv (V B : Edge L k j → Matrices.ComplexMatrix2) :
    Edge L k (j + 1) → Matrices.ComplexMatrix2 :=
  complexSmoothingDeriv V B + covDiff (smoothingMap L k j V) (contourLogDrift V B)
def complexIter (L k : ℕ) :
    (j : ℕ) → (Edge L k 0 → Matrices.ComplexMatrix2) → Edge L k j → Matrices.ComplexMatrix2
  | 0, U => U
  | j + 1, U => smoothingMap L k j (complexIter L k j U)
def smallIterateFields (L k : ℕ) : Set (Edge L k 0 → Matrices.ComplexMatrix2) :=
  {U | U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup ∧
    ∀ j < k, complexIter L k j U ∈ smallComplexFields L k j}
def complexIterDeriv (L k j : ℕ) (U B : Edge L k 0 → Matrices.ComplexMatrix2) :
    Edge L k j → Matrices.ComplexMatrix2 :=
  holLeftDifferential OneLoop.pauliBasis (smallIterateFields L k)
    (complexIter L k j) U B
def iterCovariantDeriv (L k : ℕ) (U : Edge L k 0 → Matrices.ComplexMatrix2) :
    (j : ℕ) → (Edge L k 0 → Matrices.ComplexMatrix2) → Edge L k j → Matrices.ComplexMatrix2
  | 0, B => B
  | j + 1, B => covariantSmoothingDeriv (complexIter L k j U)
      (iterCovariantDeriv L k U j B)
def iterAdjointCubeAverage (L k : ℕ) (U : Edge L k 0 → Matrices.ComplexMatrix2) :
    (j : ℕ) → (Vertex L k 0 → Matrices.ComplexMatrix2) → Vertex L k j → Matrices.ComplexMatrix2
  | 0, l => l
  | j + 1, l => adjointCubeAverage (complexIter L k j U) (iterAdjointCubeAverage L k U j l)
def iterContourLogDrift (L k : ℕ) (U : Edge L k 0 → Matrices.ComplexMatrix2) :
    (j : ℕ) → (Edge L k 0 → Matrices.ComplexMatrix2) → Vertex L k j → Matrices.ComplexMatrix2
  | 0, _ => 0
  | j + 1, B =>
      adjointCubeAverage (complexIter L k j U) (iterContourLogDrift L k U j B) +
        contourLogDrift (complexIter L k j U) (complexIterDeriv L k j U B)
end Tower
end FullSpace
end Tower
end YangMills.Construction
end

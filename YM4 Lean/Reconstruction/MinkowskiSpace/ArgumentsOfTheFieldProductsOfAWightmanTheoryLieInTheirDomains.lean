import YangMills.Construction.ClusterExpansion.PolymerGraphs
import Reconstruction.MinkowskiSpace.WightmanTheoriesOfOneHermitianScalarField
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace WightmanTheory
namespace DomainFacts
def PoincareMulMem : Prop :=
  ∀ g g' : PoincareElt,
    MinkowskiSpace.poincareMul g.1 g'.1 ∈ MinkowskiSpace.restrictedPoincare
def LinearCombinationMemSchwartz : Prop :=
  ∀ (a b : ℂ) (f f' : TestFn), a • f.1 + b • f'.1 ∈ schwartzR4
def BoundaryApproachMemTube : Prop :=
  ∀ (m : ℕ) (x : TestSpaces.PointTuple (m + 1)) (ε : ℝ), 0 < ε →
    boundaryApproach x ε ∈ tubeTuples m
def WickDiffsMemTube : Prop :=
  ∀ (m : ℕ) (y : TestSpaces.PointTuple (m + 1)), y ∈ TestSpaces.increasingTimes (m + 1) →
    wickDiffs y ∈ tubeTuples m
def SmoothCompactSuppSubsetFlatSchwartz : Prop :=
  ∀ (m : ℕ) (φ : TestSpaces.PointTuple (m + 1) → ℂ),
    φ ∈ TestSpaces.smoothCompactSupp (TestSpaces.distinctLocus (m + 1)) →
      φ ∈ ConfigSpace.schwartzFlatOffDiagonal (m + 1)
def PartitionBlockCardLt : Prop :=
  ∀ n : ℕ, ∀ η ∈ (ClusterExpansion.SymGraph.partitions (Fin n)).erase {Finset.univ},
    ∀ J ∈ η, J.card < n
def HamiltonianSemigroupHasWeakIntegrals : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    ProjectionMeasures.IsBddMeasurableFun
        (MinkowskiSpace.closedFutureCone.indicator fun p => Complex.exp (-((t * p 0 : ℝ) : ℂ))) ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H),
      ProjectionMeasures.IsPVM E →
      ProjectionMeasures.IsSupportedOn E closedFutureConeBorel →
        PVMCalculus.HasWeakIntegrals E
          (MinkowskiSpace.closedFutureCone.indicator fun p => Complex.exp (-((t * p 0 : ℝ) : ℂ)))
          (HermitianScalarTheory.hamiltonianSemigroup E t)
def SchwartzNormLtTop : Prop :=
  ∀ (f : TestFn) (k : ℕ), 0 < k → schwartzNorm k f.1 < ⊤
def MinkowskiPhaseHasWeakIntegrals : Prop :=
  ∀ a : MinkowskiSpace.RealVec4, ProjectionMeasures.IsBddMeasurableFun (minkowskiPhase a) ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H),
      ProjectionMeasures.IsPVM E →
      ProjectionMeasures.IsSupportedOn E closedFutureConeBorel →
        PVMCalculus.HasWeakIntegrals E (minkowskiPhase a)
          (PVMCalculus.pvmIntegral E (minkowskiPhase a))
def Statement : Prop :=
  PoincareMulMem ∧ LinearCombinationMemSchwartz ∧
    BoundaryApproachMemTube ∧ WickDiffsMemTube ∧
    SmoothCompactSuppSubsetFlatSchwartz ∧
    PartitionBlockCardLt ∧
    HamiltonianSemigroupHasWeakIntegrals ∧ SchwartzNormLtTop ∧
    MinkowskiPhaseHasWeakIntegrals
end DomainFacts
end WightmanTheory
end YangMills.Construction
end

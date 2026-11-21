import YangMills.Construction.Lattice.ConnectedFunctionsAtArbitraryArguments
import YangMills.Construction.LimitsOfLatticeFamilies.BoundFunctionsHierarchiesAndLimitData
import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror (Ambient)
open LatticeLimits (SeparationBound HierarchySequence)
open AmbientPoints
open scoped ENNReal MeasureTheory Topology
namespace TorusFunctionals
def singletonFreePartitions {α : Type*} [DecidableEq α] (I : Finset α) :
    Finset (SetPartition.Partitions I) :=
  Finset.univ.filter fun π => ∀ J ∈ π.parts, J.card ≠ 1
namespace Periodic
variable (D : ConnectedFunctions.CouplingData)
def centredObs (f : D.Torus → ℝ) (U : D.Config) : ℝ :=
  PeriodicLattice.smearedObservable f U -
    PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling fun V => PeriodicLattice.smearedObservable f V
def centredProductExpectation {q : ℕ} (h : Fin q → D.Torus → ℝ) : ℝ :=
  PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling fun U => ∏ i, centredObs D (h i) U
end Periodic
def toModelSpace : Ambient → LatticeLimits.ModelSpace
  | .torus => .torus
  | .euclidean => .euclidean
variable (s : Conventions.StandingParameters) (E : Ambient)
def liftFun : (E : Ambient) → (Pt s E → ℝ) → (toModelSpace E).Carrier s → ℝ
  | .torus, f => f
  | .euclidean, f => f
def sharpNormAt (M : ℕ) (f : Pt s E → ℝ) : ℝ :=
  LatticeLimits.ModelSpace.sharpNormOfScale s M (toModelSpace E) (liftFun s E f)
variable (M : ℕ) (C : SeparationBound)
end TorusFunctionals
end YangMills.Construction

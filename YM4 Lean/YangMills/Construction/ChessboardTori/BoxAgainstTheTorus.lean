import YangMills.Construction.ChessboardTori.BoxWithAnOuterConfiguration
import YangMills.Construction.ChessboardTori.NamesOfAMirrorGridOnATorus
import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import YangMills.Construction.Constants.SurfaceTermNumbers
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open InfiniteLattice
open scoped ComplexOrder
noncomputable section
namespace ChessboardTori
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def openBlockLinks : Finset D.Link := D.boxLinks g.fundamentalBlockInterior
def facesLeavingInterior : Set D.Plaquette :=
  {p | (∃ e ∈ p.edges, e ∈ g.openBlockLinks) ∧
    ∃ v ∈ p.cornerSet, (v : AmbientSpace) ∉ g.fundamentalBlockInterior}
def facesCrossingBoundary : Set (PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ)) :=
  {p | ∃ e ∈ WilsonOperator.periodicEdgeList p, ∀ e' ∈ g.openBlockLinks, D.projLink e' ≠ e}
def boundaryFaceCount : ℕ :=
  g.facesCrossingBoundary.ncard + g.facesLeavingInterior.ncard
end ReflectionGrid
def BoxTorusComparison.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.IsCoarse →
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    (g.boundaryFaceCount : ℝ) ≤
        (Constants.SurfaceTerms.plaquetteCount : ℝ) *
          (PeriodicLattice.torusSide D.L D.m / D.mesh) ^ 3 ∧
      ∀ A : D.GaugeField → ℂ, IsBoundedObservable A →
        IsRegionMeasurable g.fundamentalBlockInterior A →
        (∀ U, 0 ≤ A U) → ∀ ξ : D.GaugeField,
          D.wilsonKernelAt g.openBlockLinks (D.coe_boxLinks_subset_positive _) A ξ ≤
            (Real.exp (2 * D.β * (g.boundaryFaceCount : ℝ)) : ℂ) *
              PeriodicLattice.gibbsExpectation D.L D.m D.K D.β (D.liftedObservable A)
end ChessboardTori
end
end YangMills.Construction

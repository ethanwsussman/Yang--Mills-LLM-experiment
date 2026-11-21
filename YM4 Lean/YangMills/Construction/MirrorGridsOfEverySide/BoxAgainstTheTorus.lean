import YangMills.Construction.ChessboardTori.BoxWithAnOuterConfiguration
import YangMills.Construction.ChessboardTori.NamesOfAMirrorGridOnATorus
import YangMills.Construction.MirrorGridsOfEverySide.MirrorGridOrientationsAndReflectionProducts
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
open InfiniteLattice (AmbientSpace)
def cubeComparisonConstant : ℝ := 768
namespace GridSetup
variable (D : GridSetup)
def IsDualLatticePoint (c : AmbientSpace) : Prop :=
  ∀ μ, ∃ i : ℤ, c μ = D.mesh * ((i : ℝ) + 1 / 2)
def cornerCube (c : AmbientSpace) : Set AmbientSpace := InfiniteLattice.cube c D.side
def cornerCubeLinks (c : AmbientSpace) : Finset D.Link := D.boxLinks (D.cornerCube c)
theorem cornerCubeLinks_subset_positiveLinks (c : AmbientSpace) :
    (D.cornerCubeLinks c : Set D.Link) ⊆ InfiniteLattice.positiveLinkSet D.mesh :=
  D.coe_boxLinks_subset_positive _
end GridSetup
def CubeVersusTorus.Statement : Prop :=
  ∀ (D : GridSetup) (c : AmbientSpace), D.IsDualLatticePoint c →
    ((∀ x ∈ D.gridPoints, x ∉ frontier (D.cornerCube c)) ∧
      Set.BijOn D.proj ((D.gridPoints : Set AmbientSpace) ∩ D.cornerCube c)
        (PeriodicLattice.sublattice D.L D.m ((D.K : ℕ) : ℤ) : Set D.Torus) ∧
      Set.MapsTo D.projLink (D.cornerCubeLinks c : Set D.Link) {b | b.IsPositivelyOriented} ∧
      Set.InjOn D.projLink (D.cornerCubeLinks c : Set D.Link)) ∧
    (∀ P : D.GaugeField → ℂ, D.IsBoundedMeasurableInLinks (D.cornerCubeLinks c) P →
      (∀ U, 0 ≤ P U) → ∀ ξ : D.GaugeField,
        D.kernelIntegral (D.cornerCubeLinks_subset_positiveLinks c) P ξ ≤
          (Real.exp (cubeComparisonConstant * D.β * (D.side / D.mesh) ^ 3) : ℂ) *
            D.expect (D.liftedObservable P)) ∧
    (∀ ν : Measure D.GaugeField, InfiniteLattice.IsGibbs D.β ν →
      ∀ H : D.GaugeField → ℝ,
        D.IsBoundedMeasurableInLinks (D.cornerCubeLinks c) (fun U => (H U : ℂ)) →
        ∫ U, H U ∂ν ≤
          Real.log (D.expect ((fun U => Real.exp (H U)) ∘ D.liftField)) +
            cubeComparisonConstant * D.β * (D.side / D.mesh) ^ 3)
end YangMills.Construction.MirrorGridsAllSides
end

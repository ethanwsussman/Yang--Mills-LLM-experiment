import YangMills.Construction.ChessboardTori.BoxWithAnOuterConfiguration
import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.ChessboardTori
def BoxVersusTorusViaFreeBoundary.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.IsCoarse →
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    ∀ B ∈ g.blocks, ∀ F : D.GaugeField → ℂ, D.IsBoxLocalObservable B F → (∀ U, 0 ≤ F U) →
      ∀ η : D.GaugeField,
        (Real.exp (-2 * D.β * (D.boundaryPlaquetteCount B : ℝ)) : ℂ) * D.freeBoxPartition B F ≤
            D.boundaryConditionPartition B η F ∧
          D.boundaryConditionPartition B η F ≤ D.freeBoxPartition B F ∧
          (Real.exp (-2 * D.β * (D.torusBoundaryPlaquetteCount B : ℝ)) : ℂ) *
              D.freeBoxPartition B F ≤
            D.torusPartition F ∧
          D.torusPartition F ≤ D.freeBoxPartition B F ∧
          ((D.boundaryPlaquetteCount B + D.torusBoundaryPlaquetteCount B : ℕ) : ℝ) ≤
            (boxBoundaryConstant : ℝ) * (PeriodicLattice.torusSide D.L D.m / D.mesh) ^ 3 ∧
          D.wilsonKernelAt (D.boxLinks B) (D.coe_boxLinks_subset_positive B) F η ≤
            (Real.exp (2 * D.β *
                ((D.boundaryPlaquetteCount B + D.torusBoundaryPlaquetteCount B : ℕ) : ℝ)) : ℂ) *
              D.liftedExpectation F ∧
          (Real.exp (2 * D.β *
                ((D.boundaryPlaquetteCount B + D.torusBoundaryPlaquetteCount B : ℕ) : ℝ)) : ℂ) *
              D.liftedExpectation F ≤
            (Real.exp (2 * (boxBoundaryConstant : ℝ) * D.β *
                (PeriodicLattice.torusSide D.L D.m / D.mesh) ^ 3) : ℂ) * D.liftedExpectation F
end YangMills.Construction.ChessboardTori
end

import YangMills.Construction.ChessboardTori.BoxWithAnOuterConfiguration
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.ChessboardTori
def FreeBoxComparison.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.IsCoarse →
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    ∀ B ∈ g.blocks,
      0 < D.freeBoxPartition B (fun _ => 1) ∧
      ∀ Ψ : D.GaugeField → ℂ, D.IsBoxLocalObservable B Ψ → (∀ U, 0 ≤ Ψ U) →
        0 ≤ D.freeBoxPartition B Ψ ∧
        ∀ ξ : D.GaugeField,
          (Real.exp (-2 * D.β * (D.boundaryPlaquetteCount B : ℝ)) : ℂ) * D.freeBoxPartition B Ψ ≤
              D.boundaryConditionPartition B ξ Ψ ∧
            D.boundaryConditionPartition B ξ Ψ ≤ D.freeBoxPartition B Ψ
end YangMills.Construction.ChessboardTori
end

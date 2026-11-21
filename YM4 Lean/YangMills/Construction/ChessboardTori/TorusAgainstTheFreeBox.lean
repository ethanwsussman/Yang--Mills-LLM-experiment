import YangMills.Construction.ChessboardTori.BoxWithAnOuterConfiguration
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.ChessboardTori
def TorusVersusFreeBox.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.IsCoarse →
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    ∀ B ∈ g.blocks, ∀ Ψ : D.GaugeField → ℂ, D.IsBoxLocalObservable B Ψ → (∀ U, 0 ≤ Ψ U) →
      (Real.exp (-2 * D.β * (D.torusBoundaryPlaquetteCount B : ℝ)) : ℂ) * D.freeBoxPartition B Ψ ≤
          D.torusPartition Ψ ∧
        D.torusPartition Ψ ≤ D.freeBoxPartition B Ψ
end YangMills.Construction.ChessboardTori
end

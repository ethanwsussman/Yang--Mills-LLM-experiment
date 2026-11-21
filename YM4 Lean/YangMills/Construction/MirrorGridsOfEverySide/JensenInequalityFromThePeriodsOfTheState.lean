import YangMills.Construction.ChessboardTori.SidesCentresAndTheChessboardFunctional
import YangMills.Construction.MirrorGridsOfEverySide.BoxAgainstTheTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
def JensenBoundFromPeriods.Statement : Prop :=
  ∀ D : GridSetup,
    (∀ ν ∈ D.periodicGibbs, ∃ p : ℕ, D.IsPeriod ν p) ∧
    ∀ (ν : Measure D.GaugeField) (p : ℕ), InfiniteLattice.IsGibbs D.β ν →
      D.IsPeriod ν p →
      ∀ g : ChessboardTori.ReflectionGrid D, g.HasAdmissibleSide → ∀ S ∈ g.cellSet,
        ∀ f : D.GaugeField → ℝ,
          (fun U => (f U : ℂ)) ∈ ChessboardTori.ReflectionGrid.cellObservables (D := D) S →
          2 * g.cellSide ≤ D.side →
          ∫ U, f U ∂ν ≤
            Real.log (g.chessboardNormOfCell S fun U => (Real.exp (f U) : ℂ)) +
              cubeComparisonConstant * (2 * (p : ℝ)) ^ 4 * D.β * (g.cellSide / D.mesh) ^ 3 *
                (g.cellSide / D.side)
end YangMills.Construction.MirrorGridsAllSides
end

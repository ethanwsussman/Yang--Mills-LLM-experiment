import YangMills.Construction.ChessboardTori.LimitingChessboardSeminorm
import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import YangMills.Construction.Constants.SurfaceTermNumbers
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
def JensenChessboardBound.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.IsCoarse →
    ∀ ν : Measure D.GaugeField, InfiniteLattice.IsGibbs D.β ν →
      (∀ r : g.reflectionGroup, InfiniteLattice.IsSymmetricUnder ν (g.toLatticeSym r)) →
      ∀ H : D.GaugeField → ℝ,
        (fun U => (H U : ℂ)) ∈ ReflectionGrid.cellObservables (D := D) g.baseCell →
        (∀ n : ℕ+, 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L n →
          ∫ U, H U ∂ν ≤
            Real.log (g.normAtExponent n g.baseCell fun U => Complex.exp (H U)) +
              (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β * g.cellSide ^ 4 /
                (D.mesh ^ 3 * PeriodicLattice.torusSide D.L n)) ∧
        ∫ U, H U ∂ν ≤ Real.log (g.limChessboardNorm fun U => Complex.exp (H U))
end YangMills.Construction.ChessboardTori
end

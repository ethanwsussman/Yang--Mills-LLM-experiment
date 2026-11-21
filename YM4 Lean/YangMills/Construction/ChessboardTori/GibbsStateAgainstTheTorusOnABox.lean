import YangMills.Construction.ChessboardTori.NamesOfAMirrorGridOnATorus
import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import YangMills.Construction.Constants.SurfaceTermNumbers
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
def GibbsBoundByTorusOnBlock.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.IsCoarse →
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    ∀ ν : Measure D.GaugeField, InfiniteLattice.IsGibbs D.β ν →
      ∀ H : D.GaugeField → ℂ, InfiniteLattice.IsBoundedObservable H → (∀ U, (H U).im = 0) →
        InfiniteLattice.IsRegionMeasurable g.fundamentalBlockInterior H →
        (∫ U, H U ∂ν).re ≤
          Real.log (D.periodicExpectation (D.liftedObservable fun U => Complex.exp (H U))).re +
            (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
              (PeriodicLattice.torusSide D.L D.m / D.mesh) ^ 3
end YangMills.Construction.ChessboardTori
end

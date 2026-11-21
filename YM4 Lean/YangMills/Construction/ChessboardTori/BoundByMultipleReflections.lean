import YangMills.Construction.ChessboardTori.CellDatumAndUpperChessboardValue
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.InfiniteLattice.ReflectionFormOfAPeriodicGibbsState
import YangMills.Construction.InfiniteLattice.TransferOperatorWithAnInsertion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (halfSpacingTimes localObsAbove positiveMultiples
  reflectionSeminorm timeConj timeStep)
namespace ChessboardTori
def MultipleReflectionBound.Statement : Prop :=
  ∀ D : ChessboardSetup, ∀ ν ∈ InfiniteLattice.periodicGibbsSet D.L D.K D.β, ∀ c : GridCell D,
    ∀ t : halfSpacingTimes D.mesh, (t : ℝ) = c.bottomTime →
    ∀ u : positiveMultiples D.mesh, (u : ℝ) = c.side →
    ∀ m : ℕ+ → ℕ+, ∀ hm : c.IsAdmissibleSideSequence m,
      (∀ F : D.GaugeField → ℂ, ∀ hF : F ∈ ReflectionGrid.cellObservables (D := D) c.cell,
        ∀ A ∈ localObsAbove t, ∀ B ∈ localObsAbove t,
          ‖∫ U, timeConj t B U * F U *
              (InfiniteLattice.shift (timeStep u)).actOn A U ∂ν‖ ≤
            c.limsupChessboardNorm m hm F hF * reflectionSeminorm ν t B *
              reflectionSeminorm ν t A) ∧
      (∃ h1 : (1 : D.GaugeField → ℂ) ∈ ReflectionGrid.cellObservables (D := D) c.cell,
        c.limsupChessboardNorm m hm 1 h1 = 1) ∧
      ∀ A ∈ localObsAbove t, ∀ B ∈ localObsAbove t,
        ‖∫ U, timeConj t B U *
            (InfiniteLattice.shift (timeStep u)).actOn A U ∂ν‖ ≤
          reflectionSeminorm ν t B * reflectionSeminorm ν t A
end ChessboardTori
end YangMills.Construction
end

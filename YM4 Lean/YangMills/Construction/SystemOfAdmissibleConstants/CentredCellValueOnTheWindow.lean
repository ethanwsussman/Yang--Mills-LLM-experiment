import YangMills.Construction.InequalityOnMirroredCopies.TheInequalityOfACell
import YangMills.Construction.SystemOfAdmissibleConstants.AdmissibleSideLengths
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SystemOfAdmissibleConstants
def CentredCellChessboardBound : Prop :=
  ForAllTrajectoryCouplings fun T y D g =>
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℝ, 1 ≤ M → ∀ E : ChessboardTori.ChessboardSetup, E.L = T.side →
      E.β ∈ D.passageWindow E.K g →
      ∀ (c : ChessboardTori.GridCell E), c.side ≤ 1 → ∀ h : InfiniteLattice.AmbientSpace → ℝ,
        TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 h →
        tsupport h ⊆ TestFunctions.closedBallR4 c.centre (c.side / 4) →
        ∀ ν ∈ InfiniteLattice.periodicGibbsSet E.L E.K E.β,
          ReflectedCopies.centredSmeared E h (∫ U, InfiniteLattice.smearedEnergy h U ∂ν) ∈
            ChessboardTori.ReflectionGrid.cellObservables (D := E) c.cell ∧
          ∀ (m : ℕ+ → ℕ+) (hm : c.IsAdmissibleSideSequence m)
            (hF : ReflectedCopies.centredSmeared E h (∫ U, InfiniteLattice.smearedEnergy h U ∂ν) ∈
              ChessboardTori.ReflectionGrid.cellObservables (D := E) c.cell),
            c.limsupChessboardNorm m hm _ hF ≤ C * c.side⁻¹ * TestFunctions.sharpNormR4 M h
end YangMills.Construction.SystemOfAdmissibleConstants
end

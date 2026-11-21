import YangMills.Construction.ChessboardTori.CellDatumAndUpperChessboardValue
import YangMills.Construction.ReflectionsAndOneInsertion.OneInsertionAtOneCutoff
import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
open RenormalizationStepParameters TorusLumps TestFunctions
open InfiniteLattice (periodicGibbsSet)
open ChessboardTori (GridCell ReflectionGrid)
open ReflectionsAndOneInsertion (complexSmeared)
def WindowCentredCellBound (ℓ : StepParameters) (Bs g CI q M : ℝ) : Prop :=
  ∀ (D : ChessboardTori.ChessboardSetup), D.L = ℓ.side → IsFirstPassagePoint ℓ Bs g D.K D.β →
    ∀ (c : GridCell D) (h : InfiniteLattice.AmbientSpace → ℝ), IsLipschitzFor euclidDistR4 h →
      tsupport h ⊆ closedBallR4 c.centre (1 / 4 * c.side) → c.side ≤ 1 →
      ∀ ν ∈ periodicGibbsSet D.L D.K D.β,
        ∃ hF : (fun U => complexSmeared D h U - ∫ V, complexSmeared D h V ∂ν) ∈
            ReflectionGrid.cellObservables (D := D) c.cell,
          ∀ (m : ℕ+ → ℕ+) (hm : c.IsAdmissibleSideSequence m),
            c.limsupChessboardNorm m hm _ hF ≤ CI * c.side ^ (-q) * sharpNormR4 M h
namespace WindowCentredCell
def Statement : Prop :=
  HoldsAtAdmissibleParameters fun T y => ∀ Bs : ℝ, 2 * T.B ≤ Bs → ForSmallCoupling fun g =>
    ∃ CI q : ℝ, 0 ≤ CI ∧ 0 ≤ q ∧ ∀ M : ℝ, 1 ≤ M → WindowCentredCellBound (T.stepParameters y) Bs g CI q M
end WindowCentredCell
end YangMills.Construction.TotalDensities
end

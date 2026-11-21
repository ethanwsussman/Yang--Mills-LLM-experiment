import YangMills.Construction.ChessboardTori.SidesCentresAndTheChessboardFunctional
import YangMills.Construction.MirrorGridsOfEverySide.MirrorGridOrientationsAndReflectionProducts
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
open ChessboardTori (ReflectionGrid)
def ChessboardDomination.Statement : Prop :=
  ∀ D : GridSetup, ∀ ν ∈ D.periodicGibbs, ∀ g : ReflectionGrid D, g.HasAdmissibleSide →
    ∀ m : ℕ+ → ℕ+, Tendsto (fun k => PeriodicLattice.torusSide D.L (m k)) atTop atTop →
      ∀ F : g.cellSet → D.GaugeField → ℂ,
        (∀ S, F S ∈ ReflectionGrid.cellObservables (D := D) S.1) →
        ∀ hF : {S | F S ≠ 1}.Finite,
          ‖D.integralOf ν fun U => ∏ S ∈ hF.toFinset, F S U‖ ≤
              liminf (fun k => ∏ S ∈ hF.toFinset,
                (g.withExponent (m k)).chessboardNormOfCell S.1 (F S)) atTop ∧
            liminf (fun k => ∏ S ∈ hF.toFinset,
                (g.withExponent (m k)).chessboardNormOfCell S.1 (F S)) atTop ≤
              ∏ S ∈ hF.toFinset,
                limsup (fun k => (g.withExponent (m k)).chessboardNormOfCell S.1 (F S)) atTop
end YangMills.Construction.MirrorGridsAllSides
end

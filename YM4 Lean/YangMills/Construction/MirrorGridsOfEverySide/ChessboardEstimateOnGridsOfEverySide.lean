import YangMills.Construction.ChessboardTori.SidesCentresAndTheChessboardFunctional
import YangMills.Construction.MirrorGridsOfEverySide.MirrorGridOrientationsAndReflectionProducts
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
open ChessboardTori Matrices
def chessboardEstimate_allSides : Prop :=
  ∀ (D : GridSetup) (g : ReflectionGrid D), g.HasAdmissibleSide →
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    ((∀ F : g.torusCellSet → (D.PeriodicLink → ComplexMatrix2) → ℂ,
        (∀ C, F C ∈ g.torusCellObservables C.1) →
        ‖D.periodicExpectation fun U => ∏ᶠ C, F C U‖ ≤
          ∏ᶠ C, g.cellChessboardSeminorm C.1 (F C)) ∧
      ∀ C ∈ g.torusCellSet, ∀ F ∈ g.torusCellObservables C,
        (D.periodicExpectation (g.cellProduct C F)).im = 0 ∧
          0 ≤ (D.periodicExpectation (g.cellProduct C F)).re) ∧
    (∀ C ∈ g.torusCellSet,
      (∀ F ∈ g.torusCellObservables C,
        (∀ G ∈ g.torusCellObservables C, F + G ∈ g.torusCellObservables C ∧
          g.cellChessboardSeminorm C (F + G) ≤
            g.cellChessboardSeminorm C F + g.cellChessboardSeminorm C G) ∧
        (∀ z : ℂ, z • F ∈ g.torusCellObservables C ∧
          g.cellChessboardSeminorm C (z • F) = ‖z‖ * g.cellChessboardSeminorm C F) ∧
        g.cellChessboardSeminorm C F ≤ ⨆ U : D.torusFields, ‖F U.1‖ ∧
        conjFun F ∈ g.torusCellObservables C ∧
        g.cellChessboardSeminorm C (conjFun F) = g.cellChessboardSeminorm C F ∧
        (∀ C' ∈ g.torusCellSet, g.torusTransportTo C C' F ∈ g.torusCellObservables C' ∧
          g.cellChessboardSeminorm C' (g.torusTransportTo C C' F) =
            g.cellChessboardSeminorm C F) ∧
        ∀ s : D.TorusSymmetry,
          (fun P : Set D.Torus => s.toFun '' P) '' g.torusWallFamily = g.torusWallFamily →
            s.toFun '' C ∈ g.torusCellSet ∧
            GridSetup.TorusSymmetry.precompose s F ∈ g.torusCellObservables (s.toFun '' C) ∧
            g.cellChessboardSeminorm (s.toFun '' C) (GridSetup.TorusSymmetry.precompose s F) =
              g.cellChessboardSeminorm C F) ∧
      (fun _ => 1) ∈ g.torusCellObservables C ∧ g.cellChessboardSeminorm C (fun _ => 1) = 1) ∧
    ∀ g' : ReflectionGrid D, g'.IsCoarsening g → 2 * g'.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
      ∀ Q ∈ g'.torusCellSet,
      ∀ F : {C : Set D.Torus // C ∈ g.torusCellSet ∧ C ⊆ Q} → (D.PeriodicLink → ComplexMatrix2) → ℂ,
        (∀ C, F C ∈ g.torusCellObservables C.1) →
          (fun U => ∏ᶠ C, F C U) ∈ g'.torusCellObservables Q ∧
          g'.cellChessboardSeminorm Q (fun U => ∏ᶠ C, F C U) ≤
            ∏ᶠ C, g.cellChessboardSeminorm C.1 (F C)
end YangMills.Construction.MirrorGridsAllSides
end

import YangMills.Construction.ChessboardTori.CoarseGridsOfAGrid
import YangMills.Construction.ChessboardTori.LimitingChessboardSeminorm
import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import YangMills.Construction.Constants.SurfaceTermNumbers
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace observableSupNorm)
namespace ReflectionGrid
variable {D : ChessboardSetup}
def coarseSurfaceTerm (g : ReflectionGrid D) (O : Set (Set AmbientSpace)) (k : ℕ+) : ℝ :=
  (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
    ((g.enclosingCoarsening O).cellSide / D.mesh) ^ 3 *
    ((g.enclosingCoarsening O).cellSide / PeriodicLattice.torusSide D.L k)
end ReflectionGrid
def PeriodicGibbsBoundOfFiniteIndex.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.IsCoarse →
    ∀ ν ∈ D.periodicStates, ∀ O : Set (Set AmbientSpace), g.IsFiniteCellFamily O →
      ∀ F : Set AmbientSpace → D.GaugeField → ℂ,
        (∀ S ∈ O, F S ∈ ReflectionGrid.cellObservables (D := D) S) →
        ∀ (Γ : AddSubgroup (InfiniteLattice.LatticePoint D.mesh)) (q : ℕ), Γ.FiniteIndex →
          Γ.index = q →
          (∀ v ∈ Γ, InfiniteLattice.IsSymmetricUnder ν (InfiniteLattice.shift v)) →
          ∀ k : ℕ+, 2 * (g.enclosingCoarsening O).cellSide ≤ PeriodicLattice.torusSide D.L k →
            ∀ t : ℝ, 0 < t →
              t < (2 * observableSupNorm (fun U : D.GaugeField => ∏ᶠ S ∈ O, F S U) + 1)⁻¹ →
              t * ‖∫ U, ∏ᶠ S ∈ O, F S U ∂ν‖ ≤
                t * ∏ᶠ S ∈ O, g.normAtExponent k S (F S) +
                  (2 * (q : ℝ)) ^ 4 * g.coarseSurfaceTerm O k +
                  t ^ 2 * observableSupNorm (fun U : D.GaugeField => ∏ᶠ S ∈ O, F S U) ^ 2
end YangMills.Construction.ChessboardTori
end

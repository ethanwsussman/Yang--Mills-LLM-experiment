import YangMills.Construction.ChessboardTori.CellDatumAndUpperChessboardValue
import YangMills.Construction.InequalityOnMirroredCopies.ArrayOnRectangularTori
import YangMills.Construction.Lattice.SettingOfTheTorusBound
import YangMills.Construction.ReflectionsAndOneInsertion.OneInsertionAtOneCutoff
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open ChessboardTori
open InfiniteLattice (AmbientSpace)
def copySize (A b l ρ : ℝ) : ℝ :=
  A * Real.exp (b * l ^ 4 + b * TorusBound.logPos (1 / ρ) ^ (1 / 20 : ℝ))
def radiusNorm (ρ : ℝ) (f : AmbientSpace → ℝ) : ℝ :=
  max (TestFunctions.uniformNorm f) (min 1 ρ * TestFunctions.lipConstR4 f)
def copyBound (A b l ρ : ℝ) (f : AmbientSpace → ℝ) : ℝ := copySize A b l ρ * radiusNorm ρ f
variable {S : ChessboardSetup}
structure SupportedInCell (c : GridCell S) (ρ : ℝ) (f : AmbientSpace → ℝ) : Prop where
  radius_pos : 0 < ρ
  radius_le : ρ ≤ c.side / 4
  lipschitz : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f
  support_in_ball : ∃ y : AmbientSpace, ∀ x, f x ≠ 0 → x ∈ TestFunctions.closedBallR4 y ρ
  support_in_cell : ∀ x, f x ≠ 0 → x ∈ c.cell
  far_from_walls : ∀ x, f x ≠ 0 → ∀ z ∈ c.grid.walls, ρ ≤ TorusMetric.euclidNormVec (x - z)
def centredSmeared (S : ChessboardSetup) (f : AmbientSpace → ℝ) (κ : ℝ) : S.GaugeField → ℂ :=
  fun U => ReflectionsAndOneInsertion.complexSmeared S f U - (κ : ℂ)
def CopyInequality (S : ChessboardSetup) (A b : ℝ) : Prop :=
  ∀ (c : GridCell S) (ρ : ℝ) (f : AmbientSpace → ℝ), SupportedInCell c ρ f →
    ∃ κ : ℝ, ∀ j : ℕ,
      (tiledMean c.grid (cubicCounts S j) c.cell (centredSmeared S f κ)).im = 0 ∧
        0 ≤ (tiledMean c.grid (cubicCounts S j) c.cell (centredSmeared S f κ)).re ∧
        (tiledMean c.grid (cubicCounts S j) c.cell (centredSmeared S f κ)).re ≤
          copyBound A b c.side ρ f ^ cellCount (cubicCounts S j)
def SixteenCopyBound (S : ChessboardSetup) (A₀ b₀ : ℝ) : Prop :=
  ∀ (c : GridCell S) (ρ : ℝ) (f : AmbientSpace → ℝ), SupportedInCell c ρ f →
    ∃ κ : ℝ, ‖tiledMean c.grid (minimalCounts S) c.cell (centredSmeared S f κ)‖ ≤
      copyBound A₀ b₀ c.side ρ f ^ 16
def torusAverage (S : ChessboardSetup) (m : ℕ+) (F : S.GaugeField → ℂ) : ℂ :=
  (S.withExponent m).periodicExpectation ((S.withExponent m).liftedObservable F)
end YangMills.Construction.ReflectedCopies
end

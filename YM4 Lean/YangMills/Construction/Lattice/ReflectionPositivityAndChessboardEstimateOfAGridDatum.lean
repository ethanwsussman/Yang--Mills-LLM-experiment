import YangMills.Construction.Lattice.CellGridGibbsMeasure
import YangMills.Construction.Lattice.ChessboardCopiesOfAGridDatum
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.CellGrid
variable {L : ℕ} {κ : ℤ} (d : CellGrid L κ)
def fixedPointComplementComponents (θ : d.Space → d.Space) : Set (Set d.Space) :=
  {H | ∃ x ∈ (Function.fixedPoints θ)ᶜ, H = connectedComponentIn (Function.fixedPoints θ)ᶜ x}
def IsReflectionPositiveAcrossFaces (β : ℝ) : Prop :=
  ∀ (μ : Fin 4) (a : ℤ) (θ : d.Space → d.Space), d.IsInducedMap θ (d.faceReflect μ a) →
    ∀ H ∈ d.fixedPointComplementComponents θ, ∀ F : d.GaugeConfig → ℂ,
      BoxTorus.IsBoundedBorelOfEdges {e : d.DirectedEdge | e.LiesIn H} F →
      0 ≤ d.gibbsMean β fun U =>
        starRingEnd ℂ ((d.symmetryOfMap θ).actOnObservables F U) * F U
def copiesProductMean (β : ℝ) (c : d.spaceCells) (F : d.cellObservables c) : ℂ :=
  d.gibbsMean β fun U => ∏ᶠ c' : d.spaceCells, d.checkerboardCopy c c' F U
def checkerboardNorm (β : ℝ) (c : d.spaceCells) (F : d.cellObservables c) : ℝ :=
  (d.copiesProductMean β c F).re ^ (1 / (d.numCells : ℝ))
def CheckerboardBound (β : ℝ) : Prop :=
  (∀ (c : d.spaceCells) (F : d.cellObservables c), 0 ≤ d.copiesProductMean β c F) ∧
  ∀ F : (c : d.spaceCells) → d.cellObservables c,
    ‖d.gibbsMean β fun U => ∏ᶠ c : d.spaceCells, (F c).1 U‖ ≤
      ∏ᶠ c : d.spaceCells, d.checkerboardNorm β c (F c)
end YangMills.Construction.CellGrid
end

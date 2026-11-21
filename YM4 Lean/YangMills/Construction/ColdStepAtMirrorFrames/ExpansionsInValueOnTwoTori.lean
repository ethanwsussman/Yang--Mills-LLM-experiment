import YangMills.Construction.ColdStepAtMirrorFrames.PartsOfTheExponent
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def CellExpansionsCloseInValueAt (P : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F F' : BlockFrame) (U : F.GaugeField F.top)
    (U' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) (star : Bool),
    AgreeingTopPair P t x U U' Y Y' r →
    IsRegularFamily P.L t P.n₀ P.σ P.decayRate P.E P.energyRatio f →
    NearCellsClose P.ballRadius x P.κ ((P.Ct * (1 + P.energyRatio) / 4) * Real.exp (-(2 * P.κ * r))) Y Y' r
      (fun Z η => cellCentredExpansion star P.a P.chainParams.ρA (frameRadius x) f Z η U)
      (fun Z η => cellCentredExpansion star P.a P.chainParams.ρA (frameRadius x) f Z η U')
def CellExpansionsCloseInValueOnTwoTori : Prop := EventuallyInParameters CellExpansionsCloseInValueAt
end YangMills.Construction.ColdStepAtMirrorFrames
end

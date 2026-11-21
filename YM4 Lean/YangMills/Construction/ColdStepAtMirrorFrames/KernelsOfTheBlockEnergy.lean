import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def cellEnergyAlong (a : ℝ) (Y : F.Cell) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) {k : ℕ} (q : Fin k → ChartDirection F) (σ : Fin k → ℝ) : ℝ :=
  cellEnergyShare a Y (fun x i => w x i + ∑ l, σ l • directionCoordinate (q l) x i)
    (leftTranslate (fun y i => ∑ l, σ l • directionMove (q l) y i) V)
def cellEnergyKernel (a : ℝ) (Y : F.Cell) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) {k : ℕ} (q : Fin k → ChartDirection F) : ℝ :=
  iteratedFDeriv ℝ k (cellEnergyAlong a Y w V q) 0 fun l => Pi.single l 1
def directionReach {k : ℕ} (Y : F.Cell) (q : Fin k → ChartDirection F) : ℕ :=
  Finset.univ.sup fun l : Fin k => cellSupDist Y (directionCell (q l))
def CellEnergyKernelBound : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ Ck : ℕ → ℝ, (∀ k, 0 < Ck k) ∧
      ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
        IsBlockTorus L F →
        IsAdmissibleChartPoint L c.σA w V → ∀ (Y : F.Cell) (k : ℕ) (q : Fin k → ChartDirection F),
          AnalyticAt ℝ (cellEnergyAlong a Y w V q) 0 ∧
          (1 ≤ k → (∀ l, ‖directionVector (q l)‖ = 1) →
            |cellEnergyKernel a Y w V q| ≤ Ck k * Real.exp (-(c.δ₁ * directionReach Y q)))
end YangMills.Construction.ColdStepAtMirrorFrames
end

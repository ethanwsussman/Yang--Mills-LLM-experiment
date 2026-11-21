import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def CellEnergyShareInvariant : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∀ (F : BlockFrame) (w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
      IsBlockTorus L F → IsAdmissibleChartPoint L c.σA w V → ∀ Y : F.Cell,
      (∀ γ : F.Cell → UnitQuaternion, (∀ b ∈ chordBonds (finiteCells F), (w' b.1 b.2 : ℍ[ℝ]) =
          (γ (enclosingCell b.1) : ℍ[ℝ]) * (w b.1 b.2 : ℍ[ℝ]) * ((γ (enclosingCell b.1))⁻¹ : UnitQuaternion)) →
        cellEnergyShare a Y w' (gaugeTransform γ V) = cellEnergyShare a Y w V) ∧
      ∀ h : F.Cell, (∀ b ∈ chordBonds (finiteCells F), w' (b.1 + cellCentre F.depth h) b.2 = w b.1 b.2) →
        cellEnergyShare a (Y + h) w' (translateField h V) = cellEnergyShare a Y w V
end YangMills.Construction.ColdStepAtMirrorFrames
end

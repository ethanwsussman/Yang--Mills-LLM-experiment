import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ChartDeterminedByField : Prop :=
  ∀ (F : BlockFrame) (w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (γ : F.Site F.depth → UnitQuaternion), Odd F.blockSide →
    (∀ i, 2 ≤ F.extent i) → (∀ b, b ∉ chordBonds (finiteCells F) → w b.1 b.2 = 0) →
    (∀ b, b ∉ chordBonds (finiteCells F) → w' b.1 b.2 = 0) →
    (∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ 1) →
    (∀ b ∈ chordBonds (finiteCells F), ‖w' b.1 b.2‖ ≤ 1) →
    (∀ z, γ (cellCentre F.depth z) = 1) →
    AgreeOnBonds (finiteCells F) F.depth (chartedField w' V) (gaugeTransform γ (chartedField w V)) → w' = w
end YangMills.Construction.ColdStepAtMirrorFrames
end

import YangMills.Construction.ColdStepAtMirrorFrames.MirrorOfAMovedTopForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
def MinimalActionIsGaugeInvariant : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (S : Finset F.Cell) (j : ℕ), 0 < F.blockSide → j ≤ F.top →
    ∀ (Γ : F.Site j → UnitQuaternion) (X : F.GaugeField j),
    minimalAction a S j (gaugeTransform Γ X) = minimalAction a S j X
def MinimizingChartGaugeCovariant : Prop :=
  ∀ (F : BlockFrame) (a ρ : ℝ) (V : F.GaugeField F.top) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (γ : F.Cell → UnitQuaternion), Odd F.blockSide →
    (∀ i, 2 ≤ F.extent i) → IsMinimizingChart a (finiteCells F) V ρ w →
    IsMinimizingChart a (finiteCells F) (gaugeTransform γ V) ρ fun x i => adjointMap (γ (enclosingCell x)) (w x i)
def MinimalActionGaugeCovariance : Prop := MinimalActionIsGaugeInvariant ∧ MinimizingChartGaugeCovariant
end ColdStepAtMirrorFrames
end YangMills.Construction
end

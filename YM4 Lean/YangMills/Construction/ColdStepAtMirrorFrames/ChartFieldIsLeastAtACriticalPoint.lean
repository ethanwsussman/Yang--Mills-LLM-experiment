import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def chartEnergyOnSegment (a : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (τ : ℝ) : ℝ :=
  blockEnergy a S F.depth (chartedField (fun x i => w x i + τ • dw x i) V) V
def ChartCriticalPointIsMinimal : Prop :=
  ∀ (F : BlockFrame) (a κ r σ : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (w₀ w₁ : F.Site F.depth → Fin 4 → imaginaryQuaternions), 0 < κ →
    HasCoerciveHessian a κ r σ S V →
    (∀ b, b ∉ chordBonds S → w₀ b.1 b.2 = 0) → (∀ b, b ∉ chordBonds S → w₁ b.1 b.2 = 0) →
    (∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → (∀ b ∈ chordBonds S, ‖w₀ b.1 b.2 + τ • (w₁ b.1 b.2 - w₀ b.1 b.2)‖ ≤ r) ∧
      IsCold S F.depth σ (chartedField (fun x i => w₀ x i + τ • (w₁ x i - w₀ x i)) V)) →
    (∀ ε : ℝ, 0 < ε → ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ < τ₀ →
      chartEnergyOnSegment a S V w₀ (fun x i => w₁ x i - w₀ x i) 0 - ε * τ ≤
        chartEnergyOnSegment a S V w₀ (fun x i => w₁ x i - w₀ x i) τ) →
    blockEnergy a S F.depth (chartedField w₀ V) V ≤ blockEnergy a S F.depth (chartedField w₁ V) V
end YangMills.Construction.ColdStepAtMirrorFrames
end

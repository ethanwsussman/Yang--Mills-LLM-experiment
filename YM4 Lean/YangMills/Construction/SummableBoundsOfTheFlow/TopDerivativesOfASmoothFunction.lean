import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionOfAMeanInTheTop
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.Estimates
open YangMills.Construction.ColdStepAtMirrorFrames
structure FieldDerivRegularity (F : BlockFrame) (ρ : ℝ) (V : F.GaugeField F.top) : Prop where
  contDiffOn : ∀ (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (k : ℕ)
    (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    JointlyContDiffOnBalls ρ V G → k ≤ 2 → ContDiffOn ℝ 1 (fieldDeriv G V e X) {η | ∀ b, ‖η b‖ < ρ}
  continuousOn : ∀ (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (k : ℕ)
    (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    JointlyContDiffOnBalls ρ V G → k ≤ 3 → ContinuousOn (fieldDeriv G V e X) {η | ∀ b, ‖η b‖ < ρ}
  bounded : ∀ (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (k : ℕ)
    (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    JointlyContDiffOnBalls ρ V G → k ≤ 3 →
    ∃ D : ℝ, ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) → |fieldDeriv G V e X η| ≤ D
  contDiffAt_slice : ∀ (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (k : ℕ)
    (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (η : StepVariable (finiteCells F)),
    JointlyContDiffOnBalls ρ V G → k ≤ 3 → (∀ b, ‖η b‖ ≤ ρ) →
    ContDiffAt ℝ k (fun τ : Fin k → ℝ => G η (leftTranslate (ColdStepAtMirrorFrames.bondSpread e X τ) V)) 0
  sum : ∀ (α : Type) (S : Finset α) (G : α → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (k : ℕ)
    (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (η : StepVariable (finiteCells F)),
    (∀ a ∈ S, JointlyContDiffOnBalls ρ V (G a)) → k ≤ 3 → (∀ b, ‖η b‖ ≤ ρ) →
    fieldDeriv (fun η V' => ∑ a ∈ S, G a η V') V e X η = ∑ a ∈ S, fieldDeriv (G a) V e X η
def fieldDerivRegularityStatement : Prop :=
  ∀ (F : BlockFrame) (ρ : ℝ) (V : F.GaugeField F.top), FieldDerivRegularity F ρ V
end YangMills.Construction.Estimates
end

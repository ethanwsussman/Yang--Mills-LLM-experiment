import YangMills.Construction.ColdStepAtMirrorFrames.JetOfAFunctionOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def MinimalOfCriticalJet : Prop :=
  ∀ (F : BlockFrame) (a lam ρ σ : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (w₀ w₁ : F.Site F.depth → Fin 4 → imaginaryQuaternions), 0 ≤ a → 0 < lam →
    (∀ b : F.Site F.depth × Fin 4, b ∈ innerBonds S F.depth) →
    HasCoerciveHessian a lam ρ σ S V →
    (∀ b, b ∉ chordBonds S → w₀ b.1 b.2 = 0) → (∀ b, b ∉ chordBonds S → w₁ b.1 b.2 = 0) →
    (∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → (∀ b ∈ chordBonds S, ‖w₀ b.1 b.2 + τ • (w₁ b.1 b.2 - w₀ b.1 b.2)‖ ≤ ρ) ∧
      IsCold S F.depth σ (chartedField (fun x i => w₀ x i + τ • (w₁ x i - w₀ x i)) V)) →
    (∀ c ∈ innerBonds S F.top, blockFit (chartedField w₀ V) V c = 0) →
    HasFDerivAt (formComposition (innerBonds S F.depth) (minimalAction a S F.depth) (chartedField w₀ V))
      (0 : (↥(innerBonds S F.depth) → imaginaryQuaternions) →L[ℝ] ℝ) 0 →
    blockEnergy a S F.depth (chartedField w₀ V) V ≤ blockEnergy a S F.depth (chartedField w₁ V) V
end YangMills.Construction.ColdStepAtMirrorFrames
end

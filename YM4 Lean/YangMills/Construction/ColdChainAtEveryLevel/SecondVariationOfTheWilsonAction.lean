import YangMills.Construction.ColdChainAtEveryLevel.VariationsOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def wilsonActionSecondVariationStatement : Prop :=
  ∀ (F : BlockFrame) (S : Finset F.Cell) (σ : ℝ) (U : F.GaugeField 0), 0 < σ → IsCold S 0 σ U →
    (∀ (k : ℕ) (c : Fin k → F.Site 0 × Fin 4),
      AnalyticAt ℝ (fun ζ : Fin k → imaginaryQuaternions =>
        wilsonAction S (expRotatedField (fun y i => ∑ l, if c l = (y, i) then ζ l else 0) U)) 0) ∧
    ∀ v : F.Site 0 → Fin 4 → imaginaryQuaternions,
      ∑ p ∈ innerPlaquettes S 0, ‖variationCurl U v p‖ ^ 2 - 64 * σ * ∑ b ∈ innerBonds S 0, ‖v b.1 b.2‖ ^ 2 ≤
          deriv (deriv fun τ : ℝ => wilsonAction S (expRotatedField (fun x i => τ • v x i) U)) 0 ∧
        |deriv (fun τ : ℝ => wilsonAction S (expRotatedField (fun x i => τ • v x i) U)) 0| ≤
          16 * σ * ∑ b ∈ innerBonds S 0, ‖v b.1 b.2‖
end YangMills.Construction.BlockAverages
end

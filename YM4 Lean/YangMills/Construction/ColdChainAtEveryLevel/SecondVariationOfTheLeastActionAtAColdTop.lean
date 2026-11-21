import YangMills.Construction.ColdChainAtEveryLevel.VariationsOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def coldTopSecondVariationStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ ca : ℝ, 0 < ca ∧ ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∃ C σ₀ : ℝ, 0 < C ∧ 0 < σ₀ ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (σ : ℝ) (V : F.GaugeField F.top), 0 < σ → σ ≤ σ₀ → IsCold S F.top σ V →
        ∀ v : F.Site F.top → Fin 4 → imaginaryQuaternions, (∀ b, b ∉ innerBonds S F.top → v b.1 b.2 = 0) →
          ca * ∑ p ∈ innerPlaquettes S F.top, ‖variationCurl V v p‖ ^ 2 -
                C * σ * ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2‖ ^ 2 ≤
              deriv (deriv fun τ : ℝ =>
                minimalAction a S F.top (expRotatedField (fun x i => τ • v x i) V)) 0 ∧
            |deriv (fun τ : ℝ => minimalAction a S F.top (expRotatedField (fun x i => τ • v x i) V)) 0| ≤
              C * σ * ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2‖
end YangMills.Construction.BlockAverages
end

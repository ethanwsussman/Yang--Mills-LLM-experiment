import YangMills.Construction.ColdChainAtEveryLevel.VariationsOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def bondListSpread {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (ζ : Fin k → imaginaryQuaternions) :
    F.Site j → Fin 4 → imaginaryQuaternions :=
  fun y i => ∑ l, if c l = (y, i) then ζ l else 0
def coldFieldSecondVariationStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ ca : ℝ, 0 < ca ∧ ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∃ C σ₀ : ℝ, 0 < C ∧ 0 < σ₀ ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (σ : ℝ) (W : F.GaugeField F.depth), 0 < σ → σ ≤ σ₀ → IsCold S F.depth σ W →
        (∀ (k : ℕ) (c : Fin k → F.Site F.depth × Fin 4),
          AnalyticAt ℝ (fun ζ : Fin k → imaginaryQuaternions =>
            minimalAction a S F.depth (expRotatedField (bondListSpread c ζ) W)) 0) ∧
        ∀ v : F.Site F.depth → Fin 4 → imaginaryQuaternions, (∀ b, b ∉ innerBonds S F.depth → v b.1 b.2 = 0) →
          ca * ∑ p ∈ innerPlaquettes S F.depth, ‖variationCurl W v p‖ ^ 2 -
                C * σ * ∑ b ∈ innerBonds S F.depth, ‖v b.1 b.2‖ ^ 2 ≤
              deriv (deriv fun τ : ℝ =>
                minimalAction a S F.depth (expRotatedField (fun x i => τ • v x i) W)) 0 ∧
            |deriv (fun τ : ℝ => minimalAction a S F.depth (expRotatedField (fun x i => τ • v x i) W)) 0| ≤
              C * σ * ∑ b ∈ innerBonds S F.depth, ‖v b.1 b.2‖
end YangMills.Construction.BlockAverages
end

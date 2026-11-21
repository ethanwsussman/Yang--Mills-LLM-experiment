import YangMills.Construction.ColdChainAtEveryLevel.TotalAtAComplexTop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BlockAverages
def rotatedTopTaylorBoundsStatement : Prop :=
  ∀ a θ δ : ℝ, 0 < a → 0 ≤ θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → ∃ Ca : ℝ, 0 < Ca ∧
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
          ∀ (k : ℕ) (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), AreUnitVectors X →
            TwistedTotalBounds a θ δ Ca c C s S V b X
end YangMills.Construction.BlockAverages
end

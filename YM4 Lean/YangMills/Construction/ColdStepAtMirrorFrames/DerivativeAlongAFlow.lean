import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def expFlow {j : ℕ} (B : F.Site j → Fin 4 → imaginaryQuaternions) (W : F.GaugeField j) (u : ℝ) : F.GaugeField j :=
  leftTranslate (fun y i => u • B y i) W
def DerivBoundAlongFlow : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : BlockFrame) (j : ℕ)
    (T : Finset (F.Site j × Fin 4)) (G : F.GaugeField j → E) (W : F.GaugeField j)
    (B : F.Site j → Fin 4 → imaginaryQuaternions)
    (M : ℕ → ℝ), (∀ b, b ∈ T) → (∀ l, 0 ≤ M l) →
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 → ContDiffThreeAlongBonds G (expFlow B W u)) →
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ (l : ℕ) (c : Fin l → F.Site j × Fin 4) (X : Fin l → imaginaryQuaternions), 1 ≤ l → l ≤ 3 →
      AreUnitVectors X → ‖bondDeriv G (expFlow B W u) c X‖ ≤ M l) →
    ∀ (k : ℕ) (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 → AreUnitVectors X →
      ‖bondDeriv G (expFlow B W 1) c X - bondDeriv G W c X‖ ≤
        C₀ * (M 1 + M 2 + M 3) * ∑ b ∈ T, ‖B b.1 b.2‖
end YangMills.Construction.ColdStepAtMirrorFrames
end

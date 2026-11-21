import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAlongAMotion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages Estimates
namespace ColdStepAtMirrorFrames
def SecondDerivAlongMotionsClose : Prop :=
  ∀ (F : BlockFrame) (j : ℕ) (T : Finset (F.Site j × Fin 4)) (G : F.GaugeField j → ℝ) (W W₀ : F.GaugeField j) (ε E K μ : ℝ),
    (∀ b, b ∈ T) → ContDiffThreeAlongBonds G W → ContDiffThreeAlongBonds G W₀ →
    0 ≤ ε → 0 ≤ E → 0 ≤ K → 0 ≤ μ →
    (∀ (k : ℕ) (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 2 → AreUnitVectors X →
      |bondDeriv G W c X - bondDeriv G W₀ c X| ≤ ε) →
    (∀ (c : Fin 1 → F.Site j × Fin 4) (X : Fin 1 → imaginaryQuaternions), AreUnitVectors X → bondDeriv G W₀ c X = 0) →
    (∀ (c : Fin 2 → F.Site j × Fin 4) (X : Fin 2 → imaginaryQuaternions), AreUnitVectors X → |bondDeriv G W₀ c X| ≤ E) →
    (∀ α : (Fin 1 → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions, (∀ x b, α 0 x b = 0) →
      (∀ x b, ContDiffAt ℝ 3 (fun τ => α τ x b) 0) →
      ∑ b ∈ T, ‖motionComponent α ![0] b.1 b.2‖ ≤ K →
      |iteratedFDeriv ℝ 1 (fun τ => G (leftTranslate (α τ) W)) 0 ![Pi.single 0 1]| ≤ ε * K) ∧
    ∀ α α₀ : (Fin 2 → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions, (∀ x b, α 0 x b = 0) → (∀ x b, α₀ 0 x b = 0) →
      (∀ x b, ContDiffAt ℝ 3 (fun τ => α τ x b) 0) → (∀ x b, ContDiffAt ℝ 3 (fun τ => α₀ τ x b) 0) →
      (∀ l, ∑ b ∈ T, ‖motionComponent α ![l] b.1 b.2‖ ≤ K) → (∀ l, ∑ b ∈ T, ‖motionComponent α₀ ![l] b.1 b.2‖ ≤ K) →
      ∑ b ∈ T, ‖motionComponent α ![0, 1] b.1 b.2‖ ≤ K →
      (∀ l, ∑ b ∈ T, ‖motionComponent α ![l] b.1 b.2 - motionComponent α₀ ![l] b.1 b.2‖ ≤ μ) →
      |iteratedFDeriv ℝ 2 (fun τ => G (leftTranslate (α τ) W)) 0 ![Pi.single 0 1, Pi.single 1 1] -
        iteratedFDeriv ℝ 2 (fun τ => G (leftTranslate (α₀ τ) W₀)) 0 ![Pi.single 0 1, Pi.single 1 1]| ≤
        ε * (K ^ 2 + K) + 2 * E * K * μ
end ColdStepAtMirrorFrames
end YangMills.Construction
end

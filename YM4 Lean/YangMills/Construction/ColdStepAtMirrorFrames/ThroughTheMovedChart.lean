import YangMills.Construction.ColdStepAtMirrorFrames.MovedBondsOfAChart
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def TranslatedChartCompositeBound : Prop :=
  ∃ C : ℕ → ℕ → ℝ, (∀ k M, 0 ≤ C k M) ∧
    ∀ (F : BlockFrame) (f : F.GaugeField F.depth → ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
      (V : F.GaugeField F.top) (k : ℕ)
      (ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions) (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions)
      (J : Fin k → Finset (F.Site F.depth × Fin 4)) (M : ℕ) (N : ℝ),
      (∀ l b, ParameterMovesBond ξ μ l b → b ∈ J l) →
      (∀ (n : ℕ) (b : Fin n → F.Site F.depth × Fin 4) (X : Fin n → imaginaryQuaternions),
        AnalyticAt ℝ (fun τ : Fin n → ℝ => f (leftTranslate (bondSpread b X τ) (chartedField w V))) 0) →
      AnalyticAt ℝ (fun σ : Fin k → ℝ => f (translatedChart w V ξ μ σ)) 0 ∧
      ((∀ b : F.Site F.depth × Fin 4, ‖w b.1 b.2‖ ≤ 1 ∨ IsAxialTreeBond b) →
        (∀ l (b : F.Site F.depth × Fin 4), ‖ξ l b.1 b.2‖ ≤ 1) → (∀ l y i, ‖μ l y i‖ ≤ 1) →
        (∀ l, (J l).card ≤ M) → 0 ≤ N → 1 ≤ k →
        (∀ (p : ℕ) (b : Fin p → F.Site F.depth × Fin 4) (X : Fin p → imaginaryQuaternions), 1 ≤ p → p ≤ k →
          AreUnitVectors X → (∀ l, ∃ m, b m ∈ J l) → |bondDeriv f (chartedField w V) b X| ≤ N) →
        |iteratedFDeriv ℝ k (fun σ : Fin k → ℝ => f (translatedChart w V ξ μ σ)) 0 fun l => Pi.single l 1| ≤ C k M * N)
end YangMills.Construction.ColdStepAtMirrorFrames
end

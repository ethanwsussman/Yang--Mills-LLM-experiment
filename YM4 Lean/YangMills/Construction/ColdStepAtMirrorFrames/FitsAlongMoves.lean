import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import YangMills.Construction.ColdStepAtMirrorFrames.MovedBondsOfAChart
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame} {k : ℕ}
def ParameterTouchesBond (ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) (l : Fin k)
    (c : F.Site F.top × Fin 4) : Prop :=
  μ l c.1 c.2 ≠ 0 ∨ ∃ b : F.Site F.depth × Fin 4,
    (enclosingCell b.1 = c.1 ∨ enclosingCell b.1 = c.1 + unitStep F.top c.2) ∧ ParameterMovesBond ξ μ l b
def BlockFitAnalyticAlongTranslates : Prop :=
  ∀ L : ℕ, Odd L → ∃ C : ℕ → ℕ → ℝ, (∀ k j, 0 ≤ C k j) ∧
    ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (k : ℕ)
      (ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions)
      (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) (c : F.Site F.top × Fin 4),
      F.blockSide = L → (∀ i, 2 ≤ F.extent i) →
      (∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ 1 / (64 * (L : ℝ))) →
      AnalyticAt ℝ (fun σ : Fin k → ℝ => blockFit (translatedChart w V ξ μ σ) (translatedTop V μ σ) c) 0 ∧
      ((∀ l (b : F.Site F.depth × Fin 4), ‖ξ l b.1 b.2‖ ≤ 1) → (∀ l y i, ‖μ l y i‖ ≤ 1) →
        ∀ (j : ℕ) (v : Fin j → Fin k → ℝ), (∀ m, ‖v m‖ ≤ 1) →
          |iteratedFDeriv ℝ j (fun σ : Fin k → ℝ => blockFit (translatedChart w V ξ μ σ) (translatedTop V μ σ) c) 0 v| ≤ C k j) ∧
      ∀ σ σ' : Fin k → ℝ, (∀ l, ParameterTouchesBond ξ μ l c → σ l = σ' l) →
        blockFit (translatedChart w V ξ μ σ) (translatedTop V μ σ) c =
          blockFit (translatedChart w V ξ μ σ') (translatedTop V μ σ') c
end YangMills.Construction.ColdStepAtMirrorFrames
end

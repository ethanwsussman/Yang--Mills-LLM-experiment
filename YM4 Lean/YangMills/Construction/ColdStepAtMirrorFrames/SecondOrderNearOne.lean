import YangMills.Construction.ColdStepAtMirrorFrames.FunctionAlongAMove
import YangMills.Construction.ColdStepAtMirrorFrames.JetOfAFunctionOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def firstDerivGap {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {j : ℕ} {B : Finset (F.Site j × Fin 4)}
    (A A₀ : P → ↥B → imaginaryQuaternions) (u : P) : ℝ :=
  ∑ b, ‖iteratedFDeriv ℝ 1 (fun τ => A τ b) 0 ![u] - iteratedFDeriv ℝ 1 (fun τ => A₀ τ b) 0 ![u]‖
def SecondOrderNearCritical : Prop :=
  ∀ (F : BlockFrame) (j : ℕ) (B : Finset (F.Site j × Fin 4)) (G G₀ : F.GaugeField j → ℝ)
    (W W₀ : F.GaugeField j)
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (Wf Wf₀ : P → F.GaugeField j)
    (A A₀ : P → ↥B → imaginaryQuaternions)
    (d₀ Eg S Δ : ℝ) (u v : P),
    ContDiffThreeAlongBonds G W → ContDiffThreeAlongBonds G₀ W₀ →
    ContDiffAt ℝ 3 A 0 → A 0 = 0 → (∀ᶠ τ in 𝓝 (0 : P), Wf τ = leftTranslate (extendByZero (A τ)) W) →
    ContDiffAt ℝ 3 A₀ 0 → A₀ 0 = 0 → (∀ᶠ τ in 𝓝 (0 : P), Wf₀ τ = leftTranslate (extendByZero (A₀ τ)) W₀) →
    0 ≤ d₀ → 0 ≤ Eg → 0 ≤ S →
    (∀ (c : Fin 1 → ↥B) (X : Fin 1 → imaginaryQuaternions), AreUnitVectors X →
      |bondDeriv G W (fun l => (c l).1) X - bondDeriv G₀ W₀ (fun l => (c l).1) X| ≤ d₀) →
    (∀ (c : Fin 2 → ↥B) (X : Fin 2 → imaginaryQuaternions), AreUnitVectors X →
      |bondDeriv G W (fun l => (c l).1) X - bondDeriv G₀ W₀ (fun l => (c l).1) X| ≤ d₀) →
    (∀ (c : Fin 1 → ↥B) (X : Fin 1 → imaginaryQuaternions), AreUnitVectors X →
      bondDeriv G₀ W₀ (fun l => (c l).1) X = 0) →
    (∀ (c : Fin 2 → ↥B) (X : Fin 2 → imaginaryQuaternions), AreUnitVectors X →
      |bondDeriv G₀ W₀ (fun l => (c l).1) X| ≤ Eg) →
    ∑ b, firstDerivNorm A u b ≤ S → ∑ b, firstDerivNorm A v b ≤ S → ∑ b, firstDerivNorm A₀ v b ≤ S →
    ∑ b, firstDerivNorm A₀ u b ≤ S →
    ∑ b, secondDerivNorm A u v b ≤ S → firstDerivGap A A₀ u ≤ Δ → firstDerivGap A A₀ v ≤ Δ →
    |iteratedFDeriv ℝ 2 (fun τ => G (Wf τ)) 0 ![u, v] - iteratedFDeriv ℝ 2 (fun τ => G₀ (Wf₀ τ)) 0 ![u, v]| ≤
      d₀ * (S ^ 2 + S) + 2 * Eg * S * Δ ∧
    |iteratedFDeriv ℝ 1 (fun τ => G (Wf τ)) 0 ![u]| ≤ d₀ * S
end ColdStepAtMirrorFrames
end YangMills.Construction
end

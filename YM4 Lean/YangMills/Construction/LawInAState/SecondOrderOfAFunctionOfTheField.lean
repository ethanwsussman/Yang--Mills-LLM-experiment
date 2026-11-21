import YangMills.Construction.ClusterExpansionOfAStep.HessianOfAFamilyAtTheFlatField
import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.StateLaw
open TorusFields BlockAverages FlatHessian
variable {n : ℕ}
def expField (ξ : TorusBond n → imaginaryQuaternions) : TorusField n := fun x i => expUnit (ξ (x, i))
def flatHessian (u : TorusField n → ℝ) (b b' : TorusBond n) : ℝ :=
  mixedDeriv u (trivialField n) ![b, b'] ![quaternionI, quaternionI]
def colorPairing (ξ ξ' : TorusBond n → imaginaryQuaternions) (b b' : TorusBond n) : ℝ :=
  ∑ e : Fin 3, imaginaryComponent e (ξ b) * imaginaryComponent e (ξ' b')
def latticeGradient (φ : TorusSite n → ℝ) (b : TorusBond n) : ℝ := φ (b.1 + TorusFields.unitStep n b.2) - φ b.1
structure IsRegularObservable (σ E E₃ : ℝ) (w : ℕ → ℝ) (y : TorusSite n) (u : TorusField n → ℝ) : Prop where
  contDiff : ∀ W : TorusField n, IsCold σ W → ContDiffThreeAt u W
  gauge_invariant : ∀ (g : TorusSite n → UnitQuaternion) (W : TorusField n), IsCold σ W → u (gaugeTransform g W) = u W
  deriv_bound : ∀ W : TorusField n, IsCold σ W → ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
    1 ≤ k → k ≤ 3 → AreUnitVectors X → |mixedDeriv u W c X| ≤ (if k = 3 then E₃ else E) / w (supportDiam y c)
def secondOrderExpansionStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (σ E E₃ : ℝ) (w : ℕ → ℝ) (y : TorusSite n) (u : TorusField n → ℝ), 0 < σ → (∀ m, 0 < w m) → 0 ≤ E₃ →
    IsRegularObservable σ E E₃ w y u →
    (∀ b b' : TorusBond n, flatHessian u b b' = flatHessian u b' b) ∧
    (∀ b b' : TorusBond n, |flatHessian u b b'| ≤ E / w (supportDiam y ![b, b'])) ∧
    (∀ (φ : TorusSite n → ℝ) (b' : TorusBond n), ∑ b, latticeGradient φ b * flatHessian u b b' = 0) ∧
    ∀ ξ : TorusBond n → imaginaryQuaternions, (∀ b, ‖(ξ b : ℍ[ℝ])‖ ≤ σ / 16) →
      |u (expField ξ) - u (trivialField n) - (1 / 2) * ∑ b, ∑ b', flatHessian u b b' * colorPairing ξ ξ b b'| ≤
        27 * E₃ * ∑ f : Fin 3 → TorusBond n, (∏ i, ‖(ξ (f i) : ℍ[ℝ])‖) / w (supportDiam y f)
end YangMills.Construction.StateLaw
end

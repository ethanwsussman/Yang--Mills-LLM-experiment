import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
namespace YangMills.Construction.ColdStepAtMirrorFrames
def TopFamilyOnTori : Prop :=
  ∀ (L t n₀ : ℕ) (s : ℝ) (g : TopLevelFamily), 0 < n₀ →
    (IsLocalDensity L t n₀ s g →
      (∀ n [NeZero n], n₀ ≤ n → ∀ (y : TorusSite n) (V : TorusField n), IsCold s V →
        ContDiffThreeAt (densityOfTopFamily L t g n y) V) ∧
      (∀ n [NeZero n], n₀ ≤ n → ∀ (y : TorusSite n) (γ : TorusSite n → UnitQuaternion) (V : TorusField n),
        IsCold s V →
        densityOfTopFamily L t g n y (gaugeTransform γ V) = densityOfTopFamily L t g n y V) ∧
      (∀ n [NeZero n], n₀ ≤ n → ∀ (y u : TorusSite n) (V : TorusField n), IsCold s V →
        densityOfTopFamily L t g n y (TorusFields.translate u V) = densityOfTopFamily L t g n (y + u) V)) ∧
    (∀ e : ℕ → ℕ → ℝ, DerivDecay L t n₀ s g e →
      ∀ n [NeZero n], n₀ ≤ n → ∀ (y : TorusSite n) (V : TorusField n), IsCold s V →
        ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
          AreUnitVectors X →
          |mixedDeriv (densityOfTopFamily L t g n y) V c X| ≤ e k (supportDiam y c)) ∧
    (∀ e : ℕ → ℝ, IsLocalOnTori L t n₀ s g e →
      ∀ n n' [NeZero n] [NeZero n'], n₀ ≤ n → n₀ ≤ n' →
        ∀ (y : TorusSite n) (y' : TorusSite n') (V : TorusField n) (V' : TorusField n') (m : ℕ),
          2 * m + 2 < n → 2 * m + 2 < n' →
          IsCold s V → IsCold s V' → FieldsAgreeNear V V' y y' m →
          ∀ (k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
            (∀ l, YangMills.Construction.TorusFields.BondOffsetInBox m (h l)) → AreUnitVectors X →
            |mixedDeriv (densityOfTopFamily L t g n y) V (fun l => bondFrom y (h l)) X -
              mixedDeriv (densityOfTopFamily L t g n' y') V' (fun l => bondFrom y' (h l)) X| ≤ e m) ∧
    (∀ (n : ℕ) [NeZero n] (y : TorusSite n) (V : TorusField n),
      densityOfTopFamily L t (centredFamily g) n y V = centered (densityOfTopFamily L t g) n y V) ∧
    ∀ (n : ℕ) [NeZero n] (b b' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
      secondDerivAtUniform g L t n b b' X X' =
        mixedDeriv (densityOfTopFamily L t g n 0) (trivialField n) ![bondFrom 0 b, bondFrom 0 b'] ![X, X']
end YangMills.Construction.ColdStepAtMirrorFrames
end

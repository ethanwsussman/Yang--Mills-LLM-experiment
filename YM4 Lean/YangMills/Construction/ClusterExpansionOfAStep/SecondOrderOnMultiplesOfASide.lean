import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderAtAbelianFields
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
variable {n : ℕ}
structure IsCurvatureFamilyOnMultiples (ℓ : StepParameters) (d : ℕ) (C : ℝ) (h : LocalDensity) : Prop where
  smooth : ∀ n [NeZero n], ℓ.n₀ ≤ n → d ∣ n → ∀ (y : TorusSite n) (W : TorusField n),
    IsCold ℓ.threshold W → ContDiffThreeAt (h n y) W
  gauge : ∀ n [NeZero n], ℓ.n₀ ≤ n → d ∣ n → ∀ (y : TorusSite n) (g : TorusSite n → UnitQuaternion)
    (W : TorusField n), IsCold ℓ.threshold W → h n y (gaugeTransform g W) = h n y W
  translation : ∀ n [NeZero n], ℓ.n₀ ≤ n → d ∣ n → ∀ (y u : TorusSite n) (W : TorusField n),
    IsCold ℓ.threshold W → h n y (TorusFields.translate u W) = h n (y + u) W
  decay : ∀ n [NeZero n], ℓ.n₀ ≤ n → d ∣ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
      |mixedDeriv (h n y) W c X| ≤ C / ℓ.weight (supportDiam y c)
  local_density : ∀ n n' [NeZero n] [NeZero n'], ℓ.n₀ ≤ n → ℓ.n₀ ≤ n' → d ∣ n → d ∣ n' →
    ∀ (y : TorusSite n) (y' : TorusSite n') (W : TorusField n) (W' : TorusField n') (m : ℕ),
      2 * m + 2 < n → 2 * m + 2 < n' →
      IsCold ℓ.threshold W → IsCold ℓ.threshold W' → FieldsAgreeNear W W' y y' m →
      ∀ (k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
        (∀ l, BondOffsetInBox m (b l)) → AreUnitVectors X →
        |mixedDeriv (centered h n y) W (fun l => bondFrom y (b l)) X -
            mixedDeriv (centered h n' y') W' (fun l => bondFrom y' (b l)) X| ≤ C / ℓ.weight m
def flatSecondDeriv (h : LocalDensity) (n : ℕ) (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions) : ℝ :=
  mixedDeriv (h n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X']
def secondDerivLimitOnMultiples (d : ℕ) (h : LocalDensity) (c c' : (Fin 4 → ℤ) × Fin 4)
    (X X' : imaginaryQuaternions) : ℝ :=
  Filter.limUnder Filter.atTop fun m : ℕ => flatSecondDeriv h (d * m) c c' X X'
def SecondOrderOnMultiplesOfSide : Prop :=
  ∀ ℓ : StepParameters, ℓ.Admissible → ∀ d : ℕ, 0 < d → ∀ (C : ℝ) (h : LocalDensity),
    IsCurvatureFamilyOnMultiples ℓ d C h →
    (∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
      Filter.Tendsto (fun m : ℕ => flatSecondDeriv h (d * m) c c' X X') Filter.atTop
        (nhds (secondDerivLimitOnMultiples d h c c' X X'))) ∧
    (∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
      |secondDerivLimitOnMultiples d h c c' X X'| ≤
        ‖X‖ * ‖X'‖ * (C / ℓ.weight (offsetTriangleDiameter c.1 c'.1))) ∧
    (∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
      secondDerivLimitOnMultiples d h c c' X X' = secondDerivLimitOnMultiples d h c' c X' X) ∧
    (∀ B B' : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions, HasPolynomialGrowth B → HasPolynomialGrowth B' →
      Summable fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        secondDerivLimitOnMultiples d h cc.1 cc.2 (B cc.1) (B' cc.2)) ∧
    (∀ A A' : Fin 4 → Fin 4 → imaginaryQuaternions, (∀ i j, A i j = - A j i) → (∀ i j, A' i j = - A' j i) →
      Summable fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        secondDerivLimitOnMultiples d h cc.1 cc.2 (linearPotential A cc.1) (linearPotential A' cc.2)) ∧
    (∀ (φ : (Fin 4 → ℤ) → imaginaryQuaternions) (B' : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
      (∃ (K : ℝ) (p : ℕ), ∀ z, ‖φ z‖ ≤ K * (1 + (offsetSupNorm z : ℝ)) ^ p) → HasPolynomialGrowth B' →
      HasSum (fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        secondDerivLimitOnMultiples d h cc.1 cc.2 (discreteGradient φ cc.1) (B' cc.2)) 0) ∧
    (∀ ω : Fin 4 → Fin 4 → ℝ, (∀ i j, ω i j = - ω j i) → ∀ ε : ℝ, 0 < ε → ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ < γ₀ → ∀ (n : ℕ) [NeZero n], d ∣ n → 4 * Real.log (1 / γ) ^ 2 + 4 < n →
        ∀ (X : imaginaryQuaternions) (V : TorusField n) (B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
          ‖X‖ = 1 → IsAbelianWithCurvature X ω γ V →
          ColdStepAtMirrorFrames.IsLinearPotential (curvatureAlong X ω) B → ∀ Y : TorusSite n,
            |centered h n Y V - γ ^ 2 / 2 *
                ∑' cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4),
                  secondDerivLimitOnMultiples d h cc.1 cc.2 (B cc.1) (B cc.2)| ≤ ε * γ ^ 2) ∧
    ∀ (ω : Fin 4 → Fin 4 → ℝ) (l : ℕ) (X : imaginaryQuaternions), (∀ i j, ω i j = - ω j i) → 0 < l →
      (∀ i j, ∃ k : ℤ, (l : ℝ) * ω i j = k) → ‖X‖ = 1 →
      ∃ v : ℝ,
        HasSum (fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
          secondDerivLimitOnMultiples d h cc.1 cc.2 (linearPotential (curvatureAlong X ω) cc.1)
            (linearPotential (curvatureAlong X ω) cc.2)) v ∧
        ∀ ε : ℝ, 0 < ε → ∃ n₁ : ℕ, ∀ (n : ℕ) [NeZero n], n₁ ≤ n → d ∣ n → ∀ V : TorusField n,
          IsAbelianWithCurvature X ω (2 * Real.pi * l / (n : ℝ) ^ 2) V → ∀ Y : TorusSite n,
            |centered h n Y V - (2 * Real.pi * l / (n : ℝ) ^ 2) ^ 2 / 2 * v| ≤
              ε * (2 * Real.pi * l / (n : ℝ) ^ 2) ^ 2
end YangMills.Construction.TorusLumps
end

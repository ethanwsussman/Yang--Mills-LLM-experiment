import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
variable {n : ℕ}
structure IsCurvatureFamily (ℓ : StepParameters) (C : ℝ) (h : LocalDensity) : Prop where
  smooth : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
    ContDiffThreeAt (h n y) W
  gauge : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (g : TorusSite n → UnitQuaternion) (W : TorusField n),
    IsCold ℓ.threshold W → h n y (gaugeTransform g W) = h n y W
  translation : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y u : TorusSite n) (W : TorusField n),
    IsCold ℓ.threshold W → h n y (TorusFields.translate u W) = h n (y + u) W
  decay : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
      |mixedDeriv (h n y) W c X| ≤ C / ℓ.weight (supportDiam y c)
  local_density : ∀ n n' [NeZero n] [NeZero n'], ℓ.n₀ ≤ n → ℓ.n₀ ≤ n' →
    ∀ (y : TorusSite n) (y' : TorusSite n') (W : TorusField n) (W' : TorusField n') (m : ℕ),
      2 * m + 2 < n → 2 * m + 2 < n' →
      IsCold ℓ.threshold W → IsCold ℓ.threshold W' → FieldsAgreeNear W W' y y' m →
      ∀ (k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
        (∀ l, BondOffsetInBox m (b l)) → AreUnitVectors X →
        |mixedDeriv (centered h n y) W (fun l => bondFrom y (b l)) X -
            mixedDeriv (centered h n' y') W' (fun l => bondFrom y' (b l)) X| ≤ C / ℓ.weight m
def SumInvariantUnderIsometries (ℓ : StepParameters) (h : LocalDensity) : Prop :=
  ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (g : TorusIsometry) (W W' : TorusField n), IsCold ℓ.threshold W →
    IsCold ℓ.threshold W' → g.Transports W W' → ∑ y, centered h n y W' = ∑ y, centered h n y W
def curvatureAlong (X : imaginaryQuaternions) (ω : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → imaginaryQuaternions :=
  fun i j => ω i j • X
def IsAbelianWithCurvature (X : imaginaryQuaternions) (ω : Fin 4 → Fin 4 → ℝ) (γ : ℝ) (V : TorusField n) : Prop :=
  (∃ θ : TorusSite n → Fin 4 → ℝ, ∀ x i, V x i = expUnit (θ x i • X)) ∧
    ∀ x i j, i < j → holonomy V x i j = expUnit ((γ * ω i j) • X)
def curvaturePairing (A A' : Fin 4 → Fin 4 → imaginaryQuaternions) : ℝ :=
  ∑ i, ∑ j, if i < j then inner ℝ (A i j : ℍ[ℝ]) (A' i j : ℍ[ℝ]) else 0
def planeAngle (g : ℝ) (i j : Fin 4) (x : TorusSite n) (k : Fin 4) : ℝ :=
  if k = j then g * ((x i).val : ℝ)
  else if k = i ∧ (x i).val + 1 = n then -g * (n : ℝ) * ((x j).val : ℝ) else 0
def totalAngle (γ : ℝ) (ω : Fin 4 → Fin 4 → ℝ) (x : TorusSite n) (k : Fin 4) : ℝ :=
  ∑ i, ∑ j, if i < j then planeAngle (γ * ω i j) i j x k else 0
def abelianFieldOfAngles (n : ℕ) (X : imaginaryQuaternions) (γ : ℝ) (ω : Fin 4 → Fin 4 → ℝ) : TorusField n :=
  fun x k => expUnit (totalAngle γ ω x k • X)
end YangMills.Construction.TorusLumps
end

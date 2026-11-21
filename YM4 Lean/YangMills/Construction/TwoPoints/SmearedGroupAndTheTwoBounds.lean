import YangMills.Construction.TwoPoints.TransformsOnTheLineAndTheirAlgebra
import Mathlib
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace YangMills.Construction.TwoPoints.LineTransforms
open YangMills.Construction.SpectralCalculus (IsCommutingSemigroupGroup IsPositiveBounded IsSymmetricBounded)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
def IsSmearing (V : ℝ → E →L[ℂ] E) (f : ℝ → ℂ) (A : E →L[ℂ] E) : Prop :=
  ∀ x y, inner ℂ x (A y) = lebesgueIntegral fun s : ℝ => f s * inner ℂ x (V s y)
def smear (V : ℝ → E →L[ℂ] E) (f : ℝ → ℂ) : E →L[ℂ] E :=
  Classical.epsilon (IsSmearing V f)
def transformSum (τ : ℝ≥0) (N : ℕ) (f : ℕ → ℝ → ℂ) (p : UnitStrip) : ℂ :=
  ∑ j ∈ Finset.range (N + 1), (intervalRpow ((j : ℝ≥0) * τ) p.1 : ℂ) * lineTransform (f j) p.2
def smearedSum (P : ℝ≥0 → E →L[ℂ] E) (V : ℝ → E →L[ℂ] E) (τ : ℝ≥0) (N : ℕ)
    (f : ℕ → ℝ → ℂ) : E →L[ℂ] E :=
  ∑ j ∈ Finset.range (N + 1), P ((j : ℝ≥0) * τ) * smear V (f j)
def convSquare (N : ℕ) (f : ℕ → ℝ → ℂ) (i : ℕ) : ℝ → ℂ :=
  ∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun p => p.1 + p.2 = i),
    convolve (reflectConj (f p.1)) (f p.2)
structure MatrixCoeffsContinuous (P : ℝ≥0 → E →L[ℂ] E) (V : ℝ → E →L[ℂ] E) : Prop where
  inner_group_left : ∀ (x y : E) (s : ℝ), inner ℂ (V s x) y = inner ℂ x (V (-s) y)
  continuous_semigroup : ∀ y : E, Continuous fun t : ℝ≥0 => P t y
  continuous_group : ∀ y : E, Continuous fun s : ℝ => V s y
  continuous_inner : ∀ x y : E, Continuous fun p : ℝ≥0 × ℝ => inner ℂ x (P p.1 (V p.2 y))
  norm_inner_le : ∀ (x y : E) (t : ℝ≥0) (s : ℝ), ‖inner ℂ x (P t (V s y))‖ ≤ ‖x‖ * ‖y‖
structure SmearingCalculus [CompleteSpace E] (V : ℝ → E →L[ℂ] E) : Prop where
  existsUnique : ∀ f ∈ c1Functions, ∃! A : E →L[ℂ] E, IsSmearing V f A
  isSmearing : ∀ f ∈ c1Functions, IsSmearing V f (smear V f)
  linear : ∀ f ∈ c1Functions, ∀ h ∈ c1Functions, ∀ a : ℂ,
    smear V (f + a • h) = smear V f + a • smear V h
  norm_le : ∀ f ∈ c1Functions, ‖smear V f‖ ≤ l1Norm f
  inner_left : ∀ f ∈ c1Functions, ∀ x y : E,
    inner ℂ (smear V f x) y = inner ℂ x (smear V (reflectConj f) y)
  mul : ∀ f ∈ c1Functions, ∀ h ∈ c1Functions,
    smear V f * smear V h = smear V (convolve f h)
  commute : ∀ A : E →L[ℂ] E, IsSymmetricBounded A → (∀ s, Commute A (V s)) →
    ∀ f ∈ c1Functions, Commute A (smear V f)
def SmearBoundedByTransform [CompleteSpace E] (V : ℝ → E →L[ℂ] E) : Prop :=
  ∀ D : E →L[ℂ] E, IsPositiveBounded D → (∀ s, Commute D (V s)) →
    ∀ f ∈ c1Functions, ∀ y : E,
      ‖inner ℂ y (D (smear V f y))‖ ≤
        TestFunctions.uniformNorm (lineTransform f) * (inner ℂ y (D y)).re
structure SmearedSumBounds (P : ℝ≥0 → E →L[ℂ] E) (V : ℝ → E →L[ℂ] E) (τ : ℝ≥0) (N : ℕ)
    (f : ℕ → ℝ → ℂ) : Prop where
  norm_inner_le : ∀ y : E, ‖inner ℂ y (smearedSum P V τ N f y)‖ ≤
    TestFunctions.uniformNorm (transformSum τ N f) * ‖y‖ ^ 2
  norm_le : ∀ y : E, ‖smearedSum P V τ N f y‖ ≤
    TestFunctions.uniformNorm (transformSum τ N f) * ‖y‖
  convSquare_mem : ∀ i ≤ 2 * N, convSquare N f i ∈ c1Functions
  norm_sq : ∀ y : E, ((‖smearedSum P V τ N f y‖ ^ 2 : ℝ) : ℂ) =
    inner ℂ y (smearedSum P V τ (2 * N) (convSquare N f) y)
  transformSum_convSquare : ∀ p : UnitStrip, transformSum τ (2 * N) (convSquare N f) p =
    ((‖transformSum τ N f p‖ ^ 2 : ℝ) : ℂ)
def SmearedPairBounds : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : ℝ≥0 → E →L[ℂ] E) (V : ℝ → E →L[ℂ] E), IsCommutingSemigroupGroup P V →
    MatrixCoeffsContinuous P V ∧ SmearingCalculus V ∧ SmearBoundedByTransform V ∧
      ∀ (τ : ℝ≥0) (N : ℕ) (f : ℕ → ℝ → ℂ), 0 < τ → (∀ j ≤ N, f j ∈ c1Functions) →
        SmearedSumBounds P V τ N f
end YangMills.Construction.TwoPoints.LineTransforms

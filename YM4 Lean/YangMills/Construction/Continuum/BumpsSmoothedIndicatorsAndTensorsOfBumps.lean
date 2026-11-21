import YangMills.Construction.TestSpaces.PointsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction
namespace TestSpaces
namespace BumpApprox
def IsStandardBump {n : ℕ} (j : PointTuple n → ℝ) : Prop :=
  j ∈ smoothCompactSupp Set.univ ∧ (∀ x, 0 ≤ j x) ∧
    (∀ x, 1 ≤ tupleNorm x → j x = 0) ∧ ∫ x, j x = 1
def IsStandardBumpR4 (j₁ : (Fin 4 → ℝ) → ℝ) : Prop :=
  IsStandardBump (n := 1) fun x => j₁ (x 0)
def mollifierKernel {n : ℕ} (j : PointTuple n → ℝ) (ε : ℝ) (x z : PointTuple n) : ℝ :=
  (ε ^ (4 * n))⁻¹ * j (ε⁻¹ • (x - z))
def regularizedIndicator {n : ℕ} (j : PointTuple n → ℝ) (Z : Set (PointTuple n)) (ε : ℝ)
    (x : PointTuple n) : ℝ :=
  ∫ z in Z, mollifierKernel j ε x z
def derivL1Mass {n : ℕ} (j : PointTuple n → ℝ) (γ : MultiIdx4 n) : ℝ :=
  ∫ x, |multiDeriv γ j x|
def rescaledBump (j₁ : (Fin 4 → ℝ) → ℝ) (ε : ℝ) (v u : Fin 4 → ℝ) : ℝ :=
  (ε ^ 4)⁻¹ * j₁ (ε⁻¹ • (u - v))
def latticeGrid (n : ℕ) (h : ℝ) : Set (PointTuple n) :=
  {z | ∃ m : Fin n → Fin 4 → ℤ, ∀ i μ, z i μ = h * m i μ}
def gridSummand {n : ℕ} (j₁ : (Fin 4 → ℝ) → ℝ) (φ : PointTuple n → ℂ) (ε h : ℝ)
    (z : PointTuple n) : PointTuple n → ℂ :=
  fun x => ((h ^ (4 * n) : ℝ) : ℂ) * φ z * ((tensorProd (fun i => rescaledBump j₁ ε (z i)) x : ℝ) : ℂ)
def gridApprox {n : ℕ} (j₁ : (Fin 4 → ℝ) → ℝ) (φ : PointTuple n → ℂ) (ε h : ℝ) :
    PointTuple n → ℂ :=
  ∑ᶠ z ∈ latticeGrid n h, gridSummand j₁ φ ε h z
def RegularizedIndicatorProps {n : ℕ} (j : PointTuple n → ℝ) (Z : Set (PointTuple n)) (ε : ℝ) :
    Prop :=
  (∀ x, IntegrableOn (mollifierKernel j ε x) Z) ∧
  ContDiff ℝ ∞ (regularizedIndicator j Z ε) ∧
  (∀ x, 0 ≤ regularizedIndicator j Z ε x ∧ regularizedIndicator j Z ε x ≤ 1) ∧
  (∀ x, {z | tupleNorm (z - x) < ε} ⊆ Z → regularizedIndicator j Z ε x = 1) ∧
  (∀ x, {z | tupleNorm (z - x) < ε} ∩ Z = ∅ → regularizedIndicator j Z ε x = 0) ∧
  ∀ γ : MultiIdx4 n, Integrable (fun x => |multiDeriv γ j x|) ∧
    ∀ x, |multiDeriv γ (regularizedIndicator j Z ε) x| ≤
      derivL1Mass j γ * (ε ^ idxOrder γ)⁻¹
def TensorBumpApproximation (n : ℕ) : Prop :=
  ∀ φ : PointTuple n → ℂ, φ ∈ smoothCompactSupp Set.univ → ∀ (p : ℕ) (ϵ : ℝ), 0 < ϵ →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ j₁ : (Fin 4 → ℝ) → ℝ, IsStandardBumpR4 j₁ →
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ∃ h : ℝ, 0 < h ∧
        {z | z ∈ latticeGrid n h ∧ gridSummand j₁ φ ε h z ≠ 0}.Finite ∧
        derivSupNorm p (φ - gridApprox j₁ φ ε h) ≤ ENNReal.ofReal ϵ
def BumpLemma : Prop :=
  ∀ n : ℕ, 0 < n →
    (∃ j : PointTuple n → ℝ, IsStandardBump j) ∧
    (∀ j : PointTuple n → ℝ, IsStandardBump j → ∀ Z : Set (PointTuple n), MeasurableSet Z →
      ∀ ε : ℝ, 0 < ε → RegularizedIndicatorProps j Z ε) ∧
    (∀ j₁ : (Fin 4 → ℝ) → ℝ, IsStandardBumpR4 j₁ → ∀ (ε : ℝ) (v : Fin 4 → ℝ), 0 < ε →
      rescaledBump j₁ ε v ∈ smoothCompactSupp Set.univ ∧
      tsupport (rescaledBump j₁ ε v) ⊆ {u | TorusMetric.euclidNormVec (u - v) ≤ ε}) ∧
    TensorBumpApproximation n
end BumpApprox
end TestSpaces
end YangMills.Construction

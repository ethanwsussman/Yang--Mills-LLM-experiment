import YangMills.Construction.Towers.DifferentialsOfRealAnalyticMaps
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.CriticalSecondDeriv
open Matrices Tower Tower.AnalyticDifferentials
variable {L n k j : ℕ}
def EntriesDifferentiableOn (I : Set ℝ) (γ : ℝ → Edge L n k j → ComplexMatrix2) : Prop :=
  IsOpenIntervalAroundZero I ∧ MapsTo γ I (fieldSpace L n k j) ∧
    ∀ e : Edge L n k j, PeriodicLattice.Bond.IsPositivelyOriented e → ∀ r c : Fin 2, ∀ t ∈ I,
      DifferentiableAt ℝ (fun u => γ u e r c) t
def EntrywiseDifferentiableCurves (L n k j : ℕ) : Prop :=
  ∀ (I : Set ℝ) (γ : ℝ → Edge L n k j → ComplexMatrix2), EntriesDifferentiableOn I γ →
    IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ
def IsRealCriticalPoint (N : Set (Edge L n k j → ComplexMatrix2)) (F : (Edge L n k j → ComplexMatrix2) → ℂ)
    (U₀ : Edge L n k j → ComplexMatrix2) : Prop :=
  U₀ ∈ fieldSpace L n k j ∧ U₀ ∈ N ∧ IsAnalyticComplexFieldFunction N F ∧
    (∀ V ∈ N, (F V).im = 0) ∧ leftGradient N F U₀ = 0
def IsSmoothTwoParamFamily (U₀ : Edge L n k j → ComplexMatrix2) (O : Set (ℝ × ℝ))
    (W : ℝ × ℝ → Edge L n k j → ComplexMatrix2) : Prop :=
  IsOpen O ∧ ((0 : ℝ), (0 : ℝ)) ∈ O ∧ MapsTo W O (fieldSpace L n k j) ∧ W (0, 0) = U₀ ∧
    ∀ e : Edge L n k j, PeriodicLattice.Bond.IsPositivelyOriented e → ∀ r c : Fin 2,
      ContDiffOn ℝ ∞ (fun p => W p e r c) O
def MixedPartialsEqHessian (N : Set (Edge L n k j → ComplexMatrix2))
    (F : (Edge L n k j → ComplexMatrix2) → ℂ) (U₀ : Edge L n k j → ComplexMatrix2) : Prop :=
  ∀ (O : Set (ℝ × ℝ)) (W : ℝ × ℝ → Edge L n k j → ComplexMatrix2), IsSmoothTwoParamFamily U₀ O W →
    (∃ O' : Set (ℝ × ℝ), IsOpen O' ∧ ((0 : ℝ), (0 : ℝ)) ∈ O' ∧ MapsTo W O' N ∧
      ContDiffOn ℝ ∞ (fun p => F (W p)) O') ∧
    deriv (fun s : ℝ => deriv (fun t : ℝ => F (W (s, t))) 0) 0 =
      leftSecondDeriv F U₀ (curveTangent fun s => W (s, 0)) (curveTangent fun t => W (0, t)) ∧
    deriv (fun t : ℝ => deriv (fun s : ℝ => F (W (s, t))) 0) 0 =
      leftSecondDeriv F U₀ (curveTangent fun s => W (s, 0)) (curveTangent fun t => W (0, t))
def IsSmoothCurveAt (U₀ : Edge L n k j → ComplexMatrix2) (I : Set ℝ)
    (γ : ℝ → Edge L n k j → ComplexMatrix2) : Prop :=
  IsOpenIntervalAroundZero I ∧ MapsTo γ I (fieldSpace L n k j) ∧ γ 0 = U₀ ∧
    ∀ e : Edge L n k j, PeriodicLattice.Bond.IsPositivelyOriented e → ∀ r c : Fin 2,
      ContDiffOn ℝ ∞ (fun t => γ t e r c) I
def HasGradientDerivAlong (N : Set (Edge L n k j → ComplexMatrix2))
    (F : (Edge L n k j → ComplexMatrix2) → ℂ) (γ : ℝ → Edge L n k j → ComplexMatrix2)
    (D : Edge L n k j → ComplexMatrix2) : Prop :=
  ∀ e : Edge L n k j, HasDerivAt (fun t => leftGradient N F (γ t) e) (D e) 0
def PairsAsHessian (F : (Edge L n k j → ComplexMatrix2) → ℂ)
    (U₀ B₁ D : Edge L n k j → ComplexMatrix2) : Prop :=
  ∀ B' ∈ edgeFormSpace L n k j, edgeFormPairing D B' = leftSecondDeriv F U₀ B₁ B'
def GradientDerivAlongCurves (N : Set (Edge L n k j → ComplexMatrix2))
    (F : (Edge L n k j → ComplexMatrix2) → ℂ) (U₀ : Edge L n k j → ComplexMatrix2) : Prop :=
  ∀ (I : Set ℝ) (γ : ℝ → Edge L n k j → ComplexMatrix2), IsSmoothCurveAt U₀ I γ →
    (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ N ∧ HasLeftGradientAt N F (γ t)) ∧
    (∀ B' ∈ edgeFormSpace L n k j,
      HasDerivAt (fun t => edgeFormPairing (leftGradient N F (γ t)) B')
        (leftSecondDeriv F U₀ (curveTangent γ) B') 0) ∧
    ∃ D ∈ edgeFormSpace L n k j, HasGradientDerivAlong N F γ D ∧
      PairsAsHessian F U₀ (curveTangent γ) D ∧
      ∀ D' ∈ edgeFormSpace L n k j, PairsAsHessian F U₀ (curveTangent γ) D' → D' = D
def HessianOfComp (j' : ℕ) (F : (Edge L n k j → ComplexMatrix2) → ℂ)
    (U₀ : Edge L n k j → ComplexMatrix2) : Prop :=
  ∀ (W : Set (Edge L n k j' → ComplexMatrix2)) (p : (Edge L n k j' → ComplexMatrix2) → Edge L n k j → ComplexMatrix2)
    (U : Edge L n k j' → ComplexMatrix2), U ∈ W → IsAnalyticFieldMap W p → p U = U₀ →
    ∀ B ∈ edgeFormSpace L n k j', ∀ B' ∈ edgeFormSpace L n k j',
      leftSecondDeriv (F ∘ p) U B B' =
        leftSecondDeriv F U₀ (leftDifferential p U B) (leftDifferential p U B')
def HessianAtCriticalPoint : Prop :=
  ∀ L n k j j' : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k → j' ≤ k →
    EntrywiseDifferentiableCurves L n k j ∧
    EntrywiseDifferentiableCurves L n k j' ∧
    ∀ (N : Set (Edge L n k j → ComplexMatrix2)) (F : (Edge L n k j → ComplexMatrix2) → ℂ)
      (U₀ : Edge L n k j → ComplexMatrix2), IsRealCriticalPoint N F U₀ →
      MixedPartialsEqHessian N F U₀ ∧ GradientDerivAlongCurves N F U₀ ∧
        HessianOfComp j' F U₀
end YangMills.Construction.Tower.CriticalSecondDeriv
end

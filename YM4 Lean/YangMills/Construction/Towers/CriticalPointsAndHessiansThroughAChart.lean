import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Geometry
namespace CurveData
variable {X T K : Type} [AddCommGroup T] [Module ℝ T] [NormedAddCommGroup K] [NormedSpace ℝ K]
structure IsChartedBy (R : CurveData X T) (N : Set X) (O : Set K) (φ : K → X) (r : X → K)
    (D : K → K →ₗ[ℝ] T) : Prop where
  isOpen_domain : IsOpen O
  mapsTo_param : MapsTo φ O N
  coord_mem : ∀ p ∈ N, r p ∈ O
  param_coord : ∀ p ∈ N, φ (r p) = p
  coord_param : ∀ x ∈ O, r (φ x) = x
  isInterval : ∀ (I : Set ℝ) (γ : ℝ → X), R.IsCurve I γ → Tower.IsOpenIntervalAroundZero I
  coord_differentiableOn : ∀ (I : Set ℝ) (γ : ℝ → X), R.IsCurve I γ → MapsTo γ I N →
    DifferentiableOn ℝ (fun t => r (γ t)) I
  twice_coord : ∀ (I : Set ℝ) (γ : ℝ → X), R.IsTwiceDiffCurve I γ → R.IsCurve I γ ∧
    (MapsTo γ I N → DifferentiableOn ℝ (deriv fun t => r (γ t)) I)
  param_isCurve : ∀ (I : Set ℝ) (x : ℝ → K), Tower.IsOpenIntervalAroundZero I →
    DifferentiableOn ℝ x I → MapsTo x I O → R.IsCurve I fun t => φ (x t)
  param_isTwiceDiffCurve : ∀ (I : Set ℝ) (x : ℝ → K), Tower.IsOpenIntervalAroundZero I →
    DifferentiableOn ℝ x I → DifferentiableOn ℝ (deriv x) I → MapsTo x I O →
    R.IsTwiceDiffCurve I fun t => φ (x t)
  tangent_eq : ∀ (I : Set ℝ) (γ : ℝ → X), R.IsCurve I γ → MapsTo γ I N →
    R.tangent γ = D (r (γ 0)) (deriv (fun t => r (γ t)) 0)
  injective_diff : ∀ x ∈ O, Function.Injective (D x)
end CurveData
def ChartedCriticalPoints.Statement : Prop :=
  ∀ (X T K : Type) [AddCommGroup T] [Module ℝ T] [NormedAddCommGroup K] [NormedSpace ℝ K]
    (R : CurveData X T) (N : Set X) (O : Set K) (φ : K → X) (r : X → K) (D : K → K →ₗ[ℝ] T)
    (F : X → ℝ),
    R.IsChartedBy N O φ r D → ContDiffOn ℝ 2 (fun x => F (φ x)) O → ∀ x ∈ O,
      (R.IsCriticalOn N F (φ x) ↔ fderiv ℝ (fun x => F (φ x)) x = 0) ∧
      (fderiv ℝ (fun x => F (φ x)) x = 0 →
        (∀ h : K, h ≠ 0 → 0 < fderiv ℝ (fderiv ℝ fun x => F (φ x)) x h h) →
        (R.hessianForm (S := R.tangentSpan N (φ x)) Subtype.val N F (φ x)).PosDef)
end YangMills.Construction.Geometry
end

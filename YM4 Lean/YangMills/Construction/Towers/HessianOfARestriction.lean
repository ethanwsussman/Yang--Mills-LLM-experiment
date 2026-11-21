import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace YangMills.Construction
namespace Geometry.CurveData
variable {X T : Type} [AddCommGroup T] [Module ℝ T] (R : CurveData X T)
structure HessianViaParametrization {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (N : Set X) (F : X → ℝ) (φ : P → X) (z : P) (D : P →ₗ[ℝ] T) : Prop where
  injective : Function.Injective D
  range_eq : LinearMap.range D = R.tangentSpan N (φ z)
  isCriticalOn_iff : R.IsCriticalOn N F (φ z) ↔ fderiv ℝ (F ∘ φ) z = 0
  secondDeriv_eq : R.IsCriticalOn N F (φ z) →
    ∀ (I : Set ℝ) (γ : ℝ → X) (h : P), R.IsTwiceDiffCurve I γ → MapsTo γ I N →
      γ 0 = φ z → R.tangent γ = D h →
      deriv (deriv fun t => F (γ t)) 0 = fderiv ℝ (fderiv ℝ (F ∘ φ)) z h h
  exists_curve : R.IsCriticalOn N F (φ z) → ∀ v ∈ R.tangentSpan N (φ z),
    ∃ (I : Set ℝ) (γ : ℝ → X), R.IsTwiceDiffCurve I γ ∧ MapsTo γ I N ∧ γ 0 = φ z ∧
      R.tangent γ = v
  existsUnique_isHessianFormAt : R.IsCriticalOn N F (φ z) →
    ∃! Q : R.tangentSpan N (φ z) → ℝ, R.IsHessianFormAt Subtype.val N F (φ z) Q
  hessianForm_isHessianFormAt : R.IsCriticalOn N F (φ z) →
    R.IsHessianFormAt Subtype.val N F (φ z)
      (R.hessianForm (S := R.tangentSpan N (φ z)) Subtype.val N F (φ z))
  hessianForm_apply : R.IsCriticalOn N F (φ z) →
    ∀ (h : P) (v : R.tangentSpan N (φ z)), (v : T) = D h →
      R.hessianForm (S := R.tangentSpan N (φ z)) Subtype.val N F (φ z) v =
        fderiv ℝ (fderiv ℝ (F ∘ φ)) z h h
  posDef_hessianForm_iff : R.IsCriticalOn N F (φ z) →
    ((R.hessianForm (S := R.tangentSpan N (φ z)) Subtype.val N F (φ z)).PosDef ↔
      ∀ h : P, h ≠ 0 → 0 < fderiv ℝ (fderiv ℝ (F ∘ φ)) z h h)
def HasUniqueHessianAt (N : Set X) (F : X → ℝ) (x : X) : Prop :=
  ∃! Q : QuadraticForm ℝ (R.tangentSpan N x), R.IsHessianFormAt Subtype.val N F x Q
def HessianEqPartialsMatrix {d : ℕ} (N : Set X) (F : X → ℝ) (ψ : (Fin d → ℝ) → X)
    (u₀ : Fin d → ℝ) (s : Set (Fin d)) : Prop :=
  (∀ w : Fin d → ℝ, (∀ i, i ∉ s → w i = 0) →
    R.tangent (fun t : ℝ => ψ (u₀ + t • w)) ∈ R.tangentSpan N (ψ u₀)) ∧
  ∀ (w w' : Fin d → ℝ) (v v' : R.tangentSpan N (ψ u₀)),
    (∀ i, i ∉ s → w i = 0) → (∀ i, i ∉ s → w' i = 0) →
    (v : T) = R.tangent (fun t : ℝ => ψ (u₀ + t • w)) →
    (v' : T) = R.tangent (fun t : ℝ => ψ (u₀ + t • w')) →
    QuadraticMap.polar (R.hessianForm (S := R.tangentSpan N (ψ u₀)) Subtype.val N F (ψ u₀)) v v' / 2 =
      ∑ i, ∑ j, w i * w' j *
        fderiv ℝ (fderiv ℝ (F ∘ ψ)) u₀ (Pi.single i 1) (Pi.single j 1)
end Geometry.CurveData
namespace Matrices.EmbeddedSubmanifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
def Chart.IsLocallyCoordinatePlane {M : Set E} (c : Chart M) (N : Set E) (u₀ : Fin c.dim → ℝ)
    (s : Set (Fin c.dim)) : Prop :=
  ∃ W : Set (Fin c.dim → ℝ), IsOpen W ∧ u₀ ∈ W ∧ W ⊆ c.source ∧
    ∀ u ∈ W, c.param u ∈ N ↔ ∀ i, i ∉ s → u i = u₀ i
end Matrices.EmbeddedSubmanifold
namespace Tower
variable {L n k j : ℕ}
def IsFieldParametrization [Fintype (PositiveEdge L n k j)] {P : Type} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] (N : Set (Edge L n k j → Matrices.ComplexMatrix2))
    (O : Set P) (φ : P → Edge L n k j → Matrices.ComplexMatrix2) : Prop :=
  MapsTo φ O N ∧
    Matrices.EmbeddedSubmanifold.IsC2Parametrization (restrictToPositiveEdges '' N) O
      fun p => restrictToPositiveEdges (φ p)
end Tower
namespace Tower.RestrictionHessian
open Matrices.EmbeddedSubmanifold in
def Statement : Prop :=
  (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (𝒳 N : Set E) (F : E → ℝ),
    IsChartedSubset 𝒳 → IsChartedSubsetOf N 𝒳 →
    IsC2OnCharted 𝒳 F →
    (∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] (O : Set P)
      (φ : P → E) (z : P), IsC2Parametrization N O φ → z ∈ O →
      (vectorCurveData E).HessianViaParametrization N F φ z
        (fderiv ℝ φ z : P →ₗ[ℝ] E)) ∧
    (∀ x ∈ N, ∃ (d : ℕ) (O : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) → E) (z : Fin d → ℝ),
      IsC2Parametrization N O φ ∧ z ∈ O ∧ φ z = x) ∧
    (∀ x, (vectorCurveData E).IsCriticalOn N F x →
      (vectorCurveData E).HasUniqueHessianAt N F x) ∧
    ∀ (c : Chart 𝒳) (u₀ : Fin c.dim → ℝ) (s : Set (Fin c.dim)),
      c.IsLocallyCoordinatePlane N u₀ s →
      (vectorCurveData E).IsCriticalOn N F (c.param u₀) →
      (vectorCurveData E).HessianEqPartialsMatrix N F c.param u₀ s) ∧
  ∀ (L n k j : ℕ) [Fintype (Tower.PositiveEdge L n k j)]
    (𝒳 N : Set (Tower.Edge L n k j → Matrices.ComplexMatrix2))
    (F : (Tower.Edge L n k j → Matrices.ComplexMatrix2) → ℝ),
    Tower.IsFieldSubmanifold 𝒳 → Tower.IsFieldSubmanifold N → N ⊆ 𝒳 →
    IsC2OnCharted (Tower.restrictToPositiveEdges '' 𝒳)
      (fun w => F (Tower.fieldOfPositiveValues w)) →
    (∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] (O : Set P)
      (φ : P → Tower.Edge L n k j → Matrices.ComplexMatrix2) (z : P),
      Tower.IsFieldParametrization N O φ →
      z ∈ O → ∃ D : P →ₗ[ℝ] Tower.Edge L n k j → Matrices.ComplexMatrix2,
        (∀ h, D h = Tower.curveTangent fun t : ℝ => φ (z + t • h)) ∧
        (Tower.fieldCurveData L n k j).HessianViaParametrization N F φ z D) ∧
    (∀ x ∈ N, ∃ (d : ℕ) (O : Set (Fin d → ℝ))
      (φ : (Fin d → ℝ) → Tower.Edge L n k j → Matrices.ComplexMatrix2) (z : Fin d → ℝ),
      Tower.IsFieldParametrization N O φ ∧ z ∈ O ∧ φ z = x) ∧
    (∀ x, (Tower.fieldCurveData L n k j).IsCriticalOn N F x →
      (Tower.fieldCurveData L n k j).HasUniqueHessianAt N F x) ∧
    ∀ (c : Chart (Tower.restrictToPositiveEdges '' 𝒳))
      (u₀ : Fin c.dim → ℝ) (s : Set (Fin c.dim)),
      c.IsLocallyCoordinatePlane (Tower.restrictToPositiveEdges '' N) u₀ s →
      (Tower.fieldCurveData L n k j).IsCriticalOn N F
        (Tower.fieldOfPositiveValues (c.param u₀)) →
      (Tower.fieldCurveData L n k j).HessianEqPartialsMatrix N F
        (fun u => Tower.fieldOfPositiveValues (c.param u)) u₀ s
end Tower.RestrictionHessian
end YangMills.Construction
end

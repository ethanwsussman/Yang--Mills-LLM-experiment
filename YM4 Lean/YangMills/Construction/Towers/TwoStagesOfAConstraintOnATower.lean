import YangMills.Construction.Towers.FibresOfTheAveragingMaps
import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
variable {L n k a b c : ℕ}
def fibreHessianOnKernel (M : edgeFormSpace L n k a →ₗ[ℝ] edgeFormSpace L n k c)
    (N : Set (Edge L n k a → Matrices.ComplexMatrix2))
    (F : (Edge L n k a → Matrices.ComplexMatrix2) → ℝ) (x : Edge L n k a → Matrices.ComplexMatrix2) :
    QuadraticForm ℝ (LinearMap.ker M) :=
  (fieldCurveData L n k a).hessianForm (S := LinearMap.ker M) (fun B => B.1.1) N F x
structure TwoStageData (𝒳 : Set (Edge L n k a → Matrices.ComplexMatrix2))
    (𝒴 𝒰 : Set (Edge L n k b → Matrices.ComplexMatrix2))
    (m : (Edge L n k a → Matrices.ComplexMatrix2) → Edge L n k b → Matrices.ComplexMatrix2)
    (q : (Edge L n k b → Matrices.ComplexMatrix2) → Edge L n k c → Matrices.ComplexMatrix2)
    (F : (Edge L n k a → Matrices.ComplexMatrix2) → ℝ)
    (f g : (Edge L n k b → Matrices.ComplexMatrix2) → ℝ)
    (x : (Edge L n k b → Matrices.ComplexMatrix2) → Edge L n k a → Matrices.ComplexMatrix2) : Prop where
  mapsTo : MapsTo m 𝒳 𝒴
  analytic_first : IsAnalyticFieldMap 𝒳 m
  surjective_first : ∀ V ∈ 𝒳, HasSurjectiveDifferential m V
  analytic_second : IsAnalyticFieldMap 𝒴 q
  surjective_second : ∀ V ∈ 𝒴, HasSurjectiveDifferential q V
  analytic_fn : IsAnalyticFieldFunction 𝒳 F
  analytic_add : IsAnalyticFieldFunction 𝒴 g
  subset : 𝒰 ⊆ 𝒴
  analytic_section : IsAnalyticFieldMap 𝒰 x
  section_mapsTo : MapsTo x 𝒰 𝒳
  section_right_inv : ∀ y ∈ 𝒰, m (x y) = y
  value_eq : ∀ y ∈ 𝒰, f y = F (x y)
  critical : ∀ y ∈ 𝒰, (fieldCurveData L n k a).IsCriticalOn (fibreWithin 𝒳 m y) F (x y)
  posDef : ∀ y ∈ 𝒰,
    (fibreHessianOnKernel (leftDifferentialLinear m (x y)) (fibreWithin 𝒳 m y) F (x y)).PosDef
def TwoStageConstraintHolds : Prop :=
  ∀ L n k a b c : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → a ≤ k → b ≤ k → c ≤ k →
    ∀ (𝒳 : Set (Edge L n k a → Matrices.ComplexMatrix2))
      (𝒴 𝒰 : Set (Edge L n k b → Matrices.ComplexMatrix2))
      (m : (Edge L n k a → Matrices.ComplexMatrix2) → Edge L n k b → Matrices.ComplexMatrix2)
      (q : (Edge L n k b → Matrices.ComplexMatrix2) → Edge L n k c → Matrices.ComplexMatrix2)
      (F : (Edge L n k a → Matrices.ComplexMatrix2) → ℝ)
      (f g : (Edge L n k b → Matrices.ComplexMatrix2) → ℝ)
      (x : (Edge L n k b → Matrices.ComplexMatrix2) → Edge L n k a → Matrices.ComplexMatrix2)
      (y₀ : Edge L n k b → Matrices.ComplexMatrix2),
    TwoStageData 𝒳 𝒴 𝒰 m q F f g x → y₀ ∈ 𝒰 →
    (fieldCurveData L n k b).IsCriticalOn (fibreWithin 𝒴 q (q y₀) ∩ 𝒰) (fun y => f y + g y) y₀ →
    (fibreHessianOnKernel (leftDifferentialLinear q y₀) (fibreWithin 𝒴 q (q y₀) ∩ 𝒰)
      (fun y => f y + g y) y₀).PosDef →
    let x₀ := x y₀
    let M := leftDifferentialLinear m x₀
    let N := leftDifferentialLinear q y₀
    let P := fibreWithin 𝒳 (q ∘ m) (q y₀)
    let G := fun U => F U + g (m U)
    (fieldCurveData L n k a).IsCriticalOn P G x₀ ∧
      (fibreHessianOnKernel (N ∘ₗ M) P G x₀).PosDef ∧
      constrainedGaussianOnEdgeForms (N ∘ₗ M) (fibreHessianOnKernel (N ∘ₗ M) P G x₀) =
        constrainedGaussianOnEdgeForms M (fibreHessianOnKernel M (fibreWithin 𝒳 m y₀) F x₀) *
          constrainedGaussianOnEdgeForms N
            (fibreHessianOnKernel N (fibreWithin 𝒴 q (q y₀) ∩ 𝒰) (fun y => f y + g y) y₀)
end YangMills.Construction.Tower
end

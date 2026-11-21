import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import YangMills.Construction.Towers.PathsDifferentiableAtZero
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower
def AnalyticMapsAlongCurves : Prop :=
  ∀ L n k a b : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → a ≤ k → b ≤ k →
    (∀ (𝒰 : Set (Edge L n k a → Matrices.ComplexMatrix2))
      (φ : (Edge L n k a → Matrices.ComplexMatrix2) → Edge L n k b → Matrices.ComplexMatrix2),
      IsAnalyticFieldMap 𝒰 φ → ContinuousOn φ 𝒰 ∧ ∀ U ∈ 𝒰,
        (∀ B : edgeFormSpace L n k a,
          (leftDifferentialLinear φ U B : Edge L n k b → Matrices.ComplexMatrix2) =
            leftDifferential φ U B) ∧
        ∀ γ : ℝ → Edge L n k a → Matrices.ComplexMatrix2, IsDiffAtZeroPath γ → γ 0 = U →
          IsDiffAtZeroPath (fun t => φ (γ t)) ∧
            curveTangent (fun t => φ (γ t)) = leftDifferential φ U (curveTangent γ)) ∧
    ∀ (𝒰 : Set (Edge L n k a → Matrices.ComplexMatrix2))
      (F : (Edge L n k a → Matrices.ComplexMatrix2) → ℝ),
      IsAnalyticFieldFunction 𝒰 F → ∀ U ∈ 𝒰, ∃ X ∈ edgeFormSpace L n k a,
        ∀ γ : ℝ → Edge L n k a → Matrices.ComplexMatrix2, IsDiffAtZeroPath γ → γ 0 = U →
          HasDerivAt (fun t => F (γ t)) (edgeFormPairing X (curveTangent γ)).re 0
end YangMills.Construction.Tower
end

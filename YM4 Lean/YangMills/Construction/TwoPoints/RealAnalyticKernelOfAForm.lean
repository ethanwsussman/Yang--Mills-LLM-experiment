import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.TwoPoints.ThreePropertiesOfAForm
import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def IsRealAnalyticAwayFromZero (K : AmbientSpace → ℝ) : Prop :=
  YangMills.Construction.Coordinates.ComplexCoordinates.IsRealAnalyticIn (N := 4) (N' := 1)
    (YangMills.Construction.Coordinates.ComplexCoordinates.realLocus 4 \ {0})
    fun z _ => ((K fun μ => (z μ).re : ℝ) : ℂ)
def IsMollifierLimit (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (K : AmbientSpace → ℝ) : Prop :=
  ∀ ξ : AmbientSpace, ξ ≠ 0 → ∀ j : ℕ → AmbientSpace → ℂ, IsMollifierSeq j →
    Tendsto (fun n : ℕ => S (j n) (translateFun ξ (j n))) atTop (𝓝 (K ξ))
structure IsAnalyticKernel (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (K : AmbientSpace → ℝ) : Prop where
  analytic : IsRealAnalyticAwayFromZero K
  even : ∀ ξ : AmbientSpace, ξ ≠ 0 → K (-ξ) = K ξ
  invariant : ∀ w ∈ hyperoctahedralPerms, ∀ ξ : AmbientSpace, ξ ≠ 0 → K (w ξ) = K ξ
  represents : ∀ f ∈ compactC1Complex, ∀ h ∈ compactC1Complex, DisjointSupports f h →
    complexifyForm S f h =
      lebesgueIntegral fun y : AmbientSpace =>
        lebesgueIntegral fun x : AmbientSpace => f x * h y * (K (y - x) : ℂ)
  limit : IsMollifierLimit S K
def analyticKernel (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) : AmbientSpace → ℝ :=
  Classical.epsilon (IsAnalyticKernel S)
def AnalyticKernel.Statement : Prop :=
  ∀ (sc : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ),
    IsDisjointForm S → IsAdmissibleForm sc S →
    IsAnalyticKernel S (analyticKernel S) ∧
      (∀ ξ : AmbientSpace, ξ ≠ 0 → ∀ j : ℕ → AmbientSpace → ℂ, IsMollifierSeq j →
        ∀ n : ℕ, 2 / euclidNorm ξ ≤ (n : ℝ) →
          j n ∈ compactC1Real ∧ translateFun ξ (j n) ∈ compactC1Real ∧
            DisjointSupports (j n) (translateFun ξ (j n))) ∧
      (∃ j : ℕ → AmbientSpace → ℂ, IsMollifierSeq j) ∧
      ∀ K : AmbientSpace → ℝ, IsMollifierLimit S K →
        ∀ ξ : AmbientSpace, ξ ≠ 0 → K ξ = analyticKernel S ξ
end YangMills.Construction.TwoPoints
end

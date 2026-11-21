import YangMills.Construction.Towers.OneStepOfACriticalBranch
import YangMills.Construction.Towers.StepOfACriticalBranchInTheChart
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower
open Matrices
def MinimizerChartGivesFibreSection : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    ∀ [Fintype (PositiveEdge L n k i)] [Fintype (PositiveEdge L n k (i + 1))]
      (F : (Edge L n k i → ComplexMatrix2) → ℝ),
      (∃ 𝒰 : Set (Edge L n k i → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
        IsAnalyticFieldFunction 𝒰 F) →
      leftGradient (fieldSpace L n k i) (fun V => (F V : ℂ)) (trivialField L n k i) = 0 →
      (∀ ξ ∈ edgeFormSpace L n k i, linearSmoothing L n k i ξ = 0 → ξ ≠ 0 →
        0 < leftSecondDeriv F (trivialField L n k i) ξ ξ) →
      ∃ T ∈ 𝓝 (0 : PositiveEdge L n k i → ComplexMatrix2.LieElement),
        ∀ (𝒩 : Set (PositiveEdge L n k i → ComplexMatrix2.LieElement))
          (O : Set (ConstrainedMinima.tangentKernel (smoothingInExpChart L n k i)))
          (𝒲 : Set (PositiveEdge L n k (i + 1) → ComplexMatrix2.LieElement))
          (ρ : (PositiveEdge L n k i → ComplexMatrix2.LieElement) →L[ℝ]
            ConstrainedMinima.tangentKernel (smoothingInExpChart L n k i))
          (c : ConstrainedMinima.tangentKernel (smoothingInExpChart L n k i) →
            (PositiveEdge L n k (i + 1) → ComplexMatrix2.LieElement) →
              PositiveEdge L n k i → ComplexMatrix2.LieElement)
          (b : (PositiveEdge L n k (i + 1) → ComplexMatrix2.LieElement) →
            ConstrainedMinima.tangentKernel (smoothingInExpChart L n k i)),
          ConstrainedMinima.IsMinimizerChart (smoothingInExpChart L n k i)
            (fnInExpChart F) 𝒩 O 𝒲 ρ c b → 𝒩 ⊆ T →
          ∃ (𝒰 : Set (Edge L n k i → ComplexMatrix2)) (ε : ℝ)
            (p : (Edge L n k (i + 1) → ComplexMatrix2) → Edge L n k i → ComplexMatrix2),
            IsFibreCriticalSection F 𝒰 ε p
end YangMills.Construction.Tower
end

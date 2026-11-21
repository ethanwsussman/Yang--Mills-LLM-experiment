import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices
def ScaledGradients : Prop :=
  ∀ (L n k j : ℕ) (hL : 0 < L) (hj : j ≤ k), Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    ∀ l ≤ j, ∀ (𝒰 : Set (Edge L n k l → ComplexMatrix2)) (F : (Edge L n k l → ComplexMatrix2) → ℝ)
      (F' : (Edge L (scaledExponent n k j) j l → ComplexMatrix2) → ℝ),
      IsAnalyticFieldFunction 𝒰 F →
      (∀ V ∈ fieldSpace L n k l, F' (transportTotal (scaleEdge hL hj l) V) = F V) →
      ∀ U ∈ 𝒰,
        leftGradient (fieldSpace L (scaledExponent n k j) j l) (fun V => (F' V : ℂ))
            (transportTotal (scaleEdge hL hj l) U) =
          transportTotal (scaleEdge hL hj l)
            (leftGradient (fieldSpace L n k l) (fun V => (F V : ℂ)) U)
end YangMills.Construction.Tower
end

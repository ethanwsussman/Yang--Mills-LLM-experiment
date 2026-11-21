import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices
def ScaledIterateDifferentials : Prop :=
  ∀ (L n k j : ℕ) (hL : 0 < L) (hj : j ≤ k), Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ j →
    ∀ l ≤ j, ∃ 𝒰 : Set (Edge L n k 0 → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧ ∀ U ∈ 𝒰,
      ∀ (B : edgeFormSpace L n k 0) (B' : edgeFormSpace L (scaledExponent n k j) j 0),
        (B' : Edge L (scaledExponent n k j) j 0 → ComplexMatrix2) =
            transportTotal (scaleEdge hL hj 0) (B : Edge L n k 0 → ComplexMatrix2) →
          (leftDifferentialLinear (smoothingIter L (scaledExponent n k j) j l)
              (transportTotal (scaleEdge hL hj 0) U) B' :
            Edge L (scaledExponent n k j) j l → ComplexMatrix2) =
            transportTotal (scaleEdge hL hj l)
              (leftDifferentialLinear (smoothingIter L n k l) U B : Edge L n k l → ComplexMatrix2)
end YangMills.Construction.Tower
end

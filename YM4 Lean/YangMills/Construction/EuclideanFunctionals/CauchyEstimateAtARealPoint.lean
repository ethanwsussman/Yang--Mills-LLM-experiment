import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.EuclideanFunctionals.MultiIndicesConvolutionsAndSeriesOfOperators
import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
set_option autoImplicit false

section
open Set
noncomputable section
namespace YangMills.Construction.RealCoordinates
def complexify {N : ℕ} (x : Fin N → ℝ) : Coordinates.ComplexCoordinates N := fun j => (x j : ℂ)
def rePart {N : ℕ} (z : Coordinates.ComplexCoordinates N) : Fin N → ℝ := fun j => (z j).re
end YangMills.Construction.RealCoordinates
end
end

open scoped ContDiff
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.CauchyEstimate
open RealCoordinates Coordinates.ComplexCoordinates.PowerSeriesHolomorphy
def realRestriction (f : Coordinates.ComplexCoordinates 4 → ℂ) : R4 → ℂ :=
  fun x => f (complexify x)
def viaRealParts (g : R4 → ℂ) :
    Coordinates.ComplexCoordinates 4 → Coordinates.ComplexCoordinates 1 :=
  fun z _ => g (rePart z)
def CauchyBound : Prop :=
  ∀ (U : Set (Coordinates.ComplexCoordinates 4)) (f : Coordinates.ComplexCoordinates 4 → ℂ),
    IsOpen U →
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U (fun z _ => f z) →
    (ContDiffOn ℝ ∞ (realRestriction f) (complexify ⁻¹' U) ∧
      ∀ γ : Multiindex, Coordinates.ComplexCoordinates.IsRealAnalyticIn
        (U ∩ Coordinates.ComplexCoordinates.realLocus 4)
        (viaRealParts (iteratedPartial γ (realRestriction f)))) ∧
    ∀ (x : R4) (r M : ℝ), complexify x ∈ U → 0 < r → 0 ≤ M →
      closedPolydisk (complexify x) r ⊆ U →
      (∀ z ∈ closedPolydisk (complexify x) r, ‖f z‖ ≤ M) →
      ∀ γ : Multiindex, ‖iteratedPartial γ (realRestriction f) x‖ ≤
        (γ.fact : ℝ) * r ^ (-(γ.order : ℤ)) * M
end YangMills.Construction.EuclideanFunctionals.CauchyEstimate

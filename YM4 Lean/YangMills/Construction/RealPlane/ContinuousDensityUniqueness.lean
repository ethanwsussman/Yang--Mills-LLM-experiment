import YangMills.Construction.PositiveDefinite.HalfPlaneKernelDefs
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.RealPlane
def IsSmoothTestFamilyIn {n : ℕ} (U : Set (Fin n → RealPlane))
    (φ : Fin n → RealPlane → ℝ) : Prop :=
  (∀ i, ContDiff ℝ ∞ (φ i)) ∧ (∀ i, HasCompactSupport (φ i)) ∧
    (Set.univ.pi fun i => tsupport (φ i)) ⊆ U
def productWeightedIntegral {n : ℕ} (U : Set (Fin n → RealPlane))
    (φ : Fin n → RealPlane → ℝ) (g : (Fin n → RealPlane) → ℂ) : ℂ :=
  ∫ x, U.indicator (fun x => (∏ i, ((φ i (x i) : ℝ) : ℂ)) * g x) x
namespace DensityUniqueness
def Claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ U : Set (Fin n → RealPlane), IsOpen U →
    ∀ g : (Fin n → RealPlane) → ℂ, ContinuousOn g U →
      ((∀ φ, IsSmoothTestFamilyIn U φ → productWeightedIntegral U φ g = 0) → ∀ x ∈ U, g x = 0) ∧
      ((∀ φ, IsSmoothTestFamilyIn U φ → (productWeightedIntegral U φ g).im = 0) →
        ∀ x ∈ U, (g x).im = 0)
end DensityUniqueness
end YangMills.Construction.RealPlane

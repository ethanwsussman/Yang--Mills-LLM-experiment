import YangMills.Construction.ClusterExpansionOfAStep.SharesOnARegionOfATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ShareContinuity
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
open YangMills.Construction.TorusLumps YangMills.Construction.TorusShares YangMills.Construction.StepCosts
def ShareLipschitzInField : Prop :=
  ∀ (a : ℝ) (L : ℕ) (s₀ A δ : ℝ), ShareLocality a L s₀ A δ → 0 ≤ A → 0 ≤ δ →
    ∀ (t m : ℕ) [NeZero m] (X X' : Finset (TorusSite m)) (W W' : TorusField m) (y : TorusSite m) (ρ : ℕ) (s ε : ℝ),
      64 ≤ m → 0 < s → 0 ≤ ε → s + 8 * ε ≤ s₀ →
      IsLocallyOrthantClosed X 1024 → IsLocallyOrthantClosed X' 1024 →
      IsColdOn X s W → IsColdOn X' s W' →
      (2 * ρ + 2 < m →
        (∀ h, OffsetInBox ρ h → (y + siteOfInt h ∈ X ↔ y + siteOfInt h ∈ X')) →
        (∀ b : (Fin 4 → ℤ) × Fin 4, BondOffsetInBox ρ b →
          ‖(W (bondFrom y b).1 (bondFrom y b).2 : ℍ[ℝ]) - W' (bondFrom y b).1 (bondFrom y b).2‖ ≤ ε) →
        |levelShare a L t X y W - levelShare a L t X' y W'| ≤
          A * Real.exp (-(δ * ρ)) + A * (2 * ε) * (4 * (2 * (ρ : ℝ) + 1) ^ 4)) ∧
      (X = X' → (∀ x i, ‖(W x i : ℍ[ℝ]) - W' x i‖ ≤ ε) →
        |levelShare a L t X y W - levelShare a L t X' y W'| ≤ A * (2 * ε) * (4 * (m : ℝ) ^ 4))
end YangMills.Construction.ShareContinuity
end

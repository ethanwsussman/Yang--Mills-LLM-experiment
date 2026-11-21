import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.TorusFields
def TwoTorusSumsBound : Prop :=
  ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (a : TorusSite n → ℝ) (a' : TorusSite n' → ℝ) (H : Finset (Fin 4 → ℤ))
    (Y : TorusSite n) (Y' : TorusSite n') (d : ℕ) (c ε : ℝ), 0 < c → 0 ≤ ε → 1 ≤ d → H.Nonempty →
    (∀ h ∈ H, ∀ h₂ ∈ H, ∀ g g₂, OffsetInBox (d - 1) g → OffsetInBox (d - 1) g₂ →
      (Y + siteOfInt (h + g) = Y + siteOfInt (h₂ + g₂) ↔ h + g = h₂ + g₂)) →
    (∀ h ∈ H, ∀ h₂ ∈ H, ∀ g g₂, OffsetInBox (d - 1) g → OffsetInBox (d - 1) g₂ →
      (Y' + siteOfInt (h + g) = Y' + siteOfInt (h₂ + g₂) ↔ h + g = h₂ + g₂)) →
    (∀ (y : TorusSite n) (R : ℕ), d ≤ R → (∀ h ∈ H, R ≤ supDist y (Y + siteOfInt h)) →
      |a y| ≤ Real.exp (-(c * ((R : ℝ) - 2)))) →
    (∀ (y : TorusSite n') (R : ℕ), d ≤ R → (∀ h ∈ H, R ≤ supDist y (Y' + siteOfInt h)) →
      |a' y| ≤ Real.exp (-(c * ((R : ℝ) - 2)))) →
    (∀ h ∈ H, ∀ g, OffsetInBox (d - 1) g → |a (Y + siteOfInt (h + g)) - a' (Y' + siteOfInt (h + g))| ≤ ε) →
    |∑ y, a y - ∑ y, a' y| ≤ (H.card : ℝ) * (2 * (d : ℝ) + 1) ^ 4 * ε +
      2 * (H.card : ℝ) * (Real.exp (2 * c) * Real.exp (-(3 / 4 * c * d)) * (2 / (1 - Real.exp (-(c / 16)))) ^ 4)
end YangMills.Construction.TorusLumps
end

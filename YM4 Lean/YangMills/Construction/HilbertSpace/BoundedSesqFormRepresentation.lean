import YangMills.Construction.HilbertSpace.CommutingSemigroupGroupPairs
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
namespace YangMills.Construction.HilbertSpace.BoundedSesqRep
open YangMills.Construction.SpectralCalculus
structure IsSesqMap {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : H → H → ℂ) : Prop where
  add_left : ∀ x₁ x₂ y, b (x₁ + x₂) y = b x₁ y + b x₂ y
  smul_left : ∀ (a : ℂ) x y, b (a • x) y = conj a * b x y
  add_right : ∀ x y₁ y₂, b x (y₁ + y₂) = b x y₁ + b x y₂
  smul_right : ∀ (a : ℂ) x y, b x (a • y) = a * b x y
def Claim : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (c : ℝ)
    (b : H → H → ℂ),
    0 ≤ c → IsSesqMap b → (∀ x y, ‖b x y‖ ≤ c * ‖x‖ * ‖y‖) →
    ∃ B : H →L[ℂ] H,
      (∀ x y, inner ℂ x (B y) = b x y) ∧
      (∀ B' : H →L[ℂ] H, (∀ x y, inner ℂ x (B' y) = b x y) → B' = B) ∧
      ‖B‖ ≤ c ∧
      ((∀ x y, b y x = conj (b x y)) → IsSymmetricBounded B)
end YangMills.Construction.HilbertSpace.BoundedSesqRep

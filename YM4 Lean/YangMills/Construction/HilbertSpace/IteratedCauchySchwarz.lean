import YangMills.Construction.HilbertSpace.CommutingSemigroupGroupPairs
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.HilbertSpace.IteratedCauchySchwarz
def Claim : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (q : V → V → ℂ) (A : V → V),
    SpectralCalculus.IsPosHermitianForm q →
    (∀ x y : V, q (A x) y = q x (A y)) →
    (∀ (x : V) (k : ℕ), 1 ≤ k →
      SpectralCalculus.formSeminorm q (A x) ≤
        SpectralCalculus.formSeminorm q x ^ (1 - (2 : ℝ) ^ (-(k : ℝ))) *
          SpectralCalculus.formSeminorm q (A^[2 ^ k] x) ^ ((2 : ℝ) ^ (-(k : ℝ)))) ∧
    (∀ (x : V) (b c : ℝ), 0 ≤ b → 0 ≤ c →
      (∀ k m : ℕ, 1 ≤ k → m = 2 ^ k →
        SpectralCalculus.formSeminorm q (A^[m] x) ≤ c * (m : ℝ) * b ^ (m - 1)) →
      SpectralCalculus.formSeminorm q (A x) ≤ b * SpectralCalculus.formSeminorm q x)
end YangMills.Construction.HilbertSpace.IteratedCauchySchwarz

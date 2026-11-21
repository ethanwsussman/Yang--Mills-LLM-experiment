import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace SmoothSlices
def IteratedFDerivSlices : Prop :=
  (∀ (E E' : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (f : E → ℝ) (L : E' →L[ℝ] E) (a : E) (x : E') (n : ℕ) (v : Fin n → E'),
    ContDiffAt ℝ n f (a + L x) →
    iteratedFDeriv ℝ n (fun z => f (a + L z)) x v = iteratedFDeriv ℝ n f (a + L x) fun i => L (v i)) ∧
  (∀ (P Q : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (G : P × Q → ℝ) (j m : ℕ) (w : Fin j → P) (η₀ : Q), ContDiffAt ℝ (m + j : ℕ) G (0, η₀) →
    ContDiffAt ℝ m (fun η => iteratedFDeriv ℝ j (fun τ => G (τ, η)) 0 w) η₀) ∧
  ∀ (P Q : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (G : P × Q → ℝ) (j : ℕ) (w : Fin j → P) (η₀ d : Q), ContDiffAt ℝ (j + 1 : ℕ) G (0, η₀) →
    fderiv ℝ (fun η => iteratedFDeriv ℝ j (fun τ => G (τ, η)) 0 w) η₀ d =
      iteratedFDeriv ℝ (j + 1) G (0, η₀) (Fin.cons (0, d) fun i => (w i, 0))
end SmoothSlices
end YangMills.Construction
end

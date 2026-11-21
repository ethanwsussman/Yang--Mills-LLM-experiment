import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ExpSums
def vandermondeOfFreqs (F : Finset ℤ) : Matrix (Fin F.card) F ℂ :=
  Matrix.of fun l h => (-4 * ((h : ℤ) : ℂ)) ^ (l : ℕ)
def IsVandermondeInverse (F : Finset ℤ) (W : Matrix F (Fin F.card) ℂ) : Prop :=
  vandermondeOfFreqs F * W = 1 ∧ W * vandermondeOfFreqs F = 1
def vandermondeInverse (F : Finset ℤ) : Matrix F (Fin F.card) ℂ :=
  Classical.epsilon (IsVandermondeInverse F)
def expSum (F : Finset ℤ) (b : F → ℂ) (s : ℝ) : ℂ :=
  ∑ h : F, b h * Complex.exp (-4 * ((h : ℤ) : ℂ) * (s : ℂ))
def derivAddSMul (c : ℂ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun s => deriv g s + c * g s
def composedOperator (F : Finset ℤ) (f : ℝ → ℂ) : ℝ → ℂ :=
  F.sort.foldr (fun (h : ℤ) g => derivAddSMul (4 * (h : ℂ)) g) f
def ExpSumsDetermined : Prop :=
  ∀ F : Finset ℤ, F.Nonempty →
    IsVandermondeInverse F (vandermondeInverse F) ∧
    (∀ (b : F → ℂ) (f : ℝ → ℂ), (∀ s : ℝ, f s = expSum F b s) →
      ∀ h : F, b h = ∑ l : Fin F.card, vandermondeInverse F h l * iteratedDeriv (l : ℕ) f 0) ∧
    (∀ b b' : F → ℂ, (∀ s : ℝ, expSum F b s = expSum F b' s) →
      ∀ h : F, b h = b' h) ∧
    (∀ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → (∀ s : ℝ, composedOperator F f s = 0) →
      ∃ b : F → ℂ, ∀ s : ℝ, f s = expSum F b s)
end YangMills.Construction.ExpSums

import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Cumulants.MultilinearForms
def IsRealSymmetricForm {X : Type*} {n : ℕ} (V : Set (X → ℝ))
    (Φ : (Fin n → X → ℝ) → ℂ) : Prop :=
  ∃ F : Submodule ℝ (X → ℝ), (F : Set (X → ℝ)) = V ∧
    ∃ M : MultilinearMap ℝ (fun _ : Fin n => F) ℝ,
      (∀ (σ : Equiv.Perm (Fin n)) (g : Fin n → F), M (fun i => g (σ i)) = M g) ∧
      ∀ g : Fin n → F, Φ (fun i => (g i : X → ℝ)) = ((M g : ℝ) : ℂ)
end YangMills.Construction.Cumulants.MultilinearForms

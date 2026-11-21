import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices
def JacobiDeterminantFormula : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n],
    (∀ (I : Set ℝ) (A A' : ℝ → Matrix n n ℂ), I.OrdConnected →
      (∀ t ∈ I, IsUnit (A t)) →
      (∀ t ∈ I, ∀ i j, HasDerivWithinAt (fun s => A s i j) (A' t i j) I t) →
      ∀ t ∈ I, HasDerivWithinAt (fun s => (A s).det)
        ((A t).det * ((A t)⁻¹ * A' t).trace) I t) ∧
    ∀ K : Matrix n n ℂ, (NormedSpace.exp K).det = Complex.exp K.trace
end YangMills.Construction.Matrices
end

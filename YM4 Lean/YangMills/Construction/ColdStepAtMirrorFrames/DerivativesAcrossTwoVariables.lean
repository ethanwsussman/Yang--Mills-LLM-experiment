import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Calculus
def IteratedFDerivParamDiff : Prop :=
  ∀ (P Q : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (j : ℕ) (G : P × Q → ℝ) (η : Q) (v : Fin j → P), ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) G (0, η) →
    ContDiffAt ℝ 1 (fun ζ => iteratedFDeriv ℝ j (fun s => G (s, ζ)) 0 v) η ∧
      ∀ e : Q, fderiv ℝ (fun ζ => iteratedFDeriv ℝ j (fun s => G (s, ζ)) 0 v) η e =
        iteratedFDeriv ℝ j (fun s => fderiv ℝ (fun ζ => G (s, ζ)) η e) 0 v
end YangMills.Construction.Calculus
end

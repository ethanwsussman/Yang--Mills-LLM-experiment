import YangMills.Construction.ClusterExpansionOfAStep.FamiliesAtConstantCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
def CurvatureUnderAnIsometry : Prop :=
  ∀ (n : ℕ) [NeZero n] (X : imaginaryQuaternions) (ω : Fin 4 → Fin 4 → ℝ) (γ : ℝ) (V : TorusField n)
    (p : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1), (∀ i j, ω i j = - ω j i) → IsAbelianWithCurvature X ω γ V →
    ∃ V' : TorusField n, (⟨p, s, 0, hs⟩ : TorusIsometry).Transports V V' ∧
      IsAbelianWithCurvature X (fun a b => (s a : ℝ) * (s b : ℝ) * ω (p a) (p b)) γ V'
end YangMills.Construction.TorusLumps
end

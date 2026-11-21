import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open Classical in
def expansionCoupling (p : StepParameters) (t : ℕ) (x : ℝ) (D : TorusFunctional) : ℝ :=
  if h : ∃ x' : ℝ, HasExpansion p (t + 1) x' (kernelImage p x D) then h.choose else x
def couplingFlow (p : StepParameters) (β : ℝ) : ℕ → ℝ × TorusFunctional
  | 0 => (β, wilsonWeight β)
  | t + 1 => (expansionCoupling p t (couplingFlow p β t).1 (couplingFlow p β t).2,
      kernelImage p (couplingFlow p β t).1 (couplingFlow p β t).2)
end YangMills.Construction.TorusLumps
end

import YangMills.Construction.Continuum.ConfigurationSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
def IterDirDerivLinear : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (I : Type) [Fintype I] [LinearOrder I]
    (e : I → V) (α : MultiIdx I),
    (∀ f ∈ smoothSet V, iterDirDeriv e α f ∈ smoothSet V) ∧
    (∀ f ∈ smoothSet V, ∀ g ∈ smoothSet V,
      iterDirDeriv e α (f + g) = iterDirDeriv e α f + iterDirDeriv e α g) ∧
    ∀ (c : ℂ), ∀ f ∈ smoothSet V,
      iterDirDeriv e α (c • f) = c • iterDirDeriv e α f
end YangMills.Construction.ConfigurationSpace
end

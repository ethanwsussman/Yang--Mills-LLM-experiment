import YangMills.Construction.Continuum.ConfigurationSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
def IterDirDerivLeibniz : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (I : Type) [Fintype I] [LinearOrder I]
    (e : I → V) (γ : MultiIdx I), ∀ f ∈ smoothSet V, ∀ g ∈ smoothSet V, ∀ x : V,
      iterDirDeriv e γ (fun y => f y * g y) x =
        ∑ δ ∈ Fintype.piFinset (fun i => Finset.range (γ i + 1)),
          (MultiIdx.choose γ δ : ℂ) * iterDirDeriv e δ f x *
            iterDirDeriv e (γ - δ) g x
end YangMills.Construction.ConfigurationSpace
end

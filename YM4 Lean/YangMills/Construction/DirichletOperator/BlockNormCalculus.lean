import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.RegionSequence.BlockOperatorNorms
import YangMills.Construction.Weighted.SeparatedSums
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions Weighted
namespace BlockCalculus
variable {ι ι' : Type}
def supportedOn (D : Set ι) : Submodule ℝ (ι → ℝ) where
  carrier := {f | ∀ i, i ∉ D → f i = 0}
  add_mem' := fun hf hg i hi => by simp [hf i hi, hg i hi]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c _ hf i hi => by simp [hf i hi]
def scaledInner (ξ : ℝ) (f g : ι → ℝ) : ℝ := ξ ^ 4 * ∑ᶠ i, f i * g i
variable {D : Set ι} {D' : Set ι'}
def IsScaledAdjoint (ξ : ℝ) (O' : supportedOn D →ₗ[ℝ] supportedOn D')
    (O : supportedOn D' →ₗ[ℝ] supportedOn D) : Prop :=
  ∀ (f : supportedOn D') (g : supportedOn D),
    scaledInner ξ (O f : ι → ℝ) g = scaledInner ξ (f : ι' → ℝ) (O' g)
end BlockCalculus
end YangMills.Construction

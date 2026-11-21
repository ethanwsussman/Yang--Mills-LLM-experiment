import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
open TopologicalSpace
noncomputable section
namespace YangMills.Construction.TestFunctions
def c1Supported (W : Compacts (Fin 4 → ℝ)) : Submodule ℝ ((Fin 4 → ℝ) → ℝ) where
  carrier := {h | IsC1R4 h ∧ tsupport h ⊆ W}
  add_mem' := fun {f g} hf hg =>
    ⟨ContDiff.add hf.1 hg.1,
      (closure_mono (Function.support_add f g)).trans
        (closure_union (s := Function.support f) (t := Function.support g)).subset
        |>.trans (Set.union_subset hf.2 hg.2)⟩
  zero_mem' := ⟨contDiff_const, by simp [tsupport]⟩
  smul_mem' := fun c f hf =>
    ⟨ContDiff.const_smul c hf.1, (closure_mono (Function.support_const_smul_subset c f)).trans hf.2⟩
instance instNormC1Supported (W : Compacts (Fin 4 → ℝ)) : Norm (c1Supported W) :=
  ⟨fun h => c1NormR4 (h : (Fin 4 → ℝ) → ℝ)⟩
theorem mem_c1Supported {W : Compacts (Fin 4 → ℝ)} {h : (Fin 4 → ℝ) → ℝ} :
    h ∈ c1Supported W ↔ IsC1R4 h ∧ tsupport h ⊆ W := Iff.rfl
end YangMills.Construction.TestFunctions

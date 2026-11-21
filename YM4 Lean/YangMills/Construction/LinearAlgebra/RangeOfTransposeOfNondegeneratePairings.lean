import YangMills.Construction.LinearAlgebra.AnnihilatorOfKernelInRangeOfTranspose
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LinearAlgebra.AnnihilatorOfKernel
theorem annihilatorSubsetRangeTranspose_of_field (𝕜 : Type) [Field 𝕜] :
    AnnihilatorSubsetRangeTranspose 𝕜 := by
  intro V V' _ _ _ _ _ _ B B' hB hBn hB' hB'n M Mt hMt f hf
  by_contra hnot
  have hfR : f ∉ LinearMap.range Mt := by
    rintro ⟨l, rfl⟩
    exact hnot ⟨l, rfl⟩
  obtain ⟨φ, hφf, hφR⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem hfR (inferInstance)
  have hinj : Function.Injective B := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact hBn v (fun w => by rw [hv]; rfl)
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := 𝕜) (V := V)).symm).mp hinj
  obtain ⟨u, hu⟩ := hsurj φ
  have hval : ∀ x, B u x = φ x := fun x => by rw [hu]
  have hφMt : ∀ l, φ (Mt l) = 0 := by
    intro l
    have hmem : φ (Mt l) ∈ (LinearMap.range Mt).map φ :=
      Submodule.mem_map_of_mem ⟨l, rfl⟩
    rw [hφR] at hmem
    simpa using hmem
  have hMu : M u = 0 := by
    refine hB'n (M u) (fun l => ?_)
    rw [hB', ← hMt, hB, hval, hφMt]
  apply hφf
  rw [← hval, hB]
  exact hf u hMu
theorem annihilatorSubsetRangeTransposeRealComplex_holds :
    AnnihilatorSubsetRangeTransposeRealComplex :=
  ⟨annihilatorSubsetRangeTranspose_of_field ℝ, annihilatorSubsetRangeTranspose_of_field ℂ⟩
end YangMills.Construction.LinearAlgebra.AnnihilatorOfKernel

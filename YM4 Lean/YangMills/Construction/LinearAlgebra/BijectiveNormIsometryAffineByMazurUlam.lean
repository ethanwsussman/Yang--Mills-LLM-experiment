import YangMills.Construction.LinearAlgebra.NormIsometryOfEuclideanFourSpaceIsAffine
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LinearAlgebra.NormIsometry
theorem exists_affineMap_of_seminorm_isometry {E : Type} [AddCommGroup E] [Module ℝ E]
    (N : Seminorm ℝ E) (hN : ∀ x, N x = 0 → x = 0) (f : E → E) (hf : Function.Bijective f)
    (hiso : ∀ x y, N (f x - f y) = N (x - y)) : ∃ g : E →ᵃ[ℝ] E, ⇑g = f := by
  let gn : AddGroupNorm E := { N.toAddGroupSeminorm with eq_zero_of_map_eq_zero' := hN }
  let _ : NormedAddCommGroup E := gn.toNormedAddCommGroup
  let _ : NormedSpace ℝ E := ⟨fun a x => (map_smul_eq_mul N a x).le⟩
  let e : E ≃ᵢ E := ⟨Equiv.ofBijective f hf, Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm]
    exact hiso x y⟩
  exact ⟨e.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap, rfl⟩
theorem bijectiveNormIsometryIsAffine_holds : BijectiveNormIsometryIsAffine :=
  fun N hN f hf hiso => exists_affineMap_of_seminorm_isometry N hN f hf hiso
end YangMills.Construction.LinearAlgebra.NormIsometry

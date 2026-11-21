import YangMills.Construction.TwoPoints.TransverseReflectionAndTheSixCoordinatePlanes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
open PeriodicLattice (coordVec)
private theorem flipTransverse_apply (x : AmbientSpace) :
    flipTransverse x = ![x 0, -x 1, -x 2, x 3] := by
  funext i
  fin_cases i <;> simp [flipTransverse, assemble, planeCoords, transCoords]
private theorem exists_mem_hyperoctahedralPerms_flipTransverse :
    ∃ w ∈ hyperoctahedralPerms, ⇑w = flipTransverse := by
  let f : AmbientSpace →ₗ[ℝ] AmbientSpace :=
    { toFun := flipTransverse
      map_add' := fun a b => by
        simp only [flipTransverse_apply]
        funext i
        fin_cases i <;> simp <;> ring
      map_smul' := fun c a => by
        simp only [flipTransverse_apply]
        funext i
        fin_cases i <;> simp }
  have hf : IsSignedPerm f := by
    refine ⟨1, ![1, -1, -1, 1], fun i => ?_⟩
    change flipTransverse (coordVec i) = _
    rw [flipTransverse_apply]
    funext j
    fin_cases i <;> fin_cases j <;> simp [PeriodicLattice.coordVec]
  obtain ⟨w, hw, e⟩ := exists_mem_hyperoctahedralPerms hf
  exact ⟨w, hw, e⟩
private theorem exists_perm_zero_three {i j : Fin 4} (hij : i < j) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 3 = j := by
  refine ⟨Equiv.swap (Equiv.swap 0 i 3) j * Equiv.swap 0 i, ?_, ?_⟩
  · have hne : i ≠ Equiv.swap 0 i 3 := by
      intro e
      have : Equiv.swap 0 i 0 = Equiv.swap 0 i 3 := by rw [Equiv.swap_apply_left]; exact e
      exact absurd ((Equiv.swap 0 i).injective this) (by decide)
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hne hij.ne
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left]
private theorem exists_axisPerm_image_coordPlane (σ : Equiv.Perm (Fin 4)) :
    ∃ w ∈ hyperoctahedralPerms, IsAxisPermutation w ∧
      w '' coordPlane =
        (Submodule.span ℝ {coordVec (σ 0), coordVec (σ 3)} :
          Submodule ℝ AmbientSpace) := by
  have hmem : TorusLifts.signedCoordinateEquiv σ⁻¹ (fun _ => 1) ∈ hyperoctahedralPerms :=
    ⟨_, _, rfl⟩
  have hlin : ∀ x, TorusLifts.signedCoordinateEquiv σ⁻¹ (fun _ => 1) x =
      signedPermLinear σ⁻¹ (fun _ => 1) x := fun _ => rfl
  have hbasis : ∀ k : Fin 4, signedPermLinear σ⁻¹ (fun _ => 1) (coordVec k) =
      coordVec (σ k) := by
    intro k
    rw [signedPermLinear_coordVec]
    simp only [Units.val_one, Int.cast_one, one_smul]
    rfl
  refine ⟨_, hmem, ⟨σ, fun k => by rw [hlin, hbasis]⟩, ?_⟩
  ext x
  simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_span_pair]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨v, rfl⟩ := (mem_coordPlane_iff p).1 hp
    refine ⟨v 1, v 0, ?_⟩
    rw [hlin, embedPlane, map_add, map_smul, map_smul, hbasis, hbasis, add_comm]
  · rintro ⟨a, b, rfl⟩
    refine ⟨embedPlane ![b, a], (mem_coordPlane_iff _).2 ⟨_, rfl⟩, ?_⟩
    rw [hlin, embedPlane, map_add, map_smul, map_smul, hbasis, hbasis, add_comm]
    simp
private theorem ncard_lt_pairs : Set.ncard {p : Fin 4 × Fin 4 | p.1 < p.2} = 6 := by
  have hset : {p : Fin 4 × Fin 4 | p.1 < p.2} =
      ↑(Finset.univ.filter fun p : Fin 4 × Fin 4 => p.1 < p.2) := by
    ext p
    simp
  rw [hset, Set.ncard_coe_finset]
  decide
theorem KernelAxisSymmetries.holds (hK : AnalyticKernel.Statement) :
    KernelAxisSymmetries.Statement := by
  intro St S hS hP
  obtain ⟨w, hw, hwe⟩ := exists_mem_hyperoctahedralPerms_flipTransverse
  refine ⟨⟨⟨w, hw, hwe⟩, fun y ζ hyζ => ?_⟩, fun i j hij => ?_, ncard_lt_pairs⟩
  · have hne : assemble y ζ ≠ 0 := by
      intro h0
      apply hyζ
      have h1 : y 1 = 0 := congrFun h0 0
      have h2 : ζ 0 = 0 := congrFun h0 1
      have h3 : ζ 1 = 0 := congrFun h0 2
      have h4 : y 0 = 0 := congrFun h0 3
      ext k <;> fin_cases k <;> simp [h1, h2, h3, h4]
    have hmap : w (assemble y ζ) = assemble y (-ζ) := by
      rw [hwe, flipTransverse_apply]
      funext k
      fin_cases k <;> simp [assemble]
    have hinv := (hK St S hS hP).1.invariant w hw _ hne
    rw [hmap] at hinv
    exact hinv
  · obtain ⟨σ, rfl, rfl⟩ := exists_perm_zero_three hij
    exact exists_axisPerm_image_coordPlane σ
end YangMills.Construction.TwoPoints
end

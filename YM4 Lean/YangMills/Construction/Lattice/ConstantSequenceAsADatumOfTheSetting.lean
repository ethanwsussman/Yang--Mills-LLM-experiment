import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice
noncomputable section
namespace YangMills.Construction.SeparatedSequence
theorem sUnion_standardCubePartition {L m : ℕ} (hL : 0 < L) (i : ℤ) :
    ⋃₀ standardCubePartition L m i = (univ : Set (FourTorus L m)) := by
  refine eq_univ_of_forall fun x => ?_
  have hmesh : 0 < meshSize L i := zpow_pos (by exact_mod_cast hL) _
  choose t ht using fun μ => QuotientAddGroup.mk_surjective (x μ)
  let n : Fin 4 → ℤ := fun μ => round (t μ / meshSize L i)
  let y : Site L m i :=
    ⟨fun μ => (((n μ : ℝ) * meshSize L i : ℝ) : AddCircle (torusSide L m)), n, fun _ => rfl⟩
  refine ⟨cubeAround y, ⟨y, rfl⟩, ?_⟩
  have hlift : TorusMetric.torusProj (torusSide L m) (fun μ => t μ - (n μ : ℝ) * meshSize L i) =
      x - (y : FourTorus L m) := by
    funext μ
    have h := ht μ
    simp only [TorusMetric.torusProj, Pi.sub_apply, AddCircle.coe_sub]
    rw [← h]
  have hbdd : BddBelow (TorusMetric.supNormVec ''
      (TorusMetric.torusProj (torusSide L m) ⁻¹' {x - (y : FourTorus L m)})) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨v, -, rfl⟩
    exact (abs_nonneg (v 0)).trans
      (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ (0 : Fin 4)))
  refine (csInf_le hbdd ⟨_, hlift, rfl⟩).trans ?_
  refine Finset.sup'_le _ _ fun μ _ => ?_
  have h := abs_sub_round (t μ / meshSize L i)
  have h2 : t μ - (n μ : ℝ) * meshSize L i =
      (t μ / meshSize L i - (round (t μ / meshSize L i) : ℝ)) * meshSize L i := by
    simp only [n]
    field_simp
  change |t μ - (n μ : ℝ) * meshSize L i| ≤ meshSize L i / 2
  rw [h2, abs_mul, abs_of_pos hmesh]
  nlinarith
end YangMills.Construction.SeparatedSequence

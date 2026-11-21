import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice
namespace SeparatedSequence
variable {L m : ℕ}
theorem sublattice_finite (hL : 0 < L) {i : ℤ} (hi : -(m : ℤ) ≤ i) :
    (sublattice L m i : Set (FourTorus L m)).Finite := by
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ (m : ℤ) + i by omega)
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hNpos : 0 < 2 * L ^ d := by positivity
  have hside : ((2 * L ^ d : ℕ) : ℝ) * meshSize L i = torusSide L m := by
    have hi' : i = (d : ℤ) - (m : ℤ) := by omega
    simp only [meshSize, torusSide, hi']
    push_cast
    rw [neg_sub, zpow_sub₀ hL', zpow_natCast, zpow_natCast]
    field_simp
  let f : (Fin 4 → Fin (2 * L ^ d)) → FourTorus L m :=
    fun c μ => ((((c μ : ℕ) : ℝ) * meshSize L i : ℝ) : AddCircle (torusSide L m))
  refine (Set.finite_range f).subset ?_
  rintro x ⟨n, hn⟩
  have hNz : ((2 * L ^ d : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hnn : ∀ μ, 0 ≤ n μ % ((2 * L ^ d : ℕ) : ℤ) := fun μ => Int.emod_nonneg _ hNz
  have hlt : ∀ μ, (n μ % ((2 * L ^ d : ℕ) : ℤ)).toNat < 2 * L ^ d := fun μ => by
    have := Int.emod_lt_of_pos (n μ) (show 0 < ((2 * L ^ d : ℕ) : ℤ) by exact_mod_cast hNpos)
    have h2 := hnn μ
    omega
  refine ⟨fun μ => ⟨(n μ % ((2 * L ^ d : ℕ) : ℤ)).toNat, hlt μ⟩, funext fun μ => ?_⟩
  have hcast : (((n μ % ((2 * L ^ d : ℕ) : ℤ)).toNat : ℕ) : ℝ) =
      ((n μ % ((2 * L ^ d : ℕ) : ℤ) : ℤ) : ℝ) := by
    have : (((n μ % ((2 * L ^ d : ℕ) : ℤ)).toNat : ℕ) : ℤ) = n μ % ((2 * L ^ d : ℕ) : ℤ) :=
      Int.toNat_of_nonneg (hnn μ)
    exact_mod_cast this
  have hdecomp : (n μ : ℝ) * meshSize L i =
      ((n μ % ((2 * L ^ d : ℕ) : ℤ) : ℤ) : ℝ) * meshSize L i +
        ((n μ / ((2 * L ^ d : ℕ) : ℤ) : ℤ) : ℝ) * torusSide L m := by
    rw [← hside]
    have h := Int.emod_add_mul_ediv (n μ) ((2 * L ^ d : ℕ) : ℤ)
    have h' : ((n μ % ((2 * L ^ d : ℕ) : ℤ) : ℤ) : ℝ) +
        ((2 * L ^ d : ℕ) : ℝ) * ((n μ / ((2 * L ^ d : ℕ) : ℤ) : ℤ) : ℝ) = (n μ : ℝ) := by
      exact_mod_cast h
    rw [← h']
    ring
  have hzero : (((((n μ / ((2 * L ^ d : ℕ) : ℤ) : ℤ) : ℝ) * torusSide L m : ℝ)) :
      AddCircle (torusSide L m)) = 0 :=
    (AddCircle.coe_eq_zero_iff _).2 ⟨n μ / ((2 * L ^ d : ℕ) : ℤ), by simp⟩
  simp only [f]
  rw [hn μ, hdecomp, AddCircle.coe_add, hzero, add_zero, hcast]
theorem torusSupNorm_le_iff {S : ℝ} (x : Torus4 S) (a : ℝ) :
    torusSupNorm x ≤ a ↔ ∀ μ, ‖x μ‖ ≤ a := by
  choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm (x μ)
  have hcov : torusProj S b = x := funext hb
  have hnonneg : ∀ v, 0 ≤ supNormVec v := fun v =>
    (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
  have heq : torusSupNorm x = supNormVec b := by
    apply le_antisymm
    · refine csInf_le ⟨0, ?_⟩ ⟨b, hcov, rfl⟩
      rintro _ ⟨v, -, rfl⟩
      exact hnonneg v
    · refine le_csInf ⟨_, b, hcov, rfl⟩ ?_
      rintro _ ⟨v, hv, rfl⟩
      have hv' : torusProj S v = x := hv
      refine Finset.sup'_le _ _ fun μ _ => ?_
      rw [hb' μ, ← hv']
      exact (addCircle_norm_coe_le_abs _).trans
        (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ μ))
  rw [heq]
  simp only [supNormVec, Finset.sup'_le_iff, Finset.mem_univ, forall_true_left, hb']
theorem isClosed_cubeAround {i : ℤ} (y : Site L m i) : IsClosed (cubeAround y) := by
  have h : cubeAround y =
      ⋂ μ, {x : FourTorus L m | ‖x μ - (y : FourTorus L m) μ‖ ≤ meshSize L i / 2} := by
    ext x
    simp only [cubeAround, mem_ofPred_eq, mem_iInter]
    exact torusSupNorm_le_iff (S := torusSide L m) (x - (y : FourTorus L m)) _
  rw [h]
  refine isClosed_iInter fun μ => isClosed_le ?_ continuous_const
  exact ((continuous_apply μ).sub continuous_const).norm
theorem isClosed_of_isPartitionRegion (hL : 0 < L) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {X : Set (FourTorus L m)} (h : IsPartitionRegion i X) : IsClosed X := by
  obtain ⟨C, hC, rfl⟩ := h
  have : Finite (Site L m i) := (sublattice_finite hL hi).to_subtype
  have hfin : (standardCubePartition L m i).Finite := Set.finite_range _
  rw [sUnion_eq_biUnion]
  refine Set.Finite.isClosed_biUnion (hfin.subset hC) fun Q hQ => ?_
  obtain ⟨y, rfl⟩ := hC hQ
  exact isClosed_cubeAround y
end SeparatedSequence
end YangMills.Construction

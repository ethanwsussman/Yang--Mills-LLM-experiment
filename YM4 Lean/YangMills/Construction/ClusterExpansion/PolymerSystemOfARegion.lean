import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
set_option autoImplicit false
open scoped Classical
noncomputable section
namespace YangMills.Construction.ClusterExpansion.RegionPolymers
open Set YangMills.Construction.PeriodicLattice
theorem sublattice_finite {L : ℕ} (hL : 0 < L) (m : ℕ) (i : ℤ) :
    (sublattice L m i : Set (FourTorus L m)).Finite := by
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ (m : ℤ) + max i (-(m : ℤ)) by omega)
  have hj : max i (-(m : ℤ)) = (d : ℤ) - (m : ℤ) := by omega
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hpos : 0 < 2 * L ^ d := by positivity
  have hposZ : ((2 * L ^ d : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hlen : ((2 * L ^ d : ℕ) : ℝ) * meshSize L ((d : ℤ) - (m : ℤ)) = torusSide L m := by
    simp only [meshSize, torusSide]
    push_cast
    rw [neg_sub, zpow_sub₀ hL0, zpow_natCast, zpow_natCast]
    field_simp
  let f : (Fin 4 → Fin (2 * L ^ d)) → FourTorus L m := fun c μ =>
    ((((c μ : ℕ) : ℝ) * meshSize L ((d : ℤ) - (m : ℤ)) : ℝ) : AddCircle (torusSide L m))
  refine (Set.finite_range f).subset fun x hx => ?_
  obtain ⟨n, hn⟩ := sublattice_mono hL m (le_max_left i (-(m : ℤ))) hx
  rw [hj] at hn
  have hnonneg : ∀ μ, 0 ≤ n μ % ((2 * L ^ d : ℕ) : ℤ) := fun μ => Int.emod_nonneg _ hposZ
  have hbound : ∀ μ, (n μ % ((2 * L ^ d : ℕ) : ℤ)).toNat < 2 * L ^ d := fun μ => by
    have h1 := Int.emod_lt_of_pos (n μ) (show 0 < ((2 * L ^ d : ℕ) : ℤ) by exact_mod_cast hpos)
    have h2 := hnonneg μ
    omega
  refine ⟨fun μ => ⟨(n μ % ((2 * L ^ d : ℕ) : ℤ)).toNat, hbound μ⟩, funext fun μ => ?_⟩
  have hcast : (((n μ % ((2 * L ^ d : ℕ) : ℤ)).toNat : ℕ) : ℝ) =
      ((n μ % ((2 * L ^ d : ℕ) : ℤ) : ℤ) : ℝ) := by
    have h : (((n μ % ((2 * L ^ d : ℕ) : ℤ)).toNat : ℕ) : ℤ) = n μ % ((2 * L ^ d : ℕ) : ℤ) :=
      Int.toNat_of_nonneg (hnonneg μ)
    exact_mod_cast h
  have hdecomp : (n μ : ℝ) * meshSize L ((d : ℤ) - (m : ℤ)) =
      ((n μ % ((2 * L ^ d : ℕ) : ℤ) : ℤ) : ℝ) * meshSize L ((d : ℤ) - (m : ℤ)) +
        ((n μ / ((2 * L ^ d : ℕ) : ℤ) : ℤ) : ℝ) * torusSide L m := by
    rw [← hlen]
    have h' : ((n μ % ((2 * L ^ d : ℕ) : ℤ) : ℤ) : ℝ) +
        ((2 * L ^ d : ℕ) : ℝ) * ((n μ / ((2 * L ^ d : ℕ) : ℤ) : ℤ) : ℝ) = (n μ : ℝ) := by
      exact_mod_cast Int.emod_add_mul_ediv (n μ) ((2 * L ^ d : ℕ) : ℤ)
    rw [← h']
    ring
  have hvanish : (((((n μ / ((2 * L ^ d : ℕ) : ℤ) : ℤ) : ℝ) * torusSide L m : ℝ)) :
      AddCircle (torusSide L m)) = 0 :=
    (AddCircle.coe_eq_zero_iff _).2 ⟨n μ / ((2 * L ^ d : ℕ) : ℤ), by simp⟩
  simp only [f]
  rw [hn μ, hdecomp, AddCircle.coe_add, hvanish, add_zero, hcast]
end YangMills.Construction.ClusterExpansion.RegionPolymers

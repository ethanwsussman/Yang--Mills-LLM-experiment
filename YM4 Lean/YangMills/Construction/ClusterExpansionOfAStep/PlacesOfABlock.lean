import YangMills.Construction.ClusterExpansionOfAStep.BallsAndBlocksOfATorusForm
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace BlockPlaces
open TorusFields TorusLumps StepSettings TorusBalls
variable {n L : ℕ}
theorem blockSite_cast_eq [NeZero n] [NeZero L] (y : TorusSite n) (o : BlockOffset L) (i : Fin 4) :
    ∃ k : ℤ, (((blockSite y o : TorusSite (n * L)) i).cast : ℤ) + ((L : ℤ) - 1) / 2 =
      (L : ℤ) * (((y i).cast : ℤ) + (n : ℤ) * k) + ((o i : ℕ) : ℤ) := by
  set a : ℤ := (L : ℤ) * ((y i).cast : ℤ) + (((o i : ℕ) : ℤ) - ((L : ℤ) - 1) / 2) with ha
  have hc : (((blockSite y o : TorusSite (n * L)) i).cast : ℤ) = a % ((n * L : ℕ) : ℤ) := by
    simp only [blockSite, siteOfInt]
    exact ZMod.coe_intCast _
  refine ⟨-(a / ((n * L : ℕ) : ℤ)), ?_⟩
  rw [hc, Int.emod_def, ha]
  push_cast
  ring
theorem parentBlock_blockSite [NeZero n] [NeZero L] (y : TorusSite n) (o : BlockOffset L) :
    parentBlock L (blockSite y o : TorusSite (n * L)) = y := by
  funext i
  obtain ⟨k, hk⟩ := blockSite_cast_eq (L := L) y o i
  have hpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hdiv : ((o i : ℕ) : ℤ) / (L : ℤ) = 0 :=
    Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast (o i).2)
  simp only [parentBlock]
  rw [hk, add_comm, Int.add_mul_ediv_left _ _ hpos.ne', hdiv, zero_add]
  push_cast
  simp
theorem siteOffset_blockSite [NeZero n] [NeZero L] (y : TorusSite n) (o : BlockOffset L) :
    siteOffset (blockSite y o : TorusSite (n * L)) = o := by
  funext i
  obtain ⟨k, hk⟩ := blockSite_cast_eq (L := L) y o i
  have hmod : (((o i : ℕ) : ℤ)) % (L : ℤ) = ((o i : ℕ) : ℤ) :=
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (o i).2)
  simp only [siteOffset]
  rw [hk, add_comm, Int.add_mul_emod_self_left, hmod]
  ext
  simp [Fin.ofNat, Nat.mod_eq_of_lt (o i).2]
theorem blockSite_parentBlock_siteOffset [NeZero n] [NeZero L] (x : TorusSite (n * L)) :
    blockSite (parentBlock L x) (siteOffset x) = x := by
  have hpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  funext i
  set h : ℤ := ((L : ℤ) - 1) / 2
  set a : ℤ := ((x i).cast : ℤ) + h with ha
  have hr0 : 0 ≤ a % (L : ℤ) := Int.emod_nonneg _ hpos.ne'
  have hr1 : a % (L : ℤ) < L := Int.emod_lt_of_pos _ hpos
  have hval : (((siteOffset x i : Fin L) : ℕ) : ℤ) = a % (L : ℤ) := by
    simp only [siteOffset, Fin.ofNat]
    have : ((a % (L : ℤ)).toNat) % L = (a % (L : ℤ)).toNat :=
      Nat.mod_eq_of_lt (by omega)
    rw [show (((((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) % (L : ℤ)).toNat) = (a % (L : ℤ)).toNat from rfl, this]
    exact Int.toNat_of_nonneg hr0
  have hcast : ∃ k : ℤ, (((parentBlock L x i : ZMod n)).cast : ℤ) = a / (L : ℤ) + (n : ℤ) * k := by
    have : (((parentBlock L x i : ZMod n)).cast : ℤ) = (a / (L : ℤ)) % (n : ℤ) := by
      simp only [parentBlock]
      exact ZMod.coe_intCast _
    refine ⟨-((a / (L : ℤ)) / (n : ℤ)), ?_⟩
    rw [this, Int.emod_def]
    ring
  obtain ⟨k, hk⟩ := hcast
  simp only [blockSite, siteOfInt]
  rw [hk, hval]
  have h1 : (L : ℤ) * (a / (L : ℤ)) + a % (L : ℤ) = a := Int.mul_ediv_add_emod a L
  have h2 : (L : ℤ) * (a / (L : ℤ) + (n : ℤ) * k) + (a % (L : ℤ) - h) =
      ((x i).cast : ℤ) + ((n * L : ℕ) : ℤ) * k := by
    push_cast
    linear_combination h1 + ha
  rw [h2, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]
  exact ZMod.intCast_zmod_cast _
theorem supDist_parentBlock_le_one [NeZero n] [NeZero L] (hL : 2 ≤ L) (p q : TorusSite (n * L))
    (h : supDist p q ≤ 1) :
    supDist (parentBlock L p) (parentBlock L q) ≤ 1 := by
  have h1 := supDist_parentBlock_le_div_add_one L p q
  have h2 : supDist p q / L = 0 := Nat.div_eq_of_lt (by omega)
  omega
end BlockPlaces
end YangMills.Construction
end

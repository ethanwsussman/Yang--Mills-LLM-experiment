import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import YangMills.Construction.ClusterExpansionOfAStep.FineDistanceByBlocks
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open TorusFields
theorem fineDistanceLeBlockDistance : FineDistanceLeBlockDistance := by
  intro n L _ _ x x'
  have hL : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [supDist_le_iff]
  intro i
  set t := supDist (parentBlock L x) (parentBlock L x') with ht
  set r : ℤ := ((L : ℤ) - 1) / 2 with hr
  set a : ℤ := ((x i).cast : ℤ) with ha
  set a' : ℤ := ((x' i).cast : ℤ) with ha'
  set q : ℤ := (a + r) / L with hq
  set q' : ℤ := (a' + r) / L with hq'
  have hblock : ∀ y : TorusSite (n * L), parentBlock L y i = ((((y i).cast : ℤ) + r) / (L : ℤ) : ℤ) :=
    fun y => rfl
  set e : ℤ := ((parentBlock L x i - parentBlock L x' i : ZMod n)).valMinAbs with he
  have het : e.natAbs ≤ t := (supDist_le_iff _ _ _).1 le_rfl i
  have hecast : ((e : ℤ) : ZMod n) = ((q - q' : ℤ) : ZMod n) := by
    rw [he, ZMod.coe_valMinAbs, hblock x, hblock x']
    push_cast
    rfl
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hecast
  obtain ⟨k, hk⟩ := hecast
  have hcast : ((x i - x' i : ZMod (n * L))) = ((a - a' : ℤ) : ZMod (n * L)) := by
    simp [ha, ha']
  set u : ℤ := (a + r) % L with hu
  set u' : ℤ := (a' + r) % L with hu'
  have e1 : a + r = L * q + u := (Int.mul_ediv_add_emod _ _).symm
  have e2 : a' + r = L * q' + u' := (Int.mul_ediv_add_emod _ _).symm
  have hu0 : 0 ≤ u := Int.emod_nonneg _ hL.ne'
  have hu1 : u < L := Int.emod_lt_of_pos _ hL
  have hu0' : 0 ≤ u' := Int.emod_nonneg _ hL.ne'
  have hu1' : u' < L := Int.emod_lt_of_pos _ hL
  have hrep : ((a - a' : ℤ) : ZMod (n * L)) = (((L : ℤ) * e + (u - u') : ℤ) : ZMod (n * L)) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨-k, ?_⟩
    have h3 : a - a' = L * (q - q') + (u - u') := by linarith
    have h4 : q - q' = e + (n : ℤ) * k := by linarith
    rw [h3, h4]
    push_cast
    ring
  rw [hcast, hrep]
  refine (natAbs_valMinAbs_intCast_le _).trans ?_
  have h5 : |(L : ℤ) * e + (u - u')| ≤ L * t + L := by
    have h6 : |(L : ℤ) * e| ≤ L * t := by
      rw [abs_mul, abs_of_pos hL]
      have : |e| ≤ (t : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast het
      exact mul_le_mul_of_nonneg_left this hL.le
    have h7 : |u - u'| ≤ L := by
      rw [abs_le]
      constructor <;> linarith
    exact (abs_add_le _ _).trans (by linarith)
  rw [Int.abs_eq_natAbs] at h5
  exact_mod_cast h5
end YangMills.Construction.TorusLumps
end

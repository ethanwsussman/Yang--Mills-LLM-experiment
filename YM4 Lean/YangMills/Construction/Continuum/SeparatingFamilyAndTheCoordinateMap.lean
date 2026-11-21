import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.Lattice.AdicGridPointsPositive
import YangMills.Construction.TestFunctions.RationalBoxFamilies
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.SeparatingFamily
open TestFunctions InfiniteLattice
abbrev ScalarField : Type := (Fin 4 → ℝ) → ℝ
def adicLatticeVectors (L : ℕ) : Set (Fin 4 → ℝ) :=
  {v | ∀ κ, v κ ∈ PeriodicLattice.adicGridPointsPositive L}
theorem exists_meshSize_eq_intCast_mul (L : ℕ) {k j : ℕ} (hk : 0 < k) (hkj : k ≤ j) :
    ∃ c : ℤ, PeriodicLattice.meshSize L (k : ℤ) = (c : ℝ) * PeriodicLattice.meshSize L (j : ℤ) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · refine ⟨0, ?_⟩
    have hk' : -(k : ℤ) ≠ 0 := by omega
    simp [PeriodicLattice.meshSize, zero_zpow _ hk']
  · refine ⟨(L : ℤ) ^ (j - k), ?_⟩
    have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    unfold PeriodicLattice.meshSize
    push_cast
    rw [← zpow_natCast, ← zpow_add₀ hL']
    congr 1
    omega
theorem zero_mem_adicGridPointsPositive (L : ℕ) :
    (0 : ℝ) ∈ PeriodicLattice.adicGridPointsPositive L :=
  (PeriodicLattice.mem_adicGridPointsPositive_iff L 0).2 ⟨1, 0, by simp⟩
theorem neg_mem_adicGridPointsPositive {L : ℕ} {x : ℝ}
    (hx : x ∈ PeriodicLattice.adicGridPointsPositive L) :
    -x ∈ PeriodicLattice.adicGridPointsPositive L := by
  obtain ⟨k, n, rfl⟩ := (PeriodicLattice.mem_adicGridPointsPositive_iff L x).1 hx
  exact (PeriodicLattice.mem_adicGridPointsPositive_iff L _).2 ⟨k, -n, by push_cast; ring⟩
theorem add_mem_adicGridPointsPositive {L : ℕ} {x y : ℝ}
    (hx : x ∈ PeriodicLattice.adicGridPointsPositive L)
    (hy : y ∈ PeriodicLattice.adicGridPointsPositive L) :
    x + y ∈ PeriodicLattice.adicGridPointsPositive L := by
  obtain ⟨k, n, rfl⟩ := (PeriodicLattice.mem_adicGridPointsPositive_iff L x).1 hx
  obtain ⟨j, m, rfl⟩ := (PeriodicLattice.mem_adicGridPointsPositive_iff L y).1 hy
  obtain ⟨c, hc⟩ := exists_meshSize_eq_intCast_mul L k.pos (show (k : ℕ) ≤ ((k + j : ℕ+) : ℕ) by simp)
  obtain ⟨d, hd⟩ := exists_meshSize_eq_intCast_mul L j.pos (show (j : ℕ) ≤ ((k + j : ℕ+) : ℕ) by simp)
  refine (PeriodicLattice.mem_adicGridPointsPositive_iff L _).2 ⟨k + j, n * c + m * d, ?_⟩
  rw [hc, hd]
  push_cast
  ring
theorem zero_mem_adicLatticeVectors (L : ℕ) : (0 : Fin 4 → ℝ) ∈ adicLatticeVectors L :=
  fun _ => zero_mem_adicGridPointsPositive L
theorem add_mem_adicLatticeVectors {L : ℕ} {v v' : Fin 4 → ℝ} (hv : v ∈ adicLatticeVectors L)
    (hv' : v' ∈ adicLatticeVectors L) : v + v' ∈ adicLatticeVectors L :=
  fun κ => add_mem_adicGridPointsPositive (hv κ) (hv' κ)
theorem neg_mem_adicLatticeVectors {L : ℕ} {v : Fin 4 → ℝ} (hv : v ∈ adicLatticeVectors L) :
    -v ∈ adicLatticeVectors L :=
  fun κ => neg_mem_adicGridPointsPositive (hv κ)
theorem map_mem_adicLatticeVectors {L : ℕ} {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace}
    (hw : w ∈ hyperoctahedralLinearGroup)
    {v : Fin 4 → ℝ} (hv : v ∈ adicLatticeVectors L) : w v ∈ adicLatticeVectors L := by
  obtain ⟨π, s, h⟩ := (mem_hyperoctahedralLinearGroup_iff w).1 hw
  intro κ
  rw [h]
  rcases Int.units_eq_one_or (s κ) with hs | hs
  · simpa [hs] using hv (π κ)
  · simpa [hs] using neg_mem_adicGridPointsPositive (hv (π κ))
def adicHyperoctahedralMotions (L : ℕ) : Subgroup (Equiv.Perm (Fin 4 → ℝ)) where
  carrier := {r | ∃ w ∈ hyperoctahedralLinearGroup, ∃ v ∈ adicLatticeVectors L, ∀ x, r x = w x + v}
  mul_mem' := by
    rintro r s ⟨w, hw, v, hv, hr⟩ ⟨w', hw', v', hv', hs⟩
    refine ⟨w * w', mul_mem hw hw', w v' + v,
      add_mem_adicLatticeVectors (map_mem_adicLatticeVectors hw hv') hv, fun x => ?_⟩
    rw [Equiv.Perm.mul_apply, hs, hr, map_add, LinearEquiv.mul_apply, add_assoc]
  one_mem' := ⟨1, one_mem _, 0, zero_mem_adicLatticeVectors L, fun x => by simp⟩
  inv_mem' := by
    rintro r ⟨w, hw, v, hv, hr⟩
    refine ⟨w⁻¹, inv_mem hw, -(w⁻¹ v),
      neg_mem_adicLatticeVectors (map_mem_adicLatticeVectors (inv_mem hw) hv), fun x => ?_⟩
    have hinv : ∀ y, w (w⁻¹ y) = y := fun y => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    apply r.injective
    rw [show r (r⁻¹ x) = x from r.apply_symm_apply x, hr, map_add, map_neg, hinv, hinv]
    abel
def fixedDenseSets : ratBoxUnions → Set ScalarField :=
  Classical.epsilon IsDenseFamily
theorem isDenseFamily_fixedDenseSets (h : ∃ D, IsDenseFamily D) :
    IsDenseFamily fixedDenseSets :=
  Classical.epsilon_spec h
def ratMotionSpan (L : ℕ) : Set ScalarField :=
  {φ | ∃ (n : ℕ) (q : Fin n → ℚ) (f : Fin n → ScalarField) (r : Fin n → Equiv.Perm (Fin 4 → ℝ)),
    (∀ i, f i ∈ ⋃ Q, fixedDenseSets Q) ∧ (∀ i, r i ∈ adicHyperoctahedralMotions L) ∧
      φ = ∑ i, (q i : ℝ) • (f i ∘ ⇑(r i)⁻¹)}
def motionDenseSets (L : ℕ) (Q : ratBoxUnions) : Set ScalarField :=
  ratMotionSpan L ∩ c1ZeroOff Q
def separatingTuples (L : ℕ) : Set (List ScalarField) :=
  {[]} ∪ disjointTupleFamily (motionDenseSets L)
end YangMills.Construction.SeparatingFamily
end

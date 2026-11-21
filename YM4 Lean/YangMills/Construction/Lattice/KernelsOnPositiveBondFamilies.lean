import YangMills.Construction.Lattice.BondLinearMaps
import YangMills.Construction.Lattice.LieFieldsOnBondSets
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
theorem Bond.opposite_not_isPositivelyOriented {L m : ℕ} {j : ℤ} (hL : 1 < L) (hj : -(m : ℤ) < j)
    {b : Bond L m j} (h : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  have hmesh : ∀ t : ℤ, meshSize L j ≠ (t : ℝ) * (L : ℝ) ^ m := by
    intro t ht
    obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ (m : ℤ) + j - 1 by omega)
    have hneg : -j = (m : ℤ) - ((d + 1 : ℕ) : ℤ) := by push_cast; omega
    have e1 : (L : ℝ) ^ m = (t : ℝ) * (L : ℝ) ^ m * (L : ℝ) ^ (d + 1) := by
      rw [← ht, meshSize, hneg, zpow_sub₀ hL0, zpow_natCast, zpow_natCast]
      field_simp
    have e2 : (t : ℝ) * (L : ℝ) ^ (d + 1) = 1 := by
      have hpow : (L : ℝ) ^ m ≠ 0 := pow_ne_zero _ hL0
      apply mul_left_cancel₀ hpow
      linear_combination -e1
    have e3 : t * (L : ℤ) ^ (d + 1) = 1 := by exact_mod_cast e2
    have e4 : (L : ℤ) ∣ 1 := ⟨t * (L : ℤ) ^ d, by rw [← e3]; ring⟩
    have e5 := Int.le_of_dvd one_pos e4
    omega
  obtain ⟨μ, hμ⟩ := h
  rintro ⟨ν, hν⟩
  have hsum : unitStep L m j μ + unitStep L m j ν = 0 := by
    rw [← hμ, ← hν]
    change b.target - b.source + (b.source - b.target) = 0
    abel
  have hcoord := congrArg (fun x : Site L m j => (x : FourTorus L m) μ) hsum
  by_cases hνμ : ν = μ
  · subst hνμ
    simp only [unitStep, AddSubgroup.coe_add, Pi.add_apply, pointOnAxis, Pi.single_eq_same,
      ZeroMemClass.coe_zero, Pi.zero_apply] at hcoord
    rw [← AddCircle.coe_add, AddCircle.coe_eq_zero_iff] at hcoord
    obtain ⟨t, ht⟩ := hcoord
    refine hmesh t ?_
    simp only [torusSide, zsmul_eq_mul] at ht
    linarith
  · have hne : μ ≠ ν := fun e => hνμ e.symm
    simp only [unitStep, AddSubgroup.coe_add, Pi.add_apply, pointOnAxis, Pi.single_eq_same,
      Pi.single_eq_of_ne hne, ZeroMemClass.coe_zero, Pi.zero_apply, add_zero] at hcoord
    rw [AddCircle.coe_eq_zero_iff] at hcoord
    obtain ⟨t, ht⟩ := hcoord
    refine hmesh (2 * t) ?_
    simp only [torusSide, zsmul_eq_mul] at ht
    push_cast
    linarith
structure PositiveBondFamily (L m K n : ℕ) where
  bonds : Finset (BondAtLevel L m K n)
  isPositive : ∀ b ∈ bonds, b.IsPositivelyOriented
namespace PositiveBondFamily
variable {L m K n n' : ℕ}
def symmetrization (C : PositiveBondFamily L m K n) : SymmetricBondSet L m K n where
  bonds := {b | b ∈ C.bonds ∨ b.opposite ∈ C.bonds}
  opposite_mem := fun _ hb => hb.symm
abbrev LieField (C : PositiveBondFamily L m K n) : Type := LieBondField C.symmetrization
def toPositiveBond (C : PositiveBondFamily L m K n) (c : ↥C.bonds) :
    PositiveBondsOf C.symmetrization :=
  ⟨c.1, Or.inl c.2, C.isPositive c.1 c.2⟩
end PositiveBondFamily
variable {L m K n n' : ℕ}
abbrev FamilyLinearMap (P : PositiveBondFamily L m K n) (C : PositiveBondFamily L m K n') : Type :=
  BondMaps.BondLinearMap (PositiveBondsOf P.symmetrization) (PositiveBondsOf C.symmetrization)
namespace FamilyLinearMap
variable {P : PositiveBondFamily L m K n} {C : PositiveBondFamily L m K n'}
  [Fintype (PositiveBondsOf P.symmetrization)] [Fintype (PositiveBondsOf C.symmetrization)]
def kernel (T : FamilyLinearMap P C) (c : ↥C.bonds) (b : ↥P.bonds) :
    ↥Matrices.ComplexMatrix2.traceless →ₗ[ℂ] ↥Matrices.ComplexMatrix2.traceless :=
  BondMaps.BondLinearMap.kernel T (C.toPositiveBond c) (P.toPositiveBond b)
def kernelNorm (T : FamilyLinearMap P C) (c : ↥C.bonds) (b : ↥P.bonds) : ℝ :=
  BondMaps.BondLinearMap.kernelNorm T (C.toPositiveBond c) (P.toPositiveBond b)
def rowSumNorm (T : FamilyLinearMap P C) : ℝ := ⨆ c : ↥C.bonds, ∑ b : ↥P.bonds, T.kernelNorm c b
def columnSumNorm (T : FamilyLinearMap P C) : ℝ :=
  ⨆ b : ↥P.bonds, ∑ c : ↥C.bonds, T.kernelNorm c b
end FamilyLinearMap
end YangMills.Construction.PeriodicLattice

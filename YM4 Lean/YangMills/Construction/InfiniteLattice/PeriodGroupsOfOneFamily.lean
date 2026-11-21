import YangMills.Construction.InfiniteLattice.SixteenFamiliesHeightsPositionsAndSides
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction
namespace NormalFamilies
open InfiniteLattice
def evenLattice : AddSubgroup AmbientSpace := latticeSubgroup 2
def orthogonalSubgroup (n : AmbientSpace) : AddSubgroup AmbientSpace where
  carrier := {x | n ⬝ᵥ x = 0}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [dotProduct_add, hx, hy, add_zero]
  zero_mem' := by simp
  neg_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [dotProduct_neg, hx, neg_zero]
def parallelPeriodLattice (n : AmbientSpace) : AddSubgroup AmbientSpace :=
  evenLattice ⊓ orthogonalSubgroup n
def axialPeriodLattice (n : AmbientSpace) (h : ℤ) : AddSubgroup AmbientSpace :=
  parallelPeriodLattice n ⊔ AddSubgroup.zmultiples ((h : ℝ) • firstNonzeroBasisVec n)
def normalPeriodLattice (n : AmbientSpace) (h : ℤ) : AddSubgroup AmbientSpace :=
  parallelPeriodLattice n ⊔ AddSubgroup.zmultiples ((2 * (h : ℝ)) • dualVector n)
open Classical in
def axialPeriodDensity (n : AmbientSpace) (h : ℤ) : ℝ :=
  if axialPeriodLattice n h ≤ latticeSubgroup 1 ∧
      (axialPeriodLattice n h).relIndex (latticeSubgroup 1) ≠ 0 then
    ((axialPeriodLattice n h).relIndex (latticeSubgroup 1) : ℝ)⁻¹
  else 0
theorem mem_axialPeriodLattice_iff {n x : AmbientSpace} {h : ℤ} :
    x ∈ axialPeriodLattice n h ↔
      ∃ y ∈ parallelPeriodLattice n, ∃ k : ℤ, y + k • ((h : ℝ) • firstNonzeroBasisVec n) = x := by
  simp only [axialPeriodLattice, AddSubgroup.mem_sup, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨y, hy, _, ⟨k, rfl⟩, rfl⟩
    exact ⟨y, hy, k, rfl⟩
  · rintro ⟨y, hy, k, rfl⟩
    exact ⟨y, hy, _, ⟨k, rfl⟩, rfl⟩
theorem mem_normalPeriodLattice_iff {n x : AmbientSpace} {h : ℤ} :
    x ∈ normalPeriodLattice n h ↔
      ∃ y ∈ parallelPeriodLattice n, ∃ k : ℤ, y + k • ((2 * (h : ℝ)) • dualVector n) = x := by
  simp only [normalPeriodLattice, AddSubgroup.mem_sup, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨y, hy, _, ⟨k, rfl⟩, rfl⟩
    exact ⟨y, hy, k, rfl⟩
  · rintro ⟨y, hy, k, rfl⟩
    exact ⟨y, hy, _, ⟨k, rfl⟩, rfl⟩
end NormalFamilies
end YangMills.Construction

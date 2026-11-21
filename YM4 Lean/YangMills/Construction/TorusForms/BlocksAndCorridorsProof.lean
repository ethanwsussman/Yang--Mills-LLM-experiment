import YangMills.Construction.TorusForms.BlocksCorridorsDomainsTrees
import YangMills.Construction.TorusForms.InequalitiesOfOneCorridorProof
import Mathlib
noncomputable section
namespace YangMills.Construction
open Lattice
namespace BlockSpin
namespace CorridorFaces
open Finset
variable {S : LatticeParameters} {ℓ : Fin S.d → ℝ}
theorem gridPoint_add (σ τ : Fin S.d → ℤ) :
    gridPoint ℓ 1 (σ + τ) = gridPoint ℓ 1 σ + gridPoint ℓ 1 τ := by apply _root_.YangMills.Construction.BlockSpin.CorridorInequalities.gridPoint_add <;> assumption
def unitPeriod (S : LatticeParameters) (ℓ : Fin S.d → ℝ) [h : PeriodsMultipleOfBlock S ℓ]
    (μ : Fin S.d) : ℕ :=
  (h.multiple μ).choose * S.L
variable [hP : PeriodsMultipleOfBlock S ℓ]
theorem gridPoint_eq_gridPoint_iff (m n : Fin S.d → ℤ) :
    gridPoint ℓ 1 m = gridPoint ℓ 1 n ↔ ∀ μ, (m μ : ZMod (unitPeriod S ℓ μ)) = n μ := by apply _root_.YangMills.Construction.BlockSpin.CorridorInequalities.gridPoint_eq_gridPoint_iff <;> assumption
abbrev fineSite (y : LatticeSite ℓ (S.L : ℝ)) : LatticeSite ℓ 1 :=
  (PeriodsMultipleOfBlock.isBlockSpacing_one (S := S) (ℓ := ℓ)).toFineSite y
theorem mem_blockOf_iff {y : LatticeSite ℓ (S.L : ℝ)} {x : LatticeSite ℓ 1} :
    x ∈ blockOf S 1 1 y ↔ ∃ σ, InBlockIndexRange S 1 σ ∧ x = fineSite y + gridPoint ℓ 1 σ := by
  constructor
  · rintro ⟨σ, hr, he⟩
    exact ⟨σ, hr, Subtype.ext he⟩
  · rintro ⟨σ, hr, rfl⟩
    exact ⟨σ, hr, rfl⟩
theorem blockOffset_one (S : LatticeParameters) : blockOffset S 1 = S.offset := by apply _root_.YangMills.Construction.SeparatedClasses.TreeLowerBound.blockOffset_one <;> assumption
def lowIndex (S : LatticeParameters) : ℤ := -(S.offset : ℤ)
def highIndex (S : LatticeParameters) : ℤ := (S.L : ℤ) - 1 - S.offset
theorem highIndex_eq (S : LatticeParameters) : highIndex S = lowIndex S + ((S.L : ℤ) - 1) := by
  simp only [highIndex, lowIndex]
  ring
theorem inBlockIndexRange_iff (σ : Fin S.d → ℤ) :
    InBlockIndexRange S 1 σ ↔ ∀ μ, lowIndex S ≤ σ μ ∧ σ μ ≤ highIndex S := by
  simp only [InBlockIndexRange, blockOffset_one, pow_one, lowIndex, highIndex]
def indexSlice (y : LatticeSite ℓ (S.L : ℝ)) (μ : Fin S.d) (t : ℤ) : Set (LatticeSite ℓ 1) :=
  {x | ∃ σ, InBlockIndexRange S 1 σ ∧ σ μ = t ∧ x = fineSite y + gridPoint ℓ 1 σ}
omit hP in
theorem gridPoint_single_natCast (μ : Fin S.d) (k : ℕ) :
    ((gridPoint ℓ 1 (Pi.single μ (k : ℤ)) : LatticeSite ℓ 1) : PeriodicTorus ℓ) =
      k • ((latticeStep ℓ 1 μ : LatticeSite ℓ 1) : PeriodicTorus ℓ) := by
  show torusMk ℓ _ = k • torusMk ℓ _
  rw [← map_nsmul]
  congr 1
  funext ν
  by_cases h : ν = μ
  · subst h; simp [basisVector]
  · simp [basisVector, h]
theorem isBlockSpacing_unit : IsBlockSpacing S 1 ℓ 1 (S.L : ℝ) :=
  PeriodsMultipleOfBlock.isBlockSpacing_one
theorem add_latticeStep_ne (H : BlockGeometry) (y : LatticeSite ℓ (S.L : ℝ))
    (μ : Fin S.d) : y + latticeStep ℓ (S.L : ℝ) μ ≠ y := fun h =>
  (((H.1 S ℓ 1 (S.L : ℝ) 1 isBlockSpacing_unit).2.2.1) y μ).2 (by rw [h])
theorem inBlockIndexRange_add_single {τ : Fin S.d → ℤ} (hτ : InBlockIndexRange S 1 τ)
    {μ : Fin S.d} (hst : τ μ = lowIndex S) :
    InBlockIndexRange S 1 (τ + Pi.single μ ((S.L : ℤ) - 1)) := by
  rw [inBlockIndexRange_iff] at hτ ⊢
  intro ν
  by_cases h : ν = μ
  · subst h
    have h1 := highIndex_eq S
    have h2 := S.two_le_L
    simp only [Pi.add_apply, Pi.single_eq_same, hst]
    omega
  · simpa [h] using hτ ν
end CorridorFaces
end BlockSpin
end YangMills.Construction

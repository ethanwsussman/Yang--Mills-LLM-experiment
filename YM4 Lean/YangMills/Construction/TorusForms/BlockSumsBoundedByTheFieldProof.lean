import YangMills.Construction.SeparatedSequences.LowerBoundOnTheContoursAtEveryLevelProof
import YangMills.Construction.TorusForms.BlocksCorridorsDomainsTrees
import Mathlib
noncomputable section
namespace YangMills.Construction.BlockSpin.EnergyBound
open Finset
open YangMills.Construction.Lattice
section IntegerBox
variable {d : ℕ}
def intBox (a b : ℤ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Icc a b
theorem mem_intBox {a b : ℤ} {σ : Fin d → ℤ} : σ ∈ intBox a b ↔ ∀ m, a ≤ σ m ∧ σ m ≤ b := by
  simp [intBox, Fintype.mem_piFinset]
def zeroBelow (σ : Fin d → ℤ) (n : ℕ) : Fin d → ℤ := fun m => if m.val < n then 0 else σ m
variable (a b : ℤ) (U : (Fin d → ℤ) → Fin d → ℝ)
variable {a b U}
end IntegerBox
section OnTorus
theorem blockOffset_one (S : LatticeParameters) : blockOffset S 1 = S.offset := by apply _root_.YangMills.Construction.SeparatedClasses.TreeLowerBound.blockOffset_one <;> assumption
variable (S : LatticeParameters) {ℓ : Fin S.d → ℝ} [PeriodsMultipleOfBlock S ℓ]
def blockPoint (y : LatticeSite ℓ (S.L : ℝ)) (σ : Fin S.d → ℤ) : LatticeSite ℓ 1 :=
  (PeriodsMultipleOfBlock.isBlockSpacing_one (S := S) (ℓ := ℓ)).toFineSite y + gridPoint ℓ 1 σ
end OnTorus
end YangMills.Construction.BlockSpin.EnergyBound

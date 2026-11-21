import YangMills.Construction.SeparatedSequences.ChosenConstantsOfTheConditions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses.TreeLowerBound
open Lattice BlockSpin Finset
section Translation
variable {d : ℕ} {ℓ : Fin d → ℝ} {ε : ℝ}
theorem gridPoint_add (σ σ' : Fin d → ℤ) :
    gridPoint ℓ ε (σ + σ') = gridPoint ℓ ε σ + gridPoint ℓ ε σ' := by
  apply Subtype.ext
  show torusMk ℓ _ = torusMk ℓ _ + torusMk ℓ _
  rw [← map_add]
  congr 1
  funext μ
  simp [add_mul]
end Translation
variable (S : LatticeParameters) {ℓ : Fin S.d → ℝ}
theorem blockOffset_one : blockOffset S 1 = S.offset := by
  have hL : 0 < S.L - 1 := by have := S.two_le_L; omega
  simp only [blockOffset, pow_one]
  exact Nat.mul_div_cancel _ hL
def offsetPoint (ℓ : Fin S.d → ℝ) : LatticeSite ℓ 1 := gridPoint ℓ 1 fun _ => (S.offset : ℤ)
variable [PeriodsMultipleOfBlock S ℓ]
end YangMills.Construction.SeparatedClasses.TreeLowerBound
end

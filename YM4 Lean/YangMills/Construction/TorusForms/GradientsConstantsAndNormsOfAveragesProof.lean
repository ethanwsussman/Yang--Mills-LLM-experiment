import YangMills.Construction.TorusForms.CurlOfABlockAverageProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.BlockAverageBasics
open Lattice BlockSpin
variable {S : LatticeParameters} {ℓ : Fin S.d → ℝ} {n : ℕ} {ε ε' : ℝ}
  [IsCommensurateSpacing ℓ ε] [IsCommensurateSpacing ℓ ε']
theorem L_cast_pos (S : LatticeParameters) : (0 : ℝ) < S.L := by
  exact_mod_cast lt_of_lt_of_le two_pos S.two_le_L
section Partition
variable {h : IsBlockSpacing S n ℓ ε ε'}
omit [IsCommensurateSpacing ℓ ε] [IsCommensurateSpacing ℓ ε'] in
theorem gridPoint_single (μ : Fin S.d) :
    gridPoint ℓ ε' (Pi.single μ 1) = latticeStep ℓ ε' μ := by apply _root_.YangMills.Construction.BlockSpin.gridPoint_single <;> assumption
omit [IsCommensurateSpacing ℓ ε] [IsCommensurateSpacing ℓ ε'] in
theorem toFineSite_latticeStep (h : IsBlockSpacing S n ℓ ε ε') (μ : Fin S.d) :
    h.toFineSite (latticeStep ℓ ε' μ) = S.L ^ n • latticeStep ℓ ε μ := by apply _root_.YangMills.Construction.BlockSpin.toFineSite_latticeStep <;> assumption
end Partition
end YangMills.Construction.BlockAverageBasics

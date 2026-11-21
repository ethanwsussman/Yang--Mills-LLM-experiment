import YangMills.Construction.TorusForms.BlocksCorridorsDomains
import Mathlib
noncomputable section
namespace YangMills.Construction.BlockSpin
open Finset Lattice
section Telescope
variable {d : ℕ} {ℓ : Fin d → ℝ} {ε : ℝ}
end Telescope
section Blocks
variable {S : LatticeParameters} {ℓ : Fin S.d → ℝ} {n : ℕ} {ε ε' : ℝ}
theorem toFineSite_latticeStep (h : IsBlockSpacing S n ℓ ε ε') (μ : Fin S.d) :
    h.toFineSite (latticeStep ℓ ε' μ) = (S.L ^ n) • latticeStep ℓ ε μ := by
  apply Subtype.ext
  show torusMk ℓ (ε' • basisVector μ) = (S.L ^ n) • torusMk ℓ (ε • basisVector μ)
  rw [← map_nsmul, h.spacing_eq]
  congr 1
  funext ρ
  simp [mul_assoc]
theorem gridPoint_single (ε' : ℝ) (μ : Fin S.d) :
    gridPoint ℓ ε' (Pi.single μ 1) = latticeStep ℓ ε' μ := by
  apply Subtype.ext
  show torusMk ℓ _ = torusMk ℓ (ε' • basisVector μ)
  congr 1
  funext ρ
  by_cases hρ : ρ = μ
  · subst hρ
    simp [basisVector]
  · simp [basisVector, hρ]
variable [IsCommensurateSpacing ℓ ε] [IsCommensurateSpacing ℓ ε']
end Blocks
end YangMills.Construction.BlockSpin

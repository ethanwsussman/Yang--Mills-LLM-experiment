import YangMills.Construction.TorusForms.BlocksCorridorsDomains
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.BlockSpin.BlockUnions
open Lattice
theorem mem_supportedIn {ι : Type*} {X : Set ι} {f : ι → ℝ} :
    f ∈ supportedIn X ↔ ∀ i, i ∉ X → f i = 0 := Iff.rfl
section Grid
variable {d : ℕ} {ℓ : Fin d → ℝ} {a : ℝ}
theorem gridPoint_add (σ τ : Fin d → ℤ) :
    (gridPoint ℓ a (σ + τ) : PeriodicTorus ℓ) =
      (gridPoint ℓ a σ : PeriodicTorus ℓ) + (gridPoint ℓ a τ : PeriodicTorus ℓ) := by
  show torusMk ℓ _ = torusMk ℓ _ + torusMk ℓ _
  rw [← map_add]
  congr 1
  funext μ
  simp [add_mul]
theorem gridPoint_single (m : ℤ) (μ : Fin d) :
    (gridPoint ℓ a (Pi.single μ m) : PeriodicTorus ℓ) = m • (latticeStep ℓ a μ : PeriodicTorus ℓ) := by
  show torusMk ℓ _ = m • torusMk ℓ _
  rw [← map_zsmul]
  congr 1
  funext ν
  by_cases hνμ : ν = μ
  · subst hνμ
    simp [basisVector]
  · simp [basisVector, hνμ]
end Grid
section Blocks
variable {P : LatticeParameters} {ℓ : Fin P.d → ℝ} {a b : ℝ} {n : ℕ}
theorem inBlockIndexRange_add_single {σ : Fin P.d → ℤ} (hσ : InBlockIndexRange P n σ) (μ : Fin P.d) (m : ℤ)
    (hlow : -(blockOffset P n : ℤ) ≤ σ μ + m)
    (hhigh : σ μ + m ≤ (P.L : ℤ) ^ n - 1 - blockOffset P n) :
    InBlockIndexRange P n (σ + Pi.single μ m) := by
  intro ν
  by_cases hνμ : ν = μ
  · subst hνμ
    simpa using ⟨hlow, hhigh⟩
  · simpa [hνμ] using hσ ν
end Blocks
end YangMills.Construction.BlockSpin.BlockUnions

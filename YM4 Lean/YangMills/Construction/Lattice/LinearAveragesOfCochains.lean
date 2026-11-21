import YangMills.Construction.Lattice.BlockAveraging
import YangMills.Construction.Lattice.Cochains
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j j' : ℤ}
def contourMeanOfCochain (α : Bond L m j' → ℝ) (y : Site L m j) (x : Site L m j') : ℝ :=
  (Fintype.card (AxisOrdering y x) : ℝ)⁻¹ *
    ∑ σ : AxisOrdering y x, pathCochainSum α (orderedContour y x σ)
def cochainAverageOnPositive (α : Bond L m j' → ℝ) (c : Bond L m j) : ℝ :=
  (L : ℝ) ^ (-4 : ℤ) * ∑ᶠ x ∈ sitesInBlock j' c.source,
    (contourMeanOfCochain α c.source x + pathCochainSum α (crossingPath c x) -
      contourMeanOfCochain α c.target (shiftAcross c x))
def cochainAverage (α : Bond L m j' → ℝ) : Bond L m j → ℝ :=
  open Classical in
  fun c => if c.IsPositivelyOriented then cochainAverageOnPositive α c
    else -cochainAverageOnPositive α c.opposite
section Iterates
variable {K : ℕ}
def cochainAverageIterate : (n : ℕ) → (BondAtLevel L m K 0 → ℝ) → BondAtLevel L m K n → ℝ
  | 0, α => α
  | n + 1, α => cochainAverage (cochainAverageIterate n α)
end Iterates
end YangMills.Construction.PeriodicLattice

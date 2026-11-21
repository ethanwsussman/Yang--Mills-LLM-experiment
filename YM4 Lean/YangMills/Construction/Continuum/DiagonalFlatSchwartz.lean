import YangMills.Construction.Lattice.LevelCoordinates
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction
namespace ConfigSpace
abbrev Config (n : ℕ) : Type := Fin n → Fin 4 → ℝ
abbrev MultiIndex (n : ℕ) : Type := Fin n → Fin 4 → ℕ
variable {n : ℕ}
def euclidNorm (x : Config n) : ℝ := Real.sqrt (∑ i, ∑ μ, x i μ ^ 2)
def diagonalSet (n : ℕ) : Set (Config n) :=
  ⋃ (i : Fin n) (j : Fin n) (_ : i < j), {x | x i = x j}
def minSeparation (x : Config n) : ℝ≥0∞ :=
  ⨅ (i : Fin n) (j : Fin n) (_ : i < j),
    ENNReal.ofReal (PeriodicLattice.supNormVec (x i - x j))
def MultiIndex.order (α : MultiIndex n) : ℕ := ∑ i, ∑ μ, α i μ
def coordPartial (i : Fin n) (μ : Fin 4) (g : Config n → ℂ) : Config n → ℂ :=
  fun x => lineDeriv ℝ g x (Pi.single i (Pi.single μ 1))
def iteratedPartial (α : MultiIndex n) (g : Config n → ℂ) : Config n → ℂ :=
  (List.finRange n).foldr
    (fun i h => (List.finRange 4).foldr (fun μ h' => (coordPartial i μ)^[α i μ] h') h) g
def schwartzSeminorm (k : ℕ) (φ : Config n → ℂ) : ℝ≥0∞ :=
  ⨆ (x : Config n) (α : MultiIndex n) (_ : α.order ≤ k),
    ENNReal.ofReal ((1 + euclidNorm x ^ 2) ^ ((k : ℝ) / 2) * ‖iteratedPartial α φ x‖)
def decaySeminorm (k q : ℕ) (φ : Config n → ℂ) : ℝ≥0∞ :=
  ⨆ (α : MultiIndex n) (_ : α.order ≤ q) (x : Config n),
    ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖iteratedPartial α φ x‖)
def schwartzSpace (n : ℕ) : Set (Config n → ℂ) :=
  {φ | ContDiff ℝ ∞ φ ∧ ∀ k : ℕ, schwartzSeminorm k φ < ⊤}
end ConfigSpace
end YangMills.Construction

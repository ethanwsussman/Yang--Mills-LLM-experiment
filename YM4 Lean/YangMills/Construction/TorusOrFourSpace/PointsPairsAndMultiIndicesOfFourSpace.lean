import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.TorusOrFourSpace.FunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Euclid
variable (D : Params) {n n' : ℕ+}
def flatCoords (x : Fin (n : ℕ) → Fin 4 → ℝ) : Coords n :=
  fun j => x ⟨(j : ℕ) / 4, by have := j.2; omega⟩ ⟨(j : ℕ) % 4, by omega⟩
theorem block_flatCoords (x : Fin (n : ℕ) → Fin 4 → ℝ) (i : Fin (n : ℕ)) :
    (flatCoords x).block i = x i := by
  funext μ
  have h₁ : (4 * (i : ℕ) + (μ : ℕ)) / 4 = i := by omega
  have h₂ : (4 * (i : ℕ) + (μ : ℕ)) % 4 = μ := by omega
  simp only [Coords.block, flatCoords, h₁, h₂, Fin.eta]
def appendPts (x : Kind.euclidean.Tuple D n) (y : Kind.euclidean.Tuple D n') :
    Kind.euclidean.Tuple D (n + n') :=
  Fin.append x y
def appendIdx (α : CoordIndex n) (β : CoordIndex n') :
    CoordIndex (n + n') :=
  fun j =>
    if h : (j : ℕ) < 4 * (n : ℕ) then α ⟨j, h⟩
    else
      β ⟨(j : ℕ) - 4 * (n : ℕ), by
        have hj : (j : ℕ) < 4 * ((n : ℕ) + (n' : ℕ)) := j.2
        omega⟩
def injTuplesIn (O : Set (Fin 4 → ℝ)) (n : ℕ) : Set (Fin n → Fin 4 → ℝ) :=
  (fun (y : Fin n → O) l => (y l : Fin 4 → ℝ)) '' TestFunctions.injectiveTuples O n
end YangMills.Construction.PeriodicSpace.Euclid
end

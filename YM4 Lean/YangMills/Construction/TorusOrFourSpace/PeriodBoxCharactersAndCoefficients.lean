import YangMills.Construction.TorusOrFourSpace.TestFunctionsAndDistributionsOnASet
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.PeriodicSpace
abbrev IntCoords (p : ℕ+) : Type := Fin (4 * (p : ℕ)) → ℤ
namespace IntCoords
variable {p : ℕ+}
def block (k : IntCoords p) (i : Fin (p : ℕ)) : Fin 4 → ℤ :=
  fun μ => k ⟨4 * (i : ℕ) + (μ : ℕ), by have := i.2; have := μ.2; omega⟩
def pairing (k : IntCoords p) (u : Coords p) : ℝ := ∑ j, (k j : ℝ) * u j
def maxAbs (k : IntCoords p) : ℕ := Finset.univ.sup fun j => (k j).natAbs
def cubeUpTo (t : ℕ+) : Finset (IntCoords p) :=
  Fintype.piFinset fun _ => Finset.Icc (-((t : ℕ) : ℤ)) ((t : ℕ) : ℤ)
theorem mem_cubeUpTo (t : ℕ+) (k : IntCoords p) : k ∈ cubeUpTo t ↔ maxAbs k ≤ (t : ℕ) := by
  simp only [cubeUpTo, maxAbs, Fintype.mem_piFinset, Finset.mem_Icc, Finset.sup_le_iff,
    Finset.mem_univ, true_implies]
  exact forall_congr' fun j => by omega
end IntCoords
def intVecNorm (κ : Fin 4 → ℤ) : ℝ := Real.sqrt (∑ μ, (κ μ : ℝ) ^ 2)
namespace PeriodCell
def cell (P : ℝ) : Set (Fin 4 → ℝ) := {x | ∀ μ, x μ ∈ Set.Ioo (-P / 2) (P / 2)}
def cellPow (D : Params) (p : ℕ+) (P : ℝ) : Set (Kind.euclidean.Tuple D p) :=
  {y | ∀ i, y i ∈ cell P}
def coordCube (p : ℕ+) (P : ℝ) : Set (Coords p) :=
  {u | ∀ j, u j ∈ Set.Ioo (-P / 2) (P / 2)}
abbrev cellTestFns (D : Params) (p : ℕ+) (P : ℝ) :
    Set (Kind.euclidean.Tuple D p → ℂ) :=
  Kind.Tuple.testFns D Kind.euclidean (cellPow D p P)
variable {p : ℕ+}
def fourierChar (P : ℝ) (k : IntCoords p) (u : Coords p) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k.pairing u : ℂ) / (P : ℂ))
def fourierCharR4 (P : ℝ) (κ : Fin 4 → ℤ) (x : Fin 4 → ℝ) : ℂ :=
  fourierChar (p := 1) P κ x
def fourierCoeff (D : Params) (P : ℝ) (F : Kind.euclidean.Tuple D p → ℂ)
    (k : IntCoords p) : ℂ :=
  ((P : ℂ) ^ (4 * (p : ℕ)))⁻¹ *
    ∫ u in coordCube p P,
      F (Kind.Tuple.proj D Kind.euclidean u) * conj (fourierChar P k u)
def fourierPartialSum (D : Params) (P : ℝ) (F : Kind.euclidean.Tuple D p → ℂ) (t : ℕ+) :
    Coords p → ℂ :=
  fun u => ∑ k ∈ IntCoords.cubeUpTo t, fourierCoeff D P F k * fourierChar P k u
end PeriodCell
end YangMills.Construction.PeriodicSpace

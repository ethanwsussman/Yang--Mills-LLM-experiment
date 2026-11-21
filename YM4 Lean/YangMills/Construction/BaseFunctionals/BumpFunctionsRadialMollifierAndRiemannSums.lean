import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false

section
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction.EuclideanFour
abbrev R4Point : Type := Fin 4 → ℝ
def eucNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)
def closedSupport {n : ℕ} {E : Type*} [Zero E] (g : (Fin n → ℝ) → E) : Set (Fin n → ℝ) :=
  closure {p | g p ≠ 0}
def smoothCompact (n : ℕ) : Set ((Fin n → ℝ) → ℂ) :=
  {g | ContDiff ℝ ∞ g ∧ IsCompact (closedSupport g)}
def closedBallAt (c : R4Point) (r : ℝ) : Set R4Point :=
  YangMills.Construction.TestFunctions.closedBallR4 c r
def openBallAt (c : R4Point) (r : ℝ) : Set R4Point := {q | eucNorm (q - c) < r}
end YangMills.Construction.EuclideanFour
end
end

open MeasureTheory
noncomputable section
namespace YangMills.Construction.Mollifiers
open EuclideanFour Euclidean
def expBump (t : ℝ) : ℝ :=
  if 0 < t then Real.exp (-1 / t) else 0
def bumpMassFour : ℝ := ∫ x : R4Point, expBump (1 - eucNorm x ^ 2)
def bumpMassOne : ℝ := ∫ u : ℝ, expBump (1 - u ^ 2)
def stdMollifier (x : R4Point) : ℝ := bumpMassFour⁻¹ * expBump (1 - eucNorm x ^ 2)
def stdMollifierLine (u : ℝ) : ℝ := bumpMassOne⁻¹ * expBump (1 - u ^ 2)
def rescaledMollifier (ε : ℝ) (x : R4Point) : ℝ := ε ^ (-4 : ℤ) * stdMollifier (ε⁻¹ • x)
def rescaledMollifierLine (ε u : ℝ) : ℝ := ε⁻¹ * stdMollifierLine (u / ε)
def shellCutoff (x : R4Point) : ℝ :=
  expBump (3 / 4 - eucNorm x ^ 2) /
    (expBump (3 / 4 - eucNorm x ^ 2) + expBump (eucNorm x ^ 2 - 1 / 4))
end YangMills.Construction.Mollifiers

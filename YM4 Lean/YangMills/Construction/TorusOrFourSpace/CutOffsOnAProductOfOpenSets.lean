import YangMills.Construction.TorusOrFourSpace.TestFunctionsAndDistributionsOnASet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace
def shellConst : ℝ := 16 / 3
def cutoffScale (ρ : ℝ) : ℝ := 2 * ρ / Real.pi
def cutoffBound (n : ℕ+) (ρ : ℝ) : ℝ :=
  1 + shellConst * ((n : ℕ) : ℝ) * 3 ^ (4 * (n : ℕ)) * cutoffScale ρ ^ (4 * (n : ℕ) + 1) *
    (cutoffScale ρ + 2) ^ (n : ℕ)
namespace Kind.Tuple
variable (D : Params) (E : Kind) {n : ℕ+}
def singleSet (O : Set (E.Pt D)) : Set (E.Tuple D 1) :=
  {y | y ⟨0, (1 : ℕ+).pos⟩ ∈ O}
def singleTestFns (O : Set (E.Pt D)) : Set (E.Pt D → ℂ) :=
  {φ | ofSingle D E φ ∈ testFns D E (singleSet D E O)}
def boxSet (O : Fin (n : ℕ) → Set (E.Pt D)) : Set (E.Tuple D n) :=
  {y | ∀ i, y i ∈ O i}
def IsCutoffFamily (O : Fin (n : ℕ) → Set (E.Pt D)) (χ : Fin (n : ℕ) → E.Pt D → ℝ) : Prop :=
  ∀ i, (fun y => (χ i y : ℂ)) ∈ singleTestFns D E (O i)
def cutoffTensor (χ : Fin (n : ℕ) → E.Pt D → ℝ) : E.Tuple D n → ℂ :=
  tensorProd D E fun i y => (χ i y : ℂ)
def IsCutoffOf {O : Fin (n : ℕ) → Set (E.Pt D)} (χ : Fin (n : ℕ) → E.Pt D → ℝ)
    (F : testFns D E (boxSet D E O)) : Prop :=
  IsCutoffFamily D E O χ ∧ cutoffTensor D E χ * F.1 = F.1
end Kind.Tuple
end YangMills.Construction.PeriodicSpace

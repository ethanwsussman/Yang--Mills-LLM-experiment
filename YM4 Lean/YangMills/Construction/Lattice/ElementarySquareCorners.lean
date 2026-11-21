import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ElementarySquare
variable {X : Type} [AddCommGroup X]
def vertexList (axis : Fin 4 → ℝ → X) (a : ℝ) (x : X) (μ ν : Fin 4) : List X :=
  [x, x + axis μ a, x + axis μ a + axis ν a, x + axis ν a]
def planePoint (axis : Fin 4 → ℝ → X) (a : ℝ) (x : X) (μ ν : Fin 4) (s t : ℝ) : X :=
  x + axis μ (s * a) + axis ν (t * a)
def filledSquare (axis : Fin 4 → ℝ → X) (a : ℝ) (x : X) (μ ν : Fin 4) : Set X :=
  {p | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧ p = planePoint axis a x μ ν s t}
def SquareFacts (Λ : AddSubgroup X) (axis : Fin 4 → ℝ → X) (a : ℝ) : Prop :=
  ∀ x ∈ Λ, ∀ x' ∈ Λ, ∀ μ ν μ' ν' : Fin 4, μ < ν → μ' < ν' →
    ((∀ c ∈ vertexList axis a x μ ν, c ∈ Λ) ∧ (vertexList axis a x μ ν).Nodup) ∧
    ({c | c ∈ vertexList axis a x μ ν} = {c | c ∈ vertexList axis a x' μ' ν'} →
      x = x' ∧ μ = μ' ∧ ν = ν') ∧
    (∀ s t : ℝ, planePoint axis a x μ ν s t ∈ Λ ↔ (∃ n : ℤ, s = n) ∧ ∃ n : ℤ, t = n) ∧
    ((Λ : Set X) ∩ filledSquare axis a x μ ν = {c | c ∈ vertexList axis a x μ ν}) ∧
    (filledSquare axis a x μ ν = filledSquare axis a x' μ' ν' → x = x' ∧ μ = μ' ∧ ν = ν')
def ElementarySquareStatement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n₀ j k : ℕ, 1 ≤ n₀ → j ≤ k →
    SquareFacts (PeriodicLattice.sublattice L n₀ (PeriodicLattice.levelDepth k j))
      (PeriodicLattice.pointOnAxis L n₀)
      (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j)) ∧
    SquareFacts
      (InfiniteLattice.latticeSubgroup
        (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j)))
      (fun μ t => Pi.single μ t) (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j))
end ElementarySquare
end YangMills.Construction
end

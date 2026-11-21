import YangMills.Construction.RunningCouplingSlope.DerivativeOfThePlainAverageAtOneProof
import YangMills.Construction.RunningCouplingSlope.LegsOfTheOrdersAreContours
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.AxisOrderLegs
abbrev permutedAxes (π : Equiv.Perm (Fin 4)) : List (Fin 4) := (List.finRange 4).map π
abbrev enumeratedAxes {S : Finset (Fin 4)} (e : Fin S.card ≃ S) : List (Fin 4) :=
  (List.finRange S.card).map fun i => ((e i : S) : Fin 4)
theorem exists_enumeration_eq_filter (S : Finset (Fin 4)) (π : Equiv.Perm (Fin 4)) :
    ∃ e : Fin S.card ≃ S, enumeratedAxes e = (permutedAxes π).filter (· ∈ S) := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.exists_enumList_eq_filter <;> assumption
section Paths
variable {L m : ℕ} {j : ℤ}
theorem stepsThroughAxes_filter_support (d : Fin 4 → ℤ) (S : Finset (Fin 4))
    (hS : ∀ μ, μ ∉ S → d μ = 0)
    (x : PeriodicLattice.Site L m j) (l : List (Fin 4)) :
    PeriodicLattice.stepsThroughAxes d x l =
      PeriodicLattice.stepsThroughAxes d x (l.filter (· ∈ S)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.stepsThroughAxes_filter <;> assumption
end Paths
theorem axisOrderLegsAreContours : AxisOrderLegsAreContours := by
  intro L m j j' y x π
  set S := PeriodicLattice.offsetAxes y x with hSdef
  have hS : ∀ μ, μ ∉ S → PeriodicLattice.blockOffset y x μ = 0 := by
    intro μ hμ
    by_contra h
    exact hμ (by simp [hSdef, PeriodicLattice.offsetAxes, h])
  obtain ⟨e, he⟩ := exists_enumeration_eq_filter S π
  refine ⟨e, ?_⟩
  rw [stepsThroughAxes_filter_support _ S hS, ← he]
  rfl
end YangMills.Construction.RunningCouplingSlope.AxisOrderLegs
end

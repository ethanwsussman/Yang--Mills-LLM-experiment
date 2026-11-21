import YangMills.Construction.PeriodicOperators.TemperedFunctionals
import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.TheSignsOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.Tempered
open YangMills.Construction.Tower
variable {L : ℕ}
theorem torusSide_succ (L n : ℕ) :
    PeriodicLattice.torusSide L (n + 1) = (L : ℝ) * PeriodicLattice.torusSide L n := by
  simp only [PeriodicLattice.torusSide, pow_succ]
  ring
theorem scaledExponent_succ_self (n i : ℕ) : Tower.scaledExponent n (i + 1) i = n + 1 := by
  simp [Tower.scaledExponent]
def topEdgeEquiv (L n k : ℕ) : Tower.Edge L n k k ≃ UnitEdge L n :=
  Equiv.cast (congrArg (PeriodicLattice.Bond L n) (by simp [PeriodicLattice.levelDepth]))
def stepEdgeEquiv (hL : 0 < L) (n i : ℕ) : Tower.Edge L n (i + 1) i ≃ UnitEdge L (n + 1) :=
  (Tower.scaleEdge hL (Nat.le_succ i) i).trans
    ((topEdgeEquiv L (Tower.scaledExponent n (i + 1) i) i).trans
      (Equiv.cast (congrArg (UnitEdge L) (scaledExponent_succ_self n i))))
def scaledProlong (hL : 0 < L) (n i : ℕ)
    (W : Tower.Edge L n (i + 1) (i + 1) → Matrices.ComplexMatrix2) :
    UnitEdge L (n + 1) → Matrices.ComplexMatrix2 :=
  Tower.transportTotal (stepEdgeEquiv hL n i) (Tower.chosenProlong L n (i + 1) i W)
def stepComp (hL : 0 < L) (n i : ℕ) (f : (UnitEdge L (n + 1) → Matrices.ComplexMatrix2) → ℝ)
    (W : Tower.Edge L n (i + 1) (i + 1) → Matrices.ComplexMatrix2) : ℝ :=
  f (scaledProlong hL n i W)
def stepCompDomain (hL : 0 < L) (n i : ℕ)
    (P : Set (Tower.Edge L n (i + 1) (i + 1) → Matrices.ComplexMatrix2))
    (D : Set (UnitEdge L (n + 1) → Matrices.ComplexMatrix2)) :
    Set (Tower.Edge L n (i + 1) (i + 1) → Matrices.ComplexMatrix2) :=
  {W | W ∈ Tower.fieldSpace L n (i + 1) (i + 1) ∧ W ∈ P ∧ scaledProlong hL n i W ∈ D}
def stepIndexSet (S : Set ℕ) : Set ℕ := {n | 0 < n ∧ n + 1 ∈ S}
def compStep (hL : 0 < L) (i : ℕ) (F : FieldFamily L) : FieldFamily L :=
  fun n => Tower.transportTotalScalar (topEdgeEquiv L n (i + 1)) (stepComp hL n i (F (n + 1)))
theorem compStep_transportTotal (hL : 0 < L) (i n : ℕ) (F : FieldFamily L)
    (W : Tower.Edge L n (i + 1) (i + 1) → Matrices.ComplexMatrix2) :
    compStep hL i F n (Tower.transportTotal (topEdgeEquiv L n (i + 1)) W) =
      F (n + 1) (scaledProlong hL n i W) :=
  Tower.transportTotalScalar_transportTotal _ _ W
end YangMills.Construction.PeriodicOperators.Tempered
end

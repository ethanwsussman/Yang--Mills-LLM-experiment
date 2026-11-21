import YangMills.Construction.HilbertSpaces.ComplexHilbertSpaceDefs
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Topology
open scoped ComplexConjugate ComplexOrder InnerProductSpace NNReal
noncomputable section
namespace YangMills.Construction
namespace SesquilinearForms
open OneLoopNotation ComplexHilbert
section Forms
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
open OneLoopNotation ComplexHilbert
structure IsSesqForm (q : V → V → ℂ) : Prop where
  add_left : ∀ x₁ x₂ y, q (x₁ + x₂) y = q x₁ y + q x₂ y
  smul_left : ∀ (c : ℂ) x y, q (c • x) y = conj c * q x y
  add_right : ∀ x y₁ y₂, q x (y₁ + y₂) = q x y₁ + q x y₂
  smul_right : ∀ (c : ℂ) x y, q x (c • y) = c * q x y
structure IsPosSemidefForm (q : V → V → ℂ) : Prop extends IsSesqForm q where
  nonneg : ∀ x, 0 ≤ q x x
def formSeminorm (q : V → V → ℂ) (x : V) : ℝ := Real.sqrt (q x x).re
def formNullSpace (q : V → V → ℂ) : Set V := {x | formSeminorm q x = 0}
structure IsHermitianForm (q : V → V → ℂ) : Prop extends IsSesqForm q where
  conj_symm : ∀ x y, q y x = conj (q x y)
end Forms
section Spaces
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
def closedLinSpan (D : Set H) : Set H := seqClosureOf (Submodule.span ℂ D : Set H)
def IsOrth (u v : H) : Prop := ⟪u, v⟫_ℂ = 0
def IsContractive (T : BddOpBetween H H') : Prop := opNormOf T ≤ 1
def StronglyContinuous {P : Type} [TopologicalSpace P] (T : P → BddOpBetween H H') :
    Prop :=
  ∀ u, Continuous fun t => T t u
def IsOpSemigroup (T : ℝ≥0 → BddOp H) : Prop := ∀ s t, T s * T t = T (s + t)
end Spaces
end SesquilinearForms
end YangMills.Construction

import Mathlib
set_option autoImplicit false
open Set Filter
noncomputable section
namespace YangMills.Construction
namespace OneLoopNotation
def reVec {k : ℕ} (v : Fin k → ℂ) : Fin k → ℝ := fun a => (v a).re
open Classical in
def kronecker {α : Type} (x y : α) : ℝ := if x = y then 1 else 0
section Operators
variable (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
abbrev IsHilbert : Prop := CompleteSpace H
abbrev BddOp : Type := H →L[ℂ] H
variable (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
abbrev BddOpBetween : Type := H →L[ℂ] H'
variable {H H'}
def opNormOf (T : BddOpBetween H H') : ℝ := ‖T‖
def TendstoInOpNorm {ι : Type} (l : Filter ι) (T : ι → BddOpBetween H H')
    (T₀ : BddOpBetween H H') : Prop :=
  Tendsto T l (nhds T₀)
def scalarOp (c : ℂ) : BddOp H := c • ContinuousLinearMap.id ℂ H
end Operators
def IsTwoSidedInverse {M : Type} [Monoid M] (x y : M) : Prop := x * y = 1 ∧ y * x = 1
structure MarkedPartition (a b : ℝ) where
  card : ℕ
  node : Fin (card + 1) → ℝ
  sample : Fin card → ℝ
  node_mono : Monotone node
  node_zero : node 0 = a
  node_last : node (Fin.last card) = b
  sample_mem : ∀ i, sample i ∈ Icc (node i.castSucc) (node i.succ)
namespace MarkedPartition
variable {a b : ℝ}
def sum {E : Type} [AddCommGroup E] [Module ℝ E] (P : MarkedPartition a b) (f : ℝ → E) : E :=
  ∑ i, (P.node i.succ - P.node i.castSucc) • f (P.sample i)
end MarkedPartition
end OneLoopNotation
end YangMills.Construction
end

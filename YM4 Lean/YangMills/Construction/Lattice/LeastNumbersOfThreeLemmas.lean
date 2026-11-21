import YangMills.Construction.Lattice.MapsAndBoundsOfTheCutOffCommutators
import YangMills.Construction.Lattice.MapsAndBoundsOfTheFurtherSeminorms
import YangMills.Construction.SeparatedSequences.EndsAtTheTrivialTriple
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LeastConstants
open SeparatedSequences.TrivialTripleEnds SequenceTriples
def exponentBoundSet (L : ℕ) (β₁ ε₁ : ℝ) : Set ℝ :=
  {B | 1 ≤ B ∧ IsExponentBound L β₁ ε₁ B}
def l2BoundSet (L : ℕ) : Set ℝ :=
  {B | 1 ≤ B ∧ IsL2Bound L B}
def seminormConstantSet (L : ℕ) : Set ℝ :=
  {N | max 2 (max (variationConstant L) (commutatorBoundConstant L)) ≤ N ∧
    ConstantBoundsFurtherSeminorms L N ∧ IsCutoffCommutatorConstant L N}
def exponentBoundInf (L : ℕ) (β₁ ε₁ : ℝ) : ℝ≥0∞ :=
  sInf (ENNReal.ofReal '' exponentBoundSet L β₁ ε₁)
def l2BoundInf (L : ℕ) : ℝ≥0∞ :=
  sInf (ENNReal.ofReal '' l2BoundSet L)
def seminormConstantInf (L : ℕ) : ℝ≥0∞ :=
  sInf (ENNReal.ofReal '' seminormConstantSet L)
def exponentConstantSet (L : ℕ) (β : ℝ) : Set ℝ :=
  {N | seminormConstantInf L ≤ ENNReal.ofReal N ∧
    ExponentBoundsFurtherSeminorms L β N ∧ IsCutoffCommutatorExponentConstant L β N}
def exponentConstantInf (L : ℕ) (β : ℝ) : ℝ≥0∞ :=
  sInf (ENNReal.ofReal '' exponentConstantSet L β)
end YangMills.Construction.LeastConstants
end

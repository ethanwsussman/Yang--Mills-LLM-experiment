import Mathlib
set_option autoImplicit false
open ComplexConjugate
noncomputable section
namespace YangMills.Construction.Continuum
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def IsConjLinearMap (a : V → W) : Prop :=
  ∀ (c c' : ℂ) (x x' : V), a (c • x + c' • x') = conj c • a x + conj c' • a x'
structure IsComplexSeminorm (p : V → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ p x
  smul : ∀ (c : ℂ) (x : V), p (c • x) = ‖c‖ * p x
  add_le : ∀ x x' : V, p (x + x') ≤ p x + p x'
def binaryLog (x : ℝ) : ℝ := Real.log x / Real.log 2
end YangMills.Construction.Continuum
end

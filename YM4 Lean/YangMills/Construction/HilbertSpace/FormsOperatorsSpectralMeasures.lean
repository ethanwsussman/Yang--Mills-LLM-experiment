import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.HilbertSpace
abbrev SesqForm (V : Type*) : Type _ := V → V → ℂ
namespace SesqForm
variable {V : Type*}
def IsConjSymm (b : SesqForm V) : Prop := ∀ u v, b v u = conj (b u v)
def IsNonnegDiag (b : SesqForm V) : Prop := ∀ u, (b u u).im = 0 ∧ 0 ≤ (b u u).re
def diagSqrt (b : SesqForm V) (u : V) : ℝ := Real.sqrt (b u u).re
variable [AddCommGroup V] [Module ℂ V]
structure IsSesquilinear (b : SesqForm V) : Prop where
  add_left : ∀ u₁ u₂ v, b (u₁ + u₂) v = b u₁ v + b u₂ v
  smul_left : ∀ (c : ℂ) u v, b (c • u) v = conj c * b u v
  add_right : ∀ u v₁ v₂, b u (v₁ + v₂) = b u v₁ + b u v₂
  smul_right : ∀ (c : ℂ) u v, b u (c • v) = c * b u v
end SesqForm
end YangMills.Construction.HilbertSpace

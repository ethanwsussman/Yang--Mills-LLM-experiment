import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace FormCompletion
variable {V : Type*}
def seminormOfForm (q : V → V → ℂ) (x : V) : ℝ := Real.sqrt (q x x).re
def antilinearBounds (q : V → V → ℂ) (f : V → ℂ) : Set ℝ :=
  {C | 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * seminormOfForm q x}
def dualNorm (q : V → V → ℂ) (f : V → ℂ) : ℝ := sInf (antilinearBounds q f)
def formClass (q : V → V → ℂ) (y : V) : V → ℂ := fun x => q x y
variable [AddCommGroup V] [Module ℂ V]
structure IsPosSemidefHermitianForm (q : V → V → ℂ) : Prop where
  add_left : ∀ x₁ x₂ y, q (x₁ + x₂) y = q x₁ y + q x₂ y
  smul_left : ∀ (z : ℂ) x y, q (z • x) y = conj z * q x y
  add_right : ∀ x y₁ y₂, q x (y₁ + y₂) = q x y₁ + q x y₂
  smul_right : ∀ (z : ℂ) x y, q x (z • y) = z * q x y
  hermitian : ∀ x y, q y x = conj (q x y)
  nonneg : ∀ x, 0 ≤ (q x x).re
structure IsConjLinear (f : V → ℂ) : Prop where
  map_add : ∀ x y, f (x + y) = f x + f y
  map_smul : ∀ (z : ℂ) x, f (z • x) = conj z * f x
def boundedConjLinearMaps (q : V → V → ℂ) : Set (V → ℂ) :=
  {f | IsConjLinear f ∧ (antilinearBounds q f).Nonempty}
def formCompletion (q : V → V → ℂ) : Set (V → ℂ) :=
  {f | f ∈ boundedConjLinearMaps q ∧
    ∃ s : ℕ → V, Tendsto (fun n => dualNorm q (f - formClass q (s n))) atTop (𝓝 0)}
end FormCompletion
end YangMills.Construction

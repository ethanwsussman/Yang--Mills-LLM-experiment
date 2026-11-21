import Mathlib
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate ComplexOrder
namespace YangMills.Construction
abbrev RealPlane : Type := EuclideanSpace ℝ (Fin 2)
namespace RealPlane
def unitX : RealPlane := !₂[1, 0]
def unitY : RealPlane := !₂[0, 1]
def openRightHalf : Set RealPlane := {v | 0 < v 0}
def reflectFirst (v : RealPlane) : RealPlane := !₂[-v 0, v 1]
end RealPlane
namespace PositiveDefinite
def KernelPosSemidef {Y : Type*} (k : Y → Y → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → Y) (c : Fin n → ℂ),
    0 ≤ ∑ i, ∑ j, conj (c i) * c j * k (x i) (x j)
end PositiveDefinite
end YangMills.Construction

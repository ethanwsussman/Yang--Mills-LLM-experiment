import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (P : Params) (Y : Kind)
def tensorFn {R : Type*} [CommMonoid R] {n : ℕ} (f : Fin n → Y.Pt P → R) :
    (Fin n → Y.Pt P) → R :=
  fun y => ∏ i, f i (y i)
def sepTensorSpan (n : ℕ) : Submodule ℂ ((Fin n → Y.Pt P) → ℂ) :=
  Submodule.span ℂ
    {F | ∃ f ∈ sepC1Tuples P Y n, F = tensorFn P Y fun i y => ((f i y : ℝ) : ℂ)}
end YangMills.Construction.PeriodicSpace.Kind

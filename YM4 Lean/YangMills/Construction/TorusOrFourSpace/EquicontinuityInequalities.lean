import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (P : PeriodicSpace.Params) (Y : PeriodicSpace.Kind)
def sharpNormReal (u : Y.Pt P → ℝ) : ℝ := (sharpNormQ P Y u).toReal
def telescopicDiffSum {n : ℕ} (f g : FnTuple P Y n) : ℝ :=
  ∑ l, sharpNormReal P Y (f l - g l) * (∏ k ∈ Finset.Iio l, sharpNormReal P Y (g k)) *
    ∏ k ∈ Finset.Ioi l, sharpNormReal P Y (f k)
def symmetricDiffSum {n : ℕ} (f g : FnTuple P Y n) : ℝ :=
  ∑ l, sharpNormReal P Y (f l - g l) *
    ∏ k ∈ Finset.univ.erase l, (sharpNormReal P Y (f k) + sharpNormReal P Y (g k))
def EquicontinuityBounds {n : ℕ} (c x y : ℝ) (f g : FnTuple P Y n) : Prop :=
  |x - y| ≤ c * telescopicDiffSum P Y f g ∧
    c * telescopicDiffSum P Y f g ≤ c * symmetricDiffSum P Y f g
end YangMills.Construction.PeriodicSpace.Kind

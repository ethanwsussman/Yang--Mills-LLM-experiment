import YangMills.Construction.InfiniteLattice.DictionaryBetweenSpacings
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
namespace LinkWindow
variable (W : LinkWindow a)
def IsInsensitive (ha : 0 < a) (H : GaugeField a → ℂ) : Prop :=
  ∀ (V : W.Assignments) (U : GaugeField a), H (W.glue ha V U) = H U
open Classical in
def rescaleToUnit (ha : 0 < a) : LinkWindow 1 where
  links := W.links.image (linkToUnit ha)
  isPositive b hb := by
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨μ, hμ⟩ := W.isPositive b' hb'
    refine ⟨μ, ?_⟩
    change pointToUnit ha b'.terminal - pointToUnit ha b'.initial = axisStep 1 μ
    rw [← map_sub, hμ, pointToUnit_axisStep]
end LinkWindow
end YangMills.Construction.InfiniteLattice

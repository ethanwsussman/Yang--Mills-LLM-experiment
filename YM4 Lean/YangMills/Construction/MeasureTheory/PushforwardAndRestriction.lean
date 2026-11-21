import YangMills.Construction.MeasureTheory.SigmaAdditiveSetFunctions
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SetFunctions
variable {Y Y' : Type*} [MeasurableSpace Y] [MeasurableSpace Y']
def pushforward (g : Y → Y') (hg : Measurable g) (ν : MeasurableSets Y → ℂ) : MeasurableSets Y' → ℂ :=
  fun B' => ν ⟨g ⁻¹' (B' : Set Y'), hg B'.2⟩
end YangMills.Construction.SetFunctions

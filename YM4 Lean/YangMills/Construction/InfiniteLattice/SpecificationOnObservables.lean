import YangMills.Construction.InfiniteLattice.WilsonWindows
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
namespace LinkWindow
variable (W : LinkWindow a)
def windowAction (U : GaugeField a) : ℝ := ∑ᶠ p ∈ W.faces, faceEnergy U p
def conditionalAverage (ha : 0 < a) (β : ℝ) (F : GaugeField a → ℂ) (ξ : GaugeField a) :
    ℂ :=
  (∫ V, F (W.glue ha V ξ) * (Real.exp (-β * W.windowAction (W.glue ha V ξ)) : ℂ) ∂W.haarProd) /
    ((∫ V, Real.exp (-β * W.windowAction (W.glue ha V ξ)) ∂W.haarProd : ℝ) : ℂ)
end LinkWindow
end YangMills.Construction.InfiniteLattice

import YangMills.Construction.ForwardTube.LightConeCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ForwardTube
def tubeMargin {p : ℕ} (v : Fin p → ℂ × ℂ) : ℝ :=
  min 1 (⨅ i, min (lightConePlus (v i)).re (lightConeMinus (v i)).re)
end YangMills.Construction.ForwardTube

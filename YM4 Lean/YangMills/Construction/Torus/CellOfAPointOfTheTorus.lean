import YangMills.Construction.Torus.DistanceBallsIntegralAndVolumeInPhysicalUnits
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
namespace TorusMeasure
variable {P : Conventions.StandingParameters}
def torusCell (a : ℝ) (z : P.Torus) : Set P.Torus :=
  (fun τ => z + proj P τ) '' Set.pi univ fun _ : Fin 4 => Ico (-(a / 2)) (a / 2)
end TorusMeasure
end YangMills.Construction

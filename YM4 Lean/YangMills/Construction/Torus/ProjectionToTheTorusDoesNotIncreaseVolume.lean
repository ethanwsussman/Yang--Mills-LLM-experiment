import YangMills.Construction.Torus.DistanceBallsIntegralAndVolumeInPhysicalUnits
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set TorusMeasure
open scoped ENNReal
namespace TorusProjection
def VolumeNonincreasing : Prop :=
  ∀ (P : Conventions.StandingParameters) (S : Set (Fin 4 → ℝ)), IsNullMeasurableR4 S →
    IsMeasurableTorusSet (proj P '' S) ∧
    ENNReal.ofReal (torusVolume (proj P '' S)) ≤ volumeR4 S ∧
    (InjOn (proj P) S →
      ENNReal.ofReal (torusVolume (proj P '' S)) = volumeR4 S)
end TorusProjection
end YangMills.Construction

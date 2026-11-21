import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace TorusBox
def boxOfIntervals (lower upper : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  pi univ fun μ => Icc (lower μ) (upper μ)
structure BoxChart (S : ℝ) (X : Set (Torus4 S)) where
  lower : Fin 4 → ℝ
  upper : Fin 4 → ℝ
  lower_le_upper : ∀ μ, lower μ ≤ upper μ
  injOn_proj : InjOn (torusProj S) (boxOfIntervals lower upper)
  image_proj : torusProj S '' boxOfIntervals lower upper = X
namespace BoxChart
variable {S : ℝ} {X : Set (Torus4 S)}
def box (c : BoxChart S X) : Set (Fin 4 → ℝ) := boxOfIntervals c.lower c.upper
theorem exists_lift (c : BoxChart S X) (z : X) : ∃ v ∈ c.box, torusProj S v = z := by
  have hz : (z : Torus4 S) ∈ torusProj S '' c.box := by
    rw [box, c.image_proj]
    exact z.2
  exact hz
end BoxChart
end TorusBox
end YangMills.Construction
end

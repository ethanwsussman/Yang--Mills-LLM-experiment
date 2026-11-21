import YangMills.Construction.ReflectionPositivity.TwoPicturesOfADirection
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField AmbientSpace axisStep shift)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
def cubeOfRadius (r : ℕ+) : Set AmbientSpace :=
  {x | ∀ i, x i ∈ Set.Icc (-(r : ℝ)) (r : ℝ)}
def cubeVector (ν : unitPositiveClass) (μ : Fin 4) (r : ℕ+)
    (A : GaugeField (1 : ℝ) → ℂ) : ReflectionPair.site.Hilb ν μ :=
  ReflectionPair.site.obsClass ν μ
    ((shift ((r : ℕ) • axisStep (1 : ℝ) μ)).actOn A)
end YangMills.Construction.ReflectionPositivity.DirectionPictures

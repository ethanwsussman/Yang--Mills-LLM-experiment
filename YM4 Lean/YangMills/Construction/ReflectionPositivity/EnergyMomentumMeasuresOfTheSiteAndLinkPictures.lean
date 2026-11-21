import YangMills.Construction.ReflectionPositivity.EnergyMomentumMeasuresOfAPicture
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open MirrorHyperplanes (unitPositiveClass)
open EnergyMomentum (SpectralSpace)
variable (ν : unitPositiveClass) (μ : Fin 4)
abbrev siteSpectralMeasure (ψ : ReflectionPair.site.Hilb ν μ) : Measure (SpectralSpace μ) :=
  ReflectionPair.site.spectralMeasure ν μ ψ
end YangMills.Construction.ReflectionPositivity.DirectionPictures

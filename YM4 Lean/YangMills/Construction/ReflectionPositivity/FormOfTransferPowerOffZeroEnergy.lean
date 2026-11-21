import YangMills.Construction.ReflectionPositivity.SpectralVariablesOfTheTwoPictures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
variable (ν : unitPositiveClass) (μ : Fin 4)
def sitePowerForm (n : ℕ) (_hn : 1 ≤ n) (φ φ' : ReflectionPair.site.Hilb ν μ) : ℂ :=
  inner ℂ φ ((ReflectionPair.site.transferOp ν μ ^ n *
    (1 - groundProjection μ ReflectionPair.site ν)) φ')
def linkPowerForm (n : ℕ) (_hn : 1 ≤ n) (φ φ' : ReflectionPair.link.Hilb ν μ) : ℂ :=
  inner ℂ φ ((ReflectionPair.link.transferOp ν μ ^ n *
    (1 - groundProjection μ ReflectionPair.link ν)) φ')
end YangMills.Construction.ReflectionPositivity.DirectionPictures

import YangMills.Construction.ReflectionPositivity.TwoPicturesOfADirection
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
def OneStepEnergyMomentumLink : Prop :=
  ∀ (ν : unitPositiveClass) (μ : Fin 4) (l : TransverseAxis μ),
    IsSelfAdjoint ((1 - ReflectionPair.link.transferOp ν μ) ^ 2) ∧
    IsSelfAdjoint (ReflectionPair.link.transferOp ν μ *
      ((2 : ℂ) • 1 - ReflectionPair.link.shiftOp ν μ l -
        star (ReflectionPair.link.shiftOp ν μ l))) ∧
    ReflectionPair.link.transferOp ν μ *
        ((2 : ℂ) • 1 - ReflectionPair.link.shiftOp ν μ l -
          star (ReflectionPair.link.shiftOp ν μ l)) ≤
      (1 - ReflectionPair.link.transferOp ν μ) ^ 2
end YangMills.Construction.ReflectionPositivity.DirectionPictures

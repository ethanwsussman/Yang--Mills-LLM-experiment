import YangMills.Construction.LimitsOfLatticeFamilies.IsometriesTranslationsAndEnlargedSupports
import YangMills.Construction.LimitsOfLatticeFamilies.TranslationModulusInTheSharpNorm
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
def ShiftIsIsometry : Prop :=
  ∀ (s : Conventions.StandingParameters) (M : BlockScale s) (Y : ModelSpace),
    ∀ a : Y.Carrier s,
      (∃ t : ModelSpace.SpaceIsometry s Y, (∀ y, t y = y + a) ∧
        ∀ f : Y.Carrier s → ℝ, t.pushFun f = ModelSpace.shift a f) ∧
      (∀ f ∈ c1CompactSupp s Y univ,
        ModelSpace.shift a f ∈ c1CompactSupp s Y univ ∧
        supportIn s Y (ModelSpace.shift a f) = shiftSet (supportIn s Y f) a ∧
        ModelSpace.grad s Y (ModelSpace.shift a f) = ModelSpace.shift a (ModelSpace.grad s Y f) ∧
        sharpNorm s M Y (ModelSpace.shift a f) = sharpNorm s M Y f) ∧
      (∀ n, 1 ≤ n → ∀ f ∈ sepTuples s Y n, shiftTuple a f ∈ sepTuples s Y n) ∧
      ∀ S : Set (Y.Carrier s), IsCompactIn s Y S → IsCompactIn s Y (shiftSet S a)
end YangMills.Construction.LatticeLimits
end

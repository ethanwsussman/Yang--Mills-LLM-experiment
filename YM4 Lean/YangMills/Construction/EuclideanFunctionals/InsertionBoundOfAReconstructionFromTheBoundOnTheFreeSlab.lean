import YangMills.Construction.Continuum.FreeSlabInsertionFormAndPulledDownNorm
import YangMills.Construction.EuclideanFunctionals.InsertionBoundAndPlateBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open InfiniteLattice (AmbientSpace)
namespace SlabInsertionTransfer
def AgreesWithCenteredFn (ς : SeparatedTuples.TupleFunctional) (S : ConnFamily) :
    Prop :=
  ∀ X : SeparatedTuples.SepTuple, ς.toFun X = centeredFn S
    ⟨X.1, (R4TupleForms.isDisjointlySupported_iff_mem_separatedAll defaultMirrorData X.1).1 X.2⟩
def FreeSlabBound (ς : SeparatedTuples.TupleFunctional) (M p C c : ℝ) : Prop :=
  ∀ (η : ℝ) (hη : 0 < η), η ≤ 1 → ∀ y : AmbientSpace, |TimeAxis.timeComponent y| ≤ η / 8 →
    ∀ (k : SeparatedTuples.RealValued) (hk : SeparatedTuples.IsC1c k),
      tsupport k ⊆ TestFunctions.closedBallR4 y (c * η) →
      ∀ F F' : SeparatedTuples.spanIn (SlabInsertion.timeAbove (η / 4)),
        ‖SlabInsertion.insertionForm ς F k hk F'‖ ≤
          C * η ^ (-p) * TestFunctions.sharpNormR4 M k *
            SlabInsertion.shiftDownNorm ς hη F * SlabInsertion.shiftDownNorm ς hη F'
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S)
    (ς : SeparatedTuples.TupleFunctional) (p C c : ℝ), 0 ≤ p → 0 < c → c < 1 / 8 →
    AgreesWithCenteredFn ς S → FreeSlabBound ς m.M p C c → InsertionBoundHolds σ p C c
end SlabInsertionTransfer
end YangMills.Construction.EuclideanFunctionals
end

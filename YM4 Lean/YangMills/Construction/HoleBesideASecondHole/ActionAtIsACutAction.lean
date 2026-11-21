import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import YangMills.Construction.HoleBesideASecondHole.OneTorusAtTwoFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages TorusFields FrameTransfer
namespace LumpContours
def ActionAtLevelIsCutAction : Prop :=
  ∀ (a : ℝ), 0 ≤ a → ∀ (L : ℕ) [NeZero L], Odd L → ∀ (n : ℕ) [NeZero n] (F : BlockFrame), F.blockSide = L →
    (∀ i, F.extent i = n) →
    (∀ (S : Finset (TorusSite n)) (V : TorusField n),
      cutEffectiveAction a F.top (cellsOfSites F S) (readAtLevel F F.top V) = actionAtLevel a L F.top S V) ∧
    ∀ (X : Finset (TorusSite (n * L))) (W : TorusField (n * L)),
      cutEffectiveAction a F.depth (sitesOfTorus F F.depth X) (readAtLevel F F.depth W) =
        actionAtLevel a L F.depth X W
end LumpContours
end YangMills.Construction
end

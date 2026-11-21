import YangMills.Construction.Lattice.AveragingMapIsABorelMap
import YangMills.Construction.Towers.DilationCarriesObjectsAtAStepOfASide
import YangMills.Construction.Towers.IteratesOfTheAveragesUnderTheDilation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
theorem scalingCommutesWithSmoothingIter_of
    (hStep : ScalingPreservesStepsAtSide.Statement)
    (hBorel : PeriodicLattice.BlockAverageIsBorelMap) :
    ScalingCommutesWithSmoothingIter := by
  intro L n k j hL hj hs hn hj1 l hl U hU
  have hk : 0 < k := by omega
  let p : Conventions.StandingParameters := ⟨L, hs, ⟨k, hk⟩, ⟨n, hn⟩⟩
  have hmem : ∀ i ≤ j, smoothingIter L n k i U ∈ fieldSpace L n k i := by
    intro i
    induction i with
    | zero => exact fun _ => hU
    | succ i ih =>
      intro hi
      obtain ⟨hmaps, -⟩ := hBorel p i (show i < k by omega)
      exact hmaps (ih (by omega))
  induction l with
  | zero => rfl
  | succ i ih =>
    have hi : i < j := by omega
    exact ((hStep L hL hs k j hj hj1 i hi n hn).smoothingStep_eq _ (hmem i hi.le)).trans
      (congrArg (smoothingStep L (scaledExponent n k j) j i) (ih (by omega)))
end YangMills.Construction.Tower
end

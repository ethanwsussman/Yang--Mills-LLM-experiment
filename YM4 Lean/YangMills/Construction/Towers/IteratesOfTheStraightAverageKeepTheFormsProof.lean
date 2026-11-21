import YangMills.Construction.Towers.IteratesOfTheStraightAverageKeepTheForms
import YangMills.Construction.Towers.LinearMapsBetweenTwoLevelsOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.CrossingSmoothingIter
theorem mapsTo_from_zero_of_start_eq_zero {L m k i s : ℕ} (hs : s = 0) (h : s ≤ i)
    (hmap : MapsTo (Tower.TwoLevelMaps.crossingSmoothingBetween L m k h)
      (Tower.edgeFormSpace L m k s) (Tower.edgeFormSpace L m k i)) :
    MapsTo (Tower.TwoLevelMaps.crossingSmoothingBetween L m k (Nat.zero_le i))
      (Tower.edgeFormSpace L m k 0) (Tower.edgeFormSpace L m k i) := by
  subst hs
  exact hmap
theorem mapsForms_of_twoLevelMaps (hTwo : Tower.TwoLevelMaps.Statement) :
    Tower.CrossingSmoothingIterMapsForms := by
  intro L hfac m i hm B hB
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact hB
  · obtain ⟨hside, -⟩ := hTwo L hfac (i + 1) (Nat.succ_pos i)
    obtain ⟨-, hcomp, hbase⟩ := hside m hm
    have hmaps := mapsTo_from_zero_of_start_eq_zero (Nat.sub_self i) (Nat.sub_le i i)
      (hcomp i i hi le_rfl (Nat.le_succ i)).crossingSmoothing_mapsTo_surjOn_real.1
    rw [← (hbase i (Nat.le_succ i)).crossingSmoothing_eq B hB]
    exact hmaps hB
end YangMills.Construction.Tower.CrossingSmoothingIter
end

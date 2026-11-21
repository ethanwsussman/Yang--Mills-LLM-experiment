import YangMills.Construction.Towers.DilationCarriesObjectsAtAStepOfASide
import YangMills.Construction.Towers.DilationCarriesObjectsAtAnIndexOfATower
import YangMills.Construction.Towers.DilationCarriesTheActionOfATower
import YangMills.Construction.Towers.DilationCarriesTheLatticesOfATower
import YangMills.Construction.Towers.PairsOfATowerAreThePairsOfItsSide
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
private theorem exponent_eq_of_torusSide {L m n K k : ℕ} (hL1 : 1 < L)
    (h : PeriodicLattice.torusSide L m * (L : ℝ) ^ (K - k) = PeriodicLattice.torusSide L n) :
    n = scaledExponent m K k := by
  have h1 : PeriodicLattice.torusSide L (scaledExponent m K k) = PeriodicLattice.torusSide L n := by
    rw [torusSide_scaledExponent, mul_comm, h]
  simp only [PeriodicLattice.torusSide] at h1
  have h2 : (L : ℝ) ^ (scaledExponent m K k) = (L : ℝ) ^ n := by linarith
  have h3 : L ^ (scaledExponent m K k) = L ^ n := by exact_mod_cast h2
  exact (Nat.pow_right_injective hL1 h3).symm
theorem towerPairsStatement_holds
    (hLattices : ScalingPreservesSublatticesAllSides)
    (hAction : ScalingPreservesActionAllSides)
    (hLevel : ScalingPreservesObjectsAtLevel.Statement)
    (hStep : ScalingPreservesStepsAtSide.Statement) :
    towerPairsStatement := by
  intro L hL hS k
  have hL1 : 1 < L := by have := hS.2; omega
  refine ⟨?_, ?_⟩
  · intro n m K hn hm hK hk hside
    refine ⟨exponent_eq_of_torusSide hL1 hside, ?_⟩
    have hlat := (hLattices L hL hS K k hk).1 m hm
    have hact := hAction L hL hS K k hk m hm
    refine
      { scaling_eq := ?_
        image_sublattice := fun j hj => hlat.image_sublattice j hj
        image_fieldSpace := hact.image_fieldSpace
        wilsonAction_eq := fun U hU => (hact.action_eq U hU).symm
        preserves := fun h1 =>
          { atLevel := fun i hi => ((hLevel L hL hS K k hk h1 i hi).1 m hm)
            atStep := fun i hi => hStep L hL hS K k hk h1 i hi m hm } }
    intro x
    rw [scaling_mk]
    funext μ
    have hd : PeriodicLattice.levelDepth K k = ((K - k : ℕ) : ℤ) := by
      rw [Nat.cast_sub hk]
    rw [PeriodicLattice.toLevelUnits, hd, zpow_natCast]
  · intro n hn _
    refine ⟨⟨n, hn, rfl⟩, ?_, ?_⟩
    · exact ⟨⟨k, by omega⟩, rfl⟩
    · simp
end YangMills.Construction.Tower
end

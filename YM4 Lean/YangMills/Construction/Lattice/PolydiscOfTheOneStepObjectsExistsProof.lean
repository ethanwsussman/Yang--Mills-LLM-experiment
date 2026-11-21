import YangMills.Construction.Lattice.BoundsOfTheOneStepObjectsOnAPolydisc
import YangMills.Construction.Lattice.HolomorphyOfBoundedOneStepObjects
import YangMills.Construction.Lattice.PolydiscOfTheOneStepObjectsExists
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
theorem existsOneStepPolydiscRadius_holds
    (hBounds : OneStepPolydiscRadiusExists)
    (hHolomorphic : HolomorphyOfBoundedStepQuantities) :
    ExistsOneStepPolydiscRadius := by
  intro L hL
  obtain ⟨r, hpos, hle, hb⟩ := hBounds L hL
  exact ⟨r, hpos, hle, hb, fun m K n hm hn s c hc =>
    hHolomorphic L hL r hpos m K n hm hn s c hc (hb m K n hm hn s c hc)⟩
end YangMills.Construction.PeriodicLattice

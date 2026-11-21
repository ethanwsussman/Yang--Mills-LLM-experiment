import YangMills.Construction.Lattice.BondsInsideAndOverInTermsOfBlocks
import YangMills.Construction.Lattice.LiftsClassesAndSitesInLevelUnits
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicLattice
theorem bondPositionByBlocks_holds
    (hUnits : RescaledLatticeStatement)
    (hBlocks : CoarseCentreProperties) :
    BondPositionByBlocks := by
  intro L m K hL hm hK j k hjk hkK b
  obtain ⟨-, hFibre, -, -, hBond, -⟩ := hBlocks L m K hL hm hK j k hjk hkK
  have mem_iff : ∀ (x : SiteAtLevel L m K j) (y : SiteAtLevel L m K k),
      (x : FourTorus L m) ∈ blockAtLevel j y ↔ coarseCentre j k x = y := by
    intro x y
    rw [(hFibre y).1]
    constructor
    · rintro ⟨x', hx', hy⟩
      have hxx : x' = x := Subtype.ext hx'
      rw [← hxx]
      exact hy
    · intro h
      exact ⟨x, rfl, h⟩
  refine ⟨fun y => ?_, fun c => ?_, ?_⟩
  · rw [mem_iff, mem_iff]
  · rw [mem_iff, mem_iff]
  · obtain ⟨-, -, hSites, -, -⟩ := hUnits L m K hL hm hK j j le_rfl (hjk.trans hkK)
    obtain ⟨-, -, -, -, -, -, hStep, -⟩ := hSites
    obtain ⟨σ, μ, hσ, hTarget⟩ := (hStep b.source b.target).1 ⟨b, rfl, rfl⟩
    have hTarget' : (b.target : FourTorus L m) = shiftBy L m K j b.source (σ • coordVec μ) := by
      simpa using hTarget
    rcases hBond b σ μ hσ hTarget' with hEq | ⟨-, -, c, hcSource, hcTarget, -, -⟩
    · exact Or.inl ⟨coarseCentre j k b.source, (mem_iff _ _).2 rfl, (mem_iff _ _).2 hEq⟩
    · exact Or.inr ⟨c, (mem_iff _ _).2 hcSource.symm, (mem_iff _ _).2 hcTarget.symm⟩
end YangMills.Construction.PeriodicLattice

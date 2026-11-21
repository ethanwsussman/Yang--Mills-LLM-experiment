import YangMills.Construction.Lattice.LiftOfOrderIsAConfiguration
import YangMills.Construction.Lattice.LiftsClassesAndSitesInLevelUnits
import YangMills.Construction.Lattice.TwoCasesOfTheLiftOfOrder
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
theorem orderLiftIsGaugeField_of
    (hCases : OrderLiftCases)
    (hBlocks : CoarseCentreProperties)
    (hUnits : RescaledLatticeStatement) :
    OrderLiftIsGaugeField := by
  intro L m K hL hm hK j k hjk hkK 𝒞 hrev V hV
  obtain ⟨-, -, -, hTwo⟩ := (hCases L m K hL hm hK).1 j k hjk hkK
  have hvals := hTwo 𝒞 V hrev hV
  have hInside : ∀ (y : SiteAtLevel L m K k) (b : BondAtLevel L m K j),
      IsInsideBlockAt j y b → IsInsideBlockAt j y b.opposite := fun _ _ h => ⟨h.2, h.1⟩
  have hOver : ∀ (b : BondAtLevel L m K j) (c : BondAtLevel L m K k),
      CoversBond c b → CoversBond c.opposite b.opposite := fun _ _ h => ⟨h.2, h.1⟩
  have hClosed : IsReversalClosed (bondsInsideOrOverCoarse j 𝒞) := by
    rintro b (⟨y, hy⟩ | ⟨c, hc, hbc⟩)
    · exact Or.inl ⟨y, hy.2, hy.1⟩
    · exact Or.inr ⟨c.opposite, hrev c hc, hOver b c hbc⟩
  have hInv : ∀ b ∈ bondsInsideOrOverCoarse j 𝒞,
      orderLift j V b.opposite = (orderLift j V b)⁻¹ := by
    intro b hb
    obtain ⟨-, hcase, -, h1, hc, -⟩ := hvals b hb
    obtain ⟨-, -, -, h1', hc', -⟩ := hvals b.opposite (hClosed b hb)
    rcases hcase with ⟨y, hy⟩ | ⟨c, hcC, hbc⟩
    · rw [h1 ⟨y, hy⟩, h1' ⟨y, hInside y b hy⟩, inv_one]
    · rw [hc c hcC hbc, hc' c.opposite (hrev c hcC) (hOver b c hbc), hV.2 c hcC]
  have hReal : IsGaugeField compactGaugeGroup 𝒞 V →
      IsGaugeField compactGaugeGroup (bondsInsideOrOverCoarse j 𝒞) (orderLift j V) := by
    intro hVr
    refine ⟨fun b hb => ?_, hInv⟩
    obtain ⟨-, hcase, -, h1, hc, -⟩ := hvals b hb
    rcases hcase with hin | ⟨c, hcC, hbc⟩
    · rw [h1 hin]
      exact Submonoid.one_mem _
    · rw [hc c hcC hbc]
      exact hVr.1 c hcC
  have hAll : 𝒞 = univ → bondsInsideOrOverCoarse j 𝒞 = univ := by
    intro hU
    obtain ⟨-, hblock, -, -, hbond, -⟩ := hBlocks L m K hL hm hK j k hjk hkK
    have hmem : ∀ x : SiteAtLevel L m K j,
        (x : FourTorus L m) ∈ blockAtLevel j (coarseCentre j k x) := by
      intro x
      rw [(hblock (coarseCentre j k x)).1]
      exact ⟨x, rfl, rfl⟩
    obtain ⟨-, -, ⟨-, -, -, -, -, -, hsteps, -⟩, -, -⟩ :=
      hUnits L m K hL hm hK j j le_rfl (hjk.trans hkK)
    refine eq_univ_of_forall fun b => ?_
    obtain ⟨σ, μ, hσ, hstep⟩ := (hsteps b.source b.target).1 ⟨b, rfl, rfl⟩
    rw [Nat.sub_self, pow_zero, mul_one] at hstep
    rcases hbond b σ μ hσ hstep with heq | ⟨-, -, c, hct, hch, -, -⟩
    · refine Or.inl ⟨coarseCentre j k b.source, hmem b.source, ?_⟩
      rw [← heq]
      exact hmem b.target
    · refine Or.inr ⟨c, by rw [hU]; exact mem_univ c, ?_, ?_⟩
      · rw [hct]
        exact hmem b.source
      · rw [hch]
        exact hmem b.target
  refine ⟨⟨hInside, hOver⟩, ⟨hClosed, hInv, ⟨fun b hb => (hvals b hb).2.2.2.2.2, hInv⟩, hReal⟩,
    fun hU => ⟨hAll hU, fun hVk => ?_⟩⟩
  have hlift := hReal (by rw [hU]; exact hVk)
  rw [hAll hU] at hlift
  exact hlift
end YangMills.Construction.PeriodicLattice

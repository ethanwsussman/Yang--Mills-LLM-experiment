import YangMills.Construction.BoundsOnEverySide.RecentringOfALimitFreeOfAWindow
import YangMills.Construction.SystemsWithFiveBounds.FieldOperatorAndFreeSlabAtNumbers
import YangMills.Construction.SystemsWithFiveBounds.InsertionBoundOfALimitAtNumbers
import YangMills.Construction.SystemsWithFiveBounds.MovingTuplesAtNumbers
import YangMills.Construction.SystemsWithFiveBounds.OneCellAtNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
theorem insertionBoundsOfLimit_of_components (h₁ : TranslatedTuplesWithConstants)
    (h₂ : BoundsOnEverySide.LimitRecentring.Statement) (h₃ : SingleCellBoundOfLimit)
    (h₄ : FieldOperatorAndFreeSlabFromSingleCell) :
    InsertionBoundsOfLimitWithConstants := by
  intro F N B s K β ρ ν σ hsL hlim hd hρs hνs
  have hbound : ∀ (ρ' ν' : ∀ j, MeasureTheory.Measure
      (InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (K j : ℤ))))
      (σ' : R4TupleForms.FinTuple s → ℝ),
      BoundsOnEverySide.IsPeriodicStateLimit K β ρ' ν' σ' →
      (∀ j (hj : 0 < K j), ρ' j ∈ F.stateSet s.L ⟨K j, hj⟩ (β j)) →
      (∀ j (hj : 0 < K j), ν' j ∈ F.stateSet s.L ⟨K j, hj⟩ (β j)) →
      ∃ hσ : AmbientPoints.IsTupleFunctional σ',
        InsertionBounds F.L F.M N (R4TupleForms.toTupleFunctional σ' hσ) := by
    intro ρ' ν' σ' hl hρ' hν'
    have hCl := h₁ F N B s K β ρ' ν' σ' hsL hl hd hρ' hν'
    obtain ⟨hσ, -⟩ := hCl.reflection_positive
    have hone := h₃ F N B s K β ρ' ν' σ' hσ hsL hl hd hρ' hν'
    obtain ⟨hfo, hfs⟩ := h₄ s K (freeMomentConstantsOf F N) ρ' ν' σ' hσ F.L N
      F.admissible B.admissible_constants hCl hone
    exact ⟨hσ, hone, hfo, hfs⟩
  have hS := (h₁ F N B s K β ρ ν σ hsL hlim hd hρs hνs).connected
  obtain ⟨hrec, hlimS⟩ := h₂ s K β ρ ν σ hS hlim
  have hlS : BoundsOnEverySide.IsPeriodicStateLimit K β ρ ρ
      (PeriodicGibbsLimit.centredOfLimit σ hS) :=
    { cutoff_pos := hlim.cutoff_pos
      periodicGibbs :=
        { cutoff_tendsto := hlim.periodicGibbs.cutoff_tendsto
          left_mem := hlim.periodicGibbs.left_mem
          right_mem := hlim.periodicGibbs.left_mem }
      pointwise := hlimS }
  exact ⟨hS, hrec, hlimS, hlS, hbound ρ ν σ hlim hρs hνs, hbound ρ ρ _ hlS hρs hρs⟩
end YangMills.Construction.SystemsWithFiveBounds
end

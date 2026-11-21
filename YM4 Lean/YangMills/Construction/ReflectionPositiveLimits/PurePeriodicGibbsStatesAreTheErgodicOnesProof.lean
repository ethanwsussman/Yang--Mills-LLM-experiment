import YangMills.Construction.InfiniteLattice.PureMeansErgodicUnderTheTranslations
import YangMills.Construction.ReflectionPositiveLimits.PurePeriodicGibbsStatesAreTheErgodicOnes
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.ExtremalIffErgodic
open YangMills.Construction.ReflectionPositivity.PeriodicGibbs (PeriodicGibbsReflectionPositive)
open YangMills.Construction.LatticePhases (ExtremalIffShiftErgodicStatement)
theorem zeroOne_of_extremal
    (hE : ExtremalIffShiftErgodicStatement) {L : ℕ}
    (hL : YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L) :
    ExtremalImpliesZeroOne L := by
  intro K β hβ μ hμ hext I hI
  exact (((hE ⟨L, hL, K, β, hβ⟩).1 μ hμ).1 hext).2.2 I hI
theorem extremal_of_zeroOne
    (hE : ExtremalIffShiftErgodicStatement) {L : ℕ}
    (hL : YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L)
    (hP : PeriodicGibbsReflectionPositive L) :
    ZeroOneImpliesExtremal L := by
  intro K β hβ μ hμ h01
  have hgibbs : InfiniteLattice.IsPeriodicGibbs β μ := hμ
  have hprob : IsProbabilityMeasure μ := hgibbs.1.1
  have hshift : InfiniteLattice.IsShiftInvariant μ := (hP K β hβ ⟨μ, hprob⟩ hμ).2.1
  exact ((hE ⟨L, hL, K, β, hβ⟩).1 μ hμ).2 ⟨hprob, hshift, h01⟩
theorem ergodicSeq_iff_extremal_holds {L : ℕ}
    (ha : ExtremalImpliesZeroOne L) (hb : ZeroOneImpliesExtremal L)
    (hP : PeriodicGibbsReflectionPositive L) : ergodicSeq_iff_extremal L := by
  intro K hK β hβ ρ μ hρ hμ w hw
  constructor
  · intro h j
    exact hb (K j) (β j) (hβ j) (ρ j).1 (hρ j) (h.2 j).2
  · intro h
    refine ⟨fun j => (hP (K j) (β j) (hβ j) (ρ j) (hρ j)).1, fun j => ⟨?_, ?_⟩⟩
    · exact (show InfiniteLattice.IsPeriodicGibbs (β j) (ρ j).1 from hρ j).2
    · exact ha (K j) (β j) (hβ j) (ρ j).1 (hρ j) (h j)
theorem purePhaseLimit_iff_ergodicLimit_holds {L : ℕ}
    (ha : ExtremalImpliesZeroOne L) (hb : ZeroOneImpliesExtremal L) :
    purePhaseLimit_iff_ergodicLimit L := by
  intro K hK β hβ μ hμ w hw σ
  constructor
  · rintro ⟨ρ, hext, hlim⟩
    have hgibbs : ∀ j, (ρ j).1 ∈ InfiniteLattice.periodicGibbsSet L (K j : ℕ) (β j) :=
      fun j => (show InfiniteLattice.IsExtremalPeriodicGibbs (β j) (ρ j).1 from hext j).1
    exact ⟨ρ, hgibbs, fun j => ⟨(ρ j).2, ha (K j) (β j) (hβ j) (ρ j).1 (hgibbs j) (hext j)⟩, hlim⟩
  · rintro ⟨ρ, hρ, herg, hlim⟩
    exact ⟨ρ, fun j => hb (K j) (β j) (hβ j) (ρ j).1 (hρ j) (herg j).2, hlim⟩
theorem extremalIffErgodic_holds (hE : ExtremalIffShiftErgodicStatement)
    (hG : YangMills.Construction.ReflectionPositivity.PeriodicGibbs.periodicGibbsTheorem) :
    ExtremalIffErgodicTheorem := by
  intro L hL
  have hP := (hG L hL).1
  have ha := zeroOne_of_extremal hE hL
  have hb := extremal_of_zeroOne hE hL hP
  exact ⟨ha, hb, ergodicSeq_iff_extremal_holds ha hb hP,
    purePhaseLimit_iff_ergodicLimit_holds ha hb⟩
end YangMills.Construction.ReflectionPositivity.ExtremalIffErgodic

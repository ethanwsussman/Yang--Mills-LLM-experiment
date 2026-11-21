import YangMills.Construction.TorusOrFourSpace.ClassC1FunctionsProductsAndNeighbourhoods
import YangMills.Construction.TorusOrFourSpace.NeighbourhoodsOfCompactSetsInTheDiagonalExtraction
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.DiagonalLimits
open YangMills.Construction.PeriodicSpace.Kind
theorem compactNhdProperties_holds
    (hC : C1ProductsAndThickenings.Statement) :
    CompactNhdProperties := by
  intro P X K K' hK hK' ε ε' hε hε'
  obtain ⟨-, -, ⟨⟨hzero, hnil⟩, hnhd, hsep, hsmall⟩, -⟩ := hC P X
  obtain ⟨hopen, hcpt, hsub, hopc⟩ := hnhd K hK ε hε
  refine ⟨⟨hopen, hcpt, hsub, hopc, hzero, (hnil ε hε).1, (hnil ε hε).2⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [tsub_le_iff_right, tsub_le_iff_right]
    refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
    rcases eq_zero_or_pos t with ht0 | ht0
    · rw [ht0]
      simp
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht0
    have hdist : ENNReal.ofReal (t : ℝ) ≤ setInfDist P X K K' := by
      rw [ENNReal.ofReal_coe_nnreal]
      exact ht.le
    have hgap := hsep K K' hK hK' (t : ℝ) htpos hdist ε ε' hε hε'
    calc (t : ℝ≥0∞) = ENNReal.ofReal (((t : ℝ) - ε - ε') + ε' + ε) := by
          rw [show ((t : ℝ) - ε - ε') + ε' + ε = (t : ℝ) by ring, ENNReal.ofReal_coe_nnreal]
      _ ≤ ENNReal.ofReal (((t : ℝ) - ε - ε') + ε') + ENNReal.ofReal ε := ENNReal.ofReal_add_le
      _ ≤ ENNReal.ofReal ((t : ℝ) - ε - ε') + ENNReal.ofReal ε' + ENNReal.ofReal ε := by
          gcongr
          exact ENNReal.ofReal_add_le
      _ ≤ _ := by gcongr
  · rintro (rfl | rfl)
    · have hemp : closedNhdWidth P X ∅ hK ε hε = ∅ := (hnil ε hε).2
      rw [hemp]
      simp [setInfDist]
    · have hemp : closedNhdWidth P X ∅ hK' ε' hε' = ∅ := (hnil ε' hε').2
      rw [hemp]
      simp [setInfDist]
  · intro r hr hincl
    have hball := hsmall K hK ε hε (ENNReal.ofReal r) (ENNReal.ofReal_pos.2 hr) ENNReal.ofReal_lt_top
      hincl
    rwa [ENNReal.toReal_ofReal hr.le] at hball
end YangMills.Construction.PeriodicSpace.DiagonalLimits

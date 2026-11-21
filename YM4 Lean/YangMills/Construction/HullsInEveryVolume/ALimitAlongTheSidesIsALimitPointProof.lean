import YangMills.Construction.HullsInEveryVolume.ALimitAlongTheSidesIsALimitPoint
import YangMills.Construction.HullsInEveryVolume.MeansUnderATilt
import YangMills.Construction.HullsInEveryVolume.TheTwoWilsonLawsAgree
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace YangMills.Construction.HullsInEveryVolume
open TorusLimits WeightedResponses
theorem limitAlongSidesMemTorusLimitSet (h : wilsonLawsAgreeStatement) :
    limitAlongSidesMemTorusLimitSetStatement := by
  intro L K β ν ms hodd hL hβ hlim
  haveI : NeZero L := ⟨by omega⟩
  have hmass : ∀ i, (InfiniteLattice.liftedWilsonMeasure L (ms i) K β).real Set.univ = 1 := by
    intro i
    have h1 := h L K (ms i) 0 β (fun _ => 1) hodd hL (hlim.1 i) hβ
      ⟨@measurable_const _ _ _ (borel _) _, 1, fun _ => by simp⟩
    have h2 : ∫ W, evalOnTorus (fun _ : WindowValuation 0 => (1 : ℝ)) W
        ∂(wilsonLaw β (fineSide L K (2 * L ^ ms i))) = 1 := by
      simp [evalOnTorus]
    have h3 : ∫ U, evalOnField (fun _ : WindowValuation 0 => (1 : ℝ)) U
        ∂(InfiniteLattice.liftedWilsonMeasure L (ms i) K β) =
        (InfiniteLattice.liftedWilsonMeasure L (ms i) K β).real Set.univ := by
      simp [evalOnField]
    rw [← h3, ← h1, h2]
  have hone := hlim.2.2 (fun _ => 1) continuous_const
  have hc : ∀ i, ∫ _U, (1 : ℂ) ∂(InfiniteLattice.liftedWilsonMeasure L (ms i) K β) = 1 := by
    intro i
    rw [integral_const, hmass i]
    simp
  have hν : ∫ _U, (1 : ℂ) ∂ν = 1 := tendsto_nhds_unique hone (by
    simp only [hc]
    exact tendsto_const_nhds)
  have hν1 : ν.real Set.univ = 1 := by
    rw [integral_const] at hν
    have : ((ν.real Set.univ : ℝ) : ℂ) = 1 := by simpa using hν
    exact_mod_cast this
  refine ⟨⟨?_⟩, ms, hlim.1, fun a b hab => ?_, hlim.2.2⟩
  · have := (ENNReal.toReal_eq_one_iff _).1 hν1
    exact this
  · have hLr : (1 : ℝ) < L := by exact_mod_cast hL
    have := pow_lt_pow_right₀ hLr (hlim.2.1 hab)
    show 2 * (L : ℝ) ^ ms a < 2 * (L : ℝ) ^ ms b
    linarith
end YangMills.Construction.HullsInEveryVolume
end

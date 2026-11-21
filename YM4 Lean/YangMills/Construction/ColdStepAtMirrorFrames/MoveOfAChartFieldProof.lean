import YangMills.Construction.RunningCouplingSlope.HaarDensityAtTheLeastFieldHasKernelsProof
import YangMills.Construction.ColdStepAtMirrorFrames.MoveOfAChartField
import YangMills.Construction.RunningCouplingSlope.EnergyAtTheLeastFieldHasKernelsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
namespace ChartedFieldMoveLemmas
theorem expUnit_zero' : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
variable {F : BlockFrame}
theorem movedField_zero' {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (V : F.GaugeField F.top) :
    movedField c X V 0 = V := by apply _root_.YangMills.DeltaSharedProofs.p2018 <;> assumption
theorem crossingMoveMap_apply' {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (b : F.Site F.depth × Fin 4) (τ : Fin k → ℝ) (h : IsCrossingBond b) :
    crossingMoveMap c X b τ = bondSpread c X τ (enclosingCell b.1) b.2 := by
  classical
  unfold crossingMoveMap bondSpread
  rw [if_pos h, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem crossingMoveMap_of_not_crossing' {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (b : F.Site F.depth × Fin 4)
    (h : ¬ IsCrossingBond b) : crossingMoveMap c X b = 0 := by
  classical
  unfold crossingMoveMap
  rw [if_neg h]
end ChartedFieldMoveLemmas
open ChartedFieldMoveLemmas
theorem chartedFieldUnderMove_of_expProductLogBounds (hb : ExpProductLogBounds) : ChartedFieldUnderMove := by
  classical
  obtain ⟨C, hC, hmove⟩ := hb
  refine ⟨C, hC, ?_⟩
  intro F k c X w V B hB hw hs
  have key : ∀ b : F.Site F.depth × Fin 4, ∃ Ab : (Fin k → ℝ) → imaginaryQuaternions,
      (IsAxialTreeBond b → ∀ τ, Ab τ = 0) ∧
      (¬ IsAxialTreeBond b →
        IsExpProductLog C (fun τ => w (movedField c X V τ) b.1 b.2) (crossingMoveMap c X b) Ab) := by
    intro b
    by_cases ht : IsAxialTreeBond b
    · exact ⟨fun _ => 0, fun _ _ => rfl, fun h => absurd ht h⟩
    · have h0 : ‖(fun τ => w (movedField c X V τ) b.1 b.2) 0‖ ≤ 1 := by
        simpa [movedField_zero'] using hs b ht
      obtain ⟨A, hA⟩ := hmove _ (crossingMoveMap c X b) (hw b ht) h0
      exact ⟨A, fun h => absurd h ht, fun _ => hA⟩
  choose Ab hAb using key
  refine ⟨fun τ b => Ab b.1 τ, ?_, ?_, ?_, ?_⟩
  · refine contDiffAt_pi.2 fun b => ?_
    by_cases ht : IsAxialTreeBond b.1
    · have : (fun τ => Ab b.1 τ) = fun _ => 0 := funext ((hAb b.1).1 ht)
      rw [this]
      exact contDiffAt_const
    · exact ((hAb b.1).2 ht).1
  · funext b
    by_cases ht : IsAxialTreeBond b.1
    · exact (hAb b.1).1 ht 0
    · exact ((hAb b.1).2 ht).2.1
  · have hev : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), ∀ b : ↥B, ¬ IsAxialTreeBond b.1 →
        expUnit (Ab b.1 τ) * expUnit (w (movedField c X V 0) b.1.1 b.1.2) =
          expUnit (w (movedField c X V τ) b.1.1 b.1.2) * expUnit (crossingMoveMap c X b.1 τ) := by
      refine Filter.eventually_all.2 fun b => ?_
      by_cases ht : IsAxialTreeBond b.1
      · exact Filter.Eventually.of_forall fun _ h => absurd ht h
      · exact ((hAb b.1).2 ht).2.2.1.mono fun _ h _ => h
    refine hev.mono fun τ hτ => ?_
    funext x i
    have hxi : (x, i) ∈ B := hB _
    have e := hτ ⟨(x, i), hxi⟩
    simp only [movedField_zero'] at e
    unfold chartedField leftTranslate _root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero
    rw [dif_pos hxi]
    by_cases hc : IsCrossingBond (x, i)
    · have ht : ¬ IsAxialTreeBond (x, i) := fun h => h.1 hc
      have e' := e ht
      rw [crossingMoveMap_apply' c X _ τ hc] at e'
      simp only [if_pos hc]
      rw [← mul_assoc, e', mul_assoc]
      simp [movedField, leftTranslate]
    · by_cases ht : IsAxialTreeBond (x, i)
      · simp only [if_neg hc, if_pos ht]
        rw [(hAb (x, i)).1 ht τ, expUnit_zero']
        simp
      · have e' := e ht
        rw [crossingMoveMap_of_not_crossing' c X _ hc] at e'
        simp only [if_neg hc, if_neg ht]
        simpa [expUnit_zero'] using e'.symm
  · intro b
    exact ⟨(hAb b.1).1, (hAb b.1).2⟩
end ColdStepAtMirrorFrames
end YangMills.Construction
end

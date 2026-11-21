import YangMills.Construction.FourPointCondition.LawsAtALevelOfTheWindow
import YangMills.Construction.FourPointCondition.LawsAtTheBareLevel
import YangMills.Construction.FourPointCondition.LawsWithNoDatum
import YangMills.Construction.ParameterData.TheNumberOfTheFlowIsNearOne
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
private theorem cumulantLawsOnTorus_mono {ℓ : TorusLumps.StepParameters} {vt C C' x al e β : ℝ} {K m : ℕ} {d : ℝ}
    (hCC : C ≤ C') (hx : 0 < x) (he : 0 ≤ e) (h : CumulantLawsOnTorus ℓ vt C x al e β K m d) :
    CumulantLawsOnTorus ℓ vt C' x al e β K m d := by
  intro q hq f hf
  refine (h q hq f hf).trans ?_
  have : 0 ≤ x ^ (-(1 / 100 : ℝ)) + e := add_nonneg (Real.rpow_nonneg hx.le _) he
  exact mul_le_mul_of_nonneg_right hCC this
theorem cumulantLawsAlongFlow_of_window_bare (hwin : cumulantLawsAtWindowLevel) (hbare : cumulantLawsAtBareLevel)
    (hnear : TrajectoryData.responseCoeffNearOneStatement) : cumulantLawsAlongFlow := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁pos, hwin⟩ := hwin a ha
  obtain ⟨L₂, r₂, C₂, hr₂pos, hbare⟩ := hbare a ha
  obtain ⟨L₃, r₃, C₃, hr₃pos, hnear⟩ := hnear a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (r₁ c) (min (r₂ c) (r₃ c)), max C₁ (max C₂ C₃),
    fun c => lt_min (hr₁pos c) (lt_min (hr₂pos c) (hr₃pos c)), ?_⟩
  intro L hL hLL T hTa hTL hD hC hO hr hCd
  have hL₁ : L₁ ≤ L := (le_max_left _ _).trans hLL
  have hL₂ : L₂ ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hLL
  have hL₃ : L₃ ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hLL
  have hr₁ : T.rt ≤ r₁ T.toChainParameters := hr.trans (min_le_left _ _)
  have hr₂ : T.rt ≤ r₂ T.toChainParameters := hr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr₃ : T.rt ≤ r₃ T.toChainParameters := hr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc₁ : C₁ ≤ T.derivBound := (le_max_left _ _).trans hCd
  have hc₂ : C₂ ≤ T.derivBound := ((le_max_left _ _).trans (le_max_right _ _)).trans hCd
  have hc₃ : C₃ ≤ T.derivBound := ((le_max_right _ _).trans (le_max_right _ _)).trans hCd
  obtain ⟨y₁, hwin⟩ := hwin L hL hL₁ T hTa hTL hD hC hO hr₁ hc₁
  obtain ⟨y₂, hbare⟩ := hbare L hL hL₂ T hTa hTL hD hC hO hr₂ hc₂
  obtain ⟨Kr, hKr, y₃, hnear⟩ := hnear L hL hL₃ T hTa hTL hD hC hO hr₃ hc₃
  refine ⟨max y₁ (max y₂ y₃), ?_⟩
  intro y hy hR hW
  have hy₁ : y₁ ≤ y := (le_max_left _ _).trans hy
  have hy₂ : y₂ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy₃ : y₃ ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hwin := hwin y hy₁ hR hW
  have hbare := hbare y hy₂ hR hW
  have hnear := hnear y hy₃ hR hW
  refine ⟨Kr, hKr y, ?_⟩
  intro vt hvt hvt1
  obtain ⟨Cw, Xw, hwin⟩ := hwin Kr (hKr y) vt hvt hvt1
  obtain ⟨Cb, Xb, hbare⟩ := hbare vt hvt hvt1
  refine ⟨max Cw Cb, max (max Xw Xb) (max y 1), ?_⟩
  intro β k hflow
  have hXw : ∀ j ≤ k, Xw ≤ (TorusLumps.couplingFlow (T.stepParameters y) β j).1 := fun j hj =>
    ((le_max_left _ _).trans (le_max_left _ _)).trans (hflow j hj)
  have hXb : ∀ j ≤ k, Xb ≤ (TorusLumps.couplingFlow (T.stepParameters y) β j).1 := fun j hj =>
    ((le_max_right _ _).trans (le_max_left _ _)).trans (hflow j hj)
  have hXy : ∀ j ≤ k, y ≤ ResponseInTheExpansion.flowCouplings (T.stepParameters y) β j := fun j hj =>
    ((le_max_left _ _).trans (le_max_right _ _)).trans (hflow j hj)
  have hX1 : ∀ j ≤ k, 1 ≤ (TorusLumps.couplingFlow (T.stepParameters y) β j).1 := fun j hj =>
    ((le_max_right _ _).trans (le_max_right _ _)).trans (hflow j hj)
  obtain ⟨al, hal, hclose, hquarter⟩ := hnear β k hXy
  have hab := abs_le.mp (hclose.trans hquarter)
  refine ⟨al, hal, by linarith [hab.1], by linarith [hab.2], ?_⟩
  intro K m d e hside hwindow
  have hxk : 0 < (TorusLumps.couplingFlow (T.stepParameters y) β k).1 := lt_of_lt_of_le one_pos (hX1 k le_rfl)
  rcases hwindow with ⟨hlo, hhi, rfl⟩ | ⟨rfl, hlo, hhi, rfl⟩
  · exact cumulantLawsOnTorus_mono (le_max_left _ _) hxk le_rfl
      (hwin β k al hXw hal K m d hside hlo hhi)
  · have h0 : (TorusLumps.couplingFlow (T.stepParameters y) β 0).1 = β := by simp [TorusLumps.couplingFlow]
    have hβ : Xb ≤ β := h0 ▸ hXb 0 le_rfl
    rw [h0] at hside hhi hxk ⊢
    rw [hal.zero_eq]
    exact cumulantLawsOnTorus_mono (le_max_right _ _) hxk (one_div_nonneg.mpr (zero_le_one.trans hlo))
      (hbare β hβ K m d hside hlo hhi)
end YangMills.Construction.FourPointCondition
end

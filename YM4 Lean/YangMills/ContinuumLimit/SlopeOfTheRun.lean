import Mathlib
import YangMills.ContinuumLimit.ChainAlongACurve
import YangMills.ContinuumLimit.UniformReadingAtPlaneFields
import YangMills.ContinuumLimit.ReadingAtAPlaneField
import YangMills.ContinuumLimit.RunAboveTheFloor
import YangMills.ContinuumLimit.FamiliesOfIncreasingFunctions
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
set_option autoImplicit false

noncomputable section

open Filter Topology

namespace YangMills.ContinuumLimit

open YangMills.Construction
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields
open YangMills.Construction.StepCosts YangMills.Construction.WeightedResponses
open YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.ResponseInTheExpansion.ConditionalMeans

def runFlow (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) : ℕ → ℝ → ℝ :=
  fun j β => flowCouplings (T.stepParameters y) β j

variable {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ}
  {Kr : ResponseParameters} {lam c₅ : ℝ}

theorem runFlow_zero : runFlow T y 0 = id :=
  funext fun _ => rfl

theorem runDomain_eq_aboveFloor (k : ℕ) :
    runDomain T y k = aboveFloor (y + 2 * T.B) (runFlow T y) k := rfl

namespace SlopeOfTheRun

theorem chainResponseSum_sub_trivial (ℓ : StepParameters) (γ : ℝ) (ξ a : ℕ → ℝ) (t n : ℕ) [NeZero n]
    (V : TorusField n) :
    chainResponseSum ℓ γ ξ a t n V - chainResponseSum ℓ γ ξ a t n (trivialField n) =
      ∑ z, centeredResponse (coldResponseChain ℓ γ ξ a t) n z V (constOneWeight _) := by
  unfold chainResponseSum centeredResponse
  rw [Finset.sum_sub_distrib]

theorem dist_lt_of_reading {a b S A ε : ℝ} (hA : 0 < A) (hab : a - b = -S / A)
    (hS : |S| / A ≤ 4 * (ε / 8)) (hε : 0 < ε) : dist a b < ε := by
  rw [Real.dist_eq, hab, neg_div, abs_neg, abs_div, abs_of_pos hA]
  linarith

theorem hasDerivAt_continuousOn_of_reading {I : Set ℝ} (hI : IsOpen I) {g g' : ℝ → ℝ}
    {G H Θ Ψ : ℕ → ℝ → ℝ} {A : ℕ → ℝ}
    (hG : ∀ m, ∀ γ ∈ I, HasDerivAt (G m) (-G m γ * Θ m γ) γ)
    (hH : ∀ m, ∀ γ ∈ I, HasDerivAt (H m) (-H m γ * Ψ m γ) γ)
    (hGpos : ∀ m γ, 0 < G m γ) (hHpos : ∀ m γ, 0 < H m γ)
    (hΘ : ∀ m, ContinuousOn (Θ m) I) (hΨ : ∀ m, ContinuousOn (Ψ m) I)
    (hval : ∀ γ ∈ I,
      Tendsto (fun m => -(Real.log (G m γ) - Real.log (H m γ)) / A m) atTop (𝓝 (g γ)))
    (hslope : TendstoUniformlyOn (fun m γ => (Θ m γ - Ψ m γ) / A m) g' atTop I) :
    (∀ γ ∈ I, HasDerivAt g (g' γ) γ) ∧ ContinuousOn g' I := by
  refine ⟨fun γ hγ => hasDerivAt_of_tendstoUniformlyOn
    (f := fun m γ => -(Real.log (G m γ) - Real.log (H m γ)) / A m) hI hslope
    (Eventually.of_forall fun m γ' hγ' => ?_) hval hγ,
    hslope.continuousOn (Eventually.of_forall fun m => ?_).frequently⟩
  · have h1 := (hGpos m γ').ne'
    have h2 := (hHpos m γ').ne'
    refine ((((hG m γ' hγ').log h1).sub ((hH m γ' hγ').log h2)).neg.div_const (A m)).congr_deriv ?_
    field_simp
    ring
  · exact ((hΘ m).sub (hΨ m)).div_const (A m)

theorem slope_step (hK : KernelHasCouplingDerivative) (hT : BondScoreProperties)
    (hS : StepTransitionDensityBounds) (hL : ChainIsProbabilityLaw)
    (hR : ResponseConditionalMeanStatement) (hA : PlaneFields.LeastActionAtPlaneField)
    (h : RunTable T y Kr lam c₅) (t : ℕ) (hopen : IsOpen (runDomain T y (t + 1)))
    (hder : ∀ j ≤ t, ∀ β ∈ runDomain T y j, HasDerivAt (runFlow T y j) (runSlope T y Kr β j) β ∧
      3 / 4 ≤ runSlope T y Kr β j ∧ runSlope T y Kr β j ≤ 5 / 4)
    (hcont : ∀ j ≤ t, ContinuousOn (fun β => runSlope T y Kr β j) (runDomain T y j)) :
    (∀ β ∈ runDomain T y (t + 1), HasDerivAt (runFlow T y (t + 1)) (runSlope T y Kr β (t + 1)) β) ∧
      ContinuousOn (fun β => runSlope T y Kr β (t + 1)) (runDomain T y (t + 1)) := by
  have hℓ : (T.stepParameters y).Admissible := h.adm.fits y h.floor
  have hy1 : 1 ≤ y := hℓ.y₁_ge
  have hsub : ∀ j ≤ t + 1, runDomain T y (t + 1) ⊆ runDomain T y j := fun j hj =>
    aboveFloor_subset_of_le (y + 2 * T.B) (runFlow T y) hj
  have h1 : ∀ j < t + 1, ∀ γ ∈ runDomain T y (t + 1),
      HasDerivAt (fun γ' => flowCouplings (T.stepParameters y) γ' j) (runSlope T y Kr γ j) γ :=
    fun j hj γ hγ => (hder j (Nat.lt_succ_iff.mp hj) γ (hsub j hj.le hγ)).1
  have h2 : ∀ j < t + 1, ∀ γ ∈ runDomain T y (t + 1), |runSlope T y Kr γ j| ≤ 2 := by
    intro j hj γ hγ
    obtain ⟨-, hl, hu⟩ := hder j (Nat.lt_succ_iff.mp hj) γ (hsub j hj.le hγ)
    rw [abs_le]
    constructor <;> linarith
  have h3 : ∀ j < t + 1, ContinuousOn (fun γ => runSlope T y Kr γ j) (runDomain T y (t + 1)) :=
    fun j hj => (hcont j (Nat.lt_succ_iff.mp hj)).mono (hsub j hj.le)
  have hchain := chain_along_curve hK hT hS hL hR hℓ hopen
    (fun γ => flowCouplings (T.stepParameters y) γ) (fun γ => runSlope T y Kr γ) 2 (t + 1) h1 h2 h3
  obtain ⟨N₀, hN₀, hfield⟩ := exists_plane_field hA h.adm y
  choose U hUp hUc hUa using fun m : ℕ => hfield t (m + N₀ + 1) (by omega)
  have hn₀ : ∀ m : ℕ, (T.stepParameters y).n₀ ≤ m + N₀ + 1 := fun m =>
    le_trans (le_trans (le_max_right _ _) hN₀) (by omega)
  have hApos : ∀ m : ℕ, 0 < actionAtLevel (T.stepParameters y).coupling (T.stepParameters y).side (t + 1)
      Finset.univ (U m) := fun m => lt_of_lt_of_le (pow_pos Real.pi_pos 2) (hUa m)
  have hpos : ∀ (m : ℕ) (γ : ℝ) (V : TorusField (m + N₀ + 1)),
      0 < chainFunctional (T.stepParameters y) γ (flowCouplings (T.stepParameters y) γ) (t + 1)
        (m + N₀ + 1) V := fun m γ V =>
    (hL (T.stepParameters y) hℓ hℓ.depth_lt γ (flowCouplings (T.stepParameters y) γ) (t + 1)
      (m + N₀ + 1)).2.2.2.1 V
  have hEE : (T.stepParameters y).E ≤ (T.stepParameters y).E₃ := by
    rw [h.response.E₃_eq]
    exact le_div_self hℓ.E_pos.le h.response.η₃_pos h.response.η₃_le
  have hE3 : 0 ≤ (T.stepParameters y).E₃ := hℓ.E₃_pos.le
  have hC0 : 0 ≤ Kr.Kb / (y * Kr.η₃) :=
    div_nonneg h.response.Kb_nonneg (mul_nonneg (by linarith) h.response.η₃_pos.le)
  refine hasDerivAt_continuousOn_of_reading hopen
    (g := runFlow T y (t + 1)) (g' := fun γ => runSlope T y Kr γ (t + 1))
    (G := fun m γ => chainFunctional (T.stepParameters y) γ (flowCouplings (T.stepParameters y) γ)
      (t + 1) (m + N₀ + 1) (U m))
    (H := fun m γ => chainFunctional (T.stepParameters y) γ (flowCouplings (T.stepParameters y) γ)
      (t + 1) (m + N₀ + 1) (trivialField (m + N₀ + 1)))
    (Θ := fun m γ => chainResponseSum (T.stepParameters y) γ (flowCouplings (T.stepParameters y) γ)
      (runSlope T y Kr γ) (t + 1) (m + N₀ + 1) (U m))
    (Ψ := fun m γ => chainResponseSum (T.stepParameters y) γ (flowCouplings (T.stepParameters y) γ)
      (runSlope T y Kr γ) (t + 1) (m + N₀ + 1) (trivialField (m + N₀ + 1)))
    (A := fun m => actionAtLevel (T.stepParameters y).coupling (T.stepParameters y).side (t + 1)
      Finset.univ (U m))
    (fun m γ hγ => (hchain (m + N₀ + 1)).2.1 (U m) γ hγ)
    (fun m γ hγ => (hchain (m + N₀ + 1)).2.1 (trivialField (m + N₀ + 1)) γ hγ)
    (fun m γ => hpos m γ (U m)) (fun m γ => hpos m γ (trivialField (m + N₀ + 1)))
    (fun m => (hchain (m + N₀ + 1)).2.2 (U m))
    (fun m => (hchain (m + N₀ + 1)).2.2 (trivialField (m + N₀ + 1))) ?_ ?_
  · intro γ hγ
    have habove : Above T y γ (t + 1) :=
      RunAboveTheFloor.above_mono (above_of_mem_domain h hγ) (Nat.le_succ _)
    obtain ⟨-, f, hf, -⟩ := hasExpansion_of_above h habove
    have hfam := curvature_family_of_coldExpansion hEE le_rfl hf
    have hno := noLimitFormTerm_of_coldExpansion hf
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := centered_small_at_planeField_uniform hℓ hE3 (ε := ε / 8) (by linarith)
    refine ⟨N, fun m hm => ?_⟩
    have hb := hN f hfam hno (m + N₀ + 1) (by omega) (U m) (hUp m)
    have hform := hf.form (m + N₀ + 1) (hn₀ m) (U m) (hUc m)
    rw [← chainFunctional_flow] at hform
    have hA0 := (hApos m).ne'
    have e : -(Real.log (chainFunctional (T.stepParameters y) γ (flowCouplings (T.stepParameters y) γ)
          (t + 1) (m + N₀ + 1) (U m)) -
        Real.log (chainFunctional (T.stepParameters y) γ (flowCouplings (T.stepParameters y) γ)
          (t + 1) (m + N₀ + 1) (trivialField (m + N₀ + 1)))) /
        actionAtLevel (T.stepParameters y).coupling (T.stepParameters y).side (t + 1) Finset.univ (U m) -
        flowCouplings (T.stepParameters y) γ (t + 1) =
        -(∑ z, centered f (m + N₀ + 1) z (U m)) /
          actionAtLevel (T.stepParameters y).coupling (T.stepParameters y).side (t + 1) Finset.univ (U m) := by
      rw [hform]
      field_simp
      ring
    exact dist_lt_of_reading (hApos m) e (abs_sum_centered_div_le hb (hUa m)) hε
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := centered_small_at_planeField_uniform hℓ hC0 (ε := ε / 8) (by linarith)
    refine eventually_atTop.mpr ⟨N, fun m hm γ hγ => ?_⟩
    have hrun := run_of_mem_domain h hγ
    obtain ⟨Ra, Rb, hRb⟩ := (runSlope_isChain h hrun).bounds (t + 1) le_rfl
    have hx : y ≤ flowCouplings (T.stepParameters y) γ (t + 1) := hrun (t + 1) le_rfl
    have hy0 : 0 < y := by linarith
    have hxpos : 0 < flowCouplings (T.stepParameters y) γ (t + 1) := by linarith
    have hη := h.response.η₃_pos
    have hE1 : Kr.Kb * (flowCouplings (T.stepParameters y) γ (t + 1))⁻¹ ≤
        Kr.Kb * (flowCouplings (T.stepParameters y) γ (t + 1))⁻¹ / Kr.η₃ :=
      le_div_self (mul_nonneg h.response.Kb_nonneg (inv_nonneg.mpr hxpos.le)) hη h.response.η₃_le
    have hE2 : Kr.Kb * (flowCouplings (T.stepParameters y) γ (t + 1))⁻¹ / Kr.η₃ ≤
        Kr.Kb / (y * Kr.η₃) := by
      have e : Kr.Kb / (y * Kr.η₃) = Kr.Kb * y⁻¹ / Kr.η₃ := by
        rw [← div_div, div_eq_mul_inv Kr.Kb y]
      rw [e]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (inv_anti₀ hy0 hx) h.response.Kb_nonneg) hη.le
    have hfam := curvature_family_of_cold_bounds hE1 hE2 hRb.total_family
    have hno := noLimitFormTerm_of_cold_bounds hℓ hE1 hRb.total_family
    have hb := hN Rb hfam hno (m + N₀ + 1) (by omega) (U m) (hUp m)
    have hshare := hRb.share_total (m + N₀ + 1) (hn₀ m) (U m) (hUc m)
    have hA0 := (hApos m).ne'
    have e : runSlope T y Kr γ (t + 1) -
        (chainResponseSum (T.stepParameters y) γ (flowCouplings (T.stepParameters y) γ)
          (runSlope T y Kr γ) (t + 1) (m + N₀ + 1) (U m) -
        chainResponseSum (T.stepParameters y) γ (flowCouplings (T.stepParameters y) γ)
          (runSlope T y Kr γ) (t + 1) (m + N₀ + 1) (trivialField (m + N₀ + 1))) /
        actionAtLevel (T.stepParameters y).coupling (T.stepParameters y).side (t + 1) Finset.univ (U m) =
        -(∑ z, centered Rb (m + N₀ + 1) z (U m)) /
          actionAtLevel (T.stepParameters y).coupling (T.stepParameters y).side (t + 1) Finset.univ (U m) := by
      rw [chainResponseSum_sub_trivial, hshare]
      field_simp
      ring
    exact dist_lt_of_reading (hApos m) e (abs_sum_centered_div_le hb (hUa m)) hε

end SlopeOfTheRun

theorem run_has_slope (hK : KernelHasCouplingDerivative) (hT : BondScoreProperties)
    (hS : StepTransitionDensityBounds) (hL : ChainIsProbabilityLaw)
    (hR : ResponseConditionalMeanStatement) (hA : PlaneFields.LeastActionAtPlaneField)
    (h : RunTable T y Kr lam c₅) (k : ℕ) :
    IsOpen (runDomain T y k) ∧ IsUpperSet (runDomain T y k) ∧ (runDomain T y k).Nonempty ∧
      (∀ β ∈ runDomain T y k, HasDerivAt (runFlow T y k) (runSlope T y Kr β k) β ∧
        3 / 4 ≤ runSlope T y Kr β k ∧ runSlope T y Kr β k ≤ 5 / 4) ∧
      ContinuousOn (fun β => runSlope T y Kr β k) (runDomain T y k) := by
  refine Nat.strong_induction_on k ?_
  intro k ih
  have hbd : ∀ β ∈ runDomain T y k, 3 / 4 ≤ runSlope T y Kr β k ∧ runSlope T y Kr β k ≤ 5 / 4 := by
    intro β hβ
    have hn := abs_le.mp (abs_runSlope_sub_one_le h (run_of_mem_domain h hβ))
    constructor <;> linarith [hn.1, hn.2]
  cases k with
  | zero =>
    obtain ⟨o, u, ne⟩ := aboveFloor_zero_isOpen_isUpperSet_nonempty (y + 2 * T.B) (runFlow T y)
    have hone : ∀ β ∈ runDomain T y 0, runSlope T y Kr β 0 = 1 := fun β hβ =>
      runSlope_zero h (run_of_mem_domain h hβ)
    refine ⟨o, u, ne, fun β hβ => ⟨?_, hbd β hβ⟩, ?_⟩
    · rw [hone β hβ, runFlow_zero]
      exact hasDerivAt_id β
    · exact continuousOn_const.congr fun β hβ => hone β hβ
  | succ t =>
    obtain ⟨o, u, ne, d, -⟩ := ih t (Nat.lt_succ_self t)
    have hgood : HasSlopeNearOneAboveFloor (y + 2 * T.B) (runFlow T y) t :=
      ⟨fun β => runSlope T y Kr β t, d⟩
    obtain ⟨o', u', ne'⟩ := aboveFloor_succ_isOpen_isUpperSet_nonempty o u ne hgood
    obtain ⟨hd, hc⟩ := SlopeOfTheRun.slope_step hK hT hS hL hR hA h t o'
      (fun j hj => (ih j (Nat.lt_succ_of_le hj)).2.2.2.1)
      (fun j hj => (ih j (Nat.lt_succ_of_le hj)).2.2.2.2)
    exact ⟨o', u', ne', fun β hβ => ⟨hd β hβ, hbd β hβ⟩, hc⟩

end YangMills.ContinuumLimit

end

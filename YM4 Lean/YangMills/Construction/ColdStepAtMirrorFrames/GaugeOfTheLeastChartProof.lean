import YangMills.Construction.ColdChainAtEveryLevel.CriticalForAllVariationsProof
import YangMills.Construction.ColdStepAtMirrorFrames.GaugeOfTheLeastChartForm
import YangMills.Construction.ColdStepAtMirrorFrames.SitesOfABlock
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace MinimalChart
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem coe_inv_mul_coe (g : UnitQuaternion) :
    ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_inv_mul_coe <;> assumption
theorem coe_mul_coe_inv (g : UnitQuaternion) :
    (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_mul_coe_inv <;> assumption
theorem norm_adjointMap (g : UnitQuaternion) (v : imaginaryQuaternions) :
    ‖adjointMap g v‖ = ‖v‖ := by
  change ‖(g : ℍ[ℝ]) * (v : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(v : ℍ[ℝ])‖
  rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, mul_one]
theorem expUnit_adjointMap (g : UnitQuaternion) (v : imaginaryQuaternions) :
    expUnit (adjointMap g v) = g * expUnit v * g⁻¹ := by
  apply Subtype.ext
  let +nondep : NormedAlgebra ℚ ℍ[ℝ] := .restrictScalars ℚ ℝ ℍ[ℝ]
  let u : ℍ[ℝ]ˣ := ⟨g, ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]), coe_mul_coe_inv g, coe_inv_mul_coe g⟩
  exact NormedSpace.exp_units_conj u (v : ℍ[ℝ])
theorem re_conj_unit (g : UnitQuaternion) (q : ℍ[ℝ]) :
    ((g : ℍ[ℝ]) * q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = q.re := by apply _root_.YangMills.Construction.GaugedCriticality.re_conj_unit <;> assumption
def gaugeTransformEquiv {j : ℕ} (Γ : F.Site j → UnitQuaternion) : F.GaugeField j ≃ F.GaugeField j where
  toFun := gaugeTransform Γ
  invFun := gaugeTransform fun x => (Γ x)⁻¹
  left_inv X := by
    funext x i
    simp [gaugeTransform, mul_assoc]
  right_inv X := by
    funext x i
    simp [gaugeTransform, mul_assoc]
end MinimalChart
open MinimalChart in
theorem minimalAction_gauge_invariant (hG : gaugeCovarianceStatement) :
    MinimalActionIsGaugeInvariant := by
  classical
  intro F a S j hL
  induction j with
  | zero =>
    intro _ Γ X
    change wilsonAction S (gaugeTransform Γ X) = wilsonAction S X
    unfold wilsonAction
    refine Finset.sum_congr rfl fun p _ => ?_
    have h := (hG F 0 (by simp [BlockFrame.top]) hL).2.2.1 Γ X p
    rw [h]
    simp only [Submonoid.coe_mul]
    rw [re_conj_unit]
  | succ j ih =>
    intro hj Γ X
    have hjn : j < F.top := hj
    obtain ⟨hinj, _, _, hfit⟩ := hG F j hjn hL
    let Γ' : F.Site j → UnitQuaternion := fun x => if h : ∃ y, refineSite y = x then Γ h.choose else 1
    have hΓ' : ∀ y, Γ' (refineSite y) = Γ y := by
      intro y
      have h : ∃ y', (refineSite y' : F.Site j) = refineSite y := ⟨y, rfl⟩
      simp only [Γ', dif_pos h]
      rw [hinj h.choose_spec]
    change (⨅ W : F.GaugeField j, (minimalAction a S j W +
        a * ∑ c ∈ innerBonds S (j + 1), blockFit W (gaugeTransform Γ X) c)) =
      ⨅ W : F.GaugeField j, (minimalAction a S j W + a * ∑ c ∈ innerBonds S (j + 1), blockFit W X c)
    rw [← (gaugeTransformEquiv Γ').iInf_comp]
    refine iInf_congr fun W => ?_
    change minimalAction a S j (gaugeTransform Γ' W) +
      a * ∑ c ∈ innerBonds S (j + 1), blockFit (gaugeTransform Γ' W) (gaugeTransform Γ X) c = _
    rw [ih (by omega)]
    congr 2
    exact Finset.sum_congr rfl fun c _ => hfit Γ' Γ W X c (hΓ' _) (hΓ' _)
open MinimalChart in
theorem minimizingChart_gauge_covariant (hS : SiteDecomposition) (hG : gaugeCovarianceStatement)
    (hinv : MinimalActionIsGaugeInvariant) : MinimizingChartGaugeCovariant := by
  classical
  intro F a ρ V w γ hL hs hw
  have hLpos : 0 < F.blockSide := by
    obtain ⟨k, hk⟩ := hL
    omega
  obtain ⟨hz, hr, hmin⟩ := hw
  let Γ : F.Site F.depth → UnitQuaternion := fun x => γ (enclosingCell x)
  have hrefine : ∀ y : F.Cell, enclosingCell (refineSite y : F.Site F.depth) = y := by
    intro y
    have hk : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by
      obtain ⟨k, hk⟩ := hL
      have hLz : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
      unfold centredCube
      rw [Fintype.mem_piFinset]
      intro i
      simp only [Pi.zero_apply, Finset.mem_Icc]
      rw [hLz]
      omega
    have h1 := ((hS F hL hs).1 y 0 hk).1
    have e1 : (siteOfCoords F.depth (0 : Fin 4 → ℤ) : F.Site F.depth) = 0 := by
      funext i
      simp [siteOfCoords]
    rw [e1, add_zero] at h1
    have e2 : (cellCentre F.depth y : F.Site F.depth) = refineSite y := by
      funext i
      simp [cellCentre, refineSite, siteOfCoords, BlockFrame.top]
    rw [e2] at h1
    exact h1
  have hchart : ∀ x i, chartedField (fun x i => adjointMap (γ (enclosingCell x)) (w x i))
      (gaugeTransform γ V) x i = gaugeTransform Γ (chartedField w V) x i := by
    intro x i
    simp only [chartedField, gaugeTransform, Γ]
    by_cases hc : IsCrossingBond (x, i)
    · have hnext : enclosingCell (x + unitStep F.depth i) = enclosingCell x + unitStep F.top i := by
        rcases (hS F hL hs).2.2.2 x i with h | h
        · exact absurd h hc
        · exact h
      simp only [if_pos hc, hnext, expUnit_adjointMap]
      group
    · have hsame : enclosingCell (x + unitStep F.depth i) = enclosingCell x := by
        by_contra hne
        exact hc hne
      simp only [if_neg hc, hsame]
      by_cases ht : IsAxialTreeBond (x, i)
      · simp [if_pos ht]
      · simp only [if_neg ht, expUnit_adjointMap]
  have hfield : chartedField (fun x i => adjointMap (γ (enclosingCell x)) (w x i)) (gaugeTransform γ V) =
      gaugeTransform Γ (chartedField w V) := by
    funext x i
    exact hchart x i
  have henergy : ∀ W : F.GaugeField F.depth,
      blockEnergy a (finiteCells F) F.depth (gaugeTransform Γ W) (gaugeTransform γ V) =
      blockEnergy a (finiteCells F) F.depth W V := by
    intro W
    unfold blockEnergy
    rw [hinv F a _ F.depth hLpos (by simp [BlockFrame.top])]
    congr 2
    refine Finset.sum_congr rfl fun c _ => ?_
    exact (hG F F.depth (by simp [BlockFrame.top]) hLpos).2.2.2 Γ γ W V c
      (by simp only [Γ, hrefine]) (by simp only [Γ, hrefine])
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun W' => ?_⟩
  · simp only [hz b hb, map_zero]
  · simp only [norm_adjointMap]
    exact hr b hb
  · rw [hfield, henergy]
    have e := henergy ((gaugeTransformEquiv Γ).symm W')
    have e2 : gaugeTransform Γ ((gaugeTransformEquiv Γ).symm W') = W' :=
      (gaugeTransformEquiv Γ).apply_symm_apply W'
    rw [e2] at e
    rw [e]
    exact hmin _
theorem minimalActionGaugeCovariance_holds (hS : SiteDecomposition) (hG : gaugeCovarianceStatement) :
    MinimalActionGaugeCovariance :=
  ⟨minimalAction_gauge_invariant hG, minimizingChart_gauge_covariant hS hG (minimalAction_gauge_invariant hG)⟩
end YangMills.Construction.ColdStepAtMirrorFrames
end

import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheTerms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.VariationRates
variable {F : BlockFrame}
theorem re_adjointAction_imaginary (g : UnitQuaternion) (w : imaginaryQuaternions) :
    (adjointAction g (w : ℍ[ℝ])).re = 0 := by
  rw [re_adjointAction]
  exact w.2
def adjointImaginary (g : UnitQuaternion) (w : imaginaryQuaternions) : imaginaryQuaternions :=
  ⟨adjointAction g (w : ℍ[ℝ]), re_adjointAction_imaginary g w⟩
theorem coe_adjointImaginary (g : UnitQuaternion) (w : imaginaryQuaternions) :
    ((adjointImaginary g w : imaginaryQuaternions) : ℍ[ℝ]) = adjointAction g (w : ℍ[ℝ]) := rfl
theorem norm_adjointImaginary (g : UnitQuaternion) (w : imaginaryQuaternions) :
    ‖adjointImaginary g w‖ = ‖w‖ := norm_adjointAction g (w : ℍ[ℝ])
abbrev InfinitesimalGauge (F : BlockFrame) : Type := (j : ℕ) → F.Site j → imaginaryQuaternions
def gaugeVariation (W : F.FieldChain) (k : F.SiteGauge) (ξ : InfinitesimalGauge F) : GaugedVariation F :=
  ⟨fun j x i => ξ j x - adjointImaginary (W j x i) (ξ j (x + unitStep j i)),
    fun j y => ξ (j + 1) y - adjointImaginary (k (j + 1) y) (ξ j (refineSite y))⟩
def gaugeOrbit (W : F.FieldChain) (ξ : InfinitesimalGauge F) (τ : ℝ) : F.FieldChain :=
  fun j => gaugeTransform (fun x => expUnit (τ • ξ j x)) (W j)
def gaugeOrbitSiteGauge (k : F.SiteGauge) (ξ : InfinitesimalGauge F) (τ : ℝ) : F.SiteGauge
  | 0 => k 0
  | j + 1 => fun y => expUnit (τ • ξ (j + 1) y) * k (j + 1) y * (expUnit (τ • ξ j (refineSite y)))⁻¹
theorem gaugeOrbit_zero (W : F.FieldChain) (ξ : InfinitesimalGauge F) : gaugeOrbit W ξ 0 = W := by
  funext j x i
  simp [gaugeOrbit, gaugeTransform, expUnit_zero]
theorem gaugeOrbitSiteGauge_zero (k : F.SiteGauge) (ξ : InfinitesimalGauge F) :
    gaugeOrbitSiteGauge k ξ 0 = k := by
  funext j y
  cases j with
  | zero => rfl
  | succ j => simp [gaugeOrbitSiteGauge, expUnit_zero]
theorem hasDerivAt_conj_expUnit (u v : imaginaryQuaternions) (g : UnitQuaternion) :
    HasDerivAt (fun τ : ℝ => ((expUnit (τ • u) * g * (expUnit (τ • v))⁻¹ : UnitQuaternion) : ℍ[ℝ]))
      (((u - adjointImaginary g v : imaginaryQuaternions) : ℍ[ℝ]) * (g : ℍ[ℝ])) 0 := by
  have h1 := (hasDerivAt_expUnit_smul u).mul_const (g : ℍ[ℝ])
  have h2 := hasDerivAt_coe_inv (g := fun τ : ℝ => expUnit (τ • v)) (w := v) (by
    simpa [expUnit_zero] using hasDerivAt_expUnit_smul v)
  have h3 := h1.fun_mul h2
  simp only [Submonoid.coe_mul]
  refine h3.congr_deriv ?_
  simp only [zero_smul, expUnit_zero, inv_one, OneMemClass.coe_one, one_mul, mul_one, mul_neg]
  simp only [Submodule.coe_sub, coe_adjointImaginary, sub_mul]
  unfold adjointAction
  rw [mul_assoc _ _ (g : ℍ[ℝ]), coe_inv_mul_coe, mul_one]
  abel
theorem gaugedBlockFit_gaugeTransform (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide) {j : ℕ}
    (hj : j < F.top) (γ : F.Site j → UnitQuaternion) (γ' : F.Site (j + 1) → UnitQuaternion)
    (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion) (X' : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) :
    gaugedBlockFit (gaugeTransform γ X) (fun y => γ' y * k y * (γ (refineSite y))⁻¹)
      (gaugeTransform γ' X') c = gaugedBlockFit X k X' c := by
  obtain ⟨-, h2, -, -⟩ := hG F j hj hL
  set y' := c.1 + unitStep (j + 1) c.2 with hy'
  have e1 : gaugedContourAverage (gaugeTransform γ X) (fun y => γ' y * k y * (γ (refineSite y))⁻¹) c =
      (γ' c.1 : ℍ[ℝ]) * gaugedContourAverage X k c * (((γ' y')⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    unfold gaugedContourAverage
    rw [h2, ← hy']
    simp only [mul_inv_rev, inv_inv, Submonoid.coe_mul]
    have a1 := coe_inv_mul_coe (γ (refineSite c.1))
    have a2 := coe_inv_mul_coe (γ (refineSite y'))
    calc _ = (γ' c.1 : ℍ[ℝ]) * (k c.1 : ℍ[ℝ]) *
            ((((γ (refineSite c.1))⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (γ (refineSite c.1) : ℍ[ℝ])) *
            contourAverage X c *
            ((((γ (refineSite y'))⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (γ (refineSite y') : ℍ[ℝ])) *
            (((k y')⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (((γ' y')⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
          simp only [mul_assoc]
      _ = _ := by
          rw [a1, a2]
          simp only [mul_one, mul_assoc]
  unfold gaugedBlockFit
  rw [e1, norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, mul_one]
  congr 1
  have e2 : ((((gaugeTransform γ' X' c.1 c.2)⁻¹ : UnitQuaternion)) : ℍ[ℝ]) =
      (γ' y' : ℍ[ℝ]) * (((X' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
        (((γ' c.1)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    unfold gaugeTransform
    simp only [mul_inv_rev, inv_inv, Submonoid.coe_mul, mul_assoc, hy']
  rw [e2]
  have a3 := coe_inv_mul_coe (γ' y')
  have e3 : (γ' c.1 : ℍ[ℝ]) * gaugedContourAverage X k c * (((γ' y')⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
      ((γ' y' : ℍ[ℝ]) * (((X' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
        (((γ' c.1)⁻¹ : UnitQuaternion) : ℍ[ℝ])) =
      adjointAction (γ' c.1) (gaugedContourAverage X k c * (((X' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by
    unfold adjointAction
    calc _ = (γ' c.1 : ℍ[ℝ]) * gaugedContourAverage X k c *
            ((((γ' y')⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (γ' y' : ℍ[ℝ])) *
            (((X' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (((γ' c.1)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
          simp only [mul_assoc]
      _ = _ := by rw [a3]; simp only [mul_one, mul_assoc]
  rw [e3, re_adjointAction]
theorem actionTermValue_gaugeOrbit (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide) {a : ℝ}
    (W : F.FieldChain) (k : F.SiteGauge) (ξ : InfinitesimalGauge F) (τ : ℝ) {S : Finset F.Cell}
    {t : F.ActionTerm} (ht : t ∈ actionTerms S) :
    actionTermValue a (gaugeOrbit W ξ τ) (gaugeOrbitSiteGauge k ξ τ) t = actionTermValue a W k t := by
  rcases t with p | ⟨j, c⟩
  · obtain ⟨-, -, h3, -⟩ := hG F 0 (by simp) hL
    simp only [actionTermValue, gaugeOrbit]
    rw [h3]
    have : (((expUnit (τ • ξ 0 p.1) * plaquetteHolonomy (W 0) p * (expUnit (τ • ξ 0 p.1))⁻¹ :
        UnitQuaternion)) : ℍ[ℝ]) =
        adjointAction (expUnit (τ • ξ 0 p.1)) ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]) := by
      simp only [Submonoid.coe_mul, adjointAction]
    rw [this, re_adjointAction]
  · have hj : j < F.top := Finset.mem_range.1 (Finset.mem_sigma.1 (Finset.inr_mem_disjSum.1 ht)).1
    simp only [actionTermValue, gaugeOrbit]
    exact congrArg (a * ·) (gaugedBlockFit_gaugeTransform hG hL hj _ _ _ _ _ _)
theorem actionTermRate_gaugeVariation (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide) {a : ℝ}
    (W : F.FieldChain) (k : F.SiteGauge) (ξ : InfinitesimalGauge F) (htop : ∀ y, ξ F.top y = 0)
    {S : Finset F.Cell} {t : F.ActionTerm} (ht : t ∈ actionTerms S) (hq : AveragesNeZero W k t) :
    actionTermRate a W k (gaugeVariation W k ξ) t = 0 := by
  have h1 := hasDerivAt_actionTermValue (a := a) (Wc := gaugeOrbit W ξ) (kc := gaugeOrbitSiteGauge k ξ)
    (Y := gaugeVariation W k ξ) (gaugeOrbit_zero W ξ) (gaugeOrbitSiteGauge_zero k ξ)
    (fun j _ x i => hasDerivAt_conj_expUnit _ _ _) (fun x i => ?_)
    (fun j y => hasDerivAt_conj_expUnit _ _ _) ht hq
  · have e : (fun τ => actionTermValue a (gaugeOrbit W ξ τ) (gaugeOrbitSiteGauge k ξ τ) t) =
        fun _ => actionTermValue a W k t := by
      funext τ
      exact actionTermValue_gaugeOrbit hG hL W k ξ τ ht
    rw [e] at h1
    exact h1.unique (hasDerivAt_const _ _)
  · have e : (fun τ => ((gaugeOrbit W ξ τ F.top x i : UnitQuaternion) : ℍ[ℝ])) =
        fun _ => (W F.top x i : ℍ[ℝ]) := by
      funext τ
      simp [gaugeOrbit, gaugeTransform, htop, expUnit_zero]
    rw [e]
    exact hasDerivAt_const _ _
end YangMills.Construction.BlockAverages.VariationRates
end

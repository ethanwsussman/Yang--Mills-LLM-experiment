import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.ColdChainAtEveryLevel.FirstOrdersUnderGaugeFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.VariationRates
variable {F : BlockFrame}
def slotValues (Y : GaugedVariation F) : VariationSlot F → imaginaryQuaternions
  | Sum.inl b => Y.bondVariation b.1 b.2.1 b.2.2
  | Sum.inr c => Y.linkVariation c.1 c.2
theorem variationOfSlots_slotValues (Y : GaugedVariation F) : variationOfSlots (slotValues Y) = Y := by
  cases Y
  rfl
def distFromOne (g : UnitQuaternion) : ℝ := ‖(g : ℍ[ℝ]) - 1‖
def imaginaryOfUnit (g : UnitQuaternion) : imaginaryQuaternions := imaginaryPart (g : ℍ[ℝ])
theorem coe_imaginaryOfUnit (g : UnitQuaternion) :
    ((imaginaryOfUnit g : imaginaryQuaternions) : ℍ[ℝ]) = pureComponent (g : ℍ[ℝ]) := rfl
theorem norm_imaginaryQuaternion (w : imaginaryQuaternions) : ‖w‖ = ‖(w : ℍ[ℝ])‖ := rfl
theorem pureComponent_sub_one (q : ℍ[ℝ]) : pureComponent (q - 1) = pureComponent q := by
  rw [pureComponent_sub, pureComponent_one, sub_zero]
theorem norm_imaginaryOfUnit_le (g : UnitQuaternion) : ‖imaginaryOfUnit g‖ ≤ _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne g := by
  rw [norm_imaginaryQuaternion, coe_imaginaryOfUnit, ← pureComponent_sub_one]
  exact norm_pureComponent_le _
theorem distFromOne_nonneg (g : UnitQuaternion) : 0 ≤ _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne g := norm_nonneg _
theorem distFromOne_le_two (g : UnitQuaternion) : _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne g ≤ 2 := by
  unfold distFromOne
  refine (norm_sub_le _ _).trans ?_
  rw [_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, norm_one]
  norm_num
theorem distFromOne_mul_le (a b : UnitQuaternion) : _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (a * b) ≤ _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne a + _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne b := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
theorem distFromOne_inv (a : UnitQuaternion) : _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne a⁻¹ = _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne a := norm_coe_inv_sub_one a
theorem distFromOne_conj (a b : UnitQuaternion) : _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (a * b * a⁻¹) = _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne b := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
theorem pureComponent_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) :
    pureComponent (adjointAction g w) = adjointAction g (pureComponent w) := by apply _root_.YangMills.Construction.BlockLines.pureComponent_adjointAction <;> assumption
theorem imaginaryOfUnit_conj (a b : UnitQuaternion) :
    imaginaryOfUnit (a * b * a⁻¹) = adjointImaginary a (imaginaryOfUnit b) := by
  apply Subtype.ext
  rw [coe_adjointImaginary, coe_imaginaryOfUnit, coe_imaginaryOfUnit, ← pureComponent_adjointAction]
  rfl
theorem distFromOne_mul_inv_le (A B e : UnitQuaternion) :
    _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (A * B⁻¹) ≤ _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (A * e * B⁻¹) + _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne e := by
  have h : A * B⁻¹ = (A * e * B⁻¹) * (B * e⁻¹ * B⁻¹) := by group
  rw [h]
  refine (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_mul_le _ _).trans ?_
  rw [_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_conj, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_inv]
theorem norm_imaginaryOfUnit_sub_sub_le (A B : UnitQuaternion) :
    ‖(imaginaryOfUnit A - imaginaryOfUnit B : imaginaryQuaternions) - imaginaryOfUnit (A * B⁻¹)‖ ≤
      _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (A * B⁻¹) * _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne B := by
  set a : ℍ[ℝ] := (A : ℍ[ℝ])
  set b : ℍ[ℝ] := (B : ℍ[ℝ])
  set bi : ℍ[ℝ] := ((B⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hbi
  have hab : ((A * B⁻¹ : UnitQuaternion) : ℍ[ℝ]) = a * bi := rfl
  have hba : bi * b = 1 := coe_inv_mul_coe B
  set f : ℍ[ℝ] := a * bi - 1 with hf
  have e1 : a = b + f * b := by
    rw [hf, sub_mul, one_mul, mul_assoc, hba, mul_one]
    abel
  have e2 : pureComponent a - pureComponent b - pureComponent (a * bi) = pureComponent (f * (b - 1)) := by
    conv_lhs => rw [e1]
    rw [pureComponent_add]
    have e3 : pureComponent (a * bi) = pureComponent f := by rw [hf, pureComponent_sub_one]
    have e4 : f * b = f + f * (b - 1) := by rw [mul_sub, mul_one]; abel
    rw [← e1, e3, e4, pureComponent_add]
    abel
  rw [norm_imaginaryQuaternion]
  have e5 : (((imaginaryOfUnit A - imaginaryOfUnit B : imaginaryQuaternions) - imaginaryOfUnit (A * B⁻¹) :
      imaginaryQuaternions) : ℍ[ℝ]) = pureComponent (f * (b - 1)) := by
    rw [← e2]
    rfl
  rw [e5]
  refine (norm_pureComponent_le _).trans ?_
  rw [norm_mul]
  unfold distFromOne
  rw [hab]
theorem norm_imaginaryOfUnit_sub_le (A B e : UnitQuaternion) :
    ‖(imaginaryOfUnit A - imaginaryOfUnit B : imaginaryQuaternions)‖ ≤
      3 * (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (A * e * B⁻¹) + _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne e) := by
  have h1 := norm_imaginaryOfUnit_sub_sub_le A B
  have h2 := _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_mul_inv_le A B e
  have h3 := norm_imaginaryOfUnit_le (A * B⁻¹)
  have h4 := _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_le_two B
  have h5 := _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg (A * B⁻¹)
  have h6 : ‖(imaginaryOfUnit A - imaginaryOfUnit B : imaginaryQuaternions)‖ ≤
      ‖(imaginaryOfUnit A - imaginaryOfUnit B : imaginaryQuaternions) - imaginaryOfUnit (A * B⁻¹)‖ +
        ‖imaginaryOfUnit (A * B⁻¹)‖ := by
    have := norm_add_le ((imaginaryOfUnit A - imaginaryOfUnit B : imaginaryQuaternions) -
      imaginaryOfUnit (A * B⁻¹)) (imaginaryOfUnit (A * B⁻¹))
    rwa [sub_add_cancel] at this
  nlinarith
theorem norm_imaginaryOfUnit_second_le (A B e : UnitQuaternion) :
    ‖(imaginaryOfUnit (A * e * B⁻¹) - imaginaryOfUnit e - (imaginaryOfUnit A - imaginaryOfUnit B) :
      imaginaryQuaternions)‖ ≤
      2 * (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne A + _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne B) * (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (A * e * B⁻¹) + _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne e) := by
  set a : ℍ[ℝ] := (A : ℍ[ℝ])
  set bi : ℍ[ℝ] := ((B⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hbi
  set ee : ℍ[ℝ] := (e : ℍ[ℝ])
  have hN : ‖a * (ee - 1) * bi - (ee - 1)‖ ≤ (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne A + _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne B) * _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne e := by
    have e1 : a * (ee - 1) * bi - (ee - 1) = (a - 1) * (ee - 1) * bi + (ee - 1) * (bi - 1) := by
      noncomm_ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, hbi, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, mul_one, norm_coe_inv_sub_one]
    have : ‖a - 1‖ = _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne A := rfl
    have h2 : ‖ee - 1‖ = _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne e := rfl
    have h3 : ‖((B : ℍ[ℝ])) - 1‖ = _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne B := rfl
    rw [this, h2, h3]
    ring_nf
    rfl
  have e2 : (((imaginaryOfUnit (A * e * B⁻¹) - imaginaryOfUnit e - imaginaryOfUnit (A * B⁻¹) :
      imaginaryQuaternions)) : ℍ[ℝ]) = pureComponent (a * (ee - 1) * bi - (ee - 1)) := by
    have h1 : ((A * e * B⁻¹ : UnitQuaternion) : ℍ[ℝ]) = a * (ee - 1) * bi + a * bi := by
      show a * ee * bi = _
      noncomm_ring
    have h2 : ((A * B⁻¹ : UnitQuaternion) : ℍ[ℝ]) = a * bi := rfl
    show pureComponent _ - pureComponent _ - pureComponent _ = _
    rw [h1, h2, pureComponent_add, pureComponent_sub, pureComponent_sub_one]
    abel
  have h3 : ‖(imaginaryOfUnit (A * e * B⁻¹) - imaginaryOfUnit e - imaginaryOfUnit (A * B⁻¹) :
      imaginaryQuaternions)‖ ≤ (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne A + _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne B) * _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne e := by
    rw [norm_imaginaryQuaternion, e2]
    exact (norm_pureComponent_le _).trans hN
  have h4 := norm_imaginaryOfUnit_sub_sub_le A B
  have h5 := _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_mul_inv_le A B e
  have e3 : (imaginaryOfUnit (A * e * B⁻¹) - imaginaryOfUnit e - (imaginaryOfUnit A - imaginaryOfUnit B) :
      imaginaryQuaternions) =
      (imaginaryOfUnit (A * e * B⁻¹) - imaginaryOfUnit e - imaginaryOfUnit (A * B⁻¹)) -
        ((imaginaryOfUnit A - imaginaryOfUnit B) - imaginaryOfUnit (A * B⁻¹)) := by abel
  rw [e3]
  refine (norm_sub_le _ _).trans ?_
  have p1 := _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg A
  have p2 := _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg B
  have p3 := _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg e
  have p4 := _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg (A * e * B⁻¹)
  have h6 : _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (A * B⁻¹) * _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne B ≤ (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (A * e * B⁻¹) + _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne e) * _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne B :=
    mul_le_mul_of_nonneg_right h5 p2
  nlinarith [mul_nonneg p1 p3, mul_nonneg p2 p3, mul_nonneg p1 p4, mul_nonneg p2 p4]
theorem norm_imaginaryOfUnit_mul_sub_le (A B : UnitQuaternion) :
    ‖(imaginaryOfUnit (A * B) - imaginaryOfUnit A - imaginaryOfUnit B : imaginaryQuaternions)‖ ≤
      _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne A * _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne B := by
  set a : ℍ[ℝ] := (A : ℍ[ℝ])
  set b : ℍ[ℝ] := (B : ℍ[ℝ])
  have e : (((imaginaryOfUnit (A * B) - imaginaryOfUnit A - imaginaryOfUnit B : imaginaryQuaternions)) : ℍ[ℝ]) =
      pureComponent ((a - 1) * (b - 1)) := by
    have h1 : ((A * B : UnitQuaternion) : ℍ[ℝ]) = (a - 1) * (b - 1) + a + b - 1 := by
      show a * b = _
      noncomm_ring
    show pureComponent _ - pureComponent _ - pureComponent _ = _
    rw [h1, pureComponent_sub, pureComponent_add, pureComponent_add, pureComponent_one]
    abel
  rw [norm_imaginaryQuaternion, e]
  refine (norm_pureComponent_le _).trans ?_
  rw [norm_mul]
  rfl
section
variable (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k : F.SiteGauge)
def slotDefect (Γ : F.SiteGauge) : VariationSlot F → UnitQuaternion
  | Sum.inl b => relativeDefect W X Γ b.1 b.2.1 b.2.2
  | Sum.inr c => gaugedLink k Γ c.1 c.2 * (kW (c.1 + 1) c.2)⁻¹
def slotSourceChange (Γ Γ' : F.SiteGauge) : VariationSlot F → UnitQuaternion
  | Sum.inl b => gaugeChange Γ Γ' b.1 b.2.1
  | Sum.inr c => gaugeChange Γ Γ' (c.1 + 1) c.2
def slotTargetChange (Γ Γ' : F.SiteGauge) : VariationSlot F → UnitQuaternion
  | Sum.inl b => W b.1 b.2.1 b.2.2 * gaugeChange Γ Γ' b.1 (b.2.1 + unitStep b.1 b.2.2) * (W b.1 b.2.1 b.2.2)⁻¹
  | Sum.inr c => kW (c.1 + 1) c.2 * gaugeChange Γ Γ' c.1 (refineSite c.2) * (kW (c.1 + 1) c.2)⁻¹
theorem slotDefect_gaugeChange (Γ Γ' : F.SiteGauge) (u : VariationSlot F) :
    slotDefect W kW X k Γ u =
      slotSourceChange Γ Γ' u * slotDefect W kW X k Γ' u * (slotTargetChange W kW Γ Γ' u)⁻¹ := by
  rcases u with b | c
  · simp only [slotDefect, slotSourceChange, slotTargetChange, relativeDefect, gaugedChainFields,
      gaugeTransform, gaugeChange]
    group
  · simp only [slotDefect, slotSourceChange, slotTargetChange, gaugedLink, gaugeChange]
    group
def gaugeSlots (Γ : F.SiteGauge) : VariationSlot F → imaginaryQuaternions :=
  fun u => imaginaryOfUnit (slotDefect W kW X k Γ u)
theorem slotValues_gaugeVariation (Γ : F.SiteGauge) :
    slotValues (BlockAverages.gaugeVariation W kW X k Γ) = gaugeSlots W kW X k Γ := by
  funext u
  rcases u with b | c <;> rfl
def gaugeChangeRates (Γ Γ' : F.SiteGauge) : InfinitesimalGauge F :=
  fun j x => imaginaryOfUnit (gaugeChange Γ Γ' j x)
def scaledRates (ψ : F.Site 0 → ℝ) (ξ : InfinitesimalGauge F) : InfinitesimalGauge F :=
  fun j x => ψ (baseSite x) • ξ j x
theorem slotValues_gaugeChange (Γ Γ' : F.SiteGauge) (u : VariationSlot F) :
    slotValues (gaugeVariation W kW (gaugeChangeRates Γ Γ')) u =
      imaginaryOfUnit (slotSourceChange Γ Γ' u) - imaginaryOfUnit (slotTargetChange W kW Γ Γ' u) := by
  rcases u with b | c
  · simp only [slotValues, gaugeVariation, slotSourceChange, slotTargetChange, imaginaryOfUnit_conj]
    rfl
  · simp only [slotValues, gaugeVariation, slotSourceChange, slotTargetChange, imaginaryOfUnit_conj]
    rfl
theorem adjointImaginary_smul (g : UnitQuaternion) (r : ℝ) (w : imaginaryQuaternions) :
    adjointImaginary g (r • w) = r • adjointImaginary g w := by
  apply Subtype.ext
  exact adjointAction_smul g r (w : ℍ[ℝ])
theorem adjointImaginary_sub (g : UnitQuaternion) (v w : imaginaryQuaternions) :
    adjointImaginary g (v - w) = adjointImaginary g v - adjointImaginary g w := by
  apply Subtype.ext
  have : ((v - w : imaginaryQuaternions) : ℍ[ℝ]) = (v : ℍ[ℝ]) + -(w : ℍ[ℝ]) := by simp [sub_eq_add_neg]
  show adjointAction g _ = adjointAction g _ - adjointAction g _
  rw [this, adjointAction_add, adjointAction_neg, sub_eq_add_neg]
theorem slotValues_scaled_bond (ψ : F.Site 0 → ℝ) (ξ : InfinitesimalGauge F) {j : ℕ} (x : F.Site j) (i : Fin 4) :
    slotValues (gaugeVariation W kW (scaledRates ψ ξ)) (slotOfBond j x i) -
        ψ (baseSite x) • slotValues (gaugeVariation W kW ξ) (slotOfBond j x i) =
      (ψ (baseSite x) - ψ (baseSite (x + unitStep j i))) • adjointImaginary (W j x i) (ξ j (x + unitStep j i)) := by
  show (ψ (baseSite x) • ξ j x - adjointImaginary (W j x i) (ψ (baseSite (x + unitStep j i)) • ξ j (x + unitStep j i))) -
    ψ (baseSite x) • (ξ j x - adjointImaginary (W j x i) (ξ j (x + unitStep j i))) = _
  rw [adjointImaginary_smul]
  module
theorem slotValues_scaled_link (ψ : F.Site 0 → ℝ) (ξ : InfinitesimalGauge F) {j : ℕ} (hj : j + 1 ≤ F.top)
    (y : F.Site (j + 1)) :
    slotValues (gaugeVariation W kW (scaledRates ψ ξ)) (slotOfLink j y) -
        ψ (baseSite y) • slotValues (gaugeVariation W kW ξ) (slotOfLink j y) = 0 := by
  show (ψ (baseSite y) • ξ (j + 1) y - adjointImaginary (kW (j + 1) y) (ψ (baseSite (refineSite y)) • ξ j (refineSite y))) -
    ψ (baseSite y) • (ξ (j + 1) y - adjointImaginary (kW (j + 1) y) (ξ j (refineSite y))) = 0
  rw [baseSite_refineSite j hj, adjointImaginary_smul]
  module
end
end YangMills.Construction.BlockAverages.VariationRates
end

import YangMills.Construction.ColdChainAtEveryLevel.ComplexifiedQuaternions
import YangMills.Construction.ColdChainAtEveryLevel.NormsOfCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction
namespace BlockAverages
open ComplexifiedQuaternions
variable {F : BlockFrame}
def ofUnit (g : UnitQuaternion) : ComplexQuat := ofQuat (g : ℍ[ℝ])
theorem ofUnit_mul (g h : UnitQuaternion) : ofUnit (g * h) = ofUnit g * ofUnit h := by
  simp [ofUnit, ofQuat_mul]
theorem ofUnit_one : ofUnit 1 = 1 := by
  simp [ofUnit, ofQuat_one]
theorem ofUnit_inv (g : UnitQuaternion) : ofUnit g⁻¹ = Matrix.adjugate (ofUnit g) := by
  have : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := rfl
  rw [ofUnit, this, ofUnit, adjugate_ofQuat]
theorem det_ofUnit (g : UnitQuaternion) : (ofUnit g).det = 1 := by
  have h : ‖(g : ℍ[ℝ])‖ = 1 := by
    have h1 := Unitary.coe_star_mul_self g
    have h2 : ‖star (g : ℍ[ℝ]) * g‖ = ‖(g : ℍ[ℝ])‖ * ‖(g : ℍ[ℝ])‖ := CStarRing.norm_star_mul_self
    rw [h1, norm_one] at h2
    nlinarith [norm_nonneg (g : ℍ[ℝ])]
  rw [ofUnit, det_ofQuat, h]
  simp
theorem ofUnit_inv_mul (g : UnitQuaternion) : ofUnit g⁻¹ * ofUnit g = 1 := by
  rw [← ofUnit_mul, inv_mul_cancel, ofUnit_one]
theorem ofUnit_mul_inv (g : UnitQuaternion) : ofUnit g * ofUnit g⁻¹ = 1 := by
  rw [← ofUnit_mul, mul_inv_cancel, ofUnit_one]
theorem norm_ofUnit_mul (g : UnitQuaternion) (e : ComplexQuat) : ‖ofUnit g * e‖ = ‖e‖ := by apply _root_.YangMills.Construction.ComplexifiedQuaternions.norm_ofQuat_unitary_mul <;> assumption
theorem norm_mul_ofUnit (g : UnitQuaternion) (e : ComplexQuat) : ‖e * ofUnit g‖ = ‖e‖ := by apply _root_.YangMills.Construction.ComplexifiedQuaternions.norm_mul_ofQuat_unitary <;> assumption
def conjByUnit (g : UnitQuaternion) (e : ComplexQuat) : ComplexQuat := ofUnit g * e * ofUnit g⁻¹
theorem norm_conjByUnit (g : UnitQuaternion) (e : ComplexQuat) : ‖conjByUnit g e‖ = ‖e‖ := by
  rw [conjByUnit, norm_mul_ofUnit, norm_ofUnit_mul]
theorem purePart_conjByUnit (g : UnitQuaternion) (e : ComplexQuat) :
    purePart (conjByUnit g e) = conjByUnit g (purePart e) := by
  have h := purePart_conj g e
  have h2 : ofQuat (star (g : ℍ[ℝ])) = ofUnit g⁻¹ := rfl
  rw [h2] at h
  exact h
def ofQuatAddHom : ℍ[ℝ] →+ ComplexQuat := AddMonoidHom.mk' ofQuat ofQuat_add
theorem ofQuat_sum {ι : Type} (s : Finset ι) (f : ι → ℍ[ℝ]) :
    ofQuat (∑ i ∈ s, f i) = ∑ i ∈ s, ofQuat (f i) :=
  map_sum ofQuatAddHom f s
def ofQuatRingHom : ℍ[ℝ] →+* ComplexQuat where
  toFun := ofQuat
  map_one' := ofQuat_one
  map_mul' := ofQuat_mul
  map_zero' := ofQuat_zero
  map_add' := ofQuat_add
theorem continuous_ofQuat : Continuous ofQuat :=
  AddMonoidHomClass.continuous_of_bound ofQuatAddHom 1 fun q => by
    simp only [one_mul]
    exact (norm_ofQuat q).le
theorem ofQuat_exp (w : ℍ[ℝ]) : ofQuat (NormedSpace.exp w) = NormedSpace.exp (ofQuat w) :=
  NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) ofQuatRingHom continuous_ofQuat w (by
    rw [NormedSpace.expSeries_radius_eq_top ℝ ℍ[ℝ]]
    exact edist_lt_top _ _)
theorem unitPart_ofQuat (q : ℍ[ℝ]) : unitPart (ofQuat q) = ofUnit (polarUnit q) := by
  by_cases h : q = 0
  · simp [unitPart, polarUnit, h, ofQuat_zero, ofUnit_one]
  · have hc : ofQuat q ≠ 0 := by
      intro h0
      apply h
      have := norm_ofQuat q
      rw [h0, norm_zero] at this
      exact norm_eq_zero.1 this.symm
    have hn : 0 < ‖q‖ := norm_pos_iff.2 h
    simp only [unitPart, if_neg hc, polarUnit, dif_neg h, ofUnit, det_ofQuat, invSqrt_ofReal_sq hn,
      ofQuat_smul]
structure ComplexChainChart (F : BlockFrame) where
  re : ChainChart F
  im : ChainChart F
def complexifiedImaginary (a b : imaginaryQuaternions) : ComplexQuat :=
  ofQuat (a : ℍ[ℝ]) + Complex.I • ofQuat (b : ℍ[ℝ])
def unitExp (e : ComplexQuat) : ComplexQuat := unitPart (NormedSpace.exp e)
abbrev BlockFrame.ComplexField (F : BlockFrame) (j : ℕ) : Type := F.Site j → Fin 4 → ComplexQuat
def complexLinkValue {j : ℕ} (X : F.ComplexField j) (x : F.Site j) (st : PathStep) : ComplexQuat :=
  if st.2 then X x st.1 else Matrix.adjugate (X (x - unitStep j st.1) st.1)
def complexPathHolonomy {j : ℕ} (X : F.ComplexField j) : F.Site j → List PathStep → ComplexQuat
  | _, [] => 1
  | x, st :: r => complexLinkValue X x st * complexPathHolonomy X (x + stepDisplacement j st) r
def contourWeight (F : BlockFrame) : ℂ := ((1 / (24 * (F.blockSide : ℝ) ^ 4) : ℝ) : ℂ)
def complexContourAverage {j : ℕ} (X : F.ComplexField j) (c : F.Site (j + 1) × Fin 4) : ComplexQuat :=
  contourWeight F • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    complexPathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2)
def complexRelativePathAverage {j : ℕ} (X : F.ComplexField j) (R : F.GaugeField j) (y : F.Site (j + 1)) :
    ComplexQuat :=
  contourWeight F • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    complexPathHolonomy X (refineSite y) (axisPath h π) * ofUnit (pathHolonomy R (refineSite y) (axisPath h π))⁻¹
def complexBalancingGauge {j : ℕ} (X : F.ComplexField j) (R : F.GaugeField j) (y : F.Site (j + 1)) :
    ComplexQuat :=
  Matrix.adjugate (unitPart (complexRelativePathAverage X R y))
def complexGaugedContourAverage {j : ℕ} (X : F.ComplexField j) (k : F.Site (j + 1) → ComplexQuat)
    (c : F.Site (j + 1) × Fin 4) : ComplexQuat :=
  k c.1 * complexContourAverage X c * Matrix.adjugate (k (c.1 + unitStep (j + 1) c.2))
def complexChartField (R : F.FieldChain) (W : ComplexChainChart F) : (j : ℕ) → F.ComplexField j
  | 0 => fun x i => unitExp (complexifiedImaginary (W.re.fine x i) (W.im.fine x i)) * ofUnit (R 0 x i)
  | j + 1 => fun y i =>
      unitExp (complexifiedImaginary (W.re.coarse j y i) (W.im.coarse j y i)) *
        ofUnit (referenceDefect R j (y, i)) *
      unitPart (complexGaugedContourAverage (complexChartField R W j)
        (complexBalancingGauge (complexChartField R W j) (R j)) (y, i))
def complexifyField {j : ℕ} (X : F.GaugeField j) : F.ComplexField j := fun x i => ofUnit (X x i)
def complexFieldChain (R : F.FieldChain) (W : ComplexChainChart F) (V : F.GaugeField F.top) :
    (j : ℕ) → F.ComplexField j := by
  classical exact Function.update (complexChartField R W) F.top (complexifyField V)
def complexBalancingGauges (R : F.FieldChain) (W : ComplexChainChart F) :
    (j : ℕ) → F.Site j → ComplexQuat
  | 0 => fun _ => 1
  | j + 1 => complexBalancingGauge (complexChartField R W j) (R j)
def complexBlockFit (m X' : ComplexQuat) : ℂ := principalSqrt m.det - (m * Matrix.adjugate X').trace / 2
def complexPlaquetteHolonomy {j : ℕ} (X : F.ComplexField j) (p : F.Site j × Fin 4 × Fin 4) : ComplexQuat :=
  complexPathHolonomy X p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)]
def complexPlaquetteTerm (X : F.ComplexField 0) (p : F.Site 0 × Fin 4 × Fin 4) : ℂ :=
  1 - (complexPlaquetteHolonomy X p).trace / 2
def complexBondTerm (R : F.FieldChain) (W : ComplexChainChart F) (V : F.GaugeField F.top) (j : ℕ)
    (c : F.Site (j + 1) × Fin 4) : ℂ :=
  complexBlockFit (complexGaugedContourAverage (complexFieldChain R W V j) (complexBalancingGauges R W (j + 1)) c)
    (complexFieldChain R W V (j + 1) c.1 c.2)
def complexCellTerms (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (W : ComplexChainChart F)
    (V : F.GaugeField F.top) (z : F.Cell) : ℂ :=
  ∑ p ∈ plaquettesOver S {z} 0, complexPlaquetteTerm (complexChartField R W 0) p +
    (a : ℂ) * ∑ j ∈ Finset.range F.top, ∑ c ∈ bondsOver S {z} (j + 1), complexBondTerm R W V j c
def realChart (U : ChainChart F) : ComplexChainChart F := ⟨U, ⟨fun _ _ => 0, fun _ _ _ => 0⟩⟩
theorem complexLinkValue_complexify {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (st : PathStep) :
    complexLinkValue (complexifyField X) x st = ofUnit (linkValue X x st) := by
  by_cases h : st.2
  · simp [complexLinkValue, linkValue, h, complexifyField]
  · simp [complexLinkValue, linkValue, h, complexifyField, ofUnit_inv]
theorem complexPathHolonomy_complexify {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (l : List PathStep) :
    complexPathHolonomy (complexifyField X) x l = ofUnit (pathHolonomy X x l) := by
  induction l generalizing x with
  | nil => simp [complexPathHolonomy, pathHolonomy, ofUnit_one]
  | cons st r ih =>
    simp only [complexPathHolonomy, pathHolonomy, complexLinkValue_complexify, ih, ofUnit_mul]
theorem complexContourAverage_complexify {j : ℕ} (X : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) :
    complexContourAverage (complexifyField X) c = ofQuat (contourAverage X c) := by
  simp only [complexContourAverage, contourAverage, ofQuat_smul, ofQuat_sum, complexPathHolonomy_complexify,
    contourWeight, ofUnit]
theorem complexRelativePathAverage_complexify {j : ℕ} (X R : F.GaugeField j) (y : F.Site (j + 1)) :
    complexRelativePathAverage (complexifyField X) R y = ofQuat (relativePathAverage X R y) := by
  simp only [complexRelativePathAverage, relativePathAverage, ofQuat_smul, ofQuat_sum,
    complexPathHolonomy_complexify, contourWeight, ← ofUnit_mul]
  rfl
theorem complexBalancingGauge_complexify {j : ℕ} (X R : F.GaugeField j) (y : F.Site (j + 1)) :
    complexBalancingGauge (complexifyField X) R y = ofUnit (balancingGauge X R y) := by
  simp only [complexBalancingGauge, balancingGauge, complexRelativePathAverage_complexify, unitPart_ofQuat,
    ofUnit_inv]
theorem complexGaugedContourAverage_complexify {j : ℕ} (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion)
    (c : F.Site (j + 1) × Fin 4) :
    complexGaugedContourAverage (complexifyField X) (fun y => ofUnit (k y)) c =
      ofQuat (gaugedContourAverage X k c) := by
  simp only [complexGaugedContourAverage, gaugedContourAverage, complexContourAverage_complexify, ofQuat_mul]
  show _ = ofUnit _ * _ * ofUnit _
  rw [ofUnit_inv]
theorem complexifiedImaginary_zero (a : imaginaryQuaternions) :
    complexifiedImaginary a 0 = ofQuat (a : ℍ[ℝ]) := by
  simp [complexifiedImaginary, ofQuat_zero]
theorem unitExp_complexifiedImaginary_zero (a : imaginaryQuaternions) :
    unitExp (complexifiedImaginary a 0) = ofUnit (expUnit a) := by
  have h := unitPart_ofQuat (NormedSpace.exp (a : ℍ[ℝ]))
  have h2 : polarUnit (NormedSpace.exp (a : ℍ[ℝ])) = expUnit a := by
    have hn : ‖NormedSpace.exp (a : ℍ[ℝ])‖ = 1 := by
      rw [Quaternion.norm_exp]
      have : (a : ℍ[ℝ]).re = 0 := a.2
      simp [this]
    have hne : NormedSpace.exp (a : ℍ[ℝ]) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hn
      exact zero_ne_one hn
    apply Subtype.ext
    simp [polarUnit, hne, hn, expUnit]
  rw [unitExp, complexifiedImaginary_zero, ← ofQuat_exp, h, h2]
theorem complexChartField_realChart (R : F.FieldChain) (U : ChainChart F) (j : ℕ) :
    complexChartField R (realChart U) j = complexifyField (chartField R U j) := by
  induction j with
  | zero =>
    funext x i
    simp [complexChartField, realChart, chartField, complexifyField, unitExp_complexifiedImaginary_zero,
      ofUnit_mul]
  | succ j ih =>
    funext y i
    have h : complexBalancingGauge (complexifyField (chartField R U j)) (R j) =
        fun y => ofUnit (balancingGauge (chartField R U j) (R j) y) := by
      funext y
      rw [complexBalancingGauge_complexify]
    have e1 : complexifyField (chartField R U (j + 1)) y i = ofUnit (chartField R U (j + 1) y i) := rfl
    rw [e1]
    simp only [complexChartField, chartField, ih, ofUnit_mul]
    rw [h, complexGaugedContourAverage_complexify, unitPart_ofQuat]
    have e2 : complexifiedImaginary ((realChart U).re.coarse j y i) ((realChart U).im.coarse j y i) =
        complexifiedImaginary (U.coarse j y i) 0 := rfl
    rw [e2, unitExp_complexifiedImaginary_zero]
end BlockAverages
end YangMills.Construction
end

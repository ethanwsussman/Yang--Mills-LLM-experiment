import YangMills.Construction.ColdChainAtEveryLevel.ComplexDifferences
import YangMills.Construction.ColdChainAtEveryLevel.SecondDifferencesOfUnits
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfAMovedExponentialProof
import YangMills.Construction.HoleBesideASecondHole.TermsOfSmallCoordinatesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.PlaquetteSecondDifference
open BlockAverages ComplexifiedQuaternions ComplexDifferences SecondDifferences
theorem ofQuat_sub_eq (p q : ℍ[ℝ]) : ofQuat (p - q) = ofQuat p - ofQuat q := ofQuatRingHom.map_sub p q
theorem norm_expUnit_sub_one_sub_le {ξ : imaginaryQuaternions} (hξ : ‖(ξ : ℍ[ℝ])‖ ≤ 1) :
    ‖((expUnit ξ : UnitQuaternion) : ℍ[ℝ]) - 1 - (ξ : ℍ[ℝ])‖ ≤ ‖(ξ : ℍ[ℝ])‖ ^ 2 := by
  have h := norm_exp_sub_one_sub_le (x := ofQuat (ξ : ℍ[ℝ])) (by rwa [norm_ofQuat])
  rw [← ofQuat_exp, norm_ofQuat] at h
  have e : ofQuat (NormedSpace.exp (ξ : ℍ[ℝ])) - 1 - ofQuat (ξ : ℍ[ℝ]) =
      ofQuat (NormedSpace.exp (ξ : ℍ[ℝ]) - 1 - (ξ : ℍ[ℝ])) := by
    simp only [ofQuat_sub_eq, ofQuat_one]
  rw [e, norm_ofQuat] at h
  exact h
theorem norm_expUnit_second_diff_le {ξ η : imaginaryQuaternions} (hξ : ‖(ξ : ℍ[ℝ])‖ ≤ 1 / 4000)
    (hη : ‖(η : ℍ[ℝ])‖ ≤ 1 / 4000) :
    ‖((expUnit (ξ + η) : UnitQuaternion) : ℍ[ℝ]) - (expUnit ξ : UnitQuaternion) - (expUnit η : UnitQuaternion) + 1‖ ≤
      8256 * ‖(ξ : ℍ[ℝ])‖ * ‖(η : ℍ[ℝ])‖ := by
  have h := norm_unitExp_second_diff_le (y := 0) (e₁ := ofQuat (ξ : ℍ[ℝ])) (e₂ := ofQuat (η : ℍ[ℝ]))
    (by simp) (by rwa [norm_ofQuat]) (by rwa [norm_ofQuat])
  rw [norm_ofQuat, norm_ofQuat, zero_add, zero_add, unitExp_zero, ← ofQuat_add] at h
  have eξ : unitExp (ofQuat (ξ : ℍ[ℝ])) = ofUnit (expUnit ξ) := by
    rw [← unitExp_complexifiedImaginary_zero, complexifiedImaginary_zero]
  have eη : unitExp (ofQuat (η : ℍ[ℝ])) = ofUnit (expUnit η) := by
    rw [← unitExp_complexifiedImaginary_zero, complexifiedImaginary_zero]
  have eξη : unitExp (ofQuat ((ξ : ℍ[ℝ]) + η)) = ofUnit (expUnit (ξ + η)) := by
    rw [← unitExp_complexifiedImaginary_zero, complexifiedImaginary_zero]
    rfl
  rw [eξ, eη, eξη] at h
  have e : ofUnit (expUnit (ξ + η)) - ofUnit (expUnit ξ) - ofUnit (expUnit η) + 1 =
      ofQuat (((expUnit (ξ + η) : UnitQuaternion) : ℍ[ℝ]) - (expUnit ξ : UnitQuaternion) -
        (expUnit η : UnitQuaternion) + 1) := by
    simp only [ofUnit, ofQuat_add, ofQuat_one, ofQuat_sub_eq]
  rw [e, norm_ofQuat] at h
  exact h
def conjExp (g : UnitQuaternion) (ξ : imaginaryQuaternions) : UnitQuaternion := g * expUnit ξ * g⁻¹
theorem star_coe_imaginary (ξ : imaginaryQuaternions) : star (ξ : ℍ[ℝ]) = -(ξ : ℍ[ℝ]) := by apply _root_.YangMills.Construction.GaugeMotions.star_coe_imaginary <;> assumption
theorem expUnit_neg_eq_inv (ξ : imaginaryQuaternions) : expUnit (-ξ) = (expUnit ξ)⁻¹ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.expUnit_neg <;> assumption
theorem coe_mul_coe_inv (g : UnitQuaternion) : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_mul_coe_inv <;> assumption
theorem coe_conjExp_sub_one (g : UnitQuaternion) (ξ : imaginaryQuaternions) :
    ((conjExp g ξ : UnitQuaternion) : ℍ[ℝ]) - 1 =
      (g : ℍ[ℝ]) * (((expUnit ξ : UnitQuaternion) : ℍ[ℝ]) - 1) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  have h := coe_mul_coe_inv g
  change (g : ℍ[ℝ]) * ((expUnit ξ : UnitQuaternion) : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 = _
  rw [mul_sub, sub_mul, mul_one, h]
theorem norm_conj (g : UnitQuaternion) (q : ℍ[ℝ]) :
    ‖(g : ℍ[ℝ]) * q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖q‖ := by
  rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, mul_one]
theorem norm_coe_expUnit_sub_one_le (ξ : imaginaryQuaternions) :
    ‖((expUnit ξ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(ξ : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.SmallCellTerms.norm_coe_expUnit_sub_one_le <;> assumption
theorem conjExp_firstOrderApprox (g : UnitQuaternion) {ξ : imaginaryQuaternions} (hξ : ‖(ξ : ℍ[ℝ])‖ ≤ 1) :
    FirstOrderApprox ‖(ξ : ℍ[ℝ])‖ 1 (conjExp g ξ) (adjointAction g (ξ : ℍ[ℝ])) where
  size := by
    rw [coe_conjExp_sub_one, norm_conj]
    exact norm_coe_expUnit_sub_one_le ξ
  remainder := by
    have e : ((conjExp g ξ : UnitQuaternion) : ℍ[ℝ]) - 1 - adjointAction g (ξ : ℍ[ℝ]) =
        (g : ℍ[ℝ]) * (((expUnit ξ : UnitQuaternion) : ℍ[ℝ]) - 1 - (ξ : ℍ[ℝ])) *
          ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      rw [coe_conjExp_sub_one, adjointAction]
      noncomm_ring
    rw [e, norm_conj, one_mul]
    exact norm_expUnit_sub_one_sub_le hξ
theorem conjExp_secondDifferenceBound (g : UnitQuaternion) {ξ η : imaginaryQuaternions}
    (hξ : ‖(ξ : ℍ[ℝ])‖ ≤ 1 / 4000) (hη : ‖(η : ℍ[ℝ])‖ ≤ 1 / 4000) :
    SecondDifferenceBound ‖(ξ : ℍ[ℝ])‖ ‖(η : ℍ[ℝ])‖ 8256 (conjExp g ξ) (conjExp g η) (conjExp g (ξ + η)) where
  size_left := (conjExp_firstOrderApprox g (by linarith)).size
  size_right := (conjExp_firstOrderApprox g (by linarith)).size
  second_diff := by
    have e : ((conjExp g (ξ + η) : UnitQuaternion) : ℍ[ℝ]) - (conjExp g ξ : UnitQuaternion) -
        (conjExp g η : UnitQuaternion) + 1 =
        (g : ℍ[ℝ]) * (((expUnit (ξ + η) : UnitQuaternion) : ℍ[ℝ]) - (expUnit ξ : UnitQuaternion) -
          (expUnit η : UnitQuaternion) + 1) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      have a1 := coe_conjExp_sub_one g (ξ + η)
      have a2 := coe_conjExp_sub_one g ξ
      have a3 := coe_conjExp_sub_one g η
      have h := coe_mul_coe_inv g
      have e1 : ((conjExp g (ξ + η) : UnitQuaternion) : ℍ[ℝ]) - (conjExp g ξ : UnitQuaternion) -
          (conjExp g η : UnitQuaternion) + 1 =
          (((conjExp g (ξ + η) : UnitQuaternion) : ℍ[ℝ]) - 1) -
            (((conjExp g ξ : UnitQuaternion) : ℍ[ℝ]) - 1) -
            (((conjExp g η : UnitQuaternion) : ℍ[ℝ]) - 1) := by abel
      rw [e1, a1, a2, a3]
      noncomm_ring
    rw [e, norm_conj]
    exact norm_expUnit_second_diff_le hξ hη
def plaquetteHolonomy (r u : Fin 4 → UnitQuaternion) : UnitQuaternion :=
  (u 0 * r 0) * (u 1 * r 1) * (u 2 * r 2)⁻¹ * (u 3 * r 3)⁻¹
def refHolonomy (r : Fin 4 → UnitQuaternion) : UnitQuaternion := r 0 * r 1 * (r 2)⁻¹ * (r 3)⁻¹
def plaquetteVariation (r : Fin 4 → UnitQuaternion) (u : Fin 4 → imaginaryQuaternions) : UnitQuaternion :=
  conjExp 1 (u 0) * conjExp (r 0) (u 1) * conjExp (r 0 * r 1 * (r 2)⁻¹) (-u 2) *
    conjExp (r 0 * r 1 * (r 2)⁻¹ * (r 3)⁻¹) (-u 3)
theorem plaquetteHolonomy_expUnit (r : Fin 4 → UnitQuaternion) (u : Fin 4 → imaginaryQuaternions) :
    plaquetteHolonomy r (fun i => expUnit (u i)) = plaquetteVariation r u * refHolonomy r := by
  simp only [plaquetteHolonomy, plaquetteVariation, refHolonomy, conjExp, expUnit_neg_eq_inv]
  group
def covariantCurl (r : Fin 4 → UnitQuaternion) (u : Fin 4 → imaginaryQuaternions) : ℍ[ℝ] :=
  (u 0 : ℍ[ℝ]) + adjointAction (r 0) (u 1) - adjointAction (r 0 * r 1 * (r 2)⁻¹) (u 2) -
    adjointAction (r 0 * r 1 * (r 2)⁻¹ * (r 3)⁻¹) (u 3)
theorem adjointAction_map_neg (g : UnitQuaternion) (q : ℍ[ℝ]) : adjointAction g (-q) = - adjointAction g q := by
  simp [adjointAction]
theorem adjointAction_one_apply (q : ℍ[ℝ]) : adjointAction 1 q = q := by
  simp [adjointAction]
theorem plaquetteVariation_firstOrderApprox (r : Fin 4 → UnitQuaternion) (u : Fin 4 → imaginaryQuaternions) {t : ℝ}
    (ht : ∑ i, ‖(u i : ℍ[ℝ])‖ ≤ t) (ht1 : t ≤ 1) :
    FirstOrderApprox t 4 (plaquetteVariation r u) (covariantCurl r u) := by
  have hs := Fin.sum_univ_four fun i => ‖(u i : ℍ[ℝ])‖
  have n0 := norm_nonneg (u 0 : ℍ[ℝ])
  have n1 := norm_nonneg (u 1 : ℍ[ℝ])
  have n2 := norm_nonneg (u 2 : ℍ[ℝ])
  have n3 := norm_nonneg (u 3 : ℍ[ℝ])
  have m2 : ‖((-u 2 : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖(u 2 : ℍ[ℝ])‖ := norm_neg _
  have m3 : ‖((-u 3 : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖(u 3 : ℍ[ℝ])‖ := norm_neg _
  have a0 := conjExp_firstOrderApprox 1 (ξ := u 0) (by linarith)
  have a1 := conjExp_firstOrderApprox (r 0) (ξ := u 1) (by linarith)
  have a2 := conjExp_firstOrderApprox (r 0 * r 1 * (r 2)⁻¹) (ξ := -u 2) (by rw [m2]; linarith)
  have a3 := conjExp_firstOrderApprox (r 0 * r 1 * (r 2)⁻¹ * (r 3)⁻¹) (ξ := -u 3) (by rw [m3]; linarith)
  rw [m2] at a2
  rw [m3] at a3
  have b := ((a0.mul a1 (c'' := 2) (by norm_num) (by norm_num) (by norm_num)).mul a2 (c'' := 3)
    (by norm_num) (by norm_num) (by norm_num)).mul a3 (c'' := 4) (by norm_num) (by norm_num) (by norm_num)
  have ecurl : covariantCurl r u = adjointAction 1 (u 0 : ℍ[ℝ]) + adjointAction (r 0) (u 1 : ℍ[ℝ]) +
      adjointAction (r 0 * r 1 * (r 2)⁻¹) ((-u 2 : imaginaryQuaternions) : ℍ[ℝ]) +
      adjointAction (r 0 * r 1 * (r 2)⁻¹ * (r 3)⁻¹) ((-u 3 : imaginaryQuaternions) : ℍ[ℝ]) := by
    have e2 : ((-u 2 : imaginaryQuaternions) : ℍ[ℝ]) = -(u 2 : ℍ[ℝ]) := rfl
    have e3 : ((-u 3 : imaginaryQuaternions) : ℍ[ℝ]) = -(u 3 : ℍ[ℝ]) := rfl
    rw [e2, e3, adjointAction_map_neg, adjointAction_map_neg, adjointAction_one_apply, covariantCurl]
    abel
  rw [ecurl]
  have hT : ‖(u 0 : ℍ[ℝ])‖ + ‖(u 1 : ℍ[ℝ])‖ + ‖(u 2 : ℍ[ℝ])‖ + ‖(u 3 : ℍ[ℝ])‖ ≤ t := by linarith
  have h0 : 0 ≤ ‖(u 0 : ℍ[ℝ])‖ + ‖(u 1 : ℍ[ℝ])‖ + ‖(u 2 : ℍ[ℝ])‖ + ‖(u 3 : ℍ[ℝ])‖ := by positivity
  refine ⟨b.size.trans hT, b.remainder.trans ?_⟩
  have := pow_le_pow_left₀ h0 hT 2
  linarith
theorem plaquetteVariation_secondDifferenceBound (r : Fin 4 → UnitQuaternion) (a b : Fin 4 → imaginaryQuaternions)
    {t₁ t₂ : ℝ} (h1 : ∑ i, ‖(a i : ℍ[ℝ])‖ ≤ t₁) (h2 : ∑ i, ‖(b i : ℍ[ℝ])‖ ≤ t₂) (ht1 : t₁ ≤ 1 / 4000)
    (ht2 : t₂ ≤ 1 / 4000) :
    SecondDifferenceBound t₁ t₂ 24768 (plaquetteVariation r a) (plaquetteVariation r b)
      (plaquetteVariation r (a + b)) := by
  have hs1 := Fin.sum_univ_four fun i => ‖(a i : ℍ[ℝ])‖
  have hs2 := Fin.sum_univ_four fun i => ‖(b i : ℍ[ℝ])‖
  have p0 := norm_nonneg (a 0 : ℍ[ℝ])
  have p1 := norm_nonneg (a 1 : ℍ[ℝ])
  have p2 := norm_nonneg (a 2 : ℍ[ℝ])
  have p3 := norm_nonneg (a 3 : ℍ[ℝ])
  have q0 := norm_nonneg (b 0 : ℍ[ℝ])
  have q1 := norm_nonneg (b 1 : ℍ[ℝ])
  have q2 := norm_nonneg (b 2 : ℍ[ℝ])
  have q3 := norm_nonneg (b 3 : ℍ[ℝ])
  have ma2 : ‖((-a 2 : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖(a 2 : ℍ[ℝ])‖ := norm_neg _
  have ma3 : ‖((-a 3 : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖(a 3 : ℍ[ℝ])‖ := norm_neg _
  have mb2 : ‖((-b 2 : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖(b 2 : ℍ[ℝ])‖ := norm_neg _
  have mb3 : ‖((-b 3 : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖(b 3 : ℍ[ℝ])‖ := norm_neg _
  have c0 := conjExp_secondDifferenceBound 1 (ξ := a 0) (η := b 0) (by linarith) (by linarith)
  have c1 := conjExp_secondDifferenceBound (r 0) (ξ := a 1) (η := b 1) (by linarith) (by linarith)
  have c2 := conjExp_secondDifferenceBound (r 0 * r 1 * (r 2)⁻¹) (ξ := -a 2) (η := -b 2)
    (by rw [ma2]; linarith) (by rw [mb2]; linarith)
  have c3 := conjExp_secondDifferenceBound (r 0 * r 1 * (r 2)⁻¹ * (r 3)⁻¹) (ξ := -a 3) (η := -b 3)
    (by rw [ma3]; linarith) (by rw [mb3]; linarith)
  rw [ma2, mb2] at c2
  rw [ma3, mb3] at c3
  have d := ((c0.mul c1 (C'' := 24768) (by norm_num) (by norm_num) (by norm_num)).mul c2 (C'' := 24768)
    (by norm_num) (by norm_num) (by norm_num)).mul c3 (C'' := 24768) (by norm_num) (by norm_num) (by norm_num)
  have e2 : -a 2 + -b 2 = -(a + b) 2 := by simp [add_comm]
  have e3 : -a 3 + -b 3 = -(a + b) 3 := by simp [add_comm]
  rw [e2, e3] at d
  have T1 : ‖(a 0 : ℍ[ℝ])‖ + ‖(a 1 : ℍ[ℝ])‖ + ‖(a 2 : ℍ[ℝ])‖ + ‖(a 3 : ℍ[ℝ])‖ ≤ t₁ := by linarith
  have T2 : ‖(b 0 : ℍ[ℝ])‖ + ‖(b 1 : ℍ[ℝ])‖ + ‖(b 2 : ℍ[ℝ])‖ + ‖(b 3 : ℍ[ℝ])‖ ≤ t₂ := by linarith
  have P1 : 0 ≤ ‖(a 0 : ℍ[ℝ])‖ + ‖(a 1 : ℍ[ℝ])‖ + ‖(a 2 : ℍ[ℝ])‖ + ‖(a 3 : ℍ[ℝ])‖ := by positivity
  have P2 : 0 ≤ ‖(b 0 : ℍ[ℝ])‖ + ‖(b 1 : ℍ[ℝ])‖ + ‖(b 2 : ℍ[ℝ])‖ + ‖(b 3 : ℍ[ℝ])‖ := by positivity
  refine ⟨d.size_left.trans T1, d.size_right.trans T2, d.second_diff.trans ?_⟩
  have := mul_le_mul T1 T2 P2 (P1.trans T1)
  nlinarith
theorem expUnit_zero_eq_one : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem conjExp_zero (g : UnitQuaternion) : conjExp g 0 = 1 := by
  simp [conjExp, expUnit_zero_eq_one]
theorem plaquetteVariation_zero (r : Fin 4 → UnitQuaternion) : plaquetteVariation r 0 = 1 := by
  simp [plaquetteVariation, conjExp_zero]
theorem abs_plaquette_second_diff_sub_inner_le (r : Fin 4 → UnitQuaternion) (a b : Fin 4 → imaginaryQuaternions)
    {t₁ t₂ : ℝ} (h1 : ∑ i, ‖(a i : ℍ[ℝ])‖ ≤ t₁) (h2 : ∑ i, ‖(b i : ℍ[ℝ])‖ ≤ t₂) (ht1 : t₁ ≤ 1 / 4000)
    (ht2 : t₂ ≤ 1 / 4000) :
    |(1 - ((plaquetteVariation r (a + b) * refHolonomy r : UnitQuaternion) : ℍ[ℝ]).re) -
        (1 - ((plaquetteVariation r a * refHolonomy r : UnitQuaternion) : ℍ[ℝ]).re) -
        (1 - ((plaquetteVariation r b * refHolonomy r : UnitQuaternion) : ℍ[ℝ]).re) +
        (1 - ((refHolonomy r : UnitQuaternion) : ℍ[ℝ]).re) -
        inner ℝ (covariantCurl r a) (covariantCurl r b)| ≤
      200000 * t₁ * t₂ * (‖((refHolonomy r : UnitQuaternion) : ℍ[ℝ]) - 1‖ + t₁ + t₂) := by
  have t10 : 0 ≤ t₁ := (Finset.sum_nonneg fun i _ => norm_nonneg _).trans h1
  have t20 : 0 ≤ t₂ := (Finset.sum_nonneg fun i _ => norm_nonneg _).trans h2
  have hT := plaquetteVariation_secondDifferenceBound r a b h1 h2 ht1 ht2
  have n1 := plaquetteVariation_firstOrderApprox r a h1 (by linarith)
  have n2 := plaquetteVariation_firstOrderApprox r b h2 (by linarith)
  set P := refHolonomy r with hP
  set A₁ := plaquetteVariation r a with hA₁
  set A₂ := plaquetteVariation r b with hA₂
  set A₃ := plaquetteVariation r (a + b) with hA₃
  set v := covariantCurl r a with hv
  set w := covariantCurl r b with hw
  have key := abs_neg_re_secondDifference_mul_sub_inner_le A₁ A₂ A₃ P v w
  have e : (1 - ((A₃ * P : UnitQuaternion) : ℍ[ℝ]).re) - (1 - ((A₁ * P : UnitQuaternion) : ℍ[ℝ]).re) -
      (1 - ((A₂ * P : UnitQuaternion) : ℍ[ℝ]).re) + (1 - (P : ℍ[ℝ]).re) =
      -(((A₃ : ℍ[ℝ]) - A₁ - A₂ + 1) * P).re := by
    have : ((A₃ : ℍ[ℝ]) - A₁ - A₂ + 1) * P = (A₃ : ℍ[ℝ]) * P - A₁ * P - A₂ * P + P := by noncomm_ring
    rw [this]
    change (1 - ((A₃ : ℍ[ℝ]) * P).re) - (1 - ((A₁ : ℍ[ℝ]) * P).re) - (1 - ((A₂ : ℍ[ℝ]) * P).re) +
      (1 - (P : ℍ[ℝ]).re) = _
    simp only [Quaternion.re_add, Quaternion.re_sub]
    ring
  rw [e]
  refine key.trans ?_
  set d := (A₃ : ℍ[ℝ]) - A₁ - A₂ + 1 with hd
  set p := ‖(P : ℍ[ℝ]) - 1‖ with hp
  have p0 : 0 ≤ p := norm_nonneg _
  have hd0 : ‖d‖ ≤ 24768 * t₁ * t₂ := hT.second_diff
  have hs1 : ‖(A₁ : ℍ[ℝ]) - 1‖ ≤ t₁ := n1.size
  have hs2 : ‖(A₂ : ℍ[ℝ]) - 1‖ ≤ t₂ := n2.size
  have hf1 : ‖(A₁ : ℍ[ℝ]) - 1 - v‖ ≤ 4 * t₁ ^ 2 := n1.remainder
  have hf2 : ‖(A₂ : ℍ[ℝ]) - 1 - w‖ ≤ 4 * t₂ ^ 2 := n2.remainder
  have hvn : ‖v‖ ≤ 2 * t₁ := by
    have : v = ((A₁ : ℍ[ℝ]) - 1) - ((A₁ : ℍ[ℝ]) - 1 - v) := by abel
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    nlinarith
  have hT2 : t₁ * t₂ ≤ t₁ / 4000 := by nlinarith
  have hQ : 0 ≤ t₁ * t₂ := mul_nonneg t10 t20
  have b1 : ‖d‖ * p ≤ 24768 * t₁ * t₂ * p := mul_le_mul_of_nonneg_right hd0 p0
  have b2 : (‖(A₁ : ℍ[ℝ]) - 1‖ + ‖(A₂ : ℍ[ℝ]) - 1‖) * ‖d‖ ≤ (t₁ + t₂) * (24768 * t₁ * t₂) :=
    mul_le_mul (add_le_add hs1 hs2) hd0 (norm_nonneg _) (by positivity)
  have b3 : ‖d‖ ^ 2 / 2 ≤ (24768 * t₁ * t₂) ^ 2 / 2 := by
    have := pow_le_pow_left₀ (norm_nonneg d) hd0 2
    linarith
  have b4 : ‖(A₁ : ℍ[ℝ]) - 1 - v‖ * ‖(A₂ : ℍ[ℝ]) - 1‖ ≤ 4 * t₁ ^ 2 * t₂ :=
    mul_le_mul hf1 hs2 (norm_nonneg _) (by positivity)
  have b5 : ‖v‖ * ‖(A₂ : ℍ[ℝ]) - 1 - w‖ ≤ 2 * t₁ * (4 * t₂ ^ 2) :=
    mul_le_mul hvn hf2 (norm_nonneg _) (by positivity)
  have b6 : (24768 * t₁ * t₂) ^ 2 / 2 ≤ 80000 * t₁ * t₂ * t₁ := by
    have e6 : (24768 * t₁ * t₂) ^ 2 / 2 = (24768 ^ 2 / 2) * ((t₁ * t₂) * (t₁ * t₂)) := by ring
    have e7 : (t₁ * t₂) * (t₁ * t₂) ≤ (t₁ * t₂) * (t₁ / 4000) := mul_le_mul_of_nonneg_left hT2 hQ
    rw [e6]
    nlinarith
  have hfin : 24768 * t₁ * t₂ * p + (t₁ + t₂) * (24768 * t₁ * t₂) + 80000 * t₁ * t₂ * t₁ +
      4 * t₁ ^ 2 * t₂ + 2 * t₁ * (4 * t₂ ^ 2) ≤ 200000 * t₁ * t₂ * (p + t₁ + t₂) := by
    have c1 : 0 ≤ t₁ * t₂ * p := by positivity
    have c3 : 0 ≤ t₁ * t₂ * t₂ := by positivity
    nlinarith
  linarith
end YangMills.Construction.PlaquetteSecondDifference
end

import YangMills.Construction.Matrices.LogMeanCovarianceProof
import YangMills.Construction.Matrices.SmallDiameterMean
import YangMills.Construction.Matrices.UnimodularArgumentHolomorphyProof
import YangMills.Construction.Numerics.ExpLogNumericBounds
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Matrices.SmallDiameterMean
open YangMills.Construction.Matrices.ComplexMatrix2
open YangMills.Construction.Coordinates
variable {n : ℕ}
private def translatedLogAverage (T : Fin n → ComplexMatrix2) (Y : ComplexMatrix2) : ComplexMatrix2 :=
  Y + (n : ℂ)⁻¹ • ∑ i, logSeries (T i * matExp (-Y))
private theorem operatorNorm_neg (Y : ComplexMatrix2) : operatorNorm (-Y) = operatorNorm Y :=
  norm_neg Y
private theorem operatorNorm_mul_matExp_neg_sub_one_le (hX : ExpLogEstimates)
    {T Y : ComplexMatrix2} {d r : ℝ}
    (hT : operatorNorm (T - 1) ≤ d) (hY : operatorNorm Y ≤ r) :
    operatorNorm (T * matExp (-Y) - 1) ≤ (1 + d) * Real.exp r - 1 := by
  obtain ⟨-, -, c3, -⟩ := hX
  have h := c3 T (-Y)
  have h1 : operatorNorm (-Y) = operatorNorm Y := norm_neg Y
  rw [h1] at h
  have h2 : Real.exp (operatorNorm Y) ≤ Real.exp r := Real.exp_le_exp.mpr hY
  have h0 : 0 ≤ operatorNorm (T - 1) := norm_nonneg _
  have h3 : (1 + operatorNorm (T - 1)) * Real.exp (operatorNorm Y) ≤ (1 + d) * Real.exp r :=
    mul_le_mul (by linarith) h2 (Real.exp_pos _).le (by linarith)
  linarith
private theorem operatorNorm_le_one_add {T : ComplexMatrix2} {d : ℝ}
    (hT : operatorNorm (T - 1) ≤ d) : operatorNorm T ≤ 1 + d := by
  have e : T = 1 + (T - 1) := by abel
  have h := norm_add_le (1 : ComplexMatrix2) (T - 1)
  rw [← e, norm_one] at h
  linarith
private theorem term_sub_le (hX : ExpLogEstimates)
    (hN : Numerics.ExpLogNumericBounds) {T Y Y' : ComplexMatrix2}
    (hT : operatorNorm (T - 1) ≤ 1 / 40)
    (hY : operatorNorm Y ≤ 1 / 8) (hY' : operatorNorm Y' ≤ 1 / 8) :
    operatorNorm ((Y - Y') + (logSeries (T * matExp (-Y)) - logSeries (T * matExp (-Y')))) ≤
      2 / 5 * operatorNorm (Y - Y') := by
  have hE : Real.exp (1 / 8) < 1.1332 := hN.2.2.2.2.1
  have hA := operatorNorm_mul_matExp_neg_sub_one_le hX hT hY
  have hB := operatorNorm_mul_matExp_neg_sub_one_le hX hT hY'
  obtain ⟨-, c2, -, -, -, -, -, -, c9, -⟩ := hX
  have num : (1 + (1 / 40 : ℝ)) * Real.exp (1 / 8) - 1 ≤ 1 / 6 := by
    norm_num at hE ⊢
    linarith
  have h9 := (c9 (1 / 6) (T * matExp (-Y)) (T * matExp (-Y')) (by norm_num) (by norm_num)
    (hA.trans num) (hB.trans num)).2.2.1
  have h2 := c2 (-Y) (-Y') (1 / 8)
    (max_le ((operatorNorm_neg Y).trans_le hY) ((operatorNorm_neg Y').trans_le hY'))
  have hδ : operatorNorm (-Y - -Y') = operatorNorm (Y - Y') := by
    rw [neg_sub_neg]; exact norm_sub_rev _ _
  rw [hδ] at h2
  obtain ⟨h2a, h2b⟩ := h2
  have hTn := operatorNorm_le_one_add hT
  have hδ0 : 0 ≤ operatorNorm (Y - Y') := norm_nonneg _
  have hAB : operatorNorm (T * matExp (-Y) - T * matExp (-Y')) ≤
      (1 + 1 / 40) * (Real.exp (1 / 8) * operatorNorm (Y - Y')) := by
    rw [← mul_sub]
    exact (norm_mul_le _ _).trans (mul_le_mul hTn h2a (norm_nonneg _) (by norm_num))
  have key : (Y - Y') + (logSeries (T * matExp (-Y)) - logSeries (T * matExp (-Y'))) =
      (logSeries (T * matExp (-Y)) - logSeries (T * matExp (-Y')) -
          (T * matExp (-Y) - T * matExp (-Y'))) +
        T * (matExp (-Y) - matExp (-Y') - (-Y - -Y')) + -((T - 1) * (Y - Y')) := by
    noncomm_ring
  rw [key]
  have t1 := norm_add₃_le (a := logSeries (T * matExp (-Y)) - logSeries (T * matExp (-Y')) -
    (T * matExp (-Y) - T * matExp (-Y'))) (b := T * (matExp (-Y) - matExp (-Y') - (-Y - -Y')))
    (c := -((T - 1) * (Y - Y')))
  have t2 : operatorNorm (T * (matExp (-Y) - matExp (-Y') - (-Y - -Y'))) ≤
      (1 + 1 / 40) * ((Real.exp (1 / 8) - 1) * operatorNorm (Y - Y')) :=
    (norm_mul_le _ _).trans (mul_le_mul hTn h2b (norm_nonneg _) (by norm_num))
  have t3 : operatorNorm (-((T - 1) * (Y - Y'))) ≤ 1 / 40 * operatorNorm (Y - Y') := by
    rw [operatorNorm_neg]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hT hδ0)
  have t4 : operatorNorm (logSeries (T * matExp (-Y)) - logSeries (T * matExp (-Y')) -
      (T * matExp (-Y) - T * matExp (-Y'))) ≤
      1 / 5 * ((1 + 1 / 40) * (Real.exp (1 / 8) * operatorNorm (Y - Y'))) := by
    refine h9.trans ?_
    have : (1 / 6 : ℝ) / (1 - 1 / 6) = 1 / 5 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left hAB (by norm_num)
  have t5 : operatorNorm ((logSeries (T * matExp (-Y)) - logSeries (T * matExp (-Y')) -
      (T * matExp (-Y) - T * matExp (-Y'))) + T * (matExp (-Y) - matExp (-Y') - (-Y - -Y')) +
      -((T - 1) * (Y - Y'))) ≤
      (1 / 5 * ((1 + 1 / 40) * Real.exp (1 / 8)) + (1 + 1 / 40) * (Real.exp (1 / 8) - 1) +
        1 / 40) * operatorNorm (Y - Y') := by
    refine t1.trans ?_
    have : (1 / 5 * ((1 + 1 / 40) * Real.exp (1 / 8)) + (1 + 1 / 40) * (Real.exp (1 / 8) - 1) +
        1 / 40) * operatorNorm (Y - Y') =
        1 / 5 * ((1 + 1 / 40) * (Real.exp (1 / 8) * operatorNorm (Y - Y'))) +
        (1 + 1 / 40) * ((Real.exp (1 / 8) - 1) * operatorNorm (Y - Y')) +
        1 / 40 * operatorNorm (Y - Y') := by ring
    rw [this]
    exact add_le_add (add_le_add t4 t2) t3
  refine t5.trans (mul_le_mul_of_nonneg_right ?_ hδ0)
  norm_num at hE ⊢
  linarith
private theorem add_inv_smul_sum (hn : 0 < n) (D : ComplexMatrix2) (f : Fin n → ComplexMatrix2) :
    D + (n : ℂ)⁻¹ • ∑ i, f i = (n : ℂ)⁻¹ • ∑ i, (D + f i) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [Finset.sum_add_distrib, smul_add]
  congr 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hn', one_smul]
private theorem operatorNorm_inv_smul_sum_le (hn : 0 < n) {c : ℝ} (f : Fin n → ComplexMatrix2)
    (h : ∀ i, operatorNorm (f i) ≤ c) : operatorNorm ((n : ℂ)⁻¹ • ∑ i, f i) ≤ c := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h1 : operatorNorm (∑ i, f i) ≤ n * c := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => h i).trans ?_
    simp
  have h2 : ‖(n : ℂ)⁻¹‖ = (n : ℝ)⁻¹ := by simp
  change ‖(n : ℂ)⁻¹ • ∑ i, f i‖ ≤ c
  rw [norm_smul, h2]
  calc (n : ℝ)⁻¹ * ‖∑ i, f i‖ ≤ (n : ℝ)⁻¹ * (n * c) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hn'.le)
    _ = c := by field_simp
private theorem translatedLogAverage_lipschitz (hX : ExpLogEstimates)
    (hN : Numerics.ExpLogNumericBounds) (hn : 0 < n) {T : Fin n → ComplexMatrix2}
    (hT : ∀ i, operatorNorm (T i - 1) ≤ 1 / 40) {Y Y' : ComplexMatrix2}
    (hY : Y ∈ closedBallEighth) (hY' : Y' ∈ closedBallEighth) :
    operatorNorm (translatedLogAverage T Y - translatedLogAverage T Y') ≤
      2 / 5 * operatorNorm (Y - Y') := by
  have e : translatedLogAverage T Y - translatedLogAverage T Y' = (n : ℂ)⁻¹ • ∑ i,
      ((Y - Y') + (logSeries (T i * matExp (-Y)) - logSeries (T i * matExp (-Y')))) := by
    rw [← add_inv_smul_sum hn, Finset.sum_sub_distrib, smul_sub]
    simp only [translatedLogAverage]
    abel
  rw [e]
  exact operatorNorm_inv_smul_sum_le hn _ fun i => term_sub_le hX hN (hT i) hY hY'
private theorem translatedLogAverage_zero_le (hX : ExpLogEstimates) (hn : 0 < n)
    {T : Fin n → ComplexMatrix2} {d : ℝ} (hd : d ≤ 1 / 40)
    (hT : ∀ i, operatorNorm (T i - 1) ≤ d) :
    operatorNorm (translatedLogAverage T 0) ≤ d / (1 - d) := by
  have e : translatedLogAverage T 0 = (n : ℂ)⁻¹ • ∑ i, logSeries (T i) := by
    simp [translatedLogAverage, NormedSpace.exp_zero]
  rw [e]
  refine operatorNorm_inv_smul_sum_le hn _ fun i => ?_
  obtain ⟨-, -, -, c4, -⟩ := hX
  have hE : operatorNorm (T i - 1) < 1 := by have := hT i; linarith
  obtain ⟨h1, h2, -⟩ := c4 (T i - 1) hE
  rw [add_sub_cancel] at h1
  refine (h1.trans h2).trans ?_
  have a := hT i
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith
private theorem mem_closedBallEighth_iff {Y : ComplexMatrix2} :
    Y ∈ closedBallEighth ↔ operatorNorm Y ≤ 1 / 8 := Iff.rfl
private theorem translatedLogAverage_mapsTo (hX : ExpLogEstimates)
    (hN : Numerics.ExpLogNumericBounds) (hn : 0 < n) {T : Fin n → ComplexMatrix2} {d : ℝ}
    (hd : d ≤ 1 / 40) (hT : ∀ i, operatorNorm (T i - 1) ≤ d) :
    MapsTo (translatedLogAverage T) closedBallEighth closedBallEighth := by
  intro Y hY
  have hT' : ∀ i, operatorNorm (T i - 1) ≤ 1 / 40 := fun i => (hT i).trans hd
  have h0 : (0 : ComplexMatrix2) ∈ closedBallEighth := by simp [mem_closedBallEighth_iff]
  have h1 := translatedLogAverage_lipschitz hX hN hn hT' hY h0
  have h2 := translatedLogAverage_zero_le hX hn hd hT
  have h3 : d / (1 - d) ≤ 1 / 39 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h4 : operatorNorm (translatedLogAverage T Y) ≤
      operatorNorm (translatedLogAverage T Y - translatedLogAverage T 0) +
      operatorNorm (translatedLogAverage T 0) := by
    have := norm_add_le (translatedLogAverage T Y - translatedLogAverage T 0)
      (translatedLogAverage T 0)
    rwa [sub_add_cancel] at this
  rw [sub_zero] at h1
  have h5 : operatorNorm Y ≤ 1 / 8 := hY
  rw [mem_closedBallEighth_iff]
  linarith
private theorem exists_fixedPoint_of_contracting {Φ : ComplexMatrix2 → ComplexMatrix2}
    {S : Set ComplexMatrix2} (hS : IsClosed S)
    (h0 : (0 : ComplexMatrix2) ∈ S) (hmap : MapsTo Φ S S)
    (hlip : ∀ Y ∈ S, ∀ Y' ∈ S, operatorNorm (Φ Y - Φ Y') ≤ 2 / 5 * operatorNorm (Y - Y')) :
    ∃ Y ∈ S, Φ Y = Y := by
  have : CompleteSpace S := hS.completeSpace_coe
  have : Nonempty S := ⟨⟨0, h0⟩⟩
  let f : S → S := fun y => ⟨Φ y, hmap y.2⟩
  have hf : ContractingWith (2 / 5) f := by
    refine ⟨by norm_num [← NNReal.coe_lt_coe], LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    simpa using hlip x x.2 y y.2
  have := hf.fixedPoint_isFixedPt
  exact ⟨(ContractingWith.fixedPoint f hf : S), Subtype.coe_prop _, congrArg Subtype.val this⟩
private theorem quotient_le_unitFamilyDiameter (V : Fin n → ComplexMatrix2) (i i' : Fin n) :
    operatorNorm (V i * (V i')⁻¹ - 1) ≤ unitFamilyDiameter V :=
  le_ciSup (f := fun p : Fin n × Fin n => operatorNorm (V p.1 * (V p.2)⁻¹ - 1))
    (Set.finite_range _).bddAbove (i, i')
private theorem leadMember_eq (V : Fin n → ComplexMatrix2) (hn : 0 < n) :
    leadMember V = V ⟨0, hn⟩ := dif_pos hn
private theorem unitFamilyDiameter_nonneg {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V) :
    0 ≤ unitFamilyDiameter V :=
  (norm_nonneg _).trans (quotient_le_unitFamilyDiameter V ⟨0, hV.1⟩ ⟨0, hV.1⟩)
private theorem isUnit_leadMember {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V) :
    IsUnit (leadMember V) := by
  rw [leadMember_eq V hV.1]
  exact hV.2 _
private theorem quotient_leadMember_le {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V)
    (i : Fin n) : operatorNorm (V i * (leadMember V)⁻¹ - 1) ≤ unitFamilyDiameter V := by
  rw [leadMember_eq V hV.1]
  exact quotient_le_unitFamilyDiameter V _ _
private theorem meanMap_eq (V : Fin n → ComplexMatrix2) :
    meanMap V = translatedLogAverage fun i => V i * (leadMember V)⁻¹ := rfl
private theorem meanMap_lipschitz (hX : ExpLogEstimates)
    (hN : Numerics.ExpLogNumericBounds) {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V)
    (hd : unitFamilyDiameter V ≤ 1 / 40) {Y Y' : ComplexMatrix2} (hY : Y ∈ closedBallEighth)
    (hY' : Y' ∈ closedBallEighth) :
    operatorNorm (meanMap V Y - meanMap V Y') ≤ 2 / 5 * operatorNorm (Y - Y') := by
  rw [meanMap_eq]
  exact translatedLogAverage_lipschitz hX hN hV.1
    (fun i => (quotient_leadMember_le hV i).trans hd) hY hY'
private theorem meanMap_mapsTo (hX : ExpLogEstimates)
    (hN : Numerics.ExpLogNumericBounds) {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V)
    (hd : unitFamilyDiameter V ≤ 1 / 40) :
    MapsTo (meanMap V) closedBallEighth closedBallEighth := by
  rw [meanMap_eq]
  exact translatedLogAverage_mapsTo hX hN hV.1 hd (quotient_leadMember_le hV)
private theorem isClosed_closedBallEighth : IsClosed closedBallEighth :=
  isClosed_le continuous_norm continuous_const
private theorem zero_mem_closedBallEighth : (0 : ComplexMatrix2) ∈ closedBallEighth := by
  simp [mem_closedBallEighth_iff]
private theorem meanFixedPt_unique (hX : ExpLogEstimates)
    (hN : Numerics.ExpLogNumericBounds) {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V)
    (hd : unitFamilyDiameter V ≤ 1 / 40) {Y Y' : ComplexMatrix2} (hY : Y ∈ closedBallEighth)
    (hY' : Y' ∈ closedBallEighth) (h : meanMap V Y = Y) (h' : meanMap V Y' = Y') : Y = Y' := by
  have := meanMap_lipschitz hX hN hV hd hY hY'
  rw [h, h'] at this
  have h0 : operatorNorm (Y - Y') ≤ 0 := by
    have : 0 ≤ operatorNorm (Y - Y') := norm_nonneg _
    linarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
private theorem meanFixedPt_mem_of_invariant (hX : ExpLogEstimates)
    (hN : Numerics.ExpLogNumericBounds) {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V)
    (hd : unitFamilyDiameter V ≤ 1 / 40) {S : Set ComplexMatrix2} (hS : IsClosed S)
    (h0 : (0 : ComplexMatrix2) ∈ S) (hSb : S ⊆ closedBallEighth) (hmap : MapsTo (meanMap V) S S) :
    meanFixedPt V ∈ S ∧ meanMap V (meanFixedPt V) = meanFixedPt V := by
  obtain ⟨Y, hY, hfix⟩ := exists_fixedPoint_of_contracting hS h0 hmap
    fun Y hY Y' hY' => meanMap_lipschitz hX hN hV hd (hSb hY) (hSb hY')
  have spec : meanFixedPt V ∈ closedBallEighth ∧ meanMap V (meanFixedPt V) = meanFixedPt V :=
    Classical.epsilon_spec (p := fun Y => Y ∈ closedBallEighth ∧ meanMap V Y = Y)
      ⟨Y, hSb hY, hfix⟩
  have e := meanFixedPt_unique hX hN hV hd (hSb hY) spec.1 hfix spec.2
  exact ⟨e ▸ hY, spec.2⟩
private theorem meanFixedPt_spec (hX : ExpLogEstimates)
    (hN : Numerics.ExpLogNumericBounds) {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V)
    (hd : unitFamilyDiameter V ≤ 1 / 40) :
    meanFixedPt V ∈ closedBallEighth ∧ meanMap V (meanFixedPt V) = meanFixedPt V :=
  meanFixedPt_mem_of_invariant hX hN hV hd isClosed_closedBallEighth zero_mem_closedBallEighth
    subset_rfl (meanMap_mapsTo hX hN hV hd)
private theorem meanFixedPt_le (hX : ExpLogEstimates)
    (hN : Numerics.ExpLogNumericBounds) {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V)
    (hd : unitFamilyDiameter V ≤ 1 / 40) :
    operatorNorm (meanFixedPt V) ≤ 2 * unitFamilyDiameter V := by
  obtain ⟨hb, hfix⟩ := meanFixedPt_spec hX hN hV hd
  have h1 := meanMap_lipschitz hX hN hV hd hb zero_mem_closedBallEighth
  rw [hfix, sub_zero] at h1
  have h2 : operatorNorm (meanMap V 0) ≤
      unitFamilyDiameter V / (1 - unitFamilyDiameter V) := by
    rw [meanMap_eq]
    exact translatedLogAverage_zero_le hX hV.1 hd (quotient_leadMember_le hV)
  have h3 : operatorNorm (meanFixedPt V) ≤
      operatorNorm (meanFixedPt V - meanMap V 0) + operatorNorm (meanMap V 0) := by
    have := norm_add_le (meanFixedPt V - meanMap V 0) (meanMap V 0)
    rwa [sub_add_cancel] at this
  have hd0 := unitFamilyDiameter_nonneg hV
  have h4 : unitFamilyDiameter V / (1 - unitFamilyDiameter V) ≤
      40 / 39 * unitFamilyDiameter V := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith
private theorem matExp_inv (hE : NormExpLogBasics) (Y : ComplexMatrix2) :
    (matExp Y)⁻¹ = matExp (-Y) := (hE.2.1 Y).2.2.2.2.1
private theorem isUnit_matExp (hE : NormExpLogBasics) (Y : ComplexMatrix2) :
    IsUnit (matExp Y) :=
  (hE.2.1 Y).2.2.2.1
private theorem mul_inv_matExp_mul (hE : NormExpLogBasics) (A W Y : ComplexMatrix2) :
    A * (matExp Y * W)⁻¹ = A * W⁻¹ * matExp (-Y) := by
  rw [Matrix.mul_inv_rev, matExp_inv hE, mul_assoc]
private theorem sum_logSeries_quotient_average (hE : NormExpLogBasics)
    (hX : ExpLogEstimates) (hN : Numerics.ExpLogNumericBounds)
    {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V) (hd : unitFamilyDiameter V ≤ 1 / 40) :
    ∑ i, logSeries (V i * (average V)⁻¹) = 0 := by
  have hfix := (meanFixedPt_spec hX hN hV hd).2
  have hn' : (n : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr (by have := hV.1; omega))
  have h : (n : ℂ)⁻¹ • ∑ i, logSeries (V i * (leadMember V)⁻¹ * matExp (-meanFixedPt V)) = 0 :=
    add_eq_left.mp hfix
  simp only [average, mul_inv_matExp_mul hE]
  exact (smul_eq_zero.mp h).resolve_left hn'
private theorem isUnit_average (hE : NormExpLogBasics) {V : Fin n → ComplexMatrix2}
    (hV : IsUnitFamily V) : IsUnit (average V) :=
  (isUnit_matExp hE _).mul (isUnit_leadMember hV)
private theorem one_add_mul_exp_two_mul_le (hN : Numerics.ExpLogNumericBounds) {d : ℝ}
    (h0 : 0 ≤ d) (h1 : d ≤ 1 / 40) :
    (1 + d) * Real.exp (2 * d) - 1 ≤ 4 * d := by
  have a1 : 1 + d ≤ Real.exp d := by linarith [Real.add_one_le_exp d]
  have a2 : (1 + d) * Real.exp (2 * d) ≤ Real.exp (3 * d) := by
    have : Real.exp (3 * d) = Real.exp d * Real.exp (2 * d) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right a1 (Real.exp_pos _).le
  have a3 : Real.exp (3 * d) ≤ 1.078 :=
    (Real.exp_le_exp.mpr (by linarith)).trans hN.2.2.2.1.le
  have a4 : (1 - 3 * d) * Real.exp (3 * d) ≤ 1 := by
    have b := Real.add_one_le_exp (-(3 * d))
    have c : Real.exp (-(3 * d)) * Real.exp (3 * d) = 1 := by
      rw [← Real.exp_add]; simp
    have e := mul_le_mul_of_nonneg_right b (Real.exp_pos (3 * d)).le
    rw [c] at e
    linarith
  nlinarith
private theorem quotient_average_le (hE : NormExpLogBasics)
    (hX : ExpLogEstimates) (hN : Numerics.ExpLogNumericBounds)
    {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V) (hd : unitFamilyDiameter V ≤ 1 / 40)
    (i : Fin n) :
    operatorNorm (V i * (average V)⁻¹ - 1) ≤ 4 * unitFamilyDiameter V := by
  have h1 := operatorNorm_mul_matExp_neg_sub_one_le hX (quotient_leadMember_le hV i)
    (meanFixedPt_le hX hN hV hd)
  have e : V i * (average V)⁻¹ = V i * (leadMember V)⁻¹ * matExp (-meanFixedPt V) :=
    mul_inv_matExp_mul hE _ _ _
  rw [e]
  exact h1.trans (one_add_mul_exp_two_mul_le hN (unitFamilyDiameter_nonneg hV) hd)
private theorem eq_average_of_near_leadMember (hE : NormExpLogBasics)
    (hX : ExpLogEstimates) (hN : Numerics.ExpLogNumericBounds)
    {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V) (hd : unitFamilyDiameter V ≤ 1 / 40)
    {V' : ComplexMatrix2} (hu : IsUnit V') (hs : ∑ i, logSeries (V i * V'⁻¹) = 0)
    (h1 : operatorNorm (leadMember V * V'⁻¹ - 1) ≤ 1 / 10) : V' = average V := by
  have hl98 : Real.log (9 / 8) < 0.1178 := hN.2.2.2.2.2.2.1
  have hX' := hX
  obtain ⟨-, -, -, c4, -⟩ := hX'
  have hfu := isUnit_leadMember hV
  have hud : IsUnit V'.det := (Matrix.isUnit_iff_isUnit_det V').mp hu
  have hfud : IsUnit (leadMember V).det := (Matrix.isUnit_iff_isUnit_det _).mp hfu
  have hlt : operatorNorm (leadMember V * V'⁻¹ - 1) < 1 := by linarith
  obtain ⟨-, -, -, hinv, -⟩ := c4 _ hlt
  rw [add_sub_cancel, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hud] at hinv
  have hX9 : operatorNorm (V' * (leadMember V)⁻¹ - 1) ≤ 1 / 9 := by
    refine hinv.trans ?_
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hlt2 : operatorNorm (V' * (leadMember V)⁻¹ - 1) < 1 := by linarith
  obtain ⟨hl1, -, -, -, hexp⟩ := c4 _ hlt2
  rw [add_sub_cancel] at hl1 hexp
  have hball : logSeries (V' * (leadMember V)⁻¹) ∈ closedBallEighth := by
    rw [mem_closedBallEighth_iff]
    have a : Real.log (8 / 9) ≤ Real.log (1 - operatorNorm (V' * (leadMember V)⁻¹ - 1)) :=
      Real.log_le_log (by norm_num) (by linarith)
    have b : Real.log (8 / 9) = -Real.log (9 / 8) := by
      rw [← Real.log_inv]; norm_num
    linarith
  have hV' : V' = matExp (logSeries (V' * (leadMember V)⁻¹)) * leadMember V := by
    rw [hexp, mul_assoc, Matrix.nonsing_inv_mul _ hfud, mul_one]
  have hfix : meanMap V (logSeries (V' * (leadMember V)⁻¹)) =
      logSeries (V' * (leadMember V)⁻¹) := by
    have e : ∀ i, V i * (leadMember V)⁻¹ * matExp (-logSeries (V' * (leadMember V)⁻¹)) =
        V i * V'⁻¹ := by
      intro i
      rw [← mul_inv_matExp_mul hE, ← hV']
    simp only [meanMap, e, hs, smul_zero, add_zero]
  have spec := meanFixedPt_spec hX hN hV hd
  have := meanFixedPt_unique hX hN hV hd hball spec.1 hfix spec.2
  rw [average, ← this]
  exact hV'
private theorem unitFamilyDiameter_comp (V : Fin n → ComplexMatrix2) (π : Equiv.Perm (Fin n)) :
    unitFamilyDiameter (V ∘ π) = unitFamilyDiameter V :=
  (Equiv.prodCongr π π).iSup_comp
    (g := fun p : Fin n × Fin n => operatorNorm (V p.1 * (V p.2)⁻¹ - 1))
private theorem isUnitFamily_comp {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V)
    (π : Equiv.Perm (Fin n)) : IsUnitFamily (V ∘ π) :=
  ⟨hV.1, fun _ => hV.2 _⟩
private theorem sum_logSeries_comp (V : Fin n → ComplexMatrix2) (π : Equiv.Perm (Fin n))
    (W : ComplexMatrix2) :
    ∑ i, logSeries ((V ∘ π) i * W) = ∑ i, logSeries (V i * W) :=
  Equiv.sum_comp π fun i => logSeries (V i * W)
private theorem eq_average_of_near_member (hE : NormExpLogBasics)
    (hX : ExpLogEstimates) (hN : Numerics.ExpLogNumericBounds)
    {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V) (hd : unitFamilyDiameter V ≤ 1 / 40)
    {V' : ComplexMatrix2} (hu : IsUnit V') (hs : ∑ i, logSeries (V i * V'⁻¹) = 0) {k : Fin n}
    (hk : operatorNorm (V k * V'⁻¹ - 1) ≤ 1 / 10) : V' = average V := by
  let z : Fin n := ⟨0, hV.1⟩
  let π : Equiv.Perm (Fin n) := Equiv.swap z k
  have hW := isUnitFamily_comp hV π
  have hdW : unitFamilyDiameter (V ∘ π) ≤ 1 / 40 := by rw [unitFamilyDiameter_comp]; exact hd
  have hfirst : leadMember (V ∘ π) = V k := by
    rw [leadMember_eq _ hV.1]
    exact congrArg V (Equiv.swap_apply_left z k)
  have e1 : V' = average (V ∘ π) :=
    eq_average_of_near_leadMember hE hX hN hW hdW hu (by rw [sum_logSeries_comp]; exact hs)
      (by rw [hfirst]; exact hk)
  have hsum := sum_logSeries_quotient_average hE hX hN hW hdW
  have hbd := quotient_average_le hE hX hN hW hdW (π.symm z)
  rw [unitFamilyDiameter_comp] at hbd
  have hz : (V ∘ π) (π.symm z) = V z := by simp
  rw [hz] at hbd
  rw [e1]
  refine eq_average_of_near_leadMember hE hX hN hV hd (isUnit_average hE hW) ?_ ?_
  · rw [← sum_logSeries_comp V π]; exact hsum
  · rw [leadMember_eq V hV.1]
    have : 4 * unitFamilyDiameter V ≤ 1 / 10 := by linarith
    exact hbd.trans this
private theorem average_comp (hE : NormExpLogBasics)
    (hX : ExpLogEstimates) (hN : Numerics.ExpLogNumericBounds)
    {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V) (hd : unitFamilyDiameter V ≤ 1 / 40)
    (π : Equiv.Perm (Fin n)) : average (V ∘ π) = average V := by
  have hW := isUnitFamily_comp hV π
  have hdW : unitFamilyDiameter (V ∘ π) ≤ 1 / 40 := by rw [unitFamilyDiameter_comp]; exact hd
  have hsum := sum_logSeries_quotient_average hE hX hN hW hdW
  rw [sum_logSeries_comp] at hsum
  have hbd := quotient_average_le hE hX hN hW hdW ⟨0, hV.1⟩
  rw [unitFamilyDiameter_comp] at hbd
  have : 4 * unitFamilyDiameter V ≤ 1 / 10 := by linarith
  exact eq_average_of_near_member hE hX hN hV hd (isUnit_average hE hW) hsum
    (k := π ⟨0, hV.1⟩) (hbd.trans this)
private theorem average_const (hX : ExpLogEstimates) (hN : Numerics.ExpLogNumericBounds)
    (hn : 1 ≤ n) {W : ComplexMatrix2} (hW : IsUnit W) :
    average (fun _ : Fin n => W) = W := by
  have hWd : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det W).mp hW
  have hone : W * W⁻¹ = 1 := Matrix.mul_nonsing_inv W hWd
  have hV : IsUnitFamily (fun _ : Fin n => W) := ⟨hn, fun _ => hW⟩
  have : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  have hd : unitFamilyDiameter (fun _ : Fin n => W) ≤ 1 / 40 := by
    refine ciSup_le fun p => ?_
    simp [hone]
  obtain ⟨hb, hfix⟩ := meanFixedPt_spec hX hN hV hd
  have hfirst : leadMember (fun _ : Fin n => W) = W := leadMember_eq _ hn
  have hlog : logSeries (matExp (-meanFixedPt fun _ : Fin n => W)) =
      -meanFixedPt fun _ : Fin n => W := by
    obtain ⟨-, -, -, -, c5, -⟩ := hX
    refine (c5 _ ?_).2
    have h8 : (1 / 8 : ℝ) < Real.log 2 := hN.2.2.2.2.2.2.2.1
    rw [operatorNorm_neg]
    exact lt_of_le_of_lt hb h8
  have hzero : meanFixedPt (fun _ : Fin n => W) = 0 := by
    rw [← hfix, meanMap, add_inv_smul_sum hn]
    simp [hfirst, hone, hlog]
  rw [average, hzero, hfirst]
  simp [NormedSpace.exp_zero]
private theorem det_matExp_of_fullTrace_eq_zero (hX : ExpLogEstimates) {Y : ComplexMatrix2}
    (hY : fullTrace Y = 0) : (matExp Y).det = 1 := by
  obtain ⟨-, -, -, -, -, c6, -⟩ := hX
  rw [c6, hY, Complex.exp_zero]
private theorem meanFixedPt_traceless (hX : ExpLogEstimates)
    (hN : Numerics.ExpLogNumericBounds) {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V)
    (hd : unitFamilyDiameter V ≤ 1 / 40) (hG : ∀ i, V i ∈ unitDeterminant) :
    meanFixedPt V ∈ traceless ∧ average V ∈ unitDeterminant := by
  have hfirst : (leadMember V).det = 1 := by
    rw [leadMember_eq V hV.1]
    exact hG _
  have hclosed : IsClosed (closedBallEighth ∩ (traceless : Set ComplexMatrix2)) :=
    isClosed_closedBallEighth.inter
      (isClosed_eq (Continuous.matrix_trace continuous_id) continuous_const)
  have hmem : meanFixedPt V ∈ closedBallEighth ∩ (traceless : Set ComplexMatrix2) := by
    refine (meanFixedPt_mem_of_invariant hX hN hV hd hclosed
      ⟨zero_mem_closedBallEighth, traceless.zero_mem⟩ inter_subset_left ?_).1
    rintro Y ⟨hb, hY⟩
    refine ⟨meanMap_mapsTo hX hN hV hd hb,
      traceless.add_mem hY (traceless.smul_mem _ (traceless.sum_mem ?_))⟩
    intro i _
    have hneg : fullTrace (-Y) = 0 := by
      have : fullTrace Y = 0 := hY
      simp [fullTrace, Matrix.trace_neg] at this ⊢
      exact this
    have hdet : (V i * (leadMember V)⁻¹ * matExp (-Y)).det = 1 := by
      have h1 : (V i).det = 1 := hG i
      rw [Matrix.det_mul, Matrix.det_mul, h1, det_matExp_of_fullTrace_eq_zero hX hneg,
        Matrix.det_nonsing_inv, hfirst]
      simp
    have hnear : operatorNorm (V i * (leadMember V)⁻¹ * matExp (-Y) - 1) ≤ 9 / 10 := by
      have h1 := operatorNorm_mul_matExp_neg_sub_one_le hX
        ((quotient_leadMember_le hV i).trans hd) hb
      have h2 : Real.exp (1 / 8) < 1.1332 := hN.2.2.2.2.1
      refine h1.trans ?_
      norm_num at h2 ⊢
      linarith
    obtain ⟨-, -, -, -, -, -, c7, -⟩ := hX
    exact (c7 _ hdet hnear).2
  refine ⟨hmem.2, ?_⟩
  change (matExp (meanFixedPt V) * leadMember V).det = 1
  rw [Matrix.det_mul, det_matExp_of_fullTrace_eq_zero hX hmem.2, hfirst, one_mul]
private theorem isClosed_I_smul_hermitianTraceless :
    IsClosed {Y : ComplexMatrix2 | ∃ A ∈ hermitianTraceless, Y = Complex.I • A} := by
  have e : {Y : ComplexMatrix2 | ∃ A ∈ hermitianTraceless, Y = Complex.I • A} =
      {Y : ComplexMatrix2 | Y.conjTranspose = -Y} ∩ {Y : ComplexMatrix2 | Matrix.trace Y = 0} := by
    ext Y
    constructor
    · rintro ⟨A, ⟨hA, tA⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · change (Complex.I • A).conjTranspose = -(Complex.I • A)
        rw [Matrix.conjTranspose_smul, ← hA]
        simp
      · change Matrix.trace (Complex.I • A) = 0
        rw [Matrix.trace_smul]
        have : Matrix.trace A = 0 := tA
        rw [this, smul_zero]
    · rintro ⟨hY, tY⟩
      have hY' : Y.conjTranspose = -Y := hY
      have tY' : Matrix.trace Y = 0 := tY
      refine ⟨(-Complex.I) • Y, ⟨?_, ?_⟩, ?_⟩
      · rw [Matrix.conjTranspose_smul, hY']
        simp
      · change Matrix.trace ((-Complex.I) • Y) = 0
        rw [Matrix.trace_smul, tY', smul_zero]
      · rw [smul_smul]
        simp
  rw [e]
  exact (isClosed_eq (Continuous.matrix_conjTranspose continuous_id) continuous_id.neg).inter
    (isClosed_eq (Continuous.matrix_trace continuous_id) continuous_const)
private theorem inv_mem_specialUnitary {A : ComplexMatrix2}
    (hA : A ∈ (specialUnitary : Set ComplexMatrix2)) :
    A⁻¹ ∈ (specialUnitary : Set ComplexMatrix2) := by apply _root_.YangMills.SharedProofs.p33390 <;> assumption
private theorem isUnit_of_mem_specialUnitary {A : ComplexMatrix2}
    (hA : A ∈ (specialUnitary : Set ComplexMatrix2)) : IsUnit A := by apply _root_.YangMills.SharedProofs.p13429 <;> assumption
private theorem meanFixedPt_I_smul_hermitianTraceless (hX : ExpLogEstimates)
    (hI : UnitaryLogarithmProperties) (hN : Numerics.ExpLogNumericBounds)
    {V : Fin n → ComplexMatrix2}
    (hV : IsUnitFamily V) (hd : unitFamilyDiameter V ≤ 1 / 40)
    (hG : ∀ i, V i ∈ specialUnitary) :
    (∃ A ∈ hermitianTraceless, meanFixedPt V = Complex.I • A) ∧ average V ∈ specialUnitary := by
  have hfirst : leadMember V ∈ (specialUnitary : Set ComplexMatrix2) := by
    rw [leadMember_eq V hV.1]
    exact hG _
  have hclosed : IsClosed (closedBallEighth ∩
      {Y : ComplexMatrix2 | ∃ A ∈ hermitianTraceless, Y = Complex.I • A}) :=
    isClosed_closedBallEighth.inter isClosed_I_smul_hermitianTraceless
  have hmem : meanFixedPt V ∈ closedBallEighth ∩
      {Y : ComplexMatrix2 | ∃ A ∈ hermitianTraceless, Y = Complex.I • A} := by
    refine (meanFixedPt_mem_of_invariant hX hN hV hd hclosed
      ⟨zero_mem_closedBallEighth, 0, hermitianTraceless.zero_mem, (smul_zero _).symm⟩
      inter_subset_left ?_).1
    rintro Y ⟨hb, A, hA, rfl⟩
    refine ⟨meanMap_mapsTo hX hN hV hd hb, ?_⟩
    have hterm : ∀ i, ∃ B ∈ hermitianTraceless,
        logSeries (V i * (leadMember V)⁻¹ * matExp (-(Complex.I • A))) = Complex.I • B := by
      intro i
      have hexp : matExp (-(Complex.I • A)) ∈ (specialUnitary : Set ComplexMatrix2) := by
        have := (hI.1 (-A) (hermitianTraceless.neg_mem hA)).2.2.2
        rwa [smul_neg] at this
      have hM : V i * (leadMember V)⁻¹ * matExp (-(Complex.I • A)) ∈ specialUnitary :=
        specialUnitary.mul_mem (specialUnitary.mul_mem (hG i) (inv_mem_specialUnitary hfirst)) hexp
      have hnear :
          operatorNorm (V i * (leadMember V)⁻¹ * matExp (-(Complex.I • A)) - 1) < 1 := by
        have h1 := operatorNorm_mul_matExp_neg_sub_one_le hX
          ((quotient_leadMember_le hV i).trans hd) hb
        have h2 : Real.exp (1 / 8) < 1.1332 := hN.2.2.2.2.1
        refine lt_of_le_of_lt h1 ?_
        norm_num at h2 ⊢
        linarith
      obtain ⟨-, -, -, -, -, -, -, c8, -⟩ := hX
      obtain ⟨H, -, -, -, -, -, h⟩ :=
        c8 _ (Matrix.specialUnitaryGroup_le_unitaryGroup hM) hnear
      exact (h (Matrix.mem_specialUnitaryGroup_iff.mp hM).2).2.2.1
    choose B hB hlog using hterm
    refine ⟨A + (n : ℝ)⁻¹ • ∑ i, B i, hermitianTraceless.add_mem hA
      (hermitianTraceless.smul_mem _ (hermitianTraceless.sum_mem fun i _ => hB i)), ?_⟩
    simp only [meanMap, hlog]
    rw [smul_add, ← Finset.smul_sum, smul_comm (n : ℂ)⁻¹ Complex.I]
    congr 2
    ext i j
    simp
  obtain ⟨-, A, hA, hY⟩ := hmem
  refine ⟨⟨A, hA, hY⟩, ?_⟩
  have hexp : matExp (meanFixedPt V) ∈ specialUnitary := by
    rw [hY]
    exact (hI.1 A hA).2.2.2
  exact specialUnitary.mul_mem hexp hfirst
private theorem eq_average_of_specialUnitary (hE : NormExpLogBasics)
    (hX : ExpLogEstimates) (hN : Numerics.ExpLogNumericBounds)
    {V : Fin n → ComplexMatrix2} (hV : IsUnitFamily V) (hd : unitFamilyDiameter V ≤ 1 / 40)
    (hG : ∀ i, V i ∈ specialUnitary) {V' : ComplexMatrix2} (hV' : V' ∈ specialUnitary)
    (hb : ∀ i, operatorNorm (V i * V'⁻¹ - 1) < 1) (hs : ∑ i, logSeries (V i * V'⁻¹) = 0) :
    V' = average V := by
  let z : Fin n := ⟨0, hV.1⟩
  have hU : ∀ i, V i * V'⁻¹ ∈ specialUnitary :=
    fun i => specialUnitary.mul_mem (hG i) (inv_mem_specialUnitary hV')
  have hzd : IsUnit (V z).det := (Matrix.isUnit_iff_isUnit_det _).mp (hV.2 z)
  have hdiff : ∀ i, operatorNorm (V i * V'⁻¹ - V z * V'⁻¹) ≤ unitFamilyDiameter V := by
    intro i
    have e : V i * V'⁻¹ - V z * V'⁻¹ = 1 * (V i * (V z)⁻¹ - 1) * (V z * V'⁻¹) := by
      rw [one_mul, sub_mul, one_mul, mul_assoc, ← mul_assoc (V z)⁻¹,
        Matrix.nonsing_inv_mul _ hzd, one_mul]
    rw [e, hE.1.2.2.2.1 _ 1 _ (Submonoid.one_mem _)
      (Matrix.specialUnitaryGroup_le_unitaryGroup (hU z))]
    exact quotient_le_unitFamilyDiameter V i z
  have hlip : ∀ i, operatorNorm (logSeries (V z * V'⁻¹) + -logSeries (V i * V'⁻¹)) ≤
      2 * unitFamilyDiameter V := by
    intro i
    obtain ⟨-, -, -, -, -, -, -, -, -, c10⟩ := hX
    have h := c10 _ (Matrix.specialUnitaryGroup_le_unitaryGroup (hU i)) _
      (Matrix.specialUnitaryGroup_le_unitaryGroup (hU z)) (hb i) (hb z)
    have e : operatorNorm (logSeries (V z * V'⁻¹) + -logSeries (V i * V'⁻¹)) =
        operatorNorm (logSeries (V i * V'⁻¹) - logSeries (V z * V'⁻¹)) := by
      rw [← sub_eq_add_neg]
      exact norm_sub_rev _ _
    have := hdiff i
    rw [e]
    linarith
  have hmean : logSeries (V z * V'⁻¹) =
      (n : ℂ)⁻¹ • ∑ i, (logSeries (V z * V'⁻¹) + -logSeries (V i * V'⁻¹)) := by
    rw [← add_inv_smul_sum hV.1, Finset.sum_neg_distrib, hs]
    simp
  have hL : operatorNorm (logSeries (V z * V'⁻¹)) ≤ 2 * unitFamilyDiameter V := by
    rw [hmean]
    exact operatorNorm_inv_smul_sum_le hV.1 _ hlip
  have h20 : operatorNorm (logSeries (V z * V'⁻¹)) ≤ 1 / 20 := by linarith
  have h51 : Real.exp (1 / 20) < 1.0513 := hN.2.2.1
  have hX' := hX
  obtain ⟨c1, -, -, c4, -⟩ := hX'
  have hexp := (c4 _ (by simpa using hb z)).2.2.2.2
  rw [add_sub_cancel] at hexp
  have hnear : operatorNorm (V z * V'⁻¹ - 1) ≤ 1 / 10 := by
    have h := (c1 (logSeries (V z * V'⁻¹))).2
    rw [hexp] at h
    have : Real.exp (operatorNorm (logSeries (V z * V'⁻¹))) ≤ Real.exp (1 / 20) :=
      Real.exp_le_exp.mpr h20
    norm_num at h51 ⊢
    linarith
  exact eq_average_of_near_member hE hX hN hV hd (isUnit_of_mem_specialUnitary hV') hs hnear
private theorem isUnitFamily_of_specialUnitary {V : Fin n → ComplexMatrix2}
    (hV : IsSpecialUnitaryFamily V) : IsUnitFamily V :=
  ⟨hV.1, fun i => isUnit_of_mem_specialUnitary (hV.2 i)⟩
private theorem logMeans_specialUnitary (hE : NormExpLogBasics)
    (hX : ExpLogEstimates) (hI : UnitaryLogarithmProperties)
    (hN : Numerics.ExpLogNumericBounds) {V : Fin n → ComplexMatrix2}
    (hV : IsSpecialUnitaryFamily V) (hd : unitFamilyDiameter V ≤ 1 / 40) :
    (∀ W : ComplexMatrix2, IsSpecialUnitaryLogMean V W ↔ W = average V) ∧
    ∀ ω ∈ Ioc (4 * unitFamilyDiameter V) 1, ∀ W : ComplexMatrix2,
      IsLogMeanOfRadius ω V W ↔ W = average V := by
  have hI' := isUnitFamily_of_specialUnitary hV
  have hd0 := unitFamilyDiameter_nonneg hI'
  have hmem := (meanFixedPt_I_smul_hermitianTraceless hX hI hN hI' hd hV.2).2
  have hbd := quotient_average_le hE hX hN hI' hd
  have hsum := sum_logSeries_quotient_average hE hX hN hI' hd
  refine ⟨fun W => ⟨?_, ?_⟩, fun ω hω W => ⟨?_, ?_⟩⟩
  · rintro ⟨-, hW, hb, hs⟩
    exact eq_average_of_specialUnitary hE hX hN hI' hd hV.2 hW hb hs
  · rintro rfl
    exact ⟨hV, hmem, fun i => lt_of_le_of_lt (hbd i) (by linarith), hsum⟩
  · rintro ⟨-, -, ⟨hW, hb, hs⟩, -⟩
    exact eq_average_of_specialUnitary hE hX hN hI' hd hV.2 hW hb hs
  · rintro rfl
    have hpos : 0 < ω := lt_of_le_of_lt (by linarith) hω.1
    exact ⟨⟨hpos, hω.2⟩, hV,
      ⟨hmem, fun i => lt_of_le_of_lt (hbd i) (by linarith [hω.1, hω.2]), hsum⟩,
      fun i => lt_of_le_of_lt (hbd i) hω.1⟩
private theorem differentiableOn_of_isHolomorphicIn
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) {N N' : ℕ}
    {O : Set (ComplexCoordinates N)} {f : ComplexCoordinates N → ComplexCoordinates N'}
    (h : ComplexCoordinates.IsHolomorphicIn O f) : DifferentiableOn ℂ f O := by apply _root_.YangMills.SharedProofs.p33060 <;> assumption
private theorem isHolomorphicIn_of_differentiableOn {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates N'} (hO : IsOpen O)
    (h : DifferentiableOn ℂ f O) : ComplexCoordinates.IsHolomorphicIn O f := by apply _root_.YangMills.SharedProofs.p1029 <;> assumption
section CoordinateCharts
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E'] {N N' : ℕ} {e : E ≃ ComplexCoordinates N} {e' : E' ≃ ComplexCoordinates N'}
private theorem image_eq_preimage_symm (c : E ≃L[ℂ] ComplexCoordinates N) (hc : ∀ x, c x = e x)
    (O : Set E) : e '' O = c.symm ⁻¹' O := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← hc]
    simpa using hx
  · intro hz
    exact ⟨c.symm z, hz, by rw [← hc]; simp⟩
private theorem equiv_symm_apply_eq (c : E ≃L[ℂ] ComplexCoordinates N) (hc : ∀ x, c x = e x)
    (z : ComplexCoordinates N) : e.symm z = c.symm z :=
  e.symm_apply_eq.mpr (by rw [← hc]; simp)
private theorem isHolomorphicVia_of_differentiableOn (c : E ≃L[ℂ] ComplexCoordinates N)
    (c' : E' ≃L[ℂ] ComplexCoordinates N') (hc : ∀ x, c x = e x) (hc' : ∀ x, c' x = e' x)
    {O : Set E} (hO : IsOpen O) {f : E → E'} (hf : DifferentiableOn ℂ f O) :
    ComplexCoordinates.IsHolomorphicVia e e' O f := by
  unfold ComplexCoordinates.IsHolomorphicVia
  rw [image_eq_preimage_symm c hc]
  have hfun : (e' ∘ f ∘ e.symm) = fun z => c' (f (c.symm z)) := by
    funext z
    simp [equiv_symm_apply_eq c hc, hc']
  rw [hfun]
  refine isHolomorphicIn_of_differentiableOn (hO.preimage c.symm.continuous) fun z hz => ?_
  have h1 : DifferentiableWithinAt ℂ (fun z => f (c.symm z)) (c.symm ⁻¹' O) z :=
    (hf _ hz).comp z c.symm.differentiableAt.differentiableWithinAt fun y hy => hy
  exact c'.differentiableAt.comp_differentiableWithinAt z h1
private theorem differentiableOn_of_isHolomorphicVia
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (c : E ≃L[ℂ] ComplexCoordinates N) (c' : E' ≃L[ℂ] ComplexCoordinates N')
    (hc : ∀ x, c x = e x) (hc' : ∀ x, c' x = e' x) {O : Set E} {f : E → E'}
    (h : ComplexCoordinates.IsHolomorphicVia e e' O f) : DifferentiableOn ℂ f O := by
  have hg := differentiableOn_of_isHolomorphicIn hH h
  have hf : ∀ x, c'.symm ((e' ∘ f ∘ e.symm) (c x)) = f x := by
    intro x
    simp [hc, ← hc']
  intro x hx
  have h1 : DifferentiableWithinAt ℂ (e' ∘ f ∘ e.symm) (e '' O) (c x) :=
    hg _ ⟨x, hx, (hc x).symm⟩
  have h2 : DifferentiableWithinAt ℂ (fun y => c'.symm ((e' ∘ f ∘ e.symm) (c y))) O x :=
    c'.symm.differentiableAt.comp_differentiableWithinAt x
      (h1.comp x c.differentiableAt.differentiableWithinAt fun y hy => ⟨y, hy, (hc y).symm⟩)
  exact h2.congr (fun y _ => (hf y).symm) (hf x).symm
end CoordinateCharts
private def entryLinearEquiv : ComplexMatrix2 ≃L[ℂ] ComplexCoordinates 4 :=
  LinearEquiv.toContinuousLinearEquiv
    { ComplexCoordinates.matrixEquiv with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
private def familyLinearEquiv (n : ℕ) : (Fin n → ComplexMatrix2) ≃L[ℂ]
    ComplexCoordinates (ComplexCoordinates.productDim
      fun _ : Fin n => ComplexCoordinates.Component.matrix) :=
  LinearEquiv.toContinuousLinearEquiv
    { familyEquiv n with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
private theorem differentiable_matExp
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    Differentiable ℂ matExp := by apply _root_.YangMills.SharedProofs.p11731 <;> assumption
private theorem differentiableOn_inv
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    DifferentiableOn ℂ (fun X : ComplexMatrix2 => X⁻¹) {X | IsUnit X} :=
  differentiableOn_of_isHolomorphicVia hH entryLinearEquiv entryLinearEquiv (fun _ => rfl)
    (fun _ => rfl) hH.2.2.2.1
private theorem differentiableOn_logSeries
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    DifferentiableOn ℂ logSeries logBall := by apply _root_.YangMills.SharedProofs.p36036 <;> assumption
private theorem isOpen_isUnit : IsOpen {X : ComplexMatrix2 | IsUnit X} := Units.isOpen
private theorem isOpen_logBall : IsOpen logBall :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
private theorem unitFamilyDiameter_lt_iff (hn : 1 ≤ n) (V : Fin n → ComplexMatrix2) :
    unitFamilyDiameter V < 1 / 40 ↔
      ∀ p : Fin n × Fin n, operatorNorm (V p.1 * (V p.2)⁻¹ - 1) < 1 / 40 := by
  constructor
  · exact fun h p => lt_of_le_of_lt (quotient_le_unitFamilyDiameter V p.1 p.2) h
  · intro h
    have : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
    obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite
      (f := fun p : Fin n × Fin n => operatorNorm (V p.1 * (V p.2)⁻¹ - 1))
    have e : unitFamilyDiameter V = operatorNorm (V p.1 * (V p.2)⁻¹ - 1) := hp.symm
    rw [e]
    exact h p
private theorem isOpen_narrowFamilies
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) (hn : 1 ≤ n) :
    IsOpen (narrowFamilies n) := by
  have hA : IsOpen {V : Fin n → ComplexMatrix2 | ∀ i, IsUnit (V i)} := by
    have e : {V : Fin n → ComplexMatrix2 | ∀ i, IsUnit (V i)} =
        ⋂ i, (fun V : Fin n → ComplexMatrix2 => V i) ⁻¹' {X : ComplexMatrix2 | IsUnit X} := by
      ext V
      simp
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_isUnit.preimage (continuous_apply i)
  have hcont : ∀ p : Fin n × Fin n, ContinuousOn
      (fun V : Fin n → ComplexMatrix2 => operatorNorm (V p.1 * (V p.2)⁻¹ - 1))
      {V : Fin n → ComplexMatrix2 | ∀ i, IsUnit (V i)} := by
    intro p
    have h1 : ContinuousOn (fun V : Fin n → ComplexMatrix2 => (V p.2)⁻¹)
        {V : Fin n → ComplexMatrix2 | ∀ i, IsUnit (V i)} :=
      (differentiableOn_inv hH).continuousOn.comp (continuous_apply p.2).continuousOn
        fun V hV => hV p.2
    exact (((continuous_apply p.1).continuousOn.mul h1).sub continuousOn_const).norm
  have e : narrowFamilies n = ⋂ p : Fin n × Fin n,
      ({V : Fin n → ComplexMatrix2 | ∀ i, IsUnit (V i)} ∩
        (fun V : Fin n → ComplexMatrix2 => operatorNorm (V p.1 * (V p.2)⁻¹ - 1)) ⁻¹'
          Iio (1 / 40)) := by
    have : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
    ext V
    simp only [narrowFamilies, mem_ofPred_eq, mem_iInter, mem_inter_iff, mem_preimage,
      mem_Iio, unitFamilyDiameter_lt_iff hn]
    exact ⟨fun h p => ⟨h.1, h.2 p⟩, fun h =>
      ⟨(h (⟨0, hn⟩, ⟨0, hn⟩)).1, fun p => (h p).2⟩⟩
  rw [e]
  exact isOpen_iInter_of_finite fun p => (hcont p).isOpen_inter_preimage hA isOpen_Iio
private theorem isUnitFamily_of_mem_narrowFamilies (hn : 1 ≤ n) {V : Fin n → ComplexMatrix2}
    (hV : V ∈ narrowFamilies n) :
    IsUnitFamily V ∧ unitFamilyDiameter V ≤ 1 / 40 :=
  ⟨⟨hn, hV.1⟩, hV.2.le⟩
private def meanMapIterate (m : ℕ) (V : Fin n → ComplexMatrix2) : ComplexMatrix2 :=
  (meanMap V)^[m] 0
private theorem meanMapIterate_succ (m : ℕ) (V : Fin n → ComplexMatrix2) :
    meanMapIterate (m + 1) V = meanMap V (meanMapIterate m V) :=
  Function.iterate_succ_apply' _ _ _
private theorem meanMapIterate_mem (hX : ExpLogEstimates)
    (hN : Numerics.ExpLogNumericBounds) (hn : 1 ≤ n) {V : Fin n → ComplexMatrix2}
    (hV : V ∈ narrowFamilies n) (m : ℕ) : meanMapIterate m V ∈ closedBallEighth := by
  obtain ⟨h1, h2⟩ := isUnitFamily_of_mem_narrowFamilies hn hV
  induction m with
  | zero => exact zero_mem_closedBallEighth
  | succ m ih =>
    rw [meanMapIterate_succ]
    exact meanMap_mapsTo hX hN h1 h2 ih
private theorem meanMapIterate_sub_le (hX : ExpLogEstimates)
    (hN : Numerics.ExpLogNumericBounds) (hn : 1 ≤ n) {V : Fin n → ComplexMatrix2}
    (hV : V ∈ narrowFamilies n) (m : ℕ) :
    operatorNorm (meanMapIterate m V - meanFixedPt V) ≤ (2 / 5) ^ m * (1 / 8) := by
  obtain ⟨h1, h2⟩ := isUnitFamily_of_mem_narrowFamilies hn hV
  obtain ⟨hb, hfix⟩ := meanFixedPt_spec hX hN h1 h2
  induction m with
  | zero =>
    have e : meanMapIterate 0 V = 0 := rfl
    rw [e, zero_sub, operatorNorm_neg, pow_zero, one_mul]
    exact hb
  | succ m ih =>
    have h := meanMap_lipschitz hX hN h1 h2 (meanMapIterate_mem hX hN hn hV m) hb
    rw [hfix, ← meanMapIterate_succ] at h
    refine h.trans ?_
    rw [pow_succ]
    nlinarith [pow_pos (show (0 : ℝ) < 2 / 5 by norm_num) m]
private theorem differentiableAt_meanMapIterate (hX : ExpLogEstimates)
    (hN : Numerics.ExpLogNumericBounds)
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) (hn : 1 ≤ n) (m : ℕ) :
    ∀ V ∈ narrowFamilies n, DifferentiableAt ℂ (meanMapIterate m) V := by
  induction m with
  | zero => exact fun V _ => differentiableAt_const _
  | succ m ih =>
    intro V hV
    have hfun : meanMapIterate (m + 1) = fun W : Fin n → ComplexMatrix2 => meanMapIterate m W +
        (n : ℂ)⁻¹ • ∑ i, logSeries (W i * (W ⟨0, hn⟩)⁻¹ * matExp (-meanMapIterate m W)) := by
      funext W
      rw [meanMapIterate_succ, meanMap, leadMember_eq W hn]
    rw [hfun]
    have hY := ih V hV
    have hproj : ∀ i, DifferentiableAt ℂ (fun W : Fin n → ComplexMatrix2 => W i) V :=
      fun i => by fun_prop
    have hinv : DifferentiableAt ℂ (fun W : Fin n → ComplexMatrix2 => (W ⟨0, hn⟩)⁻¹) V :=
      ((differentiableOn_inv hH).differentiableAt
        (isOpen_isUnit.mem_nhds (hV.1 ⟨0, hn⟩))).comp V (hproj _)
    have hexp : DifferentiableAt ℂ
        (fun W : Fin n → ComplexMatrix2 => matExp (-meanMapIterate m W)) V :=
      (differentiable_matExp hH _).comp V hY.neg
    refine hY.add (DifferentiableAt.fun_const_smul (DifferentiableAt.fun_sum fun i _ => ?_) _)
    have hprod : DifferentiableAt ℂ
        (fun W : Fin n → ComplexMatrix2 => W i * (W ⟨0, hn⟩)⁻¹ * matExp (-meanMapIterate m W)) V :=
      ((hproj i).mul hinv).mul hexp
    have hdom : V i * (V ⟨0, hn⟩)⁻¹ * matExp (-meanMapIterate m V) ∈ logBall := by
      obtain ⟨h1, h2⟩ := isUnitFamily_of_mem_narrowFamilies hn hV
      have a := operatorNorm_mul_matExp_neg_sub_one_le hX
        ((quotient_le_unitFamilyDiameter V i ⟨0, hn⟩).trans h2)
        (meanMapIterate_mem hX hN hn hV m)
      have b : Real.exp (1 / 8) < 1.1332 := hN.2.2.2.2.1
      refine lt_of_le_of_lt a ?_
      norm_num at b ⊢
      linarith
    exact DifferentiableAt.comp (g := logSeries) V
      ((differentiableOn_logSeries hH).differentiableAt (isOpen_logBall.mem_nhds hdom)) hprod
private theorem meanFixedPt_isHolomorphicVia (hX : ExpLogEstimates)
    (hN : Numerics.ExpLogNumericBounds)
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) (hn : 1 ≤ n) :
    ComplexCoordinates.IsHolomorphicVia (familyEquiv n) ComplexCoordinates.matrixEquiv
      (narrowFamilies n) meanFixedPt := by
  have hO := isOpen_narrowFamilies hH hn
  have hc : ∀ x, familyLinearEquiv n x = familyEquiv n x := fun _ => rfl
  have hc' : ∀ x, entryLinearEquiv x = ComplexCoordinates.matrixEquiv x := fun _ => rfl
  have hF : ∀ m, ComplexCoordinates.IsHolomorphicVia (familyEquiv n)
      ComplexCoordinates.matrixEquiv (narrowFamilies n) (meanMapIterate m) := fun m =>
    isHolomorphicVia_of_differentiableOn (familyLinearEquiv n) entryLinearEquiv hc hc' hO
      fun V hV => (differentiableAt_meanMapIterate hX hN hH hn m V hV).differentiableWithinAt
  have hO' : IsOpen (familyEquiv n '' narrowFamilies n) := (hF 0).1
  have hU : TendstoUniformlyOn (meanMapIterate (n := n)) meanFixedPt Filter.atTop
      (narrowFamilies n) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Filter.Tendsto (fun m : ℕ => ((2 : ℝ) / 5) ^ m * (1 / 8)) Filter.atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ) / 5) (by norm_num)
        (by norm_num)).mul_const (1 / 8 : ℝ)
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with m hm V hV
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (meanMapIterate_sub_le hX hN hn hV m) hm
  have hU' : TendstoUniformlyOn
      (fun m => ComplexCoordinates.matrixEquiv ∘ meanMapIterate m ∘ (familyEquiv n).symm)
      (ComplexCoordinates.matrixEquiv ∘ meanFixedPt ∘ (familyEquiv n).symm) Filter.atTop
      (familyEquiv n '' narrowFamilies n) := by
    have h1 := entryLinearEquiv.toContinuousLinearMap.uniformContinuous.comp_tendstoUniformlyOn hU
    have h2 := h1.comp (familyLinearEquiv n).symm
    rw [← image_eq_preimage_symm (familyLinearEquiv n) hc] at h2
    have hs : ⇑(familyEquiv n).symm = ⇑(familyLinearEquiv n).symm :=
      funext (equiv_symm_apply_eq (familyLinearEquiv n) hc)
    rw [hs]
    exact h2
  exact (hH.1 _ _ hO').2 4 _ _ hF hU'
private theorem average_isHolomorphicVia (hX : ExpLogEstimates)
    (hN : Numerics.ExpLogNumericBounds)
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) (hn : 1 ≤ n) :
    ComplexCoordinates.IsHolomorphicVia (familyEquiv n) ComplexCoordinates.matrixEquiv
      (narrowFamilies n) average := by
  have hO := isOpen_narrowFamilies hH hn
  have hc : ∀ x, familyLinearEquiv n x = familyEquiv n x := fun _ => rfl
  have hc' : ∀ x, entryLinearEquiv x = ComplexCoordinates.matrixEquiv x := fun _ => rfl
  have hY := differentiableOn_of_isHolomorphicVia hH (familyLinearEquiv n) entryLinearEquiv hc hc'
    (meanFixedPt_isHolomorphicVia hX hN hH hn)
  refine isHolomorphicVia_of_differentiableOn (familyLinearEquiv n) entryLinearEquiv hc hc' hO
    fun V hV => ?_
  have hfun : (average : (Fin n → ComplexMatrix2) → ComplexMatrix2) =
      fun W => matExp (meanFixedPt W) * W ⟨0, hn⟩ := by
    funext W
    rw [average, leadMember_eq W hn]
  rw [hfun]
  have h1 : DifferentiableAt ℂ (meanFixedPt (n := n)) V := hY.differentiableAt (hO.mem_nhds hV)
  have h2 : DifferentiableAt ℂ (fun W : Fin n → ComplexMatrix2 => W ⟨0, hn⟩) V := by fun_prop
  exact (((differentiable_matExp hH _).comp V h1).mul h2).differentiableWithinAt
theorem averageStatement_holds (hE : NormExpLogBasics)
    (hX : ExpLogEstimates) (hI : UnitaryLogarithmProperties)
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hN : Numerics.ExpLogNumericBounds) : AverageStatement := by
  refine ⟨fun n V hV hd => ?_, fun n hn W hW => average_const hX hN hn hW,
    fun n hn => ⟨isOpen_narrowFamilies hH hn, meanFixedPt_isHolomorphicVia hX hN hH hn,
      average_isHolomorphicVia hX hN hH hn⟩,
    fun n V hV hd => logMeans_specialUnitary hE hX hI hN hV hd⟩
  have spec := meanFixedPt_spec hX hN hV hd
  have hb : Real.exp (1 / 8) < 1.1332 := hN.2.2.2.2.1
  refine ⟨fun Y hY i => ?_, meanMap_mapsTo hX hN hV hd,
    fun Y hY Y' hY' => meanMap_lipschitz hX hN hV hd hY hY',
    ⟨meanFixedPt V, spec, fun Y hY =>
      meanFixedPt_unique hX hN hV hd hY.1 spec.1 hY.2 spec.2⟩,
    meanFixedPt_le hX hN hV hd, isUnit_average hE hV, quotient_average_le hE hX hN hV hd,
    by linarith, sum_logSeries_quotient_average hE hX hN hV hd,
    fun V' hu _ hs ⟨k, hk⟩ => eq_average_of_near_member hE hX hN hV hd hu hs hk,
    average_comp hE hX hN hV hd, meanFixedPt_traceless hX hN hV hd,
    meanFixedPt_I_smul_hermitianTraceless hX hI hN hV hd,
    fun hG V' hV' hb' hs => eq_average_of_specialUnitary hE hX hN hV hd hG hV' hb' hs⟩
  refine lt_of_le_of_lt
    (operatorNorm_mul_matExp_neg_sub_one_le hX ((quotient_leadMember_le hV i).trans hd) hY) ?_
  norm_num at hb ⊢
  linarith
end YangMills.Construction.Matrices.SmallDiameterMean

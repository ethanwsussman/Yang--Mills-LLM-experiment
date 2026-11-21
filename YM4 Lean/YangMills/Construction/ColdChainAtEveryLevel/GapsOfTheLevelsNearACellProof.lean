import YangMills.Construction.ColdChainAtEveryLevel.AveragesAndLocalSizesOfALevelProof
import YangMills.Construction.ColdChainAtEveryLevel.SizesOnARegion
import YangMills.Construction.ColdChainAtEveryLevel.ColdnessOfTheFieldBelowTheTopProof
import YangMills.Construction.ColdChainAtEveryLevel.GapsOfTheLevelsNearACell
import YangMills.Construction.ColdChainAtEveryLevel.MeanOfTheContoursOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LevelGaps
open BlockAverages BlockLines FlatPairing LatticeFractionalIntegration
variable {F : BlockFrame}
section Exp
theorem pureComponent_of_re_eq_zero {q : ℍ[ℝ]} (h : q.re = 0) : pureComponent q = q := by apply _root_.YangMills.Construction.BlockAverages.pureComponent_of_re_eq_zero <;> assumption
theorem pureComponent_expUnit (w : imaginaryQuaternions) : pureComponent ((expUnit w : UnitQuaternion) : ℍ[ℝ]) =
    (Real.sin ‖(w : ℍ[ℝ])‖ / ‖(w : ℍ[ℝ])‖) • (w : ℍ[ℝ]) := by
  show pureComponent (NormedSpace.exp (w : ℍ[ℝ])) = _
  rw [Quaternion.exp_of_re_eq_zero _ w.2, pureComponent_add, pureComponent_coe, zero_add, pureComponent_smul,
    pureComponent_of_re_eq_zero w.2]
theorem re_expUnit (w : imaginaryQuaternions) :
    (((expUnit w : UnitQuaternion) : ℍ[ℝ])).re = Real.cos ‖(w : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.GaugeFixing.re_coe_expUnit <;> assumption
theorem norm_pureComponent_expUnit_le (w : imaginaryQuaternions) :
    ‖pureComponent ((expUnit w : UnitQuaternion) : ℍ[ℝ])‖ ≤ ‖(w : ℍ[ℝ])‖ := by
  rw [pureComponent_expUnit, norm_smul]
  by_cases h0 : ‖(w : ℍ[ℝ])‖ = 0
  · rw [h0]
    simp
  · have hp : 0 < ‖(w : ℍ[ℝ])‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, div_mul_cancel₀ _ h0]
    exact Real.abs_sin_le_abs.trans (le_of_eq (abs_of_pos hp))
theorem norm_pureComponent_expUnit_sub_le (w : imaginaryQuaternions) (h1 : ‖(w : ℍ[ℝ])‖ ≤ 1) :
    ‖pureComponent ((expUnit w : UnitQuaternion) : ℍ[ℝ]) - (w : ℍ[ℝ])‖ ≤ ‖(w : ℍ[ℝ])‖ ^ 2 := by
  rw [pureComponent_expUnit]
  by_cases h0 : ‖(w : ℍ[ℝ])‖ = 0
  · have hw : (w : ℍ[ℝ]) = 0 := norm_eq_zero.1 h0
    simp [hw]
  · have hp : 0 < ‖(w : ℍ[ℝ])‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    set x := ‖(w : ℍ[ℝ])‖ with hx
    have e : (Real.sin x / x) • (w : ℍ[ℝ]) - (w : ℍ[ℝ]) = (Real.sin x / x - 1) • (w : ℍ[ℝ]) := by
      rw [sub_smul, one_smul]
    rw [e, norm_smul, Real.norm_eq_abs, ← hx]
    have e2 : (Real.sin x / x - 1) * x = Real.sin x - x := by
      field_simp
    have h3 := Real.sin_le hp.le
    have h4 := Real.sin_gt_sub_cube hp
    have e3 : |Real.sin x / x - 1| * x = |Real.sin x - x| := by
      rw [← e2, abs_mul, abs_of_pos hp]
    rw [e3, abs_of_nonpos (by linarith)]
    have h5 : x ^ 3 ≤ x ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (pow_pos hp 2).le
      nlinarith
    nlinarith [pow_pos hp 2, pow_pos hp 3]
theorem norm_expUnit_sub_one_le (w : imaginaryQuaternions) (h1 : ‖(w : ℍ[ℝ])‖ ≤ 1) :
    ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * ‖(w : ℍ[ℝ])‖ := by
  have hre : 0 ≤ (((expUnit w : UnitQuaternion) : ℍ[ℝ])).re := by
    rw [re_expUnit]
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · have := Real.pi_gt_three
      have h0 := norm_nonneg (w : ℍ[ℝ])
      linarith
    · have := Real.pi_gt_three
      linarith
  have := norm_sub_one_le_two_mul_pureComponent _ hre
  have h2 := norm_pureComponent_expUnit_le w
  linarith
end Exp
def ContourMeanBound (C c₀ : ℝ) : Prop :=
  ∀ (F : BlockFrame) (j : ℕ) (X R : F.GaugeField j) (b : F.Site (j + 1) × Fin 4) (t ε : ℝ),
    Odd F.blockSide → j + 1 ≤ F.top → 0 ≤ t → 0 ≤ ε → (F.blockSide : ℝ) * t ≤ c₀ → ε ≤ c₀ →
    (∀ a ∈ twoBlockHull F.blockSide b.2, ∀ k, a + basisVector k ∈ twoBlockHull F.blockSide b.2 →
      ‖((X (refineSite b.1 + siteOfCoords j a) k * (R (refineSite b.1 + siteOfCoords j a) k)⁻¹ : UnitQuaternion) :
        ℍ[ℝ]) - 1‖ ≤ t) →
    (∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2) *
        (polarUnit (contourAverage R b))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε) →
    ‖parallelAverage R (pureGap X R) b‖ ≤ (F.blockSide : ℝ) * t ∧
      ‖pureComponent ((relativeContourMean X R b : UnitQuaternion) : ℍ[ℝ]) - parallelAverage R (pureGap X R) b‖ ≤
        C * ((F.blockSide : ℝ) * t) * ((F.blockSide : ℝ) * t + ε) ∧
      ‖((relativeContourMean X R b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        4 * ‖parallelAverage R (pureGap X R) b‖ + C * ((F.blockSide : ℝ) * t) * ((F.blockSide : ℝ) * t + ε)
theorem chartGap_succ (R : F.FieldChain) (U : ChainChart F) (j : ℕ) (c : F.Site (j + 1) × Fin 4) :
    chartGap R U (j + 1) c.1 c.2 = expUnit (U.coarse j c.1 c.2) *
      (referenceDefect R j c * relativeContourMean (chartField R U j) (R j) c * (referenceDefect R j c)⁻¹) := by
  simp only [chartGap, chartField, relativeContourMean, referenceDefect]
  group
def levelForm (R : F.FieldChain) (U : ChainChart F) (j : ℕ) : F.Site j → Fin 4 → ℍ[ℝ] :=
  pureGap (chartField R U j) (R j)
theorem bond_estimate {C₀ c₀ : ℝ} (hM : ContourMeanBound C₀ c₀) (hC₀ : 0 < C₀) (hodd : Odd F.blockSide)
    (R : F.FieldChain) (U : ChainChart F) (j : ℕ) (hj : j + 1 ≤ F.top) (c : F.Site (j + 1) × Fin 4) (t ε : ℝ)
    (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε) (hτ : (F.blockSide : ℝ) * t ≤ c₀) (hε : ε ≤ c₀)
    (hsm : C₀ * ((F.blockSide : ℝ) * t + ε) ≤ 1)
    (hcl : ∀ a ∈ twoBlockHull F.blockSide c.2, ∀ k, a + basisVector k ∈ twoBlockHull F.blockSide c.2 →
      ‖((chartField R U j (refineSite c.1 + siteOfCoords j a) k *
        (R j (refineSite c.1 + siteOfCoords j a) k)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ t)
    (hsp : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy (R j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage (R j) c))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (hmis : ‖((referenceDefect R j c : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (hμ : ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ≤ 1) :
    ‖((chartGap R U (j + 1) c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        2 * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ + 5 * ((F.blockSide : ℝ) * t) ∧
      ‖levelForm R U (j + 1) c.1 c.2 - parallelAverage (R j) (levelForm R U j) c - (U.coarse j c.1 c.2 : ℍ[ℝ])‖ ≤
        (C₀ + 10) * (((F.blockSide : ℝ) * t) ^ 2 + ε * ((F.blockSide : ℝ) * t) +
          ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ * ((F.blockSide : ℝ) * t) + ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2) := by
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  obtain ⟨q1, q2, q3⟩ := hM F j (chartField R U j) (R j) c t ε hodd hj ht0 hε0 hτ hε hcl hsp
  set τ : ℝ := (F.blockSide : ℝ) * t with hτdef
  have hτ0 : 0 ≤ τ := mul_nonneg hLr.le ht0
  set μ : ℝ := ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ with hμdef
  have hμ0 : 0 ≤ μ := norm_nonneg _
  set e : UnitQuaternion := relativeContourMean (chartField R U j) (R j) c with he
  set m : UnitQuaternion := referenceDefect R j c with hm
  set Q : ℍ[ℝ] := parallelAverage (R j) (pureGap (chartField R U j) (R j)) c with hQ
  have hsq : C₀ * τ * (τ + ε) ≤ τ := by
    have := mul_le_mul_of_nonneg_left hsm hτ0
    nlinarith
  have he1 : ‖(e : ℍ[ℝ]) - 1‖ ≤ 5 * τ := by linarith
  have hw1 : ‖((m * e * m⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 5 * τ := by
    rw [norm_coe_conj_sub_one]
    exact he1
  have hE1 := norm_expUnit_sub_one_le (U.coarse j c.1 c.2) hμ
  have hgap : chartGap R U (j + 1) c.1 c.2 = expUnit (U.coarse j c.1 c.2) * (m * e * m⁻¹) := chartGap_succ R U j c
  refine ⟨?_, ?_⟩
  · rw [hgap]
    have := norm_coe_mul_sub_one_le (expUnit (U.coarse j c.1 c.2)) (m * e * m⁻¹)
    linarith
  · have hform : levelForm R U (j + 1) c.1 c.2 =
        pureComponent ((expUnit (U.coarse j c.1 c.2) * (m * e * m⁻¹) : UnitQuaternion) : ℍ[ℝ]) := by
      rw [← hgap]
      rfl
    have hpw : pureComponent ((m * e * m⁻¹ : UnitQuaternion) : ℍ[ℝ]) = adjointAction m (pureComponent (e : ℍ[ℝ])) := by
      rw [← _root_.YangMills.Construction.BlockLines.pureComponent_adjointAction]
      rfl
    have e0 : levelForm R U (j + 1) c.1 c.2 - parallelAverage (R j) (levelForm R U j) c -
        (U.coarse j c.1 c.2 : ℍ[ℝ]) =
        (pureComponent ((expUnit (U.coarse j c.1 c.2) * (m * e * m⁻¹) : UnitQuaternion) : ℍ[ℝ]) -
            pureComponent ((expUnit (U.coarse j c.1 c.2) : UnitQuaternion) : ℍ[ℝ]) -
            pureComponent ((m * e * m⁻¹ : UnitQuaternion) : ℍ[ℝ])) +
          (pureComponent ((expUnit (U.coarse j c.1 c.2) : UnitQuaternion) : ℍ[ℝ]) - (U.coarse j c.1 c.2 : ℍ[ℝ])) +
          (adjointAction m (pureComponent (e : ℍ[ℝ])) - pureComponent (e : ℍ[ℝ])) +
          (pureComponent (e : ℍ[ℝ]) - Q) := by
      rw [hform, ← hpw]
      show _ - Q - _ = _
      abel
    rw [e0]
    have b1 := norm_pureComponent_mul_sub_le (expUnit (U.coarse j c.1 c.2)) (m * e * m⁻¹)
    have b1' : ‖((expUnit (U.coarse j c.1 c.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ *
        ‖((m * e * m⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        (2 * μ) * (5 * τ) := mul_le_mul hE1 hw1 (norm_nonneg _) (by positivity)
    have b2 := norm_pureComponent_expUnit_sub_le (U.coarse j c.1 c.2) hμ
    have b3 := norm_adjointAction_sub_le m (pureComponent (e : ℍ[ℝ]))
    have b3' : ‖pureComponent (e : ℍ[ℝ])‖ ≤ 5 * τ := (norm_pureComponent_coe_le e).trans he1
    have b3'' : 2 * ‖(m : ℍ[ℝ]) - 1‖ * ‖pureComponent (e : ℍ[ℝ])‖ ≤ 2 * ε * (5 * τ) :=
      mul_le_mul (by linarith) b3' (norm_nonneg _) (by positivity)
    refine (norm_add_le _ _).trans ?_
    have s1 := norm_add_le ((pureComponent ((expUnit (U.coarse j c.1 c.2) * (m * e * m⁻¹) : UnitQuaternion) : ℍ[ℝ]) -
      pureComponent ((expUnit (U.coarse j c.1 c.2) : UnitQuaternion) : ℍ[ℝ]) -
      pureComponent ((m * e * m⁻¹ : UnitQuaternion) : ℍ[ℝ])) +
      (pureComponent ((expUnit (U.coarse j c.1 c.2) : UnitQuaternion) : ℍ[ℝ]) - (U.coarse j c.1 c.2 : ℍ[ℝ])))
      (adjointAction m (pureComponent (e : ℍ[ℝ])) - pureComponent (e : ℍ[ℝ]))
    have s2 := norm_add_le (pureComponent ((expUnit (U.coarse j c.1 c.2) * (m * e * m⁻¹) : UnitQuaternion) : ℍ[ℝ]) -
      pureComponent ((expUnit (U.coarse j c.1 c.2) : UnitQuaternion) : ℍ[ℝ]) -
      pureComponent ((m * e * m⁻¹ : UnitQuaternion) : ℍ[ℝ]))
      (pureComponent ((expUnit (U.coarse j c.1 c.2) : UnitQuaternion) : ℍ[ℝ]) - (U.coarse j c.1 c.2 : ℍ[ℝ]))
    have hfin : 10 * (μ * τ) + μ ^ 2 + 10 * (ε * τ) + C₀ * τ * (τ + ε) ≤
        (C₀ + 10) * (τ ^ 2 + ε * τ + μ * τ + μ ^ 2) := by
      nlinarith [mul_nonneg hτ0 hτ0, mul_nonneg hε0 hτ0, mul_nonneg hμ0 hτ0, mul_nonneg hμ0 hμ0,
        mul_pos hC₀ hC₀, mul_nonneg hC₀.le (mul_nonneg hμ0 hτ0), mul_nonneg hC₀.le (mul_nonneg hμ0 hμ0)]
    linarith
section Sums
theorem le_of_pow_four_le_pow_four {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 4 ≤ b ^ 4) : a ≤ b :=
  (pow_le_pow_iff_left₀ ha hb (by norm_num)).1 h
theorem le_of_sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b :=
  (pow_le_pow_iff_left₀ ha hb (by norm_num)).1 h
def fourthRoot (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)
theorem fourthRoot_nonneg (x : ℝ) : 0 ≤ fourthRoot x := Real.sqrt_nonneg _
theorem fourthRoot_pow_four {x : ℝ} (hx : 0 ≤ x) : fourthRoot x ^ 4 = x := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.sqrt_sqrt_pow_four <;> assumption
theorem finset_minkowski_natPow {ι : Type*} (s : Finset ι) (p : ℕ) (hp : 1 ≤ p) (f g h : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) (hh : ∀ i ∈ s, 0 ≤ h i)
    (hle : ∀ i ∈ s, f i ≤ g i + h i) :
    (∑ i ∈ s, f i ^ p) ^ (1 / (p : ℝ)) ≤
      (∑ i ∈ s, g i ^ p) ^ (1 / (p : ℝ)) + (∑ i ∈ s, h i ^ p) ^ (1 / (p : ℝ)) := by
  have hp' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have key := Real.Lp_add_le_of_nonneg s hp' hg hh
  simp only [Real.rpow_natCast] at key
  refine le_trans ?_ key
  refine Real.rpow_le_rpow (Finset.sum_nonneg fun i hi => pow_nonneg (hf i hi) _) ?_ (by positivity)
  exact Finset.sum_le_sum fun i hi => pow_le_pow_left₀ (hf i hi) (hle i hi) _
theorem rpow_inv_two_le {x : ℝ} (_hx : 0 ≤ x) {b : ℝ} (hb : 0 ≤ b) (h : x ≤ b ^ 2) :
    x ^ (1 / ((2 : ℕ) : ℝ)) ≤ b := by
  have : x ^ (1 / ((2 : ℕ) : ℝ)) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [this]
  exact Real.sqrt_le_iff.2 ⟨hb, h⟩
theorem le_sq_of_rpow_inv_two_le {x : ℝ} (hx : 0 ≤ x) {b : ℝ} (h : x ^ (1 / ((2 : ℕ) : ℝ)) ≤ b) : x ≤ b ^ 2 := by
  have e : x ^ (1 / ((2 : ℕ) : ℝ)) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [e] at h
  have h0 := Real.sqrt_nonneg x
  have := pow_le_pow_left₀ h0 h 2
  rwa [Real.sq_sqrt hx] at this
theorem rpow_inv_four_le {x : ℝ} (hx : 0 ≤ x) {b : ℝ} (hb : 0 ≤ b) (h : x ≤ b ^ 4) :
    x ^ (1 / ((4 : ℕ) : ℝ)) ≤ b := by
  have hh : (b ^ 4) ^ (1 / ((4 : ℕ) : ℝ)) = b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
    norm_num
  rw [← hh]
  exact Real.rpow_le_rpow hx h (by norm_num)
theorem le_pow_four_of_rpow_inv_four_le {x : ℝ} (hx : 0 ≤ x) {b : ℝ} (h : x ^ (1 / ((4 : ℕ) : ℝ)) ≤ b) :
    x ≤ b ^ 4 := by
  have h0 : 0 ≤ x ^ (1 / ((4 : ℕ) : ℝ)) := Real.rpow_nonneg hx _
  have := pow_le_pow_left₀ h0 h 4
  have e : (x ^ (1 / ((4 : ℕ) : ℝ))) ^ 4 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  rwa [e] at this
theorem sum_pow_four_le_sq_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, f i ^ 4 ≤ (∑ i ∈ s, f i ^ 2) ^ 2 := by
  have hnn : ∀ i ∈ s, 0 ≤ f i ^ 2 := fun i _ => sq_nonneg _
  have h1 : ∀ i ∈ s, f i ^ 4 ≤ f i ^ 2 * ∑ k ∈ s, f k ^ 2 := by
    intro i hi
    have := Finset.single_le_sum hnn hi
    calc f i ^ 4 = f i ^ 2 * f i ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (sq_nonneg _)
  refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, sq]
theorem sum_sq_remainder_le {ι : Type*} (Y : Finset ι) (τ μ qn : ι → ℝ) (ε K β T P Q : ℝ) (hε : 0 ≤ ε)
    (_hK : 0 ≤ K) (_hβ : 0 ≤ β) (hτ : ∀ c ∈ Y, 0 ≤ τ c) (hμ : ∀ c ∈ Y, 0 ≤ μ c) (hq0 : ∀ c ∈ Y, 0 ≤ qn c)
    (hq : ∀ c ∈ Y, qn c ≤ K * (τ c ^ 2 + ε * τ c + μ c * τ c + μ c ^ 2)) (hT : ∀ c ∈ Y, τ c ≤ T)
    (hμβ : ∀ c ∈ Y, μ c ≤ β) (h1 : ∑ c ∈ Y, τ c ^ 4 ≤ P) (h2 : ε ^ 2 * ∑ c ∈ Y, τ c ^ 2 ≤ Q)
    (h3 : ∑ c ∈ Y, μ c ^ 2 ≤ β ^ 2) :
    ∑ c ∈ Y, qn c ^ 2 ≤ 4 * K ^ 2 * (P + Q + T ^ 2 * β ^ 2 + β ^ 4) := by
  have hone : ∀ c ∈ Y, qn c ^ 2 ≤
      4 * K ^ 2 * (τ c ^ 4 + ε ^ 2 * τ c ^ 2 + T ^ 2 * μ c ^ 2 + β ^ 2 * μ c ^ 2) := by
    intro c hc
    have a0 := hτ c hc
    have b0 := hμ c hc
    have hs : 0 ≤ τ c ^ 2 + ε * τ c + μ c * τ c + μ c ^ 2 := by positivity
    have h4 : qn c ^ 2 ≤ (K * (τ c ^ 2 + ε * τ c + μ c * τ c + μ c ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (hq0 c hc) (hq c hc) 2
    have h5 : (τ c ^ 2 + ε * τ c + μ c * τ c + μ c ^ 2) ^ 2 ≤
        4 * ((τ c ^ 2) ^ 2 + (ε * τ c) ^ 2 + (μ c * τ c) ^ 2 + (μ c ^ 2) ^ 2) := by
      nlinarith [sq_nonneg (τ c ^ 2 - ε * τ c), sq_nonneg (τ c ^ 2 - μ c * τ c), sq_nonneg (τ c ^ 2 - μ c ^ 2),
        sq_nonneg (ε * τ c - μ c * τ c), sq_nonneg (ε * τ c - μ c ^ 2), sq_nonneg (μ c * τ c - μ c ^ 2)]
    have h6 : (μ c * τ c) ^ 2 ≤ T ^ 2 * μ c ^ 2 := by
      have := pow_le_pow_left₀ a0 (hT c hc) 2
      nlinarith [sq_nonneg (μ c)]
    have h7 : (μ c ^ 2) ^ 2 ≤ β ^ 2 * μ c ^ 2 := by
      have := pow_le_pow_left₀ b0 (hμβ c hc) 2
      nlinarith [sq_nonneg (μ c)]
    have h8 : (τ c ^ 2) ^ 2 = τ c ^ 4 := by ring
    have h9 : (ε * τ c) ^ 2 = ε ^ 2 * τ c ^ 2 := by ring
    calc qn c ^ 2 ≤ K ^ 2 * (τ c ^ 2 + ε * τ c + μ c * τ c + μ c ^ 2) ^ 2 := by
          rw [mul_pow] at h4
          exact h4
      _ ≤ K ^ 2 * (4 * (τ c ^ 4 + ε ^ 2 * τ c ^ 2 + T ^ 2 * μ c ^ 2 + β ^ 2 * μ c ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
          rw [h8, h9] at h5
          linarith
      _ = _ := by ring
  refine (Finset.sum_le_sum hone).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have e1 : T ^ 2 * ∑ c ∈ Y, μ c ^ 2 ≤ T ^ 2 * β ^ 2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg T)
  have e2 : β ^ 2 * ∑ c ∈ Y, μ c ^ 2 ≤ β ^ 2 * β ^ 2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg β)
  nlinarith
end Sums
section Levels
def carriedForm (R : F.FieldChain) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) : (j : ℕ) → F.Site j → Fin 4 → ℍ[ℝ]
  | 0 => f
  | j + 1 => fun y i => parallelAverage (R j) (carriedForm R f j) (y, i)
theorem sum_carriedForm_pow_four_le (hodd : Odd F.blockSide) (B : Finset F.Cell) (R : F.FieldChain)
    (f : F.Site 0 → Fin 4 → ℍ[ℝ]) :
    ∀ j, j ≤ F.top → ∑ b ∈ innerBonds B j, ‖carriedForm R f j b.1 b.2‖ ^ 4 ≤ ∑ b ∈ innerBonds B 0, ‖f b.1 b.2‖ ^ 4 := by
  intro j
  induction j with
  | zero => intro _; exact le_rfl
  | succ j ih =>
    intro hj
    exact (sum_norm_parallelAverage_pow_four_le (B := B) (by omega) hodd (innerBonds B (j + 1)) subset_rfl (R j)
      (carriedForm R f j)).trans (ih (by omega))
theorem parallelAverage_sub {j : ℕ} (R : F.GaugeField j) (f g : F.Site j → Fin 4 → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) :
    parallelAverage R (fun x i => f x i - g x i) c = parallelAverage R f c - parallelAverage R g c := by apply _root_.YangMills.Construction.BlockAverages.ColdBelowTop.parallelAverage_sub <;> assumption
def residualForm (R : F.FieldChain) (U : ChainChart F) (j : ℕ) : F.Site j → Fin 4 → ℍ[ℝ] :=
  fun x i => levelForm R U j x i - carriedForm R (levelForm R U 0) j x i
theorem hullSum_nonneg {j : ℕ} (g : F.Site j × Fin 4 → ℝ) (hg : ∀ b, 0 ≤ g b) (c : F.Site (j + 1) × Fin 4) :
    0 ≤ hullSum g c := by
  classical
  unfold hullSum
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun k _ => ?_
  split_ifs
  · exact hg _
  · exact le_rfl
theorem level_succ_bounds {C₀ c₀ : ℝ} (hM : ContourMeanBound C₀ c₀) (hC₀ : 0 < C₀) (hodd : Odd F.blockSide)
    (hL3 : 3 ≤ F.blockSide) (B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (j : ℕ) (hj : j + 1 < F.top)
    (ε β E : ℝ) (hε0 : 0 ≤ ε) (hβ0 : 0 ≤ β) (hE0 : 0 ≤ E) (hτ : (F.blockSide : ℝ) * (8 * β) ≤ c₀) (hε : ε ≤ c₀)
    (hsm : C₀ * ((F.blockSide : ℝ) * (8 * β) + ε) ≤ 1) (hnear : 2 * β + 5 * ((F.blockSide : ℝ) * (8 * β)) ≤ 1)
    (hβ1 : β ≤ 1)
    (hsp : ∀ c ∈ innerBonds B (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy (R j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage (R j) c))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (hmis : ∀ c ∈ innerBonds B (j + 1), ‖((referenceDefect R j c : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (hcard : ε ^ 4 * ((innerBonds B (j + 1)).card : ℝ) ≤ E ^ 2)
    (hfin : 4 * (C₀ + 10) ^ 2 * ((F.blockSide : ℝ) ^ 4 * (16 * ((hullBox F.blockSide).card : ℝ)) * (8 * β) ^ 4 +
        E * ((F.blockSide : ℝ) ^ 2 * (16 * ((hullBox F.blockSide).card : ℝ)) * (8 * β) ^ 2) +
        ((F.blockSide : ℝ) * (8 * β)) ^ 2 * β ^ 2 + β ^ 4) ≤ β ^ 2)
    (hmu : ∑ c ∈ innerBonds B (j + 1), ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 ≤ β ^ 2)
    (hZ : ∑ b ∈ innerBonds B j, normSubOne (chartGap R U j b.1 b.2) ^ 4 ≤ (8 * β) ^ 4)
    (hD : ∑ b ∈ innerBonds B j, ‖residualForm R U j b.1 b.2‖ ^ 2 ≤ (3 * β) ^ 2)
    (hA : ∑ b ∈ innerBonds B (j + 1), ‖carriedForm R (levelForm R U 0) (j + 1) b.1 b.2‖ ^ 4 ≤ β ^ 4) :
    ∑ b ∈ innerBonds B (j + 1), normSubOne (chartGap R U (j + 1) b.1 b.2) ^ 4 ≤ (8 * β) ^ 4 ∧
      ∑ b ∈ innerBonds B (j + 1), ‖residualForm R U (j + 1) b.1 b.2‖ ^ 2 ≤ (3 * β) ^ 2 := by
  classical
  have hjn : j < F.top := by omega
  have hLr : (3 : ℝ) ≤ F.blockSide := by exact_mod_cast hL3
  have hLp : (0 : ℝ) < F.blockSide := by linarith
  have hL1 : 1 ≤ F.blockSide := by omega
  set Y := innerBonds B (j + 1) with hY
  set g : F.Site j × Fin 4 → ℝ := fun b => normSubOne (chartGap R U j b.1 b.2) ^ 4 with hg
  have hg0 : ∀ b, 0 ≤ g b := fun b => by positivity
  set Mh : ℝ := 16 * ((hullBox F.blockSide).card : ℝ) with hMh
  have hbox : (1 : ℝ) ≤ ((hullBox F.blockSide).card : ℝ) := by
    have h0 : (0 : Lattice4) ∈ hullBox F.blockSide := by
      refine Fintype.mem_piFinset.2 fun μ => Finset.mem_Icc.2 ?_
      simp only [Pi.zero_apply]
      constructor <;> omega
    have := Finset.card_pos.2 ⟨_, h0⟩
    exact_mod_cast this
  have hMh1 : 1 ≤ Mh := by rw [hMh]; linarith
  set t : F.Site (j + 1) × Fin 4 → ℝ := fun c => min (8 * β) (fourthRoot (hullSum g c)) with ht
  have ht0 : ∀ c, 0 ≤ t c := fun c => le_min (by positivity) (fourthRoot_nonneg _)
  have ht8 : ∀ c, t c ≤ 8 * β := fun c => min_le_left _ _
  have ht4 : ∀ c, t c ^ 4 ≤ hullSum g c := by
    intro c
    have h1 := pow_le_pow_left₀ (ht0 c) (min_le_right (8 * β) (fourthRoot (hullSum g c))) 4
    rwa [fourthRoot_pow_four (hullSum_nonneg g hg0 c)] at h1
  have hclose : ∀ c ∈ Y, ∀ a ∈ twoBlockHull F.blockSide c.2, ∀ k, a + basisVector k ∈ twoBlockHull F.blockSide c.2 →
      ‖((chartField R U j (refineSite c.1 + siteOfCoords j a) k *
        (R j (refineSite c.1 + siteOfCoords j a) k)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ t c := by
    intro c hc a ha k hk
    have hb := bond_mem_innerBonds_of_mem_twoBlockHull hjn hodd c hc a k ha hk
    have hsz0 : 0 ≤ normSubOne (chartGap R U j (refineSite c.1 + siteOfCoords j a) k) := norm_nonneg _
    refine le_min ?_ ?_
    · have h1 := Finset.single_le_sum (f := g) (fun b _ => hg0 b) hb
      exact le_of_pow_four_le_pow_four hsz0 (by positivity) (h1.trans hZ)
    · have h1 := le_hullSum hL1 g hg0 c k ha hk
      refine le_of_pow_four_le_pow_four hsz0 (fourthRoot_nonneg _) ?_
      rw [fourthRoot_pow_four (hullSum_nonneg g hg0 c)]
      exact h1
  have hμβ : ∀ c ∈ Y, ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ≤ β := by
    intro c hc
    have h1 := Finset.single_le_sum (f := fun c : F.Site (j + 1) × Fin 4 => ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2)
      (fun _ _ => by positivity) hc
    exact le_of_sq_le_sq_of_nonneg (norm_nonneg _) hβ0 (h1.trans hmu)
  have hLt : ∀ c, (F.blockSide : ℝ) * t c ≤ (F.blockSide : ℝ) * (8 * β) := fun c =>
    mul_le_mul_of_nonneg_left (ht8 c) hLp.le
  have hbond : ∀ c ∈ Y, _ := fun c hc =>
    bond_estimate hM hC₀ hodd R U j hj.le c (t c) ε (ht0 c) hε0 ((hLt c).trans hτ) hε
      (le_trans (mul_le_mul_of_nonneg_left (by linarith [hLt c]) hC₀.le) hsm) (hclose c hc) (hsp c hc) (hmis c hc)
      ((hμβ c hc).trans hβ1)
  set q : F.Site (j + 1) × Fin 4 → ℍ[ℝ] := fun c =>
    levelForm R U (j + 1) c.1 c.2 - parallelAverage (R j) (levelForm R U j) c - (U.coarse j c.1 c.2 : ℍ[ℝ]) with hq
  have hsumW : ∑ c ∈ Y, hullSum g c ≤ Mh * (8 * β) ^ 4 :=
    (sum_hullSum_le hjn hodd Y subset_rfl g hg0).trans (mul_le_mul_of_nonneg_left hZ (by positivity))
  set P : ℝ := (F.blockSide : ℝ) ^ 4 * Mh * (8 * β) ^ 4 with hP
  have hP0 : 0 ≤ P := by positivity
  have h1 : ∑ c ∈ Y, ((F.blockSide : ℝ) * t c) ^ 4 ≤ P := by
    have e : ∑ c ∈ Y, ((F.blockSide : ℝ) * t c) ^ 4 = (F.blockSide : ℝ) ^ 4 * ∑ c ∈ Y, t c ^ 4 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [e, hP, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun c _ => ht4 c).trans hsumW) (by positivity)
  set Qn : ℝ := E * ((F.blockSide : ℝ) ^ 2 * Mh * (8 * β) ^ 2) with hQn
  have hQ0 : 0 ≤ Qn := by positivity
  have h2 : ε ^ 2 * ∑ c ∈ Y, ((F.blockSide : ℝ) * t c) ^ 2 ≤ Qn := by
    have hcs : (∑ c ∈ Y, ((F.blockSide : ℝ) * t c) ^ 2) ^ 2 ≤
        (Y.card : ℝ) * ∑ c ∈ Y, (((F.blockSide : ℝ) * t c) ^ 2) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have e4 : ∑ c ∈ Y, (((F.blockSide : ℝ) * t c) ^ 2) ^ 2 = ∑ c ∈ Y, ((F.blockSide : ℝ) * t c) ^ 4 :=
      Finset.sum_congr rfl fun c _ => by ring
    rw [e4] at hcs
    have hcs2 : (∑ c ∈ Y, ((F.blockSide : ℝ) * t c) ^ 2) ^ 2 ≤ (Y.card : ℝ) * P :=
      hcs.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    refine le_of_sq_le_sq_of_nonneg (by positivity) hQ0 ?_
    have hPM : P ≤ ((F.blockSide : ℝ) ^ 2 * Mh * (8 * β) ^ 2) ^ 2 := by
      have : (F.blockSide : ℝ) ^ 4 * Mh * (8 * β) ^ 4 ≤ (F.blockSide : ℝ) ^ 4 * (Mh * Mh) * (8 * β) ^ 4 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
        nlinarith
      calc P ≤ _ := this
        _ = _ := by ring
    calc (ε ^ 2 * ∑ c ∈ Y, ((F.blockSide : ℝ) * t c) ^ 2) ^ 2 =
          ε ^ 4 * (∑ c ∈ Y, ((F.blockSide : ℝ) * t c) ^ 2) ^ 2 := by ring
      _ ≤ ε ^ 4 * ((Y.card : ℝ) * P) := mul_le_mul_of_nonneg_left hcs2 (by positivity)
      _ = ε ^ 4 * (Y.card : ℝ) * P := by ring
      _ ≤ E ^ 2 * ((F.blockSide : ℝ) ^ 2 * Mh * (8 * β) ^ 2) ^ 2 :=
          mul_le_mul hcard hPM hP0 (by positivity)
      _ = Qn ^ 2 := by rw [hQn]; ring
  have hSq : ∑ c ∈ Y, ‖q c‖ ^ 2 ≤ β ^ 2 := by
    refine (sum_sq_remainder_le Y (fun c => (F.blockSide : ℝ) * t c) (fun c => ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖)
      (fun c => ‖q c‖) ε (C₀ + 10) β ((F.blockSide : ℝ) * (8 * β)) P Qn hε0 (by positivity) hβ0
      (fun c _ => mul_nonneg hLp.le (ht0 c)) (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      (fun c hc => (hbond c hc).2) (fun c _ => hLt c) hμβ h1 h2 hmu).trans hfin
  have hrest : ∀ c ∈ Y, ‖residualForm R U (j + 1) c.1 c.2‖ ≤
      ‖parallelAverage (R j) (residualForm R U j) c‖ + (‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ + ‖q c‖) := by
    intro c _
    have e : residualForm R U (j + 1) c.1 c.2 = parallelAverage (R j) (residualForm R U j) c +
        ((U.coarse j c.1 c.2 : ℍ[ℝ]) + q c) := by
      have e1 : parallelAverage (R j) (residualForm R U j) c = parallelAverage (R j) (levelForm R U j) c -
          parallelAverage (R j) (carriedForm R (levelForm R U 0) j) c :=
        parallelAverage_sub (R j) _ _ c
      have e2 : carriedForm R (levelForm R U 0) (j + 1) c.1 c.2 =
          parallelAverage (R j) (carriedForm R (levelForm R U 0) j) c := rfl
      rw [e1]
      simp only [residualForm, hq, e2]
      abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
  have hQ2 : (∑ c ∈ Y, ‖parallelAverage (R j) (residualForm R U j) c‖ ^ 2) ^ (1 / ((2 : ℕ) : ℝ)) ≤ β := by
    refine rpow_inv_two_le (Finset.sum_nonneg fun _ _ => by positivity) hβ0 ?_
    refine (sum_norm_parallelAverage_sq_le hjn hodd Y subset_rfl (R j) (residualForm R U j)).trans ?_
    have h3 : (1 / (F.blockSide : ℝ) ^ 2) * ∑ b ∈ innerBonds B j, ‖residualForm R U j b.1 b.2‖ ^ 2 ≤
        (1 / (F.blockSide : ℝ) ^ 2) * (3 * β) ^ 2 := mul_le_mul_of_nonneg_left hD (by positivity)
    refine h3.trans ?_
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    have h9 : (9 : ℝ) ≤ (F.blockSide : ℝ) ^ 2 := by nlinarith
    have e9 : (3 * β) ^ 2 = β ^ 2 * 9 := by ring
    rw [e9]
    exact mul_le_mul_of_nonneg_left h9 (sq_nonneg β)
  have hmu2 : (∑ c ∈ Y, ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2) ^ (1 / ((2 : ℕ) : ℝ)) ≤ β :=
    rpow_inv_two_le (Finset.sum_nonneg fun _ _ => by positivity) hβ0 hmu
  have hq2 : (∑ c ∈ Y, ‖q c‖ ^ 2) ^ (1 / ((2 : ℕ) : ℝ)) ≤ β :=
    rpow_inv_two_le (Finset.sum_nonneg fun _ _ => by positivity) hβ0 hSq
  have hm2 := finset_minkowski_natPow Y 2 (by norm_num) (fun c => ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ + ‖q c‖)
    (fun c => ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖) (fun c => ‖q c‖) (fun _ _ => by positivity)
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) (fun _ _ => le_rfl)
  have hm3 := finset_minkowski_natPow Y 2 (by norm_num) (fun c => ‖residualForm R U (j + 1) c.1 c.2‖)
    (fun c => ‖parallelAverage (R j) (residualForm R U j) c‖) (fun c => ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ + ‖q c‖)
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) (fun _ _ => by positivity) hrest
  have hRest : ∑ c ∈ Y, ‖residualForm R U (j + 1) c.1 c.2‖ ^ 2 ≤ (3 * β) ^ 2 :=
    le_sq_of_rpow_inv_two_le (Finset.sum_nonneg fun _ _ => by positivity) (by linarith)
  have hR4 : ∑ c ∈ Y, ‖residualForm R U (j + 1) c.1 c.2‖ ^ 4 ≤ (3 * β) ^ 4 := by
    refine (sum_pow_four_le_sq_sum_sq Y _).trans ?_
    have := pow_le_pow_left₀ (Finset.sum_nonneg fun c _ => by positivity) hRest 2
    calc _ ≤ ((3 * β) ^ 2) ^ 2 := this
      _ = (3 * β) ^ 4 := by ring
  have hform : ∀ c ∈ Y, ‖levelForm R U (j + 1) c.1 c.2‖ ≤
      ‖carriedForm R (levelForm R U 0) (j + 1) c.1 c.2‖ + ‖residualForm R U (j + 1) c.1 c.2‖ := by
    intro c _
    have e : levelForm R U (j + 1) c.1 c.2 =
        carriedForm R (levelForm R U 0) (j + 1) c.1 c.2 + residualForm R U (j + 1) c.1 c.2 := by
      simp only [residualForm]
      abel
    rw [e]
    exact norm_add_le _ _
  have hm4 := finset_minkowski_natPow Y 4 (by norm_num) (fun c => ‖levelForm R U (j + 1) c.1 c.2‖)
    (fun c => ‖carriedForm R (levelForm R U 0) (j + 1) c.1 c.2‖) (fun c => ‖residualForm R U (j + 1) c.1 c.2‖)
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) hform
  have hF4 : ∑ c ∈ Y, ‖levelForm R U (j + 1) c.1 c.2‖ ^ 4 ≤ (4 * β) ^ 4 := by
    refine le_pow_four_of_rpow_inv_four_le (Finset.sum_nonneg fun _ _ => by positivity) (hm4.trans ?_)
    have a1 := rpow_inv_four_le (Finset.sum_nonneg fun _ _ => by positivity) hβ0 hA
    have a2 := rpow_inv_four_le (Finset.sum_nonneg fun _ _ => by positivity) (by positivity : 0 ≤ 3 * β) hR4
    linarith
  refine ⟨?_, hRest⟩
  have hsz : ∀ c ∈ Y, normSubOne (chartGap R U (j + 1) c.1 c.2) ^ 4 ≤ 16 * ‖levelForm R U (j + 1) c.1 c.2‖ ^ 4 := by
    intro c hc
    have b1 := (hbond c hc).1
    have hμ := hμβ c hc
    have hn : ‖((chartGap R U (j + 1) c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 1 := by
      have := hLt c
      linarith
    have hle : normSubOne (chartGap R U (j + 1) c.1 c.2) ≤ 2 * ‖levelForm R U (j + 1) c.1 c.2‖ :=
      norm_sub_one_le_two_mul_pureComponent _ (re_nonneg_of_norm_sub_one_le _ hn)
    have := pow_le_pow_left₀ (norm_nonneg _ : 0 ≤ normSubOne (chartGap R U (j + 1) c.1 c.2)) hle 4
    calc _ ≤ (2 * ‖levelForm R U (j + 1) c.1 c.2‖) ^ 4 := this
      _ = _ := by ring
  refine (Finset.sum_le_sum hsz).trans ?_
  rw [← Finset.mul_sum]
  calc 16 * ∑ c ∈ Y, ‖levelForm R U (j + 1) c.1 c.2‖ ^ 4 ≤ 16 * (4 * β) ^ 4 :=
        mul_le_mul_of_nonneg_left hF4 (by norm_num)
    _ = (8 * β) ^ 4 := by ring
theorem exists_small_threshold {C₀ c₀ cb A D G : ℝ} (hC₀ : 0 < C₀) (hc₀ : 0 < c₀) (hcb : 0 < cb) (hA : 0 < A)
    (hD : 0 < D) (hG : 0 ≤ G) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ c ≤ cb ∧ c * A ≤ c₀ ∧ C₀ * (c * A) ≤ 1 ∧ c * D ≤ 1 ∧ 2 * G * c ≤ 1 := by
  have hCA : 0 < C₀ * A := mul_pos hC₀ hA
  have h2G : 0 < 2 * G + 1 := by linarith
  refine ⟨min (min 1 cb) (min (c₀ / A) (min (1 / (C₀ * A)) (min (1 / D) (1 / (2 * G + 1))))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · have h : min (min 1 cb) (min (c₀ / A) (min (1 / (C₀ * A)) (min (1 / D) (1 / (2 * G + 1))))) ≤ c₀ / A :=
      (min_le_right _ _).trans (min_le_left _ _)
    exact (le_div_iff₀ hA).1 h
  · have h : min (min 1 cb) (min (c₀ / A) (min (1 / (C₀ * A)) (min (1 / D) (1 / (2 * G + 1))))) ≤
        1 / (C₀ * A) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have := (le_div_iff₀ hCA).1 h
    nlinarith
  · have h : min (min 1 cb) (min (c₀ / A) (min (1 / (C₀ * A)) (min (1 / D) (1 / (2 * G + 1))))) ≤ 1 / D :=
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    exact (le_div_iff₀ hD).1 h
  · have h : min (min 1 cb) (min (c₀ / A) (min (1 / (C₀ * A)) (min (1 / D) (1 / (2 * G + 1))))) ≤
        1 / (2 * G + 1) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have := (le_div_iff₀ h2G).1 h
    have hc0 : 0 < min (min 1 cb) (min (c₀ / A) (min (1 / (C₀ * A)) (min (1 / D) (1 / (2 * G + 1))))) := by
      positivity
    nlinarith
theorem remainder_le_bound {K Lr Mh Db β r : ℝ} (_hL : 0 ≤ Lr) (hM : 0 ≤ Mh) (_hβ : 0 ≤ β) (_hr : 0 ≤ r)
    (hG : 4 * K ^ 2 * (Lr ^ 4 * Mh * 8 ^ 4 + 18 * Db ^ 2 * (Lr ^ 2 * Mh * 8 ^ 2) + 64 * Lr ^ 2 + 1) *
      (β ^ 2 + r ^ 2) ≤ 1) :
    4 * K ^ 2 * (Lr ^ 4 * Mh * (8 * β) ^ 4 + (18 * Db ^ 2 * r ^ 2) * (Lr ^ 2 * Mh * (8 * β) ^ 2) +
      (Lr * (8 * β)) ^ 2 * β ^ 2 + β ^ 4) ≤ β ^ 2 := by
  set a := Lr ^ 4 * Mh * 8 ^ 4 with ha
  set b := 18 * Db ^ 2 * (Lr ^ 2 * Mh * 8 ^ 2) with hb
  set d := 64 * Lr ^ 2 with hd
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hd0 : 0 ≤ d := by positivity
  have hK : 0 ≤ 4 * K ^ 2 := by positivity
  have e : Lr ^ 4 * Mh * (8 * β) ^ 4 + (18 * Db ^ 2 * r ^ 2) * (Lr ^ 2 * Mh * (8 * β) ^ 2) +
      (Lr * (8 * β)) ^ 2 * β ^ 2 + β ^ 4 = β ^ 2 * (a * β ^ 2 + b * r ^ 2 + d * β ^ 2 + β ^ 2) := by
    simp only [ha, hb, hd]
    ring
  rw [e]
  have h1 : a * β ^ 2 + b * r ^ 2 + d * β ^ 2 + β ^ 2 ≤ (a + b + d + 1) * (β ^ 2 + r ^ 2) := by
    nlinarith [mul_nonneg ha0 (sq_nonneg r), mul_nonneg hb0 (sq_nonneg β), mul_nonneg hd0 (sq_nonneg r), sq_nonneg r]
  have h2 : 4 * K ^ 2 * (a * β ^ 2 + b * r ^ 2 + d * β ^ 2 + β ^ 2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left h1 hK).trans (by rw [← mul_assoc]; exact hG)
  calc 4 * K ^ 2 * (β ^ 2 * (a * β ^ 2 + b * r ^ 2 + d * β ^ 2 + β ^ 2))
      = β ^ 2 * (4 * K ^ 2 * (a * β ^ 2 + b * r ^ 2 + d * β ^ 2 + β ^ 2)) := by ring
    _ ≤ β ^ 2 * 1 := mul_le_mul_of_nonneg_left h2 (sq_nonneg β)
    _ = β ^ 2 := mul_one _
theorem levelScale_le_one (hodd : Odd F.blockSide) (j : ℕ) : levelScale F j ≤ 1 := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.levelScale_le_one <;> assumption
theorem levelScale_nonneg (j : ℕ) : 0 ≤ levelScale F j := by apply _root_.YangMills.Construction.ReferenceBounds.zero_le_levelScale <;> assumption
theorem levelScale_mul_blockSide_pow (hodd : Odd F.blockSide) (j : ℕ) :
    levelScale F j * ((F.blockSide ^ (F.top - j) : ℕ) : ℝ) = 1 := by
  have hL : (F.blockSide : ℝ) ≠ 0 := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
    exact this.ne'
  unfold levelScale
  push_cast
  rw [← mul_pow]
  rw [one_div, inv_mul_cancel₀ hL, one_pow]
theorem card_innerBonds_cellBall_scale_le (hodd : Odd F.blockSide) (S : Finset F.Cell) (z : F.Cell) (j : ℕ)
    (Db r : ℝ) (_hr : 0 ≤ r) (_hD : 0 ≤ Db) :
    (Db * r * levelScale F j ^ 2) ^ 4 * ((innerBonds (cellBall S z 1) j).card : ℝ) ≤ (18 * Db ^ 2 * r ^ 2) ^ 2 := by
  have h1 := card_innerBonds_le hodd (cellBall S z 1) j
  have h2 := card_cellBall_one_le S z
  set M : ℝ := ((F.blockSide ^ (F.top - j) : ℕ) : ℝ) with hM
  have h3 : ((innerBonds (cellBall S z 1) j).card : ℝ) ≤ 324 * M ^ 4 := by
    have : (innerBonds (cellBall S z 1) j).card ≤ 4 * (81 * (F.blockSide ^ (F.top - j)) ^ 4) :=
      h1.trans (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right _ h2))
    have h4 : ((innerBonds (cellBall S z 1) j).card : ℝ) ≤ ((4 * (81 * (F.blockSide ^ (F.top - j)) ^ 4) : ℕ) : ℝ) := by
      exact_mod_cast this
    refine h4.trans (le_of_eq ?_)
    rw [hM]
    push_cast
    ring
  have hl := levelScale_mul_blockSide_pow (F := F) hodd j
  rw [← hM] at hl
  have hl0 := levelScale_nonneg (F := F) j
  have hl1 := levelScale_le_one (F := F) hodd j
  set l := levelScale F j with hldef
  have hl4 : l ^ 4 ≤ 1 := pow_le_one₀ hl0 hl1
  have e : (Db * r * l ^ 2) ^ 4 * (324 * M ^ 4) = 324 * (Db * r) ^ 4 * l ^ 4 * (l * M) ^ 4 := by ring
  calc (Db * r * l ^ 2) ^ 4 * ((innerBonds (cellBall S z 1) j).card : ℝ) ≤ (Db * r * l ^ 2) ^ 4 * (324 * M ^ 4) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 324 * (Db * r) ^ 4 * l ^ 4 := by rw [e, hl, one_pow, mul_one]
    _ ≤ 324 * (Db * r) ^ 4 * 1 := mul_le_mul_of_nonneg_left hl4 (by positivity)
    _ = (18 * Db ^ 2 * r ^ 2) ^ 2 := by ring
theorem bounds_of_localNorm_le (hodd : Odd F.blockSide) (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (z : F.Cell) (β : ℝ) (hβ : 0 ≤ β) (hN : localNorm S R U (oneSiteWeights F) z ≤ β) :
    ∑ b ∈ innerBonds (cellBall S z 1) 0, ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4 ≤ β ^ 4 ∧
      ∀ j, j + 1 < F.top → ∑ c ∈ innerBonds (cellBall S z 1) (j + 1), ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 ≤ β ^ 2 := by
  have hN' := (Real.sqrt_le_iff.1 hN).2
  unfold localNormSq oneSiteWeights at hN'
  simp only [one_mul] at hN'
  have hA : 0 ≤ Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, ‖U.fine b.1 b.2‖ ^ 4) := Real.sqrt_nonneg _
  have hB : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, ‖linearizedCurl (R 0) U.fine p‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hC : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      ‖U.coarse j c.1 c.2‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨?_, ?_⟩
  · have h1 : Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, ‖U.fine b.1 b.2‖ ^ 4) ≤ β ^ 2 := by linarith
    have h2 := (Real.sqrt_le_iff.1 h1).2
    have h3 : ∑ b ∈ innerBonds (cellBall S z 1) 0, ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4 ≤
        ∑ b ∈ bondsOver S (cellBall S z 3) 0, ‖U.fine b.1 b.2‖ ^ 4 :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => mem_bondsOver_of_mem_innerBonds_cellBall hodd S z 0 hb)
        fun _ _ _ => by positivity
    refine h3.trans (h2.trans (le_of_eq ?_))
    ring
  · intro j hj
    have h1 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        ‖U.coarse j c.1 c.2‖ ^ 2 ≤ β ^ 2 := by
      linarith
    have hmem : j ∈ Finset.range (F.top - 1) := Finset.mem_range.2 (by omega)
    have h2 := Finset.single_le_sum
      (f := fun j => ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1), ‖U.coarse j c.1 c.2‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hmem
    have h3 : ∑ c ∈ innerBonds (cellBall S z 1) (j + 1), ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 ≤
        ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1), ‖U.coarse j c.1 c.2‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun b hb => mem_bondsOver_of_mem_innerBonds_cellBall hodd S z (j + 1) hb) fun _ _ _ => by positivity
    exact h3.trans (h2.trans h1)
theorem mul_sq_add_sq_le_one {G c β r : ℝ} (hG0 : 0 ≤ G) (hcG : 2 * G * c ≤ 1) (hc1 : c ≤ 1) (hβ0 : 0 ≤ β)
    (hβc : β ≤ c) (hr0 : 0 ≤ r) (hrc : r ≤ c) : G * (β ^ 2 + r ^ 2) ≤ 1 := by
  have hb2 : β ^ 2 ≤ c := by nlinarith
  have hr2 : r ^ 2 ≤ c := by nlinarith
  have : G * (β ^ 2 + r ^ 2) ≤ G * (2 * c) := mul_le_mul_of_nonneg_left (by linarith) hG0
  linarith
theorem chartGap_zero (R : F.FieldChain) (U : ChainChart F) (x : F.Site 0) (i : Fin 4) :
    chartGap R U 0 x i = expUnit (U.fine x i) := by
  simp [chartGap, chartField]
end Levels
set_option maxHeartbeats 1000000 in
theorem levelGapNearCell_holds (hMean : contourMeanFirstOrderStatement)
    (hB : referenceBoundsStatement) : levelGapNearCellStatement := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hM⟩ := hMean
  obtain ⟨Db, cb, L1, hDb, hcb, hBd⟩ := hB
  refine ⟨8, by norm_num, max L1 3, fun L hL hge => ?_⟩
  have hL1 : L1 ≤ L := le_of_max_le_left hge
  have hL3 : 3 ≤ L := le_of_max_le_right hge
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL3
  obtain ⟨c, hc0, hc1, hccb, hcA, hcC, hcD, hcG⟩ :=
    exists_small_threshold (A := 8 * (L : ℝ) + Db + 1) (D := 2 + 40 * (L : ℝ))
    (G := 4 * (C₀ + 10) ^ 2 * ((L : ℝ) ^ 4 * (16 * ((hullBox L).card : ℝ)) * 8 ^ 4 +
      18 * Db ^ 2 * ((L : ℝ) ^ 2 * (16 * ((hullBox L).card : ℝ)) * 8 ^ 2) + 64 * (L : ℝ) ^ 2 + 1))
    hC₀ hc₀ hcb (by positivity) (by positivity) (by positivity)
  refine ⟨c, hc0, ?_⟩
  intro F m S hFL hamb hm hreg r V hr0 hrc hcold U z β hz hβ0 hβc hN
  subst hFL
  set R := referenceFieldChain S V with hR
  set B := cellBall S z 1 with hBdef
  have hodd : Odd F.blockSide := hL
  have hBS : B ⊆ S := cellBall_subset S z 1
  obtain ⟨-, -, c3, -, c5, -⟩ := hBd F m S hodd hL1 hamb hm hreg r V hr0 (hrc.trans hccb) hcold
  obtain ⟨hU4, hMu⟩ := bounds_of_localNorm_le hodd S R U z β hβ0 hN
  have hβ1 : β ≤ 1 := hβc.trans hc1
  have hr1 : r ≤ 1 := hrc.trans hc1
  have hu1 : ∀ b ∈ innerBonds B 0, ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ≤ 1 := by
    intro b hb
    have h1 := Finset.single_le_sum (f := fun b : F.Site 0 × Fin 4 => ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4)
      (fun _ _ => by positivity) hb
    exact (le_of_pow_four_le_pow_four (norm_nonneg _) hβ0 (h1.trans hU4)).trans hβ1
  have hform0 : ∑ b ∈ innerBonds B 0, ‖levelForm R U 0 b.1 b.2‖ ^ 4 ≤ β ^ 4 := by
    refine le_trans (Finset.sum_le_sum fun b _ => ?_) hU4
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 4
    have : levelForm R U 0 b.1 b.2 = pureComponent ((expUnit (U.fine b.1 b.2) : UnitQuaternion) : ℍ[ℝ]) := by
      rw [← chartGap_zero]
      rfl
    rw [this]
    exact norm_pureComponent_expUnit_le _
  have hcar : ∀ j, j ≤ F.top → ∑ b ∈ innerBonds B j, ‖carriedForm R (levelForm R U 0) j b.1 b.2‖ ^ 4 ≤ β ^ 4 :=
    fun j hj => (sum_carriedForm_pow_four_le hodd B R (levelForm R U 0) j hj).trans hform0
  have main : ∀ j, j < F.top → ∑ b ∈ innerBonds B j, normSubOne (chartGap R U j b.1 b.2) ^ 4 ≤ (8 * β) ^ 4 ∧
      ∑ b ∈ innerBonds B j, ‖residualForm R U j b.1 b.2‖ ^ 2 ≤ (3 * β) ^ 2 := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · have h1 : ∀ b ∈ innerBonds B 0, normSubOne (chartGap R U 0 b.1 b.2) ^ 4 ≤
            16 * ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4 := by
          intro b hb
          rw [chartGap_zero]
          have := pow_le_pow_left₀ (norm_nonneg _ : 0 ≤ normSubOne (expUnit (U.fine b.1 b.2)))
            (norm_expUnit_sub_one_le _ (hu1 b hb)) 4
          calc _ ≤ (2 * ‖(U.fine b.1 b.2 : ℍ[ℝ])‖) ^ 4 := this
            _ = _ := by ring
        refine (Finset.sum_le_sum h1).trans ?_
        rw [← Finset.mul_sum]
        have := mul_le_mul_of_nonneg_left hU4 (by norm_num : (0 : ℝ) ≤ 16)
        refine this.trans ?_
        have hb4 : 0 ≤ β ^ 4 := by positivity
        nlinarith
      · have : ∀ b ∈ innerBonds B 0, ‖residualForm R U 0 b.1 b.2‖ ^ 2 = 0 := by
          intro b _
          simp [residualForm, carriedForm]
        rw [Finset.sum_eq_zero this]
        positivity
    | succ j ih =>
      intro hj
      obtain ⟨i1, i2⟩ := ih (by omega)
      have hjn : j < F.top := by omega
      set l := levelScale F (j + 1) with hl
      have hl0 : 0 ≤ l := levelScale_nonneg _
      have hl1 : l ≤ 1 := levelScale_le_one hodd _
      set ε := Db * r * l ^ 2 with hε
      have hε0 : 0 ≤ ε := by positivity
      have hεD : ε ≤ Db * r := by
        have : l ^ 2 ≤ 1 := pow_le_one₀ hl0 hl1
        have h0 : 0 ≤ Db * r := by positivity
        calc ε = (Db * r) * l ^ 2 := rfl
          _ ≤ (Db * r) * 1 := mul_le_mul_of_nonneg_left this h0
          _ = _ := mul_one _
      have hLn : (0 : ℝ) ≤ (F.blockSide : ℝ) := by positivity
      have hsum : (F.blockSide : ℝ) * (8 * β) + ε ≤ c * (8 * (F.blockSide : ℝ) + Db + 1) := by
        have a1 := mul_le_mul_of_nonneg_left hβc hLn
        have a2 := mul_le_mul_of_nonneg_left hrc hDb.le
        have a3 : c * (8 * (F.blockSide : ℝ) + Db + 1) = 8 * ((F.blockSide : ℝ) * c) + Db * c + c := by ring
        rw [a3]
        linarith
      have hsum0 : 0 ≤ (F.blockSide : ℝ) * (8 * β) := by positivity
      refine level_succ_bounds (C₀ := C₀) (c₀ := c₀) hM hC₀ hodd hL3 B R U j hj ε β (18 * Db ^ 2 * r ^ 2) hε0 hβ0
        (by positivity) (by linarith) (by linarith) ((mul_le_mul_of_nonneg_left hsum hC₀.le).trans hcC) ?_ hβ1
        ?_ ?_ ?_ ?_ (hMu j hj) i1 i2 (hcar (j + 1) hj.le)
      · have : (2 + 40 * (F.blockSide : ℝ)) * β ≤ 1 := by
          have h0 : 0 ≤ 2 + 40 * (F.blockSide : ℝ) := by positivity
          calc (2 + 40 * (F.blockSide : ℝ)) * β ≤ (2 + 40 * (F.blockSide : ℝ)) * c :=
                mul_le_mul_of_nonneg_left hβc h0
            _ = c * (2 + 40 * (F.blockSide : ℝ)) := mul_comm _ _
            _ ≤ 1 := hcD
        linarith
      · intro c' hc' h hh π
        exact c5 j hjn c' (innerBonds_mono hBS _ hc') h hh π
      · intro c' hc'
        have h1 := c3 j hj c' (innerBonds_mono hBS _ hc')
        refine le_trans h1 ?_
        have h2 : l ^ 3 ≤ l ^ 2 := pow_le_pow_of_le_one hl0 hl1 (by norm_num)
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      · exact card_innerBonds_cellBall_scale_le hodd S z (j + 1) Db r hr0.le hDb.le
      · have hG : 4 * (C₀ + 10) ^ 2 * ((F.blockSide : ℝ) ^ 4 * (16 * ((hullBox F.blockSide).card : ℝ)) * 8 ^ 4 +
            18 * Db ^ 2 * ((F.blockSide : ℝ) ^ 2 * (16 * ((hullBox F.blockSide).card : ℝ)) * 8 ^ 2) +
            64 * (F.blockSide : ℝ) ^ 2 + 1) * (β ^ 2 + r ^ 2) ≤ 1 := by
          exact mul_sq_add_sq_le_one (by positivity) hcG hc1 hβ0 hβc hr0.le hrc
        exact remainder_le_bound (by positivity) (by positivity) hβ0 hr0.le hG
  intro j hj
  have h1 := (main j hj).1
  refine ⟨h1, ?_⟩
  refine le_trans ?_ h1
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun b hb => mem_innerBonds_cellBall_of_mem_bondsOver hamb hodd S z hj.le hb) fun _ _ _ => by positivity
end YangMills.Construction.LevelGaps
end

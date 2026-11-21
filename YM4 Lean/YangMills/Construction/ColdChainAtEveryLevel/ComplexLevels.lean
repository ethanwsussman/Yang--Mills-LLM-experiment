import YangMills.Construction.ColdChainAtEveryLevel.ColdnessOfTheFieldBelowTheTopProof
import YangMills.Construction.ColdChainAtEveryLevel.ComplexRemainders
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.ComplexLevels
open YangMills.Construction.BlockAverages YangMills.Construction.ComplexifiedQuaternions YangMills.Construction.ComplexContours YangMills.Construction.ComplexRemainders YangMills.Construction.ComplexChainStep YangMills.Construction.BlockLines YangMills.Construction.LatticePaths YangMills.Construction.LatticeFractionalIntegration YangMills.Construction.FlatPairing
variable {F : BlockFrame} {j : ℕ}
theorem invSqrt_one : invSqrt 1 = 1 := by simp [invSqrt]
theorem unitPart_of_det_eq_one {q : ComplexQuat} (hdet : q.det = 1) : unitPart q = q := by
  have hq : q ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  rw [unitPart, if_neg hq, hdet, invSqrt_one, one_smul]
theorem complexPathHolonomy_congr {X X' : F.ComplexField j} {x : F.Site j} {l : List PathStep}
    (hX : PathBondsSatisfy (fun b i => X b i = X' b i) x l) :
    complexPathHolonomy X x l = complexPathHolonomy X' x l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    simp only [complexPathHolonomy]
    rw [ih hX.2]
    congr 1
    have h1 := hX.1
    rcases hs : st.2 with _ | _
    · simp only [crossedBond, hs, Bool.false_eq_true, if_false] at h1
      simp only [complexLinkValue, hs, Bool.false_eq_true, if_false, h1]
    · simp only [crossedBond, hs, if_true] at h1
      simp only [complexLinkValue, hs, if_true, h1]
def HoldsOnHull (c : F.Site (j + 1) × Fin 4) (Q : F.Site j → Fin 4 → Prop) : Prop :=
  (∀ h ∈ centredCube F.blockSide, ∀ k, h + Pi.single k 1 ∈ centredCube F.blockSide →
    Q (refineSite c.1 + siteOfCoords j h) k ∧
      Q (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k) ∧
  ∀ h ∈ centredCube F.blockSide, ∀ r ∈ Finset.range F.blockSide,
    Q (lineBond c h r).1 (lineBond c h r).2
theorem complexGaugedContourAverage_congr (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {X X' : F.ComplexField j} (R : F.GaugeField j)
    {c : F.Site (j + 1) × Fin 4} (hX : HoldsOnHull c (fun b i => X b i = X' b i)) :
    complexGaugedContourAverage X (complexBalancingGauge X R) c =
      complexGaugedContourAverage X' (complexBalancingGauge X' R) c := by
  have hleg : ∀ g ∈ centredCube F.blockSide, ∀ π, complexPathHolonomy X (refineSite c.1) (axisPath g π) =
      complexPathHolonomy X' (refineSite c.1) (axisPath g π) := fun g hg π =>
    complexPathHolonomy_congr
      (pathBondsSatisfy_axisPath _ hodd.pos (fun v hv k hk => (hX.1 v hv k hk).1) hg π)
  have hleg' : ∀ g ∈ centredCube F.blockSide, ∀ π,
      complexPathHolonomy X (refineSite (c.1 + unitStep (j + 1) c.2)) (axisPath g π) =
      complexPathHolonomy X' (refineSite (c.1 + unitStep (j + 1) c.2)) (axisPath g π) := fun g hg π =>
    complexPathHolonomy_congr
      (pathBondsSatisfy_axisPath _ hodd.pos (fun v hv k hk => (hX.1 v hv k hk).2) hg π)
  have hline : ∀ g ∈ centredCube F.blockSide,
      complexPathHolonomy X (refineSite c.1 + siteOfCoords j g) (List.replicate F.blockSide (c.2, true)) =
      complexPathHolonomy X' (refineSite c.1 + siteOfCoords j g)
        (List.replicate F.blockSide (c.2, true)) := fun g hg =>
    complexPathHolonomy_congr (pathBondsSatisfy_replicate _ _ _ fun r hr => hX.2 g hg r hr)
  have hc : complexContourAverage X c = complexContourAverage X' c := by
    simp only [complexContourAverage]
    congr 1
    refine Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun π _ => ?_
    rw [complexPathHolonomy_bondContour hj, complexPathHolonomy_bondContour hj, hleg g hg π,
      hleg' g hg π, hline g hg]
  have hk : complexBalancingGauge X R c.1 = complexBalancingGauge X' R c.1 := by
    simp only [complexBalancingGauge, complexRelativePathAverage]
    congr 3
    refine Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun π _ => ?_
    rw [hleg g hg π]
  have hk' : complexBalancingGauge X R (c.1 + unitStep (j + 1) c.2) =
      complexBalancingGauge X' R (c.1 + unitStep (j + 1) c.2) := by
    simp only [complexBalancingGauge, complexRelativePathAverage]
    congr 3
    refine Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun π _ => ?_
    rw [hleg' g hg π]
  simp only [complexGaugedContourAverage, hc, hk, hk']
theorem liftedField_linkDeviation {X : F.ComplexField j} {R : F.GaugeField j} {b : F.Site j} {i : Fin 4}
    (hdet : (X b i).det = 1) : liftedField R (linkDeviation X R) b i = X b i := by
  have h1 : (1 + linkDeviation X R b i) = X b i * ofUnit (R b i)⁻¹ := by
    rw [linkDeviation, add_sub_cancel]
  have h2 : (1 + linkDeviation X R b i).det = 1 := by
    rw [h1, Matrix.det_mul, hdet, det_ofUnit, one_mul]
  rw [liftedField, unitPart_of_det_eq_one h2, h1, mul_assoc, ofUnit_inv_mul, mul_one]
theorem complexGaugedContourAverage_eq_liftedBondMean (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {X : F.ComplexField j} {R : F.GaugeField j}
    {c : F.Site (j + 1) × Fin 4} (hX : HoldsOnHull c (fun b i => (X b i).det = 1)) :
    complexGaugedContourAverage X (complexBalancingGauge X R) c = liftedBondMean R c (linkDeviation X R) := by
  refine complexGaugedContourAverage_congr hodd hj R ⟨fun g hg k hk => ?_, fun g hg r hr => ?_⟩
  · exact ⟨(liftedField_linkDeviation (hX.1 g hg k hk).1).symm,
      (liftedField_linkDeviation (hX.1 g hg k hk).2).symm⟩
  · exact (liftedField_linkDeviation (hX.2 g hg r hr)).symm
def levelDeviation (R : F.FieldChain) (W : ComplexChainChart F) (j : ℕ) : F.Site j → Fin 4 → ComplexQuat :=
  linkDeviation (complexChartField R W j) (R j)
def levelSource (W : ComplexChainChart F) (j : ℕ) (y : F.Site (j + 1)) (i : Fin 4) : ComplexQuat :=
  unitExp (complexifiedImaginary (W.re.coarse j y i) (W.im.coarse j y i))
theorem levelDeviation_succ (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) (R : F.FieldChain)
    (W : ComplexChainChart F) {c : F.Site (j + 1) × Fin 4}
    (hdet : HoldsOnHull c (fun b i => (complexChartField R W j b i).det = 1)) :
    levelDeviation R W (j + 1) c.1 c.2 = levelSource W j c.1 c.2 *
      conjByUnit (referenceDefect R j c) (1 + purePart (transportedAverage (R j) (levelDeviation R W j) c) +
        unitRemainder (R j) c (levelDeviation R W j)) - 1 := by
  have hm := complexGaugedContourAverage_eq_liftedBondMean hodd hj
    (X := complexChartField R W j) (R := R j) hdet
  set w : UnitQuaternion := polarUnit (contourAverage (R j) c) with hw
  set m : UnitQuaternion := referenceDefect R j c with hm'
  have hR : R (j + 1) c.1 c.2 = m * w := by
    simp only [hm', referenceDefect, hw, inv_mul_cancel_right]
  have e1 : 1 + purePart (transportedAverage (R j) (levelDeviation R W j) c) +
      unitRemainder (R j) c (levelDeviation R W j) =
      unitPart (liftedBondMean (R j) c (levelDeviation R W j)) * ofUnit w⁻¹ := by
    rw [unitRemainder]
    abel
  rw [e1]
  simp only [levelDeviation, linkDeviation, levelSource, complexChartField]
  rw [hR, ← hm, conjByUnit]
  simp only [mul_inv_rev, ofUnit_mul, mul_assoc]
  rfl
theorem det_complexChartField_of_norm_lt_one (R : F.FieldChain) (W : ComplexChainChart F) (j : ℕ)
    (x : F.Site j) (i : Fin 4) (hx : ‖levelDeviation R W j x i‖ < 1) :
    (complexChartField R W j x i).det = 1 := by
  cases j with
  | zero =>
    simp only [complexChartField, Matrix.det_mul, det_ofUnit, mul_one]
    exact det_unitExp _
  | succ j =>
    have h1 : (complexChartField R W (j + 1) x i).det ≠ 0 := by
      have e : complexChartField R W (j + 1) x i =
          (1 + levelDeviation R W (j + 1) x i) * ofUnit (R (j + 1) x i) :=
        field_eq_one_add_linkDeviation_mul _ _ _ _
      rw [e, Matrix.det_mul, det_ofUnit, mul_one]
      exact det_one_add_ne_zero_of_norm_lt_one hx
    have e2 : (complexChartField R W (j + 1) x i).det =
        (unitPart (complexGaugedContourAverage (complexChartField R W j)
          (complexBalancingGauge (complexChartField R W j) (R j)) (x, i))).det := by
      simp only [complexChartField, Matrix.det_mul, det_ofUnit, mul_one, det_unitExp, one_mul]
    rw [e2] at h1 ⊢
    set M := complexGaugedContourAverage (complexChartField R W j)
      (complexBalancingGauge (complexChartField R W j) (R j)) (x, i) with hM
    by_cases hq : M = 0
    · simp [unitPart, hq]
    · refine det_unitPart ?_
      intro hd
      apply h1
      rw [unitPart, if_neg hq, det_smul_complexQuat, hd, mul_zero]
def hullBondCount (L : ℕ) : ℝ := 8 * (L : ℝ) ^ 4 + (L : ℝ) ^ 5
theorem bondHullSum_le (hodd : Odd F.blockSide) {c : F.Site (j + 1) × Fin 4} {f : F.Site j → Fin 4 → ℝ}
    {t : ℝ} (ht : 0 ≤ t) (hf : HoldsOnHull c (fun b i => f b i ≤ t)) :
    bondHullSum c f ≤ hullBondCount F.blockSide * t := by
  have h1 : ∑ g ∈ centredCube F.blockSide, ∑ k : Fin 4, (if g + Pi.single k 1 ∈ centredCube F.blockSide then
      f (refineSite c.1 + siteOfCoords j g) k +
        f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j g) k else 0) ≤
      ∑ g ∈ centredCube F.blockSide, (8 * t) := by
    refine Finset.sum_le_sum fun g hg => ?_
    have : ∀ k ∈ (Finset.univ : Finset (Fin 4)), (if g + Pi.single k 1 ∈ centredCube F.blockSide then
        f (refineSite c.1 + siteOfCoords j g) k +
          f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j g) k else 0) ≤ 2 * t := by
      intro k _
      split_ifs with hk
      · have := hf.1 g hg k hk
        linarith [this.1, this.2]
      · linarith
    refine (Finset.sum_le_card_nsmul _ _ (2 * t) this).trans ?_
    simp
    linarith
  have h2 : ∑ g ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
      f (lineBond c g r).1 (lineBond c g r).2 ≤
      ∑ g ∈ centredCube F.blockSide, ((F.blockSide : ℝ) * t) := by
    refine Finset.sum_le_sum fun g hg => ?_
    refine (Finset.sum_le_card_nsmul _ _ t (hf.2 g hg)).trans ?_
    simp
  rw [Finset.sum_const, card_centredCube hodd] at h1 h2
  simp only [nsmul_eq_mul] at h1 h2
  push_cast at h1 h2
  unfold bondHullSum hullBondCount
  nlinarith
theorem mem_twoBlockHull_of_mem_centredCube {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) (i : Fin 4) :
    h ∈ twoBlockHull L i := by apply _root_.YangMills.Construction.BlockAverages.ColdBelowTop.mem_twoBlockHull_of_mem_centredCube <;> assumption
theorem shift_mem_twoBlockHull {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) (i : Fin 4) :
    (L : ℤ) • basisVector i + h ∈ twoBlockHull L i := by apply _root_.YangMills.Construction.BlockAverages.ColdBelowTop.smul_basisVector_add_mem_twoBlockHull <;> assumption
theorem holdsOnHull_of_innerBonds {D : Finset F.Cell} (hj : j < F.top) (hodd : Odd F.blockSide)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds D (j + 1)) {Q : F.Site j → Fin 4 → Prop}
    (hQ : ∀ b ∈ innerBonds D j, Q b.1 b.2) : HoldsOnHull c Q := by
  refine ⟨fun g hg k hk => ⟨?_, ?_⟩, fun g hg r hr => ?_⟩
  · exact hQ _ (bond_mem_innerBonds_of_mem_twoBlockHull hj hodd c hc g k
      (mem_twoBlockHull_of_mem_centredCube hg _) (mem_twoBlockHull_of_mem_centredCube hk _))
  · have e : refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j g =
        refineSite c.1 + siteOfCoords j ((F.blockSide : ℤ) • basisVector c.2 + g) := by
      rw [refineSite_add_unitStep hj, siteOfCoords_add, add_assoc]
    rw [e]
    refine hQ _ (bond_mem_innerBonds_of_mem_twoBlockHull hj hodd c hc _ k (shift_mem_twoBlockHull hg _) ?_)
    have e2 : (F.blockSide : ℤ) • basisVector c.2 + g + basisVector k =
        (F.blockSide : ℤ) • basisVector c.2 + (g + Pi.single k 1) := by
      rw [add_assoc]
      rfl
    rw [e2]
    exact shift_mem_twoBlockHull hk _
  · exact hQ _ (lineBond_mem_innerBonds hj hodd c hc g hg r (Finset.mem_range.1 hr))
theorem norm_levelDeviation_succ_le (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) (R : F.FieldChain)
    (W : ComplexChainChart F) {c : F.Site (j + 1) × Fin 4} {σ t : ℝ} (hσ : σ ≤ 1 / 64) (ht : 0 ≤ t)
    (hsm : 8 * (F.blockSide : ℝ) * (hullBondCount F.blockSide * t) ≤ 1 / 1024)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy (R j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ)
    (hb : HoldsOnHull c (fun b i => ‖levelDeviation R W j b i‖ ≤ t)) :
    ‖levelDeviation R W (j + 1) c.1 c.2‖ ≤ ‖levelSource W j c.1 c.2 - 1‖ +
        lineBlockAverage (fun x i => ‖levelDeviation R W j x i‖) c +
      200000 * (F.blockSide : ℝ) ^ 2 * hullBondCount F.blockSide ^ 2 * (t ^ 2 + σ * t) +
      ‖levelSource W j c.1 c.2 - 1‖ * (F.blockSide * t +
        200000 * (F.blockSide : ℝ) ^ 2 * hullBondCount F.blockSide ^ 2 * (t ^ 2 + σ * t)) := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hH1 : 1 ≤ hullBondCount F.blockSide := by
    unfold hullBondCount
    have : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ 4 := one_le_pow₀ hL1
    have : 0 ≤ (F.blockSide : ℝ) ^ 5 := by positivity
    linarith
  have hσ0 : 0 ≤ σ := by
    have h0 : (0 : Lattice4) ∈ centredCube F.blockSide := by
      rw [mem_centredCube_iff]
      intro i
      have := hodd.pos
      simp only [Pi.zero_apply]
      omega
    exact (norm_nonneg _).trans (href 0 h0 1)
  set H := hullBondCount F.blockSide with hH
  set x := levelDeviation R W j with hx
  set N := bondHullNorm c x with hN
  have hN0 : 0 ≤ N := bondHullSum_nonneg c fun _ _ => norm_nonneg _
  have hNt : N ≤ H * t := bondHullSum_le hodd ht hb
  have ht1 : t < 1 := by
    have : t ≤ H * t := by nlinarith
    have h2 : H * t ≤ 8 * (F.blockSide : ℝ) * (H * t) := by
      have : 0 ≤ H * t := by positivity
      nlinarith
    linarith
  have hdet : HoldsOnHull c (fun b i => (complexChartField R W j b i).det = 1) := by
    refine ⟨fun g hg k hk => ?_, fun g hg r hr => ?_⟩
    · have := hb.1 g hg k hk
      exact ⟨det_complexChartField_of_norm_lt_one R W j _ _ (lt_of_le_of_lt this.1 ht1),
        det_complexChartField_of_norm_lt_one R W j _ _ (lt_of_le_of_lt this.2 ht1)⟩
    · exact det_complexChartField_of_norm_lt_one R W j _ _ (lt_of_le_of_lt (hb.2 g hg r hr) ht1)
  have hsmall : 8 * (F.blockSide : ℝ) * N ≤ 1 / 1024 := by
    have : 8 * (F.blockSide : ℝ) * N ≤ 8 * (F.blockSide : ℝ) * (H * t) := by
      apply mul_le_mul_of_nonneg_left hNt
      positivity
    linarith
  obtain ⟨-, hq, -⟩ := remainder_bounds hodd hj hσ hsmall href
  rw [levelDeviation_succ hodd hj R W hdet]
  set E := levelSource W j c.1 c.2 with hE
  set m := referenceDefect R j c with hm
  set P := purePart (transportedAverage (R j) x c) with hP
  set q := unitRemainder (R j) c x with hq'
  set K := 200000 * (F.blockSide : ℝ) ^ 2 * H ^ 2 * (t ^ 2 + σ * t) with hK
  have hqK : ‖q‖ ≤ K := by
    refine hq.trans ?_
    rw [hK]
    have a1 : N ^ 2 ≤ (H * t) ^ 2 := pow_le_pow_left₀ hN0 hNt 2
    have a2 : σ * N ≤ σ * (H * t) := mul_le_mul_of_nonneg_left hNt hσ0
    have a3 : σ * (H * t) ≤ H ^ 2 * (σ * t) := by
      have h0 : 0 ≤ σ * t := by positivity
      have h6 : H ≤ H ^ 2 := by nlinarith
      calc σ * (H * t) = H * (σ * t) := by ring
        _ ≤ H ^ 2 * (σ * t) := mul_le_mul_of_nonneg_right h6 h0
    have a4 : N ^ 2 + σ * N ≤ H ^ 2 * (t ^ 2 + σ * t) := by
      nlinarith
    calc 200000 * (F.blockSide : ℝ) ^ 2 * (N ^ 2 + σ * N) ≤
          200000 * (F.blockSide : ℝ) ^ 2 * (H ^ 2 * (t ^ 2 + σ * t)) :=
          mul_le_mul_of_nonneg_left a4 (by positivity)
      _ = _ := by ring
  have hPQ : ‖P‖ ≤ lineBlockAverage (fun x' i => ‖x x' i‖) c :=
    (norm_purePart_le _).trans (norm_transportedAverage_le hodd _ _ c)
  have hPt : lineBlockAverage (fun x' i => ‖x x' i‖) c ≤ F.blockSide * t := lineBlockAverage_le hodd hb.2
  have hid : E * conjByUnit m (1 + P + q) - 1 =
      (E - 1) + conjByUnit m (P + q) + (E - 1) * conjByUnit m (P + q) := by
    have : conjByUnit m (1 + P + q) = 1 + conjByUnit m (P + q) := by
      rw [add_assoc, conjByUnit_add, conjByUnit_one]
    rw [this]
    noncomm_ring
  rw [hid]
  have h1 := norm_add_le ((E - 1) + conjByUnit m (P + q)) ((E - 1) * conjByUnit m (P + q))
  have h2 := norm_add_le (E - 1) (conjByUnit m (P + q))
  have h3 := norm_mul_le (E - 1) (conjByUnit m (P + q))
  rw [norm_conjByUnit] at h2 h3
  have h4 := norm_add_le P q
  have h5 : ‖E - 1‖ * ‖P + q‖ ≤ ‖E - 1‖ * (F.blockSide * t + K) :=
    mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  linarith
def ContoursNearUnit (R : F.FieldChain) (D : Finset F.Cell) (C s : ℝ) : Prop :=
  ∀ j, j + 1 ≤ F.top → ∀ c ∈ innerBonds D (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π,
    ‖ofUnit (pathHolonomy (R j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
      (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤
      C * s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2
theorem inv_pow_le_one {L : ℕ} (hL : 1 ≤ L) (e : ℕ) : (1 / (L : ℝ)) ^ e ≤ 1 := by
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  exact pow_le_one₀ (by positivity) (by rw [div_le_one (by positivity)]; exact h1)
theorem level_bound_arith {K1 C₀ L t m A A3 σ : ℝ} (hK1 : 0 ≤ K1) (hC : 0 ≤ C₀) (hL : 0 ≤ L) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hm : 0 ≤ m) (hA : 0 ≤ A) (hA3 : 0 ≤ A3) (hσ0 : 0 ≤ σ) (hσA : σ = C₀ * A) (hσ1 : σ ≤ 1) :
    K1 * (t ^ 2 + σ * t) + m * (L * t + K1 * (t ^ 2 + σ * t)) ≤
      (3 * K1 + L) * (1 + C₀) * (t ^ 2 + (A + m + A3) * t) := by
  set K := (3 * K1 + L) * (1 + C₀) with hK
  have hLK : 3 * K1 + L ≤ K := by
    rw [hK]
    have : 0 ≤ (3 * K1 + L) * C₀ := by positivity
    nlinarith
  have hCK : K1 * C₀ ≤ K := by
    rw [hK]
    have h2 : 0 ≤ L * (1 + C₀) := by positivity
    have h3 : 0 ≤ K1 * (1 + C₀) := by positivity
    nlinarith
  have hKK : K1 ≤ K := by linarith
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have hσt : σ * t ≤ t := by nlinarith
  have b1 : K1 * (t ^ 2 + σ * t) ≤ K * t ^ 2 + K * (A * t) := by
    have e1 : K1 * (σ * t) = (K1 * C₀) * (A * t) := by
      rw [hσA]
      ring
    have e2 : K1 * t ^ 2 ≤ K * t ^ 2 := mul_le_mul_of_nonneg_right hKK (sq_nonneg t)
    have e3 : (K1 * C₀) * (A * t) ≤ K * (A * t) := mul_le_mul_of_nonneg_right hCK (by positivity)
    linarith [mul_add K1 (t ^ 2) (σ * t)]
  have b2 : m * (L * t + K1 * (t ^ 2 + σ * t)) ≤ K * (m * t) := by
    have e1 : L * t + K1 * (t ^ 2 + σ * t) ≤ K * t := by
      have e2 : K1 * (t ^ 2 + σ * t) ≤ K1 * (2 * t) :=
        mul_le_mul_of_nonneg_left (by linarith) hK1
      have e3 : (3 * K1 + L) * t ≤ K * t := mul_le_mul_of_nonneg_right hLK ht0
      have e4 : 0 ≤ K1 * t := by positivity
      linarith [add_mul (3 * K1) L t]
    calc m * (L * t + K1 * (t ^ 2 + σ * t)) ≤ m * (K * t) := mul_le_mul_of_nonneg_left e1 hm
      _ = K * (m * t) := by ring
  have b3 : 0 ≤ K * (A3 * t) := by
    have : 0 ≤ K := by positivity
    positivity
  have e5 : K * (t ^ 2 + (A + m + A3) * t) = K * t ^ 2 + K * (A * t) + K * (m * t) + K * (A3 * t) := by ring
  rw [e5]
  linarith
theorem quartic_levelDeviation_bound (hrec : UniformQuarticBoundAcrossLevels) (L : ℕ) (hodd : Odd L)
    (h5 : 5 ≤ L) {C₀ : ℝ} (hC : 0 ≤ C₀) : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (F : BlockFrame) (D : Finset F.Cell)
      (R : F.FieldChain) (W : ComplexChainChart F) (s B : ℝ), F.blockSide = L → D.card ≤ 81 →
      ContoursNearUnit R D C₀ s → 0 ≤ s → s ≤ c → 0 ≤ B → B ≤ c →
      Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D 0, ‖levelDeviation R W 0 b.1 b.2‖ ^ 4)) ≤ B →
      (∀ j, j + 1 < F.top →
        Real.sqrt (∑ c ∈ innerBonds D (j + 1), ‖levelSource W j c.1 c.2 - 1‖ ^ 2) ≤ B) →
      ∀ j, j < F.top →
        Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D j, ‖levelDeviation R W j b.1 b.2‖ ^ 4)) ≤ 4 * B := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hodd.pos
  set H := hullBondCount L with hH
  have hH1 : 1 ≤ H := by
    rw [hH]
    unfold hullBondCount
    have : (1 : ℝ) ≤ (L : ℝ) ^ 4 := one_le_pow₀ hL1
    have : 0 ≤ (L : ℝ) ^ 5 := by positivity
    linarith
  set K1 := 200000 * (L : ℝ) ^ 2 * H ^ 2 with hK1
  have hK10 : 0 ≤ K1 := by positivity
  set K := (3 * K1 + L) * (1 + C₀) with hK
  have hK0 : 0 ≤ K := by positivity
  set c0 : ℝ := 1 / (8192 * (L : ℝ) * H) with hc0
  have hc0pos : 0 < c0 := by positivity
  obtain ⟨c1, hc1, hrec'⟩ := hrec L 81 K c0 hodd h5 hK0 hc0pos
  refine ⟨min c1 (min 1 (1 / (64 * (C₀ + 1)))), by positivity, (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro F D R W s B hFL hD hnear hs0 hsc hB0 hBc h0 hsrc
  have hsc1 : s ≤ c1 := hsc.trans (min_le_left _ _)
  have hBc1 : B ≤ c1 := hBc.trans (min_le_left _ _)
  have hs64 : s ≤ 1 / (64 * (C₀ + 1)) := hsc.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hodd' : Odd F.blockSide := hFL ▸ hodd
  refine hrec' F D (fun j x i => ‖levelDeviation R W j x i‖) (fun j y i => ‖levelSource W j y i - 1‖) s B
    hFL hD hs0 hsc1 hB0 hBc1 (fun _ _ _ => norm_nonneg _) (fun _ _ _ => norm_nonneg _) h0 hsrc ?_
  intro j hj c hc t ht0 htc hmc hb
  have hLF : (F.blockSide : ℝ) = L := by rw [hFL]
  set σ : ℝ := C₀ * s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 with hσd
  have hl1 : ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_pow_le_one hodd'.pos _)
  have hσ0 : 0 ≤ σ := by positivity
  have hσle : σ ≤ C₀ * s := by
    rw [hσd]
    exact mul_le_of_le_one_right (by positivity) hl1
  have hσ64 : σ ≤ 1 / 64 := by
    refine hσle.trans ?_
    rw [le_div_iff₀ (by positivity)] at hs64
    nlinarith
  have hsm : 8 * (F.blockSide : ℝ) * (hullBondCount F.blockSide * t) ≤ 1 / 1024 := by
    rw [hFL]
    have e1 : 8 * (L : ℝ) * (H * c0) = 1 / 1024 := by
      rw [hc0]
      field_simp
      norm_num
    have : 8 * (L : ℝ) * (H * t) ≤ 8 * (L : ℝ) * (H * c0) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left htc (by positivity)
    linarith
  have hstep := norm_levelDeviation_succ_le hodd' (by omega : j + 1 ≤ F.top) R W hσ64 ht0 hsm
    (hnear j (by omega) c hc) hb
  have hHF : hullBondCount F.blockSide = H := by rw [hFL]
  rw [hHF, hLF, ← hK1] at hstep
  refine hstep.trans ?_
  have ht1 : t ≤ 1 := htc.trans (by
    rw [hc0, div_le_one (by positivity)]
    nlinarith)
  set m := ‖levelSource W j c.1 c.2 - 1‖ with hm
  have hm0 : 0 ≤ m := norm_nonneg _
  set Q := lineBlockAverage (fun x i => ‖levelDeviation R W j x i‖) c with hQ
  set A := s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 with hA
  set A3 := s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 3 with hA3
  have hA0 : 0 ≤ A := by positivity
  have hA30 : 0 ≤ A3 := by positivity
  have hσA : σ = C₀ * A := by
    rw [hσd, hA]
    ring
  have hσ1 : σ ≤ 1 := by linarith
  have hfin := level_bound_arith hK10 hC (by positivity : (0 : ℝ) ≤ L) ht0 ht1 hm0 hA0 hA30 hσ0 hσA hσ1
  rw [← hK] at hfin
  linarith
end YangMills.Construction.ComplexLevels
end

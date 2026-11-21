import YangMills.Construction.LawByMomentsOfTheFlow.FactsOfAReflection
import YangMills.Construction.LawByMomentsOfTheFlow.FourPointsNearALine
import YangMills.Construction.LawByMomentsOfTheFlow.IntegrandOfTheCyclicFormula
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAtTheLastFarLevelInALimitFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open CyclicFormula TestFunctions
private def reflect (u w : EuclideanFourSpace) : EuclideanFourSpace := w - ((2 / ‖u‖ ^ 2) * inner ℝ u w) • u
private theorem norm_reflect (u w : EuclideanFourSpace) (hu : u ≠ 0) : ‖reflect u w‖ = ‖w‖ := by
  have h1 : inner ℝ w (((2 / ‖u‖ ^ 2) * inner ℝ u w) • u) = (2 / ‖u‖ ^ 2) * inner ℝ u w * inner ℝ u w := by
    rw [inner_smul_right, real_inner_comm]
  have h : ‖reflect u w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [reflect, norm_sub_sq_real, h1, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
private theorem reflect_reflect (e w : EuclideanFourSpace) (he : e ≠ 0) : reflect e (reflect e w) = w := by
  have h1 : inner ℝ e (reflect e w) = - inner ℝ e w := by
    rw [reflect, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    ring
  have h2 : reflect e (reflect e w) = reflect e w - ((2 / ‖e‖ ^ 2) * inner ℝ e (reflect e w)) • e := rfl
  rw [h2, h1, mul_neg, neg_smul, sub_neg_eq_add, reflect, sub_add_cancel]
private theorem reflect_sub_reflect (e a b : EuclideanFourSpace) : reflect e a - reflect e b = reflect e (a - b) := by
  simp only [reflect, inner_sub_right, mul_sub, sub_smul]
  abel
private theorem norm_reflect_sub_reflect (e a b : EuclideanFourSpace) (he : e ≠ 0) :
    ‖reflect e a - reflect e b‖ = ‖a - b‖ := by
  rw [reflect_sub_reflect, norm_reflect _ _ he]
private theorem norm_reflect_sub_reflect_le (e u w : EuclideanFourSpace) (he : ‖e‖ = 1) (hu : u ≠ 0)
    (hn : 63 / 64 * ‖u‖ ^ 2 ≤ inner ℝ u e ^ 2) : ‖reflect u w - reflect e w‖ ≤ 1 / 4 * ‖w‖ := by
  have hU : 0 < ‖u‖ ^ 2 := by
    have := norm_pos_iff.mpr hu
    positivity
  set U := ‖u‖ ^ 2 with hUd
  set W := ‖w‖ ^ 2 with hWd
  set a := inner ℝ u w with ha
  set b := inner ℝ e w with hb
  set c := inner ℝ u e with hc
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have huu : inner ℝ u u = U := real_inner_self_eq_norm_sq u
  have hww : inner ℝ w w = W := real_inner_self_eq_norm_sq w
  have heu : inner ℝ e u = c := real_inner_comm _ _
  have hwe : inner ℝ w e = b := real_inner_comm _ _
  have hg : (a - b * c) ^ 2 ≤ (U - c ^ 2) * (W - b ^ 2) := by
    have h := real_inner_mul_inner_self_le (u - c • e) (w - b • e)
    have h1 : inner ℝ (u - c • e) (w - b • e) = a - b * c := by
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hee, ← ha, ← hb, ← hc]
      simp
      ring
    have h2 : inner ℝ (u - c • e) (u - c • e) = U - c ^ 2 := by
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hee, huu, heu, ← hc]
      simp
      ring
    have h3 : inner ℝ (w - b • e) (w - b • e) = W - b ^ 2 := by
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hee, hww, hwe, ← hb]
      simp
      ring
    rw [h1, h2, h3] at h
    nlinarith [h]
  have hW : 0 ≤ W := by positivity
  have hD : reflect u w - reflect e w = (2 * b) • e - ((2 / U) * a) • u := by
    simp only [reflect, he, ← hUd, ← ha, ← hb]
    have : (2 / (1 : ℝ) ^ 2) * b = 2 * b := by norm_num
    rw [this]
    abel
  have hsq : ‖reflect u w - reflect e w‖ ^ 2 = 4 * (b ^ 2 * U + a ^ 2 - 2 * a * b * c) / U := by
    have hi : inner ℝ ((2 * b) • e) (((2 / U) * a) • u) = (2 * b) * ((2 / U) * a) * c := by
      simp only [inner_smul_left, inner_smul_right, heu]
      simp
      ring
    have n1 : ‖(2 * b) • e‖ ^ 2 = 4 * b ^ 2 := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
      ring
    have n2 : ‖((2 / U) * a) • u‖ ^ 2 = ((2 / U) * a) ^ 2 * U := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [hD, norm_sub_sq_real, hi, n1, n2]
    field_simp
    ring
  have hmain : ‖reflect u w - reflect e w‖ ^ 2 ≤ (1 / 4 * ‖w‖) ^ 2 := by
    rw [hsq, div_le_iff₀ hU, mul_pow, ← hWd]
    have h1 : U - c ^ 2 ≤ U / 64 := by linarith
    have h2 : W * (U - c ^ 2) ≤ W * (U / 64) := mul_le_mul_of_nonneg_left h1 hW
    nlinarith [hg, h2]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hmain
private theorem norm_reflect_four_sub_le (e : EuclideanFourSpace) (he : ‖e‖ = 1) (u : Fin 4 → EuclideanFourSpace)
    (hu : ∀ c, u c ≠ 0) (hn : ∀ c, 63 / 64 * ‖u c‖ ^ 2 ≤ inner ℝ (u c) e ^ 2) (v : EuclideanFourSpace) :
    ‖reflect (u 0) (reflect (u 1) (reflect (u 2) (reflect (u 3) v))) - v‖ ≤ ‖v‖ := by
  have he0 : e ≠ 0 := by
    intro h
    rw [h, norm_zero] at he
    norm_num at he
  set v3 := reflect (u 3) v with h3
  set v2 := reflect (u 2) v3 with h2
  set v1 := reflect (u 1) v2 with h1
  set v0 := reflect (u 0) v1 with h0
  have n3 : ‖v3‖ = ‖v‖ := norm_reflect _ _ (hu 3)
  have n2 : ‖v2‖ = ‖v‖ := (norm_reflect _ _ (hu 2)).trans n3
  have n1 : ‖v1‖ = ‖v‖ := (norm_reflect _ _ (hu 1)).trans n2
  have a0 : ‖v0 - reflect e v1‖ ≤ 1 / 4 * ‖v‖ := by
    rw [← n1]
    exact norm_reflect_sub_reflect_le e _ _ he (hu 0) (hn 0)
  have a1 : ‖reflect e v1 - v2‖ ≤ 1 / 4 * ‖v‖ := by
    have := norm_reflect_sub_reflect_le e (u 1) v2 he (hu 1) (hn 1)
    rw [n2, ← norm_reflect_sub_reflect e _ _ he0, reflect_reflect e _ he0] at this
    exact this
  have a2 : ‖v2 - reflect e v3‖ ≤ 1 / 4 * ‖v‖ := by
    rw [← n3]
    exact norm_reflect_sub_reflect_le e _ _ he (hu 2) (hn 2)
  have a3 : ‖reflect e v3 - v‖ ≤ 1 / 4 * ‖v‖ := by
    have := norm_reflect_sub_reflect_le e (u 3) v he (hu 3) (hn 3)
    rw [← norm_reflect_sub_reflect e _ _ he0, reflect_reflect e _ he0] at this
    exact this
  have hsplit : v0 - v = (v0 - reflect e v1) + (reflect e v1 - v2) + (v2 - reflect e v3) + (reflect e v3 - v) := by abel
  rw [hsplit]
  have ht := (norm_add_le ((v0 - reflect e v1) + (reflect e v1 - v2) + (v2 - reflect e v3)) (reflect e v3 - v)).trans
    (add_le_add ((norm_add_le ((v0 - reflect e v1) + (reflect e v1 - v2)) (v2 - reflect e v3)).trans
      (add_le_add (norm_add_le (v0 - reflect e v1) (reflect e v1 - v2)) le_rfl)) le_rfl)
  linarith
private theorem inversionMatrix_mulVec (u w : EuclideanFourSpace) :
    (inversionMatrix u).mulVec (fun a => w a) = fun a => reflect u w a := by
  have hin : inner ℝ u w = ∑ i, u i * w i := by
    simp [PiLp.inner_apply, mul_comm]
  funext a
  simp only [Matrix.mulVec, dotProduct, inversionMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, reflect, PiLp.sub_apply, PiLp.smul_apply, hin, Fin.sum_univ_four, Matrix.one_apply]
  fin_cases a <;> simp <;> ring
private theorem inner_eq_dotProduct (v w : EuclideanFourSpace) :
    inner ℝ v w = (fun a => v a) ⬝ᵥ (fun a => w a) := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]
private theorem list_prod_ofFn_four (f : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ) :
    (List.ofFn f).prod = f 0 * (f 1 * (f 2 * f 3)) := by
  simp [List.ofFn_succ]
private theorem transpose_mul_self_of_involution (M X : Matrix (Fin 4) (Fin 4) ℝ) (hT : M.transpose = M)
    (hI : M * M = 1) (hX : X.transpose * X = 1) : (M * X).transpose * (M * X) = 1 := by
  rw [Matrix.transpose_mul, hT, Matrix.mul_assoc, ← Matrix.mul_assoc M, hI, Matrix.one_mul, hX]
private theorem exteriorSquareTrace_ge_three_of_near_identity
    (hE : ∀ A : Matrix (Fin 4) (Fin 4) ℝ, exteriorSquareTrace A = ((Matrix.trace A) ^ 2 - Matrix.trace (A * A)) / 2)
    (A : Matrix (Fin 4) (Fin 4) ℝ) (h1 : A.transpose * A = 1)
    (hv : ∀ v : Fin 4 → ℝ, 1 / 2 * (v ⬝ᵥ v) ≤ v ⬝ᵥ A.mulVec v) : 3 ≤ exteriorSquareTrace A := by
  have ht : 2 ≤ Matrix.trace A := by
    have hd : ∀ a, 1 / 2 ≤ A a a := by
      intro a
      have h := hv (Pi.single a 1)
      simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using h
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_four]
    linarith [hd 0, hd 1, hd 2, hd 3]
  have hs : Matrix.trace (A * A) ≤ 3 * Matrix.trace A - 8 := by
    have hsum : 1 / 2 * Matrix.trace ((A - 1).transpose * (A - 1)) ≤
        Matrix.trace ((A - 1).transpose * (A * (A - 1))) := by
      have hc : ∀ a, (fun i => (A - 1) i a) ⬝ᵥ (fun i => (A - 1) i a) = ((A - 1).transpose * (A - 1)) a a := by
        intro a
        simp only [dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
      have hd : ∀ a, (fun i => (A - 1) i a) ⬝ᵥ A.mulVec (fun i => (A - 1) i a) =
          ((A - 1).transpose * (A * (A - 1))) a a := by
        intro a
        simp only [dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec]
      simp only [Matrix.trace, Matrix.diag, Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [← hc, ← hd]
      exact hv _
    have e1 : (A - 1).transpose * (A - 1) = 1 - A.transpose - A + 1 := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, h1]
      simp only [Matrix.mul_one, Matrix.one_mul]
      abel
    have e2 : (A - 1).transpose * (A * (A - 1)) = A + A - 1 - A * A := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.one_mul,
        Matrix.mul_sub, Matrix.mul_one]
      abel
    have hone : Matrix.trace (1 : Matrix (Fin 4) (Fin 4) ℝ) = 4 := by
      simp [Matrix.trace_one]
    rw [e1, e2] at hsum
    simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_transpose, hone] at hsum
    linarith
  rw [hE]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr ht)]
private theorem exteriorSquareTrace_prod_inversionMatrix_ge_three
    (hT : ∀ x : EuclideanFourSpace, (inversionMatrix x).transpose = inversionMatrix x)
    (hI : ∀ x : EuclideanFourSpace, inversionMatrix x * inversionMatrix x = 1)
    (hE : ∀ A : Matrix (Fin 4) (Fin 4) ℝ, exteriorSquareTrace A = ((Matrix.trace A) ^ 2 - Matrix.trace (A * A)) / 2)
    (e : EuclideanFourSpace) (he : ‖e‖ = 1) (u : Fin 4 → EuclideanFourSpace) (hu : ∀ c, u c ≠ 0)
    (hn : ∀ c, 63 / 64 * ‖u c‖ ^ 2 ≤ inner ℝ (u c) e ^ 2) :
    3 ≤ exteriorSquareTrace (List.ofFn fun c : Fin 4 => inversionMatrix (u c)).prod := by
  rw [list_prod_ofFn_four]
  refine exteriorSquareTrace_ge_three_of_near_identity hE _ ?_ ?_
  · refine transpose_mul_self_of_involution _ _ (hT _) (hI _)
      (transpose_mul_self_of_involution _ _ (hT _) (hI _) (transpose_mul_self_of_involution _ _ (hT _) (hI _) ?_))
    rw [hT, hI]
  · intro v
    set w : EuclideanFourSpace := WithLp.toLp 2 v with hw
    have hwv : (fun a => w a) = v := rfl
    set z := reflect (u 0) (reflect (u 1) (reflect (u 2) (reflect (u 3) w))) with hz
    have hmul : (inversionMatrix (u 0) * (inversionMatrix (u 1) * (inversionMatrix (u 2) * inversionMatrix (u 3)))).mulVec v =
        fun a => z a := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hwv]
      simp only [inversionMatrix_mulVec]
      rfl
    have hzn : ‖z‖ = ‖w‖ := by
      rw [hz, norm_reflect _ _ (hu 0), norm_reflect _ _ (hu 1), norm_reflect _ _ (hu 2), norm_reflect _ _ (hu 3)]
    have hnear := norm_reflect_four_sub_le e he u hu hn w
    have hsq : ‖z - w‖ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnear 2
    rw [norm_sub_sq_real, hzn] at hsq
    have hvv : v ⬝ᵥ v = ‖w‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_eq_dotProduct]
    have hzw : v ⬝ᵥ (fun a => z a) = inner ℝ z w := by
      rw [real_inner_comm, inner_eq_dotProduct]
    rw [hmul, hvv, hzw]
    linarith
private theorem supDist_le_dist (x y : EuclideanFourSpace) : supDist x y ≤ dist x y := by apply _root_.YangMills.SharedProofs.p2932 <;> assumption
private theorem ne_add_one_fin_four (c : Fin 4) : c ≠ c + 1 := by
  revert c
  decide
theorem nearlyCollinearPositivity (hF : InversionMatrixProperties) (hN : CycleIntegrandIntegrable) :
    nearlyCollinearPositivityStatement := by
  obtain ⟨hT, hI, -, -, -, hE, -⟩ := hF
  intro φ R d hd hS hpos hne e he hnear
  have hdist : ∀ i j, i ≠ j → ∀ x ∈ tsupport (φ i), ∀ y ∈ tsupport (φ j), d ≤ ‖x - y‖ := by
    intro i j hij x hx y hy
    rw [← dist_eq_norm]
    exact (hS.le_supDist i j hij x hx y hy).trans (supDist_le_dist x y)
  have htr : ∀ x : Fin 4 → EuclideanFourSpace, (∀ i, x i ∈ tsupport (φ i)) → ∀ σ : Equiv.Perm (Fin 4),
      3 ≤ exteriorSquareTrace (List.ofFn fun c : Fin 4 => inversionMatrix (x (σ c) - x (σ (c + 1)))).prod := by
    intro x hx σ
    have hij : ∀ c : Fin 4, σ c ≠ σ (c + 1) := fun c h => ne_add_one_fin_four c (σ.injective h)
    refine exteriorSquareTrace_prod_inversionMatrix_ge_three hT hI hE e he (fun c => x (σ c) - x (σ (c + 1)))
      (fun c h0 => ?_) fun c => ?_
    · have := hdist _ _ (hij c) _ (hx _) _ (hx _)
      rw [h0, norm_zero] at this
      linarith
    · exact hnear _ _ (hij c) _ (hx _) _ (hx _)
  refine ⟨fun x hx σ _ => htr x hx σ, ?_⟩
  have hR : 0 ≤ R := by
    obtain ⟨x, hx⟩ := hne 0
    exact (abs_nonneg _).trans (hS.abs_coord_le 0 x (subset_tsupport _ hx) 0)
  have hTF : IsSeparatedLipschitzFamily (2 * R) d φ := by
    refine ⟨fun i => ?_, hS.abs_le_one, fun i x hx => ?_, fun i j hij x hx y hy => ?_⟩
    · refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq]
      simpa using (hS.lipschitz i x y).trans (supDist_le_dist x y)
    · have hb := hS.abs_coord_le i x hx
      rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      simp only [Real.norm_eq_abs, Fin.sum_univ_four]
      have hs : ∀ a, |x a| ^ 2 ≤ R ^ 2 := fun a => pow_le_pow_left₀ (abs_nonneg _) (hb a) 2
      nlinarith [hs 0, hs 1, hs 2, hs 3]
    · exact (hS.le_supDist i j hij x hx y hy).trans (supDist_le_dist x y)
  have hterm : ∀ (σ : Equiv.Perm (Fin 4)) (x : Fin 4 → EuclideanFourSpace), (∀ i, φ i (x i) ≠ 0) →
      0 < (∏ i, φ i (x i)) * cycleKernel σ x := by
    intro σ x hx
    have hxs : ∀ i, x i ∈ tsupport (φ i) := fun i => subset_tsupport _ (hx i)
    have hij : ∀ c : Fin 4, σ c ≠ σ (c + 1) := fun c h => ne_add_one_fin_four c (σ.injective h)
    have hp : 0 < ∏ i, φ i (x i) :=
      Finset.prod_pos fun i _ => lt_of_le_of_ne (hpos i _) (hx i).symm
    have hq : 0 < ∏ c : Fin 4, (Real.pi ^ 2 * ‖x (σ c) - x (σ (c + 1))‖ ^ 4)⁻¹ := by
      refine Finset.prod_pos fun c _ => ?_
      have := hdist _ _ (hij c) _ (hxs _) _ (hxs _)
      have h0 : 0 < ‖x (σ c) - x (σ (c + 1))‖ := lt_of_lt_of_le hd this
      positivity
    have h3 := htr x hxs σ
    have h4 : 0 < exteriorSquareTrace (List.ofFn fun c : Fin 4 => inversionMatrix (x (σ c) - x (σ (c + 1)))).prod := by
      linarith
    exact mul_pos hp (mul_pos hq h4)
  have hnn : ∀ (σ : Equiv.Perm (Fin 4)),
      0 ≤ fun x : Fin 4 → EuclideanFourSpace => (∏ i, φ i (x i)) * cycleKernel σ x := by
    intro σ x
    by_cases hx : ∀ i, φ i (x i) ≠ 0
    · exact (hterm σ x hx).le
    · simp only [not_forall, not_not] at hx
      obtain ⟨i, hi⟩ := hx
      have : ∏ i, φ i (x i) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
      simp [this]
  have hcont : ∀ i, Continuous fun x : Fin 4 → EuclideanFourSpace => φ i (x i) := fun i =>
    (hTF.lipschitzWith_one i).continuous.comp (continuous_apply i)
  have hU : 0 < volume {x : Fin 4 → EuclideanFourSpace | ∀ i, φ i (x i) ≠ 0} := by
    have hop : IsOpen {x : Fin 4 → EuclideanFourSpace | ∀ i, φ i (x i) ≠ 0} := by
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (hcont i) continuous_const
    choose x0 hx0 using hne
    exact hop.measure_pos volume ⟨x0, hx0⟩
  have hint : ∀ σ : Equiv.Perm (Fin 4), 0 < ∫ x : Fin 4 → EuclideanFourSpace, (∏ i, φ i (x i)) * cycleKernel σ x := by
    intro σ
    refine (integral_pos_iff_support_of_nonneg (hnn σ) (hN 4 (by norm_num) (2 * R) d φ hd hTF σ)).mpr ?_
    refine lt_of_lt_of_le hU (measure_mono fun x hx => ?_)
    exact (hterm σ x hx).ne'
  have hmem : (1 : Equiv.Perm (Fin 4)) ∈ unorientedCyclicOrders 4 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp; decide⟩
  have hsum : 0 < ∑ σ ∈ unorientedCyclicOrders 4, ∫ x : Fin 4 → EuclideanFourSpace, (∏ i, φ i (x i)) * cycleKernel σ x :=
    Finset.sum_pos (fun σ _ => hint σ) ⟨1, hmem⟩
  rw [cyclicMomentFormula, if_neg (by norm_num)]
  linarith
end YangMills.Construction.MomentLaw
end

import YangMills.Construction.LawInAState.ProductsInOneBoxProof
import YangMills.Construction.LawOnABoxOfTheFlow.BoundsOnTheEllipsoid
import YangMills.Construction.LawOnABoxOfTheFlow.ColdFieldsLieInTheChartProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open YangMills.Construction.TorusFields YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.BlockAverages hiding unitStep adjointAction
open YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.RenormalizationStepParameters
section Shifts
variable {G E : Type} [AddCommGroup G] [Fintype G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private theorem sum_add_right_eq {M : Type} [AddCommMonoid M] (F : G → M) (c : G) : ∑ x, F (x + c) = ∑ x, F x :=
  Equiv.sum_comp (Equiv.addRight c) F
private theorem sum_inner_sub_shift (f g : G → E) (a b : G) :
    ∑ x, inner ℝ (f x - f (x - a)) (g x - g (x - b)) = ∑ x, inner ℝ (f x - f (x + b)) (g x - g (x + a)) := by
  have e1 : ∑ x, inner ℝ (f x) (g (x - b)) = ∑ x, inner ℝ (f (x + b)) (g x) := by
    rw [← sum_add_right_eq (fun x => inner ℝ (f x) (g (x - b))) b]
    simp
  have e2 : ∑ x, inner ℝ (f (x - a)) (g x) = ∑ x, inner ℝ (f x) (g (x + a)) := by
    rw [← sum_add_right_eq (fun x => inner ℝ (f (x - a)) (g x)) a]
    simp
  have e3 : ∑ x, inner ℝ (f (x - a)) (g (x - b)) = ∑ x, inner ℝ (f (x + b)) (g (x + a)) := by
    rw [← sum_add_right_eq (fun x => inner ℝ (f (x - a)) (g (x - b))) (a + b)]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 2 <;> abel_nf
  simp only [inner_sub_left, inner_sub_right, Finset.sum_sub_distrib]
  rw [e1, e2, e3]
  ring
private def discreteCurl {ι : Type} (e : ι → G) (f : ι → G → E) (x : G) (i j : ι) : E :=
  f i x + f j (x + e i) - f i (x + e j) - f j x
private theorem sum_norm_discreteCurl_sq {ι : Type} (e : ι → G) (f : ι → G → E) (i j : ι) :
    ∑ x, ‖discreteCurl e f x i j‖ ^ 2 = ∑ x, ‖f i x - f i (x + e j)‖ ^ 2 + ∑ x, ‖f j x - f j (x + e i)‖ ^ 2 -
      2 * ∑ x, inner ℝ (f i x - f i (x - e i)) (f j x - f j (x - e j)) := by
  rw [sum_inner_sub_shift, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have : discreteCurl e f x i j = (f i x - f i (x + e j)) - (f j x - f j (x + e i)) := by
    unfold discreteCurl
    abel
  rw [this, norm_sub_sq_real]
  ring
private theorem offdiag_diff_le_curl_add_div (e : Fin 4 → G) (f : Fin 4 → G → E) (S : Finset G)
    (hS : ∀ x, x ∉ S → ∀ i j, i ≠ j → inner ℝ (f i x - f i (x - e i)) (f j x - f j (x - e j)) = (0 : ℝ)) :
    ∑ i, ∑ j, (if i = j then 0 else ∑ x, ‖f i x - f i (x + e j)‖ ^ 2) ≤
      ∑ i, ∑ j, (if i < j then ∑ x, ‖discreteCurl e f x i j‖ ^ 2 else 0) +
        ∑ x ∈ S, ‖∑ i, (f i x - f i (x - e i))‖ ^ 2 := by
  classical
  set u : Fin 4 → G → E := fun i x => f i x - f i (x - e i) with hu
  set C : Fin 4 → Fin 4 → ℝ := fun i j => ∑ x, inner ℝ (u i x) (u j x) with hC
  have hCs : ∀ i j, C i j = C j i := fun i j => Finset.sum_congr rfl fun x _ => real_inner_comm _ _
  have hQ : ∑ i, ∑ j, (if i = j then (0 : ℝ) else C i j) ≤ ∑ x ∈ S, ‖∑ i, u i x‖ ^ 2 := by
    have h1 : ∀ x, ∑ i, ∑ j, (if i = j then (0 : ℝ) else inner ℝ (u i x) (u j x)) ≤ ‖∑ i, u i x‖ ^ 2 := by
      intro x
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [inner_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with h
      · subst h
        exact real_inner_self_nonneg
      · exact le_rfl
    have h2 : ∑ i, ∑ j, (if i = j then (0 : ℝ) else C i j) =
        ∑ x ∈ S, ∑ i, ∑ j, (if i = j then (0 : ℝ) else inner ℝ (u i x) (u j x)) := by
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with h
      · simp
      · exact Finset.sum_subset (Finset.subset_univ S) fun x _ hx => hS x hx i j h
    rw [h2]
    exact Finset.sum_le_sum fun x _ => h1 x
  refine le_trans ?_ (add_le_add_right hQ _)
  have hT : ∀ i j, ∑ x, ‖discreteCurl e f x i j‖ ^ 2 = ∑ x, ‖f i x - f i (x + e j)‖ ^ 2 +
      ∑ x, ‖f j x - f j (x + e i)‖ ^ 2 - 2 * C i j := fun i j => sum_norm_discreteCurl_sq e f i j
  simp (decide := true) only [Fin.sum_univ_four, ↓reduceIte]
  have a01 := hCs 0 1
  have a02 := hCs 0 2
  have a03 := hCs 0 3
  have a12 := hCs 1 2
  have a13 := hCs 1 3
  have a23 := hCs 2 3
  have t01 := hT 0 1
  have t02 := hT 0 2
  have t03 := hT 0 3
  have t12 := hT 1 2
  have t13 := hT 1 3
  have t23 := hT 2 3
  rw [t01, t02, t03, t12, t13, t23]
  linarith
end Shifts
section Torus
variable {n : ℕ} [NeZero n]
private def axisOffset (o z : TorusSite n) (i : Fin 4) : ℕ := ((z i - o i).valMinAbs).natAbs
private theorem mem_supBall_iff_axisOffset (o z : TorusSite n) (r : ℕ) :
    z ∈ supBall o (r : ℝ) ↔ ∀ i, axisOffset o z i ≤ r := by
  have h : (((supDist z o : ℕ) : ℝ) ≤ (r : ℝ)) ↔ supDist z o ≤ r := Nat.cast_le
  rw [supBall, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [h]
  simp only [supDist, Finset.sup_le_iff, axisOffset, Finset.mem_univ, true_imp_iff]
private theorem mem_supBall_two_mul_iff (o z : TorusSite n) (R : ℕ) :
    z ∈ supBall o (2 * (R : ℝ)) ↔ ∀ i, axisOffset o z i ≤ 2 * R := by
  have h : (2 * (R : ℝ)) = ((2 * R : ℕ) : ℝ) := by push_cast; ring
  rw [h, mem_supBall_iff_axisOffset]
private theorem unitStep_self (i : Fin 4) : unitStep n i i = 1 := by simp [unitStep]
private theorem unitStep_of_ne {i l : Fin 4} (h : l ≠ i) : unitStep n i l = 0 := by
  simp [unitStep, Pi.single_apply, h]
private theorem axisOffset_add_unitStep_of_ne (o x : TorusSite n) {i l : Fin 4} (h : l ≠ i) :
    axisOffset o (x + unitStep n i) l = axisOffset o x l := by
  simp [axisOffset, unitStep_of_ne h]
private theorem axisOffset_sub_unitStep_of_ne (o x : TorusSite n) {i l : Fin 4} (h : l ≠ i) :
    axisOffset o (x - unitStep n i) l = axisOffset o x l := by
  simp [axisOffset, unitStep_of_ne h]
private theorem natAbs_valMinAbs_one_le (hn : 2 ≤ n) : ((1 : ZMod n).valMinAbs).natAbs ≤ 1 := by apply _root_.YangMills.SharedProofs.p10270 <;> assumption
private theorem axisOffset_add_unitStep_le (hn : 2 ≤ n) (o x : TorusSite n) (i l : Fin 4) :
    axisOffset o (x + unitStep n i) l ≤ axisOffset o x l + 1 := by
  by_cases h : l = i
  · subst h
    have e : (x + unitStep n l) l - o l = (x l - o l) + 1 := by
      simp only [Pi.add_apply, unitStep_self]
      ring
    unfold axisOffset
    rw [e]
    have h1 := ZMod.natAbs_valMinAbs_add_le (x l - o l) (1 : ZMod n)
    have h2 := Int.natAbs_add_le (x l - o l).valMinAbs (1 : ZMod n).valMinAbs
    have h3 := natAbs_valMinAbs_one_le hn
    omega
  · rw [axisOffset_add_unitStep_of_ne o x h]
    omega
private theorem axisOffset_le_add_unitStep (hn : 2 ≤ n) (o x : TorusSite n) (i l : Fin 4) :
    axisOffset o x l ≤ axisOffset o (x + unitStep n i) l + 1 := by
  by_cases h : l = i
  · subst h
    have e : x l - o l = ((x + unitStep n l) l - o l) + (-1) := by
      simp only [Pi.add_apply, unitStep_self]
      ring
    unfold axisOffset
    rw [e]
    have h1 := ZMod.natAbs_valMinAbs_add_le ((x + unitStep n l) l - o l) (-1 : ZMod n)
    have h2 := Int.natAbs_add_le ((x + unitStep n l) l - o l).valMinAbs (-1 : ZMod n).valMinAbs
    have h3 := natAbs_valMinAbs_one_le hn
    have h4 := ZMod.natAbs_valMinAbs_neg (1 : ZMod n)
    omega
  · rw [axisOffset_add_unitStep_of_ne o x h]
    omega
variable {E : Type} [NormedAddCommGroup E]
private theorem norm_sub_walk_sq_le (g : TorusSite n → E) (e x : TorusSite n) (m : ℕ) :
    ‖g x - g (x + m • e)‖ ^ 2 ≤ m * ∑ s ∈ Finset.range m, ‖g (x + s • e) - g (x + s • e + e)‖ ^ 2 := by
  have h1 : ‖g x - g (x + m • e)‖ ≤ ∑ s ∈ Finset.range m, ‖g (x + s • e) - g (x + s • e + e)‖ := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have e1 : x + (m + 1) • e = x + m • e + e := by
        rw [succ_nsmul, add_assoc]
      rw [e1]
      have h2 := norm_add_le (g x - g (x + m • e)) (g (x + m • e) - g (x + m • e + e))
      rw [sub_add_sub_cancel] at h2
      linarith
  have h3 := sq_sum_le_card_mul_sum_sq (s := Finset.range m)
    (f := fun s => ‖g (x + s • e) - g (x + s • e + e)‖)
  rw [Finset.card_range] at h3
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h3
private theorem norm_sq_le_walk_sums (o : TorusSite n) (R : ℕ) (j : Fin 4) (hR : R + 1 ≤ n / 2)
    (g : TorusSite n → E) (hg : ∀ y, R < axisOffset o y j → g y = 0) (x : TorusSite n) :
    ‖g x‖ ^ 2 ≤ ((R : ℝ) + 1) * (∑ s ∈ Finset.range (R + 1),
      ‖g (x + s • unitStep n j) - g (x + s • unitStep n j + unitStep n j)‖ ^ 2 +
      ∑ s ∈ Finset.range (R + 1),
        ‖g (x - (s + 1) • unitStep n j) - g (x - (s + 1) • unitStep n j + unitStep n j)‖ ^ 2) := by
  set e := unitStep n j with he
  set h : TorusSite n → ℝ := fun y => ‖g y - g (y + e)‖ ^ 2 with hh
  have hnn : ∀ y, 0 ≤ h y := fun y => by positivity
  have hup : 0 ≤ ∑ s ∈ Finset.range (R + 1), h (x + s • e) := Finset.sum_nonneg fun s _ => hnn _
  have hdn : 0 ≤ ∑ s ∈ Finset.range (R + 1), h (x - (s + 1) • e) := Finset.sum_nonneg fun s _ => hnn _
  show ‖g x‖ ^ 2 ≤ ((R : ℝ) + 1) * (∑ s ∈ Finset.range (R + 1), h (x + s • e) +
    ∑ s ∈ Finset.range (R + 1), h (x - (s + 1) • e))
  by_cases hfar : R < axisOffset o x j
  · rw [hg x hfar]
    have : ‖(0 : E)‖ ^ 2 = 0 := by simp
    rw [this]
    positivity
  set tn := axisOffset o x j with htn
  have hval : ((x j - o j).valMinAbs : ZMod n) = x j - o j := ZMod.coe_valMinAbs _
  have hm : R + 1 - tn + tn = R + 1 := by omega
  set m := R + 1 - tn with hmdef
  have hmle : m ≤ R + 1 := by omega
  have hmR : (m : ℝ) ≤ (R : ℝ) + 1 := by exact_mod_cast hmle
  rcases le_total 0 (x j - o j).valMinAbs with ht | ht
  · have ht' : ((tn : ℤ)) = (x j - o j).valMinAbs := by
      rw [htn]
      unfold axisOffset
      exact Int.natAbs_of_nonneg ht
    have hxo : x j - o j = (tn : ZMod n) := by
      rw [← hval, ← ht']
      simp
    have hy : (x + m • e) j - o j = ((R + 1 : ℕ) : ZMod n) := by
      have : (x + m • e) j = x j + (m : ZMod n) := by
        simp [he, unitStep_self]
      rw [this, ← hm]
      push_cast
      rw [show x j + (m : ZMod n) - o j = (x j - o j) + m by ring, hxo]
      ring
    have hz : g (x + m • e) = 0 := by
      apply hg
      unfold axisOffset
      rw [hy, ZMod.valMinAbs_natCast_of_le_half hR]
      simp only [Nat.cast_add, Nat.cast_one]
      omega
    have h1 := norm_sub_walk_sq_le g e x m
    rw [hz, sub_zero] at h1
    have h2 : ∑ s ∈ Finset.range m, h (x + s • e) ≤ ∑ s ∈ Finset.range (R + 1), h (x + s • e) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hmle) fun _ _ _ => hnn _
    have h3 : 0 ≤ ∑ s ∈ Finset.range m, h (x + s • e) := Finset.sum_nonneg fun s _ => hnn _
    calc ‖g x‖ ^ 2 ≤ (m : ℝ) * ∑ s ∈ Finset.range m, h (x + s • e) := h1
      _ ≤ ((R : ℝ) + 1) * ∑ s ∈ Finset.range (R + 1), h (x + s • e) := by
          exact mul_le_mul hmR h2 h3 (by positivity)
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
  · have ht' : (-(tn : ℤ)) = (x j - o j).valMinAbs := by
      rw [htn]
      unfold axisOffset
      exact Int.ofNat_natAbs_of_nonpos ht ▸ by simp
    have hxo : x j - o j = -(tn : ZMod n) := by
      rw [← hval, ← ht']
      simp
    set y := x - m • e with hydef
    have hy : y j - o j = -((R + 1 : ℕ) : ZMod n) := by
      have : y j = x j - (m : ZMod n) := by
        simp [hydef, he, unitStep_self]
      rw [this, ← hm]
      push_cast
      rw [show x j - (m : ZMod n) - o j = (x j - o j) - m by ring, hxo]
      ring
    have hz : g y = 0 := by
      apply hg
      unfold axisOffset
      rw [hy, ZMod.natAbs_valMinAbs_neg, ZMod.valMinAbs_natCast_of_le_half hR]
      simp only [Nat.cast_add, Nat.cast_one]
      omega
    have h1 := norm_sub_walk_sq_le g e y m
    have hyx : y + m • e = x := by
      rw [hydef]
      abel
    rw [hyx, hz, zero_sub, norm_neg] at h1
    have h4 : ∑ s ∈ Finset.range m, ‖g (y + s • e) - g (y + s • e + e)‖ ^ 2 =
        ∑ s ∈ Finset.range m, h (x - (s + 1) • e) := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hs' : s < m := Finset.mem_range.mp hs
      have e2 : y + (m - 1 - s) • e = x - (s + 1) • e := by
        have e3 : m • e = (m - 1 - s) • e + (s + 1) • e := by
          rw [← add_nsmul]
          congr 1
          omega
        rw [hydef, e3]
        abel
      rw [e2]
    rw [h4] at h1
    have h2 : ∑ s ∈ Finset.range m, h (x - (s + 1) • e) ≤ ∑ s ∈ Finset.range (R + 1), h (x - (s + 1) • e) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hmle) fun _ _ _ => hnn _
    have h3 : 0 ≤ ∑ s ∈ Finset.range m, h (x - (s + 1) • e) := Finset.sum_nonneg fun s _ => hnn _
    calc ‖g x‖ ^ 2 ≤ (m : ℝ) * ∑ s ∈ Finset.range m, h (x - (s + 1) • e) := h1
      _ ≤ ((R : ℝ) + 1) * ∑ s ∈ Finset.range (R + 1), h (x - (s + 1) • e) := by
          exact mul_le_mul hmR h2 h3 (by positivity)
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
private theorem sum_norm_sq_le_poincare (o : TorusSite n) (R : ℕ) (j : Fin 4) (hR : R + 1 ≤ n / 2)
    (g : TorusSite n → E) (hg : ∀ y, R < axisOffset o y j → g y = 0) :
    ∑ x, ‖g x‖ ^ 2 ≤ 2 * ((R : ℝ) + 1) ^ 2 * ∑ x, ‖g x - g (x + unitStep n j)‖ ^ 2 := by
  set e := unitStep n j with he
  set H := ∑ x, ‖g x - g (x + e)‖ ^ 2 with hH
  have h1 : ∀ s : ℕ, ∑ x, ‖g (x + s • e) - g (x + s • e + e)‖ ^ 2 = H := fun s =>
    sum_add_right_eq (fun y => ‖g y - g (y + e)‖ ^ 2) (s • e)
  have h2 : ∀ s : ℕ, ∑ x, ‖g (x - (s + 1) • e) - g (x - (s + 1) • e + e)‖ ^ 2 = H := fun s => by
    simp only [sub_eq_add_neg (_ : TorusSite n) ((s + 1) • e)]
    exact sum_add_right_eq (fun y => ‖g y - g (y + e)‖ ^ 2) (-((s + 1) • e))
  calc ∑ x, ‖g x‖ ^ 2 ≤ ∑ x, ((R : ℝ) + 1) * (∑ s ∈ Finset.range (R + 1), ‖g (x + s • e) - g (x + s • e + e)‖ ^ 2 +
        ∑ s ∈ Finset.range (R + 1), ‖g (x - (s + 1) • e) - g (x - (s + 1) • e + e)‖ ^ 2) :=
        Finset.sum_le_sum fun x _ => norm_sq_le_walk_sums o R j hR g hg x
    _ = 2 * ((R : ℝ) + 1) ^ 2 * H := by
        have a1 : ∑ x, ∑ s ∈ Finset.range (R + 1), ‖g (x + s • e) - g (x + s • e + e)‖ ^ 2 =
            ((R : ℝ) + 1) * H := by
          rw [Finset.sum_comm, Finset.sum_congr rfl fun s _ => h1 s, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
          push_cast
          ring
        have a2 : ∑ x, ∑ s ∈ Finset.range (R + 1), ‖g (x - (s + 1) • e) - g (x - (s + 1) • e + e)‖ ^ 2 =
            ((R : ℝ) + 1) * H := by
          rw [Finset.sum_comm, Finset.sum_congr rfl fun s _ => h2 s, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
          push_cast
          ring
        rw [← Finset.mul_sum, Finset.sum_add_distrib, a1, a2]
        ring
end Torus
section Quaternions
private theorem norm_coe_imaginary (X : imaginaryQuaternions) : ‖(X : ℍ[ℝ])‖ = ‖X‖ := rfl
private theorem exp_imaginary_eq (w : imaginaryQuaternions) : NormedSpace.exp (w : ℍ[ℝ]) =
    ((Real.cos ‖w‖ : ℝ) : ℍ[ℝ]) + Real.sinc ‖w‖ • (w : ℍ[ℝ]) := by
  have h1 := re_add_pureComponent (NormedSpace.exp (w : ℍ[ℝ]))
  rw [re_exp_of_re_eq_zero w.2, pureComponent_exp w.2] at h1
  exact h1.symm
private theorem scalar_add_mul_scalar_add (s c t : ℝ) (p r : ℍ[ℝ]) : ((s : ℍ[ℝ]) + p) * ((c : ℍ[ℝ]) + t • r) =
    ((s * c : ℝ) : ℍ[ℝ]) + (s * t) • r + c • p + t • (p * r) := by
  ext <;> simp <;> ring
private theorem re_scalar_add_terms (x y c t : ℝ) {p r : ℍ[ℝ]} (m : ℍ[ℝ]) (hp : p.re = 0) (hr : r.re = 0) :
    (((x : ℝ) : ℍ[ℝ]) + y • r + c • p + t • m).re = x + t * m.re := by
  simp [hp, hr]
private theorem pureComponent_imaginary (w : imaginaryQuaternions) : pureComponent (w : ℍ[ℝ]) = (w : ℍ[ℝ]) :=
  pureComponent_of_re_eq_zero w.2
private theorem sqrt_one_sub_sq_bounds {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) :
    1 - z ^ 2 ≤ Real.sqrt (1 - z ^ 2) ∧ Real.sqrt (1 - z ^ 2) ≤ 1 := by
  have hy : 0 ≤ 1 - z ^ 2 := by nlinarith
  have hy1 : 1 - z ^ 2 ≤ 1 := by nlinarith [sq_nonneg z]
  refine ⟨Real.le_sqrt_of_sq_le ?_, Real.sqrt_le_one.mpr hy1⟩
  nlinarith
private theorem abs_mul_sub_one_le {s t z a : ℝ} (hs1 : 1 - z ^ 2 ≤ s) (hs2 : s ≤ 1) (ht1 : |t - 1| ≤ a ^ 2 / 4)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 100) (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 100) : |s * t - 1| ≤ z ^ 2 + a ^ 2 / 4 := by
  obtain ⟨ht2, ht3⟩ := abs_le.mp ht1
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hz2 : z ^ 2 ≤ 1 := by nlinarith
  have ht0 : 0 ≤ t := by linarith
  have hs0 : 0 ≤ s := by linarith
  have h1 : s * t ≤ 1 * t := mul_le_mul_of_nonneg_right hs2 ht0
  have h2 : (1 - z ^ 2) * (1 - a ^ 2 / 4) ≤ s * t :=
    mul_le_mul hs1 (by linarith) (by linarith) hs0
  have h3 : 0 ≤ z ^ 2 * a ^ 2 := by positivity
  refine abs_le.mpr ⟨?_, ?_⟩
  · nlinarith
  · nlinarith [sq_nonneg z]
private theorem chart_error_terms_le {a z st c w : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 100) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1 / 100) (hst : st ≤ (z ^ 2 + a ^ 2 / 4) * a) (hc : c ≤ a ^ 2 / 2 * z)
    (hw : w ≤ (1 + a ^ 2 / 4) * (z * a)) :
    st + c + w ≤ (3 / 5) * (a ^ 2 + z ^ 2) := by
  have q1 : 0 ≤ a ^ 2 := sq_nonneg a
  have q2 : 0 ≤ z ^ 2 := sq_nonneg z
  have m1 : (z ^ 2 + a ^ 2 / 4) * a ≤ (a ^ 2 + z ^ 2) / 100 := by
    have : (z ^ 2 + a ^ 2 / 4) * a ≤ (z ^ 2 + a ^ 2 / 4) * (1 / 100) := mul_le_mul_of_nonneg_left ha1 (by positivity)
    linarith
  have m2 : a ^ 2 / 2 * z ≤ (a ^ 2 + z ^ 2) / 100 := by
    have : a ^ 2 / 2 * z ≤ a ^ 2 / 2 * (1 / 100) := mul_le_mul_of_nonneg_left hz1 (by positivity)
    linarith
  have m3 : (1 + a ^ 2 / 4) * (z * a) ≤ (51 / 100) * (a ^ 2 + z ^ 2) := by
    have h1 : a ^ 2 / 4 ≤ 1 / 50 := by nlinarith
    have h2 : z * a ≤ (a ^ 2 + z ^ 2) / 2 := by nlinarith [sq_nonneg (a - z)]
    have h3 : 0 ≤ z * a := by positivity
    have h4 : (1 + a ^ 2 / 4) * (z * a) ≤ (1 + 1 / 50) * ((a ^ 2 + z ^ 2) / 2) :=
      mul_le_mul (by linarith) h2 h3 (by norm_num)
    linarith
  linarith
private theorem re_chart_lower {s c t r z a : ℝ} (hs1 : 1 - z ^ 2 ≤ s) (hc2 : 1 - a ^ 2 / 2 ≤ c) (ht : |t| ≤ 2)
    (hr : |r| ≤ z * a) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 100) (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 100) :
    (9 / 10 : ℝ) ≤ s * c + t * r := by
  have e3 : |t * r| ≤ 2 * (z * a) := by
    rw [abs_mul]
    exact mul_le_mul ht hr (abs_nonneg _) (by norm_num)
  have e4 : z * a ≤ 1 / 100 * (1 / 100) := mul_le_mul hz1 ha1 ha0 (by norm_num)
  have h1 : z ^ 2 ≤ 1 / 100 * (1 / 100) := by nlinarith
  have h2 : a ^ 2 ≤ 1 / 100 * (1 / 100) := by nlinarith
  have e5 : (0.99 : ℝ) * 0.99 ≤ s * c := mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  have := (abs_le.mp e3).1
  linarith
private theorem chartPoint_pure_near (A ζ : imaginaryQuaternions) (q : UnitQuaternion) (h : (q : ℍ[ℝ]) = chartPoint A ζ)
    (hA : ‖A‖ ≤ 1 / 100) (hζ : ‖ζ‖ ≤ 1 / 100) :
    ‖pureComponent (q : ℍ[ℝ]) - (A : ℍ[ℝ]) - (ζ : ℍ[ℝ])‖ ≤ (3 / 5) * (‖A‖ ^ 2 + ‖ζ‖ ^ 2) ∧
      (9 / 10 : ℝ) ≤ (q : ℍ[ℝ]).re := by
  have ha0 : 0 ≤ ‖A‖ := norm_nonneg _
  have hz0 : 0 ≤ ‖ζ‖ := norm_nonneg _
  obtain ⟨hs1, hs2⟩ := sqrt_one_sub_sq_bounds hz0 (by linarith)
  have hc1 : Real.cos ‖A‖ ≤ 1 := Real.cos_le_one _
  have hc2 : 1 - ‖A‖ ^ 2 / 2 ≤ Real.cos ‖A‖ := Real.one_sub_sq_div_two_le_cos
  have ht1 : |Real.sinc ‖A‖ - 1| ≤ ‖A‖ ^ 2 / 4 := abs_sinc_sub_one_le ha0 (by linarith)
  generalize hs : Real.sqrt (1 - ‖ζ‖ ^ 2) = s at hs1 hs2
  generalize hc : Real.cos ‖A‖ = c at hc1 hc2
  generalize ht : Real.sinc ‖A‖ = t at ht1
  have hq : (q : ℍ[ℝ]) = ((s * c : ℝ) : ℍ[ℝ]) + (s * t) • (A : ℍ[ℝ]) + c • (ζ : ℍ[ℝ]) +
      t • ((ζ : ℍ[ℝ]) * (A : ℍ[ℝ])) := by
    rw [h, chartPoint]
    show (((Real.sqrt (1 - ‖ζ‖ ^ 2) : ℝ) : ℍ[ℝ]) + (ζ : ℍ[ℝ])) * NormedSpace.exp (A : ℍ[ℝ]) = _
    rw [exp_imaginary_eq, hs, hc, ht, scalar_add_mul_scalar_add]
  have hwn : ‖pureComponent ((ζ : ℍ[ℝ]) * (A : ℍ[ℝ]))‖ ≤ ‖ζ‖ * ‖A‖ := by
    refine (norm_pureComponent_le _).trans ?_
    rw [norm_mul]
    exact le_rfl
  have hu : pureComponent (q : ℍ[ℝ]) = (s * t) • (A : ℍ[ℝ]) + c • (ζ : ℍ[ℝ]) +
      t • pureComponent ((ζ : ℍ[ℝ]) * (A : ℍ[ℝ])) := by
    rw [hq, pureComponent_add, pureComponent_add, pureComponent_add, pureComponent_coe, pureComponent_smul,
      pureComponent_smul, pureComponent_smul, pureComponent_imaginary, pureComponent_imaginary, zero_add]
  have hst := abs_mul_sub_one_le hs1 hs2 ht1 ha0 hA hz0 hζ
  have hc3 : |c - 1| ≤ ‖A‖ ^ 2 / 2 := abs_le.mpr ⟨by linarith, by nlinarith [sq_nonneg ‖A‖]⟩
  have ht5 : |t| ≤ 1 + ‖A‖ ^ 2 / 4 := by
    obtain ⟨ht2, ht3⟩ := abs_le.mp ht1
    refine abs_le.mpr ⟨?_, by linarith⟩
    nlinarith [sq_nonneg ‖A‖]
  have ht4 : |t| ≤ 2 := by nlinarith
  constructor
  · have e1 : pureComponent (q : ℍ[ℝ]) - (A : ℍ[ℝ]) - (ζ : ℍ[ℝ]) =
        (s * t - 1) • (A : ℍ[ℝ]) + (c - 1) • (ζ : ℍ[ℝ]) + t • pureComponent ((ζ : ℍ[ℝ]) * (A : ℍ[ℝ])) := by
      rw [hu, sub_smul, sub_smul, one_smul, one_smul]
      abel
    rw [e1]
    have n1 : ‖(s * t - 1) • (A : ℍ[ℝ])‖ ≤ (‖ζ‖ ^ 2 + ‖A‖ ^ 2 / 4) * ‖A‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hst ha0
    have n2 : ‖(c - 1) • (ζ : ℍ[ℝ])‖ ≤ ‖A‖ ^ 2 / 2 * ‖ζ‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hc3 hz0
    have n3 : ‖t • pureComponent ((ζ : ℍ[ℝ]) * (A : ℍ[ℝ]))‖ ≤ (1 + ‖A‖ ^ 2 / 4) * (‖ζ‖ * ‖A‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul ht5 hwn (norm_nonneg _) (by positivity)
    exact (norm_add₃_le).trans (chart_error_terms_le ha0 hA hz0 hζ n1 n2 n3)
  · have e1 : (q : ℍ[ℝ]).re = s * c + t * ((ζ : ℍ[ℝ]) * (A : ℍ[ℝ])).re := by
      rw [hq]
      exact re_scalar_add_terms _ _ _ _ _ ζ.2 A.2
    have e2 : |((ζ : ℍ[ℝ]) * (A : ℍ[ℝ])).re| ≤ ‖ζ‖ * ‖A‖ := by
      have h1 := quaternion_re_le_norm ((ζ : ℍ[ℝ]) * (A : ℍ[ℝ]))
      have h2 := quaternion_re_le_norm (-((ζ : ℍ[ℝ]) * (A : ℍ[ℝ])))
      rw [norm_neg, Quaternion.re_neg] at h2
      rw [norm_mul] at h1 h2
      exact abs_le.mpr ⟨by linarith [show ‖(ζ : ℍ[ℝ])‖ * ‖(A : ℍ[ℝ])‖ = ‖ζ‖ * ‖A‖ from rfl],
        by linarith [show ‖(ζ : ℍ[ℝ])‖ * ‖(A : ℍ[ℝ])‖ = ‖ζ‖ * ‖A‖ from rfl]⟩
    rw [e1]
    exact re_chart_lower hs1 hc2 ht4 e2 ha0 hA hz0 hζ
private theorem angle_bounds {a z D θ u : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 100) (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 100)
    (hD : D = a ^ 2 + z ^ 2) (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ (4 / 3) * u) (hu : u ≤ a + z + (3 / 5) * D) :
    θ ≤ 1 / 25 ∧ θ ^ 2 ≤ 4 * D := by
  have hDs : D ≤ (a + z) * (a + z) := by nlinarith [mul_nonneg ha0 hz0]
  have hs2 : (a + z) * (a + z) ≤ 2 * D := by nlinarith [sq_nonneg (a - z)]
  have haz : a + z ≤ 1 / 50 := by linarith
  have haz0 : 0 ≤ a + z := by linarith
  have h1 : (a + z) * (a + z) ≤ (1 / 50) * (a + z) := mul_le_mul_of_nonneg_right haz haz0
  have hθ3 : θ ≤ (27 / 20) * (a + z) := by linarith
  refine ⟨by linarith, ?_⟩
  have h2 : θ ^ 2 ≤ ((27 / 20) * (a + z)) ^ 2 := pow_le_pow_left₀ hθ0 hθ3 2
  nlinarith
private theorem chartPoint_log_near (A ζ : imaginaryQuaternions) (q : UnitQuaternion) (h : (q : ℍ[ℝ]) = chartPoint A ζ)
    (hA : ‖A‖ ≤ 1 / 100) (hζ : ‖ζ‖ ≤ 1 / 100) :
    ∃ v : imaginaryQuaternions, q = expUnit v ∧ ‖v - A - ζ‖ ≤ 2 * (‖A‖ ^ 2 + ‖ζ‖ ^ 2) := by
  obtain ⟨hE, hre⟩ := chartPoint_pure_near A ζ q h hA hζ
  have ha0 : 0 ≤ ‖A‖ := norm_nonneg _
  have hz0 : 0 ≤ ‖ζ‖ := norm_nonneg _
  obtain ⟨v, hv⟩ : ∃ v : imaginaryQuaternions, v = ⟨unitQuaternionLog q, re_unitQuaternionLog q⟩ := ⟨_, rfl⟩
  have hqv : q = expUnit v := by
    rw [hv]
    exact (expUnit_unitQuaternionLog q).symm
  have hθa : ‖v‖ = Real.arccos (q : ℍ[ℝ]).re := by
    rw [hv]
    exact norm_unitQuaternionLog q
  have hθ0 : 0 ≤ ‖v‖ := norm_nonneg _
  have hθ1 : ‖v‖ ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have h1 : Real.cos ‖v‖ < Real.cos 1 := by
      have hpi : ‖v‖ ≤ Real.pi := by
        rw [hθa]
        exact Real.arccos_le_pi _
      exact Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num) hpi hlt
    have h2 : Real.cos ‖v‖ = (q : ℍ[ℝ]).re := by
      rw [hθa]
      exact cos_arccos_re_coe q
    have h3 := Real.cos_one_le
    linarith
  have hsn := abs_sinc_sub_one_le hθ0 hθ1
  obtain ⟨hsn1, hsn2⟩ := abs_le.mp hsn
  have hsn3 : (3 / 4 : ℝ) ≤ Real.sinc ‖v‖ := by nlinarith
  have hvu : pureComponent (q : ℍ[ℝ]) = Real.sinc ‖v‖ • (v : ℍ[ℝ]) := by
    have e1 : (q : ℍ[ℝ]) = NormedSpace.exp (v : ℍ[ℝ]) := by
      conv_lhs => rw [hqv]
      rfl
    rw [e1]
    exact pureComponent_exp v.2
  have hnu : ‖pureComponent (q : ℍ[ℝ])‖ = Real.sinc ‖v‖ * ‖v‖ := by
    rw [hvu, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rfl
  have hθ2 : ‖v‖ ≤ (4 / 3) * ‖pureComponent (q : ℍ[ℝ])‖ := by
    rw [hnu]
    nlinarith
  have hnu2 : ‖pureComponent (q : ℍ[ℝ])‖ ≤ ‖A‖ + ‖ζ‖ + (3 / 5) * (‖A‖ ^ 2 + ‖ζ‖ ^ 2) := by
    have e1 : pureComponent (q : ℍ[ℝ]) =
        (pureComponent (q : ℍ[ℝ]) - (A : ℍ[ℝ]) - (ζ : ℍ[ℝ])) + (A : ℍ[ℝ]) + (ζ : ℍ[ℝ]) := by abel
    have h3 := norm_add₃_le (a := pureComponent (q : ℍ[ℝ]) - (A : ℍ[ℝ]) - (ζ : ℍ[ℝ])) (b := (A : ℍ[ℝ]))
      (c := (ζ : ℍ[ℝ]))
    rw [← e1] at h3
    have e2 : ‖(A : ℍ[ℝ])‖ = ‖A‖ := rfl
    have e3 : ‖(ζ : ℍ[ℝ])‖ = ‖ζ‖ := rfl
    linarith
  obtain ⟨hθ5, hθ4⟩ := angle_bounds ha0 hA hz0 hζ rfl hθ0 hθ2 hnu2
  have hvd : ‖(v : ℍ[ℝ]) - pureComponent (q : ℍ[ℝ])‖ ≤ (‖A‖ ^ 2 + ‖ζ‖ ^ 2) / 25 := by
    have e1 : (v : ℍ[ℝ]) - pureComponent (q : ℍ[ℝ]) = (1 - Real.sinc ‖v‖) • (v : ℍ[ℝ]) := by
      rw [hvu, sub_smul, one_smul]
    rw [e1, norm_smul, Real.norm_eq_abs, abs_sub_comm]
    have e2 : ‖(v : ℍ[ℝ])‖ = ‖v‖ := rfl
    rw [e2]
    have h4 : |Real.sinc ‖v‖ - 1| * ‖v‖ ≤ ‖v‖ ^ 2 / 4 * (1 / 25) := mul_le_mul hsn hθ5 hθ0 (by positivity)
    nlinarith
  refine ⟨v, hqv, ?_⟩
  have e1 : ‖v - A - ζ‖ =
      ‖((v : ℍ[ℝ]) - pureComponent (q : ℍ[ℝ])) + (pureComponent (q : ℍ[ℝ]) - (A : ℍ[ℝ]) - (ζ : ℍ[ℝ]))‖ := by
    rw [← norm_coe_imaginary]
    congr 1
    push_cast
    abel
  rw [e1]
  have h5 := norm_add_le ((v : ℍ[ℝ]) - pureComponent (q : ℍ[ℝ]))
    (pureComponent (q : ℍ[ℝ]) - (A : ℍ[ℝ]) - (ζ : ℍ[ℝ]))
  nlinarith [sq_nonneg ‖A‖, sq_nonneg ‖ζ‖]
end Quaternions
section Plaquette
private theorem norm_exp_sub_one_sub_le (w : imaginaryQuaternions) (h : ‖w‖ ≤ 1) :
    ‖NormedSpace.exp (w : ℍ[ℝ]) - 1 - (w : ℍ[ℝ])‖ ≤ ‖w‖ ^ 2 := by apply _root_.YangMills.SharedProofs.p105988 <;> assumption
private theorem star_imaginary (w : imaginaryQuaternions) : star (w : ℍ[ℝ]) = -(w : ℍ[ℝ]) := by apply _root_.YangMills.Construction.GaugeMotions.star_coe_imaginary <;> assumption
private theorem norm_star_exp_sub_one_add_le (w : imaginaryQuaternions) (h : ‖w‖ ≤ 1) :
    ‖star (NormedSpace.exp (w : ℍ[ℝ])) - 1 + (w : ℍ[ℝ])‖ ≤ ‖w‖ ^ 2 := by
  have e : star (NormedSpace.exp (w : ℍ[ℝ])) - 1 + (w : ℍ[ℝ]) =
      star (NormedSpace.exp (w : ℍ[ℝ]) - 1 - (w : ℍ[ℝ])) := by
    rw [star_sub, star_sub, star_one, star_imaginary]
    abel
  rw [e, norm_star]
  exact norm_exp_sub_one_sub_le w h
private theorem norm_mul_sub_first_order_le {P g : ℍ[ℝ]} {p V : ℝ} (hP : ‖P - 1‖ ≤ p) (hg : ‖g - 1‖ ≤ V)
    (hV : 0 ≤ V) (hp : 0 ≤ p) :
    ‖P * g - 1 - (P - 1) - (g - 1)‖ ≤ p * V := by
  have e : P * g - 1 - (P - 1) - (g - 1) = (P - 1) * (g - 1) := by noncomm_ring
  rw [e, norm_mul]
  exact mul_le_mul hP hg (norm_nonneg _) hp
private theorem norm_prod_four_sub_one_le {g₁ g₂ g₃ g₄ w₁ w₂ w₃ w₄ : ℍ[ℝ]} {V : ℝ} (hV : 0 ≤ V) (hV1 : V ≤ 1)
    (h₁ : ‖g₁ - 1‖ ≤ V) (h₂ : ‖g₂ - 1‖ ≤ V) (h₃ : ‖g₃ - 1‖ ≤ V) (h₄ : ‖g₄ - 1‖ ≤ V)
    (k₁ : ‖g₁ - 1 - w₁‖ ≤ V ^ 2) (k₂ : ‖g₂ - 1 - w₂‖ ≤ V ^ 2) (k₃ : ‖g₃ - 1 - w₃‖ ≤ V ^ 2)
    (k₄ : ‖g₄ - 1 - w₄‖ ≤ V ^ 2) :
    ‖g₁ * g₂ * g₃ * g₄ - 1‖ ≤ ‖w₁ + w₂ + w₃ + w₄‖ + 15 * V ^ 2 := by
  have a2 := norm_mul_sub_first_order_le h₁ h₂ hV hV
  have hV2 : V ^ 2 ≤ V := by nlinarith
  have p2 : ‖g₁ * g₂ - 1‖ ≤ 3 * V := by
    have e : g₁ * g₂ - 1 = (g₁ * g₂ - 1 - (g₁ - 1) - (g₂ - 1)) + (g₁ - 1) + (g₂ - 1) := by abel
    rw [e]
    refine (norm_add₃_le).trans ?_
    nlinarith
  have a3 := norm_mul_sub_first_order_le p2 h₃ hV (by positivity)
  have p3 : ‖g₁ * g₂ * g₃ - 1‖ ≤ 7 * V := by
    have e : g₁ * g₂ * g₃ - 1 = (g₁ * g₂ * g₃ - 1 - (g₁ * g₂ - 1) - (g₃ - 1)) + (g₁ * g₂ - 1) + (g₃ - 1) := by abel
    rw [e]
    refine (norm_add₃_le).trans ?_
    nlinarith
  have a4 := norm_mul_sub_first_order_le p3 h₄ hV (by positivity)
  have e : g₁ * g₂ * g₃ * g₄ - 1 = (w₁ + w₂ + w₃ + w₄) +
      ((g₁ * g₂ * g₃ * g₄ - 1 - (g₁ * g₂ * g₃ - 1) - (g₄ - 1)) + (g₁ * g₂ * g₃ - 1 - (g₁ * g₂ - 1) - (g₃ - 1)) +
        (g₁ * g₂ - 1 - (g₁ - 1) - (g₂ - 1))) +
      ((g₁ - 1 - w₁) + (g₂ - 1 - w₂) + (g₃ - 1 - w₃) + (g₄ - 1 - w₄)) := by abel
  rw [e]
  have n1 := norm_add₃_le (a := g₁ * g₂ * g₃ * g₄ - 1 - (g₁ * g₂ * g₃ - 1) - (g₄ - 1))
    (b := g₁ * g₂ * g₃ - 1 - (g₁ * g₂ - 1) - (g₃ - 1)) (c := g₁ * g₂ - 1 - (g₁ - 1) - (g₂ - 1))
  have n2 := norm_add₃_le (a := g₁ - 1 - w₁ + (g₂ - 1 - w₂)) (b := g₃ - 1 - w₃) (c := g₄ - 1 - w₄)
  have n3 := norm_add_le (g₁ - 1 - w₁) (g₂ - 1 - w₂)
  have n4 := norm_add₃_le (a := w₁ + w₂ + w₃ + w₄)
    (b := (g₁ * g₂ * g₃ * g₄ - 1 - (g₁ * g₂ * g₃ - 1) - (g₄ - 1)) + (g₁ * g₂ * g₃ - 1 - (g₁ * g₂ - 1) - (g₃ - 1)) +
        (g₁ * g₂ - 1 - (g₁ - 1) - (g₂ - 1)))
    (c := (g₁ - 1 - w₁) + (g₂ - 1 - w₂) + (g₃ - 1 - w₃) + (g₄ - 1 - w₄))
  refine n4.trans ?_
  nlinarith
private theorem norm_star_sub_one_eq (g : ℍ[ℝ]) : ‖star g - 1‖ = ‖g - 1‖ := by
  rw [← norm_star (g - 1), star_sub, star_one]
private theorem holonomy_exp_near_one (v₁ v₂ v₃ v₄ : imaginaryQuaternions) {V : ℝ} (hV1 : V ≤ 1)
    (h₁ : ‖v₁‖ ≤ V) (h₂ : ‖v₂‖ ≤ V) (h₃ : ‖v₃‖ ≤ V) (h₄ : ‖v₄‖ ≤ V) :
    ‖((expUnit v₁ * expUnit v₂ * (expUnit v₃)⁻¹ * (expUnit v₄)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      ‖v₁ + v₂ - v₃ - v₄‖ + 15 * V ^ 2 := by
  have hV : 0 ≤ V := (norm_nonneg _).trans h₁
  have hs : ∀ v : imaginaryQuaternions, ‖v‖ ≤ V → ‖v‖ ^ 2 ≤ V ^ 2 := fun v h =>
    pow_le_pow_left₀ (norm_nonneg _) h 2
  have hv1 : ∀ v : imaginaryQuaternions, ‖v‖ ≤ V → ‖v‖ ≤ 1 := fun v h => h.trans hV1
  have he : ∀ v : imaginaryQuaternions, ‖v‖ ≤ V → ‖NormedSpace.exp (v : ℍ[ℝ]) - 1‖ ≤ V := fun v h =>
    (norm_exp_sub_one_le v.2).trans h
  have hq := norm_prod_four_sub_one_le (g₁ := NormedSpace.exp (v₁ : ℍ[ℝ])) (g₂ := NormedSpace.exp (v₂ : ℍ[ℝ]))
    (g₃ := star (NormedSpace.exp (v₃ : ℍ[ℝ]))) (g₄ := star (NormedSpace.exp (v₄ : ℍ[ℝ])))
    (w₁ := (v₁ : ℍ[ℝ])) (w₂ := (v₂ : ℍ[ℝ])) (w₃ := -(v₃ : ℍ[ℝ])) (w₄ := -(v₄ : ℍ[ℝ])) hV hV1
    (he _ h₁) (he _ h₂) (by rw [norm_star_sub_one_eq]; exact he _ h₃) (by rw [norm_star_sub_one_eq]; exact he _ h₄)
    ((norm_exp_sub_one_sub_le _ (hv1 _ h₁)).trans (hs _ h₁)) ((norm_exp_sub_one_sub_le _ (hv1 _ h₂)).trans (hs _ h₂))
    (by rw [sub_neg_eq_add]; exact (norm_star_exp_sub_one_add_le _ (hv1 _ h₃)).trans (hs _ h₃))
    (by rw [sub_neg_eq_add]; exact (norm_star_exp_sub_one_add_le _ (hv1 _ h₄)).trans (hs _ h₄))
  have e : ‖(v₁ : ℍ[ℝ]) + (v₂ : ℍ[ℝ]) + -(v₃ : ℍ[ℝ]) + -(v₄ : ℍ[ℝ])‖ = ‖v₁ + v₂ - v₃ - v₄‖ := by
    rw [← norm_coe_imaginary]
    congr 1
  rw [e] at hq
  exact hq
private theorem norm_adjointAction_exp_sub_le (A X : imaginaryQuaternions) :
    ‖_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit A) X - X‖ ≤ 2 * ‖A‖ * ‖X‖ := by
  have hg : ‖((expUnit A : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖A‖ := norm_exp_sub_one_le A.2
  set g : UnitQuaternion := expUnit A with hgdef
  have e1 : ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X - X : imaginaryQuaternions) : ℍ[ℝ]) =
      ((((g : ℍ[ℝ]) - 1) * (X : ℍ[ℝ]) - (X : ℍ[ℝ]) * ((g : ℍ[ℝ]) - 1))) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    have h1 : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
      rw [← Submonoid.coe_mul]
      simp
    have e2 : ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X : imaginaryQuaternions) : ℍ[ℝ]) =
        (g : ℍ[ℝ]) * (X : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := rfl
    have e0 : ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X - X : imaginaryQuaternions) : ℍ[ℝ]) =
        ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X : imaginaryQuaternions) : ℍ[ℝ]) - (X : ℍ[ℝ]) := rfl
    rw [e0, e2]
    have : (((g : ℍ[ℝ]) - 1) * (X : ℍ[ℝ]) - (X : ℍ[ℝ]) * ((g : ℍ[ℝ]) - 1)) =
        (g : ℍ[ℝ]) * (X : ℍ[ℝ]) - (X : ℍ[ℝ]) * (g : ℍ[ℝ]) := by noncomm_ring
    rw [this, sub_mul, mul_assoc (X : ℍ[ℝ]), h1, mul_one]
  rw [← norm_coe_imaginary, e1, norm_mul, norm_coe_unitQuaternion, mul_one]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_coe_imaginary]
  nlinarith [norm_nonneg X]
end Plaquette
section Sizes
open Filter in
private theorem boxRadius_boxScale_eventually (κ₀ : ℝ) (h1 : 1 / 27 ≤ κ₀) (h2 : κ₀ ≤ 1 / 21) (c : ℝ) (hc : 0 < c)
    (N : ℕ) :
    ∃ xs : ℝ, ∀ x, xs ≤ x → N ≤ boxRadius κ₀ x ∧ 0 < boxScale x ∧
      c * (boxRadius κ₀ x : ℝ) ^ 4 * boxScale x ≤ 1 := by
  have t1 : Tendsto (fun x : ℝ => x ^ (1 / 27 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have t2 : Tendsto (fun x : ℝ => x ^ (-(2 / 7 : ℝ))) atTop (nhds 0) := tendsto_rpow_neg_atTop (by norm_num)
  have e1 : ∀ᶠ x in atTop, (N : ℝ) ≤ x ^ (1 / 27 : ℝ) := t1.eventually_ge_atTop _
  have e2 : ∀ᶠ x in atTop, x ^ (-(2 / 7 : ℝ)) < 1 / (1344 * c) :=
    t2.eventually_lt_const (by positivity)
  have e3 : ∀ᶠ x : ℝ in atTop, 3 ≤ x := eventually_ge_atTop 3
  obtain ⟨xs, hxs⟩ := eventually_atTop.1 (e1.and (e2.and e3))
  refine ⟨xs, fun x hx => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hxs x hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hδ : 0 < boxScale x := by
    unfold boxScale
    positivity
  have hk0 : 0 ≤ x ^ κ₀ := (Real.rpow_pos_of_pos hx0 _).le
  have hlow : x ^ (1 / 27 : ℝ) ≤ x ^ κ₀ := Real.rpow_le_rpow_of_exponent_le hx1 h1
  have hup : x ^ κ₀ ≤ x ^ (1 / 21 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 h2
  have hR1 : x ^ κ₀ ≤ (boxRadius κ₀ x : ℝ) := Nat.le_ceil _
  have hR2 : (boxRadius κ₀ x : ℝ) < x ^ κ₀ + 1 := Nat.ceil_lt_add_one hk0
  have hone : 1 ≤ x ^ (1 / 21 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  refine ⟨?_, hδ, ?_⟩
  · have : (N : ℝ) ≤ (boxRadius κ₀ x : ℝ) := by linarith
    exact_mod_cast this
  have hR3 : (boxRadius κ₀ x : ℝ) ≤ 2 * x ^ (1 / 21 : ℝ) := by linarith
  have hR4 : (boxRadius κ₀ x : ℝ) ^ 4 ≤ 16 * x ^ (4 / 21 : ℝ) := by
    have h3 : (boxRadius κ₀ x : ℝ) ^ 4 ≤ (2 * x ^ (1 / 21 : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) hR3 4
    have h4 : (x ^ (1 / 21 : ℝ)) ^ 4 = x ^ (4 / 21 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    rw [mul_pow, h4] at h3
    linarith
  have hl : Real.log x ≤ 42 * x ^ (1 / 42 : ℝ) := by
    have h3 := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 1 / 42 by norm_num)
    have h4 : x ^ (1 / 42 : ℝ) / (1 / 42) = 42 * x ^ (1 / 42 : ℝ) := by ring
    rwa [h4] at h3
  have hprod : x ^ (4 / 21 : ℝ) * x ^ (-(1 / 2 : ℝ)) * x ^ (1 / 42 : ℝ) = x ^ (-(2 / 7 : ℝ)) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
    norm_num
  have hδ2 : boxScale x ≤ 2 * x ^ (-(1 / 2 : ℝ)) * (42 * x ^ (1 / 42 : ℝ)) := by
    unfold boxScale
    exact mul_le_mul_of_nonneg_left hl (by positivity)
  calc c * (boxRadius κ₀ x : ℝ) ^ 4 * boxScale x ≤
      c * (16 * x ^ (4 / 21 : ℝ)) * (2 * x ^ (-(1 / 2 : ℝ)) * (42 * x ^ (1 / 42 : ℝ))) := by
        have : 0 ≤ x ^ (4 / 21 : ℝ) := (Real.rpow_pos_of_pos hx0 _).le
        exact mul_le_mul (mul_le_mul_of_nonneg_left hR4 hc.le) hδ2 hδ.le (by positivity)
    _ = 1344 * c * (x ^ (4 / 21 : ℝ) * x ^ (-(1 / 2 : ℝ)) * x ^ (1 / 42 : ℝ)) := by ring
    _ = 1344 * c * x ^ (-(2 / 7 : ℝ)) := by rw [hprod]
    _ ≤ 1 := by
        have h5 : 0 < 1344 * c := by positivity
        have h6 : 1344 * c * x ^ (-(2 / 7 : ℝ)) ≤ 1344 * c * (1 / (1344 * c)) :=
          mul_le_mul_of_nonneg_left a2.le h5.le
        have h7 : 1344 * c * (1 / (1344 * c)) = 1 := by field_simp
        linarith
end Sizes
section Slice
variable {n : ℕ} [NeZero n]
private def siteDivergence (ζ : TorusBond n → imaginaryQuaternions) (x : TorusSite n) : imaginaryQuaternions :=
  ∑ i, (ζ (x, i) - ζ (x - unitStep n i, i))
private theorem sum_inner_grad_eq_divergence (ζ : TorusBond n → imaginaryQuaternions)
    (χ : TorusSite n → imaginaryQuaternions) :
    ∑ b : TorusBond n, inner ℝ (ζ b) (χ b.1 - χ (b.1 + unitStep n b.2)) =
      ∑ x, (inner ℝ (siteDivergence ζ x) (χ x) : ℝ) := by
  have h1 : ∑ b : TorusBond n, (inner ℝ (ζ b) (χ b.1 - χ (b.1 + unitStep n b.2)) : ℝ) =
      ∑ i : Fin 4, ∑ x : TorusSite n, (inner ℝ (ζ (x, i)) (χ x - χ (x + unitStep n i)) : ℝ) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have h2 : ∑ x, (inner ℝ (siteDivergence ζ x) (χ x) : ℝ) =
      ∑ i : Fin 4, ∑ x : TorusSite n, (inner ℝ (ζ (x, i) - ζ (x - unitStep n i, i)) (χ x) : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [siteDivergence, sum_inner]
  rw [h1, h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∑ x, (inner ℝ (ζ (x - unitStep n i, i)) (χ x) : ℝ) =
      ∑ x, (inner ℝ (ζ (x, i)) (χ (x + unitStep n i)) : ℝ) := by
    rw [← sum_add_right_eq (fun x => (inner ℝ (ζ (x - unitStep n i, i)) (χ x) : ℝ)) (unitStep n i)]
    simp
  simp only [inner_sub_left, inner_sub_right, Finset.sum_sub_distrib]
  rw [e]
private theorem divergence_sq_small_on_slice (o : TorusSite n) (R : ℕ) (A ζ : TorusBond n → imaginaryQuaternions)
    (hζ : ζ ∈ gaugeSlice o R A) (ε : ℝ) (hε : 0 ≤ ε)
    (hAd : ∀ b ∈ bondsTouching o R, ∀ X : imaginaryQuaternions, ‖_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A b)) X - X‖ ≤ ε * ‖X‖) :
    ∑ x ∈ supBall o (R : ℝ), ‖siteDivergence ζ x‖ ^ 2 ≤ 4 * ε ^ 2 * ∑ b, ‖ζ b‖ ^ 2 := by
  classical
  obtain ⟨hz0, hz1⟩ := hζ
  set B := supBall o (R : ℝ) with hB
  set χ : TorusSite n → imaginaryQuaternions := fun x => if x ∈ B then siteDivergence ζ x else 0 with hχ
  have hχ0 : ∀ z, z ∉ B → χ z = 0 := fun z hz => by simp [hχ, hz]
  have hs := hz1 χ hχ0
  set Q := ∑ x ∈ B, ‖siteDivergence ζ x‖ ^ 2 with hQ
  set Z := ∑ b, ‖ζ b‖ ^ 2 with hZ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => by positivity
  have hQ1 : Q = ∑ x, (inner ℝ (siteDivergence ζ x) (χ x) : ℝ) := by
    rw [hQ, ← Finset.sum_subset (Finset.subset_univ B) fun x _ hx => by rw [hχ0 x hx, inner_zero_right]]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [hχ, if_pos hx]
    rw [real_inner_self_eq_norm_sq]
  have hQ2 : Q = ∑ x, ‖χ x‖ ^ 2 := by
    rw [hQ, ← Finset.sum_subset (Finset.subset_univ B) fun x _ hx => by rw [hχ0 x hx, norm_zero]; norm_num]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [hχ, if_pos hx]
  have hQ3 : Q = ∑ b : TorusBond n, inner ℝ (ζ b)
      (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A b)) (χ (b.1 + unitStep n b.2)) - χ (b.1 + unitStep n b.2)) := by
    rw [hQ1, ← sum_inner_grad_eq_divergence]
    have : ∀ b : TorusBond n, (inner ℝ (ζ b) (χ b.1 - χ (b.1 + unitStep n b.2)) : ℝ) =
        inner ℝ (ζ b) (covariantGrad A χ b) +
          inner ℝ (ζ b) (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A b)) (χ (b.1 + unitStep n b.2)) - χ (b.1 + unitStep n b.2)) := by
      intro b
      rw [← inner_add_right]
      congr 1
      unfold covariantGrad
      abel
    simp only [this, Finset.sum_add_distrib]
    rw [hs, zero_add]
  have hb : ∀ b : TorusBond n, (inner ℝ (ζ b)
      (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A b)) (χ (b.1 + unitStep n b.2)) - χ (b.1 + unitStep n b.2)) : ℝ) ≤
      ε * (‖ζ b‖ * ‖χ (b.1 + unitStep n b.2)‖) := by
    intro b
    by_cases hbi : b ∈ bondsTouching o R
    · refine (real_inner_le_norm _ _).trans ?_
      have := hAd b hbi (χ (b.1 + unitStep n b.2))
      nlinarith [norm_nonneg (ζ b)]
    · rw [hz0 b hbi]
      simp
  have hSum : Q ≤ ε * ∑ b : TorusBond n, ‖ζ b‖ * ‖χ (b.1 + unitStep n b.2)‖ := by
    rw [hQ3, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => hb b
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (TorusBond n)) (fun b => ‖ζ b‖)
    (fun b => ‖χ (b.1 + unitStep n b.2)‖)
  have hFour : ∑ b : TorusBond n, ‖χ (b.1 + unitStep n b.2)‖ ^ 2 = 4 * Q := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have : ∀ i : Fin 4, ∑ x : TorusSite n, ‖χ (x + unitStep n i)‖ ^ 2 = Q := fun i => by
      rw [hQ2]
      exact sum_add_right_eq (fun x => ‖χ x‖ ^ 2) (unitStep n i)
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [hFour] at hCS
  have hsq : Q ^ 2 ≤ ε ^ 2 * (Z * (4 * Q)) := by
    have h1 : Q ^ 2 ≤ (ε * ∑ b : TorusBond n, ‖ζ b‖ * ‖χ (b.1 + unitStep n b.2)‖) ^ 2 :=
      pow_le_pow_left₀ hQ0 hSum 2
    rw [mul_pow] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hCS (by positivity))
  rcases hQ0.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · have : Q * Q ≤ (4 * ε ^ 2 * Z) * Q := by nlinarith
    exact le_of_mul_le_mul_right this hpos
private theorem form_eq_zero_of_far {o : TorusSite n} {R : ℕ} {ζ : TorusBond n → imaginaryQuaternions}
    (hz : ∀ b, b ∉ bondsTouching o R → ζ b = 0)
    {y : TorusSite n} {i k : Fin 4} (hk : k ≠ i) (hy : R < axisOffset o y k) : ζ (y, i) = 0 := by
  apply hz
  simp only [bondsTouching, Finset.mem_filter, Finset.mem_univ, true_and, mem_supBall_iff_axisOffset, not_or]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h k
    omega
  · have := h k
    rw [axisOffset_add_unitStep_of_ne o y hk] at this
    omega
private theorem bond_not_mem_bondsTouching (hn : 2 ≤ n) {o x : TorusSite n} {R : ℕ} {l : Fin 4}
    (h : R + 2 < axisOffset o x l) (k : Fin 4) :
    (x, k) ∉ bondsTouching o R := by
  simp only [bondsTouching, Finset.mem_filter, Finset.mem_univ, true_and, mem_supBall_iff_axisOffset, not_or]
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have := h1 l
    omega
  · have a1 := h1 l
    have a2 := axisOffset_le_add_unitStep hn o x k l
    omega
private theorem shifted_bond_not_mem_bondsTouching (hn : 2 ≤ n) {o x : TorusSite n} {R : ℕ} {l : Fin 4}
    (h : R + 2 < axisOffset o x l) (i k : Fin 4) :
    (x + unitStep n i, k) ∉ bondsTouching o R := by
  simp only [bondsTouching, Finset.mem_filter, Finset.mem_univ, true_and, mem_supBall_iff_axisOffset, not_or]
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have a1 := h1 l
    have a2 := axisOffset_le_add_unitStep hn o x i l
    omega
  · have a1 := h1 l
    have a2 := axisOffset_le_add_unitStep hn o x i l
    have a3 := axisOffset_le_add_unitStep hn o (x + unitStep n i) k l
    omega
private theorem lieFormCurl_eq_zero_off_cube (hn : 2 ≤ n) {o : TorusSite n} {R : ℕ} (hR : 4 ≤ R)
    {ζ : TorusBond n → imaginaryQuaternions}
    (hz : ∀ b, b ∉ bondsTouching o R → ζ b = 0) (p : TorusPlaquette n)
    (hp : ¬ ∀ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, z ∈ supBall o (2 * (R : ℝ))) : lieFormCurl ζ p = 0 := by
  obtain ⟨x, i, j⟩ := p
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hp
  have hfar : ∃ l, R + 2 < axisOffset o x l := by
    by_contra hc
    push_neg at hc
    apply hp
    have s1 := axisOffset_add_unitStep_le hn o x i
    have s2 := axisOffset_add_unitStep_le hn o x j
    have s3 := axisOffset_add_unitStep_le hn o (x + unitStep n i) j
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [mem_supBall_two_mul_iff] <;> intro l
    · have := hc l
      omega
    · have := hc l
      have := s1 l
      omega
    · have := hc l
      have := s2 l
      omega
    · have := hc l
      have := s1 l
      have := s3 l
      omega
  obtain ⟨l, hl⟩ := hfar
  simp only [lieFormCurl]
  rw [hz _ (bond_not_mem_bondsTouching hn hl i), hz _ (bond_not_mem_bondsTouching hn hl j),
    hz _ (shifted_bond_not_mem_bondsTouching hn hl i j), hz _ (shifted_bond_not_mem_bondsTouching hn hl j i)]
  simp
private theorem sum_discreteCurl_eq_curlNormSq (hn : 2 ≤ n) {o : TorusSite n} {R : ℕ} (hR : 4 ≤ R)
    {ζ : TorusBond n → imaginaryQuaternions}
    (hz : ∀ b, b ∉ bondsTouching o R → ζ b = 0) :
    ∑ i, ∑ j, (if i < j then ∑ x, ‖discreteCurl (unitStep n) (fun i x => ζ (x, i)) x i j‖ ^ 2 else 0) =
      curlNormSq (supBall o (2 * (R : ℝ))) ζ := by
  classical
  have h : ∀ i j : Fin 4,
      (if i < j then ∑ x, ‖discreteCurl (unitStep n) (fun i x => ζ (x, i)) x i j‖ ^ 2 else 0) =
      ∑ x, (if i < j then ‖lieFormCurl ζ (x, i, j)‖ ^ 2 else 0) := by
    intro i j
    split_ifs
    · rfl
    · simp
  have e1 : ∑ i, ∑ j, (if i < j then ∑ x, ‖discreteCurl (unitStep n) (fun i x => ζ (x, i)) x i j‖ ^ 2 else 0) =
      ∑ p : TorusPlaquette n, (if p.2.1 < p.2.2 then ‖lieFormCurl ζ p‖ ^ 2 else 0) := by
    calc _ = ∑ i : Fin 4, ∑ j : Fin 4, ∑ x : TorusSite n,
          (if i < j then ‖lieFormCurl ζ (x, i, j)‖ ^ 2 else 0) := by
          simp only [h]
      _ = ∑ i : Fin 4, ∑ x : TorusSite n, ∑ j : Fin 4, (if i < j then ‖lieFormCurl ζ (x, i, j)‖ ^ 2 else 0) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ x : TorusSite n, ∑ i : Fin 4, ∑ j : Fin 4, (if i < j then ‖lieFormCurl ζ (x, i, j)‖ ^ 2 else 0) :=
          Finset.sum_comm
      _ = _ := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Fintype.sum_prod_type]
  rw [e1, ← Finset.sum_filter, curlNormSq]
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hp.1
  · intro p hp hnot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hc : ¬ ∀ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, z ∈ supBall o (2 * (R : ℝ)) := by
      intro hall
      apply hnot
      simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hp, hall⟩
    rw [lieFormCurl_eq_zero_off_cube hn hR hz p hc]
    simp
end Slice
section Control
variable {n : ℕ} [NeZero n]
private theorem sum_ite_ne_const (c : ℝ) (i : Fin 4) : ∑ j, (if i = j then (0 : ℝ) else c) = 3 * c := by
  fin_cases i <;> simp [Fin.sum_univ_four] <;> ring
private theorem form_sq_le_curl_div (hn : 2 ≤ n) (o : TorusSite n) (R : ℕ) (hR : 4 ≤ R) (hRn : R + 1 ≤ n / 2)
    {ζ : TorusBond n → imaginaryQuaternions}
    (hz : ∀ b, b ∉ bondsTouching o R → ζ b = 0) :
    3 * ∑ b, ‖ζ b‖ ^ 2 ≤ 2 * ((R : ℝ) + 1) ^ 2 * (curlNormSq (supBall o (2 * (R : ℝ))) ζ +
      ∑ x ∈ supBall o (R : ℝ), ‖siteDivergence ζ x‖ ^ 2) := by
  set f : Fin 4 → TorusSite n → imaginaryQuaternions := fun i x => ζ (x, i) with hf
  have hS : ∀ x, x ∉ supBall o (R : ℝ) → ∀ i j, i ≠ j →
      inner ℝ (f i x - f i (x - unitStep n i)) (f j x - f j (x - unitStep n j)) = (0 : ℝ) := by
    intro x hx i j hij
    rw [mem_supBall_iff_axisOffset] at hx
    push_neg at hx
    obtain ⟨k, hk⟩ := hx
    by_cases hki : k = i
    · have hkj : k ≠ j := fun h => hij (hki.symm.trans h)
      have e1 : f j x = 0 := form_eq_zero_of_far hz hkj hk
      have e2 : f j (x - unitStep n j) = 0 :=
        form_eq_zero_of_far hz hkj (by rwa [axisOffset_sub_unitStep_of_ne o x hkj])
      rw [e1, e2]
      simp
    · have e1 : f i x = 0 := form_eq_zero_of_far hz hki hk
      have e2 : f i (x - unitStep n i) = 0 :=
        form_eq_zero_of_far hz hki (by rwa [axisOffset_sub_unitStep_of_ne o x hki])
      rw [e1, e2]
      simp
  have hb := offdiag_diff_le_curl_add_div (unitStep n) f (supBall o (R : ℝ)) hS
  rw [sum_discreteCurl_eq_curlNormSq hn hR hz] at hb
  have hdiv : ∀ x, ∑ i, (f i x - f i (x - unitStep n i)) = siteDivergence ζ x := fun x => rfl
  simp only [hdiv] at hb
  set Z : Fin 4 → ℝ := fun i => ∑ x, ‖ζ (x, i)‖ ^ 2 with hZ
  have hp : ∀ i j, (if i = j then (0 : ℝ) else Z i) ≤
      2 * ((R : ℝ) + 1) ^ 2 * (if i = j then 0 else ∑ x, ‖f i x - f i (x + unitStep n j)‖ ^ 2) := by
    intro i j
    split_ifs with h
    · simp
    · exact sum_norm_sq_le_poincare o R j hRn (f i) fun y hy => form_eq_zero_of_far hz (Ne.symm h) hy
  have htot : ∑ b, ‖ζ b‖ ^ 2 = ∑ i, Z i := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have h3 : 3 * ∑ i, Z i = ∑ i, ∑ j, (if i = j then (0 : ℝ) else Z i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (sum_ite_ne_const (Z i) i).symm
  rw [htot, h3]
  calc ∑ i, ∑ j, (if i = j then (0 : ℝ) else Z i) ≤
      ∑ i, ∑ j, 2 * ((R : ℝ) + 1) ^ 2 * (if i = j then 0 else ∑ x, ‖f i x - f i (x + unitStep n j)‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hp i j
    _ = 2 * ((R : ℝ) + 1) ^ 2 * ∑ i, ∑ j, (if i = j then 0 else ∑ x, ‖f i x - f i (x + unitStep n j)‖ ^ 2) := by
        simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)
private theorem mem_bondsWithin_of_mem_bondsTouching (hn : 2 ≤ n) {o : TorusSite n} {R : ℕ} (hR : 1 ≤ R)
    {b : TorusBond n} (hb : b ∈ bondsTouching o R) :
    b ∈ bondsWithin (supBall o (2 * (R : ℝ))) := by
  classical
  simp only [bondsTouching, Finset.mem_filter, Finset.mem_univ, true_and, mem_supBall_iff_axisOffset] at hb
  simp only [bondsWithin, Finset.mem_filter, Finset.mem_univ, true_and, mem_supBall_two_mul_iff]
  rcases hb with h | h
  · refine ⟨fun l => ?_, fun l => ?_⟩
    · have := h l
      omega
    · have a1 := h l
      have a2 := axisOffset_add_unitStep_le hn o b.1 b.2 l
      omega
  · refine ⟨fun l => ?_, fun l => ?_⟩
    · have a1 := h l
      have a2 := axisOffset_le_add_unitStep hn o b.1 b.2 l
      omega
    · have := h l
      omega
private theorem slice_form_sq_le_curl (hn : 2 ≤ n) (o : TorusSite n) (R : ℕ) (hR : 20 ≤ R) (hRn : R + 1 ≤ n / 2)
    (δ : ℝ) (hδ : 0 < δ)
    (hsm : 128 * (R : ℝ) ^ 2 * δ ≤ 1) {A ζ : TorusBond n → imaginaryQuaternions}
    (hA : ∀ b ∈ bondsWithin (supBall o (2 * (R : ℝ))), ‖A b‖ ≤ 7 * R * δ) (hζ : ζ ∈ gaugeSlice o R A) :
    ∑ b, ‖ζ b‖ ^ 2 ≤ (R : ℝ) ^ 2 * curlNormSq (supBall o (2 * (R : ℝ))) ζ := by
  have hR1 : 1 ≤ R := by omega
  have hRr : (20 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have h1 := form_sq_le_curl_div hn o R (by omega) hRn hζ.1
  have h2 := divergence_sq_small_on_slice o R A ζ hζ (14 * R * δ) (by positivity) (fun b hb X => by
    have a1 := norm_adjointAction_exp_sub_le (A b) X
    have a2 := hA b (mem_bondsWithin_of_mem_bondsTouching hn hR1 hb)
    have a3 : 2 * ‖A b‖ * ‖X‖ ≤ 14 * R * δ * ‖X‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      linarith
    exact a1.trans a3)
  set Z := ∑ b, ‖ζ b‖ ^ 2 with hZ
  set P := curlNormSq (supBall o (2 * (R : ℝ))) ζ with hP
  set Q := ∑ x ∈ supBall o (R : ℝ), ‖siteDivergence ζ x‖ ^ 2 with hQ
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => by positivity
  have s1 : 2 * ((R : ℝ) + 1) ^ 2 ≤ (5 / 2) * (R : ℝ) ^ 2 := by nlinarith
  have s2 : 4 * (14 * (R : ℝ) * δ) ^ 2 * (R : ℝ) ^ 2 ≤ 1 / 8 := by
    have e : 4 * (14 * (R : ℝ) * δ) ^ 2 * (R : ℝ) ^ 2 = 784 * ((R : ℝ) ^ 2 * δ) ^ 2 := by ring
    have a0 : 0 ≤ (R : ℝ) ^ 2 * δ := by positivity
    have a1 : (R : ℝ) ^ 2 * δ ≤ 1 / 128 := by linarith
    have a2 : ((R : ℝ) ^ 2 * δ) ^ 2 ≤ (1 / 128) ^ 2 := pow_le_pow_left₀ a0 a1 2
    rw [e]
    nlinarith
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun _ _ => by positivity
  have h3 : 3 * Z ≤ (5 / 2) * (R : ℝ) ^ 2 * (P + Q) := h1.trans (mul_le_mul_of_nonneg_right s1 (by positivity))
  have h4 : (R : ℝ) ^ 2 * Q ≤ (1 / 8) * Z := by
    have a1 : (R : ℝ) ^ 2 * Q ≤ (R : ℝ) ^ 2 * (4 * (14 * (R : ℝ) * δ) ^ 2 * Z) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have a2 : (R : ℝ) ^ 2 * (4 * (14 * (R : ℝ) * δ) ^ 2 * Z) = (4 * (14 * (R : ℝ) * δ) ^ 2 * (R : ℝ) ^ 2) * Z := by
      ring
    have a3 := mul_le_mul_of_nonneg_right s2 hZ0
    linarith
  nlinarith
end Control
section Assembly
variable {n : ℕ} [NeZero n]
private theorem bond_log_real_bounds {a z b V : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 100) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1 / 100) (hb0 : 0 ≤ b) (hb : b ≤ 2 * (a ^ 2 + z ^ 2)) (hV0 : 0 ≤ V) (hV : V ≤ a + z + b) :
    V ≤ 2 * (a + z) ∧ V ^ 2 ≤ 8 * (a ^ 2 + z ^ 2) ∧ b ^ 2 ≤ 8 * (a ^ 2 * a ^ 2 + z ^ 2 * z ^ 2) := by
  have h1 : a ^ 2 ≤ a / 100 := by nlinarith
  have h2 : z ^ 2 ≤ z / 100 := by nlinarith
  have h3 : V ≤ 2 * (a + z) := by linarith
  refine ⟨h3, ?_, ?_⟩
  · have h4 : V ^ 2 ≤ (2 * (a + z)) ^ 2 := pow_le_pow_left₀ hV0 h3 2
    nlinarith [sq_nonneg (a - z)]
  · have h4 : b ^ 2 ≤ (2 * (a ^ 2 + z ^ 2)) ^ 2 := pow_le_pow_left₀ hb0 hb 2
    nlinarith [sq_nonneg (a ^ 2 - z ^ 2)]
private theorem scale_real_bounds {r δ K : ℝ} (hr : 1 ≤ r) (hδ : 0 < δ) (hK : 1 ≤ K)
    (hsm : 2 ^ 10 * K * r ^ 4 * δ ≤ 1) :
    7 * r * δ ≤ 1 / 100 ∧ K * r ^ 3 * δ ≤ 1 / 100 ∧ 7 * r * δ ≤ 7 * (r ^ 3 * δ) ∧
      2 * (7 + K) * (r ^ 3 * δ) ≤ 1 ∧ r ^ 2 * δ ^ 2 ≤ r ^ 2 * δ ∧ r ^ 6 * δ ^ 2 ≤ r ^ 2 * δ := by
  have p2 : 1 ≤ r ^ 2 := one_le_pow₀ hr
  have p3 : 1 ≤ r ^ 3 := one_le_pow₀ hr
  have p4 : 1 ≤ r ^ 4 := one_le_pow₀ hr
  have r13 : r ≤ r ^ 3 := by nlinarith
  have r34 : r ^ 3 ≤ r ^ 4 := by nlinarith
  have t0 : 0 < r ^ 4 * δ := by positivity
  have t2 : 2 ^ 10 * (r ^ 4 * δ) ≤ 1 := by
    have : 2 ^ 10 * 1 * (r ^ 4 * δ) ≤ 2 ^ 10 * K * (r ^ 4 * δ) :=
      mul_le_mul_of_nonneg_right (by linarith) t0.le
    linarith
  have t3 : r ^ 3 * δ ≤ r ^ 4 * δ := mul_le_mul_of_nonneg_right r34 hδ.le
  have t4 : r * δ ≤ r ^ 3 * δ := mul_le_mul_of_nonneg_right r13 hδ.le
  have t5 : K * (r ^ 3 * δ) ≤ K * (r ^ 4 * δ) := mul_le_mul_of_nonneg_left t3 (by linarith)
  have t6 : δ ≤ r ^ 4 * δ := by nlinarith
  refine ⟨by linarith, by linarith [mul_assoc K (r ^ 3) δ], by linarith, by nlinarith, ?_, ?_⟩
  · have : δ ^ 2 ≤ δ := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  · have e : r ^ 6 * δ ^ 2 = (r ^ 2 * δ) * (r ^ 4 * δ) := by ring
    rw [e]
    have h0 : 0 ≤ r ^ 2 * δ := by positivity
    nlinarith
private theorem curvature_real_bound {K r δ B c V : ℝ} (hK : 1 ≤ K) (hr : 1 ≤ r) (hδ : 0 < δ)
    (h1 : r ^ 2 * δ ^ 2 ≤ r ^ 2 * δ) (h2 : r ^ 6 * δ ^ 2 ≤ r ^ 2 * δ)
    (hB : B ≤ 2 * (49 * (r ^ 2 * δ ^ 2) + K ^ 2 * (r ^ 6 * δ ^ 2))) (hc : c ≤ K * (r ^ 2 * δ))
    (hV : V ^ 2 ≤ 4 * (7 + K) ^ 2 * (r ^ 6 * δ ^ 2)) :
    c + 4 * B + 15 * V ^ 2 ≤ (2 ^ 26 * K ^ 3) * r ^ 2 * δ := by
  set T := r ^ 2 * δ with hT
  have hT0 : 0 ≤ T := by positivity
  have k2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have k3 : K ≤ K ^ 3 := by nlinarith
  have k23 : K ^ 2 ≤ K ^ 3 := by nlinarith
  have b2 : K ^ 2 * (r ^ 6 * δ ^ 2) ≤ K ^ 2 * T := mul_le_mul_of_nonneg_left h2 (by positivity)
  have b3 : 4 * (7 + K) ^ 2 * (r ^ 6 * δ ^ 2) ≤ 4 * (7 + K) ^ 2 * T := mul_le_mul_of_nonneg_left h2 (by positivity)
  have b4 : (7 + K) ^ 2 ≤ 64 * K ^ 2 := by nlinarith
  have b5 : (4 * (7 + K) ^ 2) * T ≤ (4 * (64 * K ^ 2)) * T := mul_le_mul_of_nonneg_right (by linarith) hT0
  have e : (2 ^ 26 * K ^ 3) * r ^ 2 * δ = (2 ^ 26 * K ^ 3) * T := by rw [hT]; ring
  rw [e]
  have c2 : K ^ 2 * T ≤ K ^ 3 * T := mul_le_mul_of_nonneg_right k23 hT0
  have c3 : T ≤ K ^ 3 * T := by nlinarith
  nlinarith
private theorem square_sum_real_bounds {K r δ : ℝ} (hK : 1 ≤ K) (hr : 1 ≤ r) (hδ : 0 < δ) :
    8 * (2 ^ 16 * r ^ 6 * δ ^ 2 + K * r ^ 6 * δ ^ 2) ≤ (2 ^ 26 * K ^ 3) * r ^ 6 * δ ^ 2 ∧
    8 * ((7 * r * δ) ^ 2 * (2 ^ 16 * r ^ 6 * δ ^ 2) + (K * r ^ 3 * δ) ^ 2 * (K * r ^ 6 * δ ^ 2)) ≤
      (2 ^ 26 * K ^ 3) * r ^ 12 * δ ^ 4 := by
  have k3 : K ≤ K ^ 3 := by nlinarith [one_le_pow₀ (n := 2) hK]
  constructor
  · have h0 : 0 ≤ r ^ 6 * δ ^ 2 := by positivity
    have e1 : 8 * (2 ^ 16 * r ^ 6 * δ ^ 2 + K * r ^ 6 * δ ^ 2) = (8 * (2 ^ 16 + K)) * (r ^ 6 * δ ^ 2) := by ring
    have e2 : (2 ^ 26 * K ^ 3) * r ^ 6 * δ ^ 2 = (2 ^ 26 * K ^ 3) * (r ^ 6 * δ ^ 2) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (by nlinarith) h0
  · have h0 : 0 ≤ r ^ 12 * δ ^ 4 := by positivity
    have r8 : r ^ 8 ≤ r ^ 12 := pow_le_pow_right₀ hr (by norm_num)
    have e1 : 8 * ((7 * r * δ) ^ 2 * (2 ^ 16 * r ^ 6 * δ ^ 2) + (K * r ^ 3 * δ) ^ 2 * (K * r ^ 6 * δ ^ 2)) =
        8 * (49 * 2 ^ 16) * (r ^ 8 * δ ^ 4) + 8 * K ^ 3 * (r ^ 12 * δ ^ 4) := by ring
    have e2 : (2 ^ 26 * K ^ 3) * r ^ 12 * δ ^ 4 = (2 ^ 26 * K ^ 3) * (r ^ 12 * δ ^ 4) := by ring
    rw [e1, e2]
    have h1 : r ^ 8 * δ ^ 4 ≤ r ^ 12 * δ ^ 4 := mul_le_mul_of_nonneg_right r8 (by positivity)
    nlinarith
private theorem norm_curl_sq_le_curlNormSq {S : Finset (TorusSite n)} {u : TorusBond n → imaginaryQuaternions}
    {p : TorusPlaquette n} (hp : p ∈ plaquettesIn S) :
    ‖lieFormCurl u p‖ ^ 2 ≤ curlNormSq S u :=
  Finset.single_le_sum (f := fun p => ‖lieFormCurl u p‖ ^ 2) (fun _ _ => by positivity) hp
private theorem plaquette_bonds_mem {S : Finset (TorusSite n)} {p : TorusPlaquette n} (hp : p ∈ plaquettesIn S) :
    (p.1, p.2.1) ∈ bondsWithin S ∧ (p.1 + unitStep n p.2.1, p.2.2) ∈ bondsWithin S ∧
      (p.1 + unitStep n p.2.2, p.2.1) ∈ bondsWithin S ∧ (p.1, p.2.2) ∈ bondsWithin S := by apply _root_.YangMills.SharedProofs.p50589 <;> assumption
private theorem chart_log_bounds (S : Finset (TorusSite n)) (R : ℕ) (hR : 1 ≤ R) (δ K₁ : ℝ) (hδ : 0 < δ)
    (hK : 1 ≤ K₁)
    (hsm : 2 ^ 10 * K₁ * (R : ℝ) ^ 4 * δ ≤ 1) (A ζ : TorusBond n → imaginaryQuaternions)
    (hA : ∀ b ∈ bondsWithin S, ‖A b‖ ≤ 7 * R * δ)
    (hAs : bondNormSq S A ≤ 2 ^ 16 * (R : ℝ) ^ 6 * δ ^ 2) (hz : ∀ b, ‖ζ b‖ ≤ K₁ * (R : ℝ) ^ 3 * δ)
    (hzs : bondNormSq S ζ ≤ K₁ * (R : ℝ) ^ 6 * δ ^ 2) (hc : curlNormSq S (A + ζ) ≤ K₁ * (R : ℝ) ^ 4 * δ ^ 2)
    (W : TorusField n) (hW : IsInChart S A ζ W) :
    ∃ v β : TorusBond n → imaginaryQuaternions,
      (∀ b ∈ bondsWithin S, W b.1 b.2 = expUnit (v b) ∧ v b = A b + ζ b + β b ∧
        ‖β b‖ ≤ 2 * (‖A b‖ ^ 2 + ‖ζ b‖ ^ 2) ∧ ‖v b‖ ≤ (2 ^ 26 * K₁ ^ 3) * (R : ℝ) ^ 3 * δ) ∧
      bondNormSq S v ≤ (2 ^ 26 * K₁ ^ 3) * (R : ℝ) ^ 6 * δ ^ 2 ∧
      bondNormSq S β ≤ (2 ^ 26 * K₁ ^ 3) * (R : ℝ) ^ 12 * δ ^ 4 ∧
      ∀ p ∈ plaquettesIn S, curvature W p.1 p.2.1 p.2.2 ≤ (2 ^ 26 * K₁ ^ 3) * (R : ℝ) ^ 2 * δ := by
  have hr : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := scale_real_bounds hr hδ hK hsm
  have H : ∀ b : TorusBond n, ∃ v : imaginaryQuaternions, b ∈ bondsWithin S → W b.1 b.2 = expUnit v ∧
      ‖v - A b - ζ b‖ ≤ 2 * (‖A b‖ ^ 2 + ‖ζ b‖ ^ 2) := by
    intro b
    by_cases hb : b ∈ bondsWithin S
    · obtain ⟨v, h1, h2⟩ := chartPoint_log_near (A b) (ζ b) (W b.1 b.2) (hW b hb) ((hA b hb).trans s1)
        ((hz b).trans s2)
      exact ⟨v, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose v hv using H
  have hfacts : ∀ b ∈ bondsWithin S, ‖v b‖ ≤ 2 * (‖A b‖ + ‖ζ b‖) ∧ ‖v b‖ ^ 2 ≤ 8 * (‖A b‖ ^ 2 + ‖ζ b‖ ^ 2) ∧
      ‖v b - A b - ζ b‖ ^ 2 ≤ 8 * (‖A b‖ ^ 2 * ‖A b‖ ^ 2 + ‖ζ b‖ ^ 2 * ‖ζ b‖ ^ 2) := by
    intro b hb
    have e : v b = A b + ζ b + (v b - A b - ζ b) := by abel
    have n1 : ‖v b‖ ≤ ‖A b‖ + ‖ζ b‖ + ‖v b - A b - ζ b‖ := by
      conv_lhs => rw [e]
      exact norm_add₃_le
    exact bond_log_real_bounds (norm_nonneg _) ((hA b hb).trans s1) (norm_nonneg _) ((hz b).trans s2)
      (norm_nonneg _) (hv b hb).2 (norm_nonneg _) n1
  obtain ⟨S1, S2⟩ := square_sum_real_bounds (r := (R : ℝ)) hK hr hδ
  have hV₀ : ∀ b ∈ bondsWithin S, ‖v b‖ ≤ 2 * (7 + K₁) * ((R : ℝ) ^ 3 * δ) := by
    intro b hb
    have a1 := (hfacts b hb).1
    have a2 := (hA b hb).trans s3
    have a3 := hz b
    have a4 : K₁ * (R : ℝ) ^ 3 * δ = K₁ * ((R : ℝ) ^ 3 * δ) := by ring
    nlinarith
  refine ⟨v, fun b => v b - A b - ζ b, fun b hb => ⟨(hv b hb).1,
    by show v b = A b + ζ b + (v b - A b - ζ b); abel, (hv b hb).2, ?_⟩, ?_, ?_, ?_⟩
  · refine (hV₀ b hb).trans ?_
    have h0 : 0 ≤ (R : ℝ) ^ 3 * δ := by positivity
    have e : (2 ^ 26 * K₁ ^ 3) * (R : ℝ) ^ 3 * δ = (2 ^ 26 * K₁ ^ 3) * ((R : ℝ) ^ 3 * δ) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ h0
    have k3 : K₁ ≤ K₁ ^ 3 := by nlinarith [one_le_pow₀ (n := 2) hK]
    have k13 : 1 ≤ K₁ ^ 3 := one_le_pow₀ hK
    nlinarith
  · refine le_trans ?_ S1
    have : bondNormSq S v ≤ 8 * (bondNormSq S A + bondNormSq S ζ) := by
      unfold bondNormSq
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_le_sum fun b hb => (hfacts b hb).2.1
    have h2 : 8 * (bondNormSq S A + bondNormSq S ζ) ≤
        8 * (2 ^ 16 * (R : ℝ) ^ 6 * δ ^ 2 + K₁ * (R : ℝ) ^ 6 * δ ^ 2) := by
      linarith
    linarith
  · refine le_trans ?_ S2
    have h3 : bondNormSq S (fun b => v b - A b - ζ b) ≤
        8 * ((7 * (R : ℝ) * δ) ^ 2 * bondNormSq S A + (K₁ * (R : ℝ) ^ 3 * δ) ^ 2 * bondNormSq S ζ) := by
      unfold bondNormSq
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_le_sum fun b hb => (hfacts b hb).2.2.trans ?_
      have a1 : ‖A b‖ ^ 2 ≤ (7 * (R : ℝ) * δ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hA b hb) 2
      have a2 : ‖ζ b‖ ^ 2 ≤ (K₁ * (R : ℝ) ^ 3 * δ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hz b) 2
      have a3 := mul_le_mul_of_nonneg_right a1 (sq_nonneg ‖A b‖)
      have a4 := mul_le_mul_of_nonneg_right a2 (sq_nonneg ‖ζ b‖)
      linarith
    refine h3.trans ?_
    have a1 := mul_le_mul_of_nonneg_left hAs (sq_nonneg (7 * (R : ℝ) * δ))
    have a2 := mul_le_mul_of_nonneg_left hzs (sq_nonneg (K₁ * (R : ℝ) ^ 3 * δ))
    linarith
  · rintro ⟨x, i, j⟩ hp
    obtain ⟨b1, b2, b3, b4⟩ := plaquette_bonds_mem hp
    set V₀ := 2 * (7 + K₁) * ((R : ℝ) ^ 3 * δ) with hV₀def
    have w1 := (hv _ b1).1
    have w2 := (hv _ b2).1
    have w3 := (hv _ b3).1
    have w4 := (hv _ b4).1
    simp only at w1 w2 w3 w4 b1 b2 b3 b4
    have hpn := holonomy_exp_near_one (v (x, i)) (v (x + unitStep n i, j)) (v (x + unitStep n j, i)) (v (x, j)) s4
      (hV₀ _ b1) (hV₀ _ b2) (hV₀ _ b3) (hV₀ _ b4)
    simp only [curvature, holonomy]
    rw [w1, w2, w3, w4]
    refine hpn.trans ?_
    set B := 2 * (49 * ((R : ℝ) ^ 2 * δ ^ 2) + K₁ ^ 2 * ((R : ℝ) ^ 6 * δ ^ 2)) with hB
    have hβ : ∀ b ∈ bondsWithin S, ‖v b - A b - ζ b‖ ≤ B := by
      intro b hb
      refine (hv b hb).2.trans ?_
      have a1 : ‖A b‖ ^ 2 ≤ (7 * (R : ℝ) * δ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hA b hb) 2
      have a2 : ‖ζ b‖ ^ 2 ≤ (K₁ * (R : ℝ) ^ 3 * δ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hz b) 2
      have e1 : (7 * (R : ℝ) * δ) ^ 2 = 49 * ((R : ℝ) ^ 2 * δ ^ 2) := by ring
      have e2 : (K₁ * (R : ℝ) ^ 3 * δ) ^ 2 = K₁ ^ 2 * ((R : ℝ) ^ 6 * δ ^ 2) := by ring
      rw [hB]
      linarith
    have hcurl : ‖lieFormCurl (A + ζ) (x, i, j)‖ ≤ K₁ * ((R : ℝ) ^ 2 * δ) := by
      have a1 := (norm_curl_sq_le_curlNormSq (u := A + ζ) hp).trans hc
      have a2 : K₁ * (R : ℝ) ^ 4 * δ ^ 2 ≤ (K₁ * ((R : ℝ) ^ 2 * δ)) ^ 2 := by
        have e : (K₁ * ((R : ℝ) ^ 2 * δ)) ^ 2 = K₁ * (K₁ * ((R : ℝ) ^ 4 * δ ^ 2)) := by ring
        have e2 : K₁ * (R : ℝ) ^ 4 * δ ^ 2 = K₁ * (1 * ((R : ℝ) ^ 4 * δ ^ 2)) := by ring
        rw [e, e2]
        have h0 : 0 ≤ (R : ℝ) ^ 4 * δ ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK h0) (by linarith)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp (a1.trans a2)
    have hdecomp : v (x, i) + v (x + unitStep n i, j) - v (x + unitStep n j, i) - v (x, j) =
        lieFormCurl (A + ζ) (x, i, j) + ((v (x, i) - A (x, i) - ζ (x, i)) +
          (v (x + unitStep n i, j) - A (x + unitStep n i, j) - ζ (x + unitStep n i, j)) -
          (v (x + unitStep n j, i) - A (x + unitStep n j, i) - ζ (x + unitStep n j, i)) -
          (v (x, j) - A (x, j) - ζ (x, j))) := by
      simp only [lieFormCurl, Pi.add_apply]
      abel
    have hnorm : ‖v (x, i) + v (x + unitStep n i, j) - v (x + unitStep n j, i) - v (x, j)‖ ≤
        ‖lieFormCurl (A + ζ) (x, i, j)‖ + 4 * B := by
      rw [hdecomp]
      refine (norm_add_le _ _).trans ?_
      have n1 := norm_sub_le ((v (x, i) - A (x, i) - ζ (x, i)) +
          (v (x + unitStep n i, j) - A (x + unitStep n i, j) - ζ (x + unitStep n i, j)) -
          (v (x + unitStep n j, i) - A (x + unitStep n j, i) - ζ (x + unitStep n j, i)))
          (v (x, j) - A (x, j) - ζ (x, j))
      have n2 := norm_sub_le ((v (x, i) - A (x, i) - ζ (x, i)) +
          (v (x + unitStep n i, j) - A (x + unitStep n i, j) - ζ (x + unitStep n i, j)))
          (v (x + unitStep n j, i) - A (x + unitStep n j, i) - ζ (x + unitStep n j, i))
      have n3 := norm_add_le (v (x, i) - A (x, i) - ζ (x, i))
          (v (x + unitStep n i, j) - A (x + unitStep n i, j) - ζ (x + unitStep n i, j))
      have m1 := hβ _ b1
      have m2 := hβ _ b2
      have m3 := hβ _ b3
      have m4 := hβ _ b4
      linarith
    have hV2 : V₀ ^ 2 ≤ 4 * (7 + K₁) ^ 2 * ((R : ℝ) ^ 6 * δ ^ 2) := by
      rw [hV₀def]
      exact le_of_eq (by ring)
    have hfin := curvature_real_bound hK hr hδ s5 s6 (le_refl B) hcurl hV2
    linarith
end Assembly
theorem ellipsoidBounds_of_cubeHessian (hF : cubeHessianStatement) : ellipsoidBoundsStatement := by
  intro Tb hTb κ₀ h1 h2 C₀ hC₀
  obtain ⟨CQ, R₀, hCQ, hForm⟩ := hF Tb hTb
  have hcK : 0 < Tb.coercivity := hTb.cK_pos
  have hq0 : 0 < C₀ / Tb.coercivity := div_pos hC₀ hcK
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = C₀ / Tb.coercivity + 2 ^ 14 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K₁ := by
    rw [hK₁]
    norm_num
    linarith
  obtain ⟨xs, hxs⟩ := boxRadius_boxScale_eventually κ₀ h1 h2 (2 ^ 10 * K₁) (by positivity) (max R₀ 20)
  have hKbig : K₁ ≤ 2 ^ 26 * K₁ ^ 3 := by
    have k3 : K₁ ≤ K₁ ^ 3 := by nlinarith [one_le_pow₀ (n := 2) hK1]
    nlinarith
  refine ⟨2 ^ 26 * K₁ ^ 3, xs, by linarith, ?_⟩
  intro x R k n _ o A hx hRx hn hA
  obtain ⟨hRN, hδ, hsm⟩ := hxs x hx
  rw [← hRx] at hRN hsm
  generalize boxScale x = δ at *
  have hR₀ : R₀ ≤ R := (le_max_left _ _).trans hRN
  have hR20 : 20 ≤ R := (le_max_right _ _).trans hRN
  have hRn : R + 1 ≤ n / 2 := by omega
  have hn2 : 2 ≤ n := by omega
  obtain ⟨-, -, -, -, hQ, -, -⟩ := hForm k n o R hR₀ hn
  have hr : (1 : ℝ) ≤ (R : ℝ) := by
    have : (20 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR20
    linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hsm2 : 128 * (R : ℝ) ^ 2 * δ ≤ 1 := by
    have a1 : (R : ℝ) ^ 2 ≤ (R : ℝ) ^ 4 := pow_le_pow_right₀ hr (by norm_num)
    have a2 : 128 * 1 * (R : ℝ) ^ 2 * δ ≤ 2 ^ 10 * K₁ * (R : ℝ) ^ 4 * δ := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul (by linarith) a1 (by positivity) (by positivity)) hδ.le
    linarith
  have hSlice : ∀ ζ ∈ gaugeSlice o R A,
      ∑ b, ‖ζ b‖ ^ 2 ≤ (R : ℝ) ^ 2 * curlNormSq (supBall o (2 * (R : ℝ))) ζ :=
    fun ζ h => slice_form_sq_le_curl hn2 o R hR20 hRn δ hδ hsm2 hA.norm_le h
  have hsub : ∀ ζ : TorusBond n → imaginaryQuaternions,
      bondNormSq (supBall o (2 * (R : ℝ))) ζ ≤ ∑ b, ‖ζ b‖ ^ 2 := fun ζ =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
  refine ⟨fun ζ hζ => ?_, fun ζ hζ => ?_⟩
  · have a1 := (hSlice ζ hζ)
    have a2 := (hQ ζ).1
    have a3 := hsub ζ
    have e : 2 * Tb.coercivity * ((R : ℝ) ^ 2)⁻¹ * ((R : ℝ) ^ 2 * curlNormSq (supBall o (2 * (R : ℝ))) ζ) =
        2 * Tb.coercivity * curlNormSq (supBall o (2 * (R : ℝ))) ζ := by
      field_simp
    have a4 : 2 * Tb.coercivity * ((R : ℝ) ^ 2)⁻¹ * bondNormSq (supBall o (2 * (R : ℝ))) ζ ≤
        2 * Tb.coercivity * ((R : ℝ) ^ 2)⁻¹ * ((R : ℝ) ^ 2 * curlNormSq (supBall o (2 * (R : ℝ))) ζ) :=
      mul_le_mul_of_nonneg_left (a3.trans a1) (mul_nonneg (mul_nonneg zero_le_two hcK.le) (by positivity))
    linarith
  · obtain ⟨hsl, hq⟩ := hζ
    have hK₁0 : 0 ≤ K₁ := by linarith
    have c1 := (hQ (A + ζ)).1
    have c2 : 2 * curlNormSq (supBall o (2 * (R : ℝ))) (A + ζ) ≤ C₀ / Tb.coercivity * ((R : ℝ) ^ 4 * δ ^ 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hcK]
      linarith
    have c3 : curlNormSq (supBall o (2 * (R : ℝ))) ζ ≤
        2 * curlNormSq (supBall o (2 * (R : ℝ))) (A + ζ) + 2 * curlNormSq (supBall o (2 * (R : ℝ))) A := by
      unfold curlNormSq
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun p _ => ?_
      have e : lieFormCurl ζ p = lieFormCurl (A + ζ) p - lieFormCurl A p := by
        simp only [lieFormCurl, Pi.add_apply]
        abel
      rw [e]
      have n1 := norm_sub_le (lieFormCurl (A + ζ) p) (lieFormCurl A p)
      have n2 : ‖lieFormCurl (A + ζ) p - lieFormCurl A p‖ ^ 2 ≤ (‖lieFormCurl (A + ζ) p‖ + ‖lieFormCurl A p‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) n1 2
      nlinarith [sq_nonneg (‖lieFormCurl (A + ζ) p‖ - ‖lieFormCurl A p‖)]
    have hY : 0 ≤ (R : ℝ) ^ 4 * δ ^ 2 := by positivity
    have c4 : curlNormSq (supBall o (2 * (R : ℝ))) ζ ≤ K₁ * (R : ℝ) ^ 4 * δ ^ 2 := by
      have a1 := hA.curlNormSq_le
      rw [hK₁]
      nlinarith
    have c5 : curlNormSq (supBall o (2 * (R : ℝ))) (A + ζ) ≤ K₁ * (R : ℝ) ^ 4 * δ ^ 2 := by
      rw [hK₁]
      nlinarith
    have c6 : ∑ b, ‖ζ b‖ ^ 2 ≤ K₁ * (R : ℝ) ^ 6 * δ ^ 2 := by
      refine (hSlice ζ hsl).trans ?_
      have a1 := mul_le_mul_of_nonneg_left c4 (sq_nonneg (R : ℝ))
      have e : (R : ℝ) ^ 2 * (K₁ * (R : ℝ) ^ 4 * δ ^ 2) = K₁ * (R : ℝ) ^ 6 * δ ^ 2 := by ring
      linarith
    have c7 : ∀ b, ‖ζ b‖ ≤ K₁ * (R : ℝ) ^ 3 * δ := by
      intro b
      have a1 : ‖ζ b‖ ^ 2 ≤ ∑ b, ‖ζ b‖ ^ 2 :=
        Finset.single_le_sum (f := fun b => ‖ζ b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ b)
      have a2 : K₁ * (R : ℝ) ^ 6 * δ ^ 2 ≤ (K₁ * (R : ℝ) ^ 3 * δ) ^ 2 := by
        have e : (K₁ * (R : ℝ) ^ 3 * δ) ^ 2 = K₁ * (K₁ * ((R : ℝ) ^ 6 * δ ^ 2)) := by ring
        have e2 : K₁ * (R : ℝ) ^ 6 * δ ^ 2 = K₁ * (1 * ((R : ℝ) ^ 6 * δ ^ 2)) := by ring
        rw [e, e2]
        have h0 : 0 ≤ (R : ℝ) ^ 6 * δ ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK1 h0) hK₁0
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp ((a1.trans c6).trans a2)
    have hup : ∀ t : ℝ, 0 ≤ t → K₁ * t ≤ 2 ^ 26 * K₁ ^ 3 * t := fun t ht => mul_le_mul_of_nonneg_right hKbig ht
    refine ⟨?_, fun b => ?_, ?_, fun W hW => ?_⟩
    · have a1 := hup ((R : ℝ) ^ 6 * δ ^ 2) (by positivity)
      have a2 := (hsub ζ).trans c6
      linarith [mul_assoc K₁ ((R : ℝ) ^ 6) (δ ^ 2), mul_assoc (2 ^ 26 * K₁ ^ 3) ((R : ℝ) ^ 6) (δ ^ 2)]
    · have a1 := hup ((R : ℝ) ^ 3 * δ) (by positivity)
      have a2 := c7 b
      linarith [mul_assoc K₁ ((R : ℝ) ^ 3) δ, mul_assoc (2 ^ 26 * K₁ ^ 3) ((R : ℝ) ^ 3) δ]
    · have a1 := hup ((R : ℝ) ^ 4 * δ ^ 2) (by positivity)
      linarith [mul_assoc K₁ ((R : ℝ) ^ 4) (δ ^ 2), mul_assoc (2 ^ 26 * K₁ ^ 3) ((R : ℝ) ^ 4) (δ ^ 2)]
    · exact chart_log_bounds _ R (by omega) δ K₁ hδ hK1 hsm A ζ hA.norm_le hA.bondNormSq_le c7
        ((hsub ζ).trans c6) c5 W hW
end YangMills.Construction.BoxGaussian
end

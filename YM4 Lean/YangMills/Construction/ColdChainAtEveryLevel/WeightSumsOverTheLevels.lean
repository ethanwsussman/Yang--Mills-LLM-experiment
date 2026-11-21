import YangMills.Construction.ColdChainAtEveryLevel.WeightChains
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.WeightedAverages.Sums
open BlockAverages WeightedAverages.Chains BlockLines
variable {F : BlockFrame}
theorem card_le_of_cellSupDist_le (b : F.Cell) (r : ℕ) [DecidableEq F.Cell] (A : Finset F.Cell)
    (hA : ∀ z ∈ A, cellSupDist z b ≤ r) : A.card ≤ (2 * r + 1) ^ 4 := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.card_le_of_cellSupDist_le <;> assumption
def expCountSum (δ : ℝ) : ℝ := ∑' k : ℕ, (2 * (k : ℝ) + 1) ^ 4 * Real.exp (-(2 * δ) * k)
theorem summable_expCountSum {δ : ℝ} (hδ : 0 < δ) :
    Summable fun k : ℕ => (2 * (k : ℝ) + 1) ^ 4 * Real.exp (-(2 * δ) * k) := by
  have h4 := Real.summable_pow_mul_exp_neg_nat_mul 4 (r := 2 * δ) (by positivity)
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 (r := 2 * δ) (by positivity)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) ((h4.mul_left 81).add h0)
  have hk : (2 * (k : ℝ) + 1) ^ 4 ≤ 81 * (k : ℝ) ^ 4 + 1 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      norm_num
    · have h1 : (1 : ℝ) ≤ k := by exact_mod_cast h
      have h2 : 2 * (k : ℝ) + 1 ≤ 3 * k := by linarith
      have h3 := pow_le_pow_left₀ (by positivity) h2 4
      nlinarith
  have he := Real.exp_pos (-(2 * δ) * k)
  calc (2 * (k : ℝ) + 1) ^ 4 * Real.exp (-(2 * δ) * k)
      ≤ (81 * (k : ℝ) ^ 4 + 1) * Real.exp (-(2 * δ) * k) := mul_le_mul_of_nonneg_right hk he.le
    _ = _ := by simp; ring
theorem expCountSum_nonneg {δ : ℝ} : 0 ≤ expCountSum δ :=
  tsum_nonneg fun k => by positivity
theorem sum_exp_cellSupDist_le {δ : ℝ} (hδ : 0 < δ) (S : Finset F.Cell) (y₀ : F.Cell) :
    ∑ z ∈ S, Real.exp (-(2 * δ) * cellSupDist z y₀) ≤ expCountSum δ := by
  classical
  set K := S.sup fun z => cellSupDist z y₀ with hK
  have hmaps : ∀ z ∈ S, cellSupDist z y₀ ∈ Finset.range (K + 1) := fun z hz =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := fun z => cellSupDist z y₀) hz))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) ((summable_expCountSum hδ).sum_le_tsum _ fun k _ => by positivity)
  have e : ∑ z ∈ S with cellSupDist z y₀ = k, Real.exp (-(2 * δ) * cellSupDist z y₀) =
      ((S.filter fun z => cellSupDist z y₀ = k).card : ℝ) * Real.exp (-(2 * δ) * k) := by
    rw [Finset.sum_congr rfl (g := fun _ => Real.exp (-(2 * δ) * k)) (fun z hz => by
      rw [(Finset.mem_filter.1 hz).2]), Finset.sum_const, nsmul_eq_mul]
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have h1 := card_le_of_cellSupDist_le y₀ k (S.filter fun z => cellSupDist z y₀ = k)
    (fun z hz => (Finset.mem_filter.1 hz).2.le)
  exact_mod_cast h1
theorem rpow_neg_le_rpow_neg {x y e : ℝ} (hy : 0 < y) (hxy : y ≤ x) (he : 0 ≤ e) : x ^ (-e) ≤ y ^ (-e) :=
  Real.rpow_le_rpow_of_nonpos hy hxy (by linarith)
theorem sum_scaleRadius_rpow_neg_lt_le {l : ℕ} (hl : l ≤ F.top) (hL : 0 < F.blockSide) (X : Finset (F.Site l))
    (p : F.Site 0) {e : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / 4) (m : ℕ)
    (hm : 2 ^ m * F.blockSide ^ l ≤ F.blockSide ^ F.top) :
    ∑ x ∈ X.filter (fun x => scaleRadius F l p x < ((2 ^ m * F.blockSide ^ l : ℕ) : ℝ)), scaleRadius F l p x ^ (-e) ≤
      200 * 16 ^ m * (((2 ^ m * F.blockSide ^ l : ℕ) : ℝ)) ^ (-e) := by
  classical
  induction m with
  | zero =>
    have hemp : X.filter (fun x => scaleRadius F l p x < ((2 ^ 0 * F.blockSide ^ l : ℕ) : ℝ)) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun x _ => ?_
      have := pow_le_scaleRadius hl hL p x
      push_cast
      simpa using this
    rw [hemp, Finset.sum_empty]
    positivity
  | succ m ih =>
    have hm' : 2 ^ m * F.blockSide ^ l ≤ F.blockSide ^ F.top := by
      refine le_trans (Nat.mul_le_mul_right _ ?_) hm
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have ih' := ih hm'
    set A : ℝ := ((2 ^ m * F.blockSide ^ l : ℕ) : ℝ) with hA
    have hA0 : 0 < A := by
      rw [hA]
      push_cast
      positivity
    have hA2 : ((2 ^ (m + 1) * F.blockSide ^ l : ℕ) : ℝ) = 2 * A := by
      rw [hA]
      push_cast
      ring
    rw [hA2]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (X.filter fun x => scaleRadius F l p x < 2 * A) (fun x => scaleRadius F l p x < A)
      (fun x => scaleRadius F l p x ^ (-e))
    have h1 : (X.filter fun x => scaleRadius F l p x < 2 * A).filter (fun x => scaleRadius F l p x < A) =
        X.filter fun x => scaleRadius F l p x < A := by
      rw [Finset.filter_filter]
      refine Finset.filter_congr fun x _ => ?_
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨by linarith, h⟩
    rw [h1] at hsplit
    have hcnt := card_scaleRadius_lt hl hL X p (m + 1) hm
    rw [hA2] at hcnt
    have h2 : ∑ x ∈ (X.filter fun x => scaleRadius F l p x < 2 * A).filter
        (fun x => ¬ scaleRadius F l p x < A), scaleRadius F l p x ^ (-e) ≤
        ((X.filter fun x => scaleRadius F l p x < 2 * A).card : ℝ) * A ^ (-e) := by
      calc _ ≤ ∑ _x ∈ (X.filter fun x => scaleRadius F l p x < 2 * A).filter
            (fun x => ¬ scaleRadius F l p x < A), A ^ (-e) :=
            Finset.sum_le_sum fun x hx => rpow_neg_le_rpow_neg hA0 (not_lt.1 (Finset.mem_filter.1 hx).2) he0
        _ = (((X.filter fun x => scaleRadius F l p x < 2 * A).filter
            (fun x => ¬ scaleRadius F l p x < A)).card : ℝ) * A ^ (-e) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast Finset.card_filter_le _ _
    have hP : 0 ≤ A ^ (-e) := by positivity
    have h3 : A ^ (-e) / 2 ≤ (2 * A) ^ (-e) := by
      rw [Real.mul_rpow (by norm_num) hA0.le]
      have h4 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-e) := by
        have h5 : (2 : ℝ) ^ (-(1 : ℝ)) ≤ (2 : ℝ) ^ (-e) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        have h6 : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_one]
          norm_num
        rw [h6] at h5
        exact h5
      nlinarith
    have h16 : (0 : ℝ) < 16 ^ m := by positivity
    have hcnt' : ((X.filter fun x => scaleRadius F l p x < 2 * A).card : ℝ) * A ^ (-e) ≤
        81 * 16 ^ (m + 1) * A ^ (-e) := mul_le_mul_of_nonneg_right hcnt hP
    calc _ = _ := hsplit.symm
      _ ≤ 200 * 16 ^ m * A ^ (-e) + 81 * 16 ^ (m + 1) * A ^ (-e) := add_le_add ih' (h2.trans hcnt')
      _ ≤ 200 * 16 ^ (m + 1) * (A ^ (-e) / 2) := by
          rw [pow_succ]
          nlinarith [mul_nonneg h16.le hP]
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
theorem sum_scaleRadius_div_rpow_neg_le {l : ℕ} (hl : l ≤ F.top) (hL : 0 < F.blockSide) (X : Finset (F.Site l))
    (p : F.Site 0) {e : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / 4) :
    ∑ x ∈ X, (scaleRadius F l p x / (F.blockSide : ℝ) ^ F.top) ^ (-e) ≤
      400 * (((F.blockSide ^ (F.top - l) : ℕ) : ℝ)) ^ 4 + 2 * X.card := by
  classical
  set Q : ℕ := F.blockSide ^ (F.top - l) with hQ
  have hQ0 : Q ≠ 0 := by
    rw [hQ]
    positivity
  set m := Nat.log 2 Q with hmd
  have h2m : 2 ^ m ≤ Q := Nat.pow_log_le_self 2 hQ0
  have h2m' : Q < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) Q
  have hN : F.blockSide ^ F.top = Q * F.blockSide ^ l := by
    rw [hQ, ← pow_add]
    congr 1
    omega
  have hm : 2 ^ m * F.blockSide ^ l ≤ F.blockSide ^ F.top := by
    rw [hN]
    exact Nat.mul_le_mul_right _ h2m
  set Nr : ℝ := (F.blockSide : ℝ) ^ F.top with hNr
  have hNr0 : 0 < Nr := by positivity
  set A : ℝ := ((2 ^ m * F.blockSide ^ l : ℕ) : ℝ) with hA
  have hA0 : 0 < A := by
    rw [hA]
    push_cast
    positivity
  have hAN : Nr / 2 ≤ A := by
    have h1 : F.blockSide ^ F.top ≤ 2 * (2 ^ m * F.blockSide ^ l) := by
      rw [hN]
      calc Q * F.blockSide ^ l ≤ 2 ^ (m + 1) * F.blockSide ^ l := Nat.mul_le_mul_right _ h2m'.le
        _ = _ := by rw [pow_succ]; ring
    have h2 : Nr ≤ 2 * A := by
      rw [hNr, hA]
      exact_mod_cast h1
    linarith
  have hAe : A ^ (-e) ≤ 2 * Nr ^ (-e) := by
    have h1 : A ^ (-e) ≤ (Nr / 2) ^ (-e) := rpow_neg_le_rpow_neg (by positivity) hAN he0
    refine h1.trans ?_
    rw [Real.div_rpow hNr0.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num), neg_neg, mul_comm]
    have h2 : (2 : ℝ) ^ e ≤ 2 := by
      calc (2 : ℝ) ^ e ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one _
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have hsum : ∑ x ∈ X, scaleRadius F l p x ^ (-e) ≤ (400 * (Q : ℝ) ^ 4 + 2 * X.card) * Nr ^ (-e) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not X (fun x => scaleRadius F l p x < A)
      (fun x => scaleRadius F l p x ^ (-e))
    have h1 := sum_scaleRadius_rpow_neg_lt_le hl hL X p he0 he m hm
    have h16 : (16 : ℝ) ^ m ≤ (Q : ℝ) ^ 4 := by
      have : (2 : ℝ) ^ m ≤ Q := by exact_mod_cast h2m
      have h3 := pow_le_pow_left₀ (by positivity) this 4
      calc (16 : ℝ) ^ m = ((2 : ℝ) ^ m) ^ 4 := by
            rw [← pow_mul, mul_comm, pow_mul]
            norm_num
        _ ≤ _ := h3
    have h2 : ∑ x ∈ X.filter (fun x => ¬ scaleRadius F l p x < A), scaleRadius F l p x ^ (-e) ≤
        (X.card : ℝ) * (2 * Nr ^ (-e)) := by
      calc _ ≤ ∑ _x ∈ X.filter (fun x => ¬ scaleRadius F l p x < A), 2 * Nr ^ (-e) :=
            Finset.sum_le_sum fun x hx =>
              (rpow_neg_le_rpow_neg hA0 (not_lt.1 (Finset.mem_filter.1 hx).2) he0).trans hAe
        _ = ((X.filter (fun x => ¬ scaleRadius F l p x < A)).card : ℝ) * (2 * Nr ^ (-e)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast Finset.card_filter_le _ _
    have h3 : 200 * 16 ^ m * A ^ (-e) ≤ 200 * (Q : ℝ) ^ 4 * (2 * Nr ^ (-e)) := by
      have hAe0 : 0 ≤ A ^ (-e) := by positivity
      have h4 : 200 * (16 : ℝ) ^ m ≤ 200 * (Q : ℝ) ^ 4 := by linarith
      exact mul_le_mul h4 hAe hAe0 (by positivity)
    calc _ = _ := hsplit.symm
      _ ≤ 200 * (Q : ℝ) ^ 4 * (2 * Nr ^ (-e)) + (X.card : ℝ) * (2 * Nr ^ (-e)) :=
          add_le_add (h1.trans h3) h2
      _ = _ := by ring
  have hNe' : 0 < Nr ^ (-e) := by positivity
  have hterm : ∀ x ∈ X, (scaleRadius F l p x / Nr) ^ (-e) = scaleRadius F l p x ^ (-e) / Nr ^ (-e) :=
    fun x _ => Real.div_rpow (scaleRadius_pos hL l p x).le hNr0.le _
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, div_le_iff₀ hNe']
  exact hsum
theorem card_sitesOfCells_enclosingCell_le (hodd : Odd F.blockSide) (S : Finset F.Cell) (l : ℕ) (z : F.Cell) :
    (((sitesOfCells S l).filter fun x => enclosingCell x = z).card : ℝ) ≤
      (((F.blockSide ^ (F.top - l) : ℕ) : ℝ)) ^ 4 := by
  classical
  have hsub : ((sitesOfCells S l).filter fun x => enclosingCell x = z) ⊆ sitesOfCells {z} l := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact mem_sitesOfCells_of_enclosingCell_mem hodd h1 (by simp [h2])
  have h1 := (Finset.card_le_card hsub).trans (card_sitesOfCells_le hodd {z} l)
  simp only [Finset.card_singleton, one_mul] at h1
  exact_mod_cast h1
theorem sum_sitesOfCells_decayWeights_sq_le (hodd : Odd F.blockSide) {l : ℕ} (hl : l ≤ F.top) (S : Finset F.Cell)
    {δ θ : ℝ} (hδ : 0 < δ) (h0 : 0 ≤ θ) (h8 : θ ≤ 1 / 8) (p : F.Site 0) (y₀ : F.Cell) :
    ∑ x ∈ sitesOfCells S l, decayWeights F δ θ p y₀ l x ^ 2 ≤
      402 * expCountSum δ * (((F.blockSide ^ (F.top - l) : ℕ) : ℝ)) ^ 4 := by
  classical
  have hL := hodd.pos
  have hmaps : ∀ x ∈ sitesOfCells S l, enclosingCell x ∈ S := fun x hx => enclosingCell_mem hodd hx
  set Q : ℝ := (((F.blockSide ^ (F.top - l) : ℕ) : ℝ)) ^ 4 with hQ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hcell : ∀ z ∈ S, ∑ x ∈ sitesOfCells S l with enclosingCell x = z, decayWeights F δ θ p y₀ l x ^ 2 ≤
      Real.exp (-(2 * δ) * cellSupDist z y₀) * (402 * Q) := by
    intro z _
    have e : ∑ x ∈ sitesOfCells S l with enclosingCell x = z, decayWeights F δ θ p y₀ l x ^ 2 =
        Real.exp (-(2 * δ) * cellSupDist z y₀) * ∑ x ∈ sitesOfCells S l with enclosingCell x = z,
          (scaleRadius F l p x / (F.blockSide : ℝ) ^ F.top) ^ (-(2 * θ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hc := (Finset.mem_filter.1 hx).2
      have hr : 0 ≤ scaleRadius F l p x / (F.blockSide : ℝ) ^ F.top :=
        div_nonneg (scaleRadius_pos hL l p x).le (by positivity)
      simp only [decayWeights, hc, mul_pow]
      congr 1
      · rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      · rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
        congr 1
        push_cast
        ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine (sum_scaleRadius_div_rpow_neg_le hl hL _ p (by positivity) (by linarith)).trans ?_
    have := card_sitesOfCells_enclosingCell_le hodd S l z
    linarith
  refine (Finset.sum_le_sum hcell).trans ?_
  rw [← Finset.sum_mul]
  calc _ ≤ expCountSum δ * (402 * Q) :=
        mul_le_mul_of_nonneg_right (sum_exp_cellSupDist_le hδ S y₀) (by positivity)
    _ = _ := by ring
theorem sum_innerBonds_le {S : Finset F.Cell} {l : ℕ} {g : F.Site l → ℝ} (hg : ∀ x, 0 ≤ g x) :
    ∑ b ∈ innerBonds S l, g b.1 ≤ 4 * ∑ x ∈ sitesOfCells S l, g x := by
  classical
  have hsub : innerBonds S l ⊆ sitesOfCells S l ×ˢ Finset.univ := Finset.filter_subset _ _
  calc _ ≤ ∑ b ∈ sitesOfCells S l ×ˢ (Finset.univ : Finset (Fin 4)), g b.1 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hg _
    _ = _ := by
        rw [Finset.sum_product]
        simp [Finset.mul_sum]
theorem sum_innerPlaquettes_le {S : Finset F.Cell} {l : ℕ} {g : F.Site l → ℝ} (hg : ∀ x, 0 ≤ g x) :
    ∑ q ∈ innerPlaquettes S l, g q.1 ≤ 16 * ∑ x ∈ sitesOfCells S l, g x := by
  classical
  have hsub : innerPlaquettes S l ⊆ sitesOfCells S l ×ˢ (Finset.univ ×ˢ Finset.univ) := Finset.filter_subset _ _
  calc _ ≤ ∑ b ∈ sitesOfCells S l ×ˢ ((Finset.univ : Finset (Fin 4)) ×ˢ (Finset.univ : Finset (Fin 4))), g b.1 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hg _
    _ = _ := by
        rw [Finset.sum_product]
        simp [Finset.mul_sum]
theorem sum_innerBonds_scaleRadius_rpow_neg_le (hodd : Odd F.blockSide) {l : ℕ} (hl : l ≤ F.top)
    {D : Finset F.Cell} (hD : D.card ≤ 81) (p : F.Site 0) {e : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / 4) :
    ∑ b ∈ innerBonds D l, (scaleRadius F l p b.1 / (F.blockSide : ℝ) ^ F.top) ^ (-e) ≤
      2248 * (((F.blockSide ^ (F.top - l) : ℕ) : ℝ)) ^ 4 := by
  have hL := hodd.pos
  have h1 := sum_innerBonds_le (S := D) (l := l)
    (g := fun x => (scaleRadius F l p x / (F.blockSide : ℝ) ^ F.top) ^ (-e))
    (fun x => Real.rpow_nonneg (div_nonneg (scaleRadius_pos hL l p x).le (by positivity)) _)
  have h2 := sum_scaleRadius_div_rpow_neg_le hl hL (sitesOfCells D l) p he0 he
  have h3 : ((sitesOfCells D l).card : ℝ) ≤ 81 * (((F.blockSide ^ (F.top - l) : ℕ) : ℝ)) ^ 4 := by
    have h4 := card_sitesOfCells_le hodd D l
    have h5 : (D.card : ℝ) ≤ 81 := by exact_mod_cast hD
    have h6 : ((sitesOfCells D l).card : ℝ) ≤ (D.card : ℝ) * (((F.blockSide ^ (F.top - l) : ℕ) : ℝ)) ^ 4 := by
      exact_mod_cast h4
    exact h6.trans (mul_le_mul_of_nonneg_right h5 (by positivity))
  linarith
end YangMills.Construction.WeightedAverages.Sums
end

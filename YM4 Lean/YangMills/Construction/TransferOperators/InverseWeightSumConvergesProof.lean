import YangMills.Construction.TransferOperators.FactsOfTheSquareRootOfTheBondKernelProof
import YangMills.Construction.TransferOperators.InverseWeightSumConverges
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.SpinHarmonics.WeightDecaySum
theorem toReal_nonneg (t : HalfNatural) : 0 ≤ t.toReal := by apply _root_.YangMills.Construction.TransferOperators.SqrtLinkFacts.halfNatural_toReal_nonneg <;> assumption
theorem summable_one_add_toReal_rpow {a : ℝ} (ha : 1 < a) :
    Summable fun t : HalfNatural => (1 + t.toReal) ^ (-a) := by
  let e : ℕ ≃ HalfNatural := ⟨HalfNatural.mk, HalfNatural.doubled, fun _ => rfl, fun _ => rfl⟩
  rw [← e.summable_iff]
  have hnat : Summable fun k : ℕ => (((k + 1 : ℕ) : ℝ)) ^ (-a) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith))
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (hnat.mul_right (((1 : ℝ) / 2) ^ (-a)))
  · have : 0 ≤ (e k).toReal := toReal_nonneg _
    exact Real.rpow_nonneg (by linarith) _
  · have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hval : (e k).toReal = (k : ℝ) / 2 := rfl
    have hle : ((k + 1 : ℕ) : ℝ) * (1 / 2) ≤ 1 + (e k).toReal := by
      rw [hval]
      push_cast
      linarith
    have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) * (1 / 2) := by
      push_cast
      linarith
    have hcmp := Real.rpow_le_rpow_of_nonpos hpos hle (by linarith : -a ≤ 0)
    rw [Real.mul_rpow (Nat.cast_nonneg _) (by norm_num)] at hcmp
    exact hcmp
theorem summable_pi_prod_of_nonneg {ι H : Type} [Fintype ι] {g : H → ℝ} (hnn : ∀ t, 0 ≤ g t)
    (hg : Summable g) : Summable fun l : ι → H => ∏ i, g (l i) := by
  classical
  refine summable_of_sum_le (c := (∑' t, g t) ^ Fintype.card ι)
    (fun l => Finset.prod_nonneg fun i _ => hnn _) fun u => ?_
  let s : ι → Finset H := fun i => u.image fun l => l i
  calc ∑ l ∈ u, ∏ i, g (l i)
      ≤ ∑ l ∈ Fintype.piFinset s, ∏ i, g (l i) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun l hl => Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ hl)
          (fun l _ _ => Finset.prod_nonneg fun i _ => hnn _)
    _ = ∏ i, ∑ t ∈ s i, g t := (Finset.prod_univ_sum s fun _ t => g t).symm
    _ ≤ ∏ _i : ι, ∑' t, g t :=
        Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun t _ => hnn t)
          fun i _ => hg.sum_le_tsum _ fun t _ => hnn t
    _ = (∑' t, g t) ^ Fintype.card ι := by
        rw [Finset.prod_const, Finset.card_univ]
theorem weightDecayTerm_le_prod {ι : Type} [Fintype ι] [Nonempty ι] {q : ℕ} (l : ι → HalfNatural) :
    weightDecayTerm q l ≤
      ∏ i, 2 * (1 + (l i).toReal) ^ (1 - (q : ℝ) / Fintype.card ι) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set s : ℝ := (q : ℝ) / Fintype.card ι with hs
  set X : ℝ := 1 + ∑ i, (l i).toReal with hX
  have hsum0 : 0 ≤ ∑ i, (l i).toReal := Finset.sum_nonneg fun i _ => toReal_nonneg _
  have hXpos : 0 < X := by linarith
  have hs0 : 0 ≤ s := by positivity
  have hpow : X ^ q = ∏ _i : ι, X ^ s := by
    rw [Finset.prod_const, Finset.card_univ, ← Real.rpow_natCast (X ^ s), ← Real.rpow_mul hXpos.le,
      hs, div_mul_cancel₀ _ hn.ne', Real.rpow_natCast]
  have hterm : weightDecayTerm q l = ∏ i, (2 * (l i).toReal + 1) * (X ^ s)⁻¹ := by
    unfold weightDecayTerm weightSum
    rw [finprod_eq_prod_of_fintype, finsum_eq_sum_of_fintype, ← hX, hpow, Finset.prod_mul_distrib,
      Finset.prod_inv_distrib]
  rw [hterm]
  refine Finset.prod_le_prod (fun i _ => ?_) fun i _ => ?_
  · have := toReal_nonneg (l i)
    have : 0 < X ^ s := Real.rpow_pos_of_pos hXpos s
    positivity
  · have hv := toReal_nonneg (l i)
    have hi : (l i).toReal ≤ ∑ i, (l i).toReal :=
      Finset.single_le_sum (f := fun i => (l i).toReal) (fun i _ => toReal_nonneg _) (Finset.mem_univ i)
    have hy : 0 < 1 + (l i).toReal := by linarith
    have hyX : 1 + (l i).toReal ≤ X := by linarith
    have hys : 0 < (1 + (l i).toReal) ^ s := Real.rpow_pos_of_pos hy s
    have hinv : (X ^ s)⁻¹ ≤ ((1 + (l i).toReal) ^ s)⁻¹ :=
      inv_anti₀ hys (Real.rpow_le_rpow hy.le hyX hs0)
    have hright : 2 * (1 + (l i).toReal) ^ (1 - s) =
        2 * (1 + (l i).toReal) * ((1 + (l i).toReal) ^ s)⁻¹ := by
      rw [Real.rpow_sub hy, Real.rpow_one, div_eq_mul_inv, mul_assoc]
    rw [hright]
    exact mul_le_mul (by linarith) hinv (inv_nonneg.2 (Real.rpow_pos_of_pos hXpos s).le) (by linarith)
theorem summable_weightDecayTerm {ι : Type} [Finite ι] [Nonempty ι] {q : ℕ}
    (hq : 2 * Nat.card ι + 1 ≤ q) :
    Summable (weightDecayTerm q : (ι → HalfNatural) → ℝ) := by
  cases nonempty_fintype ι
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [Nat.card_eq_fintype_card] at hq
  have hqr : 2 * (Fintype.card ι : ℝ) + 1 ≤ q := by exact_mod_cast hq
  set a : ℝ := (q : ℝ) / Fintype.card ι - 1 with ha
  have ha1 : 1 < a := by
    have : 2 < (q : ℝ) / Fintype.card ι := by
      rw [lt_div_iff₀ hn]
      linarith
    linarith
  have hg : Summable fun t : HalfNatural => 2 * (1 + t.toReal) ^ (-a) :=
    (summable_one_add_toReal_rpow ha1).mul_left 2
  have hg0 : ∀ t : HalfNatural, 0 ≤ 2 * (1 + t.toReal) ^ (-a) := fun t => by
    have := toReal_nonneg t
    have := Real.rpow_nonneg (by linarith : 0 ≤ 1 + t.toReal) (-a)
    positivity
  refine Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_)
    (summable_pi_prod_of_nonneg (ι := ι) hg0 hg)
  · unfold weightDecayTerm
    rw [finprod_eq_prod_of_fintype]
    have hprod : 0 ≤ ∏ i, (2 * (l i).toReal + 1) := Finset.prod_nonneg fun i _ => by
      have := toReal_nonneg (l i)
      positivity
    have hw : 0 ≤ weightSum l := by
      unfold weightSum
      rw [finsum_eq_sum_of_fintype]
      exact Finset.sum_nonneg fun i _ => toReal_nonneg _
    positivity
  · have hb := weightDecayTerm_le_prod (q := q) l
    have he : 1 - (q : ℝ) / Fintype.card ι = -a := by
      rw [ha]
      ring
    rw [he] at hb
    exact hb
theorem weightDecayTerm_comp_equiv {ι κ : Type} [Finite ι] [Finite κ] (e : κ ≃ ι) (q : ℕ)
    (l : ι → HalfNatural) :
    weightDecayTerm q (fun i => l (e i)) = weightDecayTerm q l := by
  unfold weightDecayTerm weightSum
  rw [finprod_comp_equiv e (f := fun i => 2 * (l i).toReal + 1),
    finsum_comp_equiv e (f := fun i => (l i).toReal)]
theorem weightDecaySum_congr_equiv {ι κ : Type} [Finite ι] [Finite κ] (e : κ ≃ ι) (q : ℕ) :
    weightDecaySum κ q = weightDecaySum ι q := by
  let E : (ι → HalfNatural) ≃ (κ → HalfNatural) :=
    ⟨fun l i => l (e i), fun l i => l (e.symm i), fun l => by simp, fun l => by simp⟩
  unfold weightDecaySum
  rw [← E.tsum_eq (weightDecayTerm q)]
  exact tsum_congr fun l => weightDecayTerm_comp_equiv e q l
theorem holds : WeightDecaySum.Statement := by
  intro ι _ _
  exact ⟨fun q hq => summable_weightDecayTerm hq, fun κ _ hc q => weightDecaySum_congr_equiv
    ((Finite.equivFin κ).trans ((finCongr hc).trans (Finite.equivFin ι).symm)) q⟩
end YangMills.Construction.SpinHarmonics.WeightDecaySum
end

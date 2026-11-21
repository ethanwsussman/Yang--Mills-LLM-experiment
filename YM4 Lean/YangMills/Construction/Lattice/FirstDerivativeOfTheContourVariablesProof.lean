import YangMills.Construction.Averaging.AveragingMapRealAnalyticAtSmallRadiiProof
import YangMills.Construction.Averaging.MeanInTheComplexGroup
import YangMills.Construction.Lattice.FirstDerivativeOfTheContourVariables
import Mathlib
open Asymptotics Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Matrices
namespace PeriodicLattice.ContourHolonomyDerivative
theorem logSeries_sub_sub_one_le (hE : ComplexMatrix2.ExpLogEstimates) (A : ComplexMatrix2)
    (hA : ‖A - 1‖ ≤ 1 / 2) : ‖ComplexMatrix2.logSeries A - (A - 1)‖ ≤ 2 * ‖A - 1‖ ^ 2 := by
  have hlogOne : ComplexMatrix2.logSeries 1 = 0 := by
    have h := (hE.2.2.2.2.1 0 (by simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    simpa [NormedSpace.exp_zero] using h
  have h := (hE.2.2.2.2.2.2.2.2.1 ‖A - 1‖ A 1 (norm_nonneg _) (by linarith) le_rfl
    (by simp)).2.2.1
  rw [hlogOne, sub_zero] at h
  refine h.trans ?_
  have hratio : ‖A - 1‖ / (1 - ‖A - 1‖) ≤ 2 * ‖A - 1‖ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (A - 1)]
  calc ‖A - 1‖ / (1 - ‖A - 1‖) * ‖A - 1‖ ≤ 2 * ‖A - 1‖ * ‖A - 1‖ :=
        mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
    _ = 2 * ‖A - 1‖ ^ 2 := by ring
theorem complexLogMean_comp_equiv {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (V : κ → ComplexMatrix2) :
    complexLogMean (fun i => V (e i)) = complexLogMean V := by
  unfold complexLogMean
  congr 1
  funext W
  apply propext
  unfold ComplexMatrix2.IsLogMean
  constructor
  · rintro ⟨⟨hW, hnear, hzero⟩, i, hi⟩
    refine ⟨⟨hW, fun k => ?_, ?_⟩, e i, hi⟩
    · simpa using hnear (e.symm k)
    · rw [← e.sum_comp (fun k => ComplexMatrix2.logSeries (V k * W⁻¹))]
      exact hzero
  · rintro ⟨⟨hW, hnear, hzero⟩, k, hk⟩
    refine ⟨⟨hW, fun i => hnear (e i), ?_⟩, e.symm k, by simpa using hk⟩
    rw [e.sum_comp (fun k => ComplexMatrix2.logSeries (V k * W⁻¹))]
    exact hzero
theorem hasDerivAt_complexLogMean (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hE : ComplexMatrix2.ExpLogEstimates) {n : ℕ} (hn : 1 ≤ n) (V : Fin n → ℂ → ComplexMatrix2)
    (D : Fin n → ComplexMatrix2) (hdet : ∀ i t, V i t ∈ complexGaugeGroup) (h0 : ∀ i, V i 0 = 1)
    (hV : ∀ i, HasDerivAt (V i) (D i) 0) :
    HasDerivAt (fun t => complexLogMean fun i => V i t) (((n : ℂ)⁻¹) • ∑ i, D i) 0 := by
  have M := hM.2.2.2.1 n hn
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hnC : (n : ℂ) ≠ 0 := by
    have : n ≠ 0 := by omega
    exact_mod_cast this
  have hinv : ∀ j, HasDerivAt (fun t => (V j t)⁻¹) (-D j) 0 := by
    intro j
    have hu := hasFDerivAt_ringInverse (𝕜 := ℂ) (1 : (ComplexMatrix2)ˣ)
    have hv : V j 0 = ((1 : (ComplexMatrix2)ˣ) : ComplexMatrix2) := by simpa using h0 j
    rw [← hv] at hu
    have h := hu.comp_hasDerivAt (0 : ℂ) (hV j)
    have hfun : (Ring.inverse ∘ V j) = fun t => (V j t)⁻¹ := by
      funext t
      simp [Matrix.nonsing_inv_eq_ringInverse]
    rw [hfun] at h
    simpa using h
  set d : ℂ → ℝ := fun t => ComplexMatrix2.familyDiameter fun i => V i t with hd_def
  have hpair : ∀ p : Fin n × Fin n,
      (fun t => ‖V p.1 t * (V p.2 t)⁻¹ - 1‖) =O[𝓝 0] (fun t : ℂ => t) := by
    intro p
    have h := ((hV p.1).mul (hinv p.2)).isBigO_sub
    simpa [h0] using h.norm_left
  have hd : d =O[𝓝 0] (fun t : ℂ => t) := by
    have hsum := IsBigO.sum (s := Finset.univ) fun p _ => hpair p
    refine IsBigO.trans (IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)) hsum
    have hnn : 0 ≤ d t := Real.iSup_nonneg fun _ => norm_nonneg _
    have hle : d t ≤ ∑ p : Fin n × Fin n, ‖V p.1 t * (V p.2 t)⁻¹ - 1‖ :=
      ciSup_le fun p => Finset.single_le_sum
        (f := fun p : Fin n × Fin n => ‖V p.1 t * (V p.2 t)⁻¹ - 1‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ p)
    rw [Real.norm_of_nonneg hnn, one_mul, Finset.sum_apply]
    exact hle.trans (Real.le_norm_self _)
  have hd0 : Tendsto d (𝓝 0) (𝓝 0) := hd.trans_tendsto tendsto_id
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℂ), d t < 1 / 40 := hd0.eventually_lt_const (by norm_num)
  set W : ℂ → ComplexMatrix2 := fun t => complexLogMean fun i => V i t with hW_def
  set S : ℂ → ComplexMatrix2 := fun t => ((n : ℂ)⁻¹) • ∑ i, V i t with hS_def
  have hS : HasDerivAt S (((n : ℂ)⁻¹) • ∑ i, D i) 0 := by
    have h1 : HasDerivAt (fun t => ∑ i, V i t) (∑ i, D i) 0 := HasDerivAt.fun_sum fun i _ => hV i
    exact h1.const_smul ((n : ℂ)⁻¹)
  have hS0 : S 0 = 1 := by
    simp only [hS_def, h0, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hnC, one_smul]
  have hW0 : W 0 = 1 := by
    have h1 : (1 : ComplexMatrix2) ∈ complexGaugeGroup := by
      simp [complexGaugeGroup, ComplexMatrix2.unitDeterminant]
    simp only [hW_def, h0]
    exact M.constantFamily 1 h1
  have key : ∀ t, d t < 1 / 40 →
      ‖S t * (W t)⁻¹ - 1‖ ≤ 32 * d t ^ 2 ∧ (W t)⁻¹ * W t = 1 := by
    intro t ht
    have hnn : 0 ≤ d t := Real.iSup_nonneg fun _ => norm_nonneg _
    have hfam : (fun i => V i t) ∈ Averaging.smallComplexFamilies n :=
      ⟨fun i => hdet i t, by simpa [Averaging.centreOfMassDiameter] using ht⟩
    obtain ⟨W', hW', -⟩ := M.existsUnique _ hfam
    have hspec : Averaging.IsNearComplexLogMean (fun i => V i t) (W t) :=
      Classical.epsilon_spec (p := fun W => Averaging.IsNearComplexLogMean (fun i => V i t) W)
        ⟨W', hW'⟩
    obtain ⟨⟨hWg, -, hlog⟩, -⟩ := hspec
    have hWu : IsUnit (W t).det := by
      have : (W t).det = 1 := hWg
      rw [this]
      exact isUnit_one
    refine ⟨?_, Matrix.nonsing_inv_mul _ hWu⟩
    have hspr : ∀ i, ‖V i t * (W t)⁻¹ - 1‖ ≤ 4 * d t := fun i => M.spread _ hfam i
    have hterm : ∀ i, ‖(V i t * (W t)⁻¹ - 1) - ComplexMatrix2.logSeries (V i t * (W t)⁻¹)‖ ≤
        32 * d t ^ 2 := by
      intro i
      rw [norm_sub_rev]
      have hb := hspr i
      have h2 := logSeries_sub_sub_one_le hE (V i t * (W t)⁻¹) (by linarith)
      have h3 : ‖V i t * (W t)⁻¹ - 1‖ ^ 2 ≤ (4 * d t) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2
      nlinarith
    have hsum : ∑ i, (V i t * (W t)⁻¹ - 1) =
        ∑ i, ((V i t * (W t)⁻¹ - 1) - ComplexMatrix2.logSeries (V i t * (W t)⁻¹)) := by
      rw [Finset.sum_sub_distrib (s := Finset.univ)
        (f := fun i => V i t * (W t)⁻¹ - 1)
        (g := fun i => ComplexMatrix2.logSeries (V i t * (W t)⁻¹))]
      have hlog' : ∑ i, ComplexMatrix2.logSeries (V i t * (W t)⁻¹) = 0 := hlog
      rw [hlog', sub_zero]
    have hform : S t * (W t)⁻¹ - 1 = ((n : ℂ)⁻¹) • ∑ i, (V i t * (W t)⁻¹ - 1) := by
      have h1 : ∑ i : Fin n, (1 : ComplexMatrix2) = (n : ℂ) • (1 : ComplexMatrix2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [Nat.cast_smul_eq_nsmul]
      rw [Finset.sum_sub_distrib, h1, smul_sub, smul_smul, inv_mul_cancel₀ hnC, one_smul]
      simp only [hS_def, smul_mul_assoc, Finset.sum_mul]
    rw [hform, hsum, norm_smul]
    have hbound :
        ‖∑ i, ((V i t * (W t)⁻¹ - 1) - ComplexMatrix2.logSeries (V i t * (W t)⁻¹))‖ ≤
          (n : ℝ) * (32 * d t ^ 2) := by
      have := norm_sum_le_of_le (Finset.univ : Finset (Fin n)) (fun i _ => hterm i)
      simpa using this
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [norm_inv, Complex.norm_natCast]
    rw [inv_mul_le_iff₀ hnR]
    exact hbound
  have hSb : ∀ᶠ t in 𝓝 (0 : ℂ), ‖S t‖ < ‖S 0‖ + 1 :=
    hS.continuousAt.norm.eventually_lt_const (lt_add_one _)
  set B : ℝ := ‖S 0‖ + 1 with hB_def
  have hdiff : ∀ᶠ t in 𝓝 (0 : ℂ), ‖W t - S t‖ ≤ 64 * B * (d t * d t) := by
    filter_upwards [hsmall, hSb] with t ht hb
    obtain ⟨hQ, hWW⟩ := key t ht
    have hnn : 0 ≤ d t := Real.iSup_nonneg fun _ => norm_nonneg _
    set Q : ComplexMatrix2 := S t * (W t)⁻¹ - 1 with hQ_def
    have hSW : S t = W t + Q * W t := by
      rw [hQ_def, sub_mul, mul_assoc, hWW, mul_one, one_mul]
      abel
    have hQs : ‖Q‖ ≤ 1 / 2 := by nlinarith
    have hWS : W t - S t = -(Q * W t) := by rw [hSW]; abel
    have hnW : ‖W t - S t‖ ≤ ‖Q‖ * ‖W t‖ := by
      rw [hWS, norm_neg]
      exact norm_mul_le _ _
    have hWn : ‖W t‖ ≤ 2 * B := by
      have h1 : ‖W t‖ ≤ ‖S t‖ + ‖W t - S t‖ := by
        have := norm_add_le (S t) (W t - S t)
        simpa using this
      have h2 : ‖Q‖ * ‖W t‖ ≤ 1 / 2 * ‖W t‖ :=
        mul_le_mul_of_nonneg_right hQs (norm_nonneg _)
      linarith
    calc ‖W t - S t‖ ≤ ‖Q‖ * ‖W t‖ := hnW
      _ ≤ (32 * d t ^ 2) * (2 * B) :=
        mul_le_mul hQ hWn (norm_nonneg _) (by positivity)
      _ = 64 * B * (d t * d t) := by ring
  have hlittle : (fun t => W t - S t) =o[𝓝 0] (fun t : ℂ => t) := by
    have h1 : (fun t => d t * d t) =o[𝓝 0] (fun t : ℂ => t * 1) :=
      hd.mul_isLittleO ((isLittleO_one_iff ℂ).2 hd0)
    have h2 : (fun t => W t - S t) =O[𝓝 0] (fun t => d t * d t) :=
      IsBigO.of_bound (64 * B) (by
        filter_upwards [hdiff] with t ht
        have hnn : 0 ≤ d t * d t :=
          mul_self_nonneg _
        rwa [Real.norm_of_nonneg hnn])
    simpa using h2.trans_isLittleO h1
  rw [hasDerivAt_iff_isLittleO]
  have hSo := hasDerivAt_iff_isLittleO.1 hS
  have hsum := hSo.add (hlittle.trans_isBigO
    (by simpa using isBigO_refl (fun t : ℂ => t) (𝓝 0) :
      (fun t : ℂ => t) =O[𝓝 0] fun t : ℂ => t - 0))
  refine hsum.congr_left fun t => ?_
  rw [hW0, ← hS0]
  abel
section Paths
variable {L m : ℕ} {j : ℤ}
theorem pathHolonomy_at_zero {A : Bond L m j → ComplexMatrix2} {C : ℂ → Bond L m j → ComplexMatrix2}
    (hC : ∀ t b, C t b = ComplexMatrix2.matExp (t • (Complex.I • A b))) (Γ : List (Bond L m j)) :
    pathHolonomy (C 0) Γ = 1 := by
  induction Γ with
  | nil => rfl
  | cons b Γ ih =>
    have h : pathHolonomy (C 0) (b :: Γ) = C 0 b * pathHolonomy (C 0) Γ := by simp [pathHolonomy]
    rw [h, ih, hC]
    simp [NormedSpace.exp_zero]
theorem hasDerivAt_pathHolonomy {A : Bond L m j → ComplexMatrix2}
    {C : ℂ → Bond L m j → ComplexMatrix2}
    (hC : ∀ t b, C t b = ComplexMatrix2.matExp (t • (Complex.I • A b))) (Γ : List (Bond L m j)) :
    HasDerivAt (fun t => pathHolonomy (C t) Γ) (Complex.I • bondFormSumAlong A Γ) 0 := by
  induction Γ with
  | nil => simpa [pathHolonomy, bondFormSumAlong] using hasDerivAt_const (0 : ℂ) (1 : ComplexMatrix2)
  | cons b Γ ih =>
    have hb : HasDerivAt (fun t => C t b) (Complex.I • A b) 0 := by
      have h := hasDerivAt_exp_smul_const (𝕂 := ℂ) (Complex.I • A b) (0 : ℂ)
      have hf : (fun t => C t b) = fun u : ℂ => NormedSpace.exp (u • Complex.I • A b) := by
        funext t
        exact hC t b
      rw [hf]
      simpa [NormedSpace.exp_zero] using h
    have h := hb.mul ih
    have h1 : C 0 b = 1 := by
      rw [hC]
      simp [NormedSpace.exp_zero]
    have hfun : (fun t => pathHolonomy (C t) (b :: Γ)) =
        (fun t => C t b) * fun t => pathHolonomy (C t) Γ := by
      funext t
      simp [pathHolonomy]
    have hderiv : Complex.I • bondFormSumAlong A (b :: Γ) =
        Complex.I • A b * pathHolonomy (C 0) Γ + C 0 b * Complex.I • bondFormSumAlong A Γ := by
      rw [pathHolonomy_at_zero hC, h1]
      simp [bondFormSumAlong, smul_add]
    rw [hfun, hderiv]
    exact h
theorem pathHolonomy_mem {U : Bond L m j → ComplexMatrix2} (hU : ∀ b, U b ∈ complexGaugeGroup)
    (Γ : List (Bond L m j)) : pathHolonomy U Γ ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.pathHolonomy_mem_complexGaugeGroup <;> assumption
end Paths
section Bonds
variable {L m K n : ℕ}
theorem eval_smul {P : SymmetricBondSet L m K n} (t : ℂ) (a : LieBondField P)
    (b : BondAtLevel L m K n) : ((t • a).eval b : ComplexMatrix2) = t • (a.eval b : ComplexMatrix2) := by
  simp only [LieBondField.eval]
  split_ifs <;> simp
theorem eval_of_not_positivelyOriented {P : SymmetricBondSet L m K n} (a : LieBondField P)
    {b : BondAtLevel L m K n} (hb : ¬ b.IsPositivelyOriented) :
    (a.eval b : ComplexMatrix2) = -(a.eval b.opposite : ComplexMatrix2) := by
  have hr : b.opposite.opposite = b := rfl
  have h1 : ¬ (b ∈ P.bonds ∧ b.IsPositivelyOriented) := fun h => hb h.2
  have h2 : ¬ (b.opposite.opposite ∈ P.bonds ∧ b.opposite.opposite.IsPositivelyOriented) := by
    rw [hr]
    exact h1
  simp only [LieBondField.eval]
  rw [dif_neg h1]
  by_cases h3 : b.opposite ∈ P.bonds ∧ b.opposite.IsPositivelyOriented
  · rw [dif_pos h3, dif_pos h3]
    simp
  · rw [dif_neg h3, dif_neg h3, dif_neg h2]
    simp
theorem expBondField_smul (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (t : ℂ) (b : BondAtLevel L m K n) :
    expBondField c (t • a) b =
      ComplexMatrix2.matExp (t • (Complex.I • (a.eval b : ComplexMatrix2))) := by
  simp only [expBondField, twistedConfig, expTwist, trivialGaugeField, mul_one]
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos hb, eval_smul, smul_comm]
  · rw [if_neg hb, eval_smul, ← Matrix.exp_neg, eval_of_not_positivelyOriented a hb]
    congr 1
    rw [smul_neg, smul_neg, smul_comm]
theorem expBondField_mem (hE : ComplexMatrix2.ExpLogEstimates)
    (c : BondAtLevel L m K (n + 1)) (a : LieBondField (doubleBlockSymmetricSet c)) (t : ℂ)
    (b : BondAtLevel L m K n) : expBondField c (t • a) b ∈ complexGaugeGroup := by
  rw [expBondField_smul]
  have h := hE.2.2.2.2.2.1 (t • (Complex.I • (a.eval b : ComplexMatrix2)))
  have htr : ComplexMatrix2.fullTrace (a.eval b : ComplexMatrix2) = 0 := (a.eval b).2
  change (ComplexMatrix2.matExp (t • (Complex.I • (a.eval b : ComplexMatrix2)))).det = 1
  rw [h]
  simp only [ComplexMatrix2.fullTrace] at htr ⊢
  rw [Matrix.trace_smul, Matrix.trace_smul, htr]
  simp
end Bonds
theorem hasDerivAt_centredContour (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hE : ComplexMatrix2.ExpLogEstimates) {L m K n : ℕ} {j : ℤ}
    (c : BondAtLevel L m K (n + 1)) (a : LieBondField (doubleBlockSymmetricSet c))
    (y : Site L m j) (x : SiteAtLevel L m K n) :
    HasDerivAt (fun t : ℂ => complexMeanContourHolonomy (expBondField c (t • a)) y x)
      (Complex.I • contourFormAverage (fun b => (a.eval b : ComplexMatrix2)) y x) 0 := by
  have : Nonempty (AxisOrdering y x) := ⟨(offsetAxes y x).equivFin.symm⟩
  set e := Fintype.equivFin (AxisOrdering y x) with he
  have hcard : 1 ≤ Fintype.card (AxisOrdering y x) := Fintype.card_pos
  have hC := expBondField_smul c a
  have h := hasDerivAt_complexLogMean hM hE hcard
    (fun k t => pathHolonomy (expBondField c (t • a)) (orderedContour y x (e.symm k)))
    (fun k => Complex.I • bondFormSumAlong (fun b => (a.eval b : ComplexMatrix2))
      (orderedContour y x (e.symm k)))
    (fun k t => pathHolonomy_mem (expBondField_mem hE c a t) _)
    (fun k => pathHolonomy_at_zero (C := fun t => expBondField c (t • a)) hC _)
    (fun k => hasDerivAt_pathHolonomy (C := fun t => expBondField c (t • a)) hC _)
  have hfun : (fun t : ℂ => complexMeanContourHolonomy (expBondField c (t • a)) y x) =
      fun t => complexLogMean fun k =>
        pathHolonomy (expBondField c (t • a)) (orderedContour y x (e.symm k)) := by
    funext t
    exact (complexLogMean_comp_equiv e.symm
      (contourHolonomies (expBondField c (t • a)) y x)).symm
  have hderiv : Complex.I • contourFormAverage (fun b => (a.eval b : ComplexMatrix2)) y x =
      ((Fintype.card (AxisOrdering y x) : ℂ)⁻¹) • ∑ k, Complex.I • bondFormSumAlong
        (fun b => (a.eval b : ComplexMatrix2)) (orderedContour y x (e.symm k)) := by
    simp only [contourFormAverage]
    rw [← e.symm.sum_comp (fun σ => bondFormSumAlong (fun b => (a.eval b : ComplexMatrix2))
        (orderedContour y x σ)),
      ← Finset.smul_sum, smul_comm]
    push_cast
    rfl
  rw [hfun, hderiv]
  exact h
theorem statement_holds (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hE : ComplexMatrix2.ExpLogEstimates) :
    ContourHolonomyDerivative.Statement := by
  intro L _ m K n _ _ s c _ a y _ x _
  cases s with
  | centred => exact hasDerivAt_centredContour hM hE c a y x
  | cornered =>
    exact hasDerivAt_pathHolonomy (C := fun t => expBondField c (t • a))
      (expBondField_smul c a) _
end PeriodicLattice.ContourHolonomyDerivative
end YangMills.Construction

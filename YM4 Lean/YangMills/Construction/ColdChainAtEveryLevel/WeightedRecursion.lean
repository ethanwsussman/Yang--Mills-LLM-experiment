import YangMills.Construction.ColdChainAtEveryLevel.CurlOfACarriedFormProof
import YangMills.Construction.ColdChainAtEveryLevel.WeightChains
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LevelRecursion
open BlockAverages BlockLines WeightedAverages WeightedAverages.Chains
variable {F : BlockFrame}
section FinsetNorms
variable {ι : Type}
def finsetLpNorm (P : ℕ) (s : Finset ι) (f : ι → ℝ) : ℝ := (∑ i ∈ s, |f i| ^ P) ^ (1 / (P : ℝ))
theorem finsetLpNorm_nonneg (P : ℕ) (s : Finset ι) (f : ι → ℝ) : 0 ≤ finsetLpNorm P s f :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => by positivity) _
theorem finsetLpNorm_add_le {P : ℕ} (hP : 1 ≤ P) (s : Finset ι) (f g : ι → ℝ) :
    finsetLpNorm P s (fun i => f i + g i) ≤ finsetLpNorm P s f + finsetLpNorm P s g := by
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have h := Real.Lp_add_le s f g hPR
  simpa only [finsetLpNorm, Real.rpow_natCast] using h
theorem finsetLpNorm_mono {P : ℕ} (hP : 1 ≤ P) (s : Finset ι) {f g : ι → ℝ} (h : ∀ i ∈ s, |f i| ≤ |g i|) :
    finsetLpNorm P s f ≤ finsetLpNorm P s g := by
  refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity) ?_ (by positivity)
  exact Finset.sum_le_sum fun i hi => pow_le_pow_left₀ (abs_nonneg _) (h i hi) P
theorem finsetLpNorm_zero {P : ℕ} (hP : 1 ≤ P) (s : Finset ι) : finsetLpNorm P s (fun _ => 0) = 0 := by
  have hPR : (P : ℝ) ≠ 0 := by
    have : (0 : ℝ) < P := by exact_mod_cast hP
    exact this.ne'
  have h0 : P ≠ 0 := by omega
  simp [finsetLpNorm, h0, hPR]
theorem finsetLpNorm_sum_le {P : ℕ} (hP : 1 ≤ P) {κ : Type} (T : Finset κ) (s : Finset ι) (f : κ → ι → ℝ) :
    finsetLpNorm P s (fun i => ∑ t ∈ T, f t i) ≤ ∑ t ∈ T, finsetLpNorm P s (f t) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [finsetLpNorm_zero hP]
  | insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    exact (finsetLpNorm_add_le hP s _ _).trans (by linarith)
theorem finsetLpNorm_le_of_sum_pow_le {P : ℕ} (hP : 1 ≤ P) {κ : Type} (s : Finset ι) (s' : Finset κ) (f : ι → ℝ) (g : κ → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (h : ∑ i ∈ s, |f i| ^ P ≤ C ^ P * ∑ i ∈ s', |g i| ^ P) : finsetLpNorm P s f ≤ C * finsetLpNorm P s' g := by
  have h1 := Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity) h (by positivity : 0 ≤ 1 / (P : ℝ))
  rw [Real.mul_rpow (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)] at h1
  have e : (C ^ P) ^ (1 / (P : ℝ)) = C := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hC]
    field_simp
    simp
  rwa [e] at h1
theorem finsetLpNorm_four_le_two (s : Finset ι) (f : ι → ℝ) : finsetLpNorm 4 s f ≤ finsetLpNorm 2 s f := by
  set S := ∑ i ∈ s, |f i| ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have h1 : ∑ i ∈ s, |f i| ^ 4 ≤ S ^ 2 := by
    have h2 : ∀ i ∈ s, |f i| ^ 4 ≤ |f i| ^ 2 * S := fun i hi => by
      have : |f i| ^ 2 ≤ S := Finset.single_le_sum (f := fun i => |f i| ^ 2) (fun _ _ => by positivity) hi
      calc |f i| ^ 4 = |f i| ^ 2 * |f i| ^ 2 := by ring
        _ ≤ |f i| ^ 2 * S := mul_le_mul_of_nonneg_left this (by positivity)
    refine (Finset.sum_le_sum h2).trans (le_of_eq ?_)
    rw [← Finset.sum_mul, ← hS]
    ring
  have h2 := Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / ((4 : ℕ) : ℝ))
  have e : (S ^ 2) ^ (1 / ((4 : ℕ) : ℝ)) = S ^ (1 / ((2 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS0]
    norm_num
  rw [e] at h2
  exact h2
theorem finsetLpNorm_two_eq_sqrt (s : Finset ι) (f : ι → ℝ) : finsetLpNorm 2 s f = Real.sqrt (∑ i ∈ s, f i ^ 2) := by
  rw [finsetLpNorm, Real.sqrt_eq_rpow]
  simp only [sq_abs]
  norm_num
theorem finsetLpNorm_four_eq_sqrt_sqrt (s : Finset ι) (f : ι → ℝ) : finsetLpNorm 4 s f = Real.sqrt (Real.sqrt (∑ i ∈ s, f i ^ 4)) := by
  have h0 : 0 ≤ ∑ i ∈ s, f i ^ 4 := Finset.sum_nonneg fun i _ => by positivity
  have e : ∀ i, |f i| ^ 4 = f i ^ 4 := fun i => by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, sq_abs]
  simp only [finsetLpNorm, e]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul h0]
  norm_num
end FinsetNorms
def sourceTransport (s : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ) (i : ℕ) : (m : ℕ) → F.Site m → Fin 4 → ℝ
  | 0 => fun _ _ => 0
  | m + 1 => fun y d => lineBlockAverage (sourceTransport s i m) (y, d) + if m = i then s m y d else 0
def baseTransport (a : F.Site 0 → Fin 4 → ℝ) : (m : ℕ) → F.Site m → Fin 4 → ℝ
  | 0 => a
  | m + 1 => fun y d => lineBlockAverage (baseTransport a m) (y, d)
theorem lineBlockAverage_nonneg {l : ℕ} {f : F.Site l → Fin 4 → ℝ} (hf : ∀ x d, 0 ≤ f x d)
    (c : F.Site (l + 1) × Fin 4) : 0 ≤ lineBlockAverage f c := by
  unfold lineBlockAverage
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hf _ _)
theorem sourceTransport_nonneg {s : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ} (hs : ∀ m y d, 0 ≤ s m y d) (i m : ℕ) :
    ∀ x d, 0 ≤ sourceTransport s i m x d := by
  induction m with
  | zero => exact fun _ _ => le_rfl
  | succ m ih =>
    intro y d
    simp only [sourceTransport]
    refine add_nonneg (lineBlockAverage_nonneg ih _) ?_
    split_ifs
    · exact hs _ _ _
    · exact le_rfl
theorem baseTransport_nonneg {a : F.Site 0 → Fin 4 → ℝ} (ha : ∀ x d, 0 ≤ a x d) (m : ℕ) :
    ∀ x d, 0 ≤ baseTransport a m x d := by
  induction m with
  | zero => exact ha
  | succ m ih => exact fun y d => lineBlockAverage_nonneg ih _
theorem sourceTransport_of_le (s : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ) (i m : ℕ) (h : m ≤ i) :
    sourceTransport s i m = fun _ _ => 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext y d
    have h1 := ih (by omega)
    have h2 : m ≠ i := by omega
    simp only [sourceTransport, h1, if_neg h2, add_zero, lineBlockAverage]
    simp
theorem lineBlockAverage_add {l : ℕ} (f g : F.Site l → Fin 4 → ℝ) (c : F.Site (l + 1) × Fin 4) :
    lineBlockAverage (fun x d => f x d + g x d) c = lineBlockAverage f c + lineBlockAverage g c := by
  simp only [lineBlockAverage, Finset.sum_add_distrib, mul_add]
theorem lineBlockAverage_sum {κ : Type} {l : ℕ} (T : Finset κ) (f : κ → F.Site l → Fin 4 → ℝ)
    (c : F.Site (l + 1) × Fin 4) :
    lineBlockAverage (fun x d => ∑ t ∈ T, f t x d) c = ∑ t ∈ T, lineBlockAverage (f t) c := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [lineBlockAverage]
  | insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    rw [lineBlockAverage_add, ih]
theorem lineBlockAverage_mono_on {D : Finset F.Cell} {l : ℕ} (hl : l < F.top) (hodd : Odd F.blockSide)
    {f g : F.Site l → Fin 4 → ℝ} (h : ∀ b ∈ innerBonds D l, f b.1 b.2 ≤ g b.1 b.2) {c : F.Site (l + 1) × Fin 4}
    (hc : c ∈ innerBonds D (l + 1)) : lineBlockAverage f c ≤ lineBlockAverage g c := by
  unfold lineBlockAverage
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun r hr => ?_
  exact h _ (lineBond_mem_innerBonds hl hodd c hc k hk r (Finset.mem_range.1 hr))
theorem le_baseTransport_add_sum {D : Finset F.Cell} (hodd : Odd F.blockSide) (a : (m : ℕ) → F.Site m → Fin 4 → ℝ)
    (s : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ)
    (hrec : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1), a (m + 1) c.1 c.2 ≤ lineBlockAverage (a m) c + s m c.1 c.2)
    (m : ℕ) (hm : m < F.top) : ∀ b ∈ innerBonds D m, a m b.1 b.2 ≤
      baseTransport (a 0) m b.1 b.2 + ∑ i ∈ Finset.range m, sourceTransport s i m b.1 b.2 := by
  induction m with
  | zero => exact fun b _ => by simp [baseTransport]
  | succ m ih =>
    intro c hc
    have h1 := hrec m hm c hc
    have h2 := lineBlockAverage_mono_on (D := D) (f := a m)
      (g := fun x d => baseTransport (a 0) m x d + ∑ i ∈ Finset.range m, sourceTransport s i m x d)
      (by omega) hodd (ih (by omega)) hc
    rw [lineBlockAverage_add, lineBlockAverage_sum] at h2
    have e0 : sourceTransport s m (m + 1) c.1 c.2 = s m c.1 c.2 := by
      simp only [sourceTransport, if_true, sourceTransport_of_le s m m le_rfl]
      simp [lineBlockAverage]
    have e1 : ∀ i ∈ Finset.range m, sourceTransport s i (m + 1) c.1 c.2 = lineBlockAverage (sourceTransport s i m) c := by
      intro i hi
      have hne : m ≠ i := by
        have := Finset.mem_range.1 hi
        omega
      simp only [sourceTransport, if_neg hne, add_zero]
    rw [Finset.sum_range_succ, e0, Finset.sum_congr rfl e1]
    have e2 : baseTransport (a 0) (m + 1) c.1 c.2 = lineBlockAverage (baseTransport (a 0) m) c := rfl
    rw [e2]
    linarith
section Scales
def scaleWeight (p : F.Site 0) (θ : ℝ) (m : ℕ) (x : F.Site m) : ℝ := scaleRadius F m p x ^ (-θ)
theorem scaleWeight_pos (hodd : Odd F.blockSide) (p : F.Site 0) (θ : ℝ) (m : ℕ) (x : F.Site m) :
    0 < scaleWeight p θ m x :=
  Real.rpow_pos_of_pos (scaleRadius_pos hodd.pos _ _ _) _
def weightedScaleNorm (D : Finset F.Cell) (p : F.Site 0) (θ : ℝ) (P m : ℕ) (f : F.Site m → Fin 4 → ℝ) : ℝ :=
  finsetLpNorm P (innerBonds D m) fun b => scaleWeight p θ m b.1 * f b.1 b.2
theorem sum_inv_pow_le_two {L : ℝ} (hL : 2 ≤ L) (m : ℕ) :
    ∑ i ∈ Finset.range m, (1 / L) ^ (m - 1 - i) ≤ 2 := by
  have hr : ∑ i ∈ Finset.range m, (1 / L) ^ (m - 1 - i) = ∑ k ∈ Finset.range m, (1 / L) ^ k := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.1 hk
    congr 1
    omega
  rw [hr]
  have h1 : 1 / L ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hL
  have h0 : 0 ≤ 1 / L := by positivity
  have h2 : ∀ k ∈ Finset.range m, (1 / L) ^ k ≤ (1 / 2 : ℝ) ^ k := fun k _ => pow_le_pow_left₀ h0 h1 k
  refine (Finset.sum_le_sum h2).trans ?_
  have := sum_geometric_two_le m
  exact this
theorem sourceTransport_norm_le (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide) (D : Finset F.Cell) (p : F.Site 0) {θ : ℝ}
    (hθ : |θ| ≤ 1 / 8) (s : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ) (hs : ∀ m y d, 0 ≤ s m y d) (i m : ℕ)
    (him : i < m) (hm : m ≤ F.top) :
    weightedScaleNorm D p θ 2 m (sourceTransport s i m) ≤
      142 * (1 / (F.blockSide : ℝ)) ^ (m - 1 - i) * weightedScaleNorm D p θ 2 (i + 1) (s i) := by
  have h := sum_weighted_pow_le hodd h2 D p hθ 2 (Or.inl rfl) (i + 1) m him hm (sourceTransport s i)
    (sourceTransport_nonneg hs i) (fun m' hm' _ c _ => by
      have hne : m' ≠ i := by omega
      simp only [sourceTransport, if_neg hne, add_zero]
      exact le_rfl)
  have e0 : sourceTransport s i (i + 1) = s i := by
    funext y d
    simp only [sourceTransport, if_true, sourceTransport_of_le s i i le_rfl]
    simp [lineBlockAverage]
  rw [e0] at h
  refine finsetLpNorm_le_of_sum_pow_le (by norm_num) _ _ _ _ (by positivity) ?_
  simp only [sq_abs]
  refine h.trans ?_
  have e1 : m - (i + 1) = m - 1 - i := by omega
  rw [e1]
  have e2 : ((F.blockSide : ℝ) ^ 2 / (F.blockSide : ℝ) ^ 4) ^ (m - 1 - i) = ((1 / (F.blockSide : ℝ)) ^ (m - 1 - i)) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    congr 1
    field_simp
  rw [e2, mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => by positivity)
  refine mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
theorem baseTransport_norm_le (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide) (D : Finset F.Cell) (p : F.Site 0) {θ : ℝ}
    (hθ : |θ| ≤ 1 / 8) (a : F.Site 0 → Fin 4 → ℝ) (ha : ∀ x d, 0 ≤ a x d) (m : ℕ) (hm : m ≤ F.top) :
    weightedScaleNorm D p θ 4 m (baseTransport a m) ≤ 20000 * weightedScaleNorm D p θ 4 0 a ∧
      weightedScaleNorm D p θ 2 m (baseTransport a m) ≤ 142 * weightedScaleNorm D p θ 2 0 a := by
  have hL : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  constructor
  · have h := sum_weighted_pow_le hodd h2 D p hθ 4 (Or.inr rfl) 0 m (Nat.zero_le m) hm (baseTransport a)
      (baseTransport_nonneg ha) (fun m' _ _ c _ => le_rfl)
    refine finsetLpNorm_le_of_sum_pow_le (by norm_num) _ _ _ _ (by positivity) ?_
    have e : ∀ x : ℝ, |x| ^ 4 = x ^ 4 := fun x => by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, sq_abs]
    simp only [e]
    refine h.trans ?_
    have e2 : (F.blockSide : ℝ) ^ 4 / (F.blockSide : ℝ) ^ 4 = 1 := div_self (by positivity)
    rw [e2, one_pow, mul_one]
    refine mul_le_mul_of_nonneg_right (by norm_num) (Finset.sum_nonneg fun _ _ => by positivity)
  · have h := sum_weighted_pow_le hodd h2 D p hθ 2 (Or.inl rfl) 0 m (Nat.zero_le m) hm (baseTransport a)
      (baseTransport_nonneg ha) (fun m' _ _ c _ => le_rfl)
    refine finsetLpNorm_le_of_sum_pow_le (by norm_num) _ _ _ _ (by positivity) ?_
    simp only [sq_abs]
    refine h.trans ?_
    have e2 : ((F.blockSide : ℝ) ^ 2 / (F.blockSide : ℝ) ^ 4) ^ (m - 0) ≤ 1 := by
      refine pow_le_one₀ (by positivity) ?_
      rw [div_le_one (by positivity)]
      exact pow_le_pow_right₀ hL (by norm_num)
    have h0 : 0 ≤ ∑ b ∈ innerBonds D 0, (scaleRadius F 0 p b.1 ^ (-θ) * baseTransport a 0 b.1 b.2) ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    have h3 : (20000 : ℝ) ^ (2 - 1) * ((F.blockSide : ℝ) ^ 2 / (F.blockSide : ℝ) ^ 4) ^ (m - 0) ≤ 142 ^ 2 := by
      have : (0 : ℝ) ≤ ((F.blockSide : ℝ) ^ 2 / (F.blockSide : ℝ) ^ 4) ^ (m - 0) := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_right h3 h0
theorem weightedScaleNorm_le_of_recursion (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide) (D : Finset F.Cell) (p : F.Site 0) {θ : ℝ}
    (hθ : |θ| ≤ 1 / 8) (a : (m : ℕ) → F.Site m → Fin 4 → ℝ) (s : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ)
    (ha : ∀ m x d, 0 ≤ a m x d) (hs : ∀ m y d, 0 ≤ s m y d)
    (hrec : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1), a (m + 1) c.1 c.2 ≤ lineBlockAverage (a m) c + s m c.1 c.2)
    {B : ℝ} (m : ℕ) (hB : ∀ i, i + 1 ≤ m → weightedScaleNorm D p θ 2 (i + 1) (s i) ≤ B) (hB0 : 0 ≤ B) (hm : m < F.top) :
    weightedScaleNorm D p θ 4 m (a m) ≤ 20000 * weightedScaleNorm D p θ 4 0 (a 0) + 284 * B ∧
      weightedScaleNorm D p θ 2 m (a m) ≤ 142 * weightedScaleNorm D p θ 2 0 (a 0) + 284 * B := by
  have hL2 : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast h2
  have hle := le_baseTransport_add_sum (D := D) hodd a s hrec m hm
  have hw := scaleWeight_pos hodd p θ m
  have hpt : ∀ b ∈ innerBonds D m, |scaleWeight p θ m b.1 * a m b.1 b.2| ≤
      |scaleWeight p θ m b.1 * baseTransport (a 0) m b.1 b.2 +
        ∑ i ∈ Finset.range m, scaleWeight p θ m b.1 * sourceTransport s i m b.1 b.2| := by
    intro b hb
    have h1 := hle b hb
    have h3 := ha m b.1 b.2
    have h4 := baseTransport_nonneg (ha 0) m b.1 b.2
    have h5 : 0 ≤ ∑ i ∈ Finset.range m, sourceTransport s i m b.1 b.2 :=
      Finset.sum_nonneg fun i _ => sourceTransport_nonneg hs i m _ _
    have hwb := hw b.1
    rw [← Finset.mul_sum, ← mul_add, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left h1 hwb.le
  have hsumB : ∀ i ∈ Finset.range m, weightedScaleNorm D p θ 2 m (sourceTransport s i m) ≤
      142 * (1 / (F.blockSide : ℝ)) ^ (m - 1 - i) * B := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    refine (sourceTransport_norm_le hodd h2 D p hθ s hs i m hi' hm.le).trans ?_
    exact mul_le_mul_of_nonneg_left (hB i (by omega)) (by positivity)
  have hsum2 : ∑ i ∈ Finset.range m, weightedScaleNorm D p θ 2 m (sourceTransport s i m) ≤ 284 * B := by
    refine (Finset.sum_le_sum hsumB).trans ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have := sum_inv_pow_le_two hL2 m
    nlinarith
  obtain ⟨hu4, hu2⟩ := baseTransport_norm_le hodd h2 D p hθ (a 0) (ha 0) m hm.le
  constructor
  · have h1 := finsetLpNorm_mono (P := 4) (by norm_num) (innerBonds D m) hpt
    have h3 := finsetLpNorm_add_le (P := 4) (by norm_num) (innerBonds D m)
      (fun b => scaleWeight p θ m b.1 * baseTransport (a 0) m b.1 b.2)
      (fun b => ∑ i ∈ Finset.range m, scaleWeight p θ m b.1 * sourceTransport s i m b.1 b.2)
    have h4 := finsetLpNorm_sum_le (P := 4) (by norm_num) (Finset.range m) (innerBonds D m)
      (fun i b => scaleWeight p θ m b.1 * sourceTransport s i m b.1 b.2)
    have h5 : ∑ i ∈ Finset.range m, finsetLpNorm 4 (innerBonds D m) (fun b => scaleWeight p θ m b.1 * sourceTransport s i m b.1 b.2) ≤
        ∑ i ∈ Finset.range m, weightedScaleNorm D p θ 2 m (sourceTransport s i m) :=
      Finset.sum_le_sum fun i _ => finsetLpNorm_four_le_two _ _
    unfold weightedScaleNorm at *
    linarith
  · have h1 := finsetLpNorm_mono (P := 2) (by norm_num) (innerBonds D m) hpt
    have h3 := finsetLpNorm_add_le (P := 2) (by norm_num) (innerBonds D m)
      (fun b => scaleWeight p θ m b.1 * baseTransport (a 0) m b.1 b.2)
      (fun b => ∑ i ∈ Finset.range m, scaleWeight p θ m b.1 * sourceTransport s i m b.1 b.2)
    have h4 := finsetLpNorm_sum_le (P := 2) (by norm_num) (Finset.range m) (innerBonds D m)
      (fun i b => scaleWeight p θ m b.1 * sourceTransport s i m b.1 b.2)
    unfold weightedScaleNorm at *
    linarith
end Scales
end YangMills.Construction.LevelRecursion
end

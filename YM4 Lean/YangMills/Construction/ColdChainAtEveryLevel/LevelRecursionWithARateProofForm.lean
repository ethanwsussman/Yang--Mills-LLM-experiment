import YangMills.Construction.ColdChainAtEveryLevel.LevelRecursionNearACellProof
import YangMills.Construction.ColdChainAtEveryLevel.LevelRecursionWithARate
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace RateRecursion
variable {F : BlockFrame}
section Norms
variable {ι : Type} {s : Finset ι}
theorem sqrt_sqrt_eq_rpow_quarter {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num
theorem sqrt_sqrt_pow_four_eq {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) ^ 4 = x := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.sqrt_sqrt_pow_four <;> assumption
theorem sqrt_sqrt_le_of_le_pow {a x : ℝ} (ha : 0 ≤ a) (h : x ≤ a ^ 4) : Real.sqrt (Real.sqrt x) ≤ a := by
  have e : Real.sqrt (Real.sqrt (a ^ 4)) = a := by
    have e1 : a ^ 4 = (a ^ 2) ^ 2 := by ring
    rw [e1, Real.sqrt_sq (by positivity), Real.sqrt_sq ha]
  calc Real.sqrt (Real.sqrt x) ≤ Real.sqrt (Real.sqrt (a ^ 4)) := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)
    _ = a := e
theorem sqrt_sum_sq_add_le {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    Real.sqrt (∑ i ∈ s, (f i + g i) ^ 2) ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) + Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  have h := Real.Lp_add_le_of_nonneg (s := s) (f := f) (g := g) (p := 2) (by norm_num) hf hg
  simp only [Real.rpow_two] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact h
theorem sqrt_sqrt_sum_pow_four_add_le {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    Real.sqrt (Real.sqrt (∑ i ∈ s, (f i + g i) ^ 4)) ≤
      Real.sqrt (Real.sqrt (∑ i ∈ s, f i ^ 4)) + Real.sqrt (Real.sqrt (∑ i ∈ s, g i ^ 4)) := by
  have h := Real.Lp_add_le_of_nonneg (s := s) (f := f) (g := g) (p := 4) (by norm_num) hf hg
  have e : ∀ x : ℝ, x ^ (4 : ℝ) = x ^ 4 := fun x => by
    rw [← Real.rpow_natCast]
    norm_num
  simp only [e] at h
  rw [sqrt_sqrt_eq_rpow_quarter (Finset.sum_nonneg fun i hi => by have := hf i hi; have := hg i hi; positivity),
    sqrt_sqrt_eq_rpow_quarter (Finset.sum_nonneg fun i hi => by have := hf i hi; positivity),
    sqrt_sqrt_eq_rpow_quarter (Finset.sum_nonneg fun i hi => by have := hg i hi; positivity)]
  exact h
theorem sqrt_sqrt_sum_pow_four_le_sqrt_sum_sq {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt (Real.sqrt (∑ i ∈ s, f i ^ 4)) ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) := by
  have hS : 0 ≤ ∑ i ∈ s, f i ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h : ∑ i ∈ s, f i ^ 4 ≤ (∑ i ∈ s, f i ^ 2) ^ 2 := by
    rw [sq (∑ i ∈ s, f i ^ 2), Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have h1 : f i ^ 2 ≤ ∑ i ∈ s, f i ^ 2 :=
      Finset.single_le_sum (f := fun i => f i ^ 2) (fun i _ => by positivity) hi
    have e : f i ^ 4 = f i ^ 2 * f i ^ 2 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  refine Real.sqrt_le_sqrt ?_
  calc Real.sqrt (∑ i ∈ s, f i ^ 4) ≤ Real.sqrt ((∑ i ∈ s, f i ^ 2) ^ 2) := Real.sqrt_le_sqrt h
    _ = ∑ i ∈ s, f i ^ 2 := Real.sqrt_sq hS
end Norms
variable {D : Finset F.Cell}
theorem sqrt_sum_sq_le_of_sum_le_sq {ι : Type} {s : Finset ι} {f : ι → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (h : ∑ i ∈ s, f i ^ 2 ≤ x ^ 2) :
    Real.sqrt (∑ i ∈ s, f i ^ 2) ≤ x := by apply _root_.YangMills.Construction.BlockAverages.QuarticRecursion.sqrt_sum_sq_le_of_le_sq <;> assumption
theorem lineBlockAverage_nonneg_of_nonneg {j : ℕ} {f : F.Site j → Fin 4 → ℝ} (hf : ∀ x i, 0 ≤ f x i)
    (c : F.Site (j + 1) × Fin 4) : 0 ≤ lineBlockAverage f c := by
  unfold lineBlockAverage
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hf _ _)
def growthConstant (L : ℕ) : ℝ := 16 * (3 * (L : ℝ)) ^ 4
def closingConstant (L : ℕ) (K : ℝ) : ℝ :=
  256 * K ^ 2 * growthConstant L + 16 * K ^ 2 * growthConstant L ^ 2 + 16 * K ^ 2 * growthConstant L
theorem one_le_growthConstant {L : ℕ} (h : 1 ≤ L) : 1 ≤ growthConstant L := by
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast h
  have h2 : (1 : ℝ) ≤ (3 * (L : ℝ)) ^ 4 := one_le_pow₀ (by linarith)
  unfold growthConstant
  linarith
theorem closingConstant_nonneg {L : ℕ} (h : 1 ≤ L) (K : ℝ) : 0 ≤ closingConstant L K := by
  have := one_le_growthConstant h
  unfold closingConstant
  positivity
theorem four_mul_sum_le_sq_of_bounds {K δ B c1 A M S4 P R k G : ℝ} (hK : 0 ≤ K) (hδ0 : 0 ≤ δ) (hB0 : 0 ≤ B)
    (hδc : δ ≤ c1) (hBc : B ≤ c1) (hA0 : 0 ≤ A) (hA : A ≤ 4 * B) (hk : 1 ≤ k) (hM0 : 0 ≤ M) (hMB : M ≤ B ^ 2)
    (hS4 : S4 ≤ k * A ^ 4) (hP : P ≤ k * δ ^ 2 * A ^ 2) (hR : R ≤ k ^ 2 * A ^ 2 * M)
    (hG : G = 256 * K ^ 2 * k + 16 * K ^ 2 * k ^ 2 + 16 * K ^ 2 * k) (hc : 64 * G * c1 ^ 2 ≤ 1) :
    4 * (M + K ^ 2 * S4 + K ^ 2 * P + K ^ 2 * R) ≤ (12 / 5 * B) ^ 2 := by
  have hA2 : A ^ 2 ≤ 16 * B ^ 2 := by
    calc A ^ 2 ≤ (4 * B) ^ 2 := pow_le_pow_left₀ hA0 hA 2
      _ = 16 * B ^ 2 := by ring
  have hA4 : A ^ 4 ≤ 256 * B ^ 4 := by
    calc A ^ 4 ≤ (4 * B) ^ 4 := pow_le_pow_left₀ hA0 hA 4
      _ = 256 * B ^ 4 := by ring
  have hK2 : 0 ≤ K ^ 2 := by positivity
  have hk0 : 0 ≤ k := by linarith
  have t1 : K ^ 2 * S4 ≤ 256 * K ^ 2 * k * (B ^ 2 * B ^ 2) := by
    have h1 : S4 ≤ k * (256 * B ^ 4) := hS4.trans (mul_le_mul_of_nonneg_left hA4 hk0)
    have := mul_le_mul_of_nonneg_left h1 hK2
    calc K ^ 2 * S4 ≤ K ^ 2 * (k * (256 * B ^ 4)) := this
      _ = _ := by ring
  have t2 : K ^ 2 * P ≤ 16 * K ^ 2 * k * (δ ^ 2 * B ^ 2) := by
    have h1 : P ≤ k * δ ^ 2 * (16 * B ^ 2) := hP.trans (mul_le_mul_of_nonneg_left hA2 (by positivity))
    have := mul_le_mul_of_nonneg_left h1 hK2
    calc K ^ 2 * P ≤ K ^ 2 * (k * δ ^ 2 * (16 * B ^ 2)) := this
      _ = _ := by ring
  have t3 : K ^ 2 * R ≤ 16 * K ^ 2 * k ^ 2 * (B ^ 2 * B ^ 2) := by
    have h0 : A ^ 2 * M ≤ (16 * B ^ 2) * B ^ 2 := mul_le_mul hA2 hMB hM0 (by positivity)
    have h1 : R ≤ k ^ 2 * ((16 * B ^ 2) * B ^ 2) := by
      calc R ≤ k ^ 2 * A ^ 2 * M := hR
        _ = k ^ 2 * (A ^ 2 * M) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h0 (by positivity)
    have := mul_le_mul_of_nonneg_left h1 hK2
    calc K ^ 2 * R ≤ K ^ 2 * (k ^ 2 * ((16 * B ^ 2) * B ^ 2)) := this
      _ = _ := by ring
  have hB2 : B ^ 2 ≤ c1 ^ 2 := pow_le_pow_left₀ hB0 hBc 2
  have hδ2 : δ ^ 2 ≤ c1 ^ 2 := pow_le_pow_left₀ hδ0 hδc 2
  have hBB : 0 ≤ B ^ 2 := by positivity
  set g1 := 256 * K ^ 2 * k with hg1
  set g2 := 16 * K ^ 2 * k ^ 2 with hg2
  set g3 := 16 * K ^ 2 * k with hg3
  have a1 : 0 ≤ g1 := by positivity
  have a2 : 0 ≤ g2 := by positivity
  have a3 : 0 ≤ g3 := by positivity
  have w : g1 * B ^ 2 + g3 * δ ^ 2 + g2 * B ^ 2 ≤ G * c1 ^ 2 := by
    have u1 := mul_le_mul_of_nonneg_left hB2 a1
    have u2 := mul_le_mul_of_nonneg_left hδ2 a3
    have u3 := mul_le_mul_of_nonneg_left hB2 a2
    rw [hG]
    nlinarith
  have w2 : (g1 * B ^ 2 + g3 * δ ^ 2 + g2 * B ^ 2) * B ^ 2 ≤ 1 / 64 * B ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ hBB
    linarith
  have e : (12 / 5 * B) ^ 2 = 144 / 25 * B ^ 2 := by ring
  rw [e]
  nlinarith
theorem sqrt_sum_source_sq_le (hA : averagesAndLocalSizesStatement) (hL : Odd F.blockSide) {j : ℕ}
    (hj : j + 1 ≤ F.top)
    {K δ B c1 : ℝ} {a : F.Site j → Fin 4 → ℝ} {T : F.Site (j + 1) × Fin 4 → ℝ}
    {m e : F.Site (j + 1) → Fin 4 → ℝ}
    (hK : 0 ≤ K) (hδ0 : 0 ≤ δ) (hB0 : 0 ≤ B) (hδc : δ ≤ c1) (hBc : B ≤ c1)
    (hc : 64 * closingConstant F.blockSide K * c1 ^ 2 ≤ 1)
    (ha : ∀ x i, 0 ≤ a x i) (hm : ∀ x i, 0 ≤ m x i) (he : ∀ x i, 0 ≤ e x i)
    (hA4 : Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D j, a b.1 b.2 ^ 4)) ≤ 4 * B)
    (hM : Real.sqrt (∑ c ∈ innerBonds D (j + 1), m c.1 c.2 ^ 2) ≤ B)
    (hE : Real.sqrt (Real.sqrt (∑ c ∈ innerBonds D (j + 1), e c.1 c.2 ^ 4)) ≤ δ)
    (hT0 : ∀ c, 0 ≤ T c)
    (hT1 : ∀ c, T c ^ 4 ≤ 4 * (3 * (F.blockSide : ℝ)) ^ 4 * ∑ b ∈ innerBonds D j, a b.1 b.2 ^ 4)
    (hT2 : ∑ c ∈ innerBonds D (j + 1), T c ^ 4 ≤
      16 * (3 * (F.blockSide : ℝ)) ^ 4 * ∑ b ∈ innerBonds D j, a b.1 b.2 ^ 4) :
    Real.sqrt (∑ c ∈ innerBonds D (j + 1), (m c.1 c.2 + K * T c ^ 2 + K * e c.1 c.2 * T c +
      K * m c.1 c.2 * T c) ^ 2) ≤ 12 / 5 * B := by
  have hLp : 1 ≤ F.blockSide := hL.pos
  have hk := one_le_growthConstant hLp
  set S := ∑ b ∈ innerBonds D j, a b.1 b.2 ^ 4 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun b _ => by have := ha b.1 b.2; positivity
  set A := Real.sqrt (Real.sqrt S) with hAdef
  have hAn : 0 ≤ A := Real.sqrt_nonneg _
  have hAp : A ^ 4 = S := sqrt_sqrt_pow_four_eq hS0
  set Ω := innerBonds D (j + 1) with hΩ
  set k := growthConstant F.blockSide with hkdef
  have hTk : ∀ c, T c ≤ k * A := by
    intro c
    have h1 : T c ^ 4 ≤ k * A ^ 4 := by
      rw [hAp]
      refine (hT1 c).trans (mul_le_mul_of_nonneg_right ?_ hS0)
      have : 0 ≤ (3 * (F.blockSide : ℝ)) ^ 4 := by positivity
      rw [hkdef]
      unfold growthConstant
      linarith
    have h2 : k ≤ k ^ 4 := le_self_pow₀ hk (by norm_num)
    have h3 : T c ^ 4 ≤ (k * A) ^ 4 := by
      rw [mul_pow]
      exact h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h3
  have hS4 : ∑ c ∈ Ω, T c ^ 4 ≤ k * A ^ 4 := by
    rw [hAp]
    exact hT2
  set sumM := ∑ c ∈ Ω, m c.1 c.2 ^ 2 with hsumM
  have hsumM0 : 0 ≤ sumM := Finset.sum_nonneg fun c _ => by positivity
  have hsumMB : sumM ≤ B ^ 2 := by
    have := Real.sq_sqrt hsumM0
    nlinarith [Real.sqrt_nonneg sumM]
  set sumE := ∑ c ∈ Ω, e c.1 c.2 ^ 4 with hsumE
  have hsumE0 : 0 ≤ sumE := Finset.sum_nonneg fun c _ => by have := he c.1 c.2; positivity
  have hsumEδ : sumE ≤ δ ^ 4 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hE 4
    rwa [sqrt_sqrt_pow_four_eq hsumE0] at this
  have hP : ∑ c ∈ Ω, (e c.1 c.2 * T c) ^ 2 ≤ k * δ ^ 2 * A ^ 2 := by
    have hc1 : (∑ c ∈ Ω, (e c.1 c.2) ^ 2 * (T c) ^ 2) ^ 2 ≤
        (∑ c ∈ Ω, ((e c.1 c.2) ^ 2) ^ 2) * ∑ c ∈ Ω, ((T c) ^ 2) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have e1 : ∑ c ∈ Ω, ((e c.1 c.2) ^ 2) ^ 2 = sumE := Finset.sum_congr rfl fun c _ => by ring
    have e2 : ∑ c ∈ Ω, ((T c) ^ 2) ^ 2 = ∑ c ∈ Ω, T c ^ 4 := Finset.sum_congr rfl fun c _ => by ring
    rw [e1, e2] at hc1
    have h2 : sumE * ∑ c ∈ Ω, T c ^ 4 ≤ δ ^ 4 * (k * A ^ 4) :=
      mul_le_mul hsumEδ hS4 (Finset.sum_nonneg fun c _ => by have := hT0 c; positivity) (by positivity)
    have h3 : δ ^ 4 * (k * A ^ 4) ≤ (k * δ ^ 2 * A ^ 2) ^ 2 := by
      have : k ≤ k ^ 2 := le_self_pow₀ hk (by norm_num)
      have h4 : 0 ≤ δ ^ 4 * A ^ 4 := by positivity
      calc δ ^ 4 * (k * A ^ 4) = k * (δ ^ 4 * A ^ 4) := by ring
        _ ≤ k ^ 2 * (δ ^ 4 * A ^ 4) := mul_le_mul_of_nonneg_right this h4
        _ = _ := by ring
    have h5 : (∑ c ∈ Ω, (e c.1 c.2) ^ 2 * (T c) ^ 2) ^ 2 ≤ (k * δ ^ 2 * A ^ 2) ^ 2 := hc1.trans (h2.trans h3)
    have h6 := (abs_le_of_sq_le_sq' h5 (by positivity)).2
    calc ∑ c ∈ Ω, (e c.1 c.2 * T c) ^ 2 = ∑ c ∈ Ω, (e c.1 c.2) ^ 2 * (T c) ^ 2 :=
          Finset.sum_congr rfl fun c _ => by ring
      _ ≤ _ := h6
  have hR : ∑ c ∈ Ω, (m c.1 c.2 * T c) ^ 2 ≤ k ^ 2 * A ^ 2 * sumM := by
    rw [hsumM, Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have h2 := pow_le_pow_left₀ (hT0 c) (hTk c) 2
    calc (m c.1 c.2 * T c) ^ 2 = T c ^ 2 * m c.1 c.2 ^ 2 := by ring
      _ ≤ (k * A) ^ 2 * m c.1 c.2 ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = _ := by ring
  have hsum : ∑ c ∈ Ω, (m c.1 c.2 + K * T c ^ 2 + K * e c.1 c.2 * T c + K * m c.1 c.2 * T c) ^ 2 ≤
      4 * (sumM + K ^ 2 * ∑ c ∈ Ω, T c ^ 4 + K ^ 2 * ∑ c ∈ Ω, (e c.1 c.2 * T c) ^ 2 +
        K ^ 2 * ∑ c ∈ Ω, (m c.1 c.2 * T c) ^ 2) := by
    have hpt : ∀ c ∈ Ω, (m c.1 c.2 + K * T c ^ 2 + K * e c.1 c.2 * T c + K * m c.1 c.2 * T c) ^ 2 ≤
        4 * (m c.1 c.2 ^ 2 + K ^ 2 * T c ^ 4 + K ^ 2 * (e c.1 c.2 * T c) ^ 2 + K ^ 2 * (m c.1 c.2 * T c) ^ 2) := by
      intro c _
      have e' : ∀ x y z w : ℝ, (x + y + z + w) ^ 2 ≤ 4 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
        intro x y z w
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - w), sq_nonneg (y - z), sq_nonneg (y - w),
          sq_nonneg (z - w)]
      have := e' (m c.1 c.2) (K * T c ^ 2) (K * e c.1 c.2 * T c) (K * m c.1 c.2 * T c)
      calc _ ≤ _ := this
        _ = _ := by ring
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum]
  exact sqrt_sum_sq_le_of_sum_le_sq (by positivity) (hsum.trans (four_mul_sum_le_sq_of_bounds hK hδ0 hB0 hδc hBc
    hAn hA4 hk hsumM0 hsumMB hS4 hP hR rfl hc))
end RateRecursion
open RateRecursion in
theorem quarticBoundAcrossLevelsWithRate_of_averages (hA : averagesAndLocalSizesStatement) :
    QuarticBoundAcrossLevelsWithRate := by
  intro L W K c0 hL h5 hK hc0
  have hk := one_le_growthConstant (L := L) hL.pos
  have hG := closingConstant_nonneg (L := L) hL.pos K
  have hkp : 0 < growthConstant L := by linarith
  set c1 := min (min (c0 / (4 * growthConstant L)) c0) (1 / (8 * (closingConstant L K + 1))) with hc1def
  have hc1p : 0 < c1 := by
    refine lt_min (lt_min (by positivity) hc0) (by positivity)
  refine ⟨c1, hc1p, ?_⟩
  intro F D a m e δ B hFL hD hδ0 hδ hB0 hB ha hm he h0 hM hE hrec
  subst hFL
  have hL5 : (5 : ℝ) ≤ F.blockSide := by exact_mod_cast h5
  have e1 : 64 * closingConstant F.blockSide K * c1 ^ 2 ≤ 1 := by
    have h1 : c1 ≤ 1 / (8 * (closingConstant F.blockSide K + 1)) := min_le_right _ _
    have h2 : c1 ^ 2 ≤ (1 / (8 * (closingConstant F.blockSide K + 1))) ^ 2 := pow_le_pow_left₀ hc1p.le h1 2
    have h3 : 64 * closingConstant F.blockSide K * (1 / (8 * (closingConstant F.blockSide K + 1))) ^ 2 ≤ 1 := by
      have : 64 * closingConstant F.blockSide K * (1 / (8 * (closingConstant F.blockSide K + 1))) ^ 2 =
          closingConstant F.blockSide K / (closingConstant F.blockSide K + 1) ^ 2 := by
        field_simp
        ring
      rw [this, div_le_one (by positivity)]
      nlinarith
    calc 64 * closingConstant F.blockSide K * c1 ^ 2 ≤
          64 * closingConstant F.blockSide K * (1 / (8 * (closingConstant F.blockSide K + 1))) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 1 := h3
  have e2 : growthConstant F.blockSide * (4 * c1) ≤ c0 := by
    have h1 : c1 ≤ c0 / (4 * growthConstant F.blockSide) := (min_le_left _ _).trans (min_le_left _ _)
    calc growthConstant F.blockSide * (4 * c1) = 4 * growthConstant F.blockSide * c1 := by ring
      _ ≤ 4 * growthConstant F.blockSide * (c0 / (4 * growthConstant F.blockSide)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = c0 := by field_simp
  have e3 : c1 ≤ c0 := (min_le_left _ _).trans (min_le_right _ _)
  have main : ∀ j, j < F.top → ∃ v ε : F.Site j → Fin 4 → ℝ, (∀ x i, 0 ≤ v x i) ∧ (∀ x i, 0 ≤ ε x i) ∧
      (∀ b ∈ innerBonds D j, a j b.1 b.2 ≤ v b.1 b.2 + ε b.1 b.2) ∧
      ∑ b ∈ innerBonds D j, v b.1 b.2 ^ 4 ≤ B ^ 4 ∧
      Real.sqrt (∑ b ∈ innerBonds D j, ε b.1 b.2 ^ 2) ≤ 3 * B ∧
      Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D j, a j b.1 b.2 ^ 4)) ≤ 4 * B := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨a 0, fun _ _ => 0, ha 0, fun _ _ => le_rfl, fun b _ => by simp, ?_, ?_, ?_⟩
      · have hS : 0 ≤ ∑ b ∈ innerBonds D 0, a 0 b.1 b.2 ^ 4 :=
          Finset.sum_nonneg fun b _ => by have := ha 0 b.1 b.2; positivity
        have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h0 4
        rwa [sqrt_sqrt_pow_four_eq hS] at this
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, Real.sqrt_zero]
        positivity
      · linarith
    | succ j ih =>
      intro hj
      obtain ⟨v, ε, hv0, hε0, i1, iv, i2, i3⟩ := ih (by omega)
      have hjn : j + 1 ≤ F.top := by omega
      obtain ⟨hline, -, -, T₀, hT00, hTb, -, hT10, hT2, -⟩ := hA F D j (a j) hL hjn (ha j)
      set T : F.Site (j + 1) × Fin 4 → ℝ := fun c => T₀ c.1 with hTdef
      have hT0 : ∀ c, 0 ≤ T c := fun c => hT00 c.1
      have hT1 : ∀ c, T c ^ 4 ≤ 4 * (3 * (F.blockSide : ℝ)) ^ 4 * ∑ b ∈ innerBonds D j, a j b.1 b.2 ^ 4 :=
        fun c => hT10 c.1
      obtain ⟨-, hv4, -, -⟩ := hA F D j v hL hjn hv0
      obtain ⟨-, -, hε2, -⟩ := hA F D j ε hL hjn hε0
      have hMj := hM j hj
      have hEj := hE j hj
      set ρ : F.Site (j + 1) × Fin 4 → ℝ := fun c => m j c.1 c.2 + K * T c ^ 2 + K * e j c.1 c.2 * T c +
        K * m j c.1 c.2 * T c with hρ
      have hρ0 : ∀ c, 0 ≤ ρ c := by
        intro c
        have h1 := hm j c.1 c.2
        have h2 := he j c.1 c.2
        have h3 := hT0 c
        simp only [hρ]
        positivity
      have hρn := sqrt_sum_source_sq_le (D := D) hA hL hjn hK hδ0 hB0 hδ hB e1 (ha j) (hm j) (he j) i3 hMj hEj
        hT0 hT1 hT2
      set v' : F.Site (j + 1) → Fin 4 → ℝ := fun y i => lineBlockAverage v (y, i) with hv'
      set ε' : F.Site (j + 1) → Fin 4 → ℝ := fun y i => lineBlockAverage ε (y, i) + ρ (y, i) with hε'
      have hv'0 : ∀ x i, 0 ≤ v' x i := fun x i => lineBlockAverage_nonneg_of_nonneg hv0 _
      have hε'0 : ∀ x i, 0 ≤ ε' x i := fun x i => add_nonneg (lineBlockAverage_nonneg_of_nonneg hε0 _) (hρ0 _)
      have hS0 : 0 ≤ ∑ b ∈ innerBonds D j, a j b.1 b.2 ^ 4 :=
        Finset.sum_nonneg fun b _ => by have := ha j b.1 b.2; positivity
      have pt : ∀ c ∈ innerBonds D (j + 1), a (j + 1) c.1 c.2 ≤ v' c.1 c.2 + ε' c.1 c.2 := by
        intro c hc
        have hTc : T c ≤ c0 := by
          have h4 : T c ^ 4 ≤ (growthConstant F.blockSide * (4 * B)) ^ 4 := by
            have hs4 : ∑ b ∈ innerBonds D j, a j b.1 b.2 ^ 4 ≤ (4 * B) ^ 4 := by
              have := pow_le_pow_left₀ (Real.sqrt_nonneg _) i3 4
              rwa [sqrt_sqrt_pow_four_eq hS0] at this
            have hkn : 4 * (3 * (F.blockSide : ℝ)) ^ 4 ≤ growthConstant F.blockSide ^ 4 := by
              have h1 : growthConstant F.blockSide ≤ growthConstant F.blockSide ^ 4 :=
                le_self_pow₀ (one_le_growthConstant hL.pos) (by norm_num)
              have h2 : 4 * (3 * (F.blockSide : ℝ)) ^ 4 ≤ growthConstant F.blockSide := by
                unfold growthConstant
                have : 0 ≤ (3 * (F.blockSide : ℝ)) ^ 4 := by positivity
                linarith
              exact h2.trans h1
            calc T c ^ 4 ≤ 4 * (3 * (F.blockSide : ℝ)) ^ 4 * ∑ b ∈ innerBonds D j, a j b.1 b.2 ^ 4 := hT1 c
              _ ≤ growthConstant F.blockSide ^ 4 * (4 * B) ^ 4 := mul_le_mul hkn hs4 hS0 (by positivity)
              _ = _ := by ring
          have h5 : T c ≤ growthConstant F.blockSide * (4 * B) :=
            le_of_pow_le_pow_left₀ (by norm_num)
              (mul_nonneg (le_trans zero_le_one (one_le_growthConstant hL.pos)) (by positivity)) h4
          have h6 : growthConstant F.blockSide * (4 * B) ≤ growthConstant F.blockSide * (4 * c1) :=
            mul_le_mul_of_nonneg_left (by linarith) (le_trans zero_le_one (one_le_growthConstant hL.pos))
          linarith
        have hmB : m j c.1 c.2 ≤ B := by
          refine le_trans ?_ hMj
          refine Real.le_sqrt_of_sq_le ?_
          exact Finset.single_le_sum (f := fun c : F.Site (j + 1) × Fin 4 => m j c.1 c.2 ^ 2)
            (fun c _ => by positivity) hc
        have hr := hrec j hj c hc (T c) (hT0 c) hTc (by linarith) (hTb c hc)
        have hadd : lineBlockAverage (a j) c ≤ lineBlockAverage v c + lineBlockAverage ε c := by
          have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
          unfold lineBlockAverage
          rw [← mul_add, ← Finset.sum_add_distrib]
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x hx => ?_) (by positivity)
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun r hr => i1 _ (hline c hc x hx r (Finset.mem_range.1 hr))
        show a (j + 1) c.1 c.2 ≤ lineBlockAverage v (c.1, c.2) + (lineBlockAverage ε (c.1, c.2) + ρ (c.1, c.2))
        simp only [hρ, Prod.mk.eta]
        nlinarith
      have hE' : Real.sqrt (∑ b ∈ innerBonds D (j + 1), ε' b.1 b.2 ^ 2) ≤ 3 * B := by
        have hQ : Real.sqrt (∑ c ∈ innerBonds D (j + 1), lineBlockAverage ε c ^ 2) ≤ 3 / 5 * B := by
          have hE0 : 0 ≤ ∑ b ∈ innerBonds D j, ε b.1 b.2 ^ 2 := Finset.sum_nonneg fun b _ => by positivity
          have h2 : Real.sqrt (∑ c ∈ innerBonds D (j + 1), lineBlockAverage ε c ^ 2) ≤
              (1 / (F.blockSide : ℝ)) * Real.sqrt (∑ b ∈ innerBonds D j, ε b.1 b.2 ^ 2) := by
            have e1' : (1 / (F.blockSide : ℝ) ^ 2) * ∑ b ∈ innerBonds D j, ε b.1 b.2 ^ 2 =
                ((1 / (F.blockSide : ℝ)) * Real.sqrt (∑ b ∈ innerBonds D j, ε b.1 b.2 ^ 2)) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt hE0]
              field_simp
            rw [e1'] at hε2
            exact sqrt_sum_sq_le_of_sum_le_sq (by positivity) hε2
          have h3 : 1 / (F.blockSide : ℝ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hL5
          calc _ ≤ (1 / (F.blockSide : ℝ)) * Real.sqrt (∑ b ∈ innerBonds D j, ε b.1 b.2 ^ 2) := h2
            _ ≤ (1 / 5) * (3 * B) := mul_le_mul h3 i2 (Real.sqrt_nonneg _) (by norm_num)
            _ = 3 / 5 * B := by ring
        have hmk := sqrt_sum_sq_add_le (s := innerBonds D (j + 1)) (f := fun c => lineBlockAverage ε c)
          (g := fun c => ρ c) (fun c _ => lineBlockAverage_nonneg_of_nonneg hε0 c) (fun c _ => hρ0 c)
        have ee : ∀ c : F.Site (j + 1) × Fin 4, ε' c.1 c.2 = lineBlockAverage ε c + ρ c := fun c => rfl
        simp only [ee]
        have : Real.sqrt (∑ c ∈ innerBonds D (j + 1), ρ c ^ 2) ≤ 12 / 5 * B := hρn
        linarith
      have hv'4 : ∑ b ∈ innerBonds D (j + 1), v' b.1 b.2 ^ 4 ≤ B ^ 4 := hv4.trans iv
      refine ⟨v', ε', hv'0, hε'0, pt, hv'4, hE', ?_⟩
      have h1 : ∑ b ∈ innerBonds D (j + 1), a (j + 1) b.1 b.2 ^ 4 ≤
          ∑ b ∈ innerBonds D (j + 1), (v' b.1 b.2 + ε' b.1 b.2) ^ 4 :=
        Finset.sum_le_sum fun c hc => pow_le_pow_left₀ (ha _ _ _) (pt c hc) 4
      have h2 := sqrt_sqrt_sum_pow_four_add_le (s := innerBonds D (j + 1)) (f := fun b => v' b.1 b.2)
        (g := fun b => ε' b.1 b.2) (fun b _ => hv'0 _ _) (fun b _ => hε'0 _ _)
      have h3 := sqrt_sqrt_sum_pow_four_le_sqrt_sum_sq (s := innerBonds D (j + 1)) (f := fun b => ε' b.1 b.2)
        (fun b _ => hε'0 _ _)
      have h4 : Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D (j + 1), v' b.1 b.2 ^ 4)) ≤ B :=
        sqrt_sqrt_le_of_le_pow hB0 hv'4
      calc Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D (j + 1), a (j + 1) b.1 b.2 ^ 4))
          ≤ Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D (j + 1), (v' b.1 b.2 + ε' b.1 b.2) ^ 4)) :=
            Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h1)
        _ ≤ 4 * B := by linarith
  intro j hj
  obtain ⟨-, -, -, -, -, -, -, h⟩ := main j hj
  exact h
end YangMills.Construction.BlockAverages
end

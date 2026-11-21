import YangMills.Construction.ColdChainAtEveryLevel.SecondDifferenceOfTheTermOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.LowerLevelTerms
open BlockAverages ComplexifiedQuaternions ComplexLevels ComplexRemainders ComplexDifferences HullBounds
  LevelRecursion RealDirections BondSecondDifference BlockLines LinearLevels
variable {F : BlockFrame} {j : ℕ}
structure ReferenceNear (D : Finset F.Cell) (R : F.FieldChain) (C₀ s : ℝ) : Prop where
  contours : ContoursNearUnit R D C₀ s
  defect : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1),
    ‖((referenceDefect R m c : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
    C₀ * s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (m + 1))) ^ 3
  defect_top : ∀ c ∈ innerBonds D (F.depth + 1),
    ‖((referenceDefect R F.depth c : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ C₀ * s
  length : ∀ m, m < F.top → ∀ c ∈ innerBonds D (m + 1), |‖contourAverage (R m) c‖ - 1| ≤
    C₀ * s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (m + 1))) ^ 3
structure SmallDirectionTriple (D : Finset F.Cell) (p : F.Site 0) (θ : ℝ) (R : F.FieldChain)
    (W₁ W₂ W₃ : ChainChart F) (C₀ s T B₁ B₂ : ℝ) : Prop where
  C₀_pos : 0 < C₀
  s_pos : 0 < s
  s_le : s ≤ 1
  spread_le : C₀ * s ≤ 1 / 64
  T_nonneg : 0 ≤ T
  T_le : T ≤ 1 / 4000
  B₁_nonneg : 0 ≤ B₁
  B₂_nonneg : 0 ≤ B₂
  radius : 24 * (2 * T + C₀ * s) < hullBallRadius F.blockSide
  lip : 12 * (200000 * (F.blockSide : ℝ) ^ 2) * (2 * T + C₀ * s) ≤ 1
  dev₁ : ∀ m, m < F.top → weightedScaleNorm D p θ 4 m
    (fun z d => ‖levelDeviation R (realChart W₁) m z d‖) ≤ 82272 * B₁
  dev₂ : ∀ m, m < F.top → weightedScaleNorm D p (-θ) 4 m
    (fun z d => ‖levelDeviation R (realChart W₂) m z d‖) ≤ 82272 * B₂
  dev₁₃ : ∀ m, m < F.top → weightedScaleNorm D p (-θ) 4 m
    (fun z d => ‖(levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₁) m) z d‖) ≤ 82272 * B₂
  dev₂₃ : ∀ m, m < F.top → weightedScaleNorm D p θ 4 m
    (fun z d => ‖(levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₂) m) z d‖) ≤ 82272 * B₁
  second : ∀ m, m < F.top → weightedScaleNorm D p 0 2 m
    (fun z d => ‖(levelDeviation R (realChart W₃) m -
      (levelDeviation R (realChart W₁) m + levelDeviation R (realChart W₂) m)) z d‖) ≤
      2 * (142 * 8256 + 284 * secondSourceConst F.blockSide) * (B₁ * B₂)
  hull₁ : ∀ m, m < F.top → ∀ c ∈ innerBonds D (m + 1), bondHullNorm c (levelDeviation R (realChart W₁) m) ≤ T
  hull₂ : ∀ m, m < F.top → ∀ c ∈ innerBonds D (m + 1), bondHullNorm c (levelDeviation R (realChart W₂) m) ≤ T
  hull₃ : ∀ m, m < F.top → ∀ c ∈ innerBonds D (m + 1), bondHullNorm c (levelDeviation R (realChart W₃) m) ≤ T
  hull₁₃ : ∀ m, m < F.top → ∀ c ∈ innerBonds D (m + 1),
    bondHullNorm c (levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₁) m) ≤ T
  hull₂₃ : ∀ m, m < F.top → ∀ c ∈ innerBonds D (m + 1),
    bondHullNorm c (levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₂) m) ≤ T
  coarse₁ : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1), ‖(W₁.coarse m c.1 c.2 : ℍ[ℝ])‖ ≤ T
  coarse₂ : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1), ‖(W₂.coarse m c.1 c.2 : ℍ[ℝ])‖ ≤ T
  coarse₃ : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1),
    W₃.coarse m c.1 c.2 = W₁.coarse m c.1 c.2 + W₂.coarse m c.1 c.2
  level₁ : ∀ m, m + 1 < F.top →
    weightedScaleNorm D p θ 2 (m + 1) (fun y d => ‖(W₁.coarse m y d : ℍ[ℝ])‖) ≤ B₁
  level₂ : ∀ m, m + 1 < F.top →
    weightedScaleNorm D p (-θ) 2 (m + 1) (fun y d => ‖(W₂.coarse m y d : ℍ[ℝ])‖) ≤ B₂
def lowerCubicConst (L : ℕ) : ℝ := 1 + 6 * (200000 * (L : ℝ) ^ 2) + 3 * (16512 + 8256 ^ 2 / 2 + 2)
theorem cubicRemainder_le {a b T : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (haT : a ≤ T) (hbT : b ≤ T) (hT : T ≤ 1) :
    cubicRemainder a b ≤ (16512 + 8256 ^ 2 / 2 + 2) * T ^ 3 := by
  have hT0 : 0 ≤ T := ha.trans haT
  have hab : a * b ≤ T * T := mul_le_mul haT hbT hb hT0
  have h₁ : (a + b) * (8256 * a * b) ≤ 16512 * T ^ 3 := by
    have : (a + b) * (a * b) ≤ (2 * T) * (T * T) :=
      mul_le_mul (by linarith) hab (by positivity) (by positivity)
    nlinarith
  have h₂ : (8256 * a * b) ^ 2 / 2 ≤ 8256 ^ 2 / 2 * T ^ 3 := by
    have e : (8256 * a * b) ^ 2 / 2 = 8256 ^ 2 / 2 * (a * b) ^ 2 := by ring
    have h3 : (a * b) ^ 2 ≤ (T * T) ^ 2 := pow_le_pow_left₀ (by positivity) hab 2
    have h4 : (T * T) ^ 2 ≤ T ^ 3 := by
      have : T ^ 4 ≤ T ^ 3 := by
        have := mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ T ^ 3)
        nlinarith
      nlinarith
    rw [e]
    nlinarith
  simp only [cubicRemainder]
  linarith
theorem bond_bound_split {a p q κ Lp nΔ K n₁ n₂ n₁₃ n₂₃ m₁ m₂ R₃ T : ℝ} (ha0 : 0 ≤ a) (hp0 : 0 ≤ p) (hκ : 0 ≤ κ)
    (ha : a ≤ κ) (hp : p ≤ κ) (hq : q = p) (hLp0 : 0 ≤ Lp) (hLp : Lp ≤ 1) (hnΔ : 0 ≤ nΔ) (hK : 0 ≤ K)
    (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂) (hn₁₃0 : 0 ≤ n₁₃) (hn₂₃0 : 0 ≤ n₂₃) (hm₁0 : 0 ≤ m₁) (hm₂0 : 0 ≤ m₂)
    (hn₁₃ : n₁₃ ≤ T) (hn₂₃ : n₂₃ ≤ T) (hm₁ : m₁ ≤ T) (hm₂ : m₂ ≤ T) (hR₃0 : 0 ≤ R₃) (hR₃ : R₃ ≤ 6 * K * T)
    (hT1 : T ≤ 1) :
    (a + 24768 * p) * (m₁ * m₂) + q ^ 2 / 2 * (Lp * nΔ + 64 * K * n₁ * n₂) + Lp * n₁₃ * (m₁ ^ 2 / 2 + m₁ * q) +
        Lp * n₂₃ * (m₂ ^ 2 / 2 + m₂ * q) + R₃ * (m₁ * m₂) + 3 * cubicRemainder m₁ m₂ ≤
      24769 * κ * (m₁ * m₂) + κ ^ 2 / 2 * nΔ + 32 * K * κ ^ 2 * (n₁ * n₂) + κ * (m₁ * n₁₃) + κ * (n₂₃ * m₂) +
        (1 + 6 * K + 3 * (16512 + 8256 ^ 2 / 2 + 2)) * T ^ 3 := by
  subst hq
  have hT0 : 0 ≤ T := hm₁0.trans hm₁
  have hmm : 0 ≤ m₁ * m₂ := mul_nonneg hm₁0 hm₂0
  have b1 : (a + 24768 * q) * (m₁ * m₂) ≤ 24769 * κ * (m₁ * m₂) :=
    mul_le_mul_of_nonneg_right (by linarith) hmm
  have hq2 : q ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ hp0 hp 2
  have b2 : q ^ 2 / 2 * (Lp * nΔ + 64 * K * n₁ * n₂) ≤ κ ^ 2 / 2 * (nΔ + 64 * K * (n₁ * n₂)) := by
    have h3 : Lp * nΔ + 64 * K * n₁ * n₂ ≤ nΔ + 64 * K * (n₁ * n₂) := by
      have := mul_le_mul_of_nonneg_right hLp hnΔ
      nlinarith
    exact mul_le_mul (by linarith) h3 (by positivity) (by positivity)
  have b3 : ∀ {n m : ℝ}, 0 ≤ n → 0 ≤ m → n ≤ T → m ≤ T →
      Lp * n * (m ^ 2 / 2 + m * q) ≤ T ^ 3 / 2 + κ * (m * n) := by
    intro n m h0 h1 h2 h3
    have c1 : Lp * n * (m ^ 2 / 2 + m * q) ≤ n * (m ^ 2 / 2 + m * q) := by
      have := mul_le_mul_of_nonneg_right hLp (mul_nonneg h0 (by positivity : 0 ≤ m ^ 2 / 2 + m * q))
      nlinarith
    have c2 : n * (m ^ 2 / 2) ≤ T * (T ^ 2 / 2) := by
      have := pow_le_pow_left₀ h1 h3 2
      exact mul_le_mul h2 (by linarith) (by positivity) hT0
    have c3 : n * (m * q) ≤ κ * (m * n) := by
      have := mul_le_mul_of_nonneg_left hp (mul_nonneg h0 h1)
      nlinarith
    nlinarith
  have b4 := b3 hn₁₃0 hm₁0 hn₁₃ hm₁
  have b5 := b3 hn₂₃0 hm₂0 hn₂₃ hm₂
  have b6 : R₃ * (m₁ * m₂) ≤ 6 * K * T ^ 3 := by
    have : m₁ * m₂ ≤ T * T := mul_le_mul hm₁ hm₂ hm₂0 hT0
    calc R₃ * (m₁ * m₂) ≤ (6 * K * T) * (T * T) := mul_le_mul hR₃ this hmm (by positivity)
      _ = _ := by ring
  have b7 := cubicRemainder_le hm₁0 hm₂0 hm₁ hm₂ hT1
  have e5 : κ * (m₂ * n₂₃) = κ * (n₂₃ * m₂) := by ring
  rw [e5] at b5
  have e2 : κ ^ 2 / 2 * (nΔ + 64 * K * (n₁ * n₂)) = κ ^ 2 / 2 * nΔ + 32 * K * κ ^ 2 * (n₁ * n₂) := by ring
  rw [e2] at b2
  have e9 : (1 + 6 * K + 3 * (16512 + 8256 ^ 2 / 2 + 2)) * T ^ 3 =
      T ^ 3 / 2 + T ^ 3 / 2 + 6 * K * T ^ 3 + 3 * ((16512 + 8256 ^ 2 / 2 + 2) * T ^ 3) := by ring
  rw [e9]
  linarith
theorem hullFactor_nonneg (hodd : Odd F.blockSide) : 0 ≤ hullFactor F.blockSide := by
  obtain ⟨a, b, c⟩ := one_le_hullFactor_parts (F := F) hodd
  unfold hullFactor
  have : (0 : ℝ) ≤ hullBondCount F.blockSide := by linarith
  positivity
theorem sum_le_weightedScaleNorm_zero (hodd : Odd F.blockSide) {D : Finset F.Cell} (hD : D.card ≤ 81)
    (p : F.Site 0) (m : ℕ) (f : F.Site m → Fin 4 → ℝ) :
    ∑ b ∈ innerBonds D m, f b.1 b.2 ≤
      25 * ((F.blockSide : ℝ) ^ (F.top - m)) ^ 2 * weightedScaleNorm D p 0 2 m f := by
  set M := (F.blockSide : ℝ) ^ (F.top - m) with hM
  have hcard : ((innerBonds D m).card : ℝ) ≤ (25 * M ^ 2) ^ 2 := by
    have h1 := card_innerBonds_le hodd D m
    have h2 : ((innerBonds D m).card : ℝ) ≤ ((4 * (D.card * (F.blockSide ^ (F.top - m)) ^ 4) : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    have h3 : (D.card : ℝ) ≤ 81 := by exact_mod_cast hD
    calc _ ≤ 4 * ((D.card : ℝ) * M ^ 4) := h2
      _ ≤ 4 * (81 * M ^ 4) := by gcongr
      _ ≤ _ := by nlinarith
  have hc := Real.sum_mul_le_sqrt_mul_sqrt (innerBonds D m) (fun b => f b.1 b.2) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at hc
  have hs : Real.sqrt ((innerBonds D m).card : ℝ) ≤ 25 * M ^ 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, hcard⟩
  have e : weightedScaleNorm D p 0 2 m f = Real.sqrt (∑ b ∈ innerBonds D m, f b.1 b.2 ^ 2) := by
    unfold weightedScaleNorm
    rw [finsetLpNorm_two_eq_sqrt]
    simp only [scaleWeight_zero_angle, one_mul]
  rw [e]
  calc _ ≤ Real.sqrt (∑ b ∈ innerBonds D m, f b.1 b.2 ^ 2) * Real.sqrt ((innerBonds D m).card : ℝ) := hc
    _ ≤ Real.sqrt (∑ b ∈ innerBonds D m, f b.1 b.2 ^ 2) * (25 * M ^ 2) :=
        mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    _ = _ := by ring
theorem weightedScaleNorm_two_bondHullSum_le (hodd : Odd F.blockSide) {D : Finset F.Cell} (hD : D.card ≤ 81)
    (p : F.Site 0) {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {m : ℕ} (hm : m < F.top) {g : F.Site m → Fin 4 → ℝ}
    (hg : ∀ x d, 0 ≤ g x d) {Y : ℝ} (hY : weightedScaleNorm D p θ 4 m g ≤ Y) :
    weightedScaleNorm D p θ 2 (m + 1) (fun y d => bondHullSum (y, d) g) ≤
      5 * (F.blockSide : ℝ) ^ (F.top - (m + 1)) * (hullFactor F.blockSide * Y) := by
  refine (_root_.YangMills.Construction.RealDirections.weightedScaleNorm_two_le_four hodd hD p θ (m + 1) _).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact (weightedScaleNorm_bondHullSum_le hodd hθ hm p 4 (by norm_num) hg).trans
    (mul_le_mul_of_nonneg_left hY (hullFactor_nonneg hodd))
def levelSecondConst (L : ℕ) : ℝ := 2 * (142 * 8256 + 284 * secondSourceConst L)
def lowerMainConst (L : ℕ) : ℝ :=
  24769 + 13 * (hullFactor L * levelSecondConst L) +
    800 * (200000 * (L : ℝ) ^ 2) * (hullFactor L * 82272) ^ 2 + 10 * (hullFactor L * 82272)
theorem cube_scale_bounds {l M c₀ : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hM : l * M = 1) (hc0 : 0 ≤ c₀)
    (hc1 : c₀ ≤ 1) :
    c₀ * l ^ 3 ≤ c₀ * l ∧ (c₀ * l ^ 3) * M ≤ c₀ * l ∧ (c₀ * l ^ 3) ^ 2 * M ^ 2 ≤ c₀ * l := by
  have h2 : l ^ 2 ≤ 1 := pow_le_one₀ hl0 hl1
  have h3 : l ^ 3 ≤ l := by nlinarith
  have e1 : (c₀ * l ^ 3) * M = c₀ * l ^ 2 * (l * M) := by ring
  have e2 : (c₀ * l ^ 3) ^ 2 * M ^ 2 = c₀ ^ 2 * l ^ 4 * (l * M) ^ 2 := by ring
  refine ⟨mul_le_mul_of_nonneg_left h3 hc0, ?_, ?_⟩
  · rw [e1, hM, mul_one]
    exact mul_le_mul_of_nonneg_left (by nlinarith) hc0
  · rw [e2, hM]
    have h4 : c₀ ^ 2 ≤ c₀ := by nlinarith
    have h5 : l ^ 4 ≤ l := by nlinarith [pow_le_one₀ hl0 hl1 (n := 3), pow_nonneg hl0 3]
    calc c₀ ^ 2 * l ^ 4 * 1 ^ 2 = c₀ ^ 2 * l ^ 4 := by ring
      _ ≤ c₀ * l := mul_le_mul h4 h5 (by positivity) hc0
theorem main_sum_bound {κ K S₁ S₂ S₃ S₄ S₅ M B₁ B₂ G Hh cl : ℝ} (hκ : 0 ≤ κ) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hG : 0 ≤ G) (hHh : 0 ≤ Hh)
    (h1 : S₁ ≤ B₁ * B₂) (h2 : S₂ ≤ 25 * M ^ 2 * (Hh * (B₁ * B₂)))
    (h3 : S₃ ≤ (5 * M * (G * B₁)) * (5 * M * (G * B₂))) (h4 : S₄ ≤ B₁ * (5 * M * (G * B₂)))
    (h5 : S₅ ≤ (5 * M * (G * B₁)) * B₂) (c1 : κ ≤ cl) (c2 : κ * M ≤ cl) (c3 : κ ^ 2 * M ^ 2 ≤ cl) :
    24769 * κ * S₁ + κ ^ 2 / 2 * S₂ + 32 * K * κ ^ 2 * S₃ + κ * S₄ + κ * S₅ ≤
      cl * ((24769 + 13 * Hh + 800 * K * G ^ 2 + 10 * G) * (B₁ * B₂)) := by
  set x := B₁ * B₂ with hx
  have hx0 : 0 ≤ x := by positivity
  have a1 : 24769 * κ * S₁ ≤ 24769 * cl * x := by
    have := mul_le_mul h1 c1 hκ hx0
    nlinarith
  have a2 : κ ^ 2 / 2 * S₂ ≤ 13 * cl * (Hh * x) := by
    have hq : 0 ≤ Hh * x := by positivity
    have s1 : κ ^ 2 / 2 * S₂ ≤ κ ^ 2 / 2 * (25 * M ^ 2 * (Hh * x)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have s2 := mul_le_mul_of_nonneg_right c3 hq
    have hcl : 0 ≤ cl := hκ.trans c1
    have s3 : 0 ≤ cl * (Hh * x) := by positivity
    nlinarith
  have a3 : 32 * K * κ ^ 2 * S₃ ≤ 800 * K * cl * (G ^ 2 * x) := by
    have hq : 0 ≤ K * (G ^ 2 * x) := by positivity
    have s1 : 32 * K * κ ^ 2 * S₃ ≤ 32 * K * κ ^ 2 * ((5 * M * (G * B₁)) * (5 * M * (G * B₂))) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have e : 32 * K * κ ^ 2 * ((5 * M * (G * B₁)) * (5 * M * (G * B₂))) =
        800 * (κ ^ 2 * M ^ 2) * (K * (G ^ 2 * x)) := by
      rw [hx]
      ring
    rw [e] at s1
    have s2 := mul_le_mul_of_nonneg_right c3 hq
    nlinarith
  have a4 : κ * S₄ ≤ 5 * cl * (G * x) := by
    have hq : 0 ≤ G * x := by positivity
    have s1 : κ * S₄ ≤ κ * (B₁ * (5 * M * (G * B₂))) := mul_le_mul_of_nonneg_left h4 hκ
    have e : κ * (B₁ * (5 * M * (G * B₂))) = 5 * (κ * M) * (G * x) := by
      rw [hx]
      ring
    rw [e] at s1
    have s2 := mul_le_mul_of_nonneg_right c2 hq
    nlinarith
  have a5 : κ * S₅ ≤ 5 * cl * (G * x) := by
    have hq : 0 ≤ G * x := by positivity
    have s1 : κ * S₅ ≤ κ * ((5 * M * (G * B₁)) * B₂) := mul_le_mul_of_nonneg_left h5 hκ
    have e : κ * ((5 * M * (G * B₁)) * B₂) = 5 * (κ * M) * (G * x) := by
      rw [hx]
      ring
    rw [e] at s1
    have s2 := mul_le_mul_of_nonneg_right c2 hq
    nlinarith
  have e : cl * ((24769 + 13 * Hh + 800 * K * G ^ 2 + 10 * G) * x) =
      24769 * cl * x + 13 * cl * (Hh * x) + 800 * K * cl * (G ^ 2 * x) + 5 * cl * (G * x) +
        5 * cl * (G * x) := by ring
  rw [e]
  linarith
def bondHullField {m : ℕ} (y : F.Site m → Fin 4 → ComplexQuat) : F.Site (m + 1) → Fin 4 → ℝ :=
  fun b d => bondHullNorm (b, d) y
def coarseNorm (W : ChainChart F) (m : ℕ) : F.Site (m + 1) → Fin 4 → ℝ :=
  fun b d => ‖(W.coarse m b d : ℍ[ℝ])‖
theorem bondHullField_nonneg {m : ℕ} (y : F.Site m → Fin 4 → ComplexQuat) (b : F.Site (m + 1)) (d : Fin 4) :
    0 ≤ bondHullField y b d :=
  bondHullNorm_nonneg' _ _
theorem coarseNorm_nonneg (W : ChainChart F) (m : ℕ) (b : F.Site (m + 1)) (d : Fin 4) :
    0 ≤ coarseNorm W m b d :=
  norm_nonneg _
def bondMainPart (κ K q₁ q₂ n₁ n₂ n₁₃ n₂₃ nΔ : ℝ) : ℝ :=
  24769 * κ * (q₁ * q₂) + κ ^ 2 / 2 * nΔ + 32 * K * κ ^ 2 * (n₁ * n₂) + κ * (q₁ * n₁₃) + κ * (n₂₃ * q₂)
theorem bondMainPart_nonneg {κ K q₁ q₂ n₁ n₂ n₁₃ n₂₃ nΔ : ℝ} (hκ : 0 ≤ κ) (hK : 0 ≤ K) (h1 : 0 ≤ q₁)
    (h2 : 0 ≤ q₂) (h3 : 0 ≤ n₁) (h4 : 0 ≤ n₂) (h5 : 0 ≤ n₁₃) (h6 : 0 ≤ n₂₃) (h7 : 0 ≤ nΔ) :
    0 ≤ bondMainPart κ K q₁ q₂ n₁ n₂ n₁₃ n₂₃ nΔ := by
  unfold bondMainPart
  positivity
theorem inv_pow_bounds {L : ℝ} (hL1 : 1 ≤ L) (e : ℕ) :
    0 ≤ (1 / L) ^ e ∧ (1 / L) ^ e ≤ 1 ∧ (1 / L) ^ e * L ^ e = 1 :=
  ⟨by positivity, pow_le_one₀ (by positivity) (by rw [one_div]; exact inv_le_one_of_one_le₀ hL1),
    inv_pow_mul_pow_eq_one hL1 e⟩
set_option maxHeartbeats 2000000 in
theorem abs_bondSecondDiff_le (hodd : Odd F.blockSide) {D : Finset F.Cell} {p : F.Site 0} {θ : ℝ}
    {R : F.FieldChain} {W₁ W₂ W₃ : ChainChart F} {C₀ s T B₁ B₂ : ℝ} (V : F.GaugeField F.top)
    (ref : ReferenceNear D R C₀ s) (dir : SmallDirectionTriple D p θ R W₁ W₂ W₃ C₀ s T B₁ B₂) {m : ℕ}
    (hm : m + 1 < F.top) {c : F.Site (m + 1) × Fin 4} (hc : c ∈ innerBonds D (m + 1)) :
    |bondEnergy R W₃ V m c - bondEnergy R W₁ V m c - bondEnergy R W₂ V m c +
        bondEnergy R (zeroChart F) V m c - inner ℝ (W₁.coarse m c.1 c.2 : ℍ[ℝ]) (W₂.coarse m c.1 c.2 : ℍ[ℝ])| ≤
      bondMainPart (C₀ * s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (m + 1))) ^ 3)
        (200000 * (F.blockSide : ℝ) ^ 2)
        (coarseNorm W₁ m c.1 c.2) (coarseNorm W₂ m c.1 c.2)
        (bondHullField (levelDeviation R (realChart W₁) m) c.1 c.2)
        (bondHullField (levelDeviation R (realChart W₂) m) c.1 c.2)
        (bondHullField (levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₁) m) c.1 c.2)
        (bondHullField (levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₂) m) c.1 c.2)
        (bondHullField (levelDeviation R (realChart W₃) m -
          (levelDeviation R (realChart W₁) m + levelDeviation R (realChart W₂) m)) c.1 c.2) +
      lowerCubicConst F.blockSide * T ^ 3 := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hC := dir.C₀_pos
  have hs := dir.s_pos
  have hT0 := dir.T_nonneg
  have hT4 := dir.T_le
  have hT1 : T ≤ 1 := by linarith
  have hc64 := dir.spread_le
  obtain ⟨hl0, hl1, -⟩ := inv_pow_bounds hL1 (F.top - (m + 1))
  set K := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set l := (1 / (F.blockSide : ℝ)) ^ (F.top - (m + 1)) with hl
  have hc00 : 0 ≤ C₀ * s := by positivity
  have hκ1 : C₀ * s * l ^ 3 ≤ 1 := by
    have : l ^ 3 ≤ 1 := pow_le_one₀ hl0 hl1
    have : C₀ * s * l ^ 3 ≤ C₀ * s * 1 := mul_le_mul_of_nonneg_left this hc00
    linarith
  have hσ0 : 0 < contourSpread F C₀ s m := by
    have : 0 < (1 / (F.blockSide : ℝ)) ^ (F.top - (m + 1)) := by positivity
    simp only [contourSpread]
    positivity
  have hσc : contourSpread F C₀ s m ≤ C₀ * s := contourSpread_le hodd hC.le hs.le m
  have hσ64 : contourSpread F C₀ s m ≤ 1 / 64 := hσc.trans hc64
  have hrad : 24 * (2 * T + contourSpread F C₀ s m) < hullBallRadius F.blockSide := by
    have := dir.radius
    linarith
  have hLp1 : 12 * K * (2 * T + contourSpread F C₀ s m) ≤ 1 := by
    refine le_trans ?_ dir.lip
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hmn : m < F.top := by omega
  have a1 := dir.hull₁ m hmn c hc
  have a2 := dir.hull₂ m hmn c hc
  have a3 := dir.hull₃ m hmn c hc
  have a13 := dir.hull₁₃ m hmn c hc
  have a23 := dir.hull₂₃ m hmn c hc
  have m1 := dir.coarse₁ m hm c hc
  have m2 := dir.coarse₂ m hm c hc
  have hlen := ref.length m hmn c hc
  have hdef := ref.defect m hm c hc
  have n₃0 : 0 ≤ bondHullNorm c (levelDeviation R (realChart W₃) m) := bondHullNorm_nonneg' _ _
  have hR6 : K * (bondHullNorm c (levelDeviation R (realChart W₃) m) ^ 2 +
      contourSpread F C₀ s m * bondHullNorm c (levelDeviation R (realChart W₃) m)) ≤ 2 * K * T := by
    generalize bondHullNorm c (levelDeviation R (realChart W₃) m) = n₃ at a3 n₃0 ⊢
    have b1 : n₃ ^ 2 ≤ T := by nlinarith
    have b2 : contourSpread F C₀ s m * n₃ ≤ T := by nlinarith
    have := mul_le_mul_of_nonneg_left (add_le_add b1 b2) hK0
    linarith
  have hlip' : K * (2 * T) ≤ 1 / 12 := by
    have := dir.lip
    have h0 : 0 ≤ K * (C₀ * s) := by positivity
    nlinarith
  have key := abs_bondEnergy_secondDifference_sub_inner_le_of_lt_top hodd (W₁ := W₁) (W₂ := W₂) (W₃ := W₃)
    (c := c) (σ := contourSpread F C₀ s m) (t := T) V hm hσ0
    hσ64 (ref.contours m hm.le c hc) hT0 hrad a1 a2 (by linarith) (by linarith) (by linarith)
    (dir.coarse₃ m hm c hc) (hlen.trans hκ1) (by linarith)
  refine key.trans ?_
  have hdef0 := norm_nonneg (((referenceDefect R m c : UnitQuaternion) : ℍ[ℝ]) - 1)
  have hLp0 : 0 ≤ 12 * K * (2 * T + contourSpread F C₀ s m) := by positivity
  have hR0 : 0 ≤ K * (bondHullNorm c (levelDeviation R (realChart W₃) m) ^ 2 +
      contourSpread F C₀ s m * bondHullNorm c (levelDeviation R (realChart W₃) m)) := by positivity
  have hR6' : K * (bondHullNorm c (levelDeviation R (realChart W₃) m) ^ 2 +
      contourSpread F C₀ s m * bondHullNorm c (levelDeviation R (realChart W₃) m)) ≤ 6 * K * T := by
    have : 0 ≤ K * T := by positivity
    linarith
  exact bond_bound_split (abs_nonneg _) hdef0 (by positivity) hlen hdef rfl hLp0 hLp1
    (bondHullNorm_nonneg' _ _) hK0
    (bondHullNorm_nonneg' _ _) (bondHullNorm_nonneg' _ _) (bondHullNorm_nonneg' _ _) (bondHullNorm_nonneg' _ _)
    (norm_nonneg _) (norm_nonneg _) a13 a23 m1 m2 hR0 hR6' hT1
set_option maxHeartbeats 2000000 in
theorem sum_bondMainPart_le (hodd : Odd F.blockSide) {D : Finset F.Cell} (hD : D.card ≤ 81) {p : F.Site 0}
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {W₁ W₂ W₃ : ChainChart F} {C₀ s T B₁ B₂ : ℝ}
    (dir : SmallDirectionTriple D p θ R W₁ W₂ W₃ C₀ s T B₁ B₂) {m : ℕ} (hm : m + 1 < F.top) :
    ∑ c ∈ innerBonds D (m + 1), bondMainPart (C₀ * s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (m + 1))) ^ 3)
        (200000 * (F.blockSide : ℝ) ^ 2)
        (coarseNorm W₁ m c.1 c.2) (coarseNorm W₂ m c.1 c.2)
        (bondHullField (levelDeviation R (realChart W₁) m) c.1 c.2)
        (bondHullField (levelDeviation R (realChart W₂) m) c.1 c.2)
        (bondHullField (levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₁) m) c.1 c.2)
        (bondHullField (levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₂) m) c.1 c.2)
        (bondHullField (levelDeviation R (realChart W₃) m -
          (levelDeviation R (realChart W₁) m + levelDeviation R (realChart W₂) m)) c.1 c.2) ≤
      C₀ * s * (1 / (F.blockSide : ℝ)) ^ (F.top - (m + 1)) * (lowerMainConst F.blockSide * (B₁ * B₂)) := by
  have hθ' : |(-θ)| ≤ 1 / 8 := by rwa [abs_neg]
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hC := dir.C₀_pos
  have hs := dir.s_pos
  have hB₁ := dir.B₁_nonneg
  have hB₂ := dir.B₂_nonneg
  have hc64 := dir.spread_le
  have hF0 := hullFactor_nonneg (F := F) hodd
  obtain ⟨hl0, hl1, hlM⟩ := inv_pow_bounds hL1 (F.top - (m + 1))
  set l := (1 / (F.blockSide : ℝ)) ^ (F.top - (m + 1)) with hl
  set M := (F.blockSide : ℝ) ^ (F.top - (m + 1)) with hM
  have hM0 : 0 ≤ M := by positivity
  have hK0 : 0 ≤ 200000 * (F.blockSide : ℝ) ^ 2 := by positivity
  have hc00 : 0 ≤ C₀ * s := by positivity
  have hκ0 : 0 ≤ C₀ * s * l ^ 3 := by positivity
  have hmn : m < F.top := by omega
  have hlev₁ : weightedScaleNorm D p θ 2 (m + 1) (coarseNorm W₁ m) ≤ B₁ := dir.level₁ m hm
  have hlev₂ : weightedScaleNorm D p (-θ) 2 (m + 1) (coarseNorm W₂ m) ≤ B₂ := dir.level₂ m hm
  have S1 : ∑ c ∈ innerBonds D (m + 1), coarseNorm W₁ m c.1 c.2 * coarseNorm W₂ m c.1 c.2 ≤ B₁ * B₂ :=
    (sum_mul_le_weightedScaleNorm hodd D p θ (m + 1) _ _).trans
      (mul_le_mul hlev₁ hlev₂ (weightedScaleNorm_nonneg' _ _ _ _ _ _) hB₁)
  have hn1 : weightedScaleNorm D p θ 2 (m + 1) (bondHullField (levelDeviation R (realChart W₁) m)) ≤
      5 * M * (hullFactor F.blockSide * (82272 * B₁)) :=
    weightedScaleNorm_two_bondHullSum_le hodd hD p hθ hmn
      (g := fun z d => ‖levelDeviation R (realChart W₁) m z d‖) (fun _ _ => norm_nonneg _) (dir.dev₁ m hmn)
  have hn2 : weightedScaleNorm D p (-θ) 2 (m + 1) (bondHullField (levelDeviation R (realChart W₂) m)) ≤
      5 * M * (hullFactor F.blockSide * (82272 * B₂)) :=
    weightedScaleNorm_two_bondHullSum_le hodd hD p hθ' hmn
      (g := fun z d => ‖levelDeviation R (realChart W₂) m z d‖) (fun _ _ => norm_nonneg _) (dir.dev₂ m hmn)
  have hn13 : weightedScaleNorm D p (-θ) 2 (m + 1)
      (bondHullField (levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₁) m)) ≤
      5 * M * (hullFactor F.blockSide * (82272 * B₂)) :=
    weightedScaleNorm_two_bondHullSum_le hodd hD p hθ' hmn
      (g := fun z d => ‖(levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₁) m) z d‖)
      (fun _ _ => norm_nonneg _) (dir.dev₁₃ m hmn)
  have hn23 : weightedScaleNorm D p θ 2 (m + 1)
      (bondHullField (levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₂) m)) ≤
      5 * M * (hullFactor F.blockSide * (82272 * B₁)) :=
    weightedScaleNorm_two_bondHullSum_le hodd hD p hθ hmn
      (g := fun z d => ‖(levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₂) m) z d‖)
      (fun _ _ => norm_nonneg _) (dir.dev₂₃ m hmn)
  have hG1 : 0 ≤ 5 * M * (hullFactor F.blockSide * (82272 * B₁)) := by positivity
  have e1 : hullFactor F.blockSide * 82272 * B₁ = hullFactor F.blockSide * (82272 * B₁) := by ring
  have e2 : hullFactor F.blockSide * 82272 * B₂ = hullFactor F.blockSide * (82272 * B₂) := by ring
  have S3 : ∑ c ∈ innerBonds D (m + 1), bondHullField (levelDeviation R (realChart W₁) m) c.1 c.2 *
      bondHullField (levelDeviation R (realChart W₂) m) c.1 c.2 ≤
      (5 * M * (hullFactor F.blockSide * 82272 * B₁)) * (5 * M * (hullFactor F.blockSide * 82272 * B₂)) := by
    rw [e1, e2]
    exact (sum_mul_le_weightedScaleNorm hodd D p θ (m + 1) _ _).trans
      (mul_le_mul hn1 hn2 (weightedScaleNorm_nonneg' _ _ _ _ _ _) hG1)
  have S4 : ∑ c ∈ innerBonds D (m + 1), coarseNorm W₁ m c.1 c.2 *
      bondHullField (levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₁) m) c.1 c.2 ≤
      B₁ * (5 * M * (hullFactor F.blockSide * 82272 * B₂)) := by
    rw [e2]
    exact (sum_mul_le_weightedScaleNorm hodd D p θ (m + 1) _ _).trans
      (mul_le_mul hlev₁ hn13 (weightedScaleNorm_nonneg' _ _ _ _ _ _) hB₁)
  have S5 : ∑ c ∈ innerBonds D (m + 1),
      bondHullField (levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₂) m) c.1 c.2 *
      coarseNorm W₂ m c.1 c.2 ≤ (5 * M * (hullFactor F.blockSide * 82272 * B₁)) * B₂ := by
    rw [e1]
    exact (sum_mul_le_weightedScaleNorm hodd D p θ (m + 1) _ _).trans
      (mul_le_mul hn23 hlev₂ (weightedScaleNorm_nonneg' _ _ _ _ _ _) hG1)
  have S2 : ∑ c ∈ innerBonds D (m + 1),
      bondHullField (levelDeviation R (realChart W₃) m -
        (levelDeviation R (realChart W₁) m + levelDeviation R (realChart W₂) m)) c.1 c.2 ≤
      25 * M ^ 2 * (hullFactor F.blockSide * levelSecondConst F.blockSide * (B₁ * B₂)) := by
    refine (sum_le_weightedScaleNorm_zero hodd hD p (m + 1) _).trans
      (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have h0 : |(0 : ℝ)| ≤ 1 / 8 := by norm_num
    refine (weightedScaleNorm_bondHullSum_le hodd h0 hmn p 2 (by norm_num) (g := fun z d =>
      ‖(levelDeviation R (realChart W₃) m -
        (levelDeviation R (realChart W₁) m + levelDeviation R (realChart W₂) m)) z d‖)
      (fun _ _ => norm_nonneg _)).trans ?_
    have := mul_le_mul_of_nonneg_left (dir.second m hmn) hF0
    rw [mul_assoc (hullFactor F.blockSide)]
    exact this
  obtain ⟨c1, c2, c3⟩ := cube_scale_bounds hl0 hl1 hlM hc00 (by linarith)
  have hsl : 0 ≤ levelSecondConst F.blockSide := by
    unfold levelSecondConst secondSourceConst
    positivity
  have fin := main_sum_bound (κ := C₀ * s * l ^ 3) (K := 200000 * (F.blockSide : ℝ) ^ 2) (M := M)
    (G := hullFactor F.blockSide * 82272) (Hh := hullFactor F.blockSide * levelSecondConst F.blockSide)
    (cl := C₀ * s * l) hκ0 hK0 hM0 hB₁ hB₂ (by positivity) (by positivity) S1 S2 S3 S4 S5 c1 c2 c3
  have e : ∑ c ∈ innerBonds D (m + 1), bondMainPart (C₀ * s * l ^ 3) (200000 * (F.blockSide : ℝ) ^ 2)
        (coarseNorm W₁ m c.1 c.2) (coarseNorm W₂ m c.1 c.2)
        (bondHullField (levelDeviation R (realChart W₁) m) c.1 c.2)
        (bondHullField (levelDeviation R (realChart W₂) m) c.1 c.2)
        (bondHullField (levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₁) m) c.1 c.2)
        (bondHullField (levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₂) m) c.1 c.2)
        (bondHullField (levelDeviation R (realChart W₃) m -
          (levelDeviation R (realChart W₁) m + levelDeviation R (realChart W₂) m)) c.1 c.2) =
      24769 * (C₀ * s * l ^ 3) * ∑ c ∈ innerBonds D (m + 1), coarseNorm W₁ m c.1 c.2 * coarseNorm W₂ m c.1 c.2 +
      (C₀ * s * l ^ 3) ^ 2 / 2 * ∑ c ∈ innerBonds D (m + 1),
        bondHullField (levelDeviation R (realChart W₃) m -
          (levelDeviation R (realChart W₁) m + levelDeviation R (realChart W₂) m)) c.1 c.2 +
      32 * (200000 * (F.blockSide : ℝ) ^ 2) * (C₀ * s * l ^ 3) ^ 2 * ∑ c ∈ innerBonds D (m + 1),
        bondHullField (levelDeviation R (realChart W₁) m) c.1 c.2 *
          bondHullField (levelDeviation R (realChart W₂) m) c.1 c.2 +
      (C₀ * s * l ^ 3) * ∑ c ∈ innerBonds D (m + 1), coarseNorm W₁ m c.1 c.2 *
        bondHullField (levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₁) m) c.1 c.2 +
      (C₀ * s * l ^ 3) * ∑ c ∈ innerBonds D (m + 1),
        bondHullField (levelDeviation R (realChart W₃) m - levelDeviation R (realChart W₂) m) c.1 c.2 *
          coarseNorm W₂ m c.1 c.2 := by
    simp only [bondMainPart, Finset.sum_add_distrib, Finset.mul_sum]
  rw [e]
  refine fin.trans (le_of_eq ?_)
  simp only [lowerMainConst]
theorem sum_abs_bondSecondDiff_le (hodd : Odd F.blockSide) {D : Finset F.Cell} (hD : D.card ≤ 81)
    {p : F.Site 0} {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {W₁ W₂ W₃ : ChainChart F}
    {C₀ s T B₁ B₂ : ℝ} (V : F.GaugeField F.top) (ref : ReferenceNear D R C₀ s)
    (dir : SmallDirectionTriple D p θ R W₁ W₂ W₃ C₀ s T B₁ B₂) {m : ℕ} (hm : m + 1 < F.top)
    {Bj : Finset (F.Site (m + 1) × Fin 4)} (hBj : Bj ⊆ innerBonds D (m + 1)) :
    ∑ c ∈ Bj, |bondEnergy R W₃ V m c - bondEnergy R W₁ V m c - bondEnergy R W₂ V m c +
        bondEnergy R (zeroChart F) V m c - inner ℝ (W₁.coarse m c.1 c.2 : ℍ[ℝ]) (W₂.coarse m c.1 c.2 : ℍ[ℝ])| ≤
      C₀ * s * (1 / (F.blockSide : ℝ)) ^ (F.top - (m + 1)) * (lowerMainConst F.blockSide * (B₁ * B₂)) +
        (Bj.card : ℝ) * (lowerCubicConst F.blockSide * T ^ 3) := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hC := dir.C₀_pos
  have hs := dir.s_pos
  have hκ0 : 0 ≤ C₀ * s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (m + 1))) ^ 3 := by positivity
  have hK0 : (0 : ℝ) ≤ 200000 * (F.blockSide : ℝ) ^ 2 := by positivity
  refine (Finset.sum_le_sum fun c hc => abs_bondSecondDiff_le hodd V ref dir hm (hBj hc)).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  refine add_le_add_left (le_trans (Finset.sum_le_sum_of_subset_of_nonneg hBj fun c _ _ => ?_)
    (sum_bondMainPart_le hodd hD hθ dir hm)) _
  exact bondMainPart_nonneg hκ0 hK0 (coarseNorm_nonneg _ _ _ _) (coarseNorm_nonneg _ _ _ _)
    (bondHullField_nonneg _ _ _) (bondHullField_nonneg _ _ _) (bondHullField_nonneg _ _ _)
    (bondHullField_nonneg _ _ _) (bondHullField_nonneg _ _ _)
end YangMills.Construction.LowerLevelTerms
end

import YangMills.Construction.ColdChainAtEveryLevel.ComplexBondTerms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.ComplexCells
open BlockAverages ComplexLevels ComplexRemainders ComplexDifferences LevelRecursion HullBounds ComplexBondTerms
variable {F : BlockFrame} {j : ℕ}
theorem complexFieldChain_top_eq (R : F.FieldChain) (W W' : ComplexChainChart F) (V : F.GaugeField F.top) {k : ℕ}
    (hk : k = F.top) :
    complexFieldChain R W V k = complexFieldChain R W' V k := by
  subst hk
  simp [complexFieldChain]
theorem norm_ofUnit (g : UnitQuaternion) : ‖ofUnit g‖ = 1 := by
  have := norm_ofUnit_mul g 1
  rw [mul_one, CStarRing.norm_one] at this
  exact this
theorem norm_complexFieldChain_top (R : F.FieldChain) (W : ComplexChainChart F) (V : F.GaugeField F.top) {k : ℕ}
    (hk : k = F.top) (y : F.Site k) (i : Fin 4) : ‖complexFieldChain R W V k y i‖ = 1 := by
  subst hk
  simp [complexFieldChain, complexifyField, norm_ofUnit]
theorem complexBondTerm_top_eq (hodd : Odd F.blockSide) (hj : j + 1 = F.top) (R : F.FieldChain)
    (W : ComplexChainChart F) (V : F.GaugeField F.top) {c : F.Site (j + 1) × Fin 4}
    (hd : HoldsOnHull c (fun b i => (complexChartField R W j b i).det = 1)) :
    complexBondTerm R W V j c =
      topBlockFit (R j) c (complexFieldChain R W V (j + 1) c.1 c.2) (levelDeviation R W j) := by
  have h1 := complexFieldChain_of_ne R W V (k := j) (by omega)
  have e1 := complexGaugedContourAverage_eq_liftedBondMean hodd hj.le (X := complexChartField R W j) (R := R j) hd
  simp only [complexBondTerm, h1, complexBalancingGauges, topBlockFit]
  rw [e1]
  rfl
theorem norm_complexBondTerm_second_diff_le_top (hodd : Odd F.blockSide) (hj : j + 1 = F.top) (R : F.FieldChain)
    (W₀ W₁ W₂ W₃ : ComplexChainChart F)
    (V : F.GaugeField F.top) {c : F.Site (j + 1) × Fin 4} {σ ε t : ℝ} (hσ : σ ≤ 1 / 64) (hε0 : 0 < ε)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy (R j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ)
    (hε : 3 * (ε + σ) < hullBallRadius F.blockSide) (hK : 200000 * (F.blockSide : ℝ) ^ 2 * (ε + σ) ≤ 1)
    (ht : 0 ≤ t) (htε : 3 * t ≤ ε / 48)
    (h0 : bondHullNorm c (levelDeviation R W₀ j) ≤ t) (h1 : bondHullNorm c (levelDeviation R W₁ j) ≤ t)
    (h2 : bondHullNorm c (levelDeviation R W₂ j) ≤ t) (h3 : bondHullNorm c (levelDeviation R W₃ j) ≤ t)
    (hn1 : bondHullNorm c (levelDeviation R W₁ j - levelDeviation R W₀ j) ≤ t)
    (hn2 : bondHullNorm c (levelDeviation R W₂ j - levelDeviation R W₀ j) ≤ t)
    (hd0 : HoldsOnHull c (fun b i => (complexChartField R W₀ j b i).det = 1))
    (hd1 : HoldsOnHull c (fun b i => (complexChartField R W₁ j b i).det = 1))
    (hd2 : HoldsOnHull c (fun b i => (complexChartField R W₂ j b i).det = 1))
    (hd3 : HoldsOnHull c (fun b i => (complexChartField R W₃ j b i).det = 1)) :
    ‖complexBondTerm R W₃ V j c - complexBondTerm R W₁ V j c - complexBondTerm R W₂ V j c +
        complexBondTerm R W₀ V j c‖ ≤
      240 * bondHullNorm c (levelDeviation R W₃ j - levelDeviation R W₁ j - levelDeviation R W₂ j +
          levelDeviation R W₀ j) +
        30720 / ε * bondHullNorm c (levelDeviation R W₁ j - levelDeviation R W₀ j) *
          bondHullNorm c (levelDeviation R W₂ j - levelDeviation R W₀ j) := by
  set X' := complexFieldChain R W₀ V (j + 1) c.1 c.2 with hX'
  have hXn : ‖X'‖ ≤ 2 := by
    rw [hX', norm_complexFieldChain_top R W₀ V hj]
    norm_num
  have eX : ∀ W : ComplexChainChart F, complexFieldChain R W V (j + 1) c.1 c.2 = X' := fun W => by
    rw [hX', complexFieldChain_top_eq R W W₀ V hj]
  rw [complexBondTerm_top_eq hodd hj R W₃ V hd3, complexBondTerm_top_eq hodd hj R W₁ V hd1,
    complexBondTerm_top_eq hodd hj R W₂ V hd2, complexBondTerm_top_eq hodd hj R W₀ V hd0, eX, eX, eX, eX]
  set x₀ := levelDeviation R W₀ j with hx₀
  set x₁ := levelDeviation R W₁ j with hx₁
  set x₂ := levelDeviation R W₂ j with hx₂
  set x₃ := levelDeviation R W₃ j with hx₃
  set δ₁ := x₁ - x₀ with hδ₁
  set δ₂ := x₂ - x₀ with hδ₂
  set Δ := x₃ - x₁ - x₂ + x₀ with hΔ
  have hq := topBlockFitRemainder_quadraticBound hodd hj.le hσ hε0 href hε hK hXn
  have hK0 : 0 ≤ 480 / ε := by positivity
  have hσt : 0 < ε / 48 := by positivity
  set yt := x₀ + δ₁ + δ₂ with hyt
  have hNyt : bondHullNorm c yt ≤ 3 * t := by
    have u1 := bondHullNorm_add_le c (x₀ + δ₁) δ₂
    have u2 := bondHullNorm_add_le c x₀ δ₁
    linarith
  have hsm : 3 * (3 * t + ε / 48) < ε := by linarith
  have a3 := hq.norm_sub_le hK0 hσt (t := 3 * t) (by linarith) hsm hNyt (y' := x₃) (by linarith)
  have e1 : x₃ - yt = Δ := by
    rw [hyt, hδ₁, hδ₂, hΔ]
    abel
  rw [e1] at a3
  have a4 := hq.norm_second_diff_le hK0 hσt (by linarith) (y := x₀) (e₁ := δ₁) (e₂ := δ₂) ht (by linarith) h0 hn1 hn2
  have e2 : x₀ + δ₁ = x₁ := by rw [hδ₁]; abel
  have e3 : x₀ + δ₂ = x₂ := by rw [hδ₂]; abel
  have e6 : x₁ + δ₂ = yt := by rw [← e2]
  rw [e2, e3, e6] at a4
  have hh0 : 0 ≤ bondHullNorm c Δ := bondHullSum_nonneg c fun _ _ => norm_nonneg _
  have c1 : 12 * (480 / ε) * (3 * t + ε / 48) ≤ 240 := by
    have : 3 * t + ε / 48 ≤ ε / 24 := by linarith
    have e : 12 * (480 / ε) * (ε / 24) = 240 := by
      field_simp
      norm_num
    calc _ ≤ 12 * (480 / ε) * (ε / 24) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 240 := e
  have c2 : 12 * (480 / ε) * (3 * t + ε / 48) * bondHullNorm c Δ ≤ 240 * bondHullNorm c Δ :=
    mul_le_mul_of_nonneg_right c1 hh0
  have c3 : 64 * (480 / ε) = 30720 / ε := by ring
  rw [c3] at a4
  have e4 : topBlockFit (R j) c X' x₃ - topBlockFit (R j) c X' x₁ - topBlockFit (R j) c X' x₂ +
        topBlockFit (R j) c X' x₀ =
      (topBlockFitRemainder (R j) c X' x₃ - topBlockFitRemainder (R j) c X' yt) +
        (topBlockFitRemainder (R j) c X' yt - topBlockFitRemainder (R j) c X' x₁ -
          topBlockFitRemainder (R j) c X' x₂ + topBlockFitRemainder (R j) c X' x₀) := by
    simp only [topBlockFitRemainder]
    ring
  rw [e4]
  exact (norm_add_le _ _).trans (add_le_add (a3.trans c2) a4)
theorem abs_le_finsetLpNorm {ι : Type} {P : ℕ} (hP : 1 ≤ P) {s : Finset ι} (f : ι → ℝ) {i : ι} (hi : i ∈ s) :
    |f i| ≤ finsetLpNorm P s f := by
  have h1 : |f i| ^ P ≤ ∑ k ∈ s, |f k| ^ P :=
    Finset.single_le_sum (f := fun k => |f k| ^ P) (fun _ _ => by positivity) hi
  have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : 0 ≤ 1 / (P : ℝ))
  have e : (|f i| ^ P) ^ (1 / (P : ℝ)) = |f i| := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    field_simp
    simp
  rwa [e] at h2
theorem scaleWeight_mul_scaleWeight_neg (hodd : Odd F.blockSide) (p : F.Site 0) (θ : ℝ) (m : ℕ) (x : F.Site m) :
    scaleWeight p θ m x * scaleWeight p (-θ) m x = 1 := by
  have hρ := WeightedAverages.Chains.scaleRadius_pos (F := F) hodd.pos m p x
  simp only [scaleWeight, neg_neg]
  rw [← Real.rpow_add hρ]
  simp
section Sums
def lowerBonds (D : Finset F.Cell) : Finset (Σ m : ℕ, F.Site (m + 1) × Fin 4) :=
  (Finset.range (F.top - 1)).sigma fun m => innerBonds D (m + 1)
theorem sum_mul_le_finsetLpNorm_two_mul {ι : Type} (s : Finset ι) (f g : ι → ℝ) :
    ∑ i ∈ s, f i * g i ≤ finsetLpNorm 2 s f * finsetLpNorm 2 s g := by
  rw [finsetLpNorm_two_eq_sqrt, finsetLpNorm_two_eq_sqrt,
    ← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => by positivity)]
  exact Real.le_sqrt_of_sq_le (Finset.sum_mul_sq_le_sq_mul_sq s f g)
structure FourDeviationBalls (R : F.FieldChain) (D : Finset F.Cell) (W₀ W₁ W₂ W₃ : ComplexChainChart F)
    (C₀ s η B : ℝ) : Prop where
  near : ContoursNearUnit R D C₀ s
  ball₀ : DeviationBall R D W₀ η B
  ball₁ : DeviationBall R D W₁ η B
  ball₂ : DeviationBall R D W₂ η B
  ball₃ : DeviationBall R D W₃ η B
  const_pos : 0 < C₀
  scale_pos : 0 < s
  radius_nonneg : 0 ≤ η
  nine_radius_le_one : 9 * η ≤ 1
  spread_le : C₀ * s ≤ 1 / 64
  lt_hullBallRadius : 24 * (6 * (hullBondCount F.blockSide * η) + C₀ * s) < hullBallRadius F.blockSide
  lipschitz_small : 12 * (200000 * (F.blockSide : ℝ) ^ 2) * (6 * (hullBondCount F.blockSide * η) + C₀ * s) ≤ 1
  hull_radius_small : 8 * (hullBondCount F.blockSide * η) ≤ 1
def deviationFirstDiff (R : F.FieldChain) (W W' : ComplexChainChart F) (m : ℕ) : F.Site m → Fin 4 → ℝ :=
  fun z d => ‖(levelDeviation R W' m - levelDeviation R W m) z d‖
def deviationSecondDiff (R : F.FieldChain) (W₀ W₁ W₂ W₃ : ComplexChainChart F) (m : ℕ) :
    F.Site m → Fin 4 → ℝ :=
  fun z d => ‖(levelDeviation R W₃ m - levelDeviation R W₁ m - levelDeviation R W₂ m + levelDeviation R W₀ m) z d‖
theorem hullBondCount_nonneg (L : ℕ) : 0 ≤ hullBondCount L := by
  unfold hullBondCount
  positivity
theorem hullFactor_nonneg (L : ℕ) : 0 ≤ hullFactor L := by
  unfold hullFactor
  have := hullBondCount_nonneg L
  positivity
theorem FourDeviationBalls.bondHullNorm_sub_le {R : F.FieldChain} {D : Finset F.Cell} {η B : ℝ}
    {W W' : ComplexChainChart F}
    (hW : DeviationBall R D W η B) (hW' : DeviationBall R D W' η B) (hodd : Odd F.blockSide) (hη0 : 0 ≤ η) {m : ℕ}
    (hm : m < F.top) {c : F.Site (m + 1) × Fin 4} (hc : c ∈ innerBonds D (m + 1)) :
    bondHullNorm c (levelDeviation R W' m - levelDeviation R W m) ≤ 2 * (hullBondCount F.blockSide * η) := by
  have h7 : HoldsOnHull c (fun x i => ‖(levelDeviation R W' m - levelDeviation R W m) x i‖ ≤ 2 * η) :=
    holdsOnHull_of_innerBonds hm hodd hc (fun b hb => by
      have q1 := hW.norm_deviation_le m hm b hb
      have q2 := hW'.norm_deviation_le m hm b hb
      have q3 := norm_sub_le (levelDeviation R W' m b.1 b.2) (levelDeviation R W m b.1 b.2)
      show ‖levelDeviation R W' m b.1 b.2 - levelDeviation R W m b.1 b.2‖ ≤ 2 * η
      linarith)
  have := bondHullSum_le hodd (mul_nonneg (by norm_num) hη0) h7
  refine this.trans (le_of_eq ?_)
  ring
theorem FourDeviationBalls.bondHullNorm_second_diff_le {R : F.FieldChain} {D : Finset F.Cell}
    {W₀ W₁ W₂ W₃ : ComplexChainChart F} {C₀ s η B : ℝ}
    (h : FourDeviationBalls R D W₀ W₁ W₂ W₃ C₀ s η B) (hodd : Odd F.blockSide) {m : ℕ} (hm : m < F.top)
    {c : F.Site (m + 1) × Fin 4} (hc : c ∈ innerBonds D (m + 1)) :
    bondHullNorm c (levelDeviation R W₃ m - levelDeviation R W₁ m - levelDeviation R W₂ m + levelDeviation R W₀ m) ≤
      4 * (hullBondCount F.blockSide * η) := by
  have h7 : HoldsOnHull c (fun x i => ‖(levelDeviation R W₃ m - levelDeviation R W₁ m - levelDeviation R W₂ m +
      levelDeviation R W₀ m) x i‖ ≤ 4 * η) :=
    holdsOnHull_of_innerBonds hm hodd hc (fun b hb => by
      have q0 := h.ball₀.norm_deviation_le m hm b hb
      have q1 := h.ball₁.norm_deviation_le m hm b hb
      have q2 := h.ball₂.norm_deviation_le m hm b hb
      have q3 := h.ball₃.norm_deviation_le m hm b hb
      show ‖levelDeviation R W₃ m b.1 b.2 - levelDeviation R W₁ m b.1 b.2 - levelDeviation R W₂ m b.1 b.2 +
        levelDeviation R W₀ m b.1 b.2‖ ≤ 4 * η
      have u1 := norm_add_le (levelDeviation R W₃ m b.1 b.2 - levelDeviation R W₁ m b.1 b.2 -
        levelDeviation R W₂ m b.1 b.2) (levelDeviation R W₀ m b.1 b.2)
      have u2 := norm_sub_le (levelDeviation R W₃ m b.1 b.2 - levelDeviation R W₁ m b.1 b.2)
        (levelDeviation R W₂ m b.1 b.2)
      have u3 := norm_sub_le (levelDeviation R W₃ m b.1 b.2) (levelDeviation R W₁ m b.1 b.2)
      linarith)
  have := bondHullSum_le hodd (mul_nonneg (by norm_num) h.radius_nonneg) h7
  refine this.trans (le_of_eq ?_)
  ring
theorem FourDeviationBalls.norm_complexBondTerm_second_diff_le {R : F.FieldChain} {D : Finset F.Cell}
    {W₀ W₁ W₂ W₃ : ComplexChainChart F} {C₀ s η B : ℝ}
    (h : FourDeviationBalls R D W₀ W₁ W₂ W₃ C₀ s η B) (hodd : Odd F.blockSide) (V : F.GaugeField F.top) {m : ℕ}
    (hm : m + 1 < F.top) {c : F.Site (m + 1) × Fin 4} (hc : c ∈ innerBonds D (m + 1)) {dm : ℝ}
    (hdm : bondHullNorm c (levelDeviation R W₃ m - levelDeviation R W₁ m - levelDeviation R W₂ m +
        levelDeviation R W₀ m) +
      64 * (200000 * (F.blockSide : ℝ) ^ 2) * bondHullNorm c (levelDeviation R W₁ m - levelDeviation R W₀ m) *
        bondHullNorm c (levelDeviation R W₂ m - levelDeviation R W₀ m) ≤ dm) :
    ‖complexBondTerm R W₃ V m c - complexBondTerm R W₁ V m c - complexBondTerm R W₂ V m c +
        complexBondTerm R W₀ V m c‖ ≤
      5 * (‖levelSource W₁ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ *
            ‖levelSource W₂ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ +
          ‖levelSource W₃ m c.1 c.2 - levelSource W₁ m c.1 c.2 - levelSource W₂ m c.1 c.2 +
              levelSource W₀ m c.1 c.2‖ *
            (‖levelSource W₀ m c.1 c.2 * ofUnit (referenceDefect R m c) - 1‖ +
              ‖levelSource W₁ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ +
              ‖levelSource W₂ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ +
              ‖levelSource W₃ m c.1 c.2 - levelSource W₁ m c.1 c.2 - levelSource W₂ m c.1 c.2 +
                levelSource W₀ m c.1 c.2‖)) +
        2 * dm *
          (‖levelSource W₀ m c.1 c.2 * ofUnit (referenceDefect R m c) - 1‖ +
            ‖levelSource W₁ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ +
            ‖levelSource W₂ m c.1 c.2 - levelSource W₀ m c.1 c.2‖) ^ 2 +
        (bondHullNorm c (levelDeviation R W₁ m - levelDeviation R W₀ m) *
            ‖levelSource W₂ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ +
          bondHullNorm c (levelDeviation R W₂ m - levelDeviation R W₀ m) *
            ‖levelSource W₁ m c.1 c.2 - levelSource W₀ m c.1 c.2‖) *
          (‖levelSource W₀ m c.1 c.2 * ofUnit (referenceDefect R m c) - 1‖ +
            ‖levelSource W₁ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ +
            ‖levelSource W₂ m c.1 c.2 - levelSource W₀ m c.1 c.2‖) := by
  have hm' : m < F.top := by omega
  have hL : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hH0 := hullBondCount_nonneg F.blockSide
  have hη0 := h.radius_nonneg
  set H := hullBondCount F.blockSide with hH
  have hHη : 0 ≤ H * η := mul_nonneg hH0 hη0
  set t := 2 * (H * η) with ht
  have ht0 : 0 ≤ t := mul_nonneg (by norm_num) hHη
  set σ := contourSpread F C₀ s m with hσd
  have hσ0 : 0 < σ := by
    have := h.const_pos
    have := h.scale_pos
    rw [hσd]
    unfold contourSpread
    positivity
  have hσle : σ ≤ C₀ * s := contourSpread_le hodd h.const_pos.le h.scale_pos.le m
  have hσ64 : σ ≤ 1 / 64 := hσle.trans h.spread_le
  have e3t : 3 * t = 6 * (H * η) := by
    rw [ht]
    ring
  have hsm : 24 * (3 * t + σ) < hullBallRadius F.blockSide := by
    have := h.lt_hullBallRadius
    rw [e3t]
    linarith
  set K := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hLip : 12 * K * (3 * t + σ) ≤ 1 := by
    have h1 := h.lipschitz_small
    rw [e3t]
    have : 12 * K * (6 * (H * η) + σ) ≤ 12 * K * (6 * (H * η) + C₀ * s) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hN : ∀ {W : ComplexChainChart F}, DeviationBall R D W η B → bondHullNorm c (levelDeviation R W m) ≤ t := by
    intro W hW
    have := hW.bondHullNorm_le hodd hη0 hm' hc
    rw [ht]
    linarith
  have hη : η < 1 := by
    have := h.nine_radius_le_one
    linarith
  have hn1 := FourDeviationBalls.bondHullNorm_sub_le h.ball₀ h.ball₁ hodd hη0 hm' hc
  have hn2 := FourDeviationBalls.bondHullNorm_sub_le h.ball₀ h.ball₂ hodd hη0 hm' hc
  have hΔ := h.bondHullNorm_second_diff_le hodd hm' hc
  set n₁ := bondHullNorm c (levelDeviation R W₁ m - levelDeviation R W₀ m) with hn₁d
  set n₂ := bondHullNorm c (levelDeviation R W₂ m - levelDeviation R W₀ m) with hn₂d
  set hh := bondHullNorm c (levelDeviation R W₃ m - levelDeviation R W₁ m - levelDeviation R W₂ m +
    levelDeviation R W₀ m) with hhd
  have hn₂0 : 0 ≤ n₂ := bondHullSum_nonneg c fun _ _ => norm_nonneg _
  have hh0 : 0 ≤ hh := bondHullSum_nonneg c fun _ _ => norm_nonneg _
  have ht8 := h.hull_radius_small
  rw [← hH] at ht8
  have hLh : 12 * K * (3 * t + σ) * hh ≤ hh := by
    have := mul_le_mul_of_nonneg_right hLip hh0
    linarith
  have hKt : K * t ≤ 1 / 36 := by
    have h1 : 12 * K * (3 * t) ≤ 12 * K * (3 * t + σ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : 12 * K * (3 * t) = 36 * (K * t) := by ring
    linarith
  have hnn : n₁ * n₂ ≤ t * t := mul_le_mul hn1 hn2 hn₂0 ht0
  have hKnn : 64 * K * n₁ * n₂ ≤ 2 * t := by
    have e : 64 * K * n₁ * n₂ = 64 * K * (n₁ * n₂) := by ring
    rw [e]
    have h1 : 64 * K * (n₁ * n₂) ≤ 64 * K * (t * t) := mul_le_mul_of_nonneg_left hnn (by positivity)
    have h2 : 64 * (K * t) * t ≤ 64 * (1 / 36) * t := mul_le_mul_of_nonneg_right (by linarith) ht0
    linarith
  have hdr : 12 * K * (3 * t + σ) * hh + 64 * K * n₁ * n₂ ≤ 1 := by
    have : t ≤ 1 / 4 := by
      rw [ht]
      linarith
    linarith
  have hb := ComplexBondTerms.norm_complexBondTerm_second_diff_le hodd hm R W₀ W₁ W₂ W₃ V (t := t) hσ0 hσ64
    (h.near m (by omega) c hc) ht0 hsm hLip
    (hN h.ball₀) (hN h.ball₁) (hN h.ball₂) (hN h.ball₃) hn1 hn2
    (h.ball₀.det_eq_one hodd hη hm' hc) (h.ball₁.det_eq_one hodd hη hm' hc) (h.ball₂.det_eq_one hodd hη hm' hc)
    (h.ball₃.det_eq_one hodd hη hm' hc) hdr
  refine hb.trans ?_
  have hdm' : 12 * K * (3 * t + σ) * hh + 64 * K * n₁ * n₂ ≤ dm := by linarith
  gcongr
end Sums
section LowerSum
theorem scaleWeight_mul_bondHullSum_le {D : Finset F.Cell} (hodd : Odd F.blockSide) {θ : ℝ} (hθ : |θ| ≤ 1 / 8)
    {m : ℕ} (hm : m < F.top)
    (p : F.Site 0) (P : ℕ) (hP : 1 ≤ P) {g : F.Site m → Fin 4 → ℝ} (hg : ∀ x d, 0 ≤ g x d) {T : ℝ}
    (hT : weightedScaleNorm D p θ P m g ≤ T) {c : F.Site (m + 1) × Fin 4} (hc : c ∈ innerBonds D (m + 1)) :
    scaleWeight p θ (m + 1) c.1 * bondHullSum c g ≤ hullFactor F.blockSide * T := by
  have h1 := weightedScaleNorm_bondHullSum_le (D := D) hodd hθ hm p P hP hg
  have h2 := abs_le_finsetLpNorm hP (s := innerBonds D (m + 1))
    (fun b => scaleWeight p θ (m + 1) b.1 * bondHullSum (b.1, b.2) g) hc
  have h3 : weightedScaleNorm D p θ P (m + 1) (fun y d => bondHullSum (y, d) g) =
      finsetLpNorm P (innerBonds D (m + 1)) (fun b => scaleWeight p θ (m + 1) b.1 * bondHullSum (b.1, b.2) g) := rfl
  rw [h3] at h1
  exact (le_abs_self _).trans (h2.trans (h1.trans (mul_le_mul_of_nonneg_left hT (hullFactor_nonneg _))))
theorem sum_sq_eq_finsetLpNorm_two_sq {ι : Type} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, f i ^ 2 = finsetLpNorm 2 s f ^ 2 := by
  rw [finsetLpNorm_two_eq_sqrt, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
theorem mem_lowerBonds {D : Finset F.Cell} {x : Σ m : ℕ, F.Site (m + 1) × Fin 4} (hx : x ∈ lowerBonds D) :
    x.1 + 1 < F.top ∧ x.2 ∈ innerBonds D (x.1 + 1) := by
  obtain ⟨h1, h2⟩ := Finset.mem_sigma.1 hx
  have := Finset.mem_range.1 h1
  exact ⟨by omega, h2⟩
set_option maxHeartbeats 2000000 in
theorem sum_norm_complexBondTerm_second_diff_le {R : F.FieldChain} {D : Finset F.Cell}
    {W₀ W₁ W₂ W₃ : ComplexChainChart F} {C₀ s η B : ℝ}
    (h : FourDeviationBalls R D W₀ W₁ W₂ W₃ C₀ s η B) (hodd : Odd F.blockSide) (V : F.GaugeField F.top) {θ : ℝ}
    (hθ : |θ| ≤ 1 / 8)
    (p : F.Site 0) {T₁ T₂ T₁₂ A₁ A₂ Y : ℝ} (hT₁0 : 0 ≤ T₁) (hT₂0 : 0 ≤ T₂) (hT₁₂0 : 0 ≤ T₁₂)
    (hA₁0 : 0 ≤ A₁) (hA₂0 : 0 ≤ A₂) (hY0 : 0 ≤ Y)
    (hT₁ : ∀ m, m < F.top → weightedScaleNorm D p θ 4 m (deviationFirstDiff R W₀ W₁ m) ≤ T₁)
    (hT₂ : ∀ m, m < F.top → weightedScaleNorm D p (-θ) 4 m (deviationFirstDiff R W₀ W₂ m) ≤ T₂)
    (hT₁₂ : ∀ m, m < F.top → weightedScaleNorm D p 0 2 m (deviationSecondDiff R W₀ W₁ W₂ W₃ m) ≤ T₁₂)
    (a₁ a₂ : (Σ m : ℕ, F.Site (m + 1) × Fin 4) → ℝ) (ha₁ : ∀ x, 0 ≤ a₁ x) (ha₂ : ∀ x, 0 ≤ a₂ x)
    (he₁ : ∀ x ∈ lowerBonds D, ‖levelSource W₁ x.1 x.2.1 x.2.2 - levelSource W₀ x.1 x.2.1 x.2.2‖ ≤ 2 * a₁ x)
    (he₂ : ∀ x ∈ lowerBonds D, ‖levelSource W₂ x.1 x.2.1 x.2.2 - levelSource W₀ x.1 x.2.1 x.2.2‖ ≤ 2 * a₂ x)
    (hdd : ∀ x ∈ lowerBonds D, ‖levelSource W₃ x.1 x.2.1 x.2.2 - levelSource W₁ x.1 x.2.1 x.2.2 -
      levelSource W₂ x.1 x.2.1 x.2.2 + levelSource W₀ x.1 x.2.1 x.2.2‖ ≤ 8256 * a₁ x * a₂ x)
    (yy : (Σ m : ℕ, F.Site (m + 1) × Fin 4) → ℝ)
    (hyy : ∀ x ∈ lowerBonds D, yy x = ‖levelSource W₀ x.1 x.2.1 x.2.2 * ofUnit (referenceDefect R x.1 x.2) - 1‖ +
      ‖levelSource W₁ x.1 x.2.1 x.2.2 - levelSource W₀ x.1 x.2.1 x.2.2‖ +
      ‖levelSource W₂ x.1 x.2.1 x.2.2 - levelSource W₀ x.1 x.2.1 x.2.2‖)
    (hy1 : ∀ x ∈ lowerBonds D, yy x + ‖levelSource W₃ x.1 x.2.1 x.2.2 - levelSource W₁ x.1 x.2.1 x.2.2 -
      levelSource W₂ x.1 x.2.1 x.2.2 + levelSource W₀ x.1 x.2.1 x.2.2‖ ≤ 1)
    (hA₁ : finsetLpNorm 2 (lowerBonds D) (fun x => scaleWeight p θ (x.1 + 1) x.2.1 * a₁ x) ≤ A₁)
    (hA₂ : finsetLpNorm 2 (lowerBonds D) (fun x => scaleWeight p (-θ) (x.1 + 1) x.2.1 * a₂ x) ≤ A₂)
    (hY : finsetLpNorm 2 (lowerBonds D) yy ≤ Y) :
    ∑ x ∈ lowerBonds D, ‖complexBondTerm R W₃ V x.1 x.2 - complexBondTerm R W₁ V x.1 x.2 -
        complexBondTerm R W₂ V x.1 x.2 + complexBondTerm R W₀ V x.1 x.2‖ ≤
      41300 * (A₁ * A₂) +
        2 * (hullFactor F.blockSide * T₁₂ + 64 * (200000 * (F.blockSide : ℝ) ^ 2) *
            (hullFactor F.blockSide * T₁ * (hullFactor F.blockSide * T₂))) * Y ^ 2 +
        2 * (hullFactor F.blockSide * T₁) * (A₂ * Y) + 2 * (hullFactor F.blockSide * T₂) * (A₁ * Y) := by
  have hK0 : 0 ≤ 200000 * (F.blockSide : ℝ) ^ 2 := by positivity
  have hF0 := hullFactor_nonneg F.blockSide
  set K₁ := hullFactor F.blockSide * T₁ with hK₁
  set K₂ := hullFactor F.blockSide * T₂ with hK₂
  have hK₁0 : 0 ≤ K₁ := mul_nonneg hF0 hT₁0
  have hK₂0 : 0 ≤ K₂ := mul_nonneg hF0 hT₂0
  set dm := hullFactor F.blockSide * T₁₂ + 64 * (200000 * (F.blockSide : ℝ) ^ 2) * (K₁ * K₂) with hdm
  have hdm0 : 0 ≤ dm := add_nonneg (mul_nonneg hF0 hT₁₂0)
    (mul_nonneg (mul_nonneg (by norm_num) hK0) (mul_nonneg hK₁0 hK₂0))
  set v : (Σ m : ℕ, F.Site (m + 1) × Fin 4) → ℝ := fun x => scaleWeight p θ (x.1 + 1) x.2.1 with hv
  set v' : (Σ m : ℕ, F.Site (m + 1) × Fin 4) → ℝ := fun x => scaleWeight p (-θ) (x.1 + 1) x.2.1 with hv'
  have hθ' : |(-θ)| ≤ 1 / 8 := by rwa [abs_neg]
  have hpt : ∀ x ∈ lowerBonds D, ‖complexBondTerm R W₃ V x.1 x.2 - complexBondTerm R W₁ V x.1 x.2 -
      complexBondTerm R W₂ V x.1 x.2 + complexBondTerm R W₀ V x.1 x.2‖ ≤
        41300 * ((v x * a₁ x) * (v' x * a₂ x)) + 2 * dm * yy x ^ 2 +
        2 * K₁ * ((v' x * a₂ x) * yy x) + 2 * K₂ * ((v x * a₁ x) * yy x) := by
    intro x hx
    obtain ⟨hxn, hxb⟩ := mem_lowerBonds hx
    have hm' : x.1 < F.top := by omega
    have hvv : v x * v' x = 1 := scaleWeight_mul_scaleWeight_neg hodd p θ (x.1 + 1) x.2.1
    have hvp : 0 < v x := scaleWeight_pos hodd p θ _ _
    have hvp' : 0 < v' x := scaleWeight_pos hodd p (-θ) _ _
    have q1 : v x * bondHullSum x.2 (deviationFirstDiff R W₀ W₁ x.1) ≤ K₁ :=
      scaleWeight_mul_bondHullSum_le hodd hθ hm' p 4 (by norm_num) (fun _ _ => norm_nonneg _) (hT₁ x.1 hm') hxb
    have q2 : v' x * bondHullSum x.2 (deviationFirstDiff R W₀ W₂ x.1) ≤ K₂ :=
      scaleWeight_mul_bondHullSum_le hodd hθ' hm' p 4 (by norm_num) (fun _ _ => norm_nonneg _) (hT₂ x.1 hm') hxb
    have q3 : scaleWeight p 0 (x.1 + 1) x.2.1 * bondHullSum x.2 (deviationSecondDiff R W₀ W₁ W₂ W₃ x.1) ≤
        hullFactor F.blockSide * T₁₂ :=
      scaleWeight_mul_bondHullSum_le hodd (θ := 0) (by norm_num) hm' p 2 (by norm_num) (fun _ _ => norm_nonneg _)
        (hT₁₂ x.1 hm') hxb
    have e0 : scaleWeight p 0 (x.1 + 1) x.2.1 = 1 := by simp [scaleWeight]
    rw [e0, one_mul] at q3
    set n₁ := bondHullSum x.2 (deviationFirstDiff R W₀ W₁ x.1) with hn₁
    set n₂ := bondHullSum x.2 (deviationFirstDiff R W₀ W₂ x.1) with hn₂
    set hh := bondHullSum x.2 (deviationSecondDiff R W₀ W₁ W₂ W₃ x.1) with hhh
    have hn₂0 : 0 ≤ n₂ := bondHullSum_nonneg _ fun _ _ => norm_nonneg _
    have hnn : n₁ * n₂ ≤ K₁ * K₂ := by
      have e : n₁ * n₂ = (v x * n₁) * (v' x * n₂) := by
        calc n₁ * n₂ = (v x * v' x) * (n₁ * n₂) := by rw [hvv, one_mul]
          _ = _ := by ring
      rw [e]
      exact mul_le_mul q1 q2 (mul_nonneg hvp'.le hn₂0) hK₁0
    have hdmx : hh + 64 * (200000 * (F.blockSide : ℝ) ^ 2) * n₁ * n₂ ≤ dm := by
      have e : 64 * (200000 * (F.blockSide : ℝ) ^ 2) * n₁ * n₂ =
          64 * (200000 * (F.blockSide : ℝ) ^ 2) * (n₁ * n₂) := by ring
      rw [e, hdm]
      have := mul_le_mul_of_nonneg_left hnn (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) hK0)
      linarith
    have hb := h.norm_complexBondTerm_second_diff_le hodd V hxn hxb hdmx
    refine hb.trans ?_
    have hye := hyy x hx
    rw [← hye]
    set e₁ := ‖levelSource W₁ x.1 x.2.1 x.2.2 - levelSource W₀ x.1 x.2.1 x.2.2‖ with he₁d
    set e₂ := ‖levelSource W₂ x.1 x.2.1 x.2.2 - levelSource W₀ x.1 x.2.1 x.2.2‖ with he₂d
    set dd := ‖levelSource W₃ x.1 x.2.1 x.2.2 - levelSource W₁ x.1 x.2.1 x.2.2 - levelSource W₂ x.1 x.2.1 x.2.2 +
      levelSource W₀ x.1 x.2.1 x.2.2‖ with hddd
    have he₁x := he₁ x hx
    have he₂x := he₂ x hx
    have hddx := hdd x hx
    have hy1x := hy1 x hx
    have hy0 : 0 ≤ yy x := by
      rw [hye]
      exact add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    have hdd0 : 0 ≤ dd := norm_nonneg _
    have hee : e₁ * e₂ ≤ 4 * ((v x * a₁ x) * (v' x * a₂ x)) := by
      have h1 : e₁ * e₂ ≤ (2 * a₁ x) * (2 * a₂ x) :=
        mul_le_mul he₁x he₂x (norm_nonneg _) (mul_nonneg (by norm_num) (ha₁ x))
      have e : 4 * ((v x * a₁ x) * (v' x * a₂ x)) = 4 * ((v x * v' x) * (a₁ x * a₂ x)) := by ring
      rw [e, hvv]
      linarith
    have hdy : dd * (yy x + dd) ≤ 8256 * ((v x * a₁ x) * (v' x * a₂ x)) := by
      have h1 : dd * (yy x + dd) ≤ dd * 1 := mul_le_mul_of_nonneg_left hy1x hdd0
      have e : 8256 * ((v x * a₁ x) * (v' x * a₂ x)) = 8256 * ((v x * v' x) * (a₁ x * a₂ x)) := by ring
      rw [e, hvv]
      linarith
    have hne : n₁ * e₂ ≤ 2 * K₁ * (v' x * a₂ x) := by
      have e : n₁ * e₂ = (v x * n₁) * (v' x * e₂) := by
        calc n₁ * e₂ = (v x * v' x) * (n₁ * e₂) := by rw [hvv, one_mul]
          _ = _ := by ring
      rw [e]
      have h1 : v' x * e₂ ≤ v' x * (2 * a₂ x) := mul_le_mul_of_nonneg_left he₂x hvp'.le
      have h2 := mul_le_mul q1 h1 (mul_nonneg hvp'.le (norm_nonneg _)) hK₁0
      refine h2.trans (le_of_eq ?_)
      ring
    have hne2 : n₂ * e₁ ≤ 2 * K₂ * (v x * a₁ x) := by
      have e : n₂ * e₁ = (v' x * n₂) * (v x * e₁) := by
        calc n₂ * e₁ = (v x * v' x) * (n₂ * e₁) := by rw [hvv, one_mul]
          _ = _ := by ring
      rw [e]
      have h1 : v x * e₁ ≤ v x * (2 * a₁ x) := mul_le_mul_of_nonneg_left he₁x hvp.le
      have h2 := mul_le_mul q2 h1 (mul_nonneg hvp.le (norm_nonneg _)) hK₂0
      refine h2.trans (le_of_eq ?_)
      ring
    have hfin : (n₁ * e₂ + n₂ * e₁) * yy x ≤ (2 * K₁ * (v' x * a₂ x) + 2 * K₂ * (v x * a₁ x)) * yy x :=
      mul_le_mul_of_nonneg_right (by linarith) hy0
    have e8 : (2 * K₁ * (v' x * a₂ x) + 2 * K₂ * (v x * a₁ x)) * yy x =
        2 * K₁ * ((v' x * a₂ x) * yy x) + 2 * K₂ * ((v x * a₁ x) * yy x) := by ring
    rw [e8] at hfin
    have e7 : bondHullNorm x.2 (levelDeviation R W₁ x.1 - levelDeviation R W₀ x.1) = n₁ := rfl
    have e9 : bondHullNorm x.2 (levelDeviation R W₂ x.1 - levelDeviation R W₀ x.1) = n₂ := rfl
    rw [e7, e9]
    linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have s1 := sum_mul_le_finsetLpNorm_two_mul (lowerBonds D) (fun x => v x * a₁ x) (fun x => v' x * a₂ x)
  have s2 := sum_mul_le_finsetLpNorm_two_mul (lowerBonds D) (fun x => v' x * a₂ x) yy
  have s3 := sum_mul_le_finsetLpNorm_two_mul (lowerBonds D) (fun x => v x * a₁ x) yy
  have s4 := sum_sq_eq_finsetLpNorm_two_sq (lowerBonds D) yy
  have n2 := finsetLpNorm_nonneg 2 (lowerBonds D) (fun x => v' x * a₂ x)
  have n3 := finsetLpNorm_nonneg 2 (lowerBonds D) yy
  have c1 : finsetLpNorm 2 (lowerBonds D) (fun x => v x * a₁ x) *
      finsetLpNorm 2 (lowerBonds D) (fun x => v' x * a₂ x) ≤ A₁ * A₂ :=
    mul_le_mul hA₁ hA₂ n2 hA₁0
  have c2 : finsetLpNorm 2 (lowerBonds D) (fun x => v' x * a₂ x) * finsetLpNorm 2 (lowerBonds D) yy ≤ A₂ * Y :=
    mul_le_mul hA₂ hY n3 hA₂0
  have c3 : finsetLpNorm 2 (lowerBonds D) (fun x => v x * a₁ x) * finsetLpNorm 2 (lowerBonds D) yy ≤ A₁ * Y :=
    mul_le_mul hA₁ hY n3 hA₁0
  have c4 : finsetLpNorm 2 (lowerBonds D) yy ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ n3 hY 2
  have d2 := mul_le_mul_of_nonneg_left (s4.le.trans c4) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hdm0)
  have d3 := mul_le_mul_of_nonneg_left (s2.trans c2) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK₁0)
  have d4 := mul_le_mul_of_nonneg_left (s3.trans c3) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK₂0)
  linarith
end LowerSum
end YangMills.Construction.ComplexCells
end

import YangMills.Construction.ColdChainAtEveryLevel.CellBound
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.CellNormBounds
open BlockAverages BlockLines ComplexLevels ComplexCells ComplexDifferences CellSources CellBounds LevelRecursion
  ComplexPlaquettes PlaquettesNearCell HullBounds ComplexifiedQuaternions
variable {F : BlockFrame}
theorem le_localNorm_of_sq {S : Finset F.Cell} {R : F.FieldChain} {U : ChainChart F} {w : F.SiteWeights}
    {z : F.Cell} {x : ℝ} (h : x ^ 2 ≤ localNormSq S (cellBall S z 3) R U w) : x ≤ localNorm S R U w z :=
  Real.le_sqrt_of_sq_le h
theorem finsetLpNorm_fine_le_localNorm (hL : Odd F.blockSide) (S : Finset F.Cell) (z : F.Cell) (R : F.FieldChain)
    (U : ChainChart F) (w : F.SiteWeights) :
    finsetLpNorm 4 (innerBonds (cellBall S z 1) 0) (fun b => w 0 b.1 * ‖U.fine b.1 b.2‖) ≤ localNorm S R U w z := by
  refine le_localNorm_of_sq ?_
  rw [finsetLpNorm_four_eq_sqrt_sqrt, Real.sq_sqrt (Real.sqrt_nonneg _)]
  unfold localNormSq
  have h1 : ∑ b ∈ innerBonds (cellBall S z 1) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤
      ∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => mem_bondsOver_of_mem_innerBonds_cellBall hL S z 0 hb)
      fun _ _ _ => by positivity
  have h2 := Real.sqrt_le_sqrt h1
  have h3 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have h4 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  linarith
theorem finsetLpNorm_coarse_le_localNorm (hL : Odd F.blockSide) (S : Finset F.Cell) (z : F.Cell)
    (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) : finsetLpNorm 2 (lowerBonds (cellBall S z 1))
      (fun x => w (x.1 + 1) x.2.1 * ‖U.coarse x.1 x.2.1 x.2.2‖) ≤ localNorm S R U w z := by
  refine le_localNorm_of_sq ?_
  rw [finsetLpNorm_two_eq_sqrt, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  unfold localNormSq
  have h1 : ∑ x ∈ lowerBonds (cellBall S z 1), (w (x.1 + 1) x.2.1 * ‖U.coarse x.1 x.2.1 x.2.2‖) ^ 2 ≤
      ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
    rw [lowerBonds, Finset.sum_sigma]
    exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum_of_subset_of_nonneg
      (fun b hb => mem_bondsOver_of_mem_innerBonds_cellBall hL S z (j + 1) hb) fun _ _ _ => by positivity
  have h3 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have h4 : 0 ≤ Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) :=
    Real.sqrt_nonneg _
  linarith
theorem finsetLpNorm_curl_le_localNorm (hL : Odd F.blockSide) (S : Finset F.Cell) (z : F.Cell)
    (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    finsetLpNorm 2 (plaquettesOver S {z} 0) (fun q => w 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ≤
      localNorm S R U w z := by
  classical
  refine le_localNorm_of_sq ?_
  rw [finsetLpNorm_two_eq_sqrt, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  unfold localNormSq
  have h1 : ∑ q ∈ plaquettesOver S {z} 0, (w 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 ≤
      ∑ q ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun _ _ _ => by positivity
    obtain ⟨hqS, hc⟩ := Finset.mem_filter.1 hq
    have hcz : enclosingCell q.1 = z := Finset.mem_singleton.1 hc
    refine Finset.mem_filter.2 ⟨hqS, ?_⟩
    rw [hcz]
    have hq1 : q.1 ∈ sitesOfCells S 0 := (Finset.mem_product.1 (Finset.mem_filter.1 hqS).1).1
    have hzS : z ∈ S := hcz ▸ BlockLines.enclosingCell_mem hL hq1
    exact Finset.mem_filter.2 ⟨hzS, by rw [BlockLines.cellSupDist_self]; omega⟩
  have h3 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have h4 : 0 ≤ Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) :=
    Real.sqrt_nonneg _
  linarith
section Const
theorem finsetLpNorm_const_le {ι : Type} (s : Finset ι) {a Cn : ℝ} (ha : 0 ≤ a) (hCn : 0 ≤ Cn) {P : ℕ}
    (hP : 1 ≤ P) (hcard : (s.card : ℝ) ≤ Cn ^ P) : finsetLpNorm P s (fun _ => a) ≤ Cn * a := by
  have h1 := finsetLpNorm_le_of_sum_pow_le (P := P) hP s ({()} : Finset Unit) (fun _ => a) (fun _ => (1 : ℝ))
    (C := Cn * a) (mul_nonneg hCn ha) (by
      simp only [Finset.sum_const, nsmul_eq_mul, abs_one, one_pow, mul_one]
      rw [abs_of_nonneg ha, mul_pow]
      have c1 : ((({()} : Finset Unit).card : ℕ) : ℝ) = 1 := by simp
      rw [c1, mul_one]
      exact mul_le_mul_of_nonneg_right hcard (pow_nonneg ha P))
  have h2 : finsetLpNorm P ({()} : Finset Unit) (fun _ => (1 : ℝ)) = 1 := by
    simp [finsetLpNorm]
  rw [h2, mul_one] at h1
  exact h1
theorem card_plaquettesOver_singleton_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (S : Finset F.Cell) (z : F.Cell) :
    ((plaquettesOver S {z} 0).card : ℝ) ≤ 1296 * ((F.blockSide : ℝ) ^ F.top) ^ 4 := by
  classical
  have h1 : (plaquettesOver S {z} 0).card ≤
      (sitesOfCells (cellBall S z 1) 0 ×ˢ (Finset.univ : Finset (Fin 4 × Fin 4))).card := by
    refine Finset.card_le_card fun q hq => ?_
    have hb := (plaquette_bonds_mem_innerBonds hamb hodd hq).1
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hb
    exact Finset.mem_product.2 ⟨hb.1, Finset.mem_univ _⟩
  rw [Finset.card_product, Finset.card_univ] at h1
  have h2 := card_sitesOfCells_le hodd (cellBall S z 1) 0
  have h3 := card_cellBall_one_le S z
  have h4 : (sitesOfCells (cellBall S z 1) 0).card ≤ 81 * (F.blockSide ^ (F.top - 0)) ^ 4 :=
    h2.trans (Nat.mul_le_mul_right _ h3)
  have h5 : (plaquettesOver S {z} 0).card ≤ 81 * (F.blockSide ^ F.top) ^ 4 * 16 := by
    simpa using h1.trans (Nat.mul_le_mul_right _ h4)
  have h6 : ((plaquettesOver S {z} 0).card : ℝ) ≤ ((81 * (F.blockSide ^ F.top) ^ 4 * 16 : ℕ) : ℝ) := by
    exact_mod_cast h5
  push_cast at h6
  linarith
end Const
section Near
structure SourceBounds (S : Finset F.Cell) (z : F.Cell) (R : F.FieldChain) (W : ComplexChainChart F) (B₀ : ℝ) :
    Prop where
  base_le : finsetLpNorm 4 (innerBonds (cellBall S z 1) 0) (fun b => ‖baseSource W b.1 b.2‖) ≤ B₀
  upper_le : finsetLpNorm 2 (lowerBonds (cellBall S z 1)) (fun x => ‖upperSource W x‖) ≤ B₀
  curl_le : finsetLpNorm 2 (plaquettesOver S {z} 0) (fun q => ‖covariantCurl (R 0) q (baseSource W)‖) ≤ B₀
theorem weightedScaleNorm_zero_baseSourceDiff_le {D : Finset F.Cell} (p : F.Site 0) {W W' : ComplexChainChart F}
    {B₀ : ℝ} (h : finsetLpNorm 4 (innerBonds D 0) (fun b => ‖baseSource W b.1 b.2‖) ≤ B₀)
    (h' : finsetLpNorm 4 (innerBonds D 0) (fun b => ‖baseSource W' b.1 b.2‖) ≤ B₀) :
    weightedScaleNorm D p 0 4 0 (fun x i => ‖baseSourceDiff W W' x i‖) ≤ 2 * B₀ := by
  rw [weightedScaleNorm_zero_weight]
  have h1 := finsetLpNorm_add_le (P := 4) (by norm_num) (innerBonds D 0) (fun b => ‖baseSource W' b.1 b.2‖)
    (fun b => ‖baseSource W b.1 b.2‖)
  refine le_trans (finsetLpNorm_le_of_le (by norm_num) (fun _ _ => norm_nonneg _) fun b _ => ?_)
    (h1.trans (by linarith))
  exact norm_sub_le _ _
theorem finsetLpNorm_plaquetteSourceNorm_le_bonds (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S : Finset F.Cell} {z : F.Cell} (p : F.Site 0) (P : ℕ) (hP : 1 ≤ P) (e : F.Site 0 → Fin 4 → ComplexQuat) :
    finsetLpNorm P (plaquettesOver S {z} 0) (fun q => plaquetteSourceNorm q e) ≤
      128 * finsetLpNorm P (innerBonds (cellBall S z 1) 0) (fun b => ‖e b.1 b.2‖) := by
  have h := finsetLpNorm_plaquetteSourceNorm_le (S := S) (z := z) hamb hodd p (θ := 0) (by norm_num) P hP e
  rw [weightedScaleNorm_zero_weight] at h
  simpa [scaleWeight] using h
end Near
section Small
structure SmallParameter (L : ℕ) (y : ℝ) : Prop where
  pos : 0 < y
  le_bound : y ≤ 1 / 20000000
  count_le_radius : 48 * (48 * hullBondCount L + 1) * y ≤ hullBallRadius L
  scaled_count_le : 12 * (200000 * (L : ℝ) ^ 2) * (48 * hullBondCount L + 1) * y ≤ 1
  count_le : 64 * hullBondCount L * y ≤ 1
  first_le : 568 * (8 + 24 * (200000 * (L : ℝ) ^ 2) * (16 * hullFactor L + 5)) * hullFactor L * y ≤ 1
  second_le : 568 * (72 + 24 * (200000 * (L : ℝ) ^ 2) * (48 * hullBondCount L + 1)) * hullFactor L * y ≤ 1
  scale_le : 2 * (200000 * (L : ℝ) ^ 2) * y ≤ 1
  count_scale_le : 4608 * hullBondCount L * (200000 * (L : ℝ) ^ 2) * y ≤ 1
  le_radius : 6 * y ≤ hullBallRadius L
theorem finsetLpNorm_levelSource_sub_one_le {D : Finset F.Cell} {W : ComplexChainChart F} (ss : SourcesSmall D W)
    {y : ℝ} (h : finsetLpNorm 2 (lowerBonds D) (fun x => ‖upperSource W x‖) ≤ y) :
    finsetLpNorm 2 (lowerBonds D) (fun x => ‖levelSource W x.1 x.2.1 x.2.2 - 1‖) ≤ 2 * y := by
  have h1 := finsetLpNorm_const_mul_le (P := 2) (by norm_num) (lowerBonds D) (fun x => ‖upperSource W x‖)
    (a := 2) (by norm_num)
  refine le_trans (finsetLpNorm_le_of_le (by norm_num) (fun _ _ => norm_nonneg _) fun x hx => ?_)
    (h1.trans (by linarith))
  rw [levelSource_eq_unitExp]
  exact ComplexDifferences.norm_unitExp_sub_one_le ((ss.upper_le x hx).trans (by norm_num))
theorem norm_levelSource_sub_one_le {D : Finset F.Cell} {W : ComplexChainChart F} (ss : SourcesSmall D W) {y : ℝ}
    (h : finsetLpNorm 2 (lowerBonds D) (fun x => ‖upperSource W x‖) ≤ y)
    {x : Σ m : ℕ, F.Site (m + 1) × Fin 4} (hx : x ∈ lowerBonds D) :
    ‖levelSource W x.1 x.2.1 x.2.2 - 1‖ ≤ 2 * y := by
  have h1 := abs_le_finsetLpNorm (P := 2) (by norm_num) (s := lowerBonds D)
    (fun x => ‖levelSource W x.1 x.2.1 x.2.2 - 1‖) hx
  rw [abs_of_nonneg (norm_nonneg _)] at h1
  exact h1.trans (finsetLpNorm_levelSource_sub_one_le ss h)
theorem lowerBondSize_le (R : F.FieldChain) (W₀ W₁ W₂ : ComplexChainChart F) (x : Σ m : ℕ, F.Site (m + 1) × Fin 4) :
    lowerBondSize R W₀ W₁ W₂ x ≤ 3 * ‖levelSource W₀ x.1 x.2.1 x.2.2 - 1‖ + ‖ofUnit (referenceDefect R x.1 x.2) - 1‖ +
      ‖levelSource W₁ x.1 x.2.1 x.2.2 - 1‖ + ‖levelSource W₂ x.1 x.2.1 x.2.2 - 1‖ := by
  unfold lowerBondSize
  set E₀ := levelSource W₀ x.1 x.2.1 x.2.2
  set E₁ := levelSource W₁ x.1 x.2.1 x.2.2
  set E₂ := levelSource W₂ x.1 x.2.1 x.2.2
  set g := ofUnit (referenceDefect R x.1 x.2)
  have h1 : ‖E₀ * g - 1‖ ≤ ‖E₀ - 1‖ + ‖g - 1‖ := by
    have e : E₀ * g - 1 = (E₀ - 1) * g + (g - 1) := by noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have : ‖(E₀ - 1) * g‖ = ‖E₀ - 1‖ := norm_mul_ofUnit _ _
    linarith
  have h2 : ‖E₁ - E₀‖ ≤ ‖E₁ - 1‖ + ‖E₀ - 1‖ := by
    have e : E₁ - E₀ = (E₁ - 1) - (E₀ - 1) := by abel
    rw [e]
    exact norm_sub_le _ _
  have h3 : ‖E₂ - E₀‖ ≤ ‖E₂ - 1‖ + ‖E₀ - 1‖ := by
    have e : E₂ - E₀ = (E₂ - 1) - (E₀ - 1) := by abel
    rw [e]
    exact norm_sub_le _ _
  linarith
end Small
section Main
set_option maxHeartbeats 4000000 in
theorem sourceBounds_to_deviationEstimates (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) {S : Finset F.Cell} {z : F.Cell}
    {R : F.FieldChain} {W₀ W₁ W₂ W₃ : ComplexChainChart F} {C₀ s y : ℝ}
    (par : SourceParallelogram W₀ W₁ W₂ W₃) (hy : SmallParameter F.blockSide y) (hC : 0 < C₀) (hs : 0 < s)
    (hCs : C₀ * s ≤ y) (hnear : ContoursNearUnit R (cellBall S z 1) C₀ s)
    (hmis : finsetLpNorm 2 (lowerBonds (cellBall S z 1)) (fun x => ‖ofUnit (referenceDefect R x.1 x.2) - 1‖) ≤ y)
    (hcurv : ∀ q ∈ plaquettesOver S {z} 0,
      ‖ofUnit (basePlaquetteHolonomy (R 0) q) - 1‖ ≤ C₀ * s / ((F.blockSide : ℝ) ^ F.top) ^ 2)
    (z₀ : SourceBounds S z R W₀ y) (z₁ : SourceBounds S z R W₁ y) (z₂ : SourceBounds S z R W₂ y)
    (z₃ : SourceBounds S z R W₃ y)
    (hcl : ∀ W : ComplexChainChart F,
      Real.sqrt (Real.sqrt (∑ b ∈ innerBonds (cellBall S z 1) 0, ‖levelDeviation R W 0 b.1 b.2‖ ^ 4)) ≤ 2 * y →
      (∀ j, j + 1 < F.top →
        Real.sqrt (∑ c ∈ innerBonds (cellBall S z 1) (j + 1), ‖levelSource W j c.1 c.2 - 1‖ ^ 2) ≤ 2 * y) →
      ∀ j, j < F.top →
        Real.sqrt (Real.sqrt (∑ b ∈ innerBonds (cellBall S z 1) j, ‖levelDeviation R W j b.1 b.2‖ ^ 4)) ≤
          4 * (2 * y))
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) (p : F.Site 0) {P : Prop}
    (finish : ∀ {η B ε σ₀ : ℝ}
        (hεValue : ε = 1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2)))
        (h : FourDeviationBalls R (cellBall S z 1) W₀ W₁ W₂ W₃ C₀ s η B)
        (s₀ : SourcesSmall (cellBall S z 1) W₀) (s₁ : SourcesSmall (cellBall S z 1) W₁)
        (s₂ : SourcesSmall (cellBall S z 1) W₂) (s₃ : SourcesSmall (cellBall S z 1) W₃)
        (hB0 : 0 ≤ B) (hfac1 : 568 * firstDiffFactor F.blockSide C₀ s B * hullFactor F.blockSide ≤ 1)
        (hfac2 : 568 * secondDiffFactor F.blockSide C₀ s η * hullFactor F.blockSide ≤ 1)
        (hε0 : 0 < ε) (hε : 3 * (ε + C₀ * s) < hullBallRadius F.blockSide)
        (hK : 200000 * (F.blockSide : ℝ) ^ 2 * (ε + C₀ * s) ≤ 1)
        (htε : 3 * (2 * (hullBondCount F.blockSide * η)) ≤ ε / 48) (hσ₀ : 0 < σ₀)
        (hcurv : ∀ q ∈ plaquettesOver S {z} 0, ‖ofUnit (basePlaquetteHolonomy (R 0) q) - 1‖ ≤ σ₀)
        (hsmq : ∀ q ∈ plaquettesOver S {z} 0,
          24 * (3 * (plaquetteSourceNorm q (baseSource W₀) + plaquetteSourceNorm q (baseSourceDiff W₀ W₁) +
            plaquetteSourceNorm q (baseSourceDiff W₀ W₂)) + σ₀) < 1 / 256)
        (hTs : finsetLpNorm 4 (plaquettesOver S {z} 0) (fun q => 12 * 173 *
          (3 * (plaquetteSourceNorm q (baseSource W₀) + plaquetteSourceNorm q (baseSourceDiff W₀ W₁) +
            plaquetteSourceNorm q (baseSourceDiff W₀ W₂)) + σ₀)) ≤ 1)
        (hYs : finsetLpNorm 2 (plaquettesOver S {z} 0) (fun q => ‖plaquetteGap (R 0) q (baseSource W₀)‖ +
          ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₁)‖ +
          ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₂)‖ +
          ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₁ + baseSourceDiff W₀ W₂)‖) ≤ 1)
        (hY : finsetLpNorm 2 (lowerBonds (cellBall S z 1)) (lowerBondSize R W₀ W₁ W₂) ≤ 1)
        (hy1 : ∀ x ∈ lowerBonds (cellBall S z 1), lowerBondSize R W₀ W₁ W₂ x + ‖levelSource W₃ x.1 x.2.1 x.2.2 -
          levelSource W₁ x.1 x.2.1 x.2.2 - levelSource W₂ x.1 x.2.1 x.2.2 + levelSource W₀ x.1 x.2.1 x.2.2‖ ≤ 1), P) : P := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hy0 : 0 < y := hy.pos
  have hy1 := hy.le_bound
  have hCs0 : 0 < C₀ * s := mul_pos hC hs
  set H := hullBondCount F.blockSide with hH
  set Hf := hullFactor F.blockSide with hHf
  set K := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hH0 : 0 ≤ H := hullBondCount_nonneg _
  have hHf0 : 0 ≤ Hf := hullFactor_nonneg _
  have hK1 : 1 ≤ K := by
    rw [hK]
    nlinarith
  set r := hullBallRadius F.blockSide with hr
  set D := cellBall S z 1 with hD
  have hball : ∀ {W : ComplexChainChart F}, SourceBounds S z R W y →
      SourcesSmall D W ∧ DeviationBall R D W (8 * y) (8 * y) := fun {W} h =>
    deviationBall_of_finsetLpNorm_le (hcl W) h.base_le h.upper_le (by linarith)
  obtain ⟨s₀, b₀⟩ := hball z₀
  obtain ⟨s₁, b₁⟩ := hball z₁
  obtain ⟨s₂, b₂⟩ := hball z₂
  obtain ⟨s₃, b₃⟩ := hball z₃
  have ha := hy.count_le_radius
  have hb := hy.scaled_count_le
  have hc := hy.count_le
  have hd := hy.first_le
  have he := hy.second_le
  have hf := hy.scale_le
  have hg := hy.count_scale_le
  have hh := hy.le_radius
  rw [← hH, ← hr] at ha
  rw [← hK, ← hH] at hb
  rw [← hH] at hc
  rw [← hK, ← hHf] at hd
  rw [← hK, ← hH, ← hHf] at he
  rw [← hK] at hf
  rw [← hH, ← hK] at hg
  rw [← hr] at hh
  have e6 : 6 * (H * (8 * y)) + C₀ * s ≤ (48 * H + 1) * y := by
    have : 6 * (H * (8 * y)) = 48 * H * y := by ring
    have e2 : (48 * H + 1) * y = 48 * H * y + y := by ring
    linarith
  have hFB : FourDeviationBalls R D W₀ W₁ W₂ W₃ C₀ s (8 * y) (8 * y) := by
    refine ⟨hnear, b₀, b₁, b₂, b₃, hC, hs, by positivity, by linarith, by linarith, ?_, ?_, ?_⟩
    · have : 24 * (6 * (H * (8 * y)) + C₀ * s) ≤ 24 * ((48 * H + 1) * y) := by linarith
      have e : 48 * (48 * H + 1) * y = 2 * (24 * ((48 * H + 1) * y)) := by ring
      have p : 0 < (48 * H + 1) * y := by positivity
      linarith
    · have h9 := mul_le_mul_of_nonneg_left e6 (by positivity : 0 ≤ 12 * K)
      have e : 12 * K * ((48 * H + 1) * y) = 12 * K * (48 * H + 1) * y := by ring
      linarith
    · have e : 8 * (H * (8 * y)) = 64 * H * y := by ring
      linarith
  have hε0 : 0 < 1 / (2 * K) := by positivity
  have hKε : K * (1 / (2 * K)) = 1 / 2 := by
    field_simp
  have hεr : 3 * (1 / (2 * K)) < r / 2 := by
    rw [hr]
    unfold hullBallRadius
    have e1 : 3 * (1 / (2 * K)) = 3 / (400000 * (F.blockSide : ℝ) ^ 2) := by
      rw [hK]
      field_simp
      ring
    rw [e1, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hfac1 : 568 * firstDiffFactor F.blockSide C₀ s (8 * y) * Hf ≤ 1 := by
    unfold firstDiffFactor
    rw [← hK, ← hHf]
    have t1 : 8 * y + 24 * K * (2 * (Hf * (8 * y)) + 5 * (C₀ * s)) ≤ (8 + 24 * K * (16 * Hf + 5)) * y := by
      have q : 24 * K * (2 * (Hf * (8 * y)) + 5 * (C₀ * s)) ≤ 24 * K * ((16 * Hf + 5) * y) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have e : (16 * Hf + 5) * y = 2 * (Hf * (8 * y)) + 5 * y := by ring
        linarith
      have e : (8 + 24 * K * (16 * Hf + 5)) * y = 8 * y + 24 * K * ((16 * Hf + 5) * y) := by ring
      linarith
    have t2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left t1 (by norm_num : (0 : ℝ) ≤ 568)) hHf0
    have e : 568 * ((8 + 24 * K * (16 * Hf + 5)) * y) * Hf = 568 * (8 + 24 * K * (16 * Hf + 5)) * Hf * y := by
      ring
    linarith
  have hfac2 : 568 * secondDiffFactor F.blockSide C₀ s (8 * y) * Hf ≤ 1 := by
    unfold secondDiffFactor
    rw [← hK, ← hH]
    have t1 : 9 * (8 * y) + 24 * K * (6 * (H * (8 * y)) + C₀ * s) ≤ (72 + 24 * K * (48 * H + 1)) * y := by
      have q := mul_le_mul_of_nonneg_left e6 (by positivity : 0 ≤ 24 * K)
      have e : (72 + 24 * K * (48 * H + 1)) * y = 72 * y + 24 * K * ((48 * H + 1) * y) := by ring
      linarith
    have t2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left t1 (by norm_num : (0 : ℝ) ≤ 568)) hHf0
    have e : 568 * ((72 + 24 * K * (48 * H + 1)) * y) * Hf = 568 * (72 + 24 * K * (48 * H + 1)) * Hf * y := by
      ring
    linarith
  have hNp : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := one_le_pow₀ hL1
  set Nn := (F.blockSide : ℝ) ^ F.top with hNn
  set σ₀ := C₀ * s / Nn ^ 2 with hσ₀
  have hσ0 : 0 < σ₀ := by positivity
  have hσy : σ₀ ≤ y := by
    have h1 : C₀ * s / Nn ^ 2 ≤ C₀ * s := div_le_self hCs0.le (one_le_pow₀ hNp)
    linarith
  set Pz := plaquettesOver S {z} 0 with hPz
  have hcardP : (Pz.card : ℝ) ≤ 1296 * Nn ^ 4 := card_plaquettesOver_singleton_le hamb hodd S z
  have hσ4 : finsetLpNorm 4 Pz (fun _ => σ₀) ≤ 6 * y := by
    have h1 := finsetLpNorm_const_le Pz (a := σ₀) (Cn := 6 * Nn) hσ0.le (by positivity) (P := 4) (by norm_num) (by
      refine hcardP.trans (le_of_eq ?_)
      ring)
    refine h1.trans ?_
    have e : 6 * Nn * σ₀ = 6 * (C₀ * s / Nn) := by
      rw [hσ₀]
      field_simp
    rw [e]
    have h2 : C₀ * s / Nn ≤ C₀ * s := div_le_self hCs0.le hNp
    linarith
  have hσ2 : finsetLpNorm 2 Pz (fun _ => σ₀) ≤ 36 * y := by
    have h1 := finsetLpNorm_const_le Pz (a := σ₀) (Cn := 36 * Nn ^ 2) hσ0.le (by positivity) (P := 2) (by norm_num)
      (by
        refine hcardP.trans (le_of_eq ?_)
        ring)
    refine h1.trans ?_
    have e : 36 * Nn ^ 2 * σ₀ = 36 * (C₀ * s) := by
      rw [hσ₀]
      field_simp
    rw [e]
    linarith
  have hN₀ : finsetLpNorm 4 Pz (fun q => plaquetteSourceNorm q (baseSource W₀)) ≤ 128 * y := by
    have h1 := finsetLpNorm_plaquetteSourceNorm_le_bonds (S := S) (z := z) hamb hodd p 4 (by norm_num)
      (baseSource W₀)
    have h3 := mul_le_mul_of_nonneg_left z₀.base_le (by norm_num : (0 : ℝ) ≤ 128)
    exact h1.trans h3
  have hNd : ∀ {W W' : ComplexChainChart F}, SourceBounds S z R W y → SourceBounds S z R W' y →
      finsetLpNorm 4 Pz (fun q => plaquetteSourceNorm q (baseSourceDiff W W')) ≤ 256 * y := by
    intro W W' h h'
    have h1 := finsetLpNorm_plaquetteSourceNorm_le_bonds (S := S) (z := z) hamb hodd p 4 (by norm_num)
      (baseSourceDiff W W')
    have h3 := weightedScaleNorm_zero_baseSourceDiff_le (D := D) p h.base_le h'.base_le
    rw [weightedScaleNorm_zero_weight] at h3
    have h4 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 128)
    refine h1.trans (h4.trans (le_of_eq ?_))
    ring
  have hN₁ := hNd z₀ z₁
  have hN₂ := hNd z₀ z₂
  have hpt : ∀ q ∈ Pz, plaquetteSourceNorm q (baseSource W₀) + plaquetteSourceNorm q (baseSourceDiff W₀ W₁) +
      plaquetteSourceNorm q (baseSourceDiff W₀ W₂) ≤ 640 * y := by
    intro q hq
    have t1 := abs_le_finsetLpNorm (P := 4) (by norm_num) (s := Pz)
      (fun q => plaquetteSourceNorm q (baseSource W₀)) hq
    have t2 := abs_le_finsetLpNorm (P := 4) (by norm_num) (s := Pz)
      (fun q => plaquetteSourceNorm q (baseSourceDiff W₀ W₁)) hq
    have t3 := abs_le_finsetLpNorm (P := 4) (by norm_num) (s := Pz)
      (fun q => plaquetteSourceNorm q (baseSourceDiff W₀ W₂)) hq
    have u1 := le_abs_self (plaquetteSourceNorm q (baseSource W₀))
    have u2 := le_abs_self (plaquetteSourceNorm q (baseSourceDiff W₀ W₁))
    have u3 := le_abs_self (plaquetteSourceNorm q (baseSourceDiff W₀ W₂))
    linarith
  have hsmq : ∀ q ∈ Pz,
      24 * (3 * (plaquetteSourceNorm q (baseSource W₀) + plaquetteSourceNorm q (baseSourceDiff W₀ W₁) +
        plaquetteSourceNorm q (baseSourceDiff W₀ W₂)) + σ₀) < 1 / 256 := by
    intro q hq
    have := hpt q hq
    linarith
  have hTs : finsetLpNorm 4 Pz (fun q => 12 * 173 *
      (3 * (plaquetteSourceNorm q (baseSource W₀) + plaquetteSourceNorm q (baseSourceDiff W₀ W₁) +
        plaquetteSourceNorm q (baseSourceDiff W₀ W₂)) + σ₀)) ≤ 1 := by
    have c1 := finsetLpNorm_const_mul_le (P := 4) (by norm_num) Pz
      (fun q => 3 * (plaquetteSourceNorm q (baseSource W₀) + plaquetteSourceNorm q (baseSourceDiff W₀ W₁) +
        plaquetteSourceNorm q (baseSourceDiff W₀ W₂)) + σ₀)
      (a := 12 * 173) (by norm_num)
    have c2 := finsetLpNorm_add_le (P := 4) (by norm_num) Pz
      (fun q => 3 * (plaquetteSourceNorm q (baseSource W₀) + plaquetteSourceNorm q (baseSourceDiff W₀ W₁) +
        plaquetteSourceNorm q (baseSourceDiff W₀ W₂)))
      (fun _ => σ₀)
    have c3 := finsetLpNorm_const_mul_le (P := 4) (by norm_num) Pz
      (fun q => plaquetteSourceNorm q (baseSource W₀) + plaquetteSourceNorm q (baseSourceDiff W₀ W₁) +
        plaquetteSourceNorm q (baseSourceDiff W₀ W₂))
      (a := 3) (by norm_num)
    have c4 := finsetLpNorm_add_le (P := 4) (by norm_num) Pz
      (fun q => plaquetteSourceNorm q (baseSource W₀) + plaquetteSourceNorm q (baseSourceDiff W₀ W₁))
      (fun q => plaquetteSourceNorm q (baseSourceDiff W₀ W₂))
    have c5 := finsetLpNorm_add_le (P := 4) (by norm_num) Pz
      (fun q => plaquetteSourceNorm q (baseSource W₀)) (fun q => plaquetteSourceNorm q (baseSourceDiff W₀ W₁))
    linarith
  have hgap : ∀ {ξ : F.Site 0 → Fin 4 → ComplexQuat}, finsetLpNorm 4 Pz (fun q => plaquetteSourceNorm q ξ) ≤ 128 * y →
      finsetLpNorm 2 Pz (fun q => ‖covariantCurl (R 0) q ξ‖) ≤ y → (∀ q ∈ Pz, plaquetteSourceNorm q ξ ≤ 1 / 256) →
      finsetLpNorm 2 Pz (fun q => ‖plaquetteGap (R 0) q ξ‖) ≤ 1 / 4 := by
    intro ξ h1 h3 h4
    have hrem : finsetLpNorm 2 Pz (fun q => ‖plaquetteRemainder (R 0) q ξ‖) ≤
        173 * ((128 * y) ^ 2 + 6 * y * (128 * y)) := by
      have p1 : ∀ q ∈ Pz, ‖plaquetteRemainder (R 0) q ξ‖ ≤
          173 * (plaquetteSourceNorm q ξ * plaquetteSourceNorm q ξ + σ₀ * plaquetteSourceNorm q ξ) := by
        intro q hq
        have := norm_plaquetteRemainder_le (R 0) q (h4 q hq) (hcurv q hq)
        have e : plaquetteSourceNorm q ξ ^ 2 = plaquetteSourceNorm q ξ * plaquetteSourceNorm q ξ := by ring
        rw [e] at this
        exact this
      refine (finsetLpNorm_le_of_le (by norm_num) (fun _ _ => norm_nonneg _) p1).trans ?_
      have c1 := finsetLpNorm_const_mul_le (P := 2) (by norm_num) Pz
        (fun q => plaquetteSourceNorm q ξ * plaquetteSourceNorm q ξ + σ₀ * plaquetteSourceNorm q ξ) (a := 173)
        (by norm_num)
      have c2 := finsetLpNorm_add_le (P := 2) (by norm_num) Pz
        (fun q => plaquetteSourceNorm q ξ * plaquetteSourceNorm q ξ) (fun q => σ₀ * plaquetteSourceNorm q ξ)
      have c3 := finsetLpNorm_two_mul_le Pz (fun q => plaquetteSourceNorm q ξ) (fun q => plaquetteSourceNorm q ξ)
      have c4 := finsetLpNorm_two_mul_le Pz (fun _ => σ₀) (fun q => plaquetteSourceNorm q ξ)
      have n0 := finsetLpNorm_nonneg 4 Pz (fun q => plaquetteSourceNorm q ξ)
      have c5 : finsetLpNorm 4 Pz (fun q => plaquetteSourceNorm q ξ) *
          finsetLpNorm 4 Pz (fun q => plaquetteSourceNorm q ξ) ≤ (128 * y) * (128 * y) :=
        mul_le_mul h1 h1 n0 (by positivity)
      have c6 : finsetLpNorm 4 Pz (fun _ : F.Site 0 × Fin 4 × Fin 4 => σ₀) *
          finsetLpNorm 4 Pz (fun q => plaquetteSourceNorm q ξ) ≤ (6 * y) * (128 * y) :=
        mul_le_mul hσ4 h1 n0 (by positivity)
      have e : (128 * y) ^ 2 = (128 * y) * (128 * y) := by ring
      rw [e]
      linarith
    have hey : ∀ q, ‖plaquetteGap (R 0) q ξ‖ ≤ ‖ofUnit (basePlaquetteHolonomy (R 0) q) - 1‖ +
        ‖covariantCurl (R 0) q ξ‖ + ‖plaquetteRemainder (R 0) q ξ‖ := by
      intro q
      rw [plaquetteGap_eq]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    have hey' : ∀ q ∈ Pz, ‖plaquetteGap (R 0) q ξ‖ ≤
        σ₀ + ‖covariantCurl (R 0) q ξ‖ + ‖plaquetteRemainder (R 0) q ξ‖ := fun q hq => by
      have := hey q
      have := hcurv q hq
      linarith
    refine (finsetLpNorm_le_of_le (by norm_num) (fun _ _ => norm_nonneg _) hey').trans ?_
    have c1 := finsetLpNorm_add_le (P := 2) (by norm_num) Pz (fun q => σ₀ + ‖covariantCurl (R 0) q ξ‖)
      (fun q => ‖plaquetteRemainder (R 0) q ξ‖)
    have c2 := finsetLpNorm_add_le (P := 2) (by norm_num) Pz (fun _ => σ₀) (fun q => ‖covariantCurl (R 0) q ξ‖)
    have hyy : y * y ≤ y * (1 / 20000000) := mul_le_mul_of_nonneg_left hy1 hy0.le
    have e : 173 * ((128 * y) ^ 2 + 6 * y * (128 * y)) = 173 * 17152 * (y * y) := by ring
    rw [e] at hrem
    linarith
  have hpl : ∀ {W : ComplexChainChart F}, SourceBounds S z R W y →
      (∀ q ∈ Pz, plaquetteSourceNorm q (baseSource W) ≤ 1 / 256) →
      finsetLpNorm 2 Pz (fun q => ‖plaquetteGap (R 0) q (baseSource W)‖) ≤ 1 / 4 := by
    intro W h hq
    refine hgap ?_ h.curl_le hq
    have h1 := finsetLpNorm_plaquetteSourceNorm_le_bonds (S := S) (z := z) hamb hodd p 4 (by norm_num)
      (baseSource W)
    exact h1.trans (mul_le_mul_of_nonneg_left h.base_le (by norm_num))
  have e₁ : baseSource W₁ = baseSource W₀ + baseSourceDiff W₀ W₁ := by
    simp only [baseSourceDiff]
    abel
  have e₂ : baseSource W₂ = baseSource W₀ + baseSourceDiff W₀ W₂ := by
    simp only [baseSourceDiff]
    abel
  have e₃ : baseSource W₃ = baseSource W₀ + baseSourceDiff W₀ W₁ + baseSourceDiff W₀ W₂ := by
    funext x i
    simp only [Pi.add_apply, baseSourceDiff, Pi.sub_apply, par.base x i]
    abel
  have hsmall : ∀ {W : ComplexChainChart F}, SourceBounds S z R W y →
      ∀ q ∈ Pz, plaquetteSourceNorm q (baseSource W) ≤ 1 / 256 := by
    intro W h q hq
    have h1 := finsetLpNorm_plaquetteSourceNorm_le_bonds (S := S) (z := z) hamb hodd p 4 (by norm_num)
      (baseSource W)
    have t1 := abs_le_finsetLpNorm (P := 4) (by norm_num) (s := Pz)
      (fun q => plaquetteSourceNorm q (baseSource W)) hq
    have u1 := le_abs_self (plaquetteSourceNorm q (baseSource W))
    have h3 := mul_le_mul_of_nonneg_left h.base_le (by norm_num : (0 : ℝ) ≤ 128)
    linarith
  have hYs : finsetLpNorm 2 Pz (fun q => ‖plaquetteGap (R 0) q (baseSource W₀)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₁)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₂)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₁ + baseSourceDiff W₀ W₂)‖) ≤ 1 := by
    rw [← e₃, ← e₁, ← e₂]
    have g0 := hpl z₀ (hsmall z₀)
    have g1 := hpl z₁ (hsmall z₁)
    have g2 := hpl z₂ (hsmall z₂)
    have g3 := hpl z₃ (hsmall z₃)
    have c1 := finsetLpNorm_add_le (P := 2) (by norm_num) Pz (fun q => ‖plaquetteGap (R 0) q (baseSource W₀)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₁)‖ + ‖plaquetteGap (R 0) q (baseSource W₂)‖)
      (fun q => ‖plaquetteGap (R 0) q (baseSource W₃)‖)
    have c2 := finsetLpNorm_add_le (P := 2) (by norm_num) Pz (fun q => ‖plaquetteGap (R 0) q (baseSource W₀)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₁)‖) (fun q => ‖plaquetteGap (R 0) q (baseSource W₂)‖)
    have c3 := finsetLpNorm_add_le (P := 2) (by norm_num) Pz (fun q => ‖plaquetteGap (R 0) q (baseSource W₀)‖)
      (fun q => ‖plaquetteGap (R 0) q (baseSource W₁)‖)
    linarith
  have hY : finsetLpNorm 2 (lowerBonds D) (lowerBondSize R W₀ W₁ W₂) ≤ 1 := by
    have m0 := finsetLpNorm_levelSource_sub_one_le s₀ z₀.upper_le
    have m1 := finsetLpNorm_levelSource_sub_one_le s₁ z₁.upper_le
    have m2 := finsetLpNorm_levelSource_sub_one_le s₂ z₂.upper_le
    have hp : ∀ x ∈ lowerBonds D, 0 ≤ lowerBondSize R W₀ W₁ W₂ x := fun x _ => by
      unfold lowerBondSize
      exact add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    refine (finsetLpNorm_le_of_le (by norm_num) hp fun x _ => lowerBondSize_le R W₀ W₁ W₂ x).trans ?_
    have c1 := finsetLpNorm_add_le (P := 2) (by norm_num) (lowerBonds D)
      (fun x => 3 * ‖levelSource W₀ x.1 x.2.1 x.2.2 - 1‖ + ‖ofUnit (referenceDefect R x.1 x.2) - 1‖ +
        ‖levelSource W₁ x.1 x.2.1 x.2.2 - 1‖) (fun x => ‖levelSource W₂ x.1 x.2.1 x.2.2 - 1‖)
    have c2 := finsetLpNorm_add_le (P := 2) (by norm_num) (lowerBonds D)
      (fun x => 3 * ‖levelSource W₀ x.1 x.2.1 x.2.2 - 1‖ + ‖ofUnit (referenceDefect R x.1 x.2) - 1‖)
      (fun x => ‖levelSource W₁ x.1 x.2.1 x.2.2 - 1‖)
    have c3 := finsetLpNorm_add_le (P := 2) (by norm_num) (lowerBonds D)
      (fun x => 3 * ‖levelSource W₀ x.1 x.2.1 x.2.2 - 1‖) (fun x => ‖ofUnit (referenceDefect R x.1 x.2) - 1‖)
    have c4 := finsetLpNorm_const_mul_le (P := 2) (by norm_num) (lowerBonds D)
      (fun x => ‖levelSource W₀ x.1 x.2.1 x.2.2 - 1‖) (a := 3) (by norm_num)
    linarith
  have hy1' : ∀ x ∈ lowerBonds D, lowerBondSize R W₀ W₁ W₂ x + ‖levelSource W₃ x.1 x.2.1 x.2.2 -
      levelSource W₁ x.1 x.2.1 x.2.2 - levelSource W₂ x.1 x.2.1 x.2.2 + levelSource W₀ x.1 x.2.1 x.2.2‖ ≤ 1 := by
    intro x hx
    have t0 := norm_levelSource_sub_one_le s₀ z₀.upper_le hx
    have t1 := norm_levelSource_sub_one_le s₁ z₁.upper_le hx
    have t2 := norm_levelSource_sub_one_le s₂ z₂.upper_le hx
    have t3 := norm_levelSource_sub_one_le s₃ z₃.upper_le hx
    have t4 := lowerBondSize_le R W₀ W₁ W₂ x
    have t5 := abs_le_finsetLpNorm (P := 2) (by norm_num) (s := lowerBonds D)
      (fun x => ‖ofUnit (referenceDefect R x.1 x.2) - 1‖) hx
    rw [abs_of_nonneg (norm_nonneg _)] at t5
    set E₀ := levelSource W₀ x.1 x.2.1 x.2.2
    set E₁ := levelSource W₁ x.1 x.2.1 x.2.2
    set E₂ := levelSource W₂ x.1 x.2.1 x.2.2
    set E₃ := levelSource W₃ x.1 x.2.1 x.2.2
    have d3 : ‖E₃ - E₁ - E₂ + E₀‖ ≤ 8 * y := by
      have e : E₃ - E₁ - E₂ + E₀ = (E₃ - 1) - (E₁ - 1) - (E₂ - 1) + (E₀ - 1) := by abel
      rw [e]
      have u1 := norm_add_le ((E₃ - 1) - (E₁ - 1) - (E₂ - 1)) (E₀ - 1)
      have u2 := norm_sub_le ((E₃ - 1) - (E₁ - 1)) (E₂ - 1)
      have u3 := norm_sub_le (E₃ - 1) (E₁ - 1)
      linarith
    linarith
  have hεK : 200000 * (F.blockSide : ℝ) ^ 2 * (1 / (2 * K) + C₀ * s) ≤ 1 := by
    rw [← hK, mul_add, hKε]
    have : K * (C₀ * s) ≤ K * y := mul_le_mul_of_nonneg_left hCs (by positivity)
    have e : 2 * K * y = 2 * (K * y) := by ring
    linarith
  have hεr' : 3 * (1 / (2 * K) + C₀ * s) < hullBallRadius F.blockSide := by
    rw [← hr]
    have : 3 * (C₀ * s) ≤ 3 * y := by linarith
    linarith
  have htε : 3 * (2 * (hullBondCount F.blockSide * (8 * y))) ≤ 1 / (2 * K) / 48 := by
    rw [← hH]
    have e : 1 / (2 * K) / 48 = 1 / (96 * K) := by
      field_simp
      norm_num
    rw [e, le_div_iff₀ (by positivity)]
    have e2 : 3 * (2 * (H * (8 * y))) * (96 * K) = 4608 * H * K * y := by ring
    rw [e2]
    exact hg
  exact finish rfl hFB s₀ s₁ s₂ s₃ (by positivity)
    hfac1 hfac2 hε0 hεr' hεK htε hσ0 hcurv hsmq hTs hYs hY hy1'

theorem norm_complexCellTerms_second_diff_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (a : ℝ) {S : Finset F.Cell} {z : F.Cell}
    {R : F.FieldChain} (V : F.GaugeField F.top) {W₀ W₁ W₂ W₃ : ComplexChainChart F} {C₀ s y : ℝ}
    (par : SourceParallelogram W₀ W₁ W₂ W₃) (hy : SmallParameter F.blockSide y) (hC : 0 < C₀) (hs : 0 < s)
    (hCs : C₀ * s ≤ y) (hnear : ContoursNearUnit R (cellBall S z 1) C₀ s)
    (hmis : finsetLpNorm 2 (lowerBonds (cellBall S z 1)) (fun x => ‖ofUnit (referenceDefect R x.1 x.2) - 1‖) ≤ y)
    (hcurv : ∀ q ∈ plaquettesOver S {z} 0,
      ‖ofUnit (basePlaquetteHolonomy (R 0) q) - 1‖ ≤ C₀ * s / ((F.blockSide : ℝ) ^ F.top) ^ 2)
    (z₀ : SourceBounds S z R W₀ y) (z₁ : SourceBounds S z R W₁ y) (z₂ : SourceBounds S z R W₂ y)
    (z₃ : SourceBounds S z R W₃ y)
    (hcl : ∀ W : ComplexChainChart F,
      Real.sqrt (Real.sqrt (∑ b ∈ innerBonds (cellBall S z 1) 0, ‖levelDeviation R W 0 b.1 b.2‖ ^ 4)) ≤ 2 * y →
      (∀ j, j + 1 < F.top →
        Real.sqrt (∑ c ∈ innerBonds (cellBall S z 1) (j + 1), ‖levelSource W j c.1 c.2 - 1‖ ^ 2) ≤ 2 * y) →
      ∀ j, j < F.top →
        Real.sqrt (Real.sqrt (∑ b ∈ innerBonds (cellBall S z 1) j, ‖levelDeviation R W j b.1 b.2‖ ^ 4)) ≤
          4 * (2 * y))
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) (p : F.Site 0) :
    ‖complexCellTerms a S R W₃ V z - complexCellTerms a S R W₁ V z - complexCellTerms a S R W₂ V z +
        complexCellTerms a S R W₀ V z‖ ≤
      cellSecondDiffConst (hullFactor F.blockSide) (200000 * (F.blockSide : ℝ) ^ 2)
          (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) a *
        ((weightedScaleNorm (cellBall S z 1) p θ 4 0 (fun x i => ‖baseSource W₁ x i - baseSource W₀ x i‖) +
            finsetLpNorm 2 (lowerBonds (cellBall S z 1))
              (fun x => lowerScaleWeight p θ x * ‖upperSource W₁ x - upperSource W₀ x‖) +
            finsetLpNorm 2 (plaquettesOver S {z} 0)
              (fun q => scaleWeight p θ 0 q.1 * ‖covariantCurl (R 0) q (baseSourceDiff W₀ W₁)‖)) *
          (weightedScaleNorm (cellBall S z 1) p (-θ) 4 0 (fun x i => ‖baseSource W₂ x i - baseSource W₀ x i‖) +
            finsetLpNorm 2 (lowerBonds (cellBall S z 1))
              (fun x => lowerScaleWeight p (-θ) x * ‖upperSource W₂ x - upperSource W₀ x‖) +
            finsetLpNorm 2 (plaquettesOver S {z} 0)
              (fun q => scaleWeight p (-θ) 0 q.1 * ‖covariantCurl (R 0) q (baseSourceDiff W₀ W₂)‖))) := by
  apply CellNormBounds.sourceBounds_to_deviationEstimates hamb hodd h2 par hy hC hs hCs hnear hmis hcurv
    z₀ z₁ z₂ z₃ hcl hθ p
  intro η B ε σ₀ hεValue h s₀ s₁ s₂ s₃ hB0 hfac1 hfac2 hε0 hε hK htε hσ₀ hcurv' hsmq hTs hYs hY hy1
  subst ε
  exact norm_complexCellTerms_second_diff_le_const hamb hodd h2 a V h s₀ s₁ s₂ s₃ par hθ p hB0
    hfac1 hfac2 hε0 hε hK htε hσ₀ hcurv' hsmq hTs hYs hY hy1
end Main
end YangMills.Construction.CellNormBounds
end

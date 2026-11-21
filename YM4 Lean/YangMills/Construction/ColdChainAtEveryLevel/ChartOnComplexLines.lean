import YangMills.Construction.ColdChainAtEveryLevel.CellBalls
import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.ColdChainAtEveryLevel.ComplexChainIsAnalytic
import YangMills.Construction.ColdChainAtEveryLevel.ComplexChartElements
import YangMills.Construction.ColdChainAtEveryLevel.MixedDerivativesOfABoundedExtension
import YangMills.Construction.ColdChainAtEveryLevel.ReferenceInTheChart
import YangMills.Construction.ColdChainAtEveryLevel.TheChartIsLocal
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
open Metric
namespace YangMills.Construction.ComplexLineChart
open BlockAverages ComplexChart ComplexChart.BlockGeometry ComplexifiedQuaternions Analytic ComplexLevels
  ComplexContours ComplexAnalyticity ComplexDifferences ComplexChainStep ComplexRemainders
  LatticeFractionalIntegration LatticePaths
variable {F : BlockFrame}
section Powers
variable {β : Type}
def finsetLpNorm (p : ℝ) (s : Finset β) (f : β → ℝ) : ℝ := (∑ b ∈ s, |f b| ^ p) ^ (1 / p)
theorem finsetLpNorm_nonneg (p : ℝ) (s : Finset β) (f : β → ℝ) : 0 ≤ finsetLpNorm p s f :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
theorem finsetLpNorm_add_le {p : ℝ} (hp : 1 ≤ p) (s : Finset β) (f g : β → ℝ) :
    finsetLpNorm p s (fun b => f b + g b) ≤ finsetLpNorm p s f + finsetLpNorm p s g :=
  Real.Lp_add_le s f g hp
theorem finsetLpNorm_const_mul {p : ℝ} (hp : 0 < p) {c : ℝ} (hc : 0 ≤ c) (s : Finset β) (f : β → ℝ) :
    finsetLpNorm p s (fun b => c * f b) = c * finsetLpNorm p s f := by
  unfold finsetLpNorm
  have h : ∀ b, |c * f b| ^ p = c ^ p * |f b| ^ p := fun b => by
    rw [abs_mul, abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg _)]
  simp only [h, ← Finset.mul_sum]
  rw [Real.mul_rpow (by positivity) (Finset.sum_nonneg fun _ _ => by positivity), ← Real.rpow_mul hc,
    mul_one_div_cancel hp.ne', Real.rpow_one]
theorem finsetLpNorm_mono {p : ℝ} (hp : 0 < p) (s : Finset β) {f g : β → ℝ} (h : ∀ b ∈ s, |f b| ≤ |g b|) :
    finsetLpNorm p s f ≤ finsetLpNorm p s g := by
  unfold finsetLpNorm
  refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity)
    (Finset.sum_le_sum fun b hb => Real.rpow_le_rpow (abs_nonneg _) (h b hb) hp.le) (by positivity)
theorem finsetLpNorm_sum_le {ι : Type} {p : ℝ} (hp : 1 ≤ p) (s : Finset β) (f : ι → β → ℝ) (T : Finset ι) :
    finsetLpNorm p s (fun b => ∑ l ∈ T, f l b) ≤ ∑ l ∈ T, finsetLpNorm p s (f l) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have hp0 : p ≠ 0 := by linarith
    simp [finsetLpNorm, Real.zero_rpow hp0, Real.zero_rpow (inv_ne_zero hp0)]
  | insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    exact (finsetLpNorm_add_le hp s _ _).trans (by linarith)
theorem abs_le_finsetLpNorm {p : ℝ} (hp : 0 < p) {s : Finset β} {b : β} (hb : b ∈ s) (f : β → ℝ) :
    |f b| ≤ finsetLpNorm p s f := by
  have h1 : |f b| ^ p ≤ ∑ b ∈ s, |f b| ^ p :=
    Finset.single_le_sum (f := fun b => |f b| ^ p) (fun _ _ => by positivity) hb
  calc |f b| = (|f b| ^ p) ^ (1 / p) := by
        rw [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hp.ne', Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) h1 (by positivity)
theorem finsetLpNorm_four (s : Finset β) (f : β → ℝ) :
    finsetLpNorm 4 s f = Real.sqrt (Real.sqrt (∑ b ∈ s, f b ^ 4)) := by
  have hs : 0 ≤ ∑ b ∈ s, f b ^ 4 := Finset.sum_nonneg fun _ _ => by positivity
  have h : ∀ b, |f b| ^ (4 : ℝ) = f b ^ 4 := fun b => by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact Even.pow_abs (by decide) _
  unfold finsetLpNorm
  simp only [h]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hs]
  norm_num
theorem finsetLpNorm_two (s : Finset β) (f : β → ℝ) : finsetLpNorm 2 s f = Real.sqrt (∑ b ∈ s, f b ^ 2) := by
  have h : ∀ b, |f b| ^ (2 : ℝ) = f b ^ 2 := fun b => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact sq_abs _
  unfold finsetLpNorm
  simp only [h]
  rw [Real.sqrt_eq_rpow]
end Powers
section Near
theorem finsetLpNorm_fine_le_localNorm (S : Finset F.Cell) (R : F.FieldChain) (A : ChainChart F) (z : F.Cell)
    {T : Finset (F.Site 0 × Fin 4)} (hT : T ⊆ bondsOver S (cellBall S z 3) 0) :
    finsetLpNorm 4 T (fun b => ‖A.fine b.1 b.2‖) ≤ localNorm S R A (oneSiteWeights F) z := by
  rw [finsetLpNorm_four]
  unfold localNorm localNormSq
  set Q := ∑ b ∈ bondsOver S (cellBall S z 3) 0, (oneSiteWeights F 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4 with hQ
  have h1 : ∑ b ∈ T, ‖A.fine b.1 b.2‖ ^ 4 ≤ Q := by
    rw [hQ]
    simp only [oneSiteWeights, one_mul]
    exact Finset.sum_le_sum_of_subset_of_nonneg hT fun _ _ _ => by positivity
  refine Real.sqrt_le_sqrt ((Real.sqrt_le_sqrt h1).trans ?_)
  have h2 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0,
      (oneSiteWeights F 0 p.1 * ‖linearizedCurl (R 0) A.fine p‖) ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have h3 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (oneSiteWeights F (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  linarith
theorem finsetLpNorm_coarse_le_localNorm (S : Finset F.Cell) (R : F.FieldChain) (A : ChainChart F) (z : F.Cell)
    {j : ℕ} (hj : j + 1 < F.top)
    {T : Finset (F.Site (j + 1) × Fin 4)} (hT : T ⊆ bondsOver S (cellBall S z 3) (j + 1)) :
    finsetLpNorm 2 T (fun b => ‖A.coarse j b.1 b.2‖) ≤ localNorm S R A (oneSiteWeights F) z := by
  rw [finsetLpNorm_two]
  unfold localNorm localNormSq
  refine Real.sqrt_le_sqrt ?_
  have hj' : j ∈ Finset.range (F.top - 1) := Finset.mem_range.2 (by omega)
  have h1 : ∑ b ∈ T, ‖A.coarse j b.1 b.2‖ ^ 2 ≤ ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (oneSiteWeights F (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2 := by
    simp only [oneSiteWeights, one_mul]
    exact Finset.sum_le_sum_of_subset_of_nonneg hT fun _ _ _ => by positivity
  have h2 := Finset.single_le_sum (f := fun j => ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (oneSiteWeights F (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hj'
  have h3 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0,
      (oneSiteWeights F 0 p.1 * ‖linearizedCurl (R 0) A.fine p‖) ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have h4 := Real.sqrt_nonneg
    (∑ b ∈ bondsOver S (cellBall S z 3) 0, (oneSiteWeights F 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4)
  beta_reduce at h2
  linarith
theorem sitesOfCells_subset {D S : Finset F.Cell} (h : D ⊆ S) (j : ℕ) : sitesOfCells D j ⊆ sitesOfCells S j := by apply _root_.YangMills.Construction.BlockLines.sitesOfCells_mono <;> assumption
theorem enclosingCell_mem_of_mem_sitesOfCells {D : Finset F.Cell} (hodd : Odd F.blockSide) {j : ℕ}
    {x : F.Site j} (hx : x ∈ sitesOfCells D j) : enclosingCell x ∈ D := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_mem <;> assumption
theorem innerBonds_subset_bondsOver {D S : Finset F.Cell} (hodd : Odd F.blockSide) (hDS : D ⊆ S) {z : F.Cell}
    (hz : ∀ y ∈ D, cellSupDist z y ≤ 3) (j : ℕ) : innerBonds D j ⊆ bondsOver S (cellBall S z 3) j := by
  classical
  intro b hb
  obtain ⟨h1, h2⟩ := mem_innerBonds_iff.1 hb
  have hbS : b ∈ innerBonds S j :=
    mem_innerBonds_iff.2 ⟨sitesOfCells_subset hDS j h1, sitesOfCells_subset hDS j h2⟩
  have hc : enclosingCell b.1 ∈ D := enclosingCell_mem_of_mem_sitesOfCells hodd h1
  unfold bondsOver
  simp only [Finset.mem_filter]
  refine ⟨hbS, ?_⟩
  unfold cellBall
  simp only [Finset.mem_filter]
  exact ⟨hDS hc, hz _ hc⟩
end Near
section Family
variable {ι : Type} [Fintype ι]
def imagToComplex (a : imaginaryQuaternions) : ComplexQuat := ofQuat (a : ℍ[ℝ])
theorem imagToComplex_add (a b : imaginaryQuaternions) :
    imagToComplex (a + b) = imagToComplex a + imagToComplex b := ofQuat_add _ _
theorem imagToComplex_zero : imagToComplex 0 = 0 := ofQuat_zero
theorem imagToComplex_smul (r : ℝ) (a : imaginaryQuaternions) :
    imagToComplex (r • a) = (r : ℂ) • imagToComplex a := ofQuat_smul r a
omit [Fintype ι] in
theorem imagToComplex_sum (T : Finset ι) (f : ι → imaginaryQuaternions) :
    imagToComplex (∑ l ∈ T, f l) = ∑ l ∈ T, imagToComplex (f l) := by
  unfold imagToComplex
  rw [AddSubmonoidClass.coe_finsetSum]
  exact ofQuat_sum _ _
theorem norm_imagToComplex (a : imaginaryQuaternions) : ‖imagToComplex a‖ = ‖a‖ := norm_ofQuat _
def complexLine (a : imaginaryQuaternions) (v : ι → imaginaryQuaternions) (w : ι → ℝ) (ζ : ι → ℂ) :
    ComplexQuat :=
  imagToComplex a + ∑ l, ζ l • ((w l : ℂ) • imagToComplex (v l))
theorem complexifiedImaginary_eq_complexLine (a : imaginaryQuaternions) (v : ι → imaginaryQuaternions)
    (w : ι → ℝ) (ζ : ι → ℂ) :
    complexifiedImaginary (a + ∑ l, (w l * (ζ l).re) • v l) ((0 : imaginaryQuaternions) + ∑ l, (w l * (ζ l).im) • v l) =
      complexLine a v w ζ := by
  show imagToComplex _ + Complex.I • imagToComplex _ = _
  rw [imagToComplex_add, imagToComplex_add, imagToComplex_zero, zero_add, imagToComplex_sum, imagToComplex_sum,
    complexLine, add_assoc, Finset.smul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [imagToComplex_smul, imagToComplex_smul, smul_smul, smul_smul, ← add_smul]
  congr 1
  apply Complex.ext <;> simp <;> ring
theorem analyticAt_complexLine (a : imaginaryQuaternions) (v : ι → imaginaryQuaternions) (w : ι → ℝ)
    (z : ι → ℂ) : AnalyticAt ℂ (fun ζ => complexLine a v w ζ) z := by
  let Lm : (ι → ℂ) →L[ℂ] ComplexQuat :=
    ∑ l, (ContinuousLinearMap.proj l : (ι → ℂ) →L[ℂ] ℂ).smulRight ((w l : ℂ) • imagToComplex (v l))
  have h : (fun ζ => complexLine a v w ζ) = fun ζ => imagToComplex a + Lm ζ := by
    funext ζ
    simp [complexLine, Lm]
  rw [h]
  exact analyticAt_const.add (Lm.analyticAt z)
theorem norm_complexLine_le (a : imaginaryQuaternions) (v : ι → imaginaryQuaternions) {w : ι → ℝ}
    (hw : ∀ l, 0 ≤ w l) (ζ : ι → ℂ) :
    ‖complexLine a v w ζ‖ ≤ ‖a‖ + ∑ l, ‖ζ l‖ * (w l * ‖v l‖) := by
  refine (norm_add_le _ _).trans (add_le_add (norm_imagToComplex a).le ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun l _ => ?_)))
  rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw l), norm_imagToComplex]
theorem complexLine_bounds {β : Type} (s : Finset β) {p : ℝ} (hp : 1 ≤ p) (a : β → imaginaryQuaternions)
    (v : ι → β → imaginaryQuaternions) {w : ι → ℝ} (ζ : ι → ℂ) {c : ℝ} (hw : ∀ l, 0 ≤ w l)
    (hc : 2 * c ≤ 1 / 4000)
    (ha : finsetLpNorm p s (fun b => ‖a b‖) ≤ c)
    (hv : ∑ l, ‖ζ l‖ * (w l * finsetLpNorm p s (fun b => ‖v l b‖)) ≤ c) :
    (∀ b ∈ s, ‖complexLine (a b) (fun l => v l b) w ζ‖ ≤ 2 * c) ∧
      finsetLpNorm p s (fun b => ‖unitExp (complexLine (a b) (fun l => v l b) w ζ) - 1‖) ≤ 4 * c := by
  have hp0 : 0 < p := by linarith
  set f : β → ℝ := fun b => ‖a b‖ + ∑ l, ‖ζ l‖ * (w l * ‖v l b‖) with hf
  have hf0 : ∀ b, 0 ≤ f b := fun b =>
    add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun l _ =>
      mul_nonneg (norm_nonneg _) (mul_nonneg (hw l) (norm_nonneg _)))
  have h1 : finsetLpNorm p s f ≤ 2 * c := by
    refine (finsetLpNorm_add_le hp s _ _).trans ?_
    have h2 := finsetLpNorm_sum_le hp s (fun l b => ‖ζ l‖ * (w l * ‖v l b‖)) Finset.univ
    have h3 : ∀ l, finsetLpNorm p s (fun b => ‖ζ l‖ * (w l * ‖v l b‖)) =
        ‖ζ l‖ * (w l * finsetLpNorm p s (fun b => ‖v l b‖)) := fun l => by
      rw [finsetLpNorm_const_mul hp0 (norm_nonneg _), finsetLpNorm_const_mul hp0 (hw l)]
    simp only [h3] at h2
    linarith
  have h4 : ∀ b, ‖complexLine (a b) (fun l => v l b) w ζ‖ ≤ f b := fun b => norm_complexLine_le _ _ hw ζ
  have h5 : ∀ b ∈ s, f b ≤ 2 * c := fun b hb => by
    have := abs_le_finsetLpNorm hp0 hb f
    rw [abs_of_nonneg (hf0 b)] at this
    linarith
  refine ⟨fun b hb => (h4 b).trans (h5 b hb), ?_⟩
  have h6 : finsetLpNorm p s (fun b => ‖unitExp (complexLine (a b) (fun l => v l b) w ζ) - 1‖) ≤
      finsetLpNorm p s (fun b => 2 * f b) := by
    refine finsetLpNorm_mono hp0 s fun b hb => ?_
    have h7 := norm_unitExp_sub_one_le (((h4 b).trans (h5 b hb)).trans hc)
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by have := hf0 b; positivity)]
    have := h4 b
    linarith
  rw [finsetLpNorm_const_mul hp0 (by norm_num)] at h6
  linarith
def complexLineChart (U : ChainChart F) (A : ι → ChainChart F) (w : ι → ℝ) (ζ : ι → ℂ) :
    ComplexChainChart F :=
  ⟨chartShiftAlong U A (fun l => w l * (ζ l).re), chartShiftAlong (zeroChart F) A (fun l => w l * (ζ l).im)⟩
theorem complexifiedImaginary_complexLineChart_fine (U : ChainChart F) (A : ι → ChainChart F) (w : ι → ℝ)
    (ζ : ι → ℂ) (x : F.Site 0) (i : Fin 4) :
    complexifiedImaginary ((complexLineChart U A w ζ).re.fine x i) ((complexLineChart U A w ζ).im.fine x i) =
      complexLine (U.fine x i) (fun l => (A l).fine x i) w ζ :=
  complexifiedImaginary_eq_complexLine _ _ _ _
theorem complexifiedImaginary_complexLineChart_coarse (U : ChainChart F) (A : ι → ChainChart F) (w : ι → ℝ)
    (ζ : ι → ℂ) (j : ℕ) (x : F.Site (j + 1)) (i : Fin 4) :
    complexifiedImaginary ((complexLineChart U A w ζ).re.coarse j x i)
        ((complexLineChart U A w ζ).im.coarse j x i) =
      complexLine (U.coarse j x i) (fun l => (A l).coarse j x i) w ζ :=
  complexifiedImaginary_eq_complexLine _ _ _ _
theorem complexLineChart_complexify (U : ChainChart F) (A : ι → ChainChart F) (w : ι → ℝ) (t : ι → ℝ) :
    complexLineChart U A w (complexifyCLM t) = realChart (chartShiftAlong U A (fun l => w l * t l)) := by
  have him : chartShiftAlong (zeroChart F) A (fun l => w l * (complexifyCLM t l).im) =
      ⟨fun _ _ => 0, fun _ _ _ => 0⟩ := by
    simp only [chartShiftAlong, zeroChart, complexifyCLM_apply, Complex.ofReal_im, mul_zero, zero_smul,
      Finset.sum_const_zero, add_zero]
  have hre : (fun l => w l * (complexifyCLM t l).re) = fun l => w l * t l := by
    funext l
    simp [complexifyCLM_apply]
  simp only [complexLineChart, realChart, hre, him]
theorem levelDeviation_zero (R : F.FieldChain) (W : ComplexChainChart F) (x : F.Site 0) (i : Fin 4) :
    levelDeviation R W 0 x i = unitExp (complexifiedImaginary (W.re.fine x i) (W.im.fine x i)) - 1 := by apply _root_.YangMills.Construction.CellSources.levelDeviation_zero <;> assumption
end Family
section Chart
theorem analyticAt_complexTreeHolonomy {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {z : P}
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {D : Finset F.Cell} {X : P → F.ComplexField F.depth}
    (hX : ∀ b ∈ innerBonds D F.depth, AnalyticAt ℂ (fun w => X w b.1 b.2) z) {x : F.Site F.depth}
    (hx : x ∈ sitesOfCells D F.depth) :
    AnalyticAt ℂ (fun w => complexTreeHolonomy (X w) x) z := by
  obtain ⟨y, hy, h, hh, rfl⟩ := exists_cellSite_eq hx
  simp only [complexTreeHolonomy]
  rw [enclosingCell_cellSite hodd y hh, cellOffset_cellSite hamb hodd y hh]
  exact analyticAt_complexPathHolonomy (pathBondsSatisfy_axisPath _ hodd.pos
    (fun v hv k hk => hX (cellCentre F.depth y + siteOfCoords F.depth v, k)
      (cellCentre_add_mem_innerBonds hy hv hk)) hh 1)
theorem analyticAt_complexBalancingGauge_of_near {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {z : P}
    (hodd : Odd F.blockSide) {D : Finset F.Cell} {X : P → F.ComplexField F.depth} {R : F.GaugeField F.depth}
    {tt : ℝ} (ht : 0 ≤ tt) (hsm : 4 * (F.blockSide : ℝ) * tt ≤ 1 / 8)
    (hX : ∀ b ∈ innerBonds D F.depth, AnalyticAt ℂ (fun w => X w b.1 b.2) z)
    (hg : ∀ b ∈ innerBonds D F.depth, BondNearReal (X z) R tt b.1 b.2) {y : F.Cell} (hy : y ∈ D) :
    AnalyticAt ℂ (fun w => complexBalancingGauge (X w) R y) z := by
  refine analyticAt_complexBalancingGauge hodd R ht hsm (fun h hh π => ?_) (fun h hh π => ?_)
  · rw [refineSite_eq_cellCentre]
    exact analyticAt_complexPathHolonomy (pathBondsSatisfy_axisPath _ hodd.pos
      (fun v hv k hk => hX (cellCentre F.depth y + siteOfCoords F.depth v, k)
        (cellCentre_add_mem_innerBonds hy hv hk)) hh π)
  · rw [refineSite_eq_cellCentre]
    exact pathNearReal_axisPath _ hodd.pos (fun v hv k hk =>
      hg (cellCentre F.depth y + siteOfCoords F.depth v, k) (cellCentre_add_mem_innerBonds hy hv hk)) hh π
open Classical in
theorem analyticAt_complexGaugedBondElement {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {z : P}
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {D : Finset F.Cell} {X : P → F.ComplexField F.depth}
    {R : F.GaugeField F.depth} {tt : ℝ} (ht : 0 ≤ tt) (hsm : 4 * (F.blockSide : ℝ) * tt ≤ 1 / 8)
    (hX : ∀ b ∈ innerBonds D F.depth, AnalyticAt ℂ (fun w => X w b.1 b.2) z)
    (hg : ∀ b ∈ innerBonds D F.depth, BondNearReal (X z) R tt b.1 b.2) {T : P → ComplexQuat}
    (hT : AnalyticAt ℂ T z) {b : F.Site F.depth × Fin 4} (hb : b ∈ innerBonds D F.depth) :
    AnalyticAt ℂ (fun w => complexGaugedBondElement (X w) (complexBalancingGauge (X w) R) (T w) b) z := by
  obtain ⟨hx, hx'⟩ := mem_innerBonds_iff.1 hb
  have h1 := analyticAt_complexBalancingGauge_of_near hodd ht hsm hX hg
    (enclosingCell_mem_of_mem_sitesOfCells hodd hx)
  have h2 := analyticAt_complexBalancingGauge_of_near hodd ht hsm hX hg
    (enclosingCell_mem_of_mem_sitesOfCells hodd hx')
  have h3 := analyticAt_complexTreeHolonomy hamb hodd hX hx
  have h4 := analyticAt_complexTreeHolonomy hamb hodd hX hx'
  simp only [complexGaugedBondElement]
  refine ((((h1.mul h3).mul (hX b hb)).mul (analyticAt_adjugate h4)).mul (analyticAt_adjugate h2)).mul ?_
  by_cases hcr : IsCrossingBond b
  · simp only [if_pos hcr]
    exact analyticAt_adjugate hT
  · simp only [if_neg hcr]
    exact analyticAt_const
open Classical in
theorem complexGaugedBondElement_congr_top (X : F.ComplexField F.depth) (k : F.Cell → ComplexQuat)
    {T T' : ComplexQuat} {b : F.Site F.depth × Fin 4} (h : IsCrossingBond b → T = T') :
    complexGaugedBondElement X k T b = complexGaugedBondElement X k T' b := by
  by_cases hcr : IsCrossingBond b
  · rw [h hcr]
  · simp only [complexGaugedBondElement, if_neg hcr]
def imagToComplexCLM : imaginaryQuaternions →L[ℝ] ComplexQuat :=
  LinearMap.toContinuousLinearMap
    { toFun := imagToComplex
      map_add' := imagToComplex_add
      map_smul' := fun r a => by
        rw [imagToComplex_smul]
        exact Complex.coe_smul r _ }
theorem norm_imagToComplexCLM (a : imaginaryQuaternions) : ‖imagToComplexCLM a‖ = ‖a‖ := norm_imagToComplex a
theorem exists_leftInverse_imagToComplexCLM :
    ∃ P : ComplexQuat →L[ℝ] imaginaryQuaternions, ∀ a, P (imagToComplexCLM a) = a := by
  have hinj : LinearMap.ker (imagToComplexCLM : imaginaryQuaternions →ₗ[ℝ] ComplexQuat) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro a ha
    have h1 : ‖a‖ = 0 := by
      rw [← norm_imagToComplexCLM]
      have : imagToComplexCLM a = 0 := ha
      rw [this, norm_zero]
    exact norm_eq_zero.1 h1
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  refine ⟨LinearMap.toContinuousLinearMap g, fun a => ?_⟩
  exact LinearMap.congr_fun hg a
end Chart
section Extension
variable {ι : Type} [Fintype ι]
structure IsLogNearOne (Lg : ComplexQuat → ComplexQuat) (r : ℝ) : Prop where
  radius_pos : 0 < r
  analyticOnNhd : AnalyticOnNhd ℂ Lg (ball 1 r)
  norm_le : ∀ E ∈ ball (1 : ComplexQuat) r, ‖Lg E‖ ≤ 1
  exp_inverse : ∀ A : ComplexQuat, ‖A‖ < r → Lg (NormedSpace.exp A) = A
def complexLineBondElement (R : F.FieldChain) (V : F.GaugeField F.top) (b : F.Site F.depth × Fin 4)
    (U : ChainChart F) (A : ι → ChainChart F) (w : ι → ℝ) (ε : ι → imaginaryQuaternions) (ζ : ι → ℂ) :
    ComplexQuat :=
  complexGaugedBondElement (complexChartField R (complexLineChart U A w ζ) F.depth)
    (complexBalancingGauge (complexChartField R (complexLineChart U A w ζ) F.depth) (R F.depth))
    (unitExp (complexLine 0 ε w ζ) * ofUnit (V (enclosingCell b.1) b.2)) b
theorem isBoundedHolomorphicExtension_bondChartCoordinates (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {R : F.FieldChain} {V : F.GaugeField F.top} {D : Finset F.Cell}
    {b : F.Site F.depth × Fin 4} (hb : b ∈ innerBonds D F.depth) {c σ Gs r : ℝ} {Lg : ComplexQuat → ComplexQuat}
    (hLg : IsLogNearOne Lg r)
    (hc0 : 0 < c) (hc1 : 2 * c ≤ 1 / 4000) (hc2 : 4 * (F.blockSide : ℝ) * (16 * c) ≤ 1 / 1024)
    (hc3 : 16 * c < 1)
    (hσ : σ ≤ 1 / 64) (hδ1 : 14 * (20 * (F.blockSide : ℝ) * (16 * c) + 2 * c + Gs) ≤ 1)
    (hδ2 : 2 * (14 * (20 * (F.blockSide : ℝ) * (16 * c) + 2 * c + Gs)) < r)
    (href : ∀ j, j + 1 ≤ F.top → ∀ c ∈ innerBonds D (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy (R j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ)
    (hlev : ∀ W : ComplexChainChart F,
      Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D 0, ‖levelDeviation R W 0 b.1 b.2‖ ^ 4)) ≤ 4 * c →
      (∀ j, j + 1 < F.top →
        Real.sqrt (∑ c ∈ innerBonds D (j + 1), ‖levelSource W j c.1 c.2 - 1‖ ^ 2) ≤ 4 * c) →
      ∀ j, j < F.top → Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D j, ‖levelDeviation R W j b.1 b.2‖ ^ 4)) ≤ 16 * c)
    (hG : ‖((gaugedBondElement (R F.depth) (fun _ => 1) V b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Gs)
    (U : ChainChart F) (A : ι → ChainChart F) (e : ι → F.Site F.top → Fin 4 → imaginaryQuaternions)
    (ε : ι → imaginaryQuaternions)
    (hε : IsCrossingBond b → ∀ l, ε l = e l (enclosingCell b.1) b.2) (w q : ι → ℝ) (hw : ∀ l, 0 ≤ w l) {ρ : ℝ}
    (hρ : 0 < ρ)
    (hbud : ρ * ∑ l, w l * q l ≤ c)
    (hU4 : finsetLpNorm 4 (innerBonds D 0) (fun b => ‖U.fine b.1 b.2‖) ≤ c)
    (hUm : ∀ j, j + 1 < F.top → finsetLpNorm 2 (innerBonds D (j + 1)) (fun b => ‖U.coarse j b.1 b.2‖) ≤ c)
    (hA4 : ∀ l, finsetLpNorm 4 (innerBonds D 0) (fun b => ‖(A l).fine b.1 b.2‖) ≤ q l)
    (hAm : ∀ l j, j + 1 < F.top →
      finsetLpNorm 2 (innerBonds D (j + 1)) (fun b => ‖(A l).coarse j b.1 b.2‖) ≤ q l)
    (hεq : ∀ l, ‖ε l‖ ≤ q l) :
    IsBoundedHolomorphicExtension imagToComplexCLM
      (fun t : ι → ℝ => bondChartCoord R V b (chartShiftAlong U A (fun l => w l * t l))
        (topVariationAlong e (fun l => w l * t l)))
      (fun ζ => Lg (complexLineBondElement R V b U A w ε ζ)) ρ 1 := by
  classical
  set tt : ℝ := 16 * c with htt
  set δ : ℝ := 20 * (F.blockSide : ℝ) * tt + 2 * c + Gs with hδ
  have ht0 : 0 ≤ tt := by positivity
  have hsm : 4 * (F.blockSide : ℝ) * tt ≤ 1 / 8 := by linarith
  have hbudget : ∀ ζ ∈ ball (0 : ι → ℂ) ρ, ∀ x : ι → ℝ, (∀ l, x l ≤ q l) → (∀ l, 0 ≤ x l) →
      ∑ l, ‖ζ l‖ * (w l * x l) ≤ c := by
    intro ζ hζ x hx hx0
    have hz : ‖ζ‖ < ρ := by simpa using hζ
    refine le_trans (Finset.sum_le_sum fun l _ => ?_) ((Finset.mul_sum _ _ _).symm.le.trans hbud)
    have h1 : ‖ζ l‖ ≤ ρ := (norm_le_pi_norm ζ l).trans hz.le
    exact mul_le_mul h1 (mul_le_mul_of_nonneg_left (hx l) (hw l)) (mul_nonneg (hw l) (hx0 l)) hρ.le
  have hpt : ∀ ζ ∈ ball (0 : ι → ℂ) ρ,
      (∀ b' ∈ innerBonds D 0, ‖complexifiedImaginary ((complexLineChart U A w ζ).re.fine b'.1 b'.2)
        ((complexLineChart U A w ζ).im.fine b'.1 b'.2)‖ ≤ 2 * c) ∧
      (∀ j, j + 1 < F.top → ∀ b' ∈ innerBonds D (j + 1),
        ‖complexifiedImaginary ((complexLineChart U A w ζ).re.coarse j b'.1 b'.2)
          ((complexLineChart U A w ζ).im.coarse j b'.1 b'.2)‖ ≤ 2 * c) ∧
      ∀ j, j < F.top → ∀ b' ∈ innerBonds D j, ‖levelDeviation R (complexLineChart U A w ζ) j b'.1 b'.2‖ ≤ tt := by
    intro ζ hζ
    obtain ⟨u1, u2⟩ := complexLine_bounds (innerBonds D 0) (p := 4) (by norm_num) (fun b => U.fine b.1 b.2)
      (fun l b => (A l).fine b.1 b.2) ζ hw hc1 hU4
      (hbudget ζ hζ _ hA4 fun _ => finsetLpNorm_nonneg _ _ _)
    have hm := fun j (hj : j + 1 < F.top) => complexLine_bounds (innerBonds D (j + 1)) (p := 2) (by norm_num)
      (fun b => U.coarse j b.1 b.2) (fun l b => (A l).coarse j b.1 b.2) ζ hw hc1 (hUm j hj)
      (hbudget ζ hζ _ (fun l => hAm l j hj) fun _ => finsetLpNorm_nonneg _ _ _)
    refine ⟨fun b' hb' => ?_, fun j hj b' hb' => ?_, ?_⟩
    · rw [complexifiedImaginary_complexLineChart_fine]
      exact u1 b' hb'
    · rw [complexifiedImaginary_complexLineChart_coarse]
      exact (hm j hj).1 b' hb'
    · have hl := hlev (complexLineChart U A w ζ) (by
        rw [← finsetLpNorm_four]
        simp only [levelDeviation_zero, complexifiedImaginary_complexLineChart_fine]
        exact u2) (fun j hj => by
        rw [← finsetLpNorm_two]
        simp only [levelSource, complexifiedImaginary_complexLineChart_coarse]
        exact (hm j hj).2)
      intro j hj b' hb'
      have h1 := hl j hj
      rw [← finsetLpNorm_four] at h1
      have h2 := abs_le_finsetLpNorm (p := 4) (by norm_num) hb'
        (fun b : F.Site j × Fin 4 => ‖levelDeviation R (complexLineChart U A w ζ) j b.1 b.2‖)
      rw [abs_of_nonneg (norm_nonneg _)] at h2
      exact h2.trans h1
  have hgood : ∀ ζ ∈ ball (0 : ι → ℂ) ρ, ∀ b' ∈ innerBonds D F.depth,
      BondNearReal (complexChartField R (complexLineChart U A w ζ) F.depth) (R F.depth) tt b'.1 b'.2 :=
    fun ζ hζ b' hb' => by
    have h := (hpt ζ hζ).2.2 F.depth (by simp [BlockFrame.top]) b' hb'
    exact ⟨h, det_complexChartField_of_norm_lt_one R _ F.depth _ _ (lt_of_le_of_lt h hc3)⟩
  have hfield : ∀ ζ ∈ ball (0 : ι → ℂ) ρ, ∀ b' ∈ innerBonds D F.depth,
      AnalyticAt ℂ (fun ζ' => complexChartField R (complexLineChart U A w ζ') F.depth b'.1 b'.2) ζ :=
    fun ζ hζ b' hb' =>
    analyticAt_complexChartField hodd R (W := complexLineChart U A w) (z := ζ) ht0 hc3 hσ hc2
      (fun b'' _ => by
        simp only [complexifiedImaginary_complexLineChart_fine]
        exact analyticAt_complexLine _ _ _ _)
      (fun b'' hb'' => ((hpt ζ hζ).1 b'' hb'').trans (by linarith))
      (fun j _ b'' _ => by
        simp only [complexifiedImaginary_complexLineChart_coarse]
        exact analyticAt_complexLine _ _ _ _)
      (fun j hj b'' hb'' => ((hpt ζ hζ).2.1 j hj b'' hb'').trans (by linarith))
      (hpt ζ hζ).2.2 href F.depth (by simp [BlockFrame.top]) b' hb'
  have hline : ∀ ζ ∈ ball (0 : ι → ℂ) ρ, ‖complexLine 0 ε w ζ‖ ≤ c := fun ζ hζ => by
    have h1 := norm_complexLine_le 0 ε hw ζ
    have h2 := hbudget ζ hζ (fun l => ‖ε l‖) hεq fun _ => norm_nonneg _
    simp only [norm_zero, zero_add] at h1
    exact h1.trans h2
  have hnear : ∀ ζ ∈ ball (0 : ι → ℂ) ρ, ‖complexLineBondElement R V b U A w ε ζ - 1‖ ≤ 14 * δ := by
    intro ζ hζ
    set τ : ComplexQuat := unitExp (complexLine 0 ε w ζ) - 1 with hτ
    have hτn : ‖τ‖ ≤ 2 * c := by
      have h1 := norm_unitExp_sub_one_le ((hline ζ hζ).trans (by linarith))
      have h2 := hline ζ hζ
      rw [hτ]
      linarith
    have e1 : unitExp (complexLine 0 ε w ζ) = 1 + τ := by rw [hτ, add_sub_cancel]
    unfold complexLineBondElement
    rw [e1]
    exact norm_complexGaugedBondElement_sub_one_le hamb hodd (hgood ζ hζ) ht0 hsm hb (by rw [hδ]; linarith) hδ1
  have hmem : ∀ ζ ∈ ball (0 : ι → ℂ) ρ, complexLineBondElement R V b U A w ε ζ ∈ ball (1 : ComplexQuat) r :=
    fun ζ hζ => by
    rw [mem_ball, dist_eq_norm]
    have h1 := hnear ζ hζ
    have h2 : 0 ≤ 14 * δ := (norm_nonneg _).trans h1
    linarith
  refine ⟨hρ, fun ζ hζ => ?_, fun ζ hζ => hLg.norm_le _ (hmem ζ hζ), fun t ht => ?_⟩
  · have hT : AnalyticAt ℂ
        (fun ζ' => unitExp (complexLine 0 ε w ζ') * ofUnit (V (enclosingCell b.1) b.2)) ζ :=
      (analyticAt_unitExp (analyticAt_complexLine 0 ε w ζ) ((hline ζ hζ).trans (by linarith))).mul
        analyticAt_const
    have hE : AnalyticAt ℂ (fun ζ' => complexLineBondElement R V b U A w ε ζ') ζ :=
      analyticAt_complexGaugedBondElement hamb hodd ht0 hsm (hfield ζ hζ) (hgood ζ hζ) hT hb
    exact (hLg.analyticOnNhd _ (hmem ζ hζ)).comp hE
  · set ζ : ι → ℂ := complexifyCLM t with hζd
    have hζ : ζ ∈ ball (0 : ι → ℂ) ρ := by
      rw [mem_ball_zero_iff, hζd, norm_complexifyCLM]
      exact ht
    set U' := chartShiftAlong U A (fun l => w l * t l) with hU'
    set v := topVariationAlong e (fun l => w l * t l) with hv
    set X := chartField R U' F.depth with hX
    set G := gaugedBondElement X (chartGauge R U' F.top) (rotatedField v V) b with hGd
    have hcf : complexChartField R (complexLineChart U A w ζ) F.depth = complexifyField X := by
      rw [hζd, complexLineChart_complexify, complexChartField_realChart]
    have hlink : complexBalancingGauge (complexifyField X) (R F.depth) = fun y => ofUnit (chartGauge R U' F.top y) :=
      funext fun y => complexBalancingGauge_complexify X (R F.depth) y
    have hE : complexLineBondElement R V b U A w ε ζ = ofUnit G := by
      unfold complexLineBondElement
      rw [hcf, hlink, complexGaugedBondElement_congr_top _ _
        (T' := ofUnit (rotatedField v V (enclosingCell b.1) b.2)) ?_, complexGaugedBondElement_complexify]
      intro hcr
      have hl : complexLine 0 ε w ζ = complexifiedImaginary (v (enclosingCell b.1) b.2) 0 := by
        rw [complexifiedImaginary_zero]
        show _ = imagToComplex _
        simp only [complexLine, imagToComplex_zero, zero_add, hv, topVariationAlong, imagToComplex_sum,
          imagToComplex_smul, hε hcr]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [smul_smul, hζd, complexifyCLM_apply]
        push_cast
        ring_nf
      show _ = ofUnit (expUnit (v (enclosingCell b.1) b.2) * V (enclosingCell b.1) b.2)
      rw [hl, unitExp_complexifiedImaginary_zero, ofUnit_mul]
    have hGn : ‖(G : ℍ[ℝ]) - 1‖ ≤ 14 * δ := by
      rw [← norm_ofUnit_sub_one, ← hE]
      exact hnear ζ hζ
    have hre := re_nonneg_of_norm_sub_one_le_one (g := G) (hGn.trans hδ1)
    have hlog := hLg.exp_inverse (ofQuat ((unitLog G : imaginaryQuaternions) : ℍ[ℝ]))
      ((norm_ofQuat_unitLog_le hre).trans_lt (by linarith))
    rw [exp_ofQuat_unitLog hre] at hlog
    show imagToComplex (unitLog G) = Lg (complexLineBondElement R V b U A w ε ζ)
    rw [hE]
    exact hlog.symm
end Extension
section Scale
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem iteratedFDeriv_comp_diagonalScaling {m : ℕ} (f : (Fin m → ℝ) → E) (w : Fin m → ℝ)
    (hw : ∀ l, w l ≠ 0) :
    iteratedFDeriv ℝ m (fun t => f (fun l => w l * t l)) 0 (fun l => Pi.single l 1) =
      (∏ l, w l) • iteratedFDeriv ℝ m f 0 (fun l => Pi.single l 1) := by
  let Dl : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) :=
    LinearEquiv.piCongrRight fun l => LinearEquiv.smulOfNeZero ℝ ℝ (w l) (hw l)
  let Dc : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) := Dl.toContinuousLinearEquiv
  have hD : ∀ t l, Dc t l = w l * t l := fun t l => rfl
  have e : (fun t => f (fun l => w l * t l)) = f ∘ Dc := by
    funext t
    simp only [Function.comp_apply]
    congr 1
  have h := Dc.iteratedFDerivWithin_comp_right f (s := Set.univ) uniqueDiffOn_univ (x := 0) (Set.mem_univ _) m
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at h
  rw [e, h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe, map_zero]
  have hs : (fun l => Dc (Pi.single l 1 : Fin m → ℝ)) = fun l => w l • (Pi.single l 1 : Fin m → ℝ) := by
    funext l l'
    rw [hD]
    by_cases hl : l' = l
    · subst hl
      simp
    · simp [hl]
  rw [hs, ContinuousMultilinearMap.map_smul_univ]
theorem le_mul_prod_of_scaled {m : ℕ} {x C : ℝ} (q : Fin m → ℝ) (hq : ∀ l, 0 ≤ q l)
    (h : ∀ w : Fin m → ℝ, (∀ l, 0 < w l) → (∀ l, w l * q l ≤ 1) → (∏ l, w l) * x ≤ C) :
    x ≤ C * ∏ l, q l := by
  have hlim : Filter.Tendsto (fun ε : ℝ => C * ∏ l, (q l + ε)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (C * ∏ l, (q l + 0))) := by
    have hc : Continuous fun ε : ℝ => C * ∏ l, (q l + ε) := by fun_prop
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  simp only [add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (0 : ℝ) < ε := hε
  have hpos : ∀ l, 0 < q l + ε := fun l => by linarith [hq l]
  have h1 := h (fun l => (q l + ε)⁻¹) (fun l => inv_pos.2 (hpos l)) (fun l => by
    rw [inv_mul_le_iff₀ (hpos l)]
    linarith)
  have hP : 0 < ∏ l, (q l + ε) := Finset.prod_pos fun l _ => hpos l
  rw [Finset.prod_inv_distrib, inv_mul_le_iff₀ hP] at h1
  linarith
end Scale
section Cells
theorem bond_interior_or_crossing (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {S : Finset F.Cell}
    {y : F.Cell} {h : Lattice4} {i : Fin 4} (hh : h ∈ centredCube F.blockSide)
    (hb : cellSite y h + unitStep F.depth i ∈ sitesOfCells S F.depth) :
    (h + basisVector i ∈ centredCube F.blockSide ∧ ¬ IsCrossingBond (cellSite y h, i)) ∨
      (IsCrossingBond (cellSite y h, i) ∧ h i = ((F.blockSide : ℤ) - 1) / 2 ∧
        y + siteOfCoords F.top (basisVector i) ∈ S ∧
        h + basisVector i - (F.blockSide : ℤ) • basisVector i ∈ centredCube F.blockSide) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.bond_cases <;> assumption
theorem mem_sitesOfCells_of_enclosingCell_mem (hodd : Odd F.blockSide) {S D : Finset F.Cell}
    {x : F.Site F.depth} (hx : x ∈ sitesOfCells S F.depth) (hD : enclosingCell x ∈ D) :
    x ∈ sitesOfCells D F.depth := by
  obtain ⟨y, hy, g, hg, rfl⟩ := exists_cellSite_eq hx
  rw [enclosingCell_cellSite hodd y hg] at hD
  exact cellSite_mem_sitesOfCells hD hg
theorem cellSupDist_enclosingCell_bond_le_one (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S : Finset F.Cell} {b : F.Site F.depth × Fin 4} (hb : b ∈ innerBonds S F.depth) :
    cellSupDist (enclosingCell b.1) (enclosingCell (b.1 + unitStep F.depth b.2)) ≤ 1 := by
  obtain ⟨x, i⟩ := b
  obtain ⟨hx, hx'⟩ := mem_innerBonds_iff.1 hb
  simp only at hx hx' ⊢
  obtain ⟨y, hy, h, hh, rfl⟩ := exists_cellSite_eq hx
  rw [enclosingCell_cellSite hodd y hh]
  rcases bond_interior_or_crossing hamb hodd (i := i) hh hx' with ⟨hc, hnc⟩ | ⟨hcr, hi, hE, h1c⟩
  · rw [cellSite_add_unitStep, enclosingCell_cellSite hodd y hc]
    simp [cellSupDist]
  · have hsite : cellSite y h + unitStep F.depth i =
        cellSite (y + siteOfCoords F.top (basisVector i)) (h + basisVector i - (F.blockSide : ℤ) • basisVector i) := by
      rw [cellSite_add_basisVector, cellSite_add_unitStep, sub_add_cancel]
    rw [hsite, enclosingCell_cellSite hodd _ h1c]
    have h1 := cellSupDist_add_le hamb (y + siteOfCoords F.top (basisVector i)) (a := - basisVector i) (r := 1)
      (by norm_num) (fun μ => by
      by_cases hμ : μ = i
      · subst hμ
        simp [basisVector]
      · simp [basisVector, hμ])
    rwa [siteOfCoords_neg, add_neg_cancel_right] at h1
end Cells
open Classical in
def crossingRotation (b : F.Site F.depth × Fin 4) (e : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    imaginaryQuaternions :=
  if IsCrossingBond b then e (enclosingCell b.1) b.2 else 0
def bondCells (b : F.Site F.depth × Fin 4) : Finset F.Cell := by
  classical exact {enclosingCell b.1, enclosingCell (b.1 + unitStep F.depth b.2)}
theorem mem_bondCells {b : F.Site F.depth × Fin 4} {u : F.Cell} :
    u ∈ bondCells b ↔ u = enclosingCell b.1 ∨ u = enclosingCell (b.1 + unitStep F.depth b.2) := by
  classical
  simp [bondCells]
theorem card_bondCells_le (b : F.Site F.depth × Fin 4) : (bondCells b).card ≤ 81 := by
  classical
  unfold bondCells
  exact (Finset.card_le_two).trans (by norm_num)
theorem bondCells_subset (hodd : Odd F.blockSide) {S : Finset F.Cell} {b : F.Site F.depth × Fin 4}
    (hb : b ∈ innerBonds S F.depth) : bondCells b ⊆ S := by
  obtain ⟨hx, hx'⟩ := mem_innerBonds_iff.1 hb
  intro u hu
  rcases mem_bondCells.1 hu with rfl | rfl
  · exact enclosingCell_mem_of_mem_sitesOfCells hodd hx
  · exact enclosingCell_mem_of_mem_sitesOfCells hodd hx'
theorem mem_innerBonds_bondCells (hodd : Odd F.blockSide) {S : Finset F.Cell} {b : F.Site F.depth × Fin 4}
    (hb : b ∈ innerBonds S F.depth) : b ∈ innerBonds (bondCells b) F.depth := by
  obtain ⟨hx, hx'⟩ := mem_innerBonds_iff.1 hb
  exact mem_innerBonds_iff.2 ⟨mem_sitesOfCells_of_enclosingCell_mem hodd hx (mem_bondCells.2 (Or.inl rfl)),
    mem_sitesOfCells_of_enclosingCell_mem hodd hx' (mem_bondCells.2 (Or.inr rfl))⟩
theorem cellSupDist_bondCells_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {S : Finset F.Cell}
    {b : F.Site F.depth × Fin 4} (hb : b ∈ innerBonds S F.depth) :
    ∀ u ∈ bondCells b, cellSupDist (enclosingCell b.1) u ≤ 3 := by
  intro u hu
  rcases mem_bondCells.1 hu with rfl | rfl
  · simp [cellSupDist]
  · exact (cellSupDist_enclosingCell_bond_le_one hamb hodd hb).trans (by norm_num)
theorem innerBonds_bondCells_subset_bondsOver (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S : Finset F.Cell} {b : F.Site F.depth × Fin 4} (hb : b ∈ chordBonds S) (j : ℕ) :
    innerBonds (bondCells b) j ⊆ bondsOver S (cellBall S (enclosingCell b.1) 3) j := by
  classical
  have hbS : b ∈ innerBonds S F.depth := (Finset.mem_filter.1 hb).1
  exact innerBonds_subset_bondsOver hodd (bondCells_subset hodd hbS) (cellSupDist_bondCells_le hamb hodd hbS) j
structure SmallOnBondCells (b : F.Site F.depth × Fin 4) (c : ℝ) (U : ChainChart F) : Prop where
  fine : finsetLpNorm 4 (innerBonds (bondCells b) 0) (fun b => ‖U.fine b.1 b.2‖) ≤ c
  coarse : ∀ j, j + 1 < F.top →
    finsetLpNorm 2 (innerBonds (bondCells b) (j + 1)) (fun b => ‖U.coarse j b.1 b.2‖) ≤ c
structure SizedOnBondCells (b : F.Site F.depth × Fin 4) (q : ℝ) (A : ChainChart F)
    (e : F.Site F.top → Fin 4 → imaginaryQuaternions) : Prop where
  fine : finsetLpNorm 4 (innerBonds (bondCells b) 0) (fun b => ‖A.fine b.1 b.2‖) ≤ q
  coarse : ∀ j, j + 1 < F.top →
    finsetLpNorm 2 (innerBonds (bondCells b) (j + 1)) (fun b => ‖A.coarse j b.1 b.2‖) ≤ q
  rearrangedPathCorner : ‖crossingRotation b e‖ ≤ q
theorem sizedOnBondCells_localDirectionSize (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S : Finset F.Cell} {R : F.FieldChain}
    {b : F.Site F.depth × Fin 4} (hb : b ∈ chordBonds S) (A : ChainChart F)
    (e : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    SizedOnBondCells b (localDirectionSize S R (topBondsAt b) (enclosingCell b.1) A e) A e := by
  classical
  have hts : 0 ≤ topVariationNorm (topBondsAt b) e := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hnn : 0 ≤ localNorm S R A (oneSiteWeights F) (enclosingCell b.1) := Real.sqrt_nonneg _
  refine ⟨(finsetLpNorm_fine_le_localNorm S R A _ (innerBonds_bondCells_subset_bondsOver hamb hodd hb 0)).trans ?_,
    fun j hj => (finsetLpNorm_coarse_le_localNorm S R A _ hj
      (innerBonds_bondCells_subset_bondsOver hamb hodd hb (j + 1))).trans ?_, ?_⟩
  · simp only [localDirectionSize]
    linarith
  · simp only [localDirectionSize]
    linarith
  · simp only [localDirectionSize]
    by_cases hcr : IsCrossingBond b
    · simp only [crossingRotation, if_pos hcr, topVariationNorm, topBondsAt, Finset.sum_singleton]
      linarith
    · simp only [crossingRotation, if_neg hcr, norm_zero]
      linarith
set_option maxHeartbeats 1000000 in
open Classical in
theorem exists_bounded_extension_bondChartCoords (hB : referenceBoundsStatement)
    (hRf : referenceChordNearOneStatement)
    (hrec : UniformQuarticBoundAcrossLevels) : ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c : ℝ, 0 < c ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V → ∀ b ∈ chordBonds S,
          ∀ U : ChainChart F, SmallOnBondCells b c U → ∀ (ι : Type) [Fintype ι] (A : ι → ChainChart F)
            (e : ι → F.Site F.top → Fin 4 → imaginaryQuaternions) (w q : ι → ℝ) (ρ : ℝ), (∀ l, 0 ≤ w l) → 0 < ρ →
            ρ * ∑ l, w l * q l ≤ c → (∀ l, SizedOnBondCells b (q l) (A l) (e l)) →
            ∃ g, IsBoundedHolomorphicExtension imagToComplexCLM
              (fun t : ι → ℝ => bondChartCoord (referenceFieldChain S V) V b
                (chartShiftAlong U A (fun l => w l * t l)) (topVariationAlong e (fun l => w l * t l))) g ρ 1 := by
  obtain ⟨C, c0, L1, hC, hc0, hbd⟩ := hB
  obtain ⟨L2, hRef⟩ := hRf
  obtain ⟨Lg, r, hr, hLa, hLb, hLi⟩ := exists_analytic_log_near_one
  have hLg : IsLogNearOne Lg r := ⟨hr, hLa, hLb, hLi⟩
  obtain ⟨P, hP⟩ := exists_leftInverse_imagToComplexCLM
  refine ⟨max (max L1 L2) 5, fun L hL hge => ?_⟩
  have hL1 : L1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hge)
  have hL2 : L2 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hge)
  have hL5 : 5 ≤ L := (le_max_right _ _).trans hge
  obtain ⟨cR, CR, hcR, hCR, href⟩ := hRef L hL hL2
  obtain ⟨cL, hcL, -, hlev⟩ := quartic_levelDeviation_bound hrec L hL hL5 (C₀ := C) hC.le
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL.pos
  set K₁ : ℝ := 320 * L + 2 + CR with hK₁
  have hK₁0 : 0 < K₁ := by positivity
  set κ : ℝ := min 1 (r / 2) with hκ
  have hκ0 : 0 < κ := lt_min one_pos (half_pos hr)
  set c : ℝ := min (min c0 cR) (min (cL / 4) (min (1 / (64 * (C + 1))) (min (1 / (65536 * L))
    (min (1 / 8000) (κ / (28 * K₁)))))) with hcdef
  have hcpos : 0 < c := by
    refine lt_min (lt_min hc0 hcR) (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by positivity)))))
  have hcc0 : c ≤ c0 := (min_le_left _ _).trans (min_le_left _ _)
  have hccR : c ≤ cR := (min_le_left _ _).trans (min_le_right _ _)
  have hccL : c ≤ cL / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hcC : c ≤ 1 / (64 * (C + 1)) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcLL : c ≤ 1 / (65536 * L) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hc8 : c ≤ 1 / 8000 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hcκ : c ≤ κ / (28 * K₁) := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hκ2 : κ ≤ r / 2 := min_le_right _ _
  have hK28 : 28 * K₁ * c ≤ κ := by
    rw [le_div_iff₀ (by positivity)] at hcκ
    linarith
  have hLc : 65536 * (L : ℝ) * c ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hcLL
    linarith
  clear_value c
  refine ⟨c, hcpos, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsc hcold b hb
  have hodd : Odd F.blockSide := hFL ▸ hL
  have hLF : (F.blockSide : ℝ) = L := by rw [hFL]
  obtain ⟨-, -, -, -, b5, -⟩ := hbd F m S hodd (hFL ▸ hL1) hamb hm hreg s V hs (hsc.trans hcc0) hcold
  have hGr := href F m S hFL hamb hm hreg s V hs (hsc.trans hccR) hcold b hb
  set R := referenceFieldChain S V with hRdef
  have hbS : b ∈ innerBonds S F.depth := (Finset.mem_filter.1 hb).1
  set y := enclosingCell b.1 with hy
  set D : Finset F.Cell := bondCells b with hDdef
  have hDS : D ⊆ S := bondCells_subset hodd hbS
  have hbD : b ∈ innerBonds D F.depth := mem_innerBonds_bondCells hodd hbS
  have hcard : D.card ≤ 81 := card_bondCells_le b
  have hbm : ∀ j, innerBonds D j ⊆ innerBonds S j := fun j b' hb' => by
    obtain ⟨h1, h2⟩ := mem_innerBonds_iff.1 hb'
    exact mem_innerBonds_iff.2 ⟨sitesOfCells_subset hDS j h1, sitesOfCells_subset hDS j h2⟩
  have hsL : s ≤ cL := by
    have : c ≤ cL := by linarith
    exact hsc.trans this
  have hsC : C * s ≤ 1 / 64 := by
    have h1 : s ≤ 1 / (64 * (C + 1)) := hsc.trans hcC
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hnearR : ContoursNearUnit R D C s := by
    intro j hj c' hc' h hh π
    rw [norm_ofUnit_sub_one]
    exact b5 j (by omega) c' (hbm _ hc') h hh π
  have hrefD : ∀ j, j + 1 ≤ F.top → ∀ c' ∈ innerBonds D (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy (R j) (refineSite c'.1) (bondContour F.blockSide h π c'.2) *
        (polarUnit (contourAverage (R j) c'))⁻¹) - 1‖ ≤ C * s := by
    intro j hj c' hc' h hh π
    refine (hnearR j hj c' hc' h hh π).trans ?_
    have h1 : ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 ≤ 1 :=
      pow_le_one₀ (by positivity) (ComplexLevels.inv_pow_le_one hodd.pos _)
    exact mul_le_of_le_one_right (by positivity) h1
  have hlevD : ∀ W : ComplexChainChart F,
      Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D 0, ‖levelDeviation R W 0 b.1 b.2‖ ^ 4)) ≤ 4 * c →
      (∀ j, j + 1 < F.top →
        Real.sqrt (∑ c' ∈ innerBonds D (j + 1), ‖levelSource W j c'.1 c'.2 - 1‖ ^ 2) ≤ 4 * c) →
      ∀ j, j < F.top → Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D j, ‖levelDeviation R W j b.1 b.2‖ ^ 4)) ≤ 16 * c :=
    fun W h0 hsrc j hj => (hlev F D R W s (4 * c) hFL hcard hnearR hs.le hsL (by positivity) (by linarith)
      h0 hsrc j hj).trans (by linarith)
  have hGs : ‖((gaugedBondElement (R F.depth) (fun _ => 1) V b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ CR * s := hGr
  have hCRs : CR * s ≤ CR * c := mul_le_mul_of_nonneg_left hsc hCR.le
  have hδK : 20 * (F.blockSide : ℝ) * (16 * c) + 2 * c + CR * s ≤ K₁ * c := by
    rw [hLF, hK₁]
    nlinarith
  intro U hU ι _ A e w q ρ hw hρ hbud hsz
  exact ⟨_, isBoundedHolomorphicExtension_bondChartCoordinates hamb hodd hbD hLg hcpos (by linarith)
    (by rw [hLF]; nlinarith) (by linarith) hsC
    (by
      have : 14 * (K₁ * c) ≤ κ / 2 := by linarith
      linarith)
    (by
      have : 2 * (14 * (K₁ * c)) ≤ κ := by linarith
      have h2 : κ ≤ r / 2 := hκ2
      have h3 : 0 < r := hr
      linarith) hrefD hlevD hGs U A e (fun l => crossingRotation b (e l))
    (fun hcr l => by simp [crossingRotation, hcr]) w q hw hρ hbud
    hU.fine hU.coarse (fun l => (hsz l).fine) (fun l j hj => (hsz l).coarse j hj) (fun l => (hsz l).rearrangedPathCorner)⟩
end YangMills.Construction.ComplexLineChart
end

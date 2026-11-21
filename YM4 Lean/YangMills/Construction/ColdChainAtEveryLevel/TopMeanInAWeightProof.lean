import YangMills.Construction.ColdChainAtEveryLevel.CellNormsOfTheClassWeights
import YangMills.Construction.ColdChainAtEveryLevel.RealPointsOfAComplexFamily
import YangMills.Construction.ColdChainAtEveryLevel.SecondDifferenceOfTheTotal
import YangMills.Construction.ColdChainAtEveryLevel.TopMeanInAWeight
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction
namespace TopAverageBound
open BlockAverages LevelRecursion ComplexLevels HullBounds ComplexRemainders SmallMultiples LowerLevelTerms
  TopLevelTerms BondSecondDifference RealChartTerms BlockLines RealDirections ComplexDifferences Filter Topology
variable {F : BlockFrame}
private theorem le_baseTransport_add_sum {D : Finset F.Cell} (hodd : Odd F.blockSide)
    (a : (m : ℕ) → F.Site m → Fin 4 → ℝ) (s' : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ)
    (hrec : ∀ m, m < F.top → ∀ c ∈ innerBonds D (m + 1),
      a (m + 1) c.1 c.2 ≤ lineBlockAverage (a m) c + s' m c.1 c.2)
    (m : ℕ) (hm : m ≤ F.top) : ∀ b ∈ innerBonds D m, a m b.1 b.2 ≤
      baseTransport (a 0) m b.1 b.2 + ∑ i ∈ Finset.range m, sourceTransport s' i m b.1 b.2 := by apply _root_.YangMills.Construction.BlockAverages.FirstVariation.le_baseTransport_add_sum <;> assumption
private theorem weightedScaleNorm_linearPart_top_le (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    {R : F.FieldChain} (A : ChainChart F) {D : Finset F.Cell}
    (hD : D.card ≤ 81) (p : F.Site 0) {ϑ : ℝ} (hϑ : |ϑ| ≤ 1 / 8) {n2 : ℝ} (hn2 : 0 ≤ n2)
    (hmu : ∀ m, m + 1 < F.top →
      weightedScaleNorm D p ϑ 2 (m + 1) (fun y d => ‖(A.coarse m y d : ℍ[ℝ])‖) ≤ n2) :
    weightedScaleNorm D p ϑ 2 (F.depth + 1) (fun y d => ‖linearPart R A (F.depth + 1) y d‖) ≤
      5 * (20000 * weightedScaleNorm D p ϑ 4 0 (fun x i => ‖(A.fine x i : ℍ[ℝ])‖)) + 284 * n2 := by
  classical
  set a : (m : ℕ) → F.Site m → Fin 4 → ℝ := fun m x d => ‖linearPart R A m x d‖ with ha
  set sf : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ :=
    fun m y d => if m + 1 < F.top then ‖(A.coarse m y d : ℍ[ℝ])‖ else 0 with hsf
  have hsf0 : ∀ m y d, 0 ≤ sf m y d := fun m y d => by
    simp only [hsf]
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  have hrec : ∀ m, m < F.top → ∀ c ∈ innerBonds D (m + 1),
      a (m + 1) c.1 c.2 ≤ lineBlockAverage (a m) c + sf m c.1 c.2 := by
    intro m _ c _
    have e0 : linearPart R A (m + 1) c.1 c.2 = parallelAverage (R m) (linearPart R A m) (c.1, c.2) +
        (if m + 1 < F.top then ((A.coarse m c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) else 0) := rfl
    have h1 := norm_parallelAverage_le_lineBlockAverage hodd (R m) (linearPart R A m) c
    show ‖linearPart R A (m + 1) c.1 c.2‖ ≤ _
    rw [e0]
    refine (norm_add_le _ _).trans (add_le_add h1 ?_)
    simp only [hsf]
    split_ifs
    · exact le_rfl
    · simp
  have h1 := le_baseTransport_add_sum (D := D) hodd a sf hrec (F.depth + 1) (by simp [BlockFrame.top])
  have h2' : weightedScaleNorm D p ϑ 2 (F.depth + 1) (fun y d => ‖linearPart R A (F.depth + 1) y d‖) ≤
      weightedScaleNorm D p ϑ 2 (F.depth + 1) (fun y d => baseTransport (a 0) (F.depth + 1) y d +
        ∑ i ∈ Finset.range (F.depth + 1), sourceTransport sf i (F.depth + 1) y d) := by
    refine weightedScaleNorm_mono_of_abs_le (by norm_num) D p ϑ (F.depth + 1) fun b hb => ?_
    rw [abs_of_nonneg (norm_nonneg _)]
    exact (h1 b hb).trans (le_abs_self _)
  refine h2'.trans ((weightedScaleNorm_add_le D p ϑ (by norm_num) _ _ _).trans (add_le_add ?_ ?_))
  · have ha0 : ∀ x d, 0 ≤ a 0 x d := fun _ _ => norm_nonneg _
    have h3 := (baseTransport_norm_le hodd h2 D p hϑ (a 0) ha0 (F.depth + 1) (by simp [BlockFrame.top])).1
    have h4 := LevelRecursion.weightedScaleNorm_two_le_four hodd hD p ϑ (F.depth + 1)
      (baseTransport (a 0) (F.depth + 1))
    have eQ : ((F.blockSide ^ (F.top - (F.depth + 1)) : ℕ) : ℝ) = 1 := by
      have : F.top - (F.depth + 1) = 0 := by simp [BlockFrame.top]
      rw [this]
      simp
    rw [eQ] at h4
    refine h4.trans ?_
    have e1 : weightedScaleNorm D p ϑ 4 0 (a 0) =
        weightedScaleNorm D p ϑ 4 0 (fun x i => ‖(A.fine x i : ℍ[ℝ])‖) := rfl
    rw [e1] at h3
    linarith
  · have hsum : weightedScaleNorm D p ϑ 2 (F.depth + 1)
        (fun y d => ∑ i ∈ Finset.range (F.depth + 1), sourceTransport sf i (F.depth + 1) y d) ≤
        ∑ i ∈ Finset.range (F.depth + 1), weightedScaleNorm D p ϑ 2 (F.depth + 1) (sourceTransport sf i (F.depth + 1)) := by
      unfold weightedScaleNorm
      refine le_trans (le_of_eq ?_) (finsetLpNorm_sum_le (by norm_num) _ _ _)
      congr 1
      funext b
      rw [Finset.mul_sum]
    refine hsum.trans ?_
    have hL2 : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast h2
    have hterm : ∀ i ∈ Finset.range (F.depth + 1),
        weightedScaleNorm D p ϑ 2 (F.depth + 1) (sourceTransport sf i (F.depth + 1)) ≤
        142 * (1 / (F.blockSide : ℝ)) ^ (F.depth + 1 - 1 - i) * n2 := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have h3 := sourceTransport_norm_le hodd h2 D p hϑ sf hsf0 i (F.depth + 1) hi' (by simp [BlockFrame.top])
      refine h3.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      by_cases hc : i + 1 < F.top
      · have e : sf i = fun y d => ‖(A.coarse i y d : ℍ[ℝ])‖ := by
          funext y d
          simp only [hsf, if_pos hc]
        rw [e]
        exact hmu i hc
      · have e : sf i = fun _ _ => 0 := by
          funext y d
          simp only [hsf, if_neg hc]
        have e0 : weightedScaleNorm D p ϑ 2 (i + 1) (fun _ _ => 0) = 0 := by
          unfold weightedScaleNorm finsetLpNorm
          simp
        rw [e, e0]
        exact hn2
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have h4 := sum_inv_pow_le_two hL2 (F.depth + 1)
    nlinarith
private theorem scaleWeight_top (p : F.Site 0) (ϑ : ℝ) (x : F.Site (F.depth + 1)) :
    scaleWeight p ϑ (F.depth + 1) x = ((F.blockSide : ℝ) ^ F.top) ^ (-ϑ) := by
  unfold scaleWeight scaleRadius
  rw [min_eq_left (le_max_left _ _)]
private theorem rpow_mul_le_weightedScaleNorm_top {D : Finset F.Cell} (p : F.Site 0) (θ : ℝ) {P : ℕ} (hP : 1 ≤ P)
    (f : F.Site (F.depth + 1) → Fin 4 → ℝ) (hf : ∀ x d, 0 ≤ f x d) {b : F.Site (F.depth + 1) × Fin 4}
    (hb : b ∈ innerBonds D (F.depth + 1)) (hL : 0 < F.blockSide) :
    ((F.blockSide : ℝ) ^ F.top) ^ θ * f b.1 b.2 ≤ weightedScaleNorm D p (-θ) P (F.depth + 1) f := by
  have h := abs_le_finsetLpNorm hP (innerBonds D (F.depth + 1))
    (fun b => scaleWeight p (-θ) (F.depth + 1) b.1 * f b.1 b.2) hb
  rw [scaleWeight_top, neg_neg] at h
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
    positivity
  rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hN.le _) (hf _ _))] at h
  exact h
private def linearCoefficient (L : ℕ) : ℝ :=
  hullFactor L * (284 * (5 * (4 + 200000 * (L : ℝ) ^ 2) * (hullFactor L * 82272))) +
    200000 * (L : ℝ) ^ 2 * (5 * (hullFactor L * 82272))
private def quadraticCoefficient (L : ℕ) (Ln : ℝ) : ℝ :=
  hullFactor L * (142 * (5 * Ln) + 284 * (3 + 5 * (200000 * (L : ℝ) ^ 2) * Ln * (hullFactor L * 82272))) +
    200000 * (L : ℝ) ^ 2 * (5 * (hullFactor L * 82272))
private theorem linearPartError_smul_eq (L : ℕ) (Ln x M Ba ε : ℝ) :
    linearPartError L Ln x (ε * M) (ε * Ba) =
      ε * (x * Ba * linearCoefficient L) + ε ^ 2 * (M * Ba * quadraticCoefficient L Ln) := by
  unfold linearPartError linearCoefficient quadraticCoefficient
  ring
private def velocityConstant (L : ℕ) : ℝ :=
  2 * linearCoefficient L + 200000 * (L : ℝ) ^ 2 * (hullFactor L * 82272)
set_option maxHeartbeats 2000000 in
private theorem gaugedBondAverage_chartMove_sub_le (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    {D : Finset F.Cell} (hD : D.card ≤ 81) {p : F.Site 0}
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {A : ChainChart F} {C₀ s Bu Ba c : ℝ}
    (hC : 0 < C₀) (hs : 0 < s) (hs1 : s ≤ 1) (hx : C₀ * s ≤ smallnessThreshold F.blockSide) (hx1 : C₀ * s ≤ 1)
    (ref : ReferenceNear D R C₀ s)
    (hc : 0 < c) (hcb : ∀ (W : ChainChart F) (B : ℝ), 0 ≤ B → B ≤ c →
      finsetLpNorm 4 (innerBonds D 0) (fun b => ‖(W.fine b.1 b.2 : ℍ[ℝ])‖) ≤ B →
      (∀ j, j + 1 < F.top →
        finsetLpNorm 2 (innerBonds D (j + 1)) (fun b => ‖(W.coarse j b.1 b.2 : ℍ[ℝ])‖) ≤ B) →
      DeviationBall R D (realChart W) (4 * B) (4 * B))
    (nm : PairWeightedNorms D p θ (zeroChart F) A Bu Ba) (hBu : 0 ≤ Bu) (hBa : 0 ≤ Ba)
    {b : F.Site (F.depth + 1) × Fin 4} (hb : b ∈ innerBonds D (F.depth + 1)) :
    ∃ (Y ε₀ : ℝ), 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ((F.blockSide : ℝ) ^ F.top) ^ θ * ‖gaugedBondAverage R (chartMove (zeroChart F) A ε) F.depth b *
          (((polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b))⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
          gaugedBondAverage R (zeroChart F) F.depth b *
            (((polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b))⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
          ε • linearPart R A (F.depth + 1) b.1 b.2‖ ≤
        ε * (C₀ * s * (Ba * velocityConstant F.blockSide) + ((F.blockSide : ℝ) ^ F.top) ^ θ * (C₀ * s) *
          ‖linearPart R A (F.depth + 1) b.1 b.2‖) + ε ^ 2 * Y := by
  have hL : 0 < F.blockSide := hodd.pos
  have hN0 : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  set Nθ := ((F.blockSide : ℝ) ^ F.top) ^ θ with hNθ
  have hNθ0 : 0 < Nθ := Real.rpow_pos_of_pos hN0 _
  set U := zeroChart F with hU
  set Q := pairSize D U A with hQ
  have hQ0 : 0 ≤ Q := pairSize_nonneg D U A
  have hH0 := hullBondCount_nonneg F.blockSide
  have hF0 := hullFactor_nonneg (F := F) hodd
  set Sm := ∑ c ∈ innerBonds D (F.depth + 1), (topLinearSize R U c.1 c.2 + topLinearSize R A c.1 c.2) with hSm
  have hSm0 : 0 ≤ Sm := Finset.sum_nonneg fun c _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
  set M := Q + 8 * (hullBondCount F.blockSide * Q) + Bu + Ba + Sm with hM
  have hM0 : 0 ≤ M := by positivity
  set κ := smallnessThreshold F.blockSide with hκ
  have hκ0 : 0 < κ := SecondDifferences.smallnessThreshold_pos hodd
  set e := min (min κ (1 / 16000)) c with he
  have he0 : 0 < e := lt_min (lt_min hκ0 (by norm_num)) hc
  set Z := 1 + hullBondCount F.blockSide + hullFactor F.blockSide with hZ
  set Dn := 1 + M + 4 * Q * Z + Q with hDn
  have hDn0 : 0 < Dn := by positivity
  set K := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set x := C₀ * s with hxd
  have hx0 : 0 ≤ x := by positivity
  refine ⟨2 * (M * Ba * quadraticCoefficient F.blockSide ((F.blockSide : ℝ) ^ F.top)) +
    K * M * (hullFactor F.blockSide * 82272) * Ba, e / Dn, by positivity, fun ε hε hεl => ?_⟩
  have hεD : ε * Dn < e := by
    rwa [lt_div_iff₀ hDn0] at hεl
  have hε0 : 0 ≤ ε := hε.le
  have le1 : ∀ X : ℝ, X ≤ Dn → ε * X ≤ e := fun X hX => (mul_le_mul_of_nonneg_left hX hε0).trans hεD.le
  have eκ : e ≤ κ := (min_le_left _ _).trans (min_le_left _ _)
  have e16 : e ≤ 1 / 16000 := (min_le_left _ _).trans (min_le_right _ _)
  have ec : e ≤ c := min_le_right _ _
  have hMD : M ≤ Dn := by
    have : 0 ≤ 4 * Q * Z := by positivity
    linarith
  have hQD : Q ≤ Dn := by
    have : 0 ≤ 4 * Q * Z := by positivity
    linarith
  have hZD : 4 * Q * Z ≤ Dn := by linarith
  have c1 : ε * M ≤ κ := (le1 M hMD).trans eκ
  have c2 : 4 * (ε * M) ≤ 1 / 4000 := by
    have := (le1 M hMD).trans e16
    linarith
  have c3 : (4 * (ε * Q)) * Z ≤ κ := by
    have := (le1 (4 * Q * Z) hZD).trans eκ
    calc (4 * (ε * Q)) * Z = ε * (4 * Q * Z) := by ring
      _ ≤ κ := this
  have c4 : ε * Q ≤ c := (le1 Q hQD).trans ec
  obtain ⟨dir, top⟩ := smallDirectionTriple_scaledChart hodd h2 hD hθ hC hs hs1 hx ref hcb nm hBu hBa hε le_rfl
    c1 c2 c3 c4
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, f12, -, -⟩ := smallness_bounds hodd hx0 hx (η := 4 * (ε * Q))
    (by positivity) c3 (T := ε * M) (by positivity) c1
  have hθ' : |(-θ)| ≤ 1 / 8 := by rwa [abs_neg]
  set W := scaledChart A ε with hW
  set y := levelDeviation R (realChart W) F.depth with hy
  set h := bondHullNorm b y with hh
  have hh0 : 0 ≤ h := bondHullNorm_nonneg' b y
  have hhT : h ≤ ε * M := dir.hull₂ F.depth (depth_lt_top F) b hb
  have hsmall : 8 * (F.blockSide : ℝ) * h ≤ 1 / 1024 := by
    have := mul_le_mul_of_nonneg_left hhT (by positivity : (0 : ℝ) ≤ 8 * (F.blockSide : ℝ))
    linarith
  have e0 : (1 / (F.blockSide : ℝ)) ^ (F.top - (F.depth + 1)) = 1 := by
    have : F.top - (F.depth + 1) = 0 := by simp [BlockFrame.top]
    rw [this, pow_zero]
  have href : ∀ g ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy (R F.depth) (_root_.YangMills.Construction.BlockAverages.refineSite b.1) (bondContour F.blockSide g π b.2) *
        (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b))⁻¹) - 1‖ ≤ x := fun g hg π => by
    have h1 := ref.contours F.depth le_rfl b hb g hg π
    rw [e0] at h1
    simpa using h1
  have hσ : x ≤ 1 / 64 := dir.spread_le
  have hne : gaugedBondAverage R W F.depth b ≠ 0 := gaugedBondAverage_ne_zero hodd le_rfl W hσ href hsmall
  obtain ⟨-, -, hroot⟩ := remainder_bounds hodd le_rfl hσ hsmall href
  rw [sqrtRemainder_realChart hodd le_rfl R W b hne, Complex.norm_real, Real.norm_eq_abs] at hroot
  set Lm := gaugedBondAverage R W F.depth b with hLm
  set r := ‖Lm‖ with hr
  set r₀ := ‖_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b‖ with hr₀
  set w := polarUnit (contourAverage (R F.depth) b) with hw
  set g := bondAverageGap R W F.depth b with hg
  set ν := linearPart R A (F.depth + 1) b.1 b.2 with hν
  have hlen : |r₀ - 1| ≤ x := by
    have h1 := ref.length F.depth (depth_lt_top F) b hb
    rw [e0] at h1
    simpa using h1
  have hc0 : _root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b ≠ 0 := by
    intro h0
    have : r₀ = 0 := by rw [hr₀, h0, norm_zero]
    rw [this] at hlen
    have := (abs_le.1 hlen).1
    simp at hlen
    linarith
  have hLmw : Lm * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) = r • ((g : UnitQuaternion) : ℍ[ℝ]) := by
    have h1 := eq_norm_smul_polarUnit hne
    have eg : g = polarUnit Lm * w⁻¹ := rfl
    rw [eg]
    conv_lhs => rw [h1]
    rw [smul_mul_assoc]
    rfl
  have hL0w : gaugedBondAverage R U F.depth b * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) = r₀ • (1 : ℍ[ℝ]) := by
    rw [gaugedBondAverage_zeroChart hodd]
    have h1 := eq_norm_smul_polarUnit hc0
    conv_lhs => rw [h1]
    rw [smul_mul_assoc]
    congr 1
    have : w * w⁻¹ = 1 := mul_inv_cancel w
    exact congrArg (fun u : UnitQuaternion => (u : ℍ[ℝ])) this
  have hgn : ‖((g : UnitQuaternion) : ℍ[ℝ])‖ = 1 := CStarRing.norm_coe_unitary g
  have hgl : Nθ * ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1 - ε • ν‖ ≤ ε * (x * Ba * linearCoefficient F.blockSide) +
      ε ^ 2 * (M * Ba * quadraticCoefficient F.blockSide ((F.blockSide : ℝ) ^ F.top)) := by
    have h1 := rpow_mul_le_weightedScaleNorm_top (D := D) p θ (P := 2) (by norm_num) (topUnitDefect R W)
      (fun _ _ => norm_nonneg _) hb hL
    have h3 := h1.trans top.lin₂
    rw [linearPartError_smul_eq] at h3
    have e3 : topUnitDefect R W b.1 b.2 = ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1 - ε • ν‖ := by
      simp only [topUnitDefect, hg, hν, hW]
      rw [linearPart_scaledChart]
    rw [e3] at h3
    exact h3
  have hωh : Nθ * h ≤ hullFactor F.blockSide * (82272 * (ε * Ba)) := by
    have h1 := rpow_mul_le_weightedScaleNorm_top (D := D) p θ (P := 4) (by norm_num)
      (fun u d => bondHullSum (u, d) fun z e' => ‖y z e'‖)
      (fun _ _ => bondHullSum_nonneg _ fun _ _ => norm_nonneg _) hb hL
    have h3 := weightedScaleNorm_bondHullSum_le (D := D) hodd hθ' (depth_lt_top F) p 4 (by norm_num)
      (g := fun z e' => ‖y z e'‖) (fun _ _ => norm_nonneg _)
    have h4 := dir.dev₂ F.depth (depth_lt_top F)
    refine h1.trans (h3.trans (mul_le_mul_of_nonneg_left h4 hF0))
  have hr2 : r₀ ≤ 2 := by
    have := (abs_le.1 hlen).2
    linarith
  have hr0 : 0 ≤ r₀ := norm_nonneg _
  have eid : r • ((g : UnitQuaternion) : ℍ[ℝ]) - r₀ • (1 : ℍ[ℝ]) - ε • ν =
      r₀ • (((g : UnitQuaternion) : ℍ[ℝ]) - 1 - ε • ν) + (r - r₀) • ((g : UnitQuaternion) : ℍ[ℝ]) +
        ((r₀ - 1) * ε) • ν := by
    module
  show Nθ * ‖Lm * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
    gaugedBondAverage R U F.depth b * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ε • ν‖ ≤ _
  rw [hLmw, hL0w, eid]
  have hn1 : ‖r₀ • (((g : UnitQuaternion) : ℍ[ℝ]) - 1 - ε • ν) + (r - r₀) • ((g : UnitQuaternion) : ℍ[ℝ]) +
      ((r₀ - 1) * ε) • ν‖ ≤
      r₀ * ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1 - ε • ν‖ + |r - r₀| + x * ε * ‖ν‖ := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    · rw [norm_smul, Real.norm_eq_abs, hgn, mul_one]
    · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hε0]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlen hε0) (norm_nonneg _)
  have hn2 : Nθ * |r - r₀| ≤ K * (ε * M + x) * (hullFactor F.blockSide * (82272 * (ε * Ba))) := by
    have h1 : Nθ * |r - r₀| ≤ Nθ * (K * (h ^ 2 + x * h)) := mul_le_mul_of_nonneg_left hroot hNθ0.le
    have e1 : Nθ * (K * (h ^ 2 + x * h)) = K * (h + x) * (Nθ * h) := by ring
    rw [e1] at h1
    refine h1.trans (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hK0) hωh (by positivity) (by positivity))
  have hn3 : r₀ * (Nθ * ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1 - ε • ν‖) ≤
      2 * (Nθ * ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1 - ε • ν‖) :=
    mul_le_mul_of_nonneg_right hr2 (by positivity)
  have ev : velocityConstant F.blockSide =
      2 * linearCoefficient F.blockSide + K * (hullFactor F.blockSide * 82272) := rfl
  have hfin := mul_le_mul_of_nonneg_left hn1 hNθ0.le
  refine hfin.trans ?_
  rw [ev]
  have e5 : Nθ * (r₀ * ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1 - ε • ν‖ + |r - r₀| + x * ε * ‖ν‖) =
      r₀ * (Nθ * ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1 - ε • ν‖) + Nθ * |r - r₀| + x * ε * (Nθ * ‖ν‖) := by ring
  rw [e5]
  have hfinal : 2 * (ε * (x * Ba * linearCoefficient F.blockSide) +
      ε ^ 2 * (M * Ba * quadraticCoefficient F.blockSide ((F.blockSide : ℝ) ^ F.top))) +
      K * (ε * M + x) * (hullFactor F.blockSide * (82272 * (ε * Ba))) + x * ε * (Nθ * ‖ν‖) =
      ε * (x * (Ba * (2 * linearCoefficient F.blockSide + K * (hullFactor F.blockSide * 82272))) + Nθ * x * ‖ν‖) +
        ε ^ 2 * (2 * (M * Ba * quadraticCoefficient F.blockSide ((F.blockSide : ℝ) ^ F.top)) +
          K * M * (hullFactor F.blockSide * 82272) * Ba) := by ring
  rw [← hfinal]
  have := mul_le_mul_of_nonneg_left hgl (by norm_num : (0 : ℝ) ≤ 2)
  linarith
private theorem derivative_sub_linearPart_le (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    {D : Finset F.Cell} (hD : D.card ≤ 81) {p : F.Site 0}
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {A : ChainChart F} {C₀ s Bu Ba c : ℝ}
    (hC : 0 < C₀) (hs : 0 < s) (hs1 : s ≤ 1) (hx : C₀ * s ≤ smallnessThreshold F.blockSide) (hx1 : C₀ * s ≤ 1)
    (ref : ReferenceNear D R C₀ s)
    (hc : 0 < c) (hcb : ∀ (W : ChainChart F) (B : ℝ), 0 ≤ B → B ≤ c →
      finsetLpNorm 4 (innerBonds D 0) (fun b => ‖(W.fine b.1 b.2 : ℍ[ℝ])‖) ≤ B →
      (∀ j, j + 1 < F.top →
        finsetLpNorm 2 (innerBonds D (j + 1)) (fun b => ‖(W.coarse j b.1 b.2 : ℍ[ℝ])‖) ≤ B) →
      DeviationBall R D (realChart W) (4 * B) (4 * B))
    (nm : PairWeightedNorms D p θ (zeroChart F) A Bu Ba) (hBu : 0 ≤ Bu) (hBa : 0 ≤ Ba)
    {b : F.Site (F.depth + 1) × Fin 4} (hb : b ∈ innerBonds D (F.depth + 1)) {q : ℍ[ℝ]}
    (hq : HasDerivAt (fun τ : ℝ => gaugedBondAverage R (chartMove (zeroChart F) A τ) F.depth b) q 0) :
    ((F.blockSide : ℝ) ^ F.top) ^ θ *
        ‖q * (((polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b))⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
          linearPart R A (F.depth + 1) b.1 b.2‖ ≤
      C₀ * s * (Ba * velocityConstant F.blockSide) + ((F.blockSide : ℝ) ^ F.top) ^ θ * (C₀ * s) *
        ‖linearPart R A (F.depth + 1) b.1 b.2‖ := by
  obtain ⟨Y, ε₀, hε₀, hY⟩ :=
    gaugedBondAverage_chartMove_sub_le hodd h2 hD hθ hC hs hs1 hx hx1 ref hc hcb nm hBu hBa hb
  set Nθ := ((F.blockSide : ℝ) ^ F.top) ^ θ with hNθ
  set w := polarUnit (contourAverage (R F.depth) b) with hw
  set ν := linearPart R A (F.depth + 1) b.1 b.2 with hν
  set B := C₀ * s * (Ba * velocityConstant F.blockSide) + Nθ * (C₀ * s) * ‖ν‖ with hB
  set f : ℝ → ℍ[ℝ] := fun τ => gaugedBondAverage R (chartMove (zeroChart F) A τ) F.depth b with hf
  have hN0 : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
    positivity
  have h0 : f 0 = gaugedBondAverage R (zeroChart F) F.depth b := by
    have : chartMove (zeroChart F) A 0 = zeroChart F := by
      apply CoordinateSeminorms.chainChart_ext
      · funext x i
        simp [chartMove]
      · funext j x i
        simp [chartMove]
    simp only [hf, this]
  have ht := (hasDerivAt_iff_tendsto_slope.1 hq).mono_left
    (nhdsWithin_mono (0 : ℝ) (fun x (hx : 0 < x) => (ne_of_gt hx : x ≠ 0)))
  have ht2 : Tendsto (fun ε : ℝ => Nθ * ‖slope f 0 ε * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ν‖) (𝓝[>] 0)
      (𝓝 (Nθ * ‖q * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ν‖)) :=
    (((ht.mul_const _).sub_const ν).norm).const_mul Nθ
  have ht3 : Tendsto (fun ε : ℝ => B + ε * Y) (𝓝[>] 0) (𝓝 B) := by
    have : Continuous fun ε : ℝ => B + ε * Y := by fun_prop
    have h3 := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using h3
  refine le_of_tendsto_of_tendsto ht2 ht3 ?_
  filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
  have h1 := hY ε hε.1 hε.2
  have hε0 : 0 < ε := hε.1
  have e1 : slope f 0 ε * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ν =
      ε⁻¹ • (f ε * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) - f 0 * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ε • ν) := by
    rw [slope_def_module, sub_zero, smul_mul_assoc, sub_mul, smul_sub ε⁻¹ (_ - _) (ε • ν), smul_smul,
      inv_mul_cancel₀ hε0.ne', one_smul]
  rw [e1, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hε0, h0]
  have e2 : Nθ * (ε⁻¹ * ‖f ε * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
        gaugedBondAverage R (zeroChart F) F.depth b * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ε • ν‖) =
      ε⁻¹ * (Nθ * ‖f ε * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
        gaugedBondAverage R (zeroChart F) F.depth b * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ε • ν‖) := by ring
  rw [e2]
  have h3 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hε0.le)
  refine h3.trans (le_of_eq ?_)
  field_simp
private theorem velocityConstant_nonneg {L : ℕ} (hL : Odd L) : 0 ≤ velocityConstant L := by
  have hF := hullFactor_nonneg (F := ⟨L, 0, fun _ => 0⟩) hL
  unfold velocityConstant linearCoefficient
  positivity
private theorem referenceNear_of_bounds (hL1 : (1 : ℝ) ≤ F.blockSide) {S D : Finset F.Cell} (hDS : D ⊆ S)
    {V : F.GaugeField F.top} {C s : ℝ}
    (hC : 0 < C) (hs : 0 < s) (hs1 : s ≤ 1)
    (b3 : ∀ j, j + 1 < F.top → ∀ c' ∈ innerBonds S (j + 1),
      unitDeviation (referenceDefect (referenceFieldChain S V) j c') ≤ C * s * levelScale F (j + 1) ^ 3)
    (b4 : ∀ c' ∈ innerBonds S F.top, unitDeviation (referenceDefect (referenceFieldChain S V) F.depth c') ≤ C * s)
    (b5 : ∀ j, j < F.top → ∀ c' ∈ innerBonds S (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      unitDeviation (pathHolonomy (referenceFieldChain S V j) (_root_.YangMills.Construction.BlockAverages.refineSite c'.1)
          (bondContour F.blockSide h π c'.2) *
          (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (referenceFieldChain S V j) c'))⁻¹) ≤ C * s * levelScale F (j + 1) ^ 2)
    (b6 : ∀ j, j < F.top → ∀ c' ∈ innerBonds S (j + 1),
      0 ≤ 1 - ‖_root_.YangMills.Construction.BlockAverages.contourAverage (referenceFieldChain S V j) c'‖ ∧
        1 - ‖_root_.YangMills.Construction.BlockAverages.contourAverage (referenceFieldChain S V j) c'‖ ≤ C * s ^ 2 * levelScale F (j + 1) ^ 4) :
    ReferenceNear D (referenceFieldChain S V) C s where
  contours := fun j hj c hc h hh π => by
    rw [norm_ofUnit_sub_one]
    exact b5 j (by omega) c (innerBonds_mono hDS _ hc) h hh π
  defect := fun m hm c hc => b3 m hm c (innerBonds_mono hDS _ hc)
  defect_top := fun c hc => b4 c (innerBonds_mono hDS _ hc)
  length := fun m hm c hc => by
    obtain ⟨h0, h1⟩ := b6 m hm c (innerBonds_mono hDS _ hc)
    rw [abs_sub_comm, abs_of_nonneg h0]
    refine h1.trans ?_
    obtain ⟨hl0, hl1, -⟩ := inv_pow_bounds hL1 (F.top - (m + 1))
    have e : levelScale F (m + 1) = (1 / (F.blockSide : ℝ)) ^ (F.top - (m + 1)) := rfl
    rw [e]
    set l := (1 / (F.blockSide : ℝ)) ^ (F.top - (m + 1)) with hl
    have h4 : l ^ 4 ≤ l ^ 3 := by
      have := mul_le_mul_of_nonneg_left hl1 (by positivity : 0 ≤ l ^ 3)
      nlinarith
    have h5 : s ^ 2 ≤ s := by nlinarith
    have h6 : s ^ 2 * l ^ 4 ≤ s * l ^ 3 := mul_le_mul h5 h4 (by positivity) hs.le
    have := mul_le_mul_of_nonneg_left h6 hC.le
    nlinarith
private theorem abs_decay_sub_le {del : ℝ} (hdel : 0 ≤ del) (y0 y y' : F.Cell) :
    |(-del * (cellSupDist y y0 : ℝ)) - (-del * (cellSupDist y' y0 : ℝ))| ≤ del * cellSupDist y y' := by apply _root_.YangMills.Construction.ComplexFamilies.abs_neg_mul_cellSupDist_sub_le <;> assumption
end TopAverageBound
set_option maxHeartbeats 2000000 in
open TopAverageBound BlockAverages LevelRecursion ComplexLevels HullBounds ComplexRemainders SmallMultiples
  LowerLevelTerms TopLevelTerms BondSecondDifference RealChartTerms BlockLines RealDirections ComplexDifferences in
theorem BlockAverages.topAverageInDecayWeight_of_referenceBounds (hb : referenceBoundsStatement)
    (hrec : UniformQuarticBoundAcrossLevels) : topAverageInDecayWeightStatement := by
  intro del hdel hdel8
  obtain ⟨Cb, cb, L1, hCb, hcb0, hB⟩ := hb
  have hE : 1 ≤ Real.exp del := Real.one_le_exp hdel.le
  refine ⟨100284 * Real.exp del, by positivity, max 5 L1, fun L hodd hL => ?_⟩
  have hL5 : 5 ≤ L := (le_max_left _ _).trans hL
  have hLb : L1 ≤ L := (le_max_right _ _).trans hL
  obtain ⟨cball, hcball0, -, hball⟩ := exists_deviationBall_realChart hrec L hodd hL5 hCb.le
  have hsm0 : 0 < smallnessThreshold L := SecondDifferences.smallnessThreshold_pos (F := ⟨L, 0, fun _ => 0⟩) hodd
  have hvN := velocityConstant_nonneg hodd
  set c := min (min cb (1 / Cb)) (min (min cball 1) (smallnessThreshold L / Cb)) with hc
  have hc0 : 0 < c := lt_min (lt_min hcb0 (by positivity)) (lt_min (lt_min hcball0 one_pos) (by positivity))
  refine ⟨c, Cb * (Real.exp del * velocityConstant L + 2 * (100284 * Real.exp del)) + 1, hc0, by positivity, ?_⟩
  intro F m S hFL hamb hm hreg s V hs0 hsc hcold A θ' p y0 hθ0 hθ8 b hbS
  have hodd' : Odd F.blockSide := hFL ▸ hodd
  have h2 : 2 ≤ F.blockSide := by omega
  have hL1' : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd'.pos
  have hscb : s ≤ cb := hsc.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hsC : s ≤ 1 / Cb := hsc.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hscball : s ≤ cball := hsc.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hs1 : s ≤ 1 := hsc.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hsS : s ≤ smallnessThreshold L / Cb := hsc.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hx : Cb * s ≤ smallnessThreshold F.blockSide := by
    rw [hFL]
    rw [le_div_iff₀ hCb] at hsS
    linarith
  have hx1 : Cb * s ≤ 1 := by
    rw [le_div_iff₀ hCb] at hsC
    linarith
  set R := referenceFieldChain S V with hR
  have hV : R F.top = V := by simp [hR, referenceFieldChain]
  obtain ⟨-, -, b3, b4, b5, b6⟩ := hB F m S hodd' (hFL ▸ hLb) hamb hm hreg s V hs0 hscb hcold
  set z := enclosingCell b.1 with hzd
  have hz : z ∈ S := CoordinateSeminorms.enclosingCell_mem hodd'
    (Finset.mem_product.1 (Finset.mem_filter.1 hbS).1).1
  have hbD : b ∈ innerBonds (cellBall S z 1) (F.depth + 1) :=
    mem_innerBonds_cellBall_of_mem_bondsOver hamb hodd' S z le_rfl
      (CoordinateSeminorms.mem_bondsOver.2 ⟨hbS, by simp [hzd]⟩)
  have ref : ReferenceNear (cellBall S z 1) R Cb s :=
    referenceNear_of_bounds hL1' (cellBall_subset S z 1) hCb hs0 hs1 b3 b4 b5 b6
  have hcb : ∀ (W : ChainChart F) (B : ℝ), 0 ≤ B → B ≤ cball →
      finsetLpNorm 4 (innerBonds (cellBall S z 1) 0) (fun b => ‖(W.fine b.1 b.2 : ℍ[ℝ])‖) ≤ B →
      (∀ j, j + 1 < F.top →
        finsetLpNorm 2 (innerBonds (cellBall S z 1) (j + 1)) (fun b => ‖(W.coarse j b.1 b.2 : ℍ[ℝ])‖) ≤ B) →
      DeviationBall R (cellBall S z 1) (realChart W) (4 * B) (4 * B) := fun W B hB0 hBc h1 h3 =>
    hball F (cellBall S z 1) R W s B hFL (card_cellBall_one_le S z) ref.contours hs0.le hscball hB0 hBc h1 h3
  set φ : F.Cell → ℝ := fun y => -del * (cellSupDist y y0 : ℝ) with hφd
  have hφ : ∀ y y', |φ y - φ y'| ≤ del * cellSupDist y y' := fun y y' => abs_decay_sub_le hdel.le y0 y y'
  have hw : classWeight F φ θ' p = decayWeights F del θ' p y0 := rfl
  have nm := pairWeightedNorms_of_classWeight hodd' hz hdel.le hφ p R (zeroChart F) A (θ := θ')
  rw [hw] at nm
  set wi := invertedWeights (decayWeights F del θ' p y0) with hwi
  set nr := localNorm S R A wi z with hnr
  have hnr0 : 0 ≤ nr := Real.sqrt_nonneg _
  have hN0 : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  set Nθ := ((F.blockSide : ℝ) ^ F.top) ^ θ' with hNθ
  have hNθ0 : 0 < Nθ := Real.rpow_pos_of_pos hN0 _
  set Ba := Real.exp del * (Real.exp (φ z) * Nθ) * nr with hBa
  have hBa0 : 0 ≤ Ba := by positivity
  have hBu0 : 0 ≤ Real.exp del * localNorm S R (zeroChart F) (decayWeights F del θ' p y0) z /
      (Real.exp (φ z) * Nθ) := by
    have : 0 ≤ localNorm S R (zeroChart F) (decayWeights F del θ' p y0) z := Real.sqrt_nonneg _
    positivity
  have hθ'' : |θ'| ≤ 1 / 8 := by rwa [abs_of_nonneg hθ0]
  have hϑ : |(-θ')| ≤ 1 / 8 := by rwa [abs_neg]
  have hφz : Real.exp (φ z) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simp only [hφd]
    have : (0 : ℝ) ≤ cellSupDist z y0 := by positivity
    nlinarith
  have hφz0 : 0 < Real.exp (φ z) := Real.exp_pos _
  have hover : nr ≤ _root_.YangMills.Construction.BlockAverages.weightedNorm S R A wi := CoordinateSeminorms.localNorm_le_weightedNorm S R A wi z
  set ν := linearPart R A F.top b.1 b.2 with hν
  have hνb : Nθ * ‖ν‖ ≤ 100284 * Ba := by
    have h1 := weightedScaleNorm_linearPart_top_le hodd' h2 (R := R) A (card_cellBall_one_le S z) p hϑ hBa0
      nm.coarse_inv_le
    have h3 := rpow_mul_le_weightedScaleNorm_top (D := cellBall S z 1) p θ' (P := 2) (by norm_num)
      (fun y d => ‖linearPart R A (F.depth + 1) y d‖) (fun _ _ => norm_nonneg _) hbD hodd'.pos
    have h4 := nm.fine_inv_le
    refine h3.trans (h1.trans ?_)
    linarith
  have hνz : ‖ν‖ ≤ 100284 * Real.exp del * nr := by
    have e : 100284 * Ba = Nθ * (100284 * Real.exp del * Real.exp (φ z) * nr) := by
      rw [hBa]
      ring
    rw [e] at hνb
    have h3 := le_of_mul_le_mul_left hνb hNθ0
    refine h3.trans ?_
    have : 100284 * Real.exp del * Real.exp (φ z) * nr ≤ 100284 * Real.exp del * 1 * nr := by gcongr
    linarith
  refine ⟨hνz.trans (mul_le_mul_of_nonneg_left hover (by positivity)), fun q hq => ?_⟩
  have hvel := derivative_sub_linearPart_le hodd' h2 (card_cellBall_one_le S z) hθ'' hCb hs0 hs1 hx hx1 ref
    hcball0 hcb nm hBu0 hBa0 hbD hq
  set w := polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b) with hwd
  set μ := referenceDefect R F.depth b with hμ
  have hqw : ‖q * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ν‖ ≤
      Cb * s * (Real.exp del * nr * velocityConstant F.blockSide) + Cb * s * ‖ν‖ := by
    have e : Cb * s * (Ba * velocityConstant F.blockSide) + Nθ * (Cb * s) * ‖ν‖ =
        Nθ * (Cb * s * (Real.exp del * Real.exp (φ z) * nr * velocityConstant F.blockSide) + Cb * s * ‖ν‖) := by
      rw [hBa]
      ring
    rw [e] at hvel
    have h3 := le_of_mul_le_mul_left hvel hNθ0
    refine h3.trans ?_
    have hv : 0 ≤ velocityConstant F.blockSide := by rw [hFL]; exact hvN
    have : Real.exp del * Real.exp (φ z) * nr * velocityConstant F.blockSide ≤
        Real.exp del * 1 * nr * velocityConstant F.blockSide := by
      gcongr
    have h5 := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ Cb * s)
    linarith
  have hVb : V b.1 b.2 = μ * w := by
    simp only [hμ, referenceDefect, hwd, inv_mul_cancel_right]
    rw [← hV]
  have eV : (((V b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((μ⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    rw [hVb, mul_inv_rev]
    rfl
  rw [eV]
  have eid : q * (((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((μ⁻¹ : UnitQuaternion) : ℍ[ℝ])) - ν =
      (q * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ν) * ((μ⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
        ν * (((μ⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) := by
    noncomm_ring
  rw [eid]
  have hμ1 : ‖((μ⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Cb * s := by
    rw [norm_coe_inv_sub_one]
    exact ref.defect_top b hbD
  have hμn : ‖((μ⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = 1 := CStarRing.norm_coe_unitary _
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, hμn, mul_one]
  have h5 := norm_mul_le ν (((μ⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1)
  have h6 : ‖ν‖ * ‖((μ⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖ν‖ * (Cb * s) :=
    mul_le_mul_of_nonneg_left hμ1 (norm_nonneg _)
  set No := _root_.YangMills.Construction.BlockAverages.weightedNorm S R A wi with hNo
  have hNo0 : 0 ≤ No := hnr0.trans hover
  have hvL : velocityConstant F.blockSide = velocityConstant L := by rw [hFL]
  rw [hvL] at hqw
  have h7 : ‖ν‖ ≤ 100284 * Real.exp del * No := hνz.trans (mul_le_mul_of_nonneg_left hover (by positivity))
  have hCs : 0 ≤ Cb * s := by positivity
  have h8 : Cb * s * (Real.exp del * nr * velocityConstant L) ≤ Cb * s * (Real.exp del * No * velocityConstant L) := by
    gcongr
  have h9 := mul_le_mul_of_nonneg_left h7 hCs
  calc _ ≤ Cb * s * (Real.exp del * No * velocityConstant L) + Cb * s * (100284 * Real.exp del * No) +
        Cb * s * (100284 * Real.exp del * No) := by nlinarith
    _ ≤ _ := by
      have : 0 ≤ s * No := by positivity
      nlinarith
end YangMills.Construction
end

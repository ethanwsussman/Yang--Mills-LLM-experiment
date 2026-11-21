import YangMills.Construction.ColdChainAtEveryLevel.CellContexts
import YangMills.Construction.ColdChainAtEveryLevel.ComplexChainIsAnalytic
import YangMills.Construction.ColdChainAtEveryLevel.SmallCoordinatesAreRegular
import YangMills.Construction.ColdChainAtEveryLevel.TopAverageOfAnyChain
import YangMills.Construction.ColdChainAtEveryLevel.VariationsAlongAMisfit
import YangMills.Construction.ColdChainAtEveryLevel.VelocityOfTheTopMean
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology Matrix.Norms.L2Operator
namespace YangMills.Construction.TopMeanVelocity
open BlockAverages ComplexifiedQuaternions ComplexContours ComplexDifferences ComplexRemainders ComplexChainStep
  ComplexLevels ComplexCells ComplexAnalyticity CellSpans CellSources CellNormBounds CellContexts HullBounds
  LevelRecursion
variable {F : BlockFrame} {j : ℕ}
private def complexLine (U A : ChainChart F) (ζ : ℂ) : ComplexChainChart F := spanChart U ![A] ![ζ]
private def complexLinear (R : F.FieldChain) (U A : ChainChart F) (ζ : ℂ) (m : ℕ) (x : F.Site m) (i : Fin 4) :
    ComplexQuat :=
  ofQuat (linearPart R U m x i) + ζ • ofQuat (linearPart R A m x i)
private theorem baseSource_complexLine (U A : ChainChart F) (ζ : ℂ) (x : F.Site 0) (i : Fin 4) :
    baseSource (complexLine U A ζ) x i = ofQuat (U.fine x i : ℍ[ℝ]) + ζ • ofQuat (A.fine x i : ℍ[ℝ]) := by
  rw [complexLine, baseSource_spanChart]
  simp
private theorem upperSource_complexLine (U A : ChainChart F) (ζ : ℂ) (x : Σ m : ℕ, F.Site (m + 1) × Fin 4) :
    upperSource (complexLine U A ζ) x =
      ofQuat (U.coarse x.1 x.2.1 x.2.2 : ℍ[ℝ]) + ζ • ofQuat (A.coarse x.1 x.2.1 x.2.2 : ℍ[ℝ]) := by
  rw [complexLine, upperSource_spanChart]
  simp
private theorem transportedAverage_ofQuat (R : F.GaugeField j) (f : F.Site j → Fin 4 → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) :
    transportedAverage R (fun x i => ofQuat (f x i)) c = ofQuat (parallelAverage R f c) := by
  simp only [transportedAverage, blockContourMean, parallelAverage, contourWeight, ofQuat_smul, ofQuat_sum,
    conjByUnit_ofQuat]
private theorem transportedAverage_const_smul (R : F.GaugeField j) (z : ℂ) (f : F.Site j → Fin 4 → ComplexQuat)
    (c : F.Site (j + 1) × Fin 4) :
    transportedAverage R (fun x i => z • f x i) c = z • transportedAverage R f c := by
  simp only [transportedAverage, blockContourMean, conjByUnit_smul, ← Finset.smul_sum]
  rw [smul_comm]
private theorem complexLinear_zero (R : F.FieldChain) (U A : ChainChart F) (ζ : ℂ) (x : F.Site 0) (i : Fin 4) :
    complexLinear R U A ζ 0 x i = baseSource (complexLine U A ζ) x i := by
  rw [baseSource_complexLine]
  rfl
private theorem complexLinear_succ (R : F.FieldChain) (U A : ChainChart F) (ζ : ℂ) {m : ℕ} (y : F.Site (m + 1))
    (i : Fin 4) :
    complexLinear R U A ζ (m + 1) y i = transportedAverage (R m) (complexLinear R U A ζ m) (y, i) +
      if m + 1 < F.top then upperSource (complexLine U A ζ) ⟨m, (y, i)⟩ else 0 := by
  have e : transportedAverage (R m) (complexLinear R U A ζ m) (y, i) =
      ofQuat (parallelAverage (R m) (linearPart R U m) (y, i)) +
        ζ • ofQuat (parallelAverage (R m) (linearPart R A m) (y, i)) := by
    have := transportedAverage_add (R m) (fun x i => ofQuat (linearPart R U m x i))
      (fun x i => ζ • ofQuat (linearPart R A m x i)) (y, i)
    rw [transportedAverage_const_smul, transportedAverage_ofQuat, transportedAverage_ofQuat] at this
    exact this
  rw [e, upperSource_complexLine]
  by_cases h : m + 1 < F.top
  · simp only [complexLinear, linearPart, if_pos h, ofQuat_add, smul_add]
    abel
  · simp only [complexLinear, linearPart, if_neg h, add_zero]
private theorem purePart_ofQuat_line (a b : imaginaryQuaternions) (z : ℂ) :
    purePart (ofQuat (a : ℍ[ℝ]) + z • ofQuat (b : ℍ[ℝ])) = ofQuat (a : ℍ[ℝ]) + z • ofQuat (b : ℍ[ℝ]) := by
  rw [purePart_add, purePart_smul, purePart_ofQuat_imaginary, purePart_ofQuat_imaginary]
private theorem purePart_complexLinear (R : F.FieldChain) (U A : ChainChart F) (ζ : ℂ) :
    ∀ (m : ℕ) (x : F.Site m) (i : Fin 4), purePart (complexLinear R U A ζ m x i) = complexLinear R U A ζ m x i := by
  intro m
  induction m with
  | zero =>
    intro x i
    exact purePart_ofQuat_line _ _ _
  | succ m ih =>
    intro y i
    rw [complexLinear_succ, purePart_add, purePart_transportedAverage]
    have e : (fun x i => purePart (complexLinear R U A ζ m x i)) = complexLinear R U A ζ m := by
      funext x i
      exact ih x i
    rw [e]
    congr 1
    by_cases h : m + 1 < F.top
    · rw [if_pos h, upperSource_complexLine]
      exact purePart_ofQuat_line _ _ _
    · rw [if_neg h]
      simp [purePart]
private theorem norm_conjByUnit_sub_le (g : UnitQuaternion) (e : ComplexQuat) :
    ‖conjByUnit g e - e‖ ≤ 2 * ‖ofUnit g - 1‖ * ‖e‖ := by
  have h1 : conjByUnit g e - e = (ofUnit g - 1) * e * ofUnit g⁻¹ + e * (ofUnit g⁻¹ - 1) := by
    simp only [conjByUnit, sub_mul, mul_sub, one_mul, mul_one]
    abel
  have h2 : ‖ofUnit g⁻¹ - 1‖ = ‖ofUnit g - 1‖ := by
    have : ofUnit g⁻¹ - 1 = ofUnit g⁻¹ * (1 - ofUnit g) := by
      rw [mul_sub, mul_one, ofUnit_inv_mul]
    rw [this, norm_ofUnit_mul, norm_sub_rev]
  rw [h1]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul_ofUnit]
  have h3 := norm_mul_le (ofUnit g - 1) e
  have h4 := norm_mul_le e (ofUnit g⁻¹ - 1)
  rw [h2] at h4
  nlinarith
private theorem norm_levelDeviation_sub_complexLinear_succ_le (hodd : Odd F.blockSide) {m : ℕ} (hm : m + 1 < F.top)
    (R : F.FieldChain) (U A : ChainChart F) (ζ : ℂ)
    {c : F.Site (m + 1) × Fin 4} {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy (R m) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R m) c))⁻¹) - 1‖ ≤ σ)
    (hμ : ‖ofUnit (referenceDefect R m c) - 1‖ ≤ σ)
    (hsm : 8 * (F.blockSide : ℝ) * bondHullNorm c (levelDeviation R (complexLine U A ζ) m) ≤ 1 / 1024)
    (hh1 : bondHullNorm c (levelDeviation R (complexLine U A ζ) m) ≤ 1)
    (hd : HoldsOnHull c (fun b i => (complexChartField R (complexLine U A ζ) m b i).det = 1))
    (hξ : ‖upperSource (complexLine U A ζ) ⟨m, c⟩‖ ≤ 1 / 8000) :
    ‖levelDeviation R (complexLine U A ζ) (m + 1) c.1 c.2 - complexLinear R U A ζ (m + 1) c.1 c.2‖ ≤
      lineBlockAverage (fun x i => ‖levelDeviation R (complexLine U A ζ) m x i - complexLinear R U A ζ m x i‖) c +
        (129 * ‖upperSource (complexLine U A ζ) ⟨m, c⟩‖ ^ 2 + 7 * (200000 * (F.blockSide : ℝ) ^ 2) *
          (‖upperSource (complexLine U A ζ) ⟨m, c⟩‖ * bondHullNorm c (levelDeviation R (complexLine U A ζ) m) +
            bondHullNorm c (levelDeviation R (complexLine U A ζ) m) ^ 2 +
              σ * bondHullNorm c (levelDeviation R (complexLine U A ζ) m))) := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  set W := complexLine U A ζ with hW
  set y := levelDeviation R W m with hy
  set h := bondHullNorm c y with hh
  set ξ := upperSource W ⟨m, c⟩ with hξd
  set K : ℝ := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hK1 : 1 ≤ K := by
    rw [hK]
    nlinarith
  have hh0 : 0 ≤ h := bondHullSum_nonneg _ fun _ _ => norm_nonneg _
  obtain ⟨-, hq, -⟩ := remainder_bounds hodd (by omega : m + 1 ≤ F.top) hσ hsm href
  set q := unitRemainder (R m) c y with hqd
  set P := purePart (transportedAverage (R m) y c) with hP
  set Pl := transportedAverage (R m) (complexLinear R U A ζ m) c with hPl
  set E := levelSource W m c.1 c.2 with hE
  set μ := referenceDefect R m c with hμd
  have hgap : levelDeviation R W (m + 1) c.1 c.2 = E * conjByUnit μ (1 + P + q) - 1 :=
    levelDeviation_succ hodd (by omega) R W hd
  have hlin : complexLinear R U A ζ (m + 1) c.1 c.2 = Pl + ξ := by
    have := complexLinear_succ R U A ζ c.1 c.2
    rw [if_pos hm] at this
    exact this
  have hpure : purePart Pl = Pl := by
    rw [hPl, purePart_transportedAverage]
    congr 1
    funext x i
    exact purePart_complexLinear R U A ζ m x i
  have hPd : ‖P - Pl‖ ≤ lineBlockAverage (fun x i => ‖y x i - complexLinear R U A ζ m x i‖) c := by
    have e : P - Pl = purePart (transportedAverage (R m) (fun x i => y x i - complexLinear R U A ζ m x i) c) := by
      rw [transportedAverage_sub, purePart_sub, hpure]
    rw [e]
    exact (norm_purePart_le _).trans (norm_transportedAverage_le hodd _ _ c)
  have hP1 : ‖P‖ ≤ h :=
    (norm_purePart_le _).trans ((norm_transportedAverage_le hodd _ _ c).trans
      (lineBlockAverage_le_bondHullSum hodd (fun _ _ => norm_nonneg _) c))
  have hξ0 := norm_nonneg ξ
  have hξp : purePart ξ = ξ := by
    rw [hξd, hW, upperSource_complexLine]
    exact purePart_ofQuat_line _ _ _
  have n1 : ‖E - 1 - ξ‖ ≤ 129 * ‖ξ‖ ^ 2 := by
    have := norm_unitExp_sub_one_sub_purePart_le (y := ξ) (by linarith)
    rwa [hξp] at this
  have n2 : ‖E - 1‖ ≤ 2 * ‖ξ‖ := norm_unitExp_sub_one_le (y := ξ) (by linarith)
  have hX : ‖P + q‖ ≤ 3 * K * h := by
    have h1 := norm_add_le P q
    have h2 : K * (h ^ 2 + σ * h) ≤ 2 * K * h := by
      have : h ^ 2 + σ * h ≤ 2 * h := by nlinarith
      nlinarith
    nlinarith
  have n3 : ‖conjByUnit μ (P + q) - (P + q)‖ ≤ 2 * σ * (3 * K * h) := by
    refine (norm_conjByUnit_sub_le μ _).trans ?_
    have h1 : 2 * ‖ofUnit μ - 1‖ ≤ 2 * σ := by linarith
    exact mul_le_mul h1 hX (norm_nonneg _) (by linarith)
  have n4 : ‖(E - 1) * conjByUnit μ (P + q)‖ ≤ 2 * ‖ξ‖ * (3 * K * h) := by
    refine (norm_mul_le _ _).trans ?_
    rw [norm_conjByUnit]
    exact mul_le_mul n2 hX (norm_nonneg _) (by linarith)
  have hid : levelDeviation R W (m + 1) c.1 c.2 - complexLinear R U A ζ (m + 1) c.1 c.2 =
      (E - 1 - ξ) + (E - 1) * conjByUnit μ (P + q) + (conjByUnit μ (P + q) - (P + q)) + q + (P - Pl) := by
    have e1 : conjByUnit μ (1 + P + q) = 1 + conjByUnit μ (P + q) := by
      rw [add_assoc, conjByUnit_add, conjByUnit_one]
    rw [hgap, hlin, e1, mul_add, mul_one, sub_mul, one_mul]
    abel
  rw [hid]
  have t1 := norm_add_le ((E - 1 - ξ) + (E - 1) * conjByUnit μ (P + q) + (conjByUnit μ (P + q) - (P + q)) + q)
    (P - Pl)
  have t2 := norm_add_le ((E - 1 - ξ) + (E - 1) * conjByUnit μ (P + q) + (conjByUnit μ (P + q) - (P + q))) q
  have t3 := norm_add_le ((E - 1 - ξ) + (E - 1) * conjByUnit μ (P + q)) (conjByUnit μ (P + q) - (P + q))
  have t4 := norm_add_le (E - 1 - ξ) ((E - 1) * conjByUnit μ (P + q))
  have e7 : 7 * K * (‖ξ‖ * h + h ^ 2 + σ * h) =
      6 * K * (‖ξ‖ * h) + 6 * K * (σ * h) + K * (h ^ 2 + σ * h) + (K * (‖ξ‖ * h) + 6 * K * h ^ 2) := by ring
  have e8 : 0 ≤ K * (‖ξ‖ * h) + 6 * K * h ^ 2 := by positivity
  rw [e7]
  linarith
private def linearDeviationBound (L : ℕ) (B Cs : ℝ) : ℝ :=
  2 * (142 * (129 * B ^ 2) + 284 * (129 * B ^ 2 + 7 * (200000 * (L : ℝ) ^ 2) *
    (B * (hullFactor L * B) + (hullFactor L * B) ^ 2 + 5 * Cs * (hullFactor L * B))))
private theorem finsetLpNorm_quadratic_le {ι : Type} (s : Finset ι) (x h : ι → ℝ) (σ : ι → ℝ) {K : ℝ}
    (hK : 0 ≤ K) :
    finsetLpNorm 2 s (fun i => 129 * x i ^ 2 + K * (x i * h i + h i ^ 2 + σ i * h i)) ≤
      129 * (finsetLpNorm 4 s x * finsetLpNorm 4 s x) + K * (finsetLpNorm 4 s x * finsetLpNorm 4 s h +
        finsetLpNorm 4 s h * finsetLpNorm 4 s h + finsetLpNorm 4 s σ * finsetLpNorm 4 s h) := by
  have a1 := finsetLpNorm_add_le (P := 2) (by norm_num) s (fun i => 129 * x i ^ 2)
    (fun i => K * (x i * h i + h i ^ 2 + σ i * h i))
  have a2 := finsetLpNorm_const_mul_le (P := 2) (by norm_num) s (fun i => x i ^ 2) (a := 129) (by norm_num)
  have a3 := finsetLpNorm_const_mul_le (P := 2) (by norm_num) s (fun i => x i * h i + h i ^ 2 + σ i * h i) hK
  have a4 := finsetLpNorm_add_le (P := 2) (by norm_num) s (fun i => x i * h i + h i ^ 2) (fun i => σ i * h i)
  have a5 := finsetLpNorm_add_le (P := 2) (by norm_num) s (fun i => x i * h i) (fun i => h i ^ 2)
  have b1 := finsetLpNorm_two_mul_le s x x
  have b2 := finsetLpNorm_two_mul_le s x h
  have b3 := finsetLpNorm_two_mul_le s h h
  have b4 := finsetLpNorm_two_mul_le s σ h
  simp only [← sq] at b1 b3
  rw [← sq, ← sq] at *
  have c1 : K * finsetLpNorm 2 s (fun i => x i * h i + h i ^ 2 + σ i * h i) ≤
      K * (finsetLpNorm 4 s x * finsetLpNorm 4 s h + finsetLpNorm 4 s h ^ 2 +
        finsetLpNorm 4 s σ * finsetLpNorm 4 s h) :=
    mul_le_mul_of_nonneg_left (by linarith) hK
  linarith
private theorem finsetLpNorm_levelDeviation_sub_complexLinear_le (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    {D : Finset F.Cell} (hD : D.card ≤ 81) {R : F.FieldChain}
    {U A : ChainChart F} {ζ : ℂ} {C₀ s B : ℝ} (hC : 0 ≤ C₀) (hs : 0 ≤ s) (hB0 : 0 ≤ B)
    (hnear : ContoursNearUnit R D C₀ s)
    (hmis : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1),
      ‖ofUnit (referenceDefect R m c) - 1‖ ≤ contourSpread F C₀ s m)
    (hb : DeviationBall R D (complexLine U A ζ) B B) (hss : SourcesSmall D (complexLine U A ζ))
    (h0 : finsetLpNorm 4 (innerBonds D 0) (fun b => ‖baseSource (complexLine U A ζ) b.1 b.2‖) ≤ B)
    (hmid : finsetLpNorm 2 (lowerBonds D) (fun x => ‖upperSource (complexLine U A ζ) x‖) ≤ B)
    (hσ : C₀ * s ≤ 1 / 64) (hB1 : B < 1) (hH1 : hullBondCount F.blockSide * B ≤ 1)
    (hsm : 8 * (F.blockSide : ℝ) * (hullBondCount F.blockSide * B) ≤ 1 / 1024) (m : ℕ) (hm : m < F.top) :
    finsetLpNorm 2 (innerBonds D m)
        (fun b => ‖levelDeviation R (complexLine U A ζ) m b.1 b.2 - complexLinear R U A ζ m b.1 b.2‖) ≤
      linearDeviationBound F.blockSide B (C₀ * s) := by
  set W := complexLine U A ζ with hW
  set K : ℝ := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hHf0 : 0 ≤ hullFactor F.blockSide := hullFactor_nonneg _
  set a : (m : ℕ) → F.Site m → Fin 4 → ℝ := fun m x d => ‖levelDeviation R W m x d - complexLinear R U A ζ m x d‖
    with ha
  set b : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ := fun m y d =>
    129 * ‖upperSource W ⟨m, (y, d)⟩‖ ^ 2 + 7 * K * (‖upperSource W ⟨m, (y, d)⟩‖ *
      bondHullNorm (y, d) (levelDeviation R W m) + bondHullNorm (y, d) (levelDeviation R W m) ^ 2 +
        contourSpread F C₀ s m * bondHullNorm (y, d) (levelDeviation R W m)) with hbd
  have hN0 : ∀ m (y : F.Site (m + 1)) d, 0 ≤ bondHullNorm (y, d) (levelDeviation R W m) := fun _ _ _ =>
    bondHullSum_nonneg _ fun _ _ => norm_nonneg _
  have hsp0 : ∀ m, 0 ≤ contourSpread F C₀ s m := fun m => by
    unfold contourSpread
    positivity
  have hb0 : ∀ m y d, 0 ≤ b m y d := fun m y d => by
    have := hN0 m y d
    have := hsp0 m
    simp only [hbd]
    positivity
  have hrec : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1),
      a (m + 1) c.1 c.2 ≤ lineBlockAverage (a m) c +
        (b m c.1 c.2 + (fun _ _ _ => (0 : ℝ)) m c.1 c.2 * bondHullSum c (a m)) := by
    intro m hm c hc
    have hm' : m < F.top := by omega
    have hhull := hb.bondHullNorm_le hodd hB0 hm' hc
    have hσle := contourSpread_le (F := F) hodd hC hs m
    have := norm_levelDeviation_sub_complexLinear_succ_le hodd hm R U A ζ (c := c) (hsp0 m) (by linarith)
      (hnear m (by omega) c hc) (hmis m hm c hc)
      (by
        have : 8 * (F.blockSide : ℝ) * bondHullNorm c (levelDeviation R W m) ≤
            8 * (F.blockSide : ℝ) * (hullBondCount F.blockSide * B) :=
          mul_le_mul_of_nonneg_left hhull (by positivity)
        linarith) (by linarith) (hb.det_eq_one hodd hB1 hm' hc) (hss.upper_le _ (mem_lowerBonds hm hc))
    simpa using this
  have hbase : weightedScaleNorm D 0 0 2 0 (a 0) ≤ 129 * B ^ 2 := by
    rw [weightedScaleNorm_zero_weight]
    have e1 : finsetLpNorm 2 (innerBonds D 0) (fun c => a 0 c.1 c.2) ≤
        finsetLpNorm 2 (innerBonds D 0) (fun c => 129 * (‖baseSource W c.1 c.2‖ * ‖baseSource W c.1 c.2‖)) := by
      refine finsetLpNorm_le_of_le (by norm_num) (fun _ _ => norm_nonneg _) fun c hc => ?_
      have hy := hss.base_le c hc
      have hp : purePart (baseSource W c.1 c.2) = baseSource W c.1 c.2 := by
        rw [hW, baseSource_complexLine]
        exact purePart_ofQuat_line _ _ _
      have := norm_unitExp_sub_one_sub_purePart_le (y := baseSource W c.1 c.2) (by linarith)
      rw [hp] at this
      simp only [ha]
      rw [levelDeviation_zero, complexLinear_zero]
      calc _ ≤ 129 * ‖baseSource W c.1 c.2‖ ^ 2 := this
        _ = _ := by ring
    have e2 := finsetLpNorm_const_mul_le (P := 2) (by norm_num) (innerBonds D 0)
      (fun c => ‖baseSource W c.1 c.2‖ * ‖baseSource W c.1 c.2‖) (a := 129) (by norm_num)
    have e3 := finsetLpNorm_two_mul_le (innerBonds D 0) (fun c => ‖baseSource W c.1 c.2‖)
      (fun c => ‖baseSource W c.1 c.2‖)
    have e4 : finsetLpNorm 4 (innerBonds D 0) (fun c => ‖baseSource W c.1 c.2‖) *
        finsetLpNorm 4 (innerBonds D 0) (fun c => ‖baseSource W c.1 c.2‖) ≤ B ^ 2 := by
      have := finsetLpNorm_nonneg 4 (innerBonds D 0) (fun c => ‖baseSource W c.1 c.2‖)
      nlinarith
    linarith
  have hS : ∀ m, m + 1 < F.top → weightedScaleNorm D 0 0 2 (m + 1) (b m) ≤ 129 * B ^ 2 + 7 * K *
      (B * (hullFactor F.blockSide * B) + (hullFactor F.blockSide * B) ^ 2 +
        5 * (C₀ * s) * (hullFactor F.blockSide * B)) := by
    intro m hm
    have hm' : m < F.top := by omega
    rw [weightedScaleNorm_zero_weight]
    have hcomb := finsetLpNorm_quadratic_le (innerBonds D (m + 1)) (fun c => ‖upperSource W ⟨m, c⟩‖)
      (fun c => bondHullNorm (c.1, c.2) (levelDeviation R W m)) (fun _ => contourSpread F C₀ s m) (K := 7 * K)
      (by positivity)
    have hx : finsetLpNorm 4 (innerBonds D (m + 1)) (fun c => ‖upperSource W ⟨m, c⟩‖) ≤ B :=
      (finsetLpNorm_four_le_two _ _).trans
        ((finsetLpNorm_level_le_lowerBonds hm (fun x => ‖upperSource W x‖)).trans hmid)
    have hh : finsetLpNorm 4 (innerBonds D (m + 1)) (fun c => bondHullNorm (c.1, c.2) (levelDeviation R W m)) ≤
        hullFactor F.blockSide * B := by
      have h1 := weightedScaleNorm_bondHullSum_le (D := D) hodd (θ := 0) (by norm_num) hm' 0 4 (by norm_num)
        (g := fun x i => ‖levelDeviation R W m x i‖) (fun _ _ => norm_nonneg _)
      rw [weightedScaleNorm_zero_weight, weightedScaleNorm_zero_weight] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (hb.lpNorm_deviation_le m hm') hHf0)
    have hsg := finsetLpNorm_contourSpread_le hodd hD hC hs m
    have p1 := finsetLpNorm_nonneg 4 (innerBonds D (m + 1)) (fun c => ‖upperSource W ⟨m, c⟩‖)
    have p2 := finsetLpNorm_nonneg 4 (innerBonds D (m + 1))
      (fun c => bondHullNorm (c.1, c.2) (levelDeviation R W m))
    refine hcomb.trans ?_
    have q1 := mul_le_mul hx hx p1 hB0
    have q2 := mul_le_mul hx hh p2 hB0
    have q3 := mul_le_mul hh hh p2 (by positivity)
    have q4 := mul_le_mul hsg hh p2 (by positivity)
    have q5 : 7 * K * (finsetLpNorm 4 (innerBonds D (m + 1)) (fun c => ‖upperSource W ⟨m, c⟩‖) *
          finsetLpNorm 4 (innerBonds D (m + 1)) (fun c => bondHullNorm (c.1, c.2) (levelDeviation R W m)) +
        finsetLpNorm 4 (innerBonds D (m + 1)) (fun c => bondHullNorm (c.1, c.2) (levelDeviation R W m)) *
          finsetLpNorm 4 (innerBonds D (m + 1)) (fun c => bondHullNorm (c.1, c.2) (levelDeviation R W m)) +
        finsetLpNorm 4 (innerBonds D (m + 1)) (fun _ : F.Site (m + 1) × Fin 4 => contourSpread F C₀ s m) *
          finsetLpNorm 4 (innerBonds D (m + 1)) (fun c => bondHullNorm (c.1, c.2) (levelDeviation R W m))) ≤
        7 * K * (B * (hullFactor F.blockSide * B) + (hullFactor F.blockSide * B) ^ 2 +
          5 * (C₀ * s) * (hullFactor F.blockSide * B)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith
    nlinarith
  have hc := weightedScaleNorm_two_le_of_small hodd h2 D 0 (θ := 0) (by norm_num) a b (fun _ _ _ => 0)
    (fun _ _ _ => norm_nonneg _) hb0 (fun _ _ _ => le_rfl) hrec (ε := 0) le_rfl (by
      have : 0 ≤ hullFactor F.blockSide * B := by positivity
      positivity) (fun _ _ _ _ => le_rfl) hS (by norm_num) m hm
  rw [weightedScaleNorm_zero_weight] at hc
  refine hc.trans ?_
  unfold linearDeviationBound
  rw [← hK]
  have : 5 * (C₀ * s) = 5 * (C₀ * s) := rfl
  nlinarith
private def topDeviation (R : F.FieldChain) (U A : ChainChart F) (b : F.Site F.top × Fin 4) (ζ : ℂ) :
    ComplexQuat :=
  complexGaugedContourAverage (complexChartField R (complexLine U A ζ) F.depth)
      (complexBalancingGauge (complexChartField R (complexLine U A ζ) F.depth) (R F.depth)) b *
      ofUnit (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b))⁻¹ -
    ((‖_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b‖ : ℝ) : ℂ) • (1 : ComplexQuat) - complexLinear R U A ζ F.top b.1 b.2
set_option maxHeartbeats 1000000 in
private theorem norm_topDeviation_le (hodd : Odd F.blockSide) (R : F.FieldChain) (U A : ChainChart F) (ζ : ℂ)
    {c : F.Site F.top × Fin 4} {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy (R F.depth) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) c))⁻¹) - 1‖ ≤ σ)
    (hsm : 8 * (F.blockSide : ℝ) * bondHullNorm c (levelDeviation R (complexLine U A ζ) F.depth) ≤ 1 / 1024)
    (hh1 : bondHullNorm c (levelDeviation R (complexLine U A ζ) F.depth) ≤ 1)
    (hKs : 200000 * (F.blockSide : ℝ) ^ 2 * (bondHullNorm c (levelDeviation R (complexLine U A ζ) F.depth) ^ 2 +
      σ * bondHullNorm c (levelDeviation R (complexLine U A ζ) F.depth)) ≤ 1)
    (hd : HoldsOnHull c (fun b i => (complexChartField R (complexLine U A ζ) F.depth b i).det = 1)) :
    ‖topDeviation R U A c ζ‖ ≤ 6 * (200000 * (F.blockSide : ℝ) ^ 2 *
        (bondHullNorm c (levelDeviation R (complexLine U A ζ) F.depth) ^ 2 +
          σ * bondHullNorm c (levelDeviation R (complexLine U A ζ) F.depth))) +
      bondHullSum c (fun x i =>
        ‖levelDeviation R (complexLine U A ζ) F.depth x i - complexLinear R U A ζ F.depth x i‖) := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hj : F.depth + 1 ≤ F.top := le_rfl
  set W := complexLine U A ζ with hW
  set y := levelDeviation R W F.depth with hy
  set h := bondHullNorm c y with hh
  set K : ℝ := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hK1 : 1 ≤ K := by
    rw [hK]
    nlinarith
  have hh0 : 0 ≤ h := bondHullSum_nonneg _ fun _ _ => norm_nonneg _
  obtain ⟨hpos, hq, hρ⟩ := remainder_bounds hodd hj hσ hsm href
  have hM : complexGaugedContourAverage (complexChartField R W F.depth)
      (complexBalancingGauge (complexChartField R W F.depth) (R F.depth)) c = liftedBondMean (R F.depth) c y :=
    complexGaugedContourAverage_eq_liftedBondMean hodd hj (R := R F.depth) hd
  set M := liftedBondMean (R F.depth) c y with hMd
  have hM0 : M ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  set r₀ : ℝ := ‖_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) c‖ with hr₀
  set w : UnitQuaternion := polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) c) with hw
  set q := unitRemainder (R F.depth) c y with hqd
  set ρ := sqrtRemainder (R F.depth) c y with hρd
  set P := purePart (transportedAverage (R F.depth) y c) with hP
  set Pl := transportedAverage (R F.depth) (complexLinear R U A ζ F.depth) c with hPl
  have e1 : unitPart M * ofUnit w⁻¹ = 1 + P + q := by
    rw [hqd, unitRemainder]
    abel
  have e2 : principalSqrt M.det = (r₀ : ℂ) + ρ := by
    rw [hρd, sqrtRemainder]
    abel
  have e4 : M * ofUnit w⁻¹ = ((r₀ : ℂ) + ρ) • (1 + P + q) := by
    calc M * ofUnit w⁻¹ = (principalSqrt M.det • unitPart M) * ofUnit w⁻¹ := by
          rw [principalSqrt_det_smul_unitPart hM0]
      _ = principalSqrt M.det • (unitPart M * ofUnit w⁻¹) := smul_mul_assoc _ _ _
      _ = _ := by rw [e1, e2]
  have hlin : complexLinear R U A ζ F.top c.1 c.2 = Pl := by
    have := complexLinear_succ R U A ζ (m := F.depth) c.1 c.2
    rw [if_neg (lt_irrefl _), add_zero] at this
    exact this
  have hG : topDeviation R U A c ζ = ρ • (1 + P + q) + (r₀ : ℂ) • q + ((r₀ : ℂ) - 1) • P + (P - Pl) := by
    unfold topDeviation
    rw [hM, e4, hlin]
    module
  have hpure : purePart Pl = Pl := by
    rw [hPl, purePart_transportedAverage]
    congr 1
    funext x i
    exact purePart_complexLinear R U A ζ F.depth x i
  have hPd : ‖P - Pl‖ ≤ lineBlockAverage (fun x i => ‖y x i - complexLinear R U A ζ F.depth x i‖) c := by
    have e : P - Pl =
        purePart (transportedAverage (R F.depth) (fun x i => y x i - complexLinear R U A ζ F.depth x i) c) := by
      rw [transportedAverage_sub, purePart_sub, hpure]
    rw [e]
    exact (norm_purePart_le _).trans (norm_transportedAverage_le hodd _ _ c)
  have hPd' := hPd.trans (lineBlockAverage_le_bondHullSum hodd
    (f := fun x i => ‖y x i - complexLinear R U A ζ F.depth x i‖) (fun _ _ => norm_nonneg _) c)
  have hP1 : ‖P‖ ≤ h :=
    (norm_purePart_le _).trans ((norm_transportedAverage_le hodd _ _ c).trans
      (lineBlockAverage_le_bondHullSum hodd (fun _ _ => norm_nonneg _) c))
  have hr1 : |r₀ - 1| ≤ σ := abs_norm_contourAverage_sub_one_le hodd href
  have hr2 : ‖(r₀ : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have := abs_le.1 hr1
    rw [abs_le]
    constructor <;> linarith
  have hr3 : ‖(r₀ : ℂ) - 1‖ ≤ σ := by
    have : (r₀ : ℂ) - 1 = ((r₀ - 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hr1
  have hX : ‖1 + P + q‖ ≤ 3 := by
    have h1 := norm_add_le (1 + P) q
    have h2 := norm_add_le (1 : ComplexQuat) P
    rw [CStarRing.norm_one] at h2
    linarith
  have n1 : ‖ρ • (1 + P + q)‖ ≤ 3 * (K * (h ^ 2 + σ * h)) := by
    rw [norm_smul]
    have h0 := norm_nonneg (1 + P + q)
    have h1 := norm_nonneg ρ
    nlinarith
  have n2 : ‖(r₀ : ℂ) • q‖ ≤ 2 * (K * (h ^ 2 + σ * h)) := by
    rw [norm_smul]
    exact mul_le_mul hr2 hq (norm_nonneg _) (by norm_num)
  have n3 : ‖((r₀ : ℂ) - 1) • P‖ ≤ K * (h ^ 2 + σ * h) := by
    rw [norm_smul]
    have h1 : ‖(r₀ : ℂ) - 1‖ * ‖P‖ ≤ σ * h := mul_le_mul hr3 hP1 (norm_nonneg _) hσ0
    have h2 : 0 ≤ h ^ 2 + σ * h := add_nonneg (sq_nonneg _) (mul_nonneg hσ0 hh0)
    nlinarith
  rw [hG]
  have t1 := norm_add_le (ρ • (1 + P + q) + (r₀ : ℂ) • q + ((r₀ : ℂ) - 1) • P) (P - Pl)
  have t2 := norm_add_le (ρ • (1 + P + q) + (r₀ : ℂ) • q) (((r₀ : ℂ) - 1) • P)
  have t3 := norm_add_le (ρ • (1 + P + q)) ((r₀ : ℂ) • q)
  linarith
private theorem analyticAt_complexGaugedContourAverage {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {z : P}
    (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {X : P → F.ComplexField j} (R : F.GaugeField j)
    {c : F.Site (j + 1) × Fin 4} {t σ : ℝ} (ht : 0 ≤ t)
    (hτ : 4 * (F.blockSide : ℝ) * t ≤ 1 / 1024) (hg : ContoursNearReal (X z) R t σ c)
    (hX : HoldsOnHull c (fun b i => AnalyticAt ℂ (fun w => X w b i) z)) :
    AnalyticAt ℂ (fun w => complexGaugedContourAverage (X w) (complexBalancingGauge (X w) R) c) z := by
  have hleg : ∀ h ∈ centredCube F.blockSide, ∀ π,
      AnalyticAt ℂ (fun w => complexPathHolonomy (X w) (refineSite c.1) (axisPath h π)) z :=
    fun h hh π => analyticAt_complexPathHolonomy
      (pathBondsSatisfy_axisPath _ hodd.pos (fun v hv k hk => (hX.1 v hv k hk).1) hh π)
  have hleg' : ∀ h ∈ centredCube F.blockSide, ∀ π, AnalyticAt ℂ
      (fun w => complexPathHolonomy (X w) (refineSite (c.1 + unitStep (j + 1) c.2)) (axisPath h π)) z :=
    fun h hh π => analyticAt_complexPathHolonomy
      (pathBondsSatisfy_axisPath _ hodd.pos (fun v hv k hk => (hX.1 v hv k hk).2) hh π)
  have hline : ∀ h ∈ centredCube F.blockSide, AnalyticAt ℂ
      (fun w => complexPathHolonomy (X w) (refineSite c.1 + siteOfCoords j h)
        (List.replicate F.blockSide (c.2, true))) z :=
    fun h hh => analyticAt_complexPathHolonomy (pathBondsSatisfy_replicate _ _ _ fun r hr => hX.2 h hh r hr)
  have hcm : AnalyticAt ℂ (fun w => complexContourAverage (X w) c) z := by
    simp only [complexContourAverage]
    have hs : AnalyticAt ℂ (fun w => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        complexPathHolonomy (X w) (refineSite c.1) (bondContour F.blockSide h π c.2)) z := by
      refine Finset.analyticAt_fun_sum _ fun h hh => Finset.analyticAt_fun_sum _ fun π _ => ?_
      simp only [complexPathHolonomy_bondContour hj]
      exact ((hleg h hh π).mul (hline h hh)).mul (analyticAt_adjugate (hleg' h hh π))
    exact analyticAt_const_smul_complexQuat _ hs
  have hτ8 : 4 * (F.blockSide : ℝ) * t ≤ 1 / 8 := by linarith
  have hk := analyticAt_complexBalancingGauge hodd R ht hτ8 hleg hg.nearLegs
  have hk' := analyticAt_complexBalancingGauge hodd R ht hτ8 hleg' hg.nearFarLegs
  simp only [complexGaugedContourAverage]
  exact (hk.mul hcm).mul (analyticAt_adjugate hk')
private theorem differentiableAt_topDeviation (hodd : Odd F.blockSide) {D : Finset F.Cell} {R : F.FieldChain}
    {U A : ChainChart F} {ζ : ℂ}
    {t σ : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hσ : σ ≤ 1 / 64) (hτ : 4 * (F.blockSide : ℝ) * t ≤ 1 / 1024)
    (hb : DeviationBall R D (complexLine U A ζ) t t) (hss : SourcesSmall D (complexLine U A ζ))
    (href : ∀ j, j + 1 ≤ F.top → ∀ c ∈ innerBonds D (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy (R j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R j) c))⁻¹) - 1‖ ≤ σ)
    {c : F.Site F.top × Fin 4} (hc : c ∈ innerBonds D F.top) : DifferentiableAt ℂ (topDeviation R U A c) ζ := by
  have hu : ∀ b ∈ innerBonds D 0, AnalyticAt ℂ (fun w => complexifiedImaginary ((complexLine U A w).re.fine b.1 b.2)
      ((complexLine U A w).im.fine b.1 b.2)) ζ := by
    intro b _
    have e : (fun w => complexifiedImaginary ((complexLine U A w).re.fine b.1 b.2)
        ((complexLine U A w).im.fine b.1 b.2)) =
        fun w => ofQuat (U.fine b.1 b.2 : ℍ[ℝ]) + w • ofQuat (A.fine b.1 b.2 : ℍ[ℝ]) :=
      funext fun w => baseSource_complexLine U A w b.1 b.2
    rw [e]
    exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hmu : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds D (j + 1),
      AnalyticAt ℂ (fun w => complexifiedImaginary ((complexLine U A w).re.coarse j b.1 b.2)
        ((complexLine U A w).im.coarse j b.1 b.2)) ζ := by
    intro j _ b _
    have e : (fun w => complexifiedImaginary ((complexLine U A w).re.coarse j b.1 b.2)
        ((complexLine U A w).im.coarse j b.1 b.2)) =
        fun w => ofQuat (U.coarse j b.1 b.2 : ℍ[ℝ]) + w • ofQuat (A.coarse j b.1 b.2 : ℍ[ℝ]) :=
      funext fun w => upperSource_complexLine U A w ⟨j, b⟩
    rw [e]
    exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hf := analyticAt_complexChartField hodd R (D := D) (W := complexLine U A) (z := ζ) ht ht1 hσ hτ hu
    (fun b hb' => (hss.base_le b hb').trans (by norm_num))
    hmu (fun j hj b hb' => (hss.upper_le ⟨j, b⟩ (mem_lowerBonds hj hb')).trans (by norm_num))
    (fun j hj b hb' => hb.norm_deviation_le j hj b hb') href F.depth (Nat.lt_succ_self _)
  have hj' : F.depth < F.top := Nat.lt_succ_self _
  have hX : HoldsOnHull c (fun b i => AnalyticAt ℂ (fun w => complexChartField R (complexLine U A w) F.depth b i) ζ) :=
    holdsOnHull_of_innerBonds hj' hodd hc fun b hb' => hf b hb'
  have hgood : ∀ b ∈ innerBonds D F.depth,
      BondNearReal (complexChartField R (complexLine U A ζ) F.depth) (R F.depth) t b.1 b.2 := fun b hb' =>
    ⟨hb.norm_deviation_le F.depth hj' b hb', det_complexChartField_of_norm_lt_one R _ F.depth _ _
      (lt_of_le_of_lt (hb.norm_deviation_le F.depth hj' b hb') ht1)⟩
  have hhull : HoldsOnHull c
      (fun b i => BondNearReal (complexChartField R (complexLine U A ζ) F.depth) (R F.depth) t b i) :=
    holdsOnHull_of_innerBonds hj' hodd hc hgood
  have hcg : ContoursNearReal (complexChartField R (complexLine U A ζ) F.depth) (R F.depth) t σ c :=
    ⟨fun h hh π => pathNearReal_axisPath _ hodd.pos (fun v hv k hk => (hhull.1 v hv k hk).1) hh π,
      fun h hh => pathNearReal_replicate _ _ _ fun r hr => hhull.2 h hh r hr,
      fun h hh π => pathNearReal_axisPath _ hodd.pos (fun v hv k hk => (hhull.1 v hv k hk).2) hh π,
      fun h hh π => href F.depth le_rfl c hc h hh π⟩
  have hM := analyticAt_complexGaugedContourAverage (X := fun w => complexChartField R (complexLine U A w) F.depth)
    hodd le_rfl (R F.depth) ht hτ hcg hX
  have hl : AnalyticAt ℂ (fun w => complexLinear R U A w F.top c.1 c.2) ζ :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  exact (((hM.mul analyticAt_const).sub analyticAt_const).sub hl).differentiableAt
private theorem complexLine_ofReal (U A : ChainChart F) (τ : ℝ) :
    complexLine U A (τ : ℂ) = realChart (chartMove U A τ) := by
  simp [complexLine, spanChart, realChart, chartMove, chartShiftMulti, zeroChart]
private theorem topDeviation_ofReal (R : F.FieldChain) (U A : ChainChart F) (b : F.Site F.top × Fin 4) (τ : ℝ) :
    topDeviation R U A b (τ : ℂ) = ofQuat (gaugedBondAverage R (chartMove U A τ) F.depth b *
      (((polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b))⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
      (‖_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b‖ : ℝ) • (1 : ℍ[ℝ]) - linearPart R U F.top b.1 b.2 -
        τ • linearPart R A F.top b.1 b.2) := by
  have hk : complexBalancingGauge (complexifyField (chartField R (chartMove U A τ) F.depth)) (R F.depth) =
      fun y => ofUnit (balancingGauge (chartField R (chartMove U A τ) F.depth) (R F.depth) y) := by
    funext y
    exact complexBalancingGauge_complexify _ _ _
  unfold topDeviation complexLinear
  rw [complexLine_ofReal, complexChartField_realChart, hk, complexGaugedContourAverage_complexify]
  simp only [ofQuat_sub, ofQuat_mul, ofQuat_smul, ofQuat_one]
  have e : ofQuat (((polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b))⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      ofUnit (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b))⁻¹ := rfl
  rw [e]
  unfold gaugedBondAverage
  abel
private theorem norm_deriv_mul_sub_le {p : ℝ → ℍ[ℝ]} {p' : ℍ[ℝ]} (hp : HasDerivAt p p' 0) (w L : ℍ[ℝ]) {b ρ : ℝ}
    (hρ : 0 < ρ) (hb : ∀ τ : ℝ, |τ| < ρ → ‖(p τ - p 0) * w - τ • L‖ ≤ b * |τ|) : ‖p' * w - L‖ ≤ b := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hw : 0 < ‖w‖ + 1 := by positivity
  have h1 := (hasDerivAt_iff_isLittleO_nhds_zero.1 hp).def (c := ε / (‖w‖ + 1)) (by positivity)
  have h2 : ∀ᶠ τ in 𝓝 (0 : ℝ), |τ| < ρ := by
    have := Metric.ball_mem_nhds (0 : ℝ) hρ
    filter_upwards [this] with τ hτ
    simpa [Real.dist_eq] using hτ
  have h3 : ∀ᶠ τ in 𝓝[≠] (0 : ℝ), τ ≠ 0 ∧ |τ| < ρ ∧
      ‖p (0 + τ) - p 0 - τ • p'‖ ≤ ε / (‖w‖ + 1) * ‖τ‖ := by
    filter_upwards [self_mem_nhdsWithin, h2.filter_mono nhdsWithin_le_nhds, h1.filter_mono nhdsWithin_le_nhds]
      with τ a1 a2 a3
    exact ⟨a1, a2, a3⟩
  obtain ⟨τ, hτ0, hτρ, hτ⟩ := h3.exists
  rw [zero_add] at hτ
  have hτp : 0 < |τ| := abs_pos.2 hτ0
  have e : τ • (p' * w - L) = ((p τ - p 0) * w - τ • L) - (p τ - p 0 - τ • p') * w := by
    simp only [sub_mul, smul_sub, smul_mul_assoc]
    abel
  have n1 : ‖τ • (p' * w - L)‖ = |τ| * ‖p' * w - L‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have n2 : ‖(p τ - p 0 - τ • p') * w‖ ≤ ε * |τ| := by
    rw [norm_mul]
    have h4 : ‖τ‖ = |τ| := Real.norm_eq_abs τ
    rw [h4] at hτ
    calc _ ≤ ε / (‖w‖ + 1) * |τ| * ‖w‖ := mul_le_mul_of_nonneg_right hτ (norm_nonneg _)
      _ ≤ ε * |τ| := by
        have : ε / (‖w‖ + 1) * ‖w‖ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hw]
          nlinarith [norm_nonneg w]
        nlinarith
  have n3 := hb τ hτρ
  have n4 : |τ| * ‖p' * w - L‖ ≤ |τ| * (b + ε) := by
    rw [← n1, e]
    refine (norm_sub_le _ _).trans ?_
    nlinarith
  exact le_of_mul_le_mul_left n4 hτp
private def topDeviationBound (L : ℕ) (y σ : ℝ) : ℝ :=
  6 * (200000 * (L : ℝ) ^ 2 * ((hullBondCount L * (8 * y)) ^ 2 + σ * (hullBondCount L * (8 * y)))) +
    hullFactor L * linearDeviationBound L (8 * y) σ
private def topQuadraticConst (L : ℕ) : ℝ :=
  6 * (200000 * (L : ℝ) ^ 2) * 64 * hullBondCount L ^ 2 + hullFactor L * (2 * 142 * 129 * 64 + 568 * 129 * 64 +
    568 * 7 * (200000 * (L : ℝ) ^ 2) * (64 * hullFactor L + 64 * hullFactor L ^ 2))
private def topMixedConst (L : ℕ) : ℝ :=
  6 * (200000 * (L : ℝ) ^ 2) * 8 * hullBondCount L +
    hullFactor L * (568 * 7 * (200000 * (L : ℝ) ^ 2) * 40 * hullFactor L)
private theorem topDeviationBound_le (L : ℕ) {y σ : ℝ} (hy : 0 ≤ y) (hσ : 0 ≤ σ) :
    topDeviationBound L y σ ≤ (topQuadraticConst L + topMixedConst L) * (y ^ 2 + σ * y) := by
  have hH := hullBondCount_nonneg L
  have hF := hullFactor_nonneg L
  have hA : 0 ≤ topQuadraticConst L := by
    unfold topQuadraticConst
    positivity
  have hB : 0 ≤ topMixedConst L := by
    unfold topMixedConst
    positivity
  have e : topDeviationBound L y σ = topQuadraticConst L * y ^ 2 + topMixedConst L * (σ * y) := by
    unfold topDeviationBound linearDeviationBound topQuadraticConst topMixedConst
    ring
  have e2 : (topQuadraticConst L + topMixedConst L) * (y ^ 2 + σ * y) =
      topQuadraticConst L * y ^ 2 + topMixedConst L * (σ * y) + topQuadraticConst L * (σ * y) +
        topMixedConst L * y ^ 2 := by ring
  have p1 : 0 ≤ topQuadraticConst L * (σ * y) := by positivity
  have p2 : 0 ≤ topMixedConst L * y ^ 2 := by positivity
  rw [e, e2]
  linarith
private theorem topConst_pos {L : ℕ} (hL : 0 < L) : 0 < topQuadraticConst L + topMixedConst L := by
  have hH := hullBondCount_nonneg L
  have hF := hullFactor_nonneg L
  have hA : 0 ≤ topQuadraticConst L := by
    unfold topQuadraticConst
    positivity
  have hH1 : 0 < hullBondCount L := by
    unfold hullBondCount
    positivity
  have : 0 < topMixedConst L := by
    unfold topMixedConst
    positivity
  linarith
set_option maxHeartbeats 1000000 in
private theorem topDeviation_bound_and_differentiableAt (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    {S : Finset F.Cell} {z : F.Cell} {R : F.FieldChain}
    {U A : ChainChart F} {C s y : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hnear : ContoursNearUnit R (cellBall S z 1) C s)
    (hmis : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds (cellBall S z 1) (m + 1),
      ‖ofUnit (referenceDefect R m c) - 1‖ ≤ contourSpread F C s m)
    (hlev : ∀ W : ComplexChainChart F,
      Real.sqrt (Real.sqrt (∑ b ∈ innerBonds (cellBall S z 1) 0, ‖levelDeviation R W 0 b.1 b.2‖ ^ 4)) ≤ 2 * y →
      (∀ j, j + 1 < F.top →
        Real.sqrt (∑ c ∈ innerBonds (cellBall S z 1) (j + 1), ‖levelSource W j c.1 c.2 - 1‖ ^ 2) ≤ 2 * y) →
      ∀ j, j < F.top →
        Real.sqrt (Real.sqrt (∑ b ∈ innerBonds (cellBall S z 1) j, ‖levelDeviation R W j b.1 b.2‖ ^ 4)) ≤
          4 * (2 * y))
    (hy : SmallParameter F.blockSide y) (hCs : C * s ≤ y) {ζ : ℂ} (hz : spanLocalNorm S R U ![A] ![ζ] z ≤ y)
    {b : F.Site F.top × Fin 4} (hb : b ∈ innerBonds (cellBall S z 1) F.top) :
    ‖topDeviation R U A b ζ‖ ≤ topDeviationBound F.blockSide y (C * s) ∧
      DifferentiableAt ℂ (topDeviation R U A b) ζ := by
  have hy0 : 0 < y := hy.pos
  have hy1 := hy.le_bound
  set H := hullBondCount F.blockSide with hH
  have hH0 : 0 ≤ H := hullBondCount_nonneg _
  have hHf0 : 0 ≤ hullFactor F.blockSide := hullFactor_nonneg _
  set K : ℝ := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hsz : SourceBounds S z R (complexLine U A ζ) y := sourceBounds_spanChart hodd R U ![A] ![ζ] hz
  obtain ⟨hss, hball⟩ := deviationBall_of_finsetLpNorm_le (hlev (complexLine U A ζ)) hsz.base_le hsz.upper_le
    (by linarith)
  have hr : hullBallRadius F.blockSide * (8192 * (F.blockSide : ℝ)) = 1 := by
    unfold hullBallRadius
    field_simp
  have hLy : 0 ≤ (F.blockSide : ℝ) * y := by positivity
  have f1 : 8 * (F.blockSide : ℝ) * (H * (8 * y)) ≤ 1 / 1024 := by
    have := mul_le_mul_of_nonneg_right hy.count_le_radius (by positivity : (0 : ℝ) ≤ 8192 * (F.blockSide : ℝ))
    rw [hr] at this
    nlinarith
  have f2 : H * (8 * y) ≤ 1 := by
    have := hy.count_le
    rw [← hH] at this
    nlinarith
  have f4 : C * s ≤ 1 / 64 := by linarith
  have hCs0 : 0 ≤ C * s := by positivity
  have f5 : 8 * y < 1 := by linarith
  have f3 : K * ((H * (8 * y)) ^ 2 + C * s * (H * (8 * y))) ≤ 1 := by
    have g1 := hy.count_scale_le
    rw [← hK, ← hH] at g1
    have g2 := hy.count_le
    rw [← hH] at g2
    have p1 : H * K * y ≤ 1 / 4608 := by
      have : 4608 * H * K * y = 4608 * (H * K * y) := by ring
      linarith
    have q1 : (H * K * y) * (64 * H * y) ≤ 1 / 4608 * 1 := mul_le_mul p1 g2 (by positivity) (by norm_num)
    have q2 : (H * K * y) * (8 * y) ≤ 1 / 4608 * 1 := mul_le_mul p1 (by linarith) (by positivity) (by norm_num)
    have q3 : K * (C * s * (H * (8 * y))) ≤ K * (y * (H * (8 * y))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCs (by positivity)) hK0
    nlinarith
  have f6 : 4 * (F.blockSide : ℝ) * (8 * y) ≤ 1 / 1024 := by
    have := mul_le_mul_of_nonneg_right hy.le_radius (by positivity : (0 : ℝ) ≤ 8192 * (F.blockSide : ℝ))
    rw [hr] at this
    nlinarith
  have hB0 : 0 ≤ 8 * y := by positivity
  have hlin := finsetLpNorm_levelDeviation_sub_complexLinear_le hodd h2 (BlockLines.card_cellBall_one_le S z) hC hs
    hB0 hnear hmis hball hss (hsz.base_le.trans (by linarith))
    (hsz.upper_le.trans (by linarith)) f4 f5 f2 f1 F.depth (Nat.lt_succ_self _)
  have hdets := hball.det_eq_one hodd f5 (Nat.lt_succ_self _) hb
  have hhull := hball.bondHullNorm_le hodd hB0 (Nat.lt_succ_self _) hb
  rw [← hH] at hhull
  have hn0 : 0 ≤ bondHullNorm b (levelDeviation R (complexLine U A ζ) F.depth) :=
    bondHullSum_nonneg _ fun _ _ => norm_nonneg _
  have href : ∀ j, j + 1 ≤ F.top → ∀ c ∈ innerBonds (cellBall S z 1) (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy (R j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R j) c))⁻¹) - 1‖ ≤ C * s :=
    fun j hj c hc h hh π => (hnear j hj c hc h hh π).trans (contourSpread_le hodd hC hs j)
  have hmono : K * (bondHullNorm b (levelDeviation R (complexLine U A ζ) F.depth) ^ 2 +
      C * s * bondHullNorm b (levelDeviation R (complexLine U A ζ) F.depth)) ≤
      K * ((H * (8 * y)) ^ 2 + C * s * (H * (8 * y))) := by
    refine mul_le_mul_of_nonneg_left ?_ hK0
    have := pow_le_pow_left₀ hn0 hhull 2
    have := mul_le_mul_of_nonneg_left hhull hCs0
    linarith
  have htop := norm_topDeviation_le hodd R U A ζ (c := b) (σ := C * s) hCs0 f4 (href F.depth le_rfl b hb)
    (by
      have : 8 * (F.blockSide : ℝ) * bondHullNorm b (levelDeviation R (complexLine U A ζ) F.depth) ≤
          8 * (F.blockSide : ℝ) * (H * (8 * y)) :=
        mul_le_mul_of_nonneg_left hhull (by positivity)
      linarith) (by linarith) (hmono.trans f3) hdets
  refine ⟨htop.trans ?_, differentiableAt_topDeviation hodd hB0 f5 f4 f6 hball hss href hb⟩
  have h1 := weightedScaleNorm_bondHullSum_le (D := cellBall S z 1) hodd (θ := 0) (by norm_num)
    (Nat.lt_succ_self F.depth) 0 2 (by norm_num)
    (g := fun x i => ‖levelDeviation R (complexLine U A ζ) F.depth x i - complexLinear R U A ζ F.depth x i‖)
    (fun _ _ => norm_nonneg _)
  rw [weightedScaleNorm_zero_weight, weightedScaleNorm_zero_weight] at h1
  have h3 := abs_le_finsetLpNorm (P := 2) (by norm_num) (s := innerBonds (cellBall S z 1) (F.depth + 1))
    (fun c => bondHullSum (c.1, c.2)
      (fun x i => ‖levelDeviation R (complexLine U A ζ) F.depth x i - complexLinear R U A ζ F.depth x i‖)) hb
  rw [abs_of_nonneg (bondHullSum_nonneg _ fun _ _ => norm_nonneg _)] at h3
  have h4 : bondHullSum b
      (fun x i => ‖levelDeviation R (complexLine U A ζ) F.depth x i - complexLinear R U A ζ F.depth x i‖) ≤
      hullFactor F.blockSide * linearDeviationBound F.blockSide (8 * y) (C * s) :=
    (h3.trans h1).trans (mul_le_mul_of_nonneg_left hlin hHf0)
  unfold topDeviationBound
  rw [← hK, ← hH]
  linarith
private theorem chartShift_zero (U A : ChainChart F) : chartMove U A 0 = U := by apply _root_.YangMills.Construction.MisfitVariation.chartMove_zero <;> assumption
private theorem norm_coe_inv_sub_one (g : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
private theorem sum_innerBonds_top_le (hodd : Odd F.blockSide) (S : Finset F.Cell) (f : F.Cell → ℝ)
    (hf : ∀ z, 0 ≤ f z) :
    ∑ b ∈ innerBonds S F.top, f b.1 ≤ 4 * ∑ z ∈ S, f z := by
  have hsub : innerBonds S F.top ⊆ S ×ˢ (Finset.univ : Finset (Fin 4)) := by
    intro b hb
    have h1 := BlockLines.enclosingCell_mem hodd (ChartCoordinates.innerBonds_ends hb).1
    rw [enclosingCell_top] at h1
    exact Finset.mem_product.2 ⟨h1, Finset.mem_univ _⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hf _).trans (le_of_eq ?_)
  rw [Finset.sum_product]
  simp [Finset.mul_sum]
set_option maxHeartbeats 2000000 in
theorem topMeanVelocityStatement_holds (hrec : UniformQuarticBoundAcrossLevels)
    (hbd : referenceBoundsStatement) (htop : linearPartLocalBoundStatement) (hreg : smallChartIsRegularStatement) :
    topMeanVelocityStatement := by
  intro del hdel hdel8
  obtain ⟨C, c₀, L1, hC, hc₀, hbr⟩ := hbd
  obtain ⟨Ct, hCt, htop'⟩ := htop
  obtain ⟨L3, hR⟩ := hreg
  refine ⟨max (max L1 L3) 5, fun L hodd hL => ?_⟩
  have l1 : L1 ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have l3 : L3 ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have h5 : 5 ≤ L := (le_max_right _ _).trans hL
  obtain ⟨c₁, hc₁, -, hlev⟩ := quartic_levelDeviation_bound hrec L hodd h5 hC.le
  obtain ⟨y₀, hy₀, hsz⟩ := exists_smallParameter (L := L) hodd.pos
  obtain ⟨c₃, hc₃, hR'⟩ := hR L hodd l3 del hdel hdel8
  set E : ℝ := C + 5 with hE
  have hE5 : 5 ≤ E := by linarith
  have hE0 : 0 < E := by linarith
  set Kf := topQuadraticConst L + topMixedConst L with hKf
  have hKf0 : 0 < Kf := topConst_pos hodd.pos
  set Eq : ℝ := E ^ 2 + C * E with hEq
  have hEq0 : 0 < Eq := by positivity
  set Cv : ℝ := Kf * Eq + Ct * C with hCv
  have hCv0 : 0 < Cv := by positivity
  set Cval : ℝ := 2 * (Kf * Eq) + 2 * C + 2 * Ct with hCval
  have hCval0 : 0 < Cval := by positivity
  set c : ℝ := min (min c₀ c₁) (min c₃ (min 1 (min (y₀ / (2 * E)) (c₁ / (4 * E))))) with hcd
  have hc0 : 0 < c := by
    refine lt_min (lt_min hc₀ hc₁) (lt_min hc₃ (lt_min one_pos (lt_min ?_ ?_))) <;> positivity
  have c_c₀ : c ≤ c₀ := (min_le_left _ _).trans (min_le_left _ _)
  have c_c₁ : c ≤ c₁ := (min_le_left _ _).trans (min_le_right _ _)
  have c_c₃ : c ≤ c₃ := (min_le_right _ _).trans (min_le_left _ _)
  have c_1 : c ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have c_y : c ≤ y₀ / (2 * E) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have c_4 : c ≤ c₁ / (4 * E) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨c, Cval + 2 * Cv, hc0, by positivity, ?_⟩
  intro F m S hFL hamb hm hregS s V hs hsc hcold U hU
  subst hFL
  have hoddF : Odd F.blockSide := hodd
  have h2 : 2 ≤ F.blockSide := by omega
  have hL1' : L1 ≤ F.blockSide := l1
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hbr F m S hoddF hL1' hamb hm hregS s V hs (hsc.trans c_c₀) hcold
  obtain ⟨hregU, hnorm⟩ := hR' F m S rfl hamb hm hregS s V hs (hsc.trans c_c₃) hcold U (hU.trans c_c₃)
  set R := referenceFieldChain S V with hRd
  have hu0 : 0 ≤ supWeightedNorm S del R U := Real.iSup_nonneg fun _ => Real.sqrt_nonneg _
  set u := supWeightedNorm S del R U with hud
  have hsu : 0 < s + u := by positivity
  have hsu2 : s + u ≤ 2 := by linarith [hsc.trans c_1, hU.trans c_1]
  set y : ℝ := E * (s + u) with hyd
  have hy0 : 0 < y := by positivity
  have hsuc : s + u ≤ 2 * c := by linarith
  have hyy₀ : y ≤ y₀ := by
    have h1 := c_y
    rw [le_div_iff₀ (by positivity)] at h1
    have : E * (s + u) ≤ E * (2 * c) := mul_le_mul_of_nonneg_left hsuc hE0.le
    rw [hyd]
    linarith
  have h2y : 2 * y ≤ c₁ := by
    have h1 := c_4
    rw [le_div_iff₀ (by positivity)] at h1
    have : E * (s + u) ≤ E * (2 * c) := mul_le_mul_of_nonneg_left hsuc hE0.le
    rw [hyd]
    linarith
  have hsy : SmallParameter F.blockSide y := hsz y hy0 hyy₀
  have hCs : C * s ≤ y := by
    rw [hyd]
    nlinarith
  have hCs0 : 0 ≤ C * s := by positivity
  have hsub : ∀ z k, innerBonds (cellBall S z 1) k ⊆ innerBonds S k := fun z k =>
    BlockLines.innerBonds_mono (BlockLines.cellBall_subset S z 1) k
  have hnearAll : ∀ z, ContoursNearUnit R (cellBall S z 1) C s := by
    intro z j hj c' hc' h' hh π
    rw [norm_ofUnit_sub_one]
    exact b5 j (by omega) c' (hsub z _ hc') h' hh π
  have hmisAll : ∀ z m', m' + 1 < F.top → ∀ c' ∈ innerBonds (cellBall S z 1) (m' + 1),
      ‖ofUnit (referenceDefect R m' c') - 1‖ ≤ contourSpread F C s m' := by
    intro z m' hm' c' hc'
    rw [norm_ofUnit_sub_one]
    refine (b3 m' hm' c' (hsub z _ hc')).trans ?_
    unfold contourSpread levelScale
    have hl1 : (1 / (F.blockSide : ℝ)) ^ (F.top - (m' + 1)) ≤ 1 := pow_le_one₀ (by positivity) (by
      rw [div_le_one (by positivity)]
      exact hL1)
    have hl0 : 0 ≤ (1 / (F.blockSide : ℝ)) ^ (F.top - (m' + 1)) := by positivity
    have : ((1 / (F.blockSide : ℝ)) ^ (F.top - (m' + 1))) ^ 3 ≤ ((1 / (F.blockSide : ℝ)) ^ (F.top - (m' + 1))) ^ 2 :=
      pow_le_pow_of_le_one hl0 hl1 (by norm_num)
    exact mul_le_mul_of_nonneg_left this hCs0
  have hlevAll : ∀ (z : F.Cell) (W : ComplexChainChart F),
      Real.sqrt (Real.sqrt (∑ b ∈ innerBonds (cellBall S z 1) 0, ‖levelDeviation R W 0 b.1 b.2‖ ^ 4)) ≤ 2 * y →
      (∀ j, j + 1 < F.top →
        Real.sqrt (∑ c ∈ innerBonds (cellBall S z 1) (j + 1), ‖levelSource W j c.1 c.2 - 1‖ ^ 2) ≤ 2 * y) →
      ∀ j, j < F.top →
        Real.sqrt (Real.sqrt (∑ b ∈ innerBonds (cellBall S z 1) j, ‖levelDeviation R W j b.1 b.2‖ ^ 4)) ≤
          4 * (2 * y) :=
    fun z W h0 hm' => hlev F (cellBall S z 1) R W s (2 * y) rfl (BlockLines.card_cellBall_one_le S z)
      (hnearAll z) hs.le (hsc.trans c_c₁) (by positivity) h2y h0 hm'
  have hQ : topDeviationBound F.blockSide y (C * s) ≤ Kf * Eq * (s + u) ^ 2 := by
    have h1 : C * s * y ≤ C * E * (s + u) ^ 2 := by
      rw [hyd]
      have : s ≤ s + u := by linarith
      have h3 : C * s * (E * (s + u)) = (C * E) * (s * (s + u)) := by ring
      have h4 : C * E * (s + u) ^ 2 = (C * E) * ((s + u) * (s + u)) := by ring
      rw [h3, h4]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hsu.le) (by positivity)
    have h2' : y ^ 2 = E ^ 2 * (s + u) ^ 2 := by
      rw [hyd]
      ring
    have h5 : y ^ 2 + C * s * y ≤ Eq * (s + u) ^ 2 := by
      have e5 : Eq * (s + u) ^ 2 = E ^ 2 * (s + u) ^ 2 + C * E * (s + u) ^ 2 := by
        rw [hEq]
        ring
      rw [h2', e5]
      linarith
    calc _ ≤ Kf * (y ^ 2 + C * s * y) := topDeviationBound_le F.blockSide hy0.le hCs0
      _ ≤ Kf * (Eq * (s + u) ^ 2) := mul_le_mul_of_nonneg_left h5 hKf0.le
      _ = _ := by ring
  have hcell : ∀ b ∈ innerBonds S F.top, b.1 ∈ S ∧ b ∈ innerBonds (cellBall S b.1 1) F.top := by
    intro b hb
    have h1 := BlockLines.enclosingCell_mem hoddF (ChartCoordinates.innerBonds_ends hb).1
    rw [enclosingCell_top] at h1
    refine ⟨h1, BlockLines.mem_innerBonds_cellBall_of_mem_bondsOver hamb hoddF S b.1 le_rfl ?_⟩
    refine Finset.mem_filter.2 ⟨hb, ?_⟩
    rw [enclosingCell_top]
    exact Finset.mem_singleton_self _
  have hRn : R (F.depth + 1) = V := by
    rw [hRd]
    unfold referenceFieldChain
    exact Function.update_self _ _ _
  have hwv : ∀ b ∈ innerBonds S F.top,
      ‖((polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b) * (V b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ C * s := by
    intro b hb
    have h1 := b4 b hb
    have e1 : referenceDefect R F.depth b = V b.1 b.2 * (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b))⁻¹ := by
      unfold referenceDefect
      rw [hRn]
    have e2 : polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b) * (V b.1 b.2)⁻¹ = (referenceDefect R F.depth b)⁻¹ := by
      rw [e1, mul_inv_rev, inv_inv]
    rw [e2, norm_coe_inv_sub_one]
    exact h1
  have hcoe : ∀ (w g : UnitQuaternion), ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((w * g : UnitQuaternion) : ℍ[ℝ]) =
      (g : ℍ[ℝ]) := by
    intro w g
    rw [← Submonoid.coe_mul, inv_mul_cancel_left]
  have hnorm' : ∀ z ∈ S, localNorm S R U (constOneWeights F) z ≤ 2 * u := hnorm
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨hzS, hbz⟩ := hcell b hb
    have hz : spanLocalNorm S R U ![U] ![(0 : ℂ)] b.1 ≤ y := by
      have e : spanLocalNorm S R U ![U] ![(0 : ℂ)] b.1 = localNorm S R U (constOneWeights F) b.1 := by
        simp [spanLocalNorm]
      rw [e]
      have := hnorm' b.1 hzS
      rw [hyd]
      nlinarith
    obtain ⟨hv, -⟩ := topDeviation_bound_and_differentiableAt hoddF h2 hC.le hs.le (hnearAll b.1) (hmisAll b.1)
      (hlevAll b.1) hsy hCs hz hbz
    have e0 := topDeviation_ofReal R U U b 0
    rw [Complex.ofReal_zero] at e0
    rw [e0, norm_ofQuat, chartShift_zero, zero_smul, sub_zero] at hv
    set w := polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b) with hw
    set r₀ := ‖_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b‖ with hr₀
    set M := gaugedBondAverage R U F.depth b with hMd
    set X := M * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hX
    set l := linearPart R U F.top b.1 b.2 with hl
    have hr1 : |r₀ - 1| ≤ C * s := by
      refine abs_norm_contourAverage_sub_one_le hoddF fun h hh π => ?_
      exact (hnearAll b.1 F.depth le_rfl b hbz h hh π).trans (contourSpread_le hoddF hC.le hs.le F.depth)
    have hlU : ‖l‖ ≤ Ct * (2 * u) := by
      have h1 := htop' F S R hoddF (by omega) hamb U b hb
      rw [enclosingCell_top] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (hnorm' b.1 hzS) hCt.le)
    have hX1 : ‖X - 1‖ ≤ Kf * Eq * (s + u) ^ 2 + C * s + Ct * (2 * u) := by
      have e : X - 1 = (X - r₀ • (1 : ℍ[ℝ]) - l) + ((r₀ - 1) • (1 : ℍ[ℝ])) + l := by
        rw [sub_smul, one_smul]
        abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have h1 := norm_add_le (X - r₀ • (1 : ℍ[ℝ]) - l) ((r₀ - 1) • (1 : ℍ[ℝ]))
      have h3 : ‖(r₀ - 1) • (1 : ℍ[ℝ])‖ ≤ C * s := by
        rw [norm_smul, norm_one, mul_one, Real.norm_eq_abs]
        exact hr1
      have h4 := hv.trans hQ
      linarith
    have e : M * (((V b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 =
        (X - 1) * ((w * (V b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
          (((w * (V b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) := by
      rw [sub_mul, one_mul, hX, mul_assoc, hcoe]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, mul_one]
    have h5 := hwv b hb
    rw [← hw] at h5
    have h6 : (s + u) ^ 2 ≤ 2 * (s + u) := by nlinarith
    have h7 : Kf * Eq * (s + u) ^ 2 ≤ Kf * Eq * (2 * (s + u)) :=
      mul_le_mul_of_nonneg_left h6 (by positivity)
    have h8 : (Cval + 2 * Cv) * (s + u) = 2 * (Kf * Eq) * (s + u) + 2 * C * (s + u) + 2 * Ct * (s + u) +
        2 * Cv * (s + u) := by
      rw [hCval]
      ring
    have h9 : 0 ≤ 2 * Cv * (s + u) := by positivity
    have h10 : 2 * C * s ≤ 2 * C * (s + u) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h11 : Ct * (2 * u) ≤ 2 * Ct * (s + u) := by nlinarith
    rw [h8]
    linarith
  · intro A
    have hbond : ∀ b ∈ innerBonds S F.top,
        ‖deriv (fun τ : ℝ => gaugedBondAverage R (chartMove U A τ) F.depth b) 0 *
            (((V b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - linearPart R A F.top b.1 b.2‖ ≤
          Cv * (s + u) * localNorm S R A (constOneWeights F) b.1 := by
      intro b hb
      obtain ⟨hzS, hbz⟩ := hcell b hb
      have hα0 : 0 ≤ localNorm S R A (constOneWeights F) b.1 := Real.sqrt_nonneg _
      set α := localNorm S R A (constOneWeights F) b.1 with hα
      set p : ℝ → ℍ[ℝ] := fun τ => gaugedBondAverage R (chartMove U A τ) F.depth b with hp
      have hpd : HasDerivAt p (deriv p 0) 0 := by
        have hr0 : ChartIsRegular S R (chartMove U A 0) := by
          rw [chartShift_zero]
          exact hregU
        have hf := ChartCoordinates.chartField_differentiableOn (S := S) (p₀ := (0 : ℝ))
          (C := fun τ : ℝ => chartMove U A τ) hoddF R
          (fun b' _ => ((differentiableAt_const _).add (differentiableAt_id.smul_const _)))
          (fun j' _ b' _ => ((differentiableAt_const _).add (differentiableAt_id.smul_const _)))
          hr0
        have hjn : F.depth < F.top := Nat.lt_succ_self _
        have := ChartCoordinates.differentiableAt_gaugedContourAverage hoddF hjn (R F.depth) (hf F.depth hjn) hb
          ((hr0 F.depth hjn).1 _ (ChartCoordinates.innerBonds_ends hb).1)
          ((hr0 F.depth hjn).1 _ (ChartCoordinates.innerBonds_ends hb).2)
        exact this.hasDerivAt
      set w := polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b) with hw
      set wi : ℍ[ℝ] := ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hwi
      set lA := linearPart R A F.top b.1 b.2 with hlA
      set T := Kf * Eq * (s + u) with hT
      have hT0 : 0 ≤ T := by positivity
      have hbe : ∀ ε : ℝ, 0 < ε → ‖deriv p 0 * wi - lA‖ ≤ T * (α + ε) := by
        intro ε hε
        have hα' : 0 < α + ε := by positivity
        set ρ := (s + u) / (α + ε) with hρd
        have hρ : 0 < ρ := by positivity
        have hρα : ρ * α ≤ s + u := by
          have : ρ * (α + ε) = s + u := by
            rw [hρd]
            field_simp
          nlinarith
        have hin : ∀ ζ : ℂ, ‖ζ‖ < 3 * ρ → ‖topDeviation R U A b ζ‖ ≤ Kf * Eq * (s + u) ^ 2 ∧
            DifferentiableAt ℂ (topDeviation R U A b) ζ := by
          intro ζ hζ
          have hz : spanLocalNorm S R U ![A] ![ζ] b.1 ≤ y := by
            have e : spanLocalNorm S R U ![A] ![ζ] b.1 = localNorm S R U (constOneWeights F) b.1 + ‖ζ‖ * α := by
              simp [spanLocalNorm, hα]
            rw [e]
            have h1 := hnorm' b.1 hzS
            have h3 : ‖ζ‖ * α ≤ 3 * ρ * α := mul_le_mul_of_nonneg_right hζ.le hα0
            rw [hyd]
            nlinarith
          obtain ⟨hv, hd⟩ := topDeviation_bound_and_differentiableAt hoddF h2 hC.le hs.le (hnearAll b.1)
            (hmisAll b.1) (hlevAll b.1) hsy hCs hz hbz
          exact ⟨hv.trans hQ, hd⟩
        have hMρ : Kf * Eq * (s + u) ^ 2 / ρ = T * (α + ε) := by
          rw [hρd, hT]
          field_simp
        rw [← hMρ]
        refine norm_deriv_mul_sub_le hpd wi lA hρ fun τ hτ => ?_
        have hlip := norm_sub_le_of_bound_on_lines (N := fun x : ℂ => ‖x‖) (fun a b => norm_add_le a b)
          (fun z a => norm_smul z a)
          (G := topDeviation R U A b) (ε := 3 * ρ) (M := Kf * Eq * (s + u) ^ 2) (by positivity) 0 (τ : ℂ)
          (fun z hz => by
            have h1 := (hin (0 + z • (τ : ℂ)) hz).2
            have h3 : DifferentiableAt ℂ (fun w : ℂ => 0 + w • (τ : ℂ)) z := by
              fun_prop
            exact h1.comp z h3)
          (fun z hz => (hin _ hz).1) ρ hρ
          (fun x h0 h1 => by
            have : ‖(0 : ℂ) + (x : ℂ) • (τ : ℂ)‖ ≤ |τ| := by
              rw [zero_add, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg h0]
              nlinarith [abs_nonneg τ]
            show ‖(0 : ℂ) + (x : ℂ) • (τ : ℂ)‖ + ρ < 3 * ρ
            linarith)
        rw [zero_add, Complex.norm_real, Real.norm_eq_abs] at hlip
        have e1 := topDeviation_ofReal R U A b τ
        have e2 := topDeviation_ofReal R U A b 0
        rw [Complex.ofReal_zero] at e2
        rw [e1, e2, ← ofQuat_sub, norm_ofQuat] at hlip
        have e3 : (p τ - p 0) * wi - τ • lA =
            (gaugedBondAverage R (chartMove U A τ) F.depth b *
                (((polarUnit (contourAverage (R F.depth) b))⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
                (‖contourAverage (R F.depth) b‖ : ℝ) • (1 : ℍ[ℝ]) - linearPart R U F.top b.1 b.2 -
                τ • linearPart R A F.top b.1 b.2) -
              (gaugedBondAverage R (chartMove U A 0) F.depth b *
                (((polarUnit (contourAverage (R F.depth) b))⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
                (‖contourAverage (R F.depth) b‖ : ℝ) • (1 : ℍ[ℝ]) - linearPart R U F.top b.1 b.2 -
                (0 : ℝ) • linearPart R A F.top b.1 b.2) := by
          simp only [hp, sub_mul, zero_smul]
          abel
        rw [e3]
        exact hlip
      have he : ‖deriv p 0 * wi - lA‖ ≤ T * α := by
        refine le_of_forall_pos_le_add fun δ hδ => ?_
        have h1 := hbe (δ / (T + 1)) (by positivity)
        refine h1.trans ?_
        have h3 : T * (δ / (T + 1)) ≤ δ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
        nlinarith
      have hlA : ‖lA‖ ≤ Ct * α := htop' F S R hoddF (by omega) hamb A b hb |>.trans (by
        rw [enclosingCell_top]
        exact le_rfl)
      have hwb := hwv b hb
      rw [← hw] at hwb
      have e : deriv p 0 * (((V b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - lA =
          (deriv p 0 * wi - lA) * ((w * (V b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
            lA * (((w * (V b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) := by
        rw [sub_mul, mul_assoc, hwi, hcoe, mul_sub, mul_one]
        abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, mul_one, norm_mul]
      have h1 : ‖lA‖ * ‖((w * (V b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Ct * α * (C * s) :=
        mul_le_mul hlA hwb (norm_nonneg _) (by positivity)
      have h3 : Ct * α * (C * s) ≤ Ct * C * (s + u) * α := by
        have : 0 ≤ Ct * C * α * u := by positivity
        nlinarith
      have h4 : Cv * (s + u) * α = T * α + Ct * C * (s + u) * α := by
        rw [hCv, hT]
        ring
      rw [h4]
      linarith
    have hsq : ∀ b ∈ innerBonds S F.top,
        ‖deriv (fun τ : ℝ => gaugedBondAverage R (chartMove U A τ) F.depth b) 0 *
            (((V b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - linearPart R A F.top b.1 b.2‖ ^ 2 ≤
          (Cv * (s + u)) ^ 2 * localNorm S R A (constOneWeights F) b.1 ^ 2 := by
      intro b hb
      have := pow_le_pow_left₀ (norm_nonneg _) (hbond b hb) 2
      rwa [mul_pow] at this
    refine (Finset.sum_le_sum hsq).trans ?_
    rw [← Finset.mul_sum]
    have hgroup := sum_innerBonds_top_le hoddF S (fun z => localNorm S R A (constOneWeights F) z ^ 2)
      fun _ => by positivity
    have hN : weightedNorm S R A (oneSiteWeights F) ^ 2 = ∑ z ∈ S, localNorm S R A (constOneWeights F) z ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
    rw [hN]
    set Sg := ∑ z ∈ S, localNorm S R A (constOneWeights F) z ^ 2 with hSg
    have hSg0 : 0 ≤ Sg := Finset.sum_nonneg fun _ _ => by positivity
    have h1 : (Cv * (s + u)) ^ 2 * ∑ b ∈ innerBonds S F.top, localNorm S R A (constOneWeights F) b.1 ^ 2 ≤
        (Cv * (s + u)) ^ 2 * (4 * Sg) := mul_le_mul_of_nonneg_left hgroup (by positivity)
    refine h1.trans ?_
    have h3 : (2 * Cv * (s + u)) ^ 2 ≤ ((Cval + 2 * Cv) * (s + u)) ^ 2 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      exact mul_le_mul_of_nonneg_right (by linarith) hsu.le
    have h4 : (Cv * (s + u)) ^ 2 * (4 * Sg) = (2 * Cv * (s + u)) ^ 2 * Sg := by ring
    rw [h4]
    exact mul_le_mul_of_nonneg_right h3 hSg0
end YangMills.Construction.TopMeanVelocity
end

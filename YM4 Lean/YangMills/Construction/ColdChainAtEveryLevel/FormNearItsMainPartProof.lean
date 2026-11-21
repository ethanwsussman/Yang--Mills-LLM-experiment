import YangMills.Construction.ColdChainAtEveryLevel.CellNormsOfTheClassWeights
import YangMills.Construction.ColdChainAtEveryLevel.FormNearItsMainPart
import YangMills.Construction.ColdChainAtEveryLevel.SecondDifferenceOfTheTotal
import YangMills.Construction.ColdChainAtEveryLevel.SecondDifferenceTendsToTheForm
import YangMills.Construction.ColdChainAtEveryLevel.TotalUnderATurnedTopProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction
namespace SecondDifferences
open BlockAverages SmallMultiples LowerLevelTerms BlockLines CellSums BondSecondDifference RealDirections
  LevelRecursion ComplexDifferences FiniteDifferences Filter Topology
variable {F : BlockFrame}
theorem referenceNear_of_bounds (hL1 : (1 : ℝ) ≤ F.blockSide) {S D : Finset F.Cell} (hDS : D ⊆ S)
    {V : F.GaugeField F.top} {C s : ℝ}
    (hC : 0 < C) (hs : 0 < s) (hs1 : s ≤ 1)
    (hdef : ∀ j, j + 1 < F.top → ∀ c' ∈ innerBonds S (j + 1),
      unitDeviation (referenceDefect (referenceFieldChain S V) j c') ≤ C * s * levelScale F (j + 1) ^ 3)
    (hdefTop : ∀ c' ∈ innerBonds S F.top,
      unitDeviation (referenceDefect (referenceFieldChain S V) F.depth c') ≤ C * s)
    (hcont : ∀ j, j < F.top → ∀ c' ∈ innerBonds S (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      unitDeviation (pathHolonomy (referenceFieldChain S V j) (refineSite c'.1) (bondContour F.blockSide h π c'.2) *
          (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (referenceFieldChain S V j) c'))⁻¹) ≤ C * s * levelScale F (j + 1) ^ 2)
    (hlen : ∀ j, j < F.top → ∀ c' ∈ innerBonds S (j + 1),
      0 ≤ 1 - ‖_root_.YangMills.Construction.BlockAverages.contourAverage (referenceFieldChain S V j) c'‖ ∧
        1 - ‖_root_.YangMills.Construction.BlockAverages.contourAverage (referenceFieldChain S V j) c'‖ ≤ C * s ^ 2 * levelScale F (j + 1) ^ 4) :
    ReferenceNear D (referenceFieldChain S V) C s where
  contours := fun j hj c hc h hh π => by
    rw [norm_ofUnit_sub_one]
    exact hcont j (by omega) c (innerBonds_mono hDS _ hc) h hh π
  defect := fun m hm c hc => hdef m hm c (innerBonds_mono hDS _ hc)
  defect_top := fun c hc => hdefTop c (innerBonds_mono hDS _ hc)
  length := fun m hm c hc => by
    obtain ⟨h0, h1⟩ := hlen m hm c (innerBonds_mono hDS _ hc)
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
theorem linearizedCurl_scaledChart (R : F.GaugeField 0) (U : ChainChart F) (ε : ℝ)
    (q : F.Site 0 × Fin 4 × Fin 4) :
    linearizedCurl R (scaledChart U ε).fine q = ε • linearizedCurl R U.fine q := by
  have hs : ∀ (g : UnitQuaternion) (a : ℍ[ℝ]), _root_.YangMills.Construction.BlockAverages.adjointAction g (ε • a) = ε • _root_.YangMills.Construction.BlockAverages.adjointAction g a := by
    intro g a
    simp [_root_.YangMills.Construction.BlockAverages.adjointAction]
  have hc : ∀ x i, (((scaledChart U ε).fine x i : imaginaryQuaternions) : ℍ[ℝ]) =
      ε • ((U.fine x i : imaginaryQuaternions) : ℍ[ℝ]) := by
    intro x i
    rw [scaledChart_fine]
    rfl
  simp only [linearizedCurl, hc, hs, smul_sub, smul_add]
theorem inner_smul_smul_eq (ε : ℝ) (v w : ℍ[ℝ]) : inner ℝ (ε • v) (ε • w) = ε ^ 2 * inner ℝ v w := by
  rw [real_inner_smul_left, real_inner_smul_right]
  ring
theorem plaquettesOver_self (hodd : Odd F.blockSide) (S : Finset F.Cell) :
    plaquettesOver S S 0 = innerPlaquettes S 0 := by
  classical
  refine Finset.filter_true_of_mem fun q hq => ?_
  exact enclosingCell_mem hodd (Finset.mem_product.1 (Finset.mem_filter.1 hq).1).1
theorem bondsOver_self (hodd : Odd F.blockSide) (S : Finset F.Cell) (j : ℕ) :
    bondsOver S S j = innerBonds S j := by apply _root_.YangMills.SharedProofs.p14425 <;> assumption
theorem principalHessian_scaledChart (hodd : Odd F.blockSide) (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain)
    (U A : ChainChart F) (ε : ℝ) :
    ∑ q ∈ innerPlaquettes S 0, inner ℝ (linearizedCurl (R 0) (scaledChart U ε).fine q)
        (linearizedCurl (R 0) (scaledChart A ε).fine q) +
      a * ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
        inner ℝ ((scaledChart U ε).coarse j c.1 c.2 : ℍ[ℝ]) ((scaledChart A ε).coarse j c.1 c.2 : ℍ[ℝ]) +
      a * ∑ c ∈ innerBonds S (F.depth + 1), inner ℝ (linearPart R (scaledChart U ε) (F.depth + 1) c.1 c.2)
        (linearPart R (scaledChart A ε) (F.depth + 1) c.1 c.2) =
    ε ^ 2 * principalHessian a S R U A := by
  have hmu : ∀ (X : ChainChart F) (j : ℕ) (y : F.Site (j + 1)) (i : Fin 4),
      (((scaledChart X ε).coarse j y i : imaginaryQuaternions) : ℍ[ℝ]) =
        ε • ((X.coarse j y i : imaginaryQuaternions) : ℍ[ℝ]) := by
    intro X j y i
    rw [scaledChart_coarse]
    rfl
  have en : F.top - 1 = F.depth := rfl
  simp only [linearizedCurl_scaledChart, hmu, linearPart_scaledChart, inner_smul_smul_eq]
  simp only [principalHessian, plaquettesOver_self hodd, bondsOver_self hodd, en]
  simp only [← Finset.mul_sum, mul_add]
  ring_nf
theorem abs_sub_principalHessian_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) {a : ℝ} (ha : 0 ≤ a) {S : Finset F.Cell}
    {p : F.Site 0} {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {V : F.GaugeField F.top} (hV : R F.top = V)
    {U A : ChainChart F} {C₀ s c Bf : ℝ} {Bu Ba : F.Cell → ℝ} (hC : 0 < C₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (hx : C₀ * s ≤ smallnessThreshold F.blockSide) (ref : ∀ z ∈ S, ReferenceNear (cellBall S z 1) R C₀ s)
    (hcurv : ∀ z ∈ S, ∀ q ∈ innerPlaquettes (cellBall S z 1) 0,
      plaquetteDefect (R 0) q ≤ C₀ * s * ((1 / (F.blockSide : ℝ)) ^ F.top) ^ 2)
    (hc : 0 < c)
    (hcb : ∀ z ∈ S, ∀ (W : ChainChart F) (B : ℝ), 0 ≤ B → B ≤ c →
      finsetLpNorm 4 (innerBonds (cellBall S z 1) 0) (fun b => ‖(W.fine b.1 b.2 : ℍ[ℝ])‖) ≤ B →
      (∀ j, j + 1 < F.top →
        finsetLpNorm 2 (innerBonds (cellBall S z 1) (j + 1)) (fun b => ‖(W.coarse j b.1 b.2 : ℍ[ℝ])‖) ≤ B) →
      DeviationBall R (cellBall S z 1) (realChart W) (4 * B) (4 * B))
    (nm : ∀ z ∈ S, PairWeightedNorms (cellBall S z 1) p θ U A (Bu z) (Ba z)) (hBu : ∀ z, 0 ≤ Bu z)
    (hBa : ∀ z, 0 ≤ Ba z)
    (tends : Tendsto (fun ε : ℝ => (chartAction a S R (scaledSumChart U A ε) V - chartAction a S R (scaledChart U ε) V -
      chartAction a S R (scaledChart A ε) V + chartAction a S R (zeroChart F) V) / ε ^ 2) (𝓝[>] 0) (𝓝 Bf)) :
    |Bf - principalHessian a S R U A| ≤ C₀ * s * cellSecondDiffConst F.blockSide a * ∑ z ∈ S, Bu z * Ba z := by
  have hex : ∀ z ∈ S, ∃ Y ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      cellSecondDiffError a S R V (scaledChart U ε) (scaledChart A ε) (scaledSumChart U A ε) z ≤
        ε ^ 2 * (C₀ * s * cellSecondDiffConst F.blockSide a * (Bu z * Ba z)) + ε ^ 3 * Y := fun z hz =>
    cellSecondDiffError_scaled_le hamb hodd h2 ha hθ hV hC hs hs1 hx (ref z hz) (hcurv z hz) hc (hcb z hz)
      (nm z hz) (hBu z) (hBa z)
  choose! Y ε₀ h0 hY using hex
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ S,
      cellSecondDiffError a S R V (scaledChart U ε) (scaledChart A ε) (scaledSumChart U A ε) z ≤
        ε ^ 2 * (C₀ * s * cellSecondDiffConst F.blockSide a * (Bu z * Ba z)) + ε ^ 3 * Y z := by
    refine (Filter.eventually_all_finset S).2 fun z hz => ?_
    filter_upwards [Ioo_mem_nhdsGT (h0 z hz)] with ε hε
    exact hY z hz ε hε.1 hε.2
  set E := C₀ * s * cellSecondDiffConst F.blockSide a * ∑ z ∈ S, Bu z * Ba z with hE
  set Ys := ∑ z ∈ S, Y z with hYs
  set M₀ := principalHessian a S R U A with hM₀
  have hle : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |(chartAction a S R (scaledSumChart U A ε) V -
      chartAction a S R (scaledChart U ε) V - chartAction a S R (scaledChart A ε) V +
      chartAction a S R (zeroChart F) V) / ε ^ 2 - M₀| ≤ E + ε * Ys := by
    filter_upwards [hall, self_mem_nhdsWithin] with ε hε hpos
    have hε0 : (0 : ℝ) < ε := hpos
    have key := abs_chartAction_second_diff_sub_inner_le hodd ha S R V (scaledChart U ε) (scaledChart A ε)
      (scaledSumChart U A ε)
    rw [principalHessian_scaledChart hodd] at key
    have hsum : ∑ z ∈ S, cellSecondDiffError a S R V (scaledChart U ε) (scaledChart A ε) (scaledSumChart U A ε) z ≤
        ε ^ 2 * E + ε ^ 3 * Ys := by
      refine (Finset.sum_le_sum hε).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hE, hYs]
    have h3 := key.trans hsum
    set Δ := chartAction a S R (scaledSumChart U A ε) V - chartAction a S R (scaledChart U ε) V -
      chartAction a S R (scaledChart A ε) V + chartAction a S R (zeroChart F) V with hΔ
    have hsq : 0 < ε ^ 2 := by positivity
    have e : Δ / ε ^ 2 - M₀ = (Δ - ε ^ 2 * M₀) / ε ^ 2 := by
      field_simp
    rw [e, abs_div, abs_of_pos hsq, div_le_iff₀ hsq]
    refine h3.trans (le_of_eq ?_)
    ring
  have hf := (tends.sub_const M₀).abs
  have hg : Tendsto (fun ε : ℝ => E + ε * Ys) (𝓝[>] 0) (𝓝 (E + 0 * Ys)) := by
    have hcont : Continuous (fun ε : ℝ => E + ε * Ys) := by fun_prop
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have := le_of_tendsto_of_tendsto hf hg hle
  simpa using this
theorem innerPlaquettes_mono {D S : Finset F.Cell} (h : D ⊆ S) {q : F.Site 0 × Fin 4 × Fin 4}
    (hq : q ∈ innerPlaquettes D 0) : q ∈ innerPlaquettes S 0 := by
  obtain ⟨hp, hμν, hcor⟩ := Finset.mem_filter.1 hq
  obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
  exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨sitesOfCells_mono h 0 h1, h2⟩, hμν, hcor.trans (sitesOfCells_mono h 0)⟩
theorem weightedNorm_zeroChart (S : Finset F.Cell) (R : F.FieldChain) (w : F.SiteWeights) :
    _root_.YangMills.Construction.BlockAverages.weightedNorm S R (zeroChart F) w = 0 := by
  have hc : ∀ q, linearizedCurl (R 0) (zeroChart F).fine q = 0 := by
    intro q
    have e : ∀ x i, (((zeroChart F).fine x i : imaginaryQuaternions) : ℍ[ℝ]) = 0 := fun _ _ => rfl
    simp [linearizedCurl, e, _root_.YangMills.Construction.BlockAverages.adjointAction]
  have hN : ∀ z, localNorm S R (zeroChart F) w z = 0 := by
    intro z
    have e : ∀ x i, (((zeroChart F).fine x i : imaginaryQuaternions) : ℍ[ℝ]) = 0 := fun _ _ => rfl
    have e2 : ∀ j y i, (((zeroChart F).coarse j y i : imaginaryQuaternions) : ℍ[ℝ]) = 0 := fun _ _ _ => rfl
    simp [localNorm, localNormSq, hc, e, e2]
  simp [_root_.YangMills.Construction.BlockAverages.weightedNorm, hN]
theorem supWeightedNorm_zeroChart_le (S : Finset F.Cell) (R : F.FieldChain) (del : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    supWeightedNorm S del R (zeroChart F) ≤ c := by
  refine Real.iSup_le (fun y => ?_) hc
  rw [_root_.YangMills.Construction.SecondDifferences.weightedNorm_zeroChart]
  exact hc
end SecondDifferences
namespace BlockAverages
open SecondDifferences SmallMultiples LowerLevelTerms BlockLines CellSums RealDirections LevelRecursion
  ComplexDifferences Filter Topology
theorem hessianNearPrincipal_holds (hb : referenceBoundsStatement) (hrec : UniformQuarticBoundAcrossLevels)
    (hd : chartActionDerivativeBoundsStatement) : hessianNearPrincipalStatement := by
  intro a θ del ha hθ0 hθ8 hdel hdel8
  obtain ⟨Cb, cb, L1, hCb, hcb0, hB⟩ := hb
  obtain ⟨Ld, hdL⟩ := hd
  refine ⟨max (max 5 L1) Ld, fun L hodd hL => ?_⟩
  have hL5 : 5 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLb : L1 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLd : Ld ≤ L := (le_max_right _ _).trans hL
  obtain ⟨cd, Cd, Ck, hcd, -, -, hD⟩ := hdL L a θ del hodd hLd ha hθ0 hθ8 hdel hdel8
  obtain ⟨cball, hcball0, -, hball⟩ := exists_deviationBall_realChart hrec L hodd hL5 hCb.le
  have hsm0 : 0 < smallnessThreshold L := smallnessThreshold_pos (F := ⟨L, 0, fun _ => 0⟩) hodd
  set c := min (min cb cd) (min (min cball 1) (smallnessThreshold L / Cb)) with hc
  have hc0 : 0 < c := lt_min (lt_min hcb0 hcd) (lt_min (lt_min hcball0 one_pos) (by positivity))
  refine ⟨c, Cb * |cellSecondDiffConst L a| * Real.exp (2 * del) + 1, hc0, by positivity, ?_⟩
  intro F m S hFL hamb hm hreg s V hs0 hsc hcold φ θ' p hθ' hφ U A
  have hodd' : Odd F.blockSide := hFL ▸ hodd
  have h2 : 2 ≤ F.blockSide := by omega
  have hL1' : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd'.pos
  have hscb : s ≤ cb := hsc.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hscd : s ≤ cd := hsc.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hscball : s ≤ cball := hsc.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hs1 : s ≤ 1 := hsc.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hsS : s ≤ smallnessThreshold L / Cb := hsc.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hx : Cb * s ≤ smallnessThreshold F.blockSide := by
    rw [hFL]
    rw [le_div_iff₀ hCb] at hsS
    linarith
  set R := referenceFieldChain S V with hR
  have hV : R F.top = V := by simp [hR, referenceFieldChain]
  obtain ⟨-, b2, b3, b4, b5, b6⟩ := hB F m S hodd' (hFL ▸ hLb) hamb hm hreg s V hs0 hscb hcold
  have hθ'' : |θ'| ≤ 1 / 8 := by
    rcases hθ' with rfl | rfl | rfl
    · rw [abs_of_nonneg hθ0]
      exact hθ8
    · simp
    · rw [abs_neg, abs_of_nonneg hθ0]
      exact hθ8
  set w := classWeight F φ θ' p with hw
  set lam : F.Cell → ℝ := fun z => Real.exp (φ z) * ((F.blockSide : ℝ) ^ F.top) ^ θ' with hlam
  have hlam0 : ∀ z, 0 < lam z := fun z => by
    have : 0 < ((F.blockSide : ℝ) ^ F.top) := by positivity
    have := Real.rpow_pos_of_pos this θ'
    simp only [hlam]
    positivity
  set Bu : F.Cell → ℝ := fun z => Real.exp del * localNorm S R U w z / lam z with hBu
  set Ba : F.Cell → ℝ := fun z => Real.exp del * lam z * localNorm S R A (invertedWeights w) z with hBa
  have hBu0 : ∀ z, 0 ≤ Bu z := fun z => by
    have := hlam0 z
    have h3 : 0 ≤ localNorm S R U w z := Real.sqrt_nonneg _
    simp only [hBu]
    positivity
  have hBa0 : ∀ z, 0 ≤ Ba z := fun z => by
    have := hlam0 z
    have h3 : 0 ≤ localNorm S R A (invertedWeights w) z := Real.sqrt_nonneg _
    simp only [hBa]
    positivity
  have ref : ∀ z ∈ S, ReferenceNear (cellBall S z 1) R Cb s := fun z _ =>
    referenceNear_of_bounds hL1' (cellBall_subset S z 1) hCb hs0 hs1 b3 b4 b5 b6
  have hcurv : ∀ z ∈ S, ∀ q ∈ innerPlaquettes (cellBall S z 1) 0,
      plaquetteDefect (R 0) q ≤ Cb * s * ((1 / (F.blockSide : ℝ)) ^ F.top) ^ 2 := fun z _ q hq =>
    b2 0 (Nat.succ_pos _) q (innerPlaquettes_mono (cellBall_subset S z 1) hq)
  have hcb : ∀ z ∈ S, ∀ (W : ChainChart F) (B : ℝ), 0 ≤ B → B ≤ cball →
      finsetLpNorm 4 (innerBonds (cellBall S z 1) 0) (fun b => ‖(W.fine b.1 b.2 : ℍ[ℝ])‖) ≤ B →
      (∀ j, j + 1 < F.top →
        finsetLpNorm 2 (innerBonds (cellBall S z 1) (j + 1)) (fun b => ‖(W.coarse j b.1 b.2 : ℍ[ℝ])‖) ≤ B) →
      DeviationBall R (cellBall S z 1) (realChart W) (4 * B) (4 * B) := fun z hz W B hB0 hBc h1 h3 =>
    hball F (cellBall S z 1) R W s B hFL (card_cellBall_one_le S z) (ref z hz).contours hs0.le hscball hB0 hBc h1 h3
  have nm : ∀ z ∈ S, PairWeightedNorms (cellBall S z 1) p θ' U A (Bu z) (Ba z) := fun z hz =>
    pairWeightedNorms_of_classWeight hodd' hz hdel.le hφ p R U A
  have han := (hD F m S hFL hamb hm hreg s V hs0 hscd hcold (zeroChart F)
    (supWeightedNorm_zeroChart_le S _ del hcd.le)).1 2 ![U, A]
  have key := abs_sub_principalHessian_le hamb hodd' h2 ha.le hθ'' hV hCb hs0 hs1 hx ref hcurv hcball0 hcb nm
    hBu0 hBa0 (tendsto_chartAction_secondDifference a S R V U A han)
  rw [hFL] at key
  refine key.trans ?_
  have hprod : ∀ z, Bu z * Ba z =
      Real.exp (2 * del) * (localNorm S R U w z * localNorm S R A (invertedWeights w) z) := by
    intro z
    have h3 := (hlam0 z).ne'
    have e : Real.exp (2 * del) = Real.exp del * Real.exp del := by
      rw [← Real.exp_add]
      ring_nf
    simp only [hBu, hBa]
    rw [e]
    field_simp
  simp only [hprod, ← Finset.mul_sum]
  have hcs : ∑ z ∈ S, localNorm S R U w z * localNorm S R A (invertedWeights w) z ≤
      _root_.YangMills.Construction.BlockAverages.weightedNorm S R U w * _root_.YangMills.Construction.BlockAverages.weightedNorm S R A (invertedWeights w) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hN1 : 0 ≤ _root_.YangMills.Construction.BlockAverages.weightedNorm S R U w * _root_.YangMills.Construction.BlockAverages.weightedNorm S R A (invertedWeights w) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsum0 : 0 ≤ ∑ z ∈ S, localNorm S R U w z * localNorm S R A (invertedWeights w) z :=
    Finset.sum_nonneg fun z _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hE0 : 0 < Real.exp (2 * del) := Real.exp_pos _
  have hab : cellSecondDiffConst L a ≤ |cellSecondDiffConst L a| := le_abs_self _
  calc Cb * s * cellSecondDiffConst L a * (Real.exp (2 * del) *
        ∑ z ∈ S, localNorm S R U w z * localNorm S R A (invertedWeights w) z)
      ≤ Cb * s * |cellSecondDiffConst L a| * (Real.exp (2 * del) *
        (_root_.YangMills.Construction.BlockAverages.weightedNorm S R U w * _root_.YangMills.Construction.BlockAverages.weightedNorm S R A (invertedWeights w))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hab (by positivity))
          (mul_le_mul_of_nonneg_left hcs hE0.le) (by positivity) (by positivity)
    _ ≤ (Cb * |cellSecondDiffConst L a| * Real.exp (2 * del) + 1) * s * _root_.YangMills.Construction.BlockAverages.weightedNorm S R U w *
        _root_.YangMills.Construction.BlockAverages.weightedNorm S R A (invertedWeights w) := by
        have h4 : 0 ≤ s * (_root_.YangMills.Construction.BlockAverages.weightedNorm S R U w * _root_.YangMills.Construction.BlockAverages.weightedNorm S R A (invertedWeights w)) := by positivity
        nlinarith
end BlockAverages
end YangMills.Construction
end

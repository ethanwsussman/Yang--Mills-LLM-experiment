import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfASplitCriticalPointProof
import YangMills.Construction.ColdChainAtEveryLevel.LocalBoundsOverATurnedTop
import YangMills.Construction.ColdChainAtEveryLevel.PlaquettesNearAPoint
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace TwistedTop
open YangMills.Construction.BlockLines YangMills.Construction.BlockWeights YangMills.Construction.PlaquetteExpansion
variable {F : BlockFrame}
theorem weightedNorm_congr {S : Finset F.Cell} {R : F.FieldChain} {U U' : ChainChart F} (h : ChartEqOnBonds S U U')
    (w : F.SiteWeights) : weightedNorm S R U w = weightedNorm S R U' w := by apply _root_.YangMills.Construction.BlockAverages.SplitCriticalPointBounds.weightedNorm_congr <;> assumption
theorem add_sq_le_two_mul {x y : ℝ} : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
theorem weightedNorm_chartSum_le (S : Finset F.Cell) (R : F.FieldChain) (A A' : ChainChart F) (w : F.SiteWeights)
    (hw : ∀ (j : ℕ) (x : F.Site j), 0 ≤ w j x) {a a' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (h1 : _root_.YangMills.Construction.BlockAverages.weightedNorm S R A w ≤ a)
    (h2 : weightedNorm S R A' w ≤ a') : weightedNorm S R (chartSum A A') w ≤ 2 * (a + a') := by apply _root_.YangMills.Construction.BlockAverages.SplitCriticalPointBounds.weightedNorm_chartSum_le <;> assumption
theorem decayWeights_nonneg (hL : 0 < F.blockSide) (δ θ : ℝ) (p : F.Site 0) (y0 : F.Cell) (j : ℕ) (x : F.Site j) :
    0 ≤ decayWeights F δ θ p y0 j x := by apply _root_.YangMills.Construction.BlockAverages.SplitCriticalPointBounds.decayWeights_nonneg <;> assumption
theorem localNorm_unitSiteWeights_le (hL : 0 < F.blockSide) {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 ≤ δ) (hδ8 : δ ≤ 1 / 8)
    (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (p : F.Site 0) (z : F.Cell) :
    localNorm S R U (oneSiteWeights F) z ≤ 2 * localNorm S R U (decayWeights F δ θ p z) z := by apply _root_.YangMills.Construction.BlockAverages.SplitCriticalPointBounds.localNorm_unit_le_two_mul <;> assumption
theorem blockMisfit_rotatedField (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (c : F.Site (F.depth + 1) × Fin 4) :
    chartBondMisfit R U (rotatedField v V) F.depth c = expUnit (v c.1 c.2) * chartBondMisfit R U V F.depth c := by
  unfold chartBondMisfit
  have e1 : chartChain R U (rotatedField v V) (F.depth + 1) = rotatedField v V := ChartCoordinates.chartChain_top R U _
  have e2 : chartChain R U V (F.depth + 1) = V := ChartCoordinates.chartChain_top R U _
  have hin : F.depth < F.top := Nat.lt_succ_self _
  rw [e1, e2, ChartCoordinates.chartChain_of_lt R U _ hin, ChartCoordinates.chartChain_of_lt R U _ hin]
  simp only [rotatedField, mul_assoc]
theorem blockMisfit_eq_of_succ_lt_top (R : F.FieldChain) (U : ChainChart F) (W V : F.GaugeField F.top) {j : ℕ}
    (hj : j + 1 < F.top) (c : F.Site (j + 1) × Fin 4) : chartBondMisfit R U W j c = chartBondMisfit R U V j c := by
  unfold chartBondMisfit
  rw [ChartCoordinates.chartChain_of_lt R U W hj, ChartCoordinates.chartChain_of_lt R U W (show j < F.top by omega),
    ChartCoordinates.chartChain_of_lt R U V hj, ChartCoordinates.chartChain_of_lt R U V (show j < F.top by omega)]
theorem localMisfitSum_rotatedField_le (hodd : Odd F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) (S : Finset F.Cell)
    (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
    {s : ℝ} (hs0 : 0 ≤ s) (hv : ∀ y i, ‖v y i‖ ≤ s) (p : F.Site 0) {r : ℝ} (hr1 : 1 ≤ r)
    (hr : r ≤ (F.blockSide : ℝ) ^ F.top) :
    localMisfitSum S R U (rotatedField v V) p r ≤
      2 * localMisfitSum S R U V p r + 5000 * s ^ 2 * (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) := by
  classical
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hNp : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  have hM : ∀ j, 0 ≤ ∑ c ∈ (innerBonds S (j + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r),
      normSubOne (chartBondMisfit R U V j c) ^ 2 := fun j => Finset.sum_nonneg fun _ _ => by positivity
  unfold localMisfitSum
  rw [Finset.sum_filter, Finset.sum_filter]
  change ∑ j ∈ Finset.range (F.depth + 1), _ ≤ 2 * ∑ j ∈ Finset.range (F.depth + 1), _ + _
  rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
  have hbelow : ∑ j ∈ Finset.range F.depth, (if (F.blockSide : ℝ) ^ (j + 1) ≤ r then
      ∑ c ∈ (innerBonds S (j + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r),
        normSubOne (chartBondMisfit R U (rotatedField v V) j c) ^ 2 else 0) ≤
      2 * ∑ j ∈ Finset.range F.depth, (if (F.blockSide : ℝ) ^ (j + 1) ≤ r then
      ∑ c ∈ (innerBonds S (j + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r),
        normSubOne (chartBondMisfit R U V j c) ^ 2 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjt : j + 1 < F.top := by
      have := Finset.mem_range.1 hj
      have e : F.top = F.depth + 1 := rfl
      omega
    split_ifs
    · have e : ∑ c ∈ (innerBonds S (j + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r),
            normSubOne (chartBondMisfit R U (rotatedField v V) j c) ^ 2 =
          ∑ c ∈ (innerBonds S (j + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r),
            normSubOne (chartBondMisfit R U V j c) ^ 2 :=
        Finset.sum_congr rfl fun c _ => by rw [blockMisfit_eq_of_succ_lt_top R U (rotatedField v V) V hjt c]
      rw [e]
      have := hM j
      linarith
    · simp
  have htop : (if (F.blockSide : ℝ) ^ (F.depth + 1) ≤ r then
      ∑ c ∈ (innerBonds S (F.depth + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r),
        normSubOne (chartBondMisfit R U (rotatedField v V) F.depth c) ^ 2 else 0) ≤
      2 * (if (F.blockSide : ℝ) ^ (F.depth + 1) ≤ r then
      ∑ c ∈ (innerBonds S (F.depth + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r),
        normSubOne (chartBondMisfit R U V F.depth c) ^ 2 else 0) +
      5000 * s ^ 2 * (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) := by
    split_ifs with hc
    · have hrN : r = (F.blockSide : ℝ) ^ F.top := le_antisymm hr hc
      have hy1 : (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) = 1 := by
        rw [hrN, div_self hNp.ne', Real.one_rpow]
      rw [hy1, mul_one]
      have h1 : ∀ c ∈ (innerBonds S (F.depth + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r),
          normSubOne (chartBondMisfit R U (rotatedField v V) F.depth c) ^ 2 ≤
            2 * normSubOne (chartBondMisfit R U V F.depth c) ^ 2 + 2 * s ^ 2 := by
        intro c _
        have e1 : normSubOne (chartBondMisfit R U (rotatedField v V) F.depth c) ≤
            s + normSubOne (chartBondMisfit R U V F.depth c) := by
          rw [blockMisfit_rotatedField]
          exact (norm_coe_mul_sub_one_le _ _).trans
            (add_le_add ((norm_exp_sub_one_le (v c.1 c.2).2).trans (hv _ _)) le_rfl)
        have e2 : normSubOne (chartBondMisfit R U (rotatedField v V) F.depth c) ^ 2 ≤
            (s + normSubOne (chartBondMisfit R U V F.depth c)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) e1 2
        have e3 := add_sq_le_two_mul (x := s) (y := normSubOne (chartBondMisfit R U V F.depth c))
        linarith
      refine (Finset.sum_le_sum h1).trans ?_
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      have hcard : ((innerBonds S (F.depth + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r)).card ≤ 2500 := by
        have h2 : ((innerBonds S (F.depth + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r)) ⊆
            sitesOfCells (cellsNearPoint S p) F.top ×ˢ (Finset.univ : Finset (Fin 4)) := by
          intro c hc'
          obtain ⟨h3, h4⟩ := Finset.mem_filter.1 hc'
          have h5 : c.1 ∈ sitesOfCells S F.top := (ChartCoordinates.innerBonds_ends h3).1
          have h6 : (2 : ℝ) * (baseDistance c.1 p : ℝ) ≤ 3 * (F.blockSide : ℝ) ^ F.top := by linarith
          have h7 : 2 * baseDistance c.1 p ≤ 3 * F.blockSide ^ F.top := by exact_mod_cast h6
          refine Finset.mem_product.2 ⟨mem_sitesOfCells_of_enclosingCell_mem hodd h5 ?_, Finset.mem_univ _⟩
          exact Finset.mem_filter.2 ⟨enclosingCell_mem hodd h5, cellSupDist_enclosingCell_le_two hodd le_rfl h5 p h7⟩
        refine (Finset.card_le_card h2).trans ?_
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        have h8 := card_sitesOfCells_le hodd (cellsNearPoint S p) F.top
        simp only [Nat.sub_self, pow_zero, one_pow, mul_one] at h8
        have h9 := card_cellsNearPoint_le S p
        omega
      have hcr : (((innerBonds S (F.depth + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r)).card : ℝ) ≤ 2500 := by
        exact_mod_cast hcard
      have h0 : 0 ≤ 2 * s ^ 2 := by positivity
      nlinarith
    · have : 0 ≤ (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) := Real.rpow_nonneg (by positivity) _
      have h3 : 0 ≤ 5000 * s ^ 2 * (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) := by positivity
      simpa using h3
  linarith
end TwistedTop
open TwistedTop YangMills.Construction.BlockLines YangMills.Construction.BlockWeights YangMills.Construction.PlaquetteExpansion
set_option maxHeartbeats 1000000 in
theorem twistedTopLocalBoundsStatement_holds (hLoc : smallChartLocalBoundsStatement)
    (hMis : misfitDecayDownLevelsStatement) (hLast : topMisfitNearCellStatement) :
    twistedTopLocalBoundsStatement := by
  obtain ⟨Cl, hCl, Ll, hLast⟩ := hLast
  intro a θ δ Ca ha hθ hθ8 hδ hδ8 hCa
  obtain ⟨Lo, hLoc⟩ := hLoc θ δ hθ hθ8 hδ hδ8
  obtain ⟨Lm, hMis⟩ := hMis a ha
  obtain ⟨E, hE2, hEdef⟩ : ∃ E : ℝ, 2 ≤ E ∧ E = 2 * Ca + 2 := ⟨_, by linarith, rfl⟩
  have hE0 : 0 < E := by linarith
  refine ⟨max Lo (max Lm Ll), fun L hL hge r C₁ hr hC₁ => ?_⟩
  have hLo : Lo ≤ L := (le_max_left _ _).trans hge
  have hLm : Lm ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hge)
  have hLl : Ll ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hge)
  obtain ⟨cl, Co, hcl, hCo, hLocL⟩ := hLoc L hL hLo
  obtain ⟨cm, Cm, hcm, hCm, hMisL⟩ := hMis L hL hLm
  obtain ⟨c4, hc4, hLastL⟩ := hLast L hL hLl
  obtain ⟨K1, hK12, hK1⟩ : ∃ K1 : ℝ, 2 ≤ K1 ∧ 1 + 3 * Cl ≤ K1 := ⟨3 + 3 * Cl, by linarith, by linarith⟩
  have hK10 : 0 < K1 := by linarith
  obtain ⟨s₂, hs20, hs22, hs23, hs25, hs26⟩ :
      ∃ s₂ : ℝ, 0 < s₂ ∧ C₁ * s₂ ≤ 1 ∧ E * s₂ ≤ cl ∧ K1 * E * s₂ ≤ cm ∧ 2 * E * s₂ ≤ c4 := by
    have hA2 : 0 < cl / E := by positivity
    have hA4 : 0 < cm / (K1 * E) := by positivity
    have hA5 : 0 < c4 / (2 * E) := by positivity
    set y := min (min (1 / C₁) (cl / E)) (min (cm / (K1 * E)) (c4 / (2 * E))) with hy
    have hy0 : 0 < y := lt_min (lt_min (by positivity) hA2) (lt_min hA4 hA5)
    have y2 : y ≤ 1 / C₁ := (min_le_left _ _).trans (min_le_left _ _)
    have y3 : y ≤ cl / E := (min_le_left _ _).trans (min_le_right _ _)
    have y5 : y ≤ cm / (K1 * E) := (min_le_right _ _).trans (min_le_left _ _)
    have y6 : y ≤ c4 / (2 * E) := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨y, hy0, ?_, ?_, ?_, ?_⟩
    · have := (le_div_iff₀ hC₁).1 y2
      linarith
    · have := (le_div_iff₀ hE0).1 y3
      linarith
    · have := (le_div_iff₀ (by positivity : 0 < K1 * E)).1 y5
      linarith
    · have := (le_div_iff₀ (by positivity : 0 < 2 * E)).1 y6
      linarith
  obtain ⟨C₂, hC₂0, hC₂1, hC₂2, hC₂3⟩ : ∃ C₂ : ℝ, 0 < C₂ ∧ Co * E ≤ C₂ ∧ Cm * (K1 * E) ≤ C₂ ∧
      2 * (Co * E) ^ 2 + 5000 ≤ C₂ ^ 2 := by
    refine ⟨Co * E + Cm * (K1 * E) + 2 * (Co * E) ^ 2 + 5001, by positivity, ?_, ?_, ?_⟩
    · have h1 : 0 ≤ Cm * (K1 * E) := by positivity
      have h2 : 0 ≤ (Co * E) ^ 2 := by positivity
      linarith
    · have h1 : 0 ≤ Co * E := by positivity
      have h2 : 0 ≤ (Co * E) ^ 2 := by positivity
      linarith
    · have h1 : 0 ≤ Co * E := by positivity
      have h2 : 0 ≤ (Co * E) ^ 2 := by positivity
      have h3 : 0 ≤ Cm * (K1 * E) := by positivity
      nlinarith
  refine ⟨s₂, C₂, hs20, hC₂0, ?_⟩
  intro F m S hFL hamb hm hreg s V v hs0 hss hcold hv U hsup hcrit hsplit
  subst hFL
  classical
  have hodd : Odd F.blockSide := hL
  have hLpos : 0 < F.blockSide := hodd.pos
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hLpos
  have hsE : s ≤ E * s := by nlinarith
  have hEs1 : E * s ≤ cl := (mul_le_mul_of_nonneg_left hss hE0.le).trans hs23
  have hEs3 : K1 * E * s ≤ cm := (mul_le_mul_of_nonneg_left hss (by positivity)).trans hs25
  have hEs4 : 2 * E * s ≤ c4 := (mul_le_mul_of_nonneg_left hss (by positivity)).trans hs26
  have hCs : C₁ * s ≤ 1 := (mul_le_mul_of_nonneg_left hss hC₁.le).trans hs22
  obtain ⟨Ulin, Urest, hsame, hsz⟩ := hsplit
  have hN : ∀ (p : F.Site 0) (y0 : F.Cell),
      _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) U (decayWeights F δ θ p y0) ≤ E * s := by
    intro p y0
    rw [_root_.YangMills.Construction.BlockAverages.TwistedTop.weightedNorm_congr hsame]
    obtain ⟨a1, a2⟩ := hsz p y0 θ (Or.inl rfl)
    have h1 := _root_.YangMills.Construction.BlockAverages.TwistedTop.weightedNorm_chartSum_le S (referenceFieldChain S V) Ulin Urest (decayWeights F δ θ p y0)
      (fun j x => decayWeights_nonneg hLpos δ θ p y0 j x) (by positivity) (by positivity) a1 a2
    refine h1.trans ?_
    rw [hEdef]
    have h2 : C₁ * s ^ 2 ≤ s := by nlinarith
    linarith
  have hN0 : ∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤ 2 * (E * s) := by
    intro z hz
    have p0 : F.Site 0 := cellCentre 0 z
    have h1 := localNorm_unitSiteWeights_le hLpos hθ.le hδ.le hδ8 S (referenceFieldChain S V) U p0 z
    have h2 := (localNorm_le_weightedNorm S (referenceFieldChain S V) U _ hz).trans (hN p0 z)
    linarith
  have hTop : ∀ b ∈ innerBonds S F.top,
      normSubOne (chartBondMisfit (referenceFieldChain S V) U (rotatedField v V) F.depth b) ≤ K1 * E * s := by
    intro b hb
    have hz : enclosingCell b.1 ∈ S := enclosingCell_mem hodd (ChartCoordinates.innerBonds_ends hb).1
    have h1 := hLastL F m S rfl hamb hm hreg s V hs0 (by nlinarith) hcold U (enclosingCell b.1) (2 * (E * s)) hz
      (by positivity) (by linarith) (hN0 _ hz) b (Finset.mem_filter.2 ⟨hb, by simp⟩)
    have h0 : normSubOne (chartBondMisfit (referenceFieldChain S V) U (rotatedField v V) F.depth b) ≤
        s + normSubOne (chartBondMisfit (referenceFieldChain S V) U V F.depth b) := by
      rw [blockMisfit_rotatedField]
      exact (norm_coe_mul_sub_one_le _ _).trans
        (add_le_add ((norm_exp_sub_one_le (v b.1 b.2).2).trans (hv _ _)) le_rfl)
    have h2 : Cl * (s + 2 * (E * s)) ≤ Cl * (3 * (E * s)) := mul_le_mul_of_nonneg_left (by linarith) hCl.le
    have h3 : (1 + 3 * Cl) * (E * s) ≤ K1 * (E * s) := mul_le_mul_of_nonneg_right hK1 (by positivity)
    nlinarith
  have hLocAll := hLocL F m S rfl hamb hm hreg s V hs0 (hsE.trans hEs1) hcold U (E * s) hsE hEs1 hN
  have hpow : Co * (E * s) ≤ C₂ * s := by
    have := mul_le_mul_of_nonneg_right hC₂1 hs0.le
    linarith
  have hpow0 : 0 ≤ Co * (E * s) := by positivity
  refine ⟨fun j p r' hj h1 h2 => ?_, fun p r' h1 h2 => ⟨?_, ?_⟩, fun j z hj => ?_⟩
  · refine (hLocAll.1 j p r' hj h1 h2).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hpow0 hpow 4) (Real.rpow_nonneg (by positivity) _)
  · refine (hLocAll.2 p r' h1 h2).1.trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hpow0 hpow 2) (Real.rpow_nonneg (by positivity) _)
  · have h3 := localMisfitSum_rotatedField_le (θ := θ) hodd hθ.le S (referenceFieldChain S V) U V v hs0.le hv p h1 h2
    have h4 := (hLocAll.2 p r' h1 h2).2
    refine h3.trans ?_
    have hy : 0 ≤ (r' / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) := Real.rpow_nonneg (by positivity) _
    have e : (C₂ * s) ^ 2 = C₂ ^ 2 * s ^ 2 := by ring
    have e2 : (Co * (E * s)) ^ 2 = (Co * E) ^ 2 * s ^ 2 := by ring
    rw [e]
    rw [e2] at h4
    have h5 := mul_le_mul_of_nonneg_right hC₂3
      (by positivity : (0 : ℝ) ≤ s ^ 2 * (r' / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ))
    nlinarith
  · have hb : K1 * E * s = K1 * (E * s) := by ring
    have hN1 : ∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤ K1 * E * s := by
      intro z hz
      refine (hN0 z hz).trans ?_
      rw [hb]
      exact mul_le_mul_of_nonneg_right hK12 (by positivity)
    have hsK : s ≤ K1 * E * s := by
      rw [hb]
      nlinarith
    obtain ⟨m1, m2⟩ := hMisL F m S rfl hamb hm hreg s V (rotatedField v V) hs0 (hsK.trans hEs3) hcold U (K1 * E * s)
      hsK hEs3 hN1 hTop hcrit j z hj
    have hcm1 : Cm * (K1 * E * s) ≤ C₂ * s := by
      have := mul_le_mul_of_nonneg_right hC₂2 hs0.le
      rw [hb]
      nlinarith
    refine ⟨m1.trans (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hcm1 (by positivity)) 4),
      m2.trans (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hcm1 (by positivity)) 2)⟩
end YangMills.Construction.BlockAverages
end

import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfTheLeastActionAtAColdTopProof
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdChainAtEveryLevel.AnalyticSharesOfAColdTop
import YangMills.Construction.ColdChainAtEveryLevel.ChainOfAFramedChain
import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.ColdChainAtEveryLevel.CriticalValueIsTheLeastAction
import YangMills.Construction.ColdChainAtEveryLevel.FirstOrderOfTheCriticalChainAtAFlatTopForm
import YangMills.Construction.ColdChainAtEveryLevel.ReferenceOfAFlatTop
import YangMills.Construction.ColdChainAtEveryLevel.SeminormsOfCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction.BlockAverages
namespace CriticalChainFirstOrder
open ChartCoordinates
variable {F : BlockFrame}
def zeroChart (F : BlockFrame) : ChainChart F := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem chartAction_eq_weightedChainTerms (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (W : F.GaugeField F.top) :
    chartAction a S R U W =
      weightedChainTerms a S (fun _ => 1) (fun _ _ => 1) (chartChain R U W) (chartGauge R U) := by
  simp [chartAction, gaugedChainAction, weightedChainTerms, wilsonAction]
theorem rotatedFlatField_zero (v : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    rotatedFlatField v 0 = flatTopField := by
  funext y i
  simp [rotatedFlatField, rotatedField, flatTopField, expUnit_zero]
theorem rotatedFlatField_of_zero (τ : ℝ) :
    rotatedFlatField (fun _ _ => (0 : imaginaryQuaternions) : F.Site F.top → Fin 4 → imaginaryQuaternions) τ =
      flatTopField := by
  funext y i
  simp [rotatedFlatField, rotatedField, flatTopField, expUnit_zero]
theorem pathHolonomy_one {j : ℕ} (l : List PathStep) (x : F.Site j) :
    pathHolonomy (fun _ _ => (1 : UnitQuaternion) : F.GaugeField j) x l = 1 := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.pathHolonomy_one <;> assumption
theorem flatTopField_isCold (S : Finset F.Cell) {s : ℝ} (hs : 0 < s) :
    IsCold S F.top s (flatTopField : F.GaugeField F.top) := by
  intro p _
  have : plaquetteHolonomy (flatTopField : F.GaugeField F.top) p = 1 := pathHolonomy_one _ _
  simp [plaquetteDefect, this, hs]
theorem hasDerivAt_zero_of_tendsto_div_sq {f : ℝ → ℝ} {l : ℝ} (h0 : f 0 = 0)
    (hl : Tendsto (fun τ : ℝ => f τ / τ ^ 2) (𝓝[≠] 0) (𝓝 l)) : HasDerivAt f 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h1 : Tendsto (fun t : ℝ => t * (f t / t ^ 2)) (𝓝[≠] 0) (𝓝 (0 * l)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).mul hl
  rw [zero_mul] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  simp only [zero_add, h0, sub_zero, smul_eq_mul]
  field_simp
theorem iteratedDeriv_two_of_tendsto_div_sq {f : ℝ → ℝ} {l : ℝ} (hf : AnalyticAt ℝ f 0) (h0 : f 0 = 0)
    (hl : Tendsto (fun τ : ℝ => f τ / τ ^ 2) (𝓝[≠] 0) (𝓝 l)) : iteratedDeriv 2 f 0 = 2 * l := by
  have hd := hasDerivAt_zero_of_tendsto_div_sq h0 hl
  have hg : AnalyticAt ℝ (deriv f) 0 := hf.deriv
  have hg0 : deriv f 0 = 0 := hd.deriv
  have hgd : HasDerivAt (deriv f) (deriv (deriv f) 0) 0 := hg.differentiableAt.hasDerivAt
  have h1 : Tendsto (fun x : ℝ => deriv f x / (2 * x)) (𝓝[≠] 0) (𝓝 (deriv (deriv f) 0 / 2)) := by
    have h2 := (hasDerivAt_iff_tendsto_slope_zero.1 hgd).div_const 2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    simp only [zero_add, hg0, sub_zero, smul_eq_mul]
    field_simp
  have hev : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt f (deriv f x) x :=
    hf.eventually_analyticAt.mono fun x hx => hx.differentiableAt.hasDerivAt
  have h3 : Tendsto (fun x : ℝ => f x / x ^ 2) (𝓝[≠] 0) (𝓝 (deriv (deriv f) 0 / 2)) := by
    refine HasDerivAt.lhopital_zero_nhdsNE (f' := deriv f) (g' := fun x => 2 * x)
      (eventually_nhdsWithin_of_eventually_nhds hev)
      (Eventually.of_forall fun x => by simpa using hasDerivAt_pow 2 x) ?_ ?_ ?_ h1
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : t ≠ 0 := ht
      simpa using ht'
    · have := hf.continuousAt.tendsto
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    · have : Tendsto (fun x : ℝ => x ^ 2) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_pow 2).tendsto (0 : ℝ)
      exact this.mono_left nhdsWithin_le_nhds
  have h4 := tendsto_nhds_unique h3 hl
  rw [iteratedDeriv_succ, iteratedDeriv_one, ← h4]
  ring
def quaternionI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
def imaginaryUnitI : imaginaryQuaternions := ⟨quaternionI, rfl⟩
theorem norm_imaginaryUnitI : ‖imaginaryUnitI‖ = 1 := by
  show ‖quaternionI‖ = 1
  have h : ‖quaternionI‖ ^ 2 = 1 := by
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    simp [quaternionI]
  have h0 := norm_nonneg quaternionI
  nlinarith
theorem exists_bondSpread (B : Finset (F.Site F.top × Fin 4)) (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (hB : ∀ b, b ∉ B → v b.1 b.2 = 0) :
    ∃ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (α : Fin k → ℝ),
      1 ≤ k ∧ AreUnitVectors X ∧ (∀ l, 0 ≤ α l) ∧ (∀ y i, ‖v y i‖ ≤ ∑ l, α l) ∧
        ∀ (τ : ℝ) y i, bondSpread c X (τ • α) y i = τ • v y i := by
  classical
  set B' := insert ((0 : F.Site F.top), (0 : Fin 4)) B with hB'
  let e := B'.equivFin
  refine ⟨B'.card, fun l => (e.symm l).1, fun l => if v (e.symm l).1.1 (e.symm l).1.2 = 0 then imaginaryUnitI
      else ‖v (e.symm l).1.1 (e.symm l).1.2‖⁻¹ • v (e.symm l).1.1 (e.symm l).1.2,
    fun l => ‖v (e.symm l).1.1 (e.symm l).1.2‖, Finset.card_pos.2 ⟨_, Finset.mem_insert_self _ _⟩, ?_,
    fun _ => norm_nonneg _, ?_, ?_⟩
  · intro l
    by_cases h : v (e.symm l).1.1 (e.symm l).1.2 = 0
    · simp only [if_pos h]
      exact norm_imaginaryUnitI
    · simp only [if_neg h]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]
  · intro y i
    by_cases hm : (y, i) ∈ B'
    · have := Finset.single_le_sum (f := fun l => ‖v (e.symm l).1.1 (e.symm l).1.2‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ (e ⟨(y, i), hm⟩))
      simpa using this
    · have : (y, i) ∉ B := fun h => hm (Finset.mem_insert_of_mem h)
      have h0 : v y i = 0 := hB (y, i) this
      rw [h0, norm_zero]
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  · intro τ y i
    simp only [bondSpread]
    by_cases hm : (y, i) ∈ B'
    · rw [Finset.sum_eq_single (e ⟨(y, i), hm⟩)]
      · simp only [Equiv.symm_apply_apply, if_true, Pi.smul_apply, smul_eq_mul]
        by_cases h : v y i = 0
        · simp [h]
        · simp only [if_neg h]
          rw [smul_smul, mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), mul_one]
      · intro l _ hl
        rw [if_neg]
        intro hc
        apply hl
        have : e.symm l = ⟨(y, i), hm⟩ := Subtype.ext hc
        rw [← this, Equiv.apply_symm_apply]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have hnot : (y, i) ∉ B := fun h => hm (Finset.mem_insert_of_mem h)
      have h0 : v y i = 0 := hB (y, i) hnot
      rw [h0, smul_zero]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [if_neg]
      intro hc
      exact hm (hc ▸ (e.symm l).2)
theorem chartMove_hasFirstOrderOn (S : Finset F.Cell) (A : ChainChart F) :
    HasFirstOrderOn S (fun τ => chartMove (zeroChart F) A τ) A := by
  have hw : ∀ w : imaginaryQuaternions,
      HasDerivAt (fun τ : ℝ => (((0 : imaginaryQuaternions) + τ • w : imaginaryQuaternions) : ℍ[ℝ])) (w : ℍ[ℝ]) 0 := by
    intro w
    have := (hasDerivAt_id (0 : ℝ)).smul_const (w : ℍ[ℝ])
    simpa using this
  exact ⟨fun b _ => by simp [chartMove, zeroChart], fun j _ c _ => by simp [chartMove, zeroChart],
    fun b _ => hw _, fun j _ c _ => hw _⟩
theorem gaugeMap_zero (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0) (x : F.Site 0) :
    GaugeMap.gaugeMap S V R (fun _ _ => (0 : ℍ[ℝ])) x = 0 := by apply _root_.YangMills.Construction.CoordinateSeminorms.gaugeMap_zero <;> assumption
theorem zeroChart_inGaugeSlice (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0) :
    GaugeMap.InGaugeSlice S V R (zeroChart F).fine := by apply _root_.YangMills.Construction.BlockAverages.ColdTopSecondVariation.inGaugeSlice_zero <;> assumption
theorem supWeightedNorm_zeroChart (S : Finset F.Cell) (del : ℝ) (R : F.FieldChain) :
    supWeightedNorm S del R (zeroChart F) = 0 := by
  have h : ∀ y0, _root_.YangMills.Construction.BlockAverages.weightedNorm S R (zeroChart F) (decayWeights F del 0 0 y0) = 0 := by
    intro y0
    simp [_root_.YangMills.Construction.BlockAverages.weightedNorm, localNorm, localNormSq, linearizedCurl, _root_.YangMills.Construction.BlockAverages.adjointAction, zeroChart]
  simp [supWeightedNorm, h]
theorem allAlong_true (l : List PathStep) (v : LatticeFractionalIntegration.Lattice4) :
    LatticePaths.AllAlong (fun _ => True) v l := by
  induction l generalizing v with
  | nil => trivial
  | cons st r ih => exact ⟨trivial, ih _⟩
theorem eventually_rotatedFlatField_isCold (S : Finset F.Cell) (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
    {s : ℝ} (hs : 0 < s) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), IsCold S F.top s (rotatedFlatField v τ) := by
  have hdiff : GaugeDifferentiableOn (fun τ : ℝ => rotatedFlatField v τ) (0 : ℝ) (Set.univ : Set (F.Site F.top)) := by
    intro x i _ _
    have h1 : DifferentiableAt ℝ (fun τ : ℝ => τ • v x i) 0 :=
      (differentiableAt_id).smul_const _
    exact differentiableAt_unitQuaternion_mul (differentiableAt_expUnit h1) (differentiableAt_const _)
  unfold IsCold
  refine (Filter.eventually_all_finset _).2 fun p _ => ?_
  have hh := differentiableAt_pathHolonomy hdiff p.1
    [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] 0
    (LatticePaths.allAlong_mono (fun _ _ => trivial) (allAlong_true _ _))
  rw [add_siteOfCoords_zero] at hh
  have hc := hh.continuousAt
  have hcont : ContinuousAt (fun τ : ℝ => plaquetteDefect (rotatedFlatField v τ) p) 0 := by
    unfold plaquetteDefect plaquetteHolonomy
    exact (hc.sub continuousAt_const).norm
  have h0 : plaquetteDefect (rotatedFlatField v 0) p = 0 := by
    have : plaquetteHolonomy (rotatedFlatField v 0) p = 1 := by
      rw [rotatedFlatField_zero]
      exact pathHolonomy_one _ _
    simp [plaquetteDefect, this]
  exact (hcont.tendsto.eventually_lt_const (by rw [h0]; exact hs))
theorem exists_minimalChain_of_chart (hG : chainOfGaugedChainStatement) (hFC : gaugedChainLowerBoundStatement)
    {a : ℝ} (ha : 0 < a) (hL : 0 < F.blockSide) (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (W : F.GaugeField F.top)
    (hmin : ∀ (X : F.FieldChain) (k : F.SiteGauge), X F.top = W → chartAction a S R U W ≤ gaugedChainAction a S X k) :
    ∃ X' : F.FieldChain, IsMinimalChain a S W X' ∧ ∀ Y : F.Cell, cellShare a S Y X' =
      weightedChainTerms a S (plaquetteCornerShare Y) (bondEndShare Y) (chartChain R U W) (chartGauge R U) := by
  obtain ⟨X', h1, h2, h3⟩ := hG F hL (chartChain R U W) (chartGauge R U)
  have htop : X' F.top = W := by rw [h1, chartChain_top]
  have htotal : chainAction a S X' = chartAction a S R U W := by
    unfold chainAction chartAction gaugedChainAction wilsonAction
    congr 1
    · exact Finset.sum_congr rfl fun p _ => by rw [h2 p]
    · congr 1
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c _ => ?_
      exact h3 j (Finset.mem_range.1 hj) c
  refine ⟨X', ⟨htop, fun X'' h => ?_⟩, fun Y => ?_⟩
  · rw [htotal, ← (hFC F a S ha.le hL).2 X'']
    exact hmin X'' _ h
  · unfold cellShare weightedChainTerms
    congr 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [h2 p]
      rfl
    · congr 1
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c _ => ?_
      rw [h3 j (Finset.mem_range.1 hj) c]
      rfl
theorem blockFit_congr_top {j : ℕ} (X : F.GaugeField j) (B B' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4)
    (h : B c.1 c.2 = B' c.1 c.2) : blockFit X B c = blockFit X B' c := by
  unfold blockFit
  rw [h]
theorem chainAction_congr (a : ℝ) (S : Finset F.Cell) (X X' : F.FieldChain) (h1 : ∀ j, j < F.top → X j = X' j)
    (h2 : ∀ c ∈ innerBonds S F.top, X F.top c.1 c.2 = X' F.top c.1 c.2) :
    chainAction a S X = chainAction a S X' ∧ ∀ Y, cellShare a S Y X = cellShare a S Y X' := by
  have hfit : ∀ j ∈ Finset.range F.top, ∀ c ∈ innerBonds S (j + 1),
      blockFit (X j) (X (j + 1)) c = blockFit (X' j) (X' (j + 1)) c := by
    intro j hj c hc
    have hjn := Finset.mem_range.1 hj
    rw [h1 j hjn]
    by_cases htop : j + 1 < F.top
    · rw [h1 (j + 1) htop]
    · obtain rfl : j = F.depth := by
        have hn : F.top = F.depth + 1 := rfl
        omega
      exact blockFit_congr_top (X' F.depth) (X (F.depth + 1)) (X' (F.depth + 1)) c (h2 c hc)
  have h0 : X 0 = X' 0 := h1 0 (Nat.succ_pos _)
  constructor
  · unfold chainAction
    rw [h0, Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c hc => hfit j hj c hc]
  · intro Y
    unfold cellShare
    rw [h0, Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c hc => by rw [hfit j hj c hc]]
theorem minimalCellShare_congr (hLV : minimalChainExistenceStatement) {a : ℝ} (ha : 0 < a) (S : Finset F.Cell)
    {W W' : F.GaugeField F.top} (hag : ∀ c ∈ innerBonds S F.top, W c.1 c.2 = W' c.1 c.2)
    (h1 : ∀ X, IsMinimalChain a S W X → ∀ Y, cellShare a S Y X = minimalCellShare a S Y W)
    (h2 : ∀ X, IsMinimalChain a S W' X → ∀ Y, cellShare a S Y X = minimalCellShare a S Y W') (Y : F.Cell) :
    minimalCellShare a S Y W = minimalCellShare a S Y W' := by
  classical
  obtain ⟨X, hX, -⟩ := (hLV F a S ha.le).2.2.2 W
  set X' : F.FieldChain := Function.update X F.top W' with hX'
  have htop' : X' F.top = W' := by simp [hX']
  have hlow : ∀ j, j < F.top → X j = X' j := fun j hj => by
    rw [hX', Function.update_of_ne (by omega)]
  have hc := chainAction_congr a S X X' hlow (fun c hc => by rw [hX.1, htop']; exact hag c hc)
  have hmin : IsMinimalChain a S W' X' := by
    refine ⟨htop', fun Z hZ => ?_⟩
    set Z' : F.FieldChain := Function.update Z F.top W with hZ'
    have htZ : Z' F.top = W := by simp [hZ']
    have hlZ : ∀ j, j < F.top → Z j = Z' j := fun j hj => by
      rw [hZ', Function.update_of_ne (by omega)]
    have hcZ := chainAction_congr a S Z Z' hlZ (fun c hc => by rw [hZ, htZ]; exact (hag c hc).symm)
    rw [← hc.1, hcZ.1]
    exact hX.2 Z' htZ
  rw [← h1 X hX Y, ← h2 X' hmin Y, hc.2 Y]
end CriticalChainFirstOrder
open CriticalChainFirstOrder ChartCoordinates in
theorem criticalChainFirstOrder (hCT : rotatedCriticalChainsStatement)
    (hCV : criticalValueEqMinimalActionStatement) (hAS : analyticCellSharesStatement)
    (hRF : flatTopReferenceStatement) (hSO : secondOrderAtFlatTopStatement)
    (hCC : chainOfGaugedChainStatement) (hFC : gaugedChainLowerBoundStatement)
    (hLV : minimalChainExistenceStatement) : criticalChainFirstOrderStatement := by
  intro a ha
  obtain ⟨θ, del, Ca, hθ0, hθ1, hd0, hd1, hCa, L₁, hCT⟩ := hCT a ha
  obtain ⟨L₂, hCV⟩ := hCV a θ del Ca ha hθ0 hθ1 hd0 hd1 hCa
  obtain ⟨δ₀, hδ₀, hAS⟩ := hAS a ha
  obtain ⟨L₃, hAS⟩ := hAS δ₀ hδ₀ le_rfl
  refine ⟨max L₁ (max L₂ L₃), fun L hodd hL => ?_⟩
  have hL1 : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : L₂ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL3 : L₃ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  obtain ⟨rL, r', sL, CL, Ck, hrL, hr'0, hr'rL, hsL, hCL, hCk, hCT1, -⟩ := hCT L hodd hL1
  obtain ⟨σ₁, hσ₁, hCV⟩ := hCV L hodd hL2 CL hCL
  obtain ⟨σ₂, N, hσ₂, hN, hAS⟩ := hAS L hodd hL3
  intro F m S hFL hamb hm hreg v₀
  classical
  obtain ⟨v, hB, hvag⟩ : ∃ v : F.Site F.top → Fin 4 → imaginaryQuaternions,
      (∀ b, b ∉ innerBonds S F.top → v b.1 b.2 = 0) ∧ ∀ c ∈ innerBonds S F.top, v c.1 c.2 = v₀ c.1 c.2 :=
    ⟨fun y i => if (y, i) ∈ innerBonds S F.top then v₀ y i else 0, fun b hb => if_neg hb, fun c hc => if_pos hc⟩
  have hoddF : Odd F.blockSide := by rw [hFL]; exact hodd
  have hLpos : 0 < F.blockSide := hoddF.pos
  set R := referenceFieldChain S (flatTopField : F.GaugeField F.top) with hRdef
  have hR : ∀ j, j < F.top → ∀ b ∈ innerBonds S j, R j b.1 b.2 = 1 := fun j hj b hb =>
    hRF F S j b.1 b.2 hoddF hamb hj.le (LocalPartition.enclosingCell_mem hoddF (innerBonds_ends hb).1)
      (LocalPartition.enclosingCell_mem hoddF (innerBonds_ends hb).2)
  set s := min sL (σ₁ / 2) with hs
  have hs0 : 0 < s := lt_min hsL (by positivity)
  obtain ⟨U, hU, -, hTall⟩ :=
    hCT1 F m S hFL hamb hm hreg s flatTopField hs0 (min_le_left _ _) (flatTopField_isCold S hs0)
  have hzero : ∀ A : ChainChart F, IsStationaryAlong a S R flatTopField (_root_.YangMills.Construction.BlockAverages.CriticalChainFirstOrder.zeroChart F) A := by
    intro A
    obtain ⟨e0, el⟩ := hSO F S R a (fun _ => 1) (fun _ _ => 1) (fun τ => chartMove (_root_.YangMills.Construction.BlockAverages.CriticalChainFirstOrder.zeroChart F) A τ) A
      (fun _ _ => 0) hoddF hR (chartMove_hasFirstOrderOn S A)
    have hfun : (fun τ : ℝ => chartAction a S R (chartMove (_root_.YangMills.Construction.BlockAverages.CriticalChainFirstOrder.zeroChart F) A τ) flatTopField) = fun τ =>
        weightedChainTerms a S (fun _ => 1) (fun _ _ => 1)
          (chartChain R (chartMove (_root_.YangMills.Construction.BlockAverages.CriticalChainFirstOrder.zeroChart F) A τ) (rotatedFlatField (fun _ _ => 0) τ))
          (chartGauge R (chartMove (_root_.YangMills.Construction.BlockAverages.CriticalChainFirstOrder.zeroChart F) A τ)) := by
      funext τ
      rw [rotatedFlatField_of_zero, chartAction_eq_weightedChainTerms]
    unfold IsStationaryAlong
    rw [hfun]
    exact hasDerivAt_zero_of_tendsto_div_sq e0 el
  have hU0 : ChartEqOnBonds S U (_root_.YangMills.Construction.BlockAverages.CriticalChainFirstOrder.zeroChart F) :=
    hU.unique _ (zeroChart_inGaugeSlice S _ _) (by rw [supWeightedNorm_zeroChart]; exact hrL.le) fun A _ => hzero A
  obtain ⟨k, c, X, α, hk, hX, hα, hvb, hsp⟩ := exists_bondSpread (innerBonds S F.top) v hB
  obtain ⟨T, hTc⟩ := hTall k c X hk hX
  set Tf : ℝ → ChainChart F := fun τ => T (τ • α) with hTf
  have htop : ∀ τ : ℝ, rotatedTop c X (τ • α) flatTopField = rotatedFlatField v τ := by
    intro τ
    funext y i
    simp only [rotatedTop, rotatedFlatField, rotatedField, hsp]
  classical
  have hT0 : Tf 0 = T 0 := by simp only [hTf, zero_smul]
  have e0 : (0 : ℝ) • α = 0 := zero_smul _ _
  have hlin : HasDerivAt (fun τ : ℝ => τ • α) α 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const α
  have hdu : ∀ b ∈ innerBonds S 0, HasDerivAt (fun τ => (((Tf τ).fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]))
      (((fderiv ℝ (fun ζ => (T ζ).fine b.1 b.2) 0 α : imaginaryQuaternions)) : ℍ[ℝ]) 0 := by
    intro b hb
    have h1 := (hTc.analyticAt_fine b hb).differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt (fun ζ => (T ζ).fine b.1 b.2) (fderiv ℝ (fun ζ => (T ζ).fine b.1 b.2) 0)
        ((0 : ℝ) • α) := by rw [e0]; exact h1
    have h3 := h2.comp_hasDerivAt (0 : ℝ) hlin
    exact (Submodule.subtypeL imaginaryQuaternions).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
  have hdm : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1),
      HasDerivAt (fun τ => (((Tf τ).coarse j b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]))
      (((fderiv ℝ (fun ζ => (T ζ).coarse j b.1 b.2) 0 α : imaginaryQuaternions)) : ℍ[ℝ]) 0 := by
    intro j hj b hb
    have h1 := (hTc.analyticAt_coarse j hj b hb).differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt (fun ζ => (T ζ).coarse j b.1 b.2) (fderiv ℝ (fun ζ => (T ζ).coarse j b.1 b.2) 0)
        ((0 : ℝ) • α) := by rw [e0]; exact h1
    have h3 := h2.comp_hasDerivAt (0 : ℝ) hlin
    exact (Submodule.subtypeL imaginaryQuaternions).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
  set D : ChainChart F :=
    ⟨fun x i => if (x, i) ∈ innerBonds S 0 then fderiv ℝ (fun ζ => (T ζ).fine x i) 0 α else 0,
      fun j y i => if j + 1 < F.top ∧ (y, i) ∈ innerBonds S (j + 1) then
        fderiv ℝ (fun ζ => (T ζ).coarse j y i) 0 α else 0⟩
    with hD
  have hfirst : HasFirstOrderOn S Tf D := by
    refine ⟨fun b hb => ?_, fun j hj c hc => ?_, fun b hb => ?_, fun j hj c hc => ?_⟩
    · rw [hT0, hTc.eq_at_zero.1 b hb, hU0.1 b hb]
      rfl
    · rw [hT0, hTc.eq_at_zero.2 j hj c hc, hU0.2 j hj c hc]
      rfl
    · have e : D.fine b.1 b.2 = fderiv ℝ (fun ζ => (T ζ).fine b.1 b.2) 0 α := by
        simp only [hD]
        exact if_pos hb
      rw [e]
      exact hdu b hb
    · have e : D.coarse j c.1 c.2 = fderiv ℝ (fun ζ => (T ζ).coarse j c.1 c.2) 0 α := by
        simp only [hD]
        exact if_pos ⟨hj, hc⟩
      rw [e]
      exact hdm j hj c hc
  set Amax : ℝ := ∑ l, α l with hAmax
  have hA0 : 0 ≤ Amax := Finset.sum_nonneg fun l _ => hα l
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set ε : ℝ := min (r' / k) (min s (σ₁ / (2 * k))) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (lt_min hs0 (by positivity))
  have hlt : ∀ᶠ τ in 𝓝 (0 : ℝ), |τ| * Amax < ε := by
    have : Tendsto (fun τ : ℝ => |τ| * Amax) (𝓝 0) (𝓝 (|(0 : ℝ)| * Amax)) :=
      (continuous_abs.tendsto 0).mul_const _
    rw [abs_zero, zero_mul] at this
    exact this.eventually_lt_const hε0
  have hkey : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ (Y : F.FieldChain) (kk : F.SiteGauge), Y F.top = rotatedFlatField v τ →
      chartAction a S R (Tf τ) (rotatedFlatField v τ) ≤ gaugedChainAction a S Y kk := by
    filter_upwards [hlt] with τ hτ Y kk hYtop
    set σ : ℝ := |τ| * Amax with hσ
    have hσ0 : 0 ≤ σ := mul_nonneg (abs_nonneg _) hA0
    have hζ : ∀ l, |(τ • α) l| ≤ σ := by
      intro l
      rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (hα l)]
      exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _ => hα i) (Finset.mem_univ l)) (abs_nonneg _)
    have h1 : σ < r' / k := lt_of_lt_of_le hτ (min_le_left _ _)
    have h2 : σ < s := lt_of_lt_of_le hτ ((min_le_right _ _).trans (min_le_left _ _))
    have h3 : σ < σ₁ / (2 * k) := lt_of_lt_of_le hτ ((min_le_right _ _).trans (min_le_right _ _))
    have hcr := hTc.critical (τ • α) σ hζ h1
    rw [htop] at hcr
    have hs' : 0 < s + k * σ := by positivity
    have hs2 : s ≤ σ₁ / 2 := min_le_right _ _
    have hs3 : s + k * σ ≤ σ₁ := by
      have : (k : ℝ) * σ < σ₁ / 2 := by
        have := mul_lt_mul_of_pos_left h3 hkpos
        have e : (k : ℝ) * (σ₁ / (2 * k)) = σ₁ / 2 := by field_simp
        linarith
      linarith
    have hvb' : ∀ y i, ‖τ • v y i‖ ≤ s + k * σ := by
      intro y i
      rw [norm_smul, Real.norm_eq_abs]
      have : |τ| * ‖v y i‖ ≤ σ := mul_le_mul_of_nonneg_left (hvb y i) (abs_nonneg _)
      have : 0 ≤ (k : ℝ) * σ := by positivity
      linarith
    have hc2 := hCV F m S hFL hamb hm hreg (s + k * σ) flatTopField (fun y i => τ • v y i) hs' hs3
      (flatTopField_isCold S hs') hvb' (T (τ • α)) hcr
    exact hc2.2 Y kk hYtop
  have hshare : ∀ Y : F.Cell, ∀ᶠ τ in 𝓝 (0 : ℝ), minimalCellShare a S Y (rotatedFlatField v τ) =
      weightedChainTerms a S (plaquetteCornerShare Y) (bondEndShare Y)
        (chartChain R (Tf τ) (rotatedFlatField v τ)) (chartGauge R (Tf τ)) := by
    intro Y
    filter_upwards [hkey, eventually_rotatedFlatField_isCold S v hσ₂] with τ h1 h2
    obtain ⟨X', hmin, hsh⟩ := exists_minimalChain_of_chart hCC hFC ha hLpos S R (Tf τ) (rotatedFlatField v τ) h1
    have h3 := ((hAS F m S hFL hamb hm hreg σ₂ (rotatedFlatField v τ) hσ₂ le_rfl h2).1).2.2.1 X' hmin Y
    rw [← h3, hsh]
  have hanalytic : ∀ Y : F.Cell, AnalyticAt ℝ (fun τ : ℝ => minimalCellShare a S Y (rotatedFlatField v τ)) 0 := by
    intro Y
    have h1 := ((hAS F m S hFL hamb hm hreg σ₂ flatTopField hσ₂ le_rfl (flatTopField_isCold S hσ₂)).1).2.1 Y k c X
    have hl : AnalyticAt ℝ (fun τ : ℝ => τ • α) 0 := (ContinuousLinearMap.toSpanSingleton ℝ α).analyticAt 0
    have h2 : AnalyticAt ℝ (fun σ : Fin k → ℝ => minimalCellShare a S Y (rotatedField (bondSpread c X σ) flatTopField))
        ((fun τ : ℝ => τ • α) 0) := by
      show AnalyticAt ℝ _ ((0 : ℝ) • α)
      rw [e0]
      exact h1
    have h3 : AnalyticAt ℝ ((fun σ : Fin k → ℝ => minimalCellShare a S Y (rotatedField (bondSpread c X σ) flatTopField)) ∘
        fun τ : ℝ => τ • α) 0 := AnalyticAt.comp h2 hl
    refine h3.congr (Eventually.of_forall fun τ => ?_)
    simp only [Function.comp]
    rw [← htop τ]
    rfl
  have hen : ∀ (wp : F.Site 0 × Fin 4 × Fin 4 → ℝ) (wc : (j : ℕ) → F.Site (j + 1) × Fin 4 → ℝ)
      (A : ChainChart F), weightedQuadraticEnergy a S wp wc R A v₀ = weightedQuadraticEnergy a S wp wc R A v := by
    intro wp wc A
    unfold weightedQuadraticEnergy
    congr 2
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [hvag c hc]
  have hagree : ∀ Y : F.Cell, (fun τ : ℝ => minimalCellShare a S Y (rotatedFlatField v₀ τ)) =ᶠ[𝓝 0]
      (fun τ : ℝ => minimalCellShare a S Y (rotatedFlatField v τ)) := by
    intro Y
    filter_upwards [eventually_rotatedFlatField_isCold S v₀ hσ₂, eventually_rotatedFlatField_isCold S v hσ₂]
      with τ c0 c1
    refine minimalCellShare_congr hLV ha S (fun c hc => ?_)
      ((hAS F m S hFL hamb hm hreg σ₂ _ hσ₂ le_rfl c0).1).2.2.1
      ((hAS F m S hFL hamb hm hreg σ₂ _ hσ₂ le_rfl c1).1).2.2.1 Y
    simp only [rotatedFlatField, rotatedField]
    rw [hvag c hc]
  refine ⟨D, fun A => ?_, fun Y => ?_⟩
  · unfold flatTopEnergy
    rw [hen, hen]
    have hD' := (hSO F S R a (fun _ => 1) (fun _ _ => 1) Tf D v hoddF hR hfirst).2
    have hA' := (hSO F S R a (fun _ => 1) (fun _ _ => 1) (fun τ => chartMove (_root_.YangMills.Construction.BlockAverages.CriticalChainFirstOrder.zeroChart F) A τ) A v hoddF hR
      (chartMove_hasFirstOrderOn S A)).2
    have hle := le_of_tendsto_of_tendsto hD' hA' (eventually_nhdsWithin_of_eventually_nhds
      (hkey.mono fun τ h => by
        have h2 : chartAction a S R (Tf τ) (rotatedFlatField v τ) ≤
            chartAction a S R (chartMove (_root_.YangMills.Construction.BlockAverages.CriticalChainFirstOrder.zeroChart F) A τ) (rotatedFlatField v τ) :=
          h (chartChain R (chartMove (_root_.YangMills.Construction.BlockAverages.CriticalChainFirstOrder.zeroChart F) A τ) (rotatedFlatField v τ))
            (chartGauge R (chartMove (_root_.YangMills.Construction.BlockAverages.CriticalChainFirstOrder.zeroChart F) A τ)) (chartChain_top _ _ _)
        rw [chartAction_eq_weightedChainTerms, chartAction_eq_weightedChainTerms] at h2
        exact div_le_div_of_nonneg_right h2 (sq_nonneg τ)))
    exact show weightedQuadraticEnergy a S (fun _ => 1) (fun _ _ => 1) R D v ≤
        weightedQuadraticEnergy a S (fun _ => 1) (fun _ _ => 1) R A v from by linarith
  · rw [(hagree Y).iteratedDeriv_eq 2, hen]
    obtain ⟨z0, zl⟩ := hSO F S R a (plaquetteCornerShare Y) (bondEndShare Y) Tf D v hoddF hR hfirst
    have hf0 : minimalCellShare a S Y (rotatedFlatField v 0) = 0 := by
      rw [(hshare Y).self_of_nhds, z0]
    have hlim : Tendsto (fun τ : ℝ => minimalCellShare a S Y (rotatedFlatField v τ) / τ ^ 2) (𝓝[≠] 0)
        (𝓝 ((1 / 2) * weightedQuadraticEnergy a S (plaquetteCornerShare Y) (bondEndShare Y) R D v)) := by
      refine zl.congr' ?_
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hshare Y)] with τ h
      rw [h]
    rw [iteratedDeriv_two_of_tendsto_div_sq (hanalytic Y) hf0 hlim]
    ring
end YangMills.Construction.BlockAverages
end

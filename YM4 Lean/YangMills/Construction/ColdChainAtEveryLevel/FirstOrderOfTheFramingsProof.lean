import YangMills.Construction.ColdChainAtEveryLevel.CriticalForAllVariationsProof
import YangMills.Construction.ColdChainAtEveryLevel.FirstOrderOfTheFramings
import YangMills.Construction.ColdChainAtEveryLevel.SumOfTheGluedFirstOrders
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.GluedFirstVariation
open VariationRates
variable {F : BlockFrame} {S : Finset F.Cell}
theorem distFromOne_chartField_le_of_quartic {R : F.FieldChain} {U : ChainChart F} {θ C₁ s : ℝ} (hθ : 0 < θ)
    (hL : 1 ≤ F.blockSide) (hpos : 0 ≤ C₁ * s)
    (hq : ∀ (j : ℕ) (p : F.Site 0) (r : ℝ), j < F.top → 1 ≤ r → r ≤ (F.blockSide : ℝ) ^ (F.top - j) →
      localQuarticSum S R U j p r ≤ (C₁ * s) ^ 4 * (r / (F.blockSide : ℝ) ^ (F.top - j)) ^ (4 * θ))
    {j : ℕ} (hj : j < F.top) {b : F.Site j × Fin 4} (hb : b ∈ innerBonds S j) :
    _root_.YangMills.Construction.BlockAverages.distFromOne (chartField R U j b.1 b.2 * (R j b.1 b.2)⁻¹) ≤ C₁ * s := by apply _root_.YangMills.Construction.GaugedCriticality.norm_chartField_ratio_sub_one_le <;> assumption
theorem bondSum_le_length_mul {j : ℕ} {g : F.Site j → Fin 4 → ℝ} {ε : ℝ} (x : F.Site j) (l : List PathStep)
    (h : ∀ b, LiesOnPath b x l → g b.1 b.2 ≤ ε) : VariationRates.bondSum g x l ≤ l.length * ε := by
  induction l generalizing x with
  | nil => simp [VariationRates.bondSum]
  | cons st r ih =>
    simp only [VariationRates.bondSum, List.length_cons]
    have h1 := ih (x + stepDisplacement j st) fun b hb => h b (Or.inr hb)
    have h2 : (if st.2 then g x st.1 else g (x - unitStep j st.1) st.1) ≤ ε := by
      split_ifs with hs
      · exact h (x, st.1) (Or.inl (by simp [hs]))
      · exact h (x - unitStep j st.1, st.1) (Or.inl (by simp [hs]))
    push_cast
    linarith
theorem norm_contourAverage_sub_le (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top) {X R : F.GaugeField j}
    {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ b ∈ innerBonds S j, _root_.YangMills.Construction.BlockAverages.distFromOne (X b.1 b.2 * (R b.1 b.2)⁻¹) ≤ ε)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1)) :
    ‖_root_.YangMills.Construction.BlockAverages.contourAverage X c - _root_.YangMills.Construction.BlockAverages.contourAverage R c‖ ≤ EvaluationSums.maxContourLength F.blockSide * ε := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hw : (0 : ℝ) ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) := by positivity
  unfold _root_.YangMills.Construction.BlockAverages.contourAverage
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
  have h1 : ∀ a ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy X (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide a π c.2) : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy R (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide a π c.2) : UnitQuaternion) : ℍ[ℝ])‖ ≤
          EvaluationSums.maxContourLength F.blockSide * ε := by
    intro a ha π
    set hX := pathHolonomy X (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide a π c.2) with hhX
    set hR := pathHolonomy R (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide a π c.2) with hhR
    have e : (hX : ℍ[ℝ]) - (hR : ℍ[ℝ]) = (((hX * hR⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) * (hR : ℍ[ℝ]) := by
      rw [sub_mul, one_mul, Submonoid.coe_mul, mul_assoc, coe_inv_mul_coe, mul_one]
    rw [e, norm_mul, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, mul_one]
    refine (distFromOne_pathHolonomy_div_le X R _ _).trans ?_
    refine (bondSum_le_length_mul (ε := ε) _ _ fun b hb' =>
      hb b (mem_innerBonds_of_liesOnPath_bondContour hodd hj hc ha π hb').1).trans ?_
    have : ((bondContour F.blockSide a π c.2).length : ℝ) ≤ EvaluationSums.maxContourLength F.blockSide := by
      exact_mod_cast EvaluationSums.length_bondContour_le ha π c.2
    exact mul_le_mul_of_nonneg_right this hε
  calc _ ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) * ∑ a ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        (EvaluationSums.maxContourLength F.blockSide * ε) := by
        refine mul_le_mul_of_nonneg_left ?_ hw
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
        rw [← Finset.sum_sub_distrib]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => h1 a ha π)
    _ = _ := EvaluationSums.contour_average_const hodd _
theorem baseDistance_le_of_mem_centredCube {x : F.Site 0} {v : F.Cell} {h : LatticeFractionalIntegration.Lattice4}
    (hh : h ∈ centredCube (F.blockSide ^ F.top)) (e : x = cellCentre 0 v + siteOfCoords 0 h) :
    ((baseDistance x (cellCentre 0 v) : ℕ) : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := by
  have h1 : baseDistance x (cellCentre 0 v) ≤ F.blockSide ^ F.top := by
    unfold baseDistance
    refine Finset.sup_le fun i _ => ?_
    have e1 : baseSite x - cellCentre 0 v = siteOfCoords 0 h := by
      rw [baseSite_of_level_zero, e]
      abel
    rw [e1]
    refine (natAbs_valMinAbs_intCast_le _ (h i)).trans ?_
    have h2 := (LatticePaths.mem_centredCube_iff _ _).1 hh i
    omega
  exact_mod_cast h1
theorem cellwiseSizes_criticalFieldChain {a θ C₁ s del Ca : ℝ} (ha : 0 ≤ a) (hθ : 0 < θ) (hC₁ : 0 < C₁)
    (hs : 0 < s) (hL : 1 ≤ F.blockSide) (hodd : Odd F.blockSide) {V : F.GaugeField F.top}
    {v : F.Site F.top → Fin 4 → imaginaryQuaternions} {U : ChainChart F}
    (hU : IsCriticalChainOverTop a θ del Ca C₁ s S V (rotatedField v V) U) :
    CellwiseSizes a S (criticalFieldChain S V v U) (criticalGauge S V U) ((1 + a) * C₁ * s)
      (4 / (F.blockSide : ℝ)) := by
  classical
  have hL' : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
  have hpw : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := one_le_pow₀ hL'
  have hnpos : 0 < F.top := Nat.succ_pos _
  have hKC : C₁ * s ≤ (1 + a) * C₁ * s := by
    nlinarith [mul_pos hC₁ hs, mul_nonneg ha (mul_pos hC₁ hs).le]
  constructor
  · intro w hw
    have h1 := (hU.curvature_and_misfits (cellCentre 0 w) ((F.blockSide : ℝ) ^ F.top) hpw le_rfl).1
    rw [div_self (by positivity), Real.one_rpow, mul_one] at h1
    have h2 : ∑ p ∈ plaquettesOver S {w} 0,
        actionTermSize a (criticalFieldChain S V v U) (criticalGauge S V U) (Sum.inl p) ^ 2 ≤
          localCurvatureSum S (referenceFieldChain S V) U (cellCentre 0 w) ((F.blockSide : ℝ) ^ F.top) := by
      unfold localCurvatureSum
      have e : ∀ p : F.Site 0 × Fin 4 × Fin 4,
          actionTermSize a (criticalFieldChain S V v U) (criticalGauge S V U) (Sum.inl p) ^ 2 =
            ‖((plaquetteHolonomy (chartField (referenceFieldChain S V) U 0) p : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 := by
        intro p
        show ‖((plaquetteHolonomy (chartChain (referenceFieldChain S V) U (rotatedField v V) 0) p :
          UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 = _
        rw [ChartCoordinates.chartChain_of_lt _ _ _ hnpos]
      simp only [e]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun _ _ _ => sq_nonneg _
      have hp' := Finset.mem_filter.1 hp
      refine Finset.mem_filter.2 ⟨hp'.1, ?_⟩
      have hcell : enclosingCell p.1 = w := by simpa using hp'.2
      have hs0 : p.1 ∈ sitesOfCells S 0 := (Finset.mem_product.1 (Finset.mem_filter.1 hp'.1).1).1
      obtain ⟨y, hy, h, hh, e'⟩ := mem_sitesOfCells.1 hs0
      have hy' : y = w := by
        rw [← hcell, e']
        exact (LocalPartition.enclosingCell_cellCentre_add (by simpa using hodd) y h hh).symm
      subst hy'
      exact baseDistance_le_of_mem_centredCube (by simpa using hh) e'
    refine h2.trans (h1.trans ?_)
    exact pow_le_pow_left₀ (mul_pos hC₁ hs).le hKC 2
  · intro j hj w hw
    have h1 := (hU.misfits_on_cells j w hj).2
    unfold cellMisfitSum at h1
    have e : ∀ c ∈ bondsOver S {w} (j + 1),
        actionTermSize a (criticalFieldChain S V v U) (criticalGauge S V U) (Sum.inr ⟨j, c⟩) ^ 2 =
          a ^ 2 * _root_.YangMills.Construction.BlockAverages.distFromOne (chartBondMisfit (referenceFieldChain S V) U (rotatedField v V) j c) ^ 2 := by
      intro c _
      show (a * _root_.YangMills.Construction.BlockAverages.distFromOne _) ^ 2 = _
      rw [mul_pow]
      rfl
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    have hρ : 0 ≤ (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j) := by positivity
    have h3 : a ^ 2 * (C₁ * s * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j)) ^ 2 ≤
        ((1 + a) * C₁ * s * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j)) ^ 2 := by
      have hp : 0 ≤ C₁ * s * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j) := by positivity
      have e2 : (1 + a) * C₁ * s * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j) =
          (1 + a) * (C₁ * s * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j)) := by
        ring
      rw [e2, mul_pow (1 + a)]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg (C₁ * s * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j)))
      nlinarith
    exact (mul_le_mul_of_nonneg_left h1 (sq_nonneg a)).trans h3
theorem gluedFirstVariationStatement_holds (h₁ : gaugeChangeBoundStatement)
    (h₂ : criticalUnderGaugedVariationsStatement) (h₃ : referenceBoundsStatement)
    (h₄ : gaugeCovarianceStatement) : gluedFirstVariationStatement := by
  intro a θ del Ca ha hθ hθ8 hdel hdel8 hCa
  obtain ⟨L₁, p₁⟩ := h₁ a θ del Ca ha hθ hθ8 hdel hdel8 hCa
  obtain ⟨L₂, p₂⟩ := h₂ a θ del Ca ha hθ hθ8 hdel hdel8 hCa
  obtain ⟨Cb, cb, L₃, hCb, hcb, hB⟩ := h₃
  refine ⟨max (max L₁ L₂) (max L₃ 8), fun L hLodd hL0 C₁ C Cd hC₁ hC hCd => ?_⟩
  have hLa : L₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL0)
  have hLb : L₂ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL0)
  have hLc : L₃ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL0)
  have hLd : 8 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL0)
  obtain ⟨C₂, c, hC₂, hc, q₁⟩ := p₁ L hLodd hLa C₁ C Cd hC₁ hC hCd
  obtain ⟨σ₂, hσ₂, q₂⟩ := p₂ L hLodd hLb C₁ hC₁
  have hfc := GluedFirstOrderData.firstOrderConstant_nonneg L hC.le hC₂.le (Cd := Cd)
  refine ⟨(1 + a) * C₁ * GluedFirstOrderData.firstOrderConstant L C C₂ Cd + 1, c, by positivity, hc,
    fun e0 he0 he0c => ?_⟩
  obtain ⟨σ₁, hσ₁, r₁⟩ := q₁ e0 he0 he0c
  set Lc : ℝ := ((EvaluationSums.maxContourLength L : ℕ) : ℝ) with hLcdef
  have hLc0 : 0 ≤ Lc := by positivity
  set σ : ℝ := min (min σ₁ σ₂) (min cb (min 1 (1 / (2 * (Lc * C₁ + Cb + 1))))) with hσ
  have hσpos : 0 < σ := lt_min (lt_min hσ₁ hσ₂) (lt_min hcb (lt_min one_pos (by positivity)))
  refine ⟨σ, hσpos, fun F m S hFL hamb hm hreg s V v hs hsσ hcold hv U hU X k Γ hX hfr => ?_⟩
  have hodd : Odd F.blockSide := hFL ▸ hLodd
  have hF1 : 1 ≤ F.blockSide := hodd.pos
  have hF8 : 8 ≤ F.blockSide := hFL ▸ hLd
  have hs1 : s ≤ σ₁ := hsσ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 : s ≤ σ₂ := hsσ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 : s ≤ cb := hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs4 : s ≤ 1 := hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs5 : s ≤ 1 / (2 * (Lc * C₁ + Cb + 1)) :=
    hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hLF3 : L₃ ≤ F.blockSide := by rw [hFL]; exact hLc
  have hBs := hB F m S hodd hLF3 hamb hm hreg s V hs hs3 hcold
  have hmean := hBs.2.2.2.2.2
  set W := criticalFieldChain S V v U with hW
  set kW := criticalGauge S V U with hkW
  set R := referenceFieldChain S V with hR
  have hε : 0 ≤ C₁ * s := by positivity
  have hsmall : Lc * (C₁ * s) + Cb * s ^ 2 < 1 := by
    have h1 : s * (2 * (Lc * C₁ + Cb + 1)) ≤ 1 := by
      rwa [le_div_iff₀ (by positivity)] at hs5
    have h2 : s ^ 2 ≤ s := by nlinarith
    have h3 : Cb * s ^ 2 ≤ Cb * s := mul_le_mul_of_nonneg_left h2 hCb.le
    nlinarith
  have hmeans : ∀ t ∈ actionTerms S, AveragesNeZero W kW t := by
    intro t ht
    rcases t with p | ⟨j, c'⟩
    · trivial
    · have hcm := Finset.inr_mem_disjSum.1 ht
      have hj : j < F.top := Finset.mem_range.1 (Finset.mem_sigma.1 hcm).1
      have hcb' : c' ∈ innerBonds S (j + 1) := (Finset.mem_sigma.1 hcm).2
      show gaugedContourAverage (W j) (kW (j + 1)) c' ≠ 0
      intro h0
      have hn := norm_gaugedContourAverage (W j) (kW (j + 1)) c'
      rw [h0, norm_zero] at hn
      have hWj : W j = chartField R U j := ChartCoordinates.chartChain_of_lt _ _ _ hj
      rw [hWj] at hn
      have hm1 := norm_contourAverage_sub_le (S := S) hodd hj (X := chartField R U j) (R := R j) hε
        (fun b hb => distFromOne_chartField_le_of_quartic hθ hF1 hε hU.quartic hj hb) hcb'
      have hz : _root_.YangMills.Construction.BlockAverages.contourAverage (chartField R U j) c' = 0 := norm_eq_zero.1 hn.symm
      rw [hz, zero_sub, norm_neg, hFL] at hm1
      have hm2 := (hmean j hj c' hcb').2
      have hsc : BlockAverages.levelScale F (j + 1) ^ 4 ≤ 1 := by
        have hh : BlockAverages.levelScale F (j + 1) = EvaluationSums.levelScale F (j + 1) := rfl
        rw [hh]
        exact pow_le_one₀ (EvaluationSums.levelScale_nonneg F _) (VariationRates.levelScale_le_one hodd _)
      have hm3 : Cb * s ^ 2 * BlockAverages.levelScale F (j + 1) ^ 4 ≤ Cb * s ^ 2 := by
        have : 0 ≤ Cb * s ^ 2 := by positivity
        nlinarith
      linarith
  have hcrit : ∀ Vv : VariationSlot F → imaginaryQuaternions,
      ∑ t ∈ actionTerms S, actionTermRateLinear a W kW t Vv = 0 := by
    intro Vv
    have h0 := (q₂ F m S hFL hamb hm hreg s V v hs hs2 hcold hv U hU (variationOfSlots Vv)).2
    rw [← h0]
    exact Finset.sum_congr rfl fun t ht =>
      (firstVariation_eq_actionTermRate a W kW (variationOfSlots Vv) ht (hmeans t ht)).symm
  set A := cellsClearOfHighEnergy a e0 S X k with hA
  set Bd := S.filter fun y => e0 ^ 2 < patchAction a S y X k with hBd
  have hAS : A ⊆ S := Finset.filter_subset _ _
  have hρ1 : 4 / (F.blockSide : ℝ) ≤ 1 / 2 := by
    have : (8 : ℝ) ≤ F.blockSide := by exact_mod_cast hF8
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hD0 : ∀ z, 0 ≤ relativeEnergy a S z W kW X k (Γ z) := by
    intro z
    unfold relativeEnergy
    exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg ha.le (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hclear : GluedFirstOrderData a C C₂ Cd e0 ((1 + a) * C₁ * s) (4 / (F.blockSide : ℝ)) S A Bd W kW X k Γ
      (fun z => relativeEnergy a S z W kW X k (Γ z)) :=
    { ambient := hamb
      odd := hodd
      covariance := h₄
      coupling_nonneg := ha.le
      pinConst_nonneg := hC.le
      changeConst_nonneg := hC₂.le
      energyConst_nonneg := hCd.le
      smallScale_nonneg := he0.le
      sizeConst_nonneg := by positivity
      ratio_nonneg := by positivity
      ratio_le_half := hρ1
      sizes := cellwiseSizes_criticalFieldChain ha.le hθ hC₁ hs hF1 hodd hU
      averages_ne_zero := hmeans
      critical := hcrit
      subset := hAS
      orthant := fun z => (closedOrthant_spec hreg (by omega) z).1
      energy_eq := fun _ => rfl
      energy_nonneg := fun z _ => hD0 z
      pinned := fun z hz => (hfr z hz).1
      energy_le := fun z hz => (hfr z hz).2
      change_le := by
        intro z hz z' hz' hd y hy hp hp' j hj
        exact (r₁ F m S hFL hamb hm hreg s V v hs hs1 hcold hv U hU X k (Γ z) (Γ z') z z' y hX (hAS hz)
          (hAS hz') hy hd hp hp' (hfr z hz) (hfr z' hz')).scaled_le j hj
      near_bad := by
        intro y hy hyA
        have h1 : ¬ ∀ b ∈ S, e0 ^ 2 < patchAction a S b X k → 40 < cellSupDist y b :=
          fun h => hyA (Finset.mem_filter.2 ⟨hy, h⟩)
        simp only [not_forall, not_lt] at h1
        obtain ⟨b, hb, hbad, hd⟩ := h1
        exact ⟨b, Finset.mem_filter.2 ⟨hb, hbad⟩, hd⟩ }
  have hb := hclear.abs_sum_weighted_le_firstOrderConstant
  have e : ∑ z ∈ A, ∑ t ∈ actionTerms S, cellPartition S (actionTermSite t) z *
      firstVariation a W kW (gaugeVariation W kW X k (Γ z)) t =
        ∑ z ∈ A, ∑ t ∈ actionTerms S, termPartition S z t *
          GluedFirstOrderData.actionForms a W kW t (VariationRates.framingVariation W kW X k Γ z) := by
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun t ht => ?_
    congr 1
    rw [firstVariation_eq_actionTermRate a W kW _ ht (hmeans t ht)]
    show _ = actionTermRate a W kW (variationOfSlots (gaugeSlots W kW X k (Γ z))) t
    rw [← slotValues_gaugeVariation, variationOfSlots_slotValues]
  have hgoal : (∑ z ∈ cellsClearOfHighEnergy a e0 S X k, ∑ t ∈ actionTerms S,
      cellPartition S (actionTermSite t) z * firstVariation a W kW (gaugeVariation W kW X k (Γ z)) t) = _ := e
  have hU0 : 0 ≤ ∑ z ∈ A, relativeEnergy a S z W kW X k (Γ z) + e0 * (Bd.card : ℝ) :=
    add_nonneg (Finset.sum_nonneg fun z _ => hD0 z) (by positivity)
  rw [hgoal]
  refine hb.trans ?_
  rw [hFL]
  have : (1 + a) * C₁ * s * GluedFirstOrderData.firstOrderConstant L C C₂ Cd *
      (∑ z ∈ A, relativeEnergy a S z W kW X k (Γ z) + e0 * (Bd.card : ℝ)) =
        ((1 + a) * C₁ * GluedFirstOrderData.firstOrderConstant L C C₂ Cd) * s *
          (∑ z ∈ A, relativeEnergy a S z W kW X k (Γ z) + e0 * (Bd.card : ℝ)) := by
    ring
  rw [this]
  refine mul_le_mul_of_nonneg_right ?_ hU0
  refine mul_le_mul_of_nonneg_right ?_ hs.le
  linarith
end YangMills.Construction.BlockAverages.GluedFirstVariation
end

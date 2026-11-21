import YangMills.Construction.ColdChainAtEveryLevel.LocalBoundsOfASmallChainProof
import YangMills.Construction.ColdChainAtEveryLevel.VariationOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.MisfitVariation
open BlockAverages BlockAverages.ChartCoordinates LatticePaths BlockLines BondHull UnitCurves BondVariation
  LatticeFractionalIntegration FiniteDifferences
variable {F : BlockFrame}
open Classical in
def selfScaledDirection (U : ChainChart F) (j : ℕ) (z : F.Cell) : ChainChart F :=
  ⟨fun _ _ => 0, fun i y k => if i = j ∧ enclosingCell y = z then (‖(U.coarse i y k : ℍ[ℝ])‖ ^ 2) • U.coarse i y k else 0⟩
theorem pathHolonomy_congr {i : ℕ} {X X' : F.GaugeField i} {x₀ : F.Site i} {H : Set Lattice4}
    (h : ∀ a ∈ H, ∀ k, a + basisVector k ∈ H → X (x₀ + siteOfCoords i a) k = X' (x₀ + siteOfCoords i a) k) :
    ∀ (l : List PathStep) (u : Lattice4), AllAlong (fun v => v ∈ H) u l →
      pathHolonomy X (x₀ + siteOfCoords i u) l = pathHolonomy X' (x₀ + siteOfCoords i u) l := by
  intro l
  induction l with
  | nil => intro u _; rfl
  | cons st r ih =>
    intro u hp
    have hnext : x₀ + siteOfCoords i u + stepDisplacement i st = x₀ + siteOfCoords i (u + FlatPairing.stepDisplacement st) := by
      rw [BlockAverages.ChartCoordinates.stepDisplacement_eq_siteOfCoords, add_assoc, ← siteOfCoords_add]
    have hs : linkValue X (x₀ + siteOfCoords i u) st = linkValue X' (x₀ + siteOfCoords i u) st := by
      obtain ⟨k, b⟩ := st
      cases b
      · have hv := allAlong_head hp.2
        have e1 : FlatPairing.stepDisplacement ((k, false) : PathStep) = - basisVector k := by
          simp [FlatPairing.stepDisplacement]
        rw [e1] at hv
        have hu' : (u + -basisVector k) + basisVector k ∈ H := by simpa using hp.1
        have e : x₀ + siteOfCoords i u - unitStep i k = x₀ + siteOfCoords i (u + -basisVector k) := by
          rw [siteOfCoords_add, unitStep_eq, ← add_assoc, sub_eq_add_neg, siteOfCoords_neg]
        simp only [linkValue, Bool.false_eq_true, if_false]
        rw [e, h _ hv k hu']
      · have hv := allAlong_head hp.2
        have e1 : FlatPairing.stepDisplacement ((k, true) : PathStep) = basisVector k := by
          simp [FlatPairing.stepDisplacement]
        rw [e1] at hv
        simp only [linkValue, if_true]
        exact h _ hp.1 k hv
    simp only [pathHolonomy]
    rw [hnext, ih _ hp.2, hs]
theorem gaugedContourAverage_congr (hodd : Odd F.blockSide) {i : ℕ} (hi : i < F.top) {X X' : F.GaugeField i}
    (Rr : F.GaugeField i) (c : F.Site (i + 1) × Fin 4)
    (h : ∀ a ∈ FlatPairing.twoBlockHull F.blockSide c.2, ∀ k, a + basisVector k ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      X (refineSite c.1 + siteOfCoords i a) k = X' (refineSite c.1 + siteOfCoords i a) k) :
    gaugedContourAverage X (balancingGauge X Rr) c = gaugedContourAverage X' (balancingGauge X' Rr) c := by
  have hL : 1 ≤ F.blockSide := hodd.pos
  have h1 : ∀ a ∈ centredCube F.blockSide, ∀ k, a + basisVector k ∈ centredCube F.blockSide →
      X (refineSite c.1 + siteOfCoords i a) k = X' (refineSite c.1 + siteOfCoords i a) k :=
    fun a ha k hk => h a (mem_twoBlockHull_of_mem_centredCube ha c.2) k (mem_twoBlockHull_of_mem_centredCube hk c.2)
  have h2 : ∀ a ∈ centredCube F.blockSide, ∀ k, a + basisVector k ∈ centredCube F.blockSide →
      X (refineSite (c.1 + unitStep (i + 1) c.2) + siteOfCoords i a) k =
        X' (refineSite (c.1 + unitStep (i + 1) c.2) + siteOfCoords i a) k := by
    intro a ha k hk
    have e : refineSite (c.1 + unitStep (i + 1) c.2) + siteOfCoords i a =
        refineSite c.1 + siteOfCoords i ((F.blockSide : ℤ) • basisVector c.2 + a) := by
      rw [refineSite_add_unitStep hi, add_assoc, ← siteOfCoords_add]
    rw [e]
    refine h _ (shift_mem_twoBlockHull_of_mem_centredCube ha c.2) k ?_
    rw [add_assoc]
    exact shift_mem_twoBlockHull_of_mem_centredCube hk c.2
  have hleg : ∀ y : F.Site (i + 1), (∀ a ∈ centredCube F.blockSide, ∀ k, a + basisVector k ∈ centredCube F.blockSide →
      X (refineSite y + siteOfCoords i a) k = X' (refineSite y + siteOfCoords i a) k) →
      balancingGauge X Rr y = balancingGauge X' Rr y := by
    intro y hy
    unfold balancingGauge relativePathAverage
    congr 3
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun π _ => ?_
    have := pathHolonomy_congr (H := {v | v ∈ centredCube F.blockSide}) hy (axisPath a π) 0
      (allAlong_axisPath_centredCube ha π)
    rw [add_siteOfCoords_zero] at this
    rw [this]
  unfold gaugedContourAverage
  rw [hleg _ h1, hleg _ h2]
  congr 2
  unfold contourAverage
  congr 1
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun π _ => ?_
  have := pathHolonomy_congr (H := {v | v ∈ FlatPairing.twoBlockHull F.blockSide c.2}) h
    (bondContour F.blockSide a π c.2) 0 (bondContour_spec π c.2 hL ha).1
  rw [add_siteOfCoords_zero] at this
  rw [this]
theorem chartMove_zero (U A : ChainChart F) : chartMove U A 0 = U := by
  cases U
  simp [chartMove]
section Curve
variable (R : F.FieldChain) (U : ChainChart F) (j : ℕ) (z : F.Cell)
def scaledCurve (τ : ℝ) : ChainChart F := chartMove U (selfScaledDirection U j z) τ
theorem scaledCurve_zero : scaledCurve U j z 0 = U := chartMove_zero _ _
theorem scaledCurve_fine (τ : ℝ) (x : F.Site 0) (i : Fin 4) : (scaledCurve U j z τ).fine x i = U.fine x i := by
  simp [scaledCurve, chartMove, selfScaledDirection]
theorem scaledCurve_coarse_of_ne (τ : ℝ) {i : ℕ} (hi : i ≠ j) (y : F.Site (i + 1)) (k : Fin 4) :
    (scaledCurve U j z τ).coarse i y k = U.coarse i y k := by
  simp [scaledCurve, chartMove, selfScaledDirection, hi]
theorem scaledCurve_coarse_of_not_mem (τ : ℝ) {y : F.Site (j + 1)} (hy : enclosingCell y ≠ z) (k : Fin 4) :
    (scaledCurve U j z τ).coarse j y k = U.coarse j y k := by
  simp [scaledCurve, chartMove, selfScaledDirection, hy]
theorem scaledCurve_coarse_of_mem (τ : ℝ) {y : F.Site (j + 1)} (hy : enclosingCell y = z) (k : Fin 4) :
    (scaledCurve U j z τ).coarse j y k = (1 + τ * ‖(U.coarse j y k : ℍ[ℝ])‖ ^ 2) • U.coarse j y k := by
  simp [scaledCurve, chartMove, selfScaledDirection, hy, add_smul, smul_smul]
theorem chartField_scaledCurve_of_le (τ : ℝ) :
    ∀ i, i ≤ j → chartField R (scaledCurve U j z τ) i = chartField R U i := by
  intro i
  induction i with
  | zero =>
    intro _
    funext x k
    simp only [chartField, scaledCurve_fine]
  | succ i ih =>
    intro hi
    funext y k
    simp only [chartField]
    rw [scaledCurve_coarse_of_ne U j z τ (by omega), ih (by omega)]
theorem chartField_scaledCurve_succ (τ : ℝ) (y : F.Site (j + 1)) (k : Fin 4) :
    chartField R (scaledCurve U j z τ) (j + 1) y k = expUnit ((scaledCurve U j z τ).coarse j y k) *
      referenceDefect R j (y, k) *
      polarUnit (gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) (y, k)) := by
  simp only [chartField]
  rw [chartField_scaledCurve_of_le R U j z τ j le_rfl]
theorem chartField_scaledCurve_of_lt (τ : ℝ) {i : ℕ} (hi : j < i) (y : F.Site (i + 1)) (k : Fin 4) :
    chartField R (scaledCurve U j z τ) (i + 1) y k = expUnit (U.coarse i y k) * referenceDefect R i (y, k) *
      polarUnit (gaugedContourAverage (chartField R (scaledCurve U j z τ) i)
        (balancingGauge (chartField R (scaledCurve U j z τ) i) (R i)) (y, k)) := by
  simp only [chartField]
  rw [scaledCurve_coarse_of_ne U j z τ (by omega)]
variable {S : Finset F.Cell}
theorem differentiableAt_scaledCurve_fine (b : F.Site 0 × Fin 4) :
    DifferentiableAt ℝ (fun τ : ℝ => (scaledCurve U j z τ).fine b.1 b.2) 0 := by
  simp only [scaledCurve_fine]
  exact differentiableAt_const _
theorem differentiableAt_scaledCurve_coarse (i : ℕ) (b : F.Site (i + 1) × Fin 4) :
    DifferentiableAt ℝ (fun τ : ℝ => (scaledCurve U j z τ).coarse i b.1 b.2) 0 := by
  simp only [scaledCurve, chartMove]
  exact (differentiableAt_const _).add (differentiableAt_id.smul_const _)
def linkDeriv (i : ℕ) (x : F.Site i) (k : Fin 4) : ℍ[ℝ] :=
  deriv (fun τ : ℝ => ((chartField R (scaledCurve U j z τ) i x k : UnitQuaternion) : ℍ[ℝ])) 0
theorem hasDerivAt_linkDeriv (hodd : Odd F.blockSide) (hreg : ChartIsRegular S R U) {i : ℕ} (hi : i < F.top)
    {b : F.Site i × Fin 4} (hb : b ∈ innerBonds S i) :
    HasDerivAt (fun τ : ℝ => ((chartField R (scaledCurve U j z τ) i b.1 b.2 : UnitQuaternion) : ℍ[ℝ]))
      (linkDeriv R U j z i b.1 b.2) 0 := by
  have hr : ChartIsRegular S R (scaledCurve U j z 0) := by rw [scaledCurve_zero]; exact hreg
  have h := chartField_differentiableOn hodd R (C := scaledCurve U j z) (p₀ := (0 : ℝ))
    (fun b _ => differentiableAt_scaledCurve_fine U j z b)
    (fun i _ b _ => differentiableAt_scaledCurve_coarse U j z i b) hr i hi
  have e := innerBonds_ends hb
  exact (h b.1 b.2 e.1 e.2).hasDerivAt
def linkDerivNorm (i : ℕ) (x : F.Site i) (k : Fin 4) : ℝ := ‖linkDeriv R U j z i x k‖
theorem linkDerivNorm_nonneg (i : ℕ) (x : F.Site i) (k : Fin 4) : 0 ≤ linkDerivNorm R U j z i x k := norm_nonneg _
def hullDerivSum (i : ℕ) (c : F.Site (i + 1) × Fin 4) : ℝ :=
  hullSum (fun b : F.Site i × Fin 4 => linkDerivNorm R U j z i b.1 b.2) c
theorem hullDerivSum_nonneg (i : ℕ) (c : F.Site (i + 1) × Fin 4) : 0 ≤ hullDerivSum R U j z i c := by
  unfold hullDerivSum hullSum
  refine Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_
  split_ifs
  · exact linkDerivNorm_nonneg _ _ _ _ _ _ _
  · exact le_rfl
theorem linkCurves_hull (hodd : Odd F.blockSide) (hreg : ChartIsRegular S R U) {i : ℕ} (hi : i < F.top)
    {c : F.Site (i + 1) × Fin 4} (hc : c ∈ innerBonds S (i + 1)) :
    LinkCurves (fun τ => chartField R (scaledCurve U j z τ) i) (linkDeriv R U j z i) (refineSite c.1)
      {v | v ∈ FlatPairing.twoBlockHull F.blockSide c.2} (hullDerivSum R U j z i c) := by
  intro a ha k hk
  have hb := bond_mem_innerBonds_of_mem_twoBlockHull hi hodd c hc a k ha hk
  refine ⟨hasDerivAt_linkDeriv R U j z hodd hreg hi hb, ?_⟩
  have := le_hullSum hodd.pos (fun b : F.Site i × Fin 4 => linkDerivNorm R U j z i b.1 b.2)
    (fun b => linkDerivNorm_nonneg _ _ _ _ _ _ _) c k ha hk
  exact this
def averageAlong (i : ℕ) (τ : ℝ) (c : F.Site (i + 1) × Fin 4) : ℍ[ℝ] :=
  gaugedContourAverage (chartField R (scaledCurve U j z τ) i)
    (balancingGauge (chartField R (scaledCurve U j z τ) i) (R i)) c
theorem exists_hasDerivAt_averageAlong (hodd : Odd F.blockSide) (hreg : ChartIsRegular S R U) {i : ℕ} (hi : i < F.top)
    {c : F.Site (i + 1) × Fin 4} (hc : c ∈ innerBonds S (i + 1)) {t ρ : ℝ} (v : UnitQuaternion) (ht0 : 0 ≤ t)
    (ht : 2 * F.blockSide * t ≤ 1 / 4) (hρ0 : 0 ≤ ρ)
    (hcl : ∀ a ∈ FlatPairing.twoBlockHull F.blockSide c.2, ∀ k, a + basisVector k ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      distFromOne (chartField R U i (refineSite c.1 + siteOfCoords i a) k *
        (R i (refineSite c.1 + siteOfCoords i a) k)⁻¹) ≤ t)
    (hρ : ∀ h ∈ centredCube F.blockSide, ∀ π,
      distFromOne (pathHolonomy (R i) (refineSite c.1) (bondContour F.blockSide h π c.2) * v⁻¹) ≤ ρ) :
    ∃ dY : ℍ[ℝ], HasDerivAt (fun τ => averageAlong R U j z i τ c) dY 0 ∧
      ‖dY‖ ≤ lineBlockAverage (linkDerivNorm R U j z i) c +
        24 * (17 * F.blockSide * t + ρ) * F.blockSide * hullDerivSum R U j z i c ∧
      (∀ (w : ℍ[ℝ]) (e : ℝ), (∀ h ∈ centredCube F.blockSide, ∀ π,
        ‖w - ((framedContour (chartField R U i) (R i) c h π : UnitQuaternion) : ℍ[ℝ])‖ ≤ e) →
        |inner ℝ w dY| ≤ e * (13 * F.blockSide * hullDerivSum R U j z i c)) ∧
      ∀ h ∈ centredCube F.blockSide, ∀ π,
        ‖((framedContour (chartField R U i) (R i) c h π : UnitQuaternion) : ℍ[ℝ]) - (v : ℍ[ℝ])‖ ≤
          17 * F.blockSide * t + ρ := by
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  obtain ⟨f1, f2, f3, f4, f5⟩ := bond_estimates_of_near hodd hi (chartField R U i) (R i) c v ht0 ht hcl hρ
  have hε0 : 0 ≤ 17 * (F.blockSide : ℝ) * t + ρ := by positivity
  have hε1 : 8 * (F.blockSide : ℝ) * t ≤ 17 * F.blockSide * t + ρ := by
    have : 0 ≤ (F.blockSide : ℝ) * t := by positivity
    nlinarith
  obtain ⟨dY, h1, h2, h3⟩ := exists_hasDerivAt_gaugedContourAverage
    (X := fun τ => chartField R (scaledCurve U j z τ) i) (dX := linkDeriv R U j z i)
    hodd hi (R i) c (M := hullDerivSum R U j z i c) (ε := 17 * F.blockSide * t + ρ) (u := (v : ℍ[ℝ]))
    (hullDerivSum_nonneg _ _ _ _ _ _)
    hε0 (norm_coe_unitQuaternion v) (linkCurves_hull R U j z hodd hreg hi hc)
    (by rw [scaledCurve_zero]; exact f1) (by rw [scaledCurve_zero]; exact f2)
    (by rw [scaledCurve_zero]; exact fun h hh π => (f3 h hh π).trans hε1)
    (by rw [scaledCurve_zero]; exact fun h hh π => (f4 h hh π).trans hε1)
    (by rw [scaledCurve_zero]; exact f5)
  refine ⟨dY, h1, h2, ?_, f5⟩
  intro w e hw
  refine h3 w e ?_
  rw [scaledCurve_zero]
  exact hw
theorem averageAlong_zero (i : ℕ) (c : F.Site (i + 1) × Fin 4) :
    averageAlong R U j z i 0 c = gaugedContourAverage (chartField R U i) (balancingGauge (chartField R U i) (R i)) c := by
  simp only [averageAlong, scaledCurve_zero]
theorem norm_gaugedContourAverage_sub_le (hodd : Odd F.blockSide) {i : ℕ} (hi : i < F.top) (X Rr : F.GaugeField i)
    (c : F.Site (i + 1) × Fin 4) (v : ℍ[ℝ]) {e : ℝ}
    (hP : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖((framedContour X Rr c h π : UnitQuaternion) : ℍ[ℝ]) - v‖ ≤ e) :
    ‖gaugedContourAverage X (balancingGauge X Rr) c - v‖ ≤ e := by
  have e1 : gaugedContourAverage X (balancingGauge X Rr) c - v =
      (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        (((framedContour X Rr c h π : UnitQuaternion) : ℍ[ℝ]) - v) := by
    simp only [Finset.sum_sub_distrib, smul_sub]
    rw [smul_sum_perm_const hodd, gaugedContourAverage_balancingGauge_eq hi]
  rw [e1]
  exact norm_smul_sum_perm_le hodd _ _ hP
theorem normalize_near {Y v : ℍ[ℝ]} {e : ℝ} (hv : ‖v‖ = 1) (h : ‖Y - v‖ ≤ e) (he : e ≤ 1 / 2) :
    Y ≠ 0 ∧ 1 - e ≤ ‖Y‖ ∧ ‖‖Y‖⁻¹ • Y - v‖ ≤ 2 * e := by
  have h1 : 1 - e ≤ ‖Y‖ := by
    have := norm_sub_norm_le v Y
    rw [hv, norm_sub_rev] at this
    linarith
  have h2 : ‖Y‖ ≤ 1 + e := by
    have := norm_sub_norm_le Y v
    rw [hv] at this
    linarith
  have hp : 0 < ‖Y‖ := by linarith
  have hY : Y ≠ 0 := norm_pos_iff.1 hp
  refine ⟨hY, h1, ?_⟩
  have e1 : ‖Y‖⁻¹ • Y - v = (‖Y‖⁻¹ • Y - Y) + (Y - v) := by abel
  rw [e1]
  refine (norm_add_le _ _).trans ?_
  have e2 : ‖Y‖⁻¹ • Y - Y = (‖Y‖⁻¹ - 1) • Y := by rw [sub_smul, one_smul]
  rw [e2, norm_smul, Real.norm_eq_abs]
  have e3 : |‖Y‖⁻¹ - 1| * ‖Y‖ = |1 - ‖Y‖| := by
    rw [← abs_of_pos hp, ← abs_mul, abs_of_pos hp, sub_mul, inv_mul_cancel₀ hp.ne', one_mul]
  rw [e3]
  have : |1 - ‖Y‖| ≤ e := abs_le.2 ⟨by linarith, by linarith⟩
  linarith
theorem lineBlockAverage_le_hullDerivSum (hodd : Odd F.blockSide) {i : ℕ} (c : F.Site (i + 1) × Fin 4) :
    lineBlockAverage (linkDerivNorm R U j z i) c ≤ F.blockSide * hullDerivSum R U j z i c := by
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  rw [lineBlockAverage_eq]
  have h1 : ∀ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
      linkDerivNorm R U j z i (lineBond c h r).1 (lineBond c h r).2 ≤ F.blockSide * hullDerivSum R U j z i c := by
    intro h hh
    have h2 : ∀ r ∈ Finset.range F.blockSide,
        linkDerivNorm R U j z i (lineBond c h r).1 (lineBond c h r).2 ≤ hullDerivSum R U j z i c := by
      intro r hr
      have hr' := Finset.mem_range.1 hr
      have e2 : h + (r : ℤ) • basisVector c.2 + basisVector c.2 = h + ((r + 1 : ℕ) : ℤ) • basisVector c.2 := by
        push_cast
        rw [add_smul, one_smul]
        abel
      have h3 := le_hullSum hodd.pos (fun b : F.Site i × Fin 4 => linkDerivNorm R U j z i b.1 b.2)
        (fun b => linkDerivNorm_nonneg _ _ _ _ _ _ _) c c.2 (add_smul_basisVector_mem_twoBlockHull hh c.2 hr'.le)
        (by rw [e2]; exact add_smul_basisVector_mem_twoBlockHull hh c.2 hr')
      show linkDerivNorm R U j z i (lineBond c h r).1 c.2 ≤ _
      rw [lineBond_fst]
      exact h3
    refine (Finset.sum_le_sum h2).trans (le_of_eq ?_)
    simp
  have h4 := Finset.sum_le_sum h1
  rw [Finset.sum_const, card_centredCube hodd, nsmul_eq_mul] at h4
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 1 / (F.blockSide : ℝ) ^ 4)
  refine h5.trans (le_of_eq ?_)
  push_cast
  field_simp
theorem linkDerivNorm_succ_le (hodd : Odd F.blockSide) (hreg : ChartIsRegular S R U) {i : ℕ} (hji : j < i)
    (hi : i + 1 < F.top) {c : F.Site (i + 1) × Fin 4} (hc : c ∈ innerBonds S (i + 1)) {t ρ : ℝ} (v : UnitQuaternion)
    (ht0 : 0 ≤ t) (ht : 2 * F.blockSide * t ≤ 1 / 4) (hρ0 : 0 ≤ ρ) (hε : 17 * F.blockSide * t + ρ ≤ 1 / 2)
    (hcl : ∀ a ∈ FlatPairing.twoBlockHull F.blockSide c.2, ∀ k, a + basisVector k ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      distFromOne (chartField R U i (refineSite c.1 + siteOfCoords i a) k *
        (R i (refineSite c.1 + siteOfCoords i a) k)⁻¹) ≤ t)
    (hρ : ∀ h ∈ centredCube F.blockSide, ∀ π,
      distFromOne (pathHolonomy (R i) (refineSite c.1) (bondContour F.blockSide h π c.2) * v⁻¹) ≤ ρ) :
    linkDerivNorm R U j z (i + 1) c.1 c.2 ≤ lineBlockAverage (linkDerivNorm R U j z i) c +
      50 * (17 * F.blockSide * t + ρ) * F.blockSide * hullDerivSum R U j z i c := by
  have hin : i < F.top := by omega
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  obtain ⟨dY, h1, h2, -, h4⟩ := exists_hasDerivAt_averageAlong R U j z hodd hreg hin hc v ht0 ht hρ0 hcl hρ
  set ε := 17 * (F.blockSide : ℝ) * t + ρ with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hnear := norm_gaugedContourAverage_sub_le hodd hin (chartField R U i) (R i) c (v : ℍ[ℝ]) h4
  rw [← averageAlong_zero R U j z] at hnear
  obtain ⟨hne, hlow, -⟩ := normalize_near (norm_coe_unitQuaternion v) hnear hε
  obtain ⟨dZ, hZ, nZ⟩ := exists_hasDerivAt_normalize_le h1 hne
  have hne' : ∀ᶠ τ in nhds (0 : ℝ), averageAlong R U j z i τ c ≠ 0 := h1.continuousAt.eventually_ne hne
  set E : UnitQuaternion := expUnit (U.coarse i c.1 c.2) * referenceDefect R i c with hE
  have hcur : HasDerivAt (fun τ : ℝ => ((chartField R (scaledCurve U j z τ) (i + 1) c.1 c.2 : UnitQuaternion) : ℍ[ℝ]))
      ((E : ℍ[ℝ]) * dZ) 0 := by
    refine (hZ.const_mul (E : ℍ[ℝ])).congr_of_eventuallyEq ?_
    filter_upwards [hne'] with τ hτ
    rw [chartField_scaledCurve_of_lt R U j z τ hji c.1 c.2, Submonoid.coe_mul]
    show (E : ℍ[ℝ]) * ((polarUnit (averageAlong R U j z i τ c) : UnitQuaternion) : ℍ[ℝ]) = _
    rw [coe_polarUnit hτ]
  have hd : linkDerivNorm R U j z (i + 1) c.1 c.2 = ‖dZ‖ := by
    unfold linkDerivNorm linkDeriv
    rw [hcur.deriv, norm_mul, norm_coe_unitQuaternion, one_mul]
  rw [hd]
  have hP := lineBlockAverage_le_hullDerivSum R U j z hodd (i := i) c
  have hM := hullDerivSum_nonneg R U j z i c
  set M := hullDerivSum R U j z i c
  set P := lineBlockAverage (linkDerivNorm R U j z i) c
  have hP0 : 0 ≤ P := lineBlockAverage_nonneg (linkDerivNorm_nonneg _ _ _ _ _) c
  have hn0 : 0 < ‖averageAlong R U j z i 0 c‖ := by linarith
  have h5 : ‖dZ‖ ≤ ‖dY‖ * (1 + 2 * ε) := by
    refine nZ.trans ?_
    rw [div_le_iff₀ hn0]
    have h6 : 1 ≤ (1 + 2 * ε) * ‖averageAlong R U j z i 0 c‖ := by nlinarith
    have := mul_le_mul_of_nonneg_left h6 (norm_nonneg dY)
    linarith
  have h7 : ‖dY‖ * (1 + 2 * ε) ≤ (P + 24 * ε * F.blockSide * M) * (1 + 2 * ε) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have hLM : 0 ≤ (F.blockSide : ℝ) * M := by positivity
  have e1 : (P + 24 * ε * F.blockSide * M) * (1 + 2 * ε) =
      P + 2 * ε * P + 24 * ε * (F.blockSide * M) * (1 + 2 * ε) := by ring
  have e2 : 2 * ε * P ≤ 2 * ε * (F.blockSide * M) := mul_le_mul_of_nonneg_left hP (by positivity)
  have e3 : 24 * ε * (F.blockSide * M) * (1 + 2 * ε) ≤ 24 * ε * (F.blockSide * M) * 2 :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e4 : 50 * ε * F.blockSide * M = 2 * ε * (F.blockSide * M) + 24 * ε * (F.blockSide * M) * 2 := by ring
  linarith
variable (W : F.GaugeField F.top)
def fitAlong (i : ℕ) (τ : ℝ) (c : F.Site (i + 1) × Fin 4) : ℝ :=
  gaugedBlockFit (chartChain R (scaledCurve U j z τ) W i) (chartGauge R (scaledCurve U j z τ) (i + 1))
    (chartChain R (scaledCurve U j z τ) W (i + 1)) c
theorem norm_sub_re_mul_inv_polarUnit {Y : ℍ[ℝ]} (hY : Y ≠ 0) (g : UnitQuaternion) :
    ‖Y‖ - (Y * (((g * polarUnit Y)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = ‖Y‖ * (1 - (g : ℍ[ℝ]).re) := by
  have hn : ‖Y‖ ≠ 0 := norm_ne_zero_iff.2 hY
  have e1 : (((g * polarUnit Y)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      star ((polarUnit Y : UnitQuaternion) : ℍ[ℝ]) * star (g : ℍ[ℝ]) := by
    rw [coe_unitQuaternion_inv, Submonoid.coe_mul, star_mul]
  have hs : ∀ r t : ℝ, r • (t : ℍ[ℝ]) = ((r * t : ℝ) : ℍ[ℝ]) := fun r t => by
    ext <;> simp
  have e2 : Y * star ((polarUnit Y : UnitQuaternion) : ℍ[ℝ]) = ((‖Y‖ : ℝ) : ℍ[ℝ]) := by
    rw [coe_polarUnit hY, quaternion_star_real_smul, mul_smul_comm, Quaternion.self_mul_star,
      Quaternion.normSq_eq_norm_mul_self, hs]
    congr 1
    field_simp
  rw [e1, ← mul_assoc, e2]
  have e3 : (((‖Y‖ : ℝ) : ℍ[ℝ]) * star (g : ℍ[ℝ])).re = ‖Y‖ * (g : ℍ[ℝ]).re := by
    simp
  rw [e3]
  ring
theorem fitAlong_eq {i : ℕ} (hi : i + 1 < F.top) (τ : ℝ) (c : F.Site (i + 1) × Fin 4)
    (hne : averageAlong R U j z i τ c ≠ 0) :
    fitAlong R U j z W i τ c = ‖averageAlong R U j z i τ c‖ *
      (1 - ((expUnit ((scaledCurve U j z τ).coarse i c.1 c.2) * referenceDefect R i c : UnitQuaternion) : ℍ[ℝ]).re) := by
  unfold fitAlong gaugedBlockFit
  rw [chartChain_of_lt R _ W (show i < F.top by omega), chartChain_of_lt R _ W hi]
  have e : chartField R (scaledCurve U j z τ) (i + 1) c.1 c.2 =
      expUnit ((scaledCurve U j z τ).coarse i c.1 c.2) * referenceDefect R i c *
        polarUnit (averageAlong R U j z i τ c) := rfl
  rw [e]
  exact norm_sub_re_mul_inv_polarUnit hne _
theorem differentiableAt_fitAlong (hodd : Odd F.blockSide) (hreg : ChartIsRegular S R U) {i : ℕ} (hi : i < F.top)
    {c : F.Site (i + 1) × Fin 4} (hc : c ∈ innerBonds S (i + 1)) :
    DifferentiableAt ℝ (fun τ => fitAlong R U j z W i τ c) 0 := by
  have hr : ChartIsRegular S R (scaledCurve U j z 0) := by rw [scaledCurve_zero]; exact hreg
  have hf := chartField_differentiableOn hodd R (C := scaledCurve U j z) (p₀ := (0 : ℝ))
    (fun b _ => differentiableAt_scaledCurve_fine U j z b)
    (fun i _ b _ => differentiableAt_scaledCurve_coarse U j z i b) hr
  unfold fitAlong
  simp only [chartChain_of_lt R _ W hi]
  unfold gaugedBlockFit chartGauge
  have hfr := differentiableAt_gaugedContourAverage hodd hi (R i) (hf i hi) hc
    ((hr i hi).1 _ (innerBonds_ends hc).1) ((hr i hi).1 _ (innerBonds_ends hc).2)
  refine (hfr.norm ℝ ((hr i hi).2 _ hc)).sub (differentiableAt_re (hfr.mul ?_))
  by_cases htop : i + 1 < F.top
  · simp only [chartChain_of_lt R _ W htop]
    exact differentiableAt_unitQuaternion_inv (hf (i + 1) htop _ _ (innerBonds_ends hc).1 (innerBonds_ends hc).2)
  · obtain rfl : i = F.depth := by
      have hn : F.top = F.depth + 1 := rfl
      omega
    simp only [chartChain_top R _ W]
    exact differentiableAt_const _
theorem sum_deriv_fitAlong_eq_zero (hodd : Odd F.blockSide) (hreg : ChartIsRegular S R U) {a : ℝ} (ha : a ≠ 0)
    (hcrit : IsStationaryAlong a S R W U (selfScaledDirection U j z)) :
    ∑ i ∈ Finset.range F.top, ∑ c ∈ innerBonds S (i + 1), deriv (fun τ => fitAlong R U j z W i τ c) 0 = 0 := by
  have h0 : 0 < F.top := Nat.succ_pos _
  have hfun : (fun τ : ℝ => chartAction a S R (chartMove U (selfScaledDirection U j z) τ) W) =
      fun τ => wilsonAction S (chartField R U 0) + a * ∑ i ∈ Finset.range F.top, ∑ c ∈ innerBonds S (i + 1),
        fitAlong R U j z W i τ c := by
    funext τ
    unfold chartAction gaugedChainAction
    rw [chartChain_of_lt R _ W h0]
    have := chartField_scaledCurve_of_le R U j z τ 0 (Nat.zero_le _)
    unfold scaledCurve at this
    rw [this]
    rfl
  have hd : HasDerivAt (fun τ => wilsonAction S (chartField R U 0) + a * ∑ i ∈ Finset.range F.top,
      ∑ c ∈ innerBonds S (i + 1), fitAlong R U j z W i τ c)
      (a * ∑ i ∈ Finset.range F.top, ∑ c ∈ innerBonds S (i + 1), deriv (fun τ => fitAlong R U j z W i τ c) 0) 0 := by
    refine HasDerivAt.const_add _ (HasDerivAt.const_mul a ?_)
    refine HasDerivAt.fun_sum fun i hi => HasDerivAt.fun_sum fun c hc => ?_
    exact (differentiableAt_fitAlong R U j z W hodd hreg (Finset.mem_range.1 hi) hc).hasDerivAt
  have hc : HasDerivAt (fun τ : ℝ => chartAction a S R (chartMove U (selfScaledDirection U j z) τ) W) 0 0 := hcrit
  rw [hfun] at hc
  have := hd.unique hc
  exact (mul_eq_zero.1 this).resolve_left ha
theorem deriv_fitAlong_of_lt {i : ℕ} (hi : i < j) (hj : j < F.top) (c : F.Site (i + 1) × Fin 4) :
    deriv (fun τ => fitAlong R U j z W i τ c) 0 = 0 := by
  have e : (fun τ => fitAlong R U j z W i τ c) = fun _ => fitAlong R U j z W i 0 c := by
    funext τ
    unfold fitAlong
    rw [chartChain_of_lt R _ W (show i < F.top by omega), chartChain_of_lt R _ W (show i + 1 < F.top by omega),
      chartChain_of_lt R _ W (show i < F.top by omega), chartChain_of_lt R _ W (show i + 1 < F.top by omega)]
    simp only [chartGauge]
    rw [chartField_scaledCurve_of_le R U j z τ i hi.le, chartField_scaledCurve_of_le R U j z τ (i + 1) hi,
      chartField_scaledCurve_of_le R U j z 0 i hi.le, chartField_scaledCurve_of_le R U j z 0 (i + 1) hi]
  rw [e]
  exact deriv_const _ _
theorem deriv_fitAlong_of_not_mem (hj : j + 1 < F.top) {c : F.Site (j + 1) × Fin 4} (hc : enclosingCell c.1 ≠ z) :
    deriv (fun τ => fitAlong R U j z W j τ c) 0 = 0 := by
  have e : (fun τ => fitAlong R U j z W j τ c) = fun _ => fitAlong R U j z W j 0 c := by
    funext τ
    unfold fitAlong gaugedBlockFit
    rw [chartChain_of_lt R _ W (show j < F.top by omega), chartChain_of_lt R _ W hj,
      chartChain_of_lt R _ W (show j < F.top by omega), chartChain_of_lt R _ W hj]
    simp only [chartGauge]
    rw [chartField_scaledCurve_of_le R U j z τ j le_rfl, chartField_scaledCurve_of_le R U j z 0 j le_rfl,
      chartField_scaledCurve_succ R U j z τ, chartField_scaledCurve_succ R U j z 0,
      scaledCurve_coarse_of_not_mem U j z τ hc, scaledCurve_coarse_of_not_mem U j z 0 hc]
  rw [e]
  exact deriv_const _ _
theorem blockMisfit_of_lt {i : ℕ} (hi : i + 1 < F.top) (c : F.Site (i + 1) × Fin 4) :
    chartBondMisfit R U W i c = expUnit (U.coarse i c.1 c.2) * referenceDefect R i c := by apply _root_.YangMills.Construction.SmallChartBounds.chartBondMisfit_of_lt_top <;> assumption
theorem one_sub_re_eq_distFromOne_sq (g : UnitQuaternion) : 1 - (g : ℍ[ℝ]).re = distFromOne g ^ 2 / 2 := by
  unfold distFromOne
  rw [norm_coe_sub_one_sq]
  ring
theorem abs_deriv_fitAlong_le (hodd : Odd F.blockSide) (hreg : ChartIsRegular S R U) {i : ℕ} (hji : j < i)
    (hi : i + 1 < F.top) {c : F.Site (i + 1) × Fin 4} (hc : c ∈ innerBonds S (i + 1)) {t ρ : ℝ} (v : UnitQuaternion)
    (ht0 : 0 ≤ t) (ht : 2 * F.blockSide * t ≤ 1 / 4) (hρ0 : 0 ≤ ρ) (hε : 17 * F.blockSide * t + ρ ≤ 1 / 2)
    (hcl : ∀ a ∈ FlatPairing.twoBlockHull F.blockSide c.2, ∀ k, a + basisVector k ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      distFromOne (chartField R U i (refineSite c.1 + siteOfCoords i a) k *
        (R i (refineSite c.1 + siteOfCoords i a) k)⁻¹) ≤ t)
    (hρ : ∀ h ∈ centredCube F.blockSide, ∀ π,
      distFromOne (pathHolonomy (R i) (refineSite c.1) (bondContour F.blockSide h π c.2) * v⁻¹) ≤ ρ) :
    |deriv (fun τ => fitAlong R U j z W i τ c) 0| ≤
      distFromOne (chartBondMisfit R U W i c) ^ 2 * (20 * (17 * F.blockSide * t + ρ) * F.blockSide * hullDerivSum R U j z i c) := by
  have hin : i < F.top := by omega
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  obtain ⟨dY, h1, -, h3, h4⟩ := exists_hasDerivAt_averageAlong R U j z hodd hreg hin hc v ht0 ht hρ0 hcl hρ
  set ε := 17 * (F.blockSide : ℝ) * t + ρ with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hnear := norm_gaugedContourAverage_sub_le hodd hin (chartField R U i) (R i) c (v : ℍ[ℝ]) h4
  rw [← averageAlong_zero R U j z] at hnear
  obtain ⟨hne, hlow, hunit⟩ := normalize_near (norm_coe_unitQuaternion v) hnear hε
  have hne' : ∀ᶠ τ in nhds (0 : ℝ), averageAlong R U j z i τ c ≠ 0 := h1.continuousAt.eventually_ne hne
  set E : UnitQuaternion := expUnit (U.coarse i c.1 c.2) * referenceDefect R i c with hE
  have hcur : HasDerivAt (fun τ => fitAlong R U j z W i τ c)
      ((inner ℝ (averageAlong R U j z i 0 c) dY / ‖averageAlong R U j z i 0 c‖) * (1 - (E : ℍ[ℝ]).re)) 0 := by
    refine ((hasDerivAt_norm_of_ne_zero h1 hne).mul_const _).congr_of_eventuallyEq ?_
    filter_upwards [hne'] with τ hτ
    rw [fitAlong_eq R U j z W hi τ c hτ, scaledCurve_coarse_of_ne U j z τ (by omega)]
  have hEq : E = chartBondMisfit R U W i c := (blockMisfit_of_lt R U W hi c).symm
  rw [hcur.deriv, abs_mul, one_sub_re_eq_distFromOne_sq,
    abs_of_nonneg (show 0 ≤ distFromOne E ^ 2 / 2 by positivity), hEq]
  set G := distFromOne (chartBondMisfit R U W i c)
  set Y0 := averageAlong R U j z i 0 c
  have hn0 : 0 < ‖Y0‖ := norm_pos_iff.2 hne
  have e1 : inner ℝ Y0 dY / ‖Y0‖ = inner ℝ (‖Y0‖⁻¹ • Y0) dY := by
    rw [inner_smul_left]
    simp only [conj_trivial]
    field_simp
  have hw : ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖‖Y0‖⁻¹ • Y0 - ((framedContour (chartField R U i) (R i) c h π : UnitQuaternion) : ℍ[ℝ])‖ ≤ 3 * ε := by
    intro h hh π
    have e2 : ‖Y0‖⁻¹ • Y0 - ((framedContour (chartField R U i) (R i) c h π : UnitQuaternion) : ℍ[ℝ]) =
        (‖Y0‖⁻¹ • Y0 - (v : ℍ[ℝ])) -
          (((framedContour (chartField R U i) (R i) c h π : UnitQuaternion) : ℍ[ℝ]) - (v : ℍ[ℝ])) := by abel
    rw [e2]
    refine (norm_sub_le _ _).trans ?_
    have := h4 h hh π
    linarith
  have h5 := h3 _ _ hw
  rw [e1]
  have hM := hullDerivSum_nonneg R U j z i c
  have hG : 0 ≤ G ^ 2 := by positivity
  have h6 : 3 * ε * (13 * F.blockSide * hullDerivSum R U j z i c) ≤
      2 * (20 * ε * F.blockSide * hullDerivSum R U j z i c) := by
    have : 0 ≤ ε * F.blockSide * hullDerivSum R U j z i c := by positivity
    nlinarith
  have h7 := mul_le_mul_of_nonneg_right (h5.trans h6) (by positivity : (0 : ℝ) ≤ G ^ 2 / 2)
  refine h7.trans (le_of_eq ?_)
  ring
theorem abs_deriv_fitAlong_depth_le (hodd : Odd F.blockSide) (hreg : ChartIsRegular S R U)
    {c : F.Site (F.depth + 1) × Fin 4} (hc : c ∈ innerBonds S (F.depth + 1))
    {t ρ : ℝ} (v : UnitQuaternion) (ht0 : 0 ≤ t) (ht : 2 * F.blockSide * t ≤ 1 / 4) (hρ0 : 0 ≤ ρ)
    (hε : 17 * F.blockSide * t + ρ ≤ 1 / 2)
    (hcl : ∀ a ∈ FlatPairing.twoBlockHull F.blockSide c.2, ∀ k, a + basisVector k ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      distFromOne (chartField R U F.depth (refineSite c.1 + siteOfCoords F.depth a) k *
        (R F.depth (refineSite c.1 + siteOfCoords F.depth a) k)⁻¹) ≤ t)
    (hρ : ∀ h ∈ centredCube F.blockSide, ∀ π,
      distFromOne (pathHolonomy (R F.depth) (refineSite c.1) (bondContour F.blockSide h π c.2) * v⁻¹) ≤ ρ) :
    |deriv (fun τ => fitAlong R U j z W F.depth τ c) 0| ≤
      distFromOne (chartBondMisfit R U W F.depth c) * (13 * F.blockSide * hullDerivSum R U j z F.depth c) := by
  have hin : F.depth < F.top := Nat.lt_succ_self _
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  obtain ⟨dY, h1, h2, -, h4⟩ := exists_hasDerivAt_averageAlong R U j z hodd hreg hin hc v ht0 ht hρ0 hcl hρ
  set ε := 17 * (F.blockSide : ℝ) * t + ρ with hεdef
  have hnear := norm_gaugedContourAverage_sub_le hodd hin (chartField R U F.depth) (R F.depth) c (v : ℍ[ℝ]) h4
  rw [← averageAlong_zero R U j z] at hnear
  obtain ⟨hne, hlow, -⟩ := normalize_near (norm_coe_unitQuaternion v) hnear hε
  set Wc : UnitQuaternion := W c.1 c.2 with hWc
  have hfit : ∀ τ, fitAlong R U j z W F.depth τ c =
      ‖averageAlong R U j z F.depth τ c‖ - (averageAlong R U j z F.depth τ c * (((Wc)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := by
    intro τ
    unfold fitAlong gaugedBlockFit
    rw [chartChain_of_lt R _ W hin]
    have e : chartChain R (scaledCurve U j z τ) W (F.depth + 1) = W := chartChain_top R _ W
    rw [e]
    rfl
  have hcur : HasDerivAt (fun τ => fitAlong R U j z W F.depth τ c)
      (inner ℝ (averageAlong R U j z F.depth 0 c) dY / ‖averageAlong R U j z F.depth 0 c‖ -
        (dY * (((Wc)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) 0 := by
    simp only [hfit]
    exact (hasDerivAt_norm_of_ne_zero h1 hne).sub
      (reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (h1.mul_const _))
  rw [hcur.deriv]
  set Y0 := averageAlong R U j z F.depth 0 c with hY0
  have e1 : inner ℝ Y0 dY / ‖Y0‖ = (dY * star (‖Y0‖⁻¹ • Y0)).re := by
    rw [← inner_eq_re_mul_star, inner_smul_left]
    simp only [conj_trivial]
    field_simp
  have e2 : (dY * star (‖Y0‖⁻¹ • Y0)).re - (dY * (((Wc)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re =
      (dY * star (‖Y0‖⁻¹ • Y0 - (Wc : ℍ[ℝ]))).re := by
    rw [star_sub, mul_sub, coe_unitQuaternion_inv]
    simp
  rw [e1, e2]
  refine (abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_star]
  have hG : ‖‖Y0‖⁻¹ • Y0 - (Wc : ℍ[ℝ])‖ = distFromOne (chartBondMisfit R U W F.depth c) := by
    have e3 : chartBondMisfit R U W F.depth c = Wc * (polarUnit Y0)⁻¹ := by
      unfold chartBondMisfit
      have e : chartChain R U W (F.depth + 1) = W := chartChain_top R _ W
      rw [e, chartChain_of_lt R U W hin, hY0, averageAlong_zero]
      rfl
    rw [e3, ← norm_coe_sub_coe_eq_distFromOne, norm_sub_rev, coe_polarUnit hne]
  rw [hG, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hP := lineBlockAverage_le_hullDerivSum R U j z hodd (i := F.depth) c
  have hM := hullDerivSum_nonneg R U j z F.depth c
  have hLM : 0 ≤ (F.blockSide : ℝ) * hullDerivSum R U j z F.depth c := by positivity
  have h5 : 24 * ε * F.blockSide * hullDerivSum R U j z F.depth c ≤
      12 * (F.blockSide * hullDerivSum R U j z F.depth c) := by
    have := mul_le_mul_of_nonneg_right hε hLM
    nlinarith
  linarith
theorem hasDerivAt_expUnit_scaled (w : imaginaryQuaternions) (κ : ℝ) :
    HasDerivAt (fun τ : ℝ => ((expUnit ((1 + τ * κ) • w) : UnitQuaternion) : ℍ[ℝ]))
      (κ • (((expUnit w : UnitQuaternion) : ℍ[ℝ]) * (w : ℍ[ℝ]))) 0 := by
  have h1 : HasDerivAt (fun τ : ℝ => 1 + τ * κ) κ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const κ).const_add 1
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (w : ℍ[ℝ]) (1 : ℝ)
  have h3 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (w : ℍ[ℝ])))
      (((expUnit w : UnitQuaternion) : ℍ[ℝ]) * (w : ℍ[ℝ])) ((fun τ : ℝ => 1 + τ * κ) 0) := by
    have e : (fun τ : ℝ => 1 + τ * κ) 0 = 1 := by simp
    rw [e]
    have e2 : NormedSpace.exp ((1 : ℝ) • (w : ℍ[ℝ])) = ((expUnit w : UnitQuaternion) : ℍ[ℝ]) := by
      rw [one_smul]
      rfl
    rw [← e2]
    exact h2
  exact h3.scomp (0 : ℝ) h1
theorem re_expUnit_mul_le (w : imaginaryQuaternions) (hw : ‖(w : ℍ[ℝ])‖ ≤ 1) :
    (((expUnit w : UnitQuaternion) : ℍ[ℝ]) * (w : ℍ[ℝ])).re ≤ - (3 / 4) * ‖(w : ℍ[ℝ])‖ ^ 2 := by
  have hre : (w : ℍ[ℝ]).re = 0 := w.2
  have e0 : ((expUnit w : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (w : ℍ[ℝ]) := rfl
  rw [e0, exp_eq_of_re_eq_zero hre, add_mul, smul_mul_assoc]
  have e1 : (w : ℍ[ℝ]) * (w : ℍ[ℝ]) = - ((‖(w : ℍ[ℝ])‖ * ‖(w : ℍ[ℝ])‖ : ℝ) : ℍ[ℝ]) := by
    have h1 := Quaternion.star_mul_self (w : ℍ[ℝ])
    rw [star_eq_neg_of_re_eq_zero hre, Quaternion.normSq_eq_norm_mul_self] at h1
    rw [neg_mul] at h1
    rw [← h1, neg_neg]
  rw [e1]
  set x := ‖(w : ℍ[ℝ])‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  have e2 : (((Real.cos x : ℝ) : ℍ[ℝ]) * (w : ℍ[ℝ]) + (Real.sin x / x) • (- ((x * x : ℝ) : ℍ[ℝ]))).re =
      - ((Real.sin x / x) * (x * x)) := by
    simp [hre]
  rw [e2]
  rcases hx0.eq_or_lt with h0 | hp
  · rw [← h0]
    simp
  · have hs := Real.sin_gt_sub_cube hp
    have e3 : Real.sin x / x * (x * x) = Real.sin x * x := by
      field_simp
    rw [e3]
    have h4 : x ^ 3 ≤ x := by
      have : x ^ 2 ≤ 1 := pow_le_one₀ hx0 hw
      nlinarith
    nlinarith
theorem linkDerivNorm_of_mem {c : F.Site (j + 1) × Fin 4} (hcz : enclosingCell c.1 = z) :
    linkDerivNorm R U j z (j + 1) c.1 c.2 = ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 3 := by
  set w := U.coarse j c.1 c.2 with hw
  set κ := ‖(w : ℍ[ℝ])‖ ^ 2 with hκ
  set Q : UnitQuaternion := referenceDefect R j (c.1, c.2) *
    polarUnit (gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) (c.1, c.2)) with hQ
  have h1 : HasDerivAt (fun τ : ℝ => ((chartField R (scaledCurve U j z τ) (j + 1) c.1 c.2 : UnitQuaternion) : ℍ[ℝ]))
      ((κ • (((expUnit w : UnitQuaternion) : ℍ[ℝ]) * (w : ℍ[ℝ]))) * (Q : ℍ[ℝ])) 0 := by
    have e : (fun τ : ℝ => ((chartField R (scaledCurve U j z τ) (j + 1) c.1 c.2 : UnitQuaternion) : ℍ[ℝ])) =
        fun τ : ℝ => ((expUnit ((1 + τ * κ) • w) : UnitQuaternion) : ℍ[ℝ]) * (Q : ℍ[ℝ]) := by
      funext τ
      rw [chartField_scaledCurve_succ R U j z τ, scaledCurve_coarse_of_mem U j z τ hcz, mul_assoc]
      rfl
    rw [e]
    exact (hasDerivAt_expUnit_scaled w κ).mul_const _
  unfold linkDerivNorm linkDeriv
  rw [h1.deriv, norm_mul, norm_smul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, mul_one,
    Real.norm_of_nonneg (by positivity)]
  ring
theorem linkDerivNorm_of_not_mem {c : F.Site (j + 1) × Fin 4} (hcz : enclosingCell c.1 ≠ z) :
    linkDerivNorm R U j z (j + 1) c.1 c.2 = 0 := by
  unfold linkDerivNorm linkDeriv
  have e : (fun τ : ℝ => ((chartField R (scaledCurve U j z τ) (j + 1) c.1 c.2 : UnitQuaternion) : ℍ[ℝ])) =
      fun _ => ((chartField R (scaledCurve U j z 0) (j + 1) c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) := by
    funext τ
    rw [chartField_scaledCurve_succ R U j z τ, chartField_scaledCurve_succ R U j z 0,
      scaledCurve_coarse_of_not_mem U j z τ hcz, scaledCurve_coarse_of_not_mem U j z 0 hcz]
  rw [e, deriv_const, norm_zero]
theorem deriv_fitAlong_ge (hj : j + 1 < F.top) {c : F.Site (j + 1) × Fin 4} (hcz : enclosingCell c.1 = z)
    (hw : ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ≤ 1)
    (hr : 1 / 2 ≤ ‖gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) c‖)
    (hr1 : ‖gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) c‖ ≤ 1) :
    3 / 8 * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 4 -
        ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 3 * distFromOne (referenceDefect R j c) ≤
      deriv (fun τ => fitAlong R U j z W j τ c) 0 := by
  set w := U.coarse j c.1 c.2 with hwdef
  set x := ‖(w : ℍ[ℝ])‖ with hx
  set κ := x ^ 2 with hκ
  set Y := gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) c with hY
  set r := ‖Y‖ with hrdef
  set m : UnitQuaternion := referenceDefect R j c with hm
  have hYne : Y ≠ 0 := by
    intro h0
    rw [hrdef, h0, norm_zero] at hr
    linarith
  have hmean : ∀ τ, averageAlong R U j z j τ c = Y := by
    intro τ
    simp only [averageAlong]
    rw [chartField_scaledCurve_of_le R U j z τ j le_rfl]
  have hform : ∀ τ : ℝ, fitAlong R U j z W j τ c =
      r * (1 - (((expUnit ((1 + τ * κ) • w) : UnitQuaternion) : ℍ[ℝ]) * (m : ℍ[ℝ])).re) := by
    intro τ
    rw [fitAlong_eq R U j z W hj τ c (by rw [hmean]; exact hYne), hmean, scaledCurve_coarse_of_mem U j z τ hcz]
    rfl
  have hcur : HasDerivAt (fun τ => fitAlong R U j z W j τ c)
      (r * (-((κ • (((expUnit w : UnitQuaternion) : ℍ[ℝ]) * (w : ℍ[ℝ]))) * (m : ℍ[ℝ])).re)) 0 := by
    simp only [hform]
    have h1 := reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_expUnit_scaled w κ).mul_const (m : ℍ[ℝ]))
    exact ((h1.const_sub 1).const_mul r)
  rw [hcur.deriv]
  have e1 : ((κ • (((expUnit w : UnitQuaternion) : ℍ[ℝ]) * (w : ℍ[ℝ]))) * (m : ℍ[ℝ])).re =
      κ * ((((expUnit w : UnitQuaternion) : ℍ[ℝ]) * (w : ℍ[ℝ])).re +
        ((((expUnit w : UnitQuaternion) : ℍ[ℝ]) * (w : ℍ[ℝ])) * ((m : ℍ[ℝ]) - 1)).re) := by
    rw [smul_mul_assoc, mul_sub, mul_one]
    simp
  rw [e1]
  have h2 := re_expUnit_mul_le w hw
  have h3 : ((((expUnit w : UnitQuaternion) : ℍ[ℝ]) * (w : ℍ[ℝ])) * ((m : ℍ[ℝ]) - 1)).re ≤ x * distFromOne m := by
    refine (quaternion_re_le_norm _).trans ?_
    rw [norm_mul, norm_mul, norm_coe_unitQuaternion, one_mul]
    rfl
  set δ := distFromOne m with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hκ0 : 0 ≤ κ := by positivity
  have h4 : κ * ((((expUnit w : UnitQuaternion) : ℍ[ℝ]) * (w : ℍ[ℝ])).re +
      ((((expUnit w : UnitQuaternion) : ℍ[ℝ]) * (w : ℍ[ℝ])) * ((m : ℍ[ℝ]) - 1)).re) ≤
      κ * (-(3 / 4) * x ^ 2 + x * δ) := mul_le_mul_of_nonneg_left (add_le_add h2 h3) hκ0
  have hr0 : 0 ≤ r := by linarith
  have h5 : r * (κ * (-(3 / 4) * x ^ 2 + x * δ)) ≥ r * (κ * ((((expUnit w : UnitQuaternion) : ℍ[ℝ]) * (w : ℍ[ℝ])).re +
      ((((expUnit w : UnitQuaternion) : ℍ[ℝ]) * (w : ℍ[ℝ])) * ((m : ℍ[ℝ]) - 1)).re)) :=
    mul_le_mul_of_nonneg_left h4 hr0
  have h6 : 0 ≤ x ^ 4 := by positivity
  have h7 : 0 ≤ x ^ 3 * δ := by positivity
  have h8 : (1 / 2) * x ^ 4 ≤ r * x ^ 4 := mul_le_mul_of_nonneg_right hr h6
  have h9 : r * (x ^ 3 * δ) ≤ 1 * (x ^ 3 * δ) := mul_le_mul_of_nonneg_right hr1 h7
  nlinarith
end Curve
end YangMills.Construction.MisfitVariation
end

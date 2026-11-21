import YangMills.Construction.ColdChainAtEveryLevel.VariationsAlongAMisfit
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.MisfitSums
open BlockAverages LatticePaths BondHull BondVariation MisfitVariation NearCellNorms FlatPairing
  LatticeFractionalIntegration FiniteDifferences
variable {F : BlockFrame}
theorem card_cellBall_five (S : Finset F.Cell) (z : F.Cell) : (cellBall S z 5).card ≤ 14641 := by
  classical
  have hc : (centredCube 11).card = 14641 := by
    rw [card_centredCube (by decide : Odd 11)]
    norm_num
  rw [← hc]
  apply Finset.card_le_card_of_injOn (fun y k => ((z - y : F.Cell) k).valMinAbs)
  · intro y hy
    have hy' : cellSupDist z y ≤ 5 := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
    refine Finset.mem_coe.2 ((mem_centredCube_iff _ _).2 fun k => ?_)
    have h1 : (((z - y : F.Cell) k).valMinAbs).natAbs ≤ cellSupDist z y :=
      Finset.le_sup (f := fun k => (((z - y : F.Cell) k).valMinAbs).natAbs) (Finset.mem_univ k)
    simp only [Pi.sub_apply] at h1 ⊢
    norm_num
    omega
  · intro y _ y' _ e
    funext k
    have h1 := congrFun e k
    have h2 : (z - y : F.Cell) k = (z - y' : F.Cell) k := ZMod.injective_valMinAbs h1
    have h3 : z k - y k = z k - y' k := h2
    exact sub_right_injective h3
theorem cellSupDist_enclosingCell_le_of_baseDistance (hodd : Odd F.blockSide) {S : Finset F.Cell} {i : ℕ}
    (hi : i ≤ F.top) {x : F.Site i} (hx : x ∈ sitesOfCells S i) (p : F.Site 0) (B : ℕ)
    (hd : baseDistance x p + F.blockSide ^ F.top ≤ B * F.blockSide ^ F.top) :
    cellSupDist (enclosingCell x) (enclosingCell p) ≤ B := by
  obtain ⟨z, hz, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
  rw [BlockLines.enclosingCell_cellCentre_add hodd z h hh, BlockLines.cellSupDist_comm]
  refine PatchPoints.cellSupDist_enclosingCell_le hodd p z B fun k => ?_
  have hb : baseSite (cellCentre i z + siteOfCoords i h) =
      cellCentre 0 z + siteOfCoords 0 (fun k => (F.blockSide : ℤ) ^ i * h k) := by
    rw [baseSite_add i hi, baseSite_cellCentre i hi]
  set x := cellCentre i z + siteOfCoords i h with hxdef
  have hdi : (((baseSite x - p : F.Site 0) k).valMinAbs).natAbs ≤ baseDistance x p :=
    Finset.le_sup (f := fun k => (((baseSite x - p : F.Site 0) k).valMinAbs).natAbs) (Finset.mem_univ k)
  have e : ((p - cellCentre 0 z : F.Site 0) k) = -((baseSite x - p : F.Site 0) k) +
      (siteOfCoords (F := F) 0 (fun k => (F.blockSide : ℤ) ^ i * h k)) k := by
    rw [hb]
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [e]
  refine (BlockWeights.natAbs_valMinAbs_add_le_add _ _).trans ?_
  rw [ZMod.natAbs_valMinAbs_neg]
  have hc := (mem_centredCube_iff _ _).1 hh k
  obtain ⟨K, hK1, hK2, hK3⟩ := BlockLines.odd_pow_eq_two_mul_add_one hodd (F.top - i)
  rw [hK2] at hc
  have h2 : (((siteOfCoords (F := F) 0 (fun k => (F.blockSide : ℤ) ^ i * h k)) k).valMinAbs).natAbs ≤
      F.blockSide ^ i * K := by
    refine (BlockWeights.natAbs_valMinAbs_intCast_le _).trans ?_
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    refine Nat.mul_le_mul_left _ ?_
    omega
  have h3 : F.blockSide ^ i * K ≤ F.blockSide ^ F.top := by
    have : F.blockSide ^ F.top = F.blockSide ^ i * F.blockSide ^ (F.top - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [this, hK1]
    nlinarith [Nat.zero_le (F.blockSide ^ i)]
  omega
theorem baseDistance_cellCentre_le (hodd : Odd F.blockSide) {S : Finset F.Cell} {i : ℕ} (hi : i ≤ F.top)
    {x : F.Site i} (hx : x ∈ sitesOfCells S i) {z : F.Cell} (hc : enclosingCell x = z) :
    baseDistance x (cellCentre 0 z) ≤ F.blockSide ^ F.top := by
  obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
  rw [BlockLines.enclosingCell_cellCentre_add hodd y h hh] at hc
  subst hc
  unfold baseDistance
  refine Finset.sup_le fun k _ => ?_
  rw [baseSite_add i hi, baseSite_cellCentre i hi, add_sub_cancel_left]
  have hcube := (mem_centredCube_iff _ _).1 hh k
  obtain ⟨K, hK1, hK2, hK3⟩ := BlockLines.odd_pow_eq_two_mul_add_one hodd (F.top - i)
  rw [hK2] at hcube
  refine (BlockWeights.natAbs_valMinAbs_intCast_le _).trans ?_
  rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  have h3 : F.blockSide ^ i * (h k).natAbs ≤ F.blockSide ^ i * F.blockSide ^ (F.top - i) := by
    refine Nat.mul_le_mul_left _ ?_
    omega
  refine h3.trans (le_of_eq ?_)
  rw [← pow_add]
  congr 1
  omega
theorem natAbs_neg_le_of_mem_twoBlockHull {L : ℕ} {a : Lattice4} {i : Fin 4} (ha : a ∈ twoBlockHull L i)
    (hL : 1 ≤ L) (k : Fin 4) : ((-a) k).natAbs ≤ 2 * L := by
  have h := ha k
  have h2 : (if k = i then (L : ℤ) else 0) ≤ L := by split_ifs <;> omega
  simp only [Pi.neg_apply]
  omega
theorem baseDistance_le_of_mem_twoBlockHull (hL : 1 ≤ F.blockSide) {i : ℕ} (hi : i < F.top)
    {c : F.Site (i + 1) × Fin 4} {a : Lattice4} (ha : a ∈ twoBlockHull F.blockSide c.2) (o : F.Site 0) :
    baseDistance c.1 o ≤ baseDistance (refineSite c.1 + siteOfCoords i a) o + 2 * F.blockSide ^ (i + 1) := by
  have h1 := BlockWeights.baseDistance_add_le hi.le (refineSite c.1 + siteOfCoords i a) (-a) o (2 * F.blockSide)
    (natAbs_neg_le_of_mem_twoBlockHull ha hL)
  have e : refineSite c.1 + siteOfCoords i a + siteOfCoords i (-a) = refineSite c.1 := by
    rw [add_assoc, ← siteOfCoords_add, add_neg_cancel, siteOfCoords_zero, add_zero]
  rw [e, BlockWeights.baseDistance_refineSite hi] at h1
  refine h1.trans (le_of_eq ?_)
  rw [pow_succ]
  ring
section Fixed
variable (R : F.FieldChain) (U : ChainChart F) (j : ℕ) (z : F.Cell) {S : Finset F.Cell} {i : ℕ}
theorem chartField_scaledCurve_of_far (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide) :
    ∀ i, j + 1 ≤ i → i < F.top → ∀ b ∈ innerBonds S i,
    F.blockSide ^ F.top + 4 * F.blockSide ^ i < baseDistance b.1 (cellCentre 0 z) → ∀ τ,
      chartField R (scaledCurve U j z τ) i b.1 b.2 = chartField R U i b.1 b.2 := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro _ b hb hfar τ
    have hcell : enclosingCell b.1 ≠ z := by
      intro h
      have := baseDistance_cellCentre_le hodd (by omega) (BlockAverages.ChartCoordinates.innerBonds_ends hb).1 h
      omega
    rw [chartField_scaledCurve_succ R U j z τ, scaledCurve_coarse_of_not_mem U j z τ hcell]
    rfl
  | succ i hi ih =>
    intro hin c hc hfar τ
    have hin' : i < F.top := by omega
    have hji : j < i := by omega
    rw [chartField_scaledCurve_of_lt R U j z τ hji]
    have hmean : gaugedContourAverage (chartField R (scaledCurve U j z τ) i)
        (balancingGauge (chartField R (scaledCurve U j z τ) i) (R i)) (c.1, c.2) =
        gaugedContourAverage (chartField R U i) (balancingGauge (chartField R U i) (R i)) (c.1, c.2) := by
      refine gaugedContourAverage_congr hodd hin' (R i) (c.1, c.2) fun a ha k hk => ?_
      have hb := BlockLines.bond_mem_innerBonds_of_mem_twoBlockHull hin' hodd c hc a k ha hk
      refine ih hin' _ hb ?_ τ
      have h1 := baseDistance_le_of_mem_twoBlockHull (by omega) hin' ha (cellCentre 0 z) (c := c)
      have h2 : F.blockSide ^ (i + 1) = F.blockSide ^ i * F.blockSide := pow_succ _ _
      have h3 : 2 * F.blockSide ^ i ≤ F.blockSide ^ (i + 1) := by
        rw [h2]
        nlinarith [Nat.zero_le (F.blockSide ^ i)]
      simp only at h1 ⊢
      omega
    rw [hmean]
    rfl
theorem linkDerivNorm_eq_zero_of_far (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide) (hi : j + 1 ≤ i)
    (hin : i < F.top) {b : F.Site i × Fin 4} (hb : b ∈ innerBonds S i)
    (hfar : F.blockSide ^ F.top + 4 * F.blockSide ^ i < baseDistance b.1 (cellCentre 0 z)) :
    linkDerivNorm R U j z i b.1 b.2 = 0 := by
  unfold linkDerivNorm linkDeriv
  have e : (fun τ : ℝ => ((chartField R (scaledCurve U j z τ) i b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) =
      fun _ => ((chartField R U i b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) := by
    funext τ
    rw [chartField_scaledCurve_of_far R U j z hodd hL i hi hin b hb hfar τ]
  rw [e, deriv_const, norm_zero]
theorem hullDerivSum_eq_zero_of_not_mem (hodd : Odd F.blockSide) (hL : 4 ≤ F.blockSide) (hi : j + 1 ≤ i)
    (hin : i < F.top) {c : F.Site (i + 1) × Fin 4} (hc : c ∈ innerBonds S (i + 1))
    (hcell : enclosingCell c.1 ∉ cellBall S z 5) : hullDerivSum R U j z i c = 0 := by
  classical
  have hL1 : 1 ≤ F.blockSide := by omega
  have hLn : F.blockSide ^ (i + 1) ≤ F.blockSide ^ F.top := Nat.pow_le_pow_right (by omega) hin
  have h4 : 4 * F.blockSide ^ i ≤ F.blockSide ^ (i + 1) := by
    rw [pow_succ]
    nlinarith [Nat.zero_le (F.blockSide ^ i)]
  have hcz : enclosingCell (F := F) (cellCentre 0 z) = z := by
    have := PatchPoints.enclosingCell_cellCentre_add (F := F) (j := 0) hodd z 0
      ((mem_centredCube_iff _ _).2 fun k => by
        have : (0 : ℤ) ≤ (((F.blockSide ^ (F.top - 0) : ℕ) : ℤ) - 1) / 2 := by
          have : 1 ≤ F.blockSide ^ (F.top - 0) := Nat.one_le_pow _ _ hodd.pos
          omega
        simp only [Pi.zero_apply]
        omega)
    rwa [siteOfCoords_zero, add_zero] at this
  have hfar : F.blockSide ^ F.top + 4 * F.blockSide ^ i + 2 * F.blockSide ^ (i + 1) <
      baseDistance c.1 (cellCentre 0 z) := by
    by_contra hnot
    apply hcell
    refine Finset.mem_filter.2
      ⟨BlockLines.enclosingCell_mem hodd (BlockAverages.ChartCoordinates.innerBonds_ends hc).1, ?_⟩
    have h1 := cellSupDist_enclosingCell_le_of_baseDistance hodd (by omega)
      (BlockAverages.ChartCoordinates.innerBonds_ends hc).1 (cellCentre 0 z) 5 (by omega)
    rw [hcz, BlockLines.cellSupDist_comm] at h1
    exact h1
  unfold hullDerivSum BlockLines.hullSum
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun k _ => ?_
  split_ifs with hh
  · have hb := BlockLines.bond_mem_innerBonds_of_mem_twoBlockHull (by omega) hodd c hc a k hh.1 hh.2
    refine linkDerivNorm_eq_zero_of_far R U j z hodd (by omega) hi hin hb ?_
    have h1 := baseDistance_le_of_mem_twoBlockHull hL1 hin hh.1 (cellCentre 0 z) (c := c)
    simp only at h1 ⊢
    omega
  · rfl
structure NearReference (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (t ρ : ℝ) : Prop where
  linkDist_le : ∀ i, i < F.top → ∀ b ∈ innerBonds S i,
    distFromOne (chartField R U i b.1 b.2 * (R i b.1 b.2)⁻¹) ≤ t
  contour_near : ∀ i, i < F.top → ∀ c ∈ innerBonds S (i + 1), ∃ v : UnitQuaternion,
    ∀ h ∈ centredCube F.blockSide, ∀ π,
    distFromOne (pathHolonomy (R i) (refineSite c.1) (bondContour F.blockSide h π c.2) * v⁻¹) ≤ ρ
variable {R U} {t ρ : ℝ}
theorem NearReference.hull_le (hs : NearReference S R U t ρ) (hodd : Odd F.blockSide) (hi : i < F.top)
    {c : F.Site (i + 1) × Fin 4} (hc : c ∈ innerBonds S (i + 1)) :
    ∀ a ∈ twoBlockHull F.blockSide c.2, ∀ k, a + basisVector k ∈ twoBlockHull F.blockSide c.2 →
    distFromOne (chartField R U i (refineSite c.1 + siteOfCoords i a) k *
      (R i (refineSite c.1 + siteOfCoords i a) k)⁻¹) ≤ t :=
  fun a ha k hk => hs.linkDist_le i hi (refineSite c.1 + siteOfCoords i a, k)
    (BlockLines.bond_mem_innerBonds_of_mem_twoBlockHull hi hodd c hc a k ha hk)
theorem NearReference.chartIsRegular (hs : NearReference S R U t ρ) (hodd : Odd F.blockSide) (ht0 : 0 ≤ t)
    (ht : 2 * F.blockSide * t ≤ 1 / 4) (hρ0 : 0 ≤ ρ) (hε : 17 * F.blockSide * t + ρ ≤ 1 / 2) :
    ChartIsRegular S R U := by
  intro i hi
  refine ⟨fun y hy => ?_, fun c hc => ?_⟩
  · have hcl : ∀ a ∈ centredCube F.blockSide, ∀ k, a + basisVector k ∈ centredCube F.blockSide →
        distFromOne (chartField R U i (refineSite y + siteOfCoords i a) k *
          (R i (refineSite y + siteOfCoords i a) k)⁻¹) ≤ t := by
      intro a ha k hk
      refine hs.linkDist_le i hi (refineSite y + siteOfCoords i a, k)
        (BlockAverages.ChartCoordinates.mem_innerBonds
          (BlockAverages.ChartCoordinates.refineSite_add_mem_sitesOfCells hodd hi hy ha) ?_)
      have := BlockAverages.ChartCoordinates.refineSite_add_mem_sitesOfCells hodd hi hy hk
      rw [siteOfCoords_add, ← add_assoc, ← unitStep_eq] at this
      exact this
    have h1 := norm_relativePathAverage_sub_one_le hodd (chartField R U i) (R i) y t ht0 hcl
    intro h0
    rw [h0, zero_sub, norm_neg, norm_one] at h1
    linarith
  · obtain ⟨v, hv⟩ := hs.contour_near i hi c hc
    obtain ⟨-, -, -, -, f5⟩ :=
      bond_estimates_of_near hodd hi (chartField R U i) (R i) c v ht0 ht (hs.hull_le hodd hi hc) hv
    exact (normalize_near (norm_coe_unitQuaternion v)
      (norm_gaugedContourAverage_sub_le hodd hi (chartField R U i) (R i) c (v : ℍ[ℝ]) f5) hε).1
variable (R U)
def levelDerivNorm (S : Finset F.Cell) (i : ℕ) : ℝ :=
  finLpNorm (innerBonds S i) (4 / 3) (fun b => linkDerivNorm R U j z i b.1 b.2)
theorem levelDerivNorm_nonneg (i : ℕ) : 0 ≤ levelDerivNorm R U j z S i :=
  finLpNorm_nonneg _ _ fun _ _ => linkDerivNorm_nonneg _ _ _ _ _ _ _
def hullLpConst (L : ℕ) : ℝ :=
  ((((4 * (BlockLines.hullBox L).card : ℕ) : ℝ) ^ ((4 / 3 : ℝ) - 1) *
    (16 * ((BlockLines.hullBox L).card : ℝ))) ^ (1 / (4 / 3 : ℝ)))
theorem hullLpConst_nonneg (L : ℕ) : 0 ≤ hullLpConst L := by
  unfold hullLpConst
  positivity
theorem hullSum_rpow_le (g : F.Site i × Fin 4 → ℝ) (hg : ∀ b, 0 ≤ g b) (c : F.Site (i + 1) × Fin 4) :
    BlockLines.hullSum g c ^ (4 / 3 : ℝ) ≤
      ((4 * (BlockLines.hullBox F.blockSide).card : ℕ) : ℝ) ^ ((4 / 3 : ℝ) - 1) *
      BlockLines.hullSum (fun b => g b ^ (4 / 3 : ℝ)) c := by
  classical
  set V := BlockLines.hullBox F.blockSide ×ˢ (Finset.univ : Finset (Fin 4)) with hV
  set x : Lattice4 × Fin 4 → ℝ := fun v =>
    if v.1 ∈ twoBlockHull F.blockSide c.2 ∧ v.1 + basisVector v.2 ∈ twoBlockHull F.blockSide c.2 then
    g (refineSite c.1 + siteOfCoords i v.1, v.2) else 0 with hx
  have hx0 : ∀ v, 0 ≤ x v := fun v => by
    simp only [hx]
    split_ifs
    · exact hg _
    · exact le_rfl
  have e1 : BlockLines.hullSum g c = ∑ v ∈ V, x v := by
    unfold BlockLines.hullSum
    rw [hV, Finset.sum_product]
  have e2 : BlockLines.hullSum (fun b => g b ^ (4 / 3 : ℝ)) c = ∑ v ∈ V, x v ^ (4 / 3 : ℝ) := by
    unfold BlockLines.hullSum
    rw [hV, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [hx]
    split_ifs
    · rfl
    · rw [Real.zero_rpow (by norm_num)]
  have h3 := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg V (f := x) (by norm_num : (1 : ℝ) ≤ 4 / 3)
    (fun v _ => hx0 v)
  have hcard : (V.card : ℝ) = ((4 * (BlockLines.hullBox F.blockSide).card : ℕ) : ℝ) := by
    rw [hV, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    push_cast
    ring
  rw [e1, e2, ← hcard]
  exact h3
end Fixed
end YangMills.Construction.MisfitSums
end

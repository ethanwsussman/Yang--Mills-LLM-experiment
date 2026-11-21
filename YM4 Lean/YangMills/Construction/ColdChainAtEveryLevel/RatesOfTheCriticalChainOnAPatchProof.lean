import YangMills.Construction.ColdChainAtEveryLevel.MorreyOfTheCriticalChainOnAPatchProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace PatchRates
open LatticePaths BlockLines PatchLocality BondHull
variable {F : BlockFrame}
theorem sum_biUnion_le_sum_sum {ι α : Type} (s : Finset ι) (t : ι → Finset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    [DecidableEq α] : ∑ a ∈ s.biUnion t, f a ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have h1 : ∑ a ∈ t i ∪ s.biUnion t, f a ≤ ∑ a ∈ t i, f a + ∑ a ∈ s.biUnion t, f a := by
      rw [← Finset.sum_union_inter]
      have : 0 ≤ ∑ a ∈ t i ∩ s.biUnion t, f a := Finset.sum_nonneg fun a _ => hf a
      linarith
    linarith
theorem add_pow_four_le_eight_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by apply _root_.YangMills.Construction.BlockAverages.SplitCriticalPointBounds.add_pow_four_le <;> assumption
theorem polarUnit_conj (g g' : UnitQuaternion) {q : ℍ[ℝ]} (h : q ≠ 0) :
    polarUnit ((g : ℍ[ℝ]) * q * ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ])) = g * polarUnit q * g'⁻¹ := by apply _root_.YangMills.Construction.GaugeMotions.polarUnit_coe_mul_mul_coe_inv <;> assumption
theorem refineSite_add_blockStep {j : ℕ} (hj : j + 1 ≤ F.top) (c : F.Site (j + 1) × Fin 4) :
    refineSite c.1 + siteOfCoords j ((F.blockSide : ℤ) • LatticeFractionalIntegration.basisVector c.2) =
      refineSite (c.1 + unitStep (j + 1) c.2) := by
  rw [unitStep_eq, refineSite_add j hj]
  congr 2
section Level
variable {j : ℕ} (Y R : F.GaugeField j) (φ : F.Site j → UnitQuaternion)
theorem distFromOne_gaugeTransform_le (x : F.Site j) (k : Fin 4) :
    _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform φ Y x k) ≤
      _root_.YangMills.Construction.BlockAverages.distFromOne (Y x k * (R x k)⁻¹) + _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform φ R x k) := by apply _root_.YangMills.Construction.PatchMorrey.distFromOne_gaugeTransform_le <;> assumption
theorem rates_of_blockBounds (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    (hcov : ∀ (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j) (c : F.Site (j + 1) × Fin 4),
      _root_.YangMills.Construction.BlockAverages.contourAverage (gaugeTransform γ X) c = (γ (refineSite c.1) : ℍ[ℝ]) * _root_.YangMills.Construction.BlockAverages.contourAverage X c *
        (((γ (refineSite (c.1 + unitStep (j + 1) c.2)))⁻¹ : UnitQuaternion) : ℍ[ℝ]))
    {P : Finset F.Cell} {T : F.Site (j + 1) → ℝ} (hT0 : ∀ y, 0 ≤ T y)
    (hTb : ∀ c ∈ innerBonds P (j + 1), BoundedOnAdjacentBlocks
      (fun x k => _root_.YangMills.Construction.BlockAverages.distFromOne (Y x k * (R x k)⁻¹) + _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform φ R x k)) c (T c.1))
    (hTs : ∀ y ∈ sitesOfCells P (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ k,
      h + Pi.single k 1 ∈ centredCube F.blockSide →
      _root_.YangMills.Construction.BlockAverages.distFromOne (Y (refineSite y + siteOfCoords j h) k * (R (refineSite y + siteOfCoords j h) k)⁻¹) +
        _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform φ R (refineSite y + siteOfCoords j h) k) ≤ T y)
    (hsmall : ∀ y, 5 * (F.blockSide : ℝ) * T y ≤ 1 / 4) :
    (∀ y ∈ sitesOfCells P (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (balancingGauge Y R y) ≤ 6 * F.blockSide * T y) ∧
    (∀ y ∈ sitesOfCells P (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      _root_.YangMills.Construction.BlockAverages.distFromOne (φ (refineSite y) * pathHolonomy Y (refineSite y) (axisPath h π) *
        (φ (refineSite y + siteOfCoords j h))⁻¹) ≤ 2 * F.blockSide * T y) ∧
    (∀ c ∈ innerBonds P (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      _root_.YangMills.Construction.BlockAverages.distFromOne (pathHolonomy Y (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage Y c))⁻¹) ≤ 20 * F.blockSide * T c.1) ∧
    (∀ c ∈ innerBonds P (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4), ∀ r, r < F.blockSide →
      _root_.YangMills.Construction.BlockAverages.distFromOne (φ (refineSite c.1) *
        pathHolonomy Y (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)) *
        (φ (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2))⁻¹) ≤ 3 * F.blockSide * T c.1) ∧
    (∀ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.contourAverage Y c ≠ 0 ∧
      _root_.YangMills.Construction.BlockAverages.distFromOne (φ (refineSite c.1) * polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage Y c) *
        (φ (refineSite (c.1 + unitStep (j + 1) c.2)))⁻¹) ≤ 15 * F.blockSide * T c.1) := by
  have hL1 : 1 ≤ F.blockSide := hodd.pos
  set Y' : F.GaugeField j := gaugeTransform φ Y with hY'
  have stepBlock : ∀ y ∈ sitesOfCells P (j + 1), ∀ a ∈ centredCube F.blockSide, ∀ k,
      a + LatticeFractionalIntegration.basisVector k ∈ centredCube F.blockSide →
      _root_.YangMills.Construction.BlockAverages.distFromOne (Y' (refineSite y + siteOfCoords j a) k) ≤ T y := fun y hy a ha k hk =>
    (_root_.YangMills.Construction.BlockAverages.PatchRates.distFromOne_gaugeTransform_le Y R φ _ k).trans (hTs y hy a ha k hk)
  have stepHull : ∀ c ∈ innerBonds P (j + 1), ∀ a ∈ FlatPairing.twoBlockHull F.blockSide c.2, ∀ k,
      a + LatticeFractionalIntegration.basisVector k ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      _root_.YangMills.Construction.BlockAverages.distFromOne (Y' (refineSite c.1 + siteOfCoords j a) k) ≤ T c.1 := fun c hc a ha k hk =>
    (_root_.YangMills.Construction.BlockAverages.PatchRates.distFromOne_gaugeTransform_le Y R φ _ k).trans (le_of_mem_twoBlockHull hodd hj (hTb c hc) a ha k hk)
  have contourY' : ∀ c ∈ innerBonds P (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      _root_.YangMills.Construction.BlockAverages.distFromOne (pathHolonomy Y' (refineSite c.1) (bondContour F.blockSide h π c.2)) ≤
        5 * F.blockSide * T c.1 := by
    intro c hc h hh π
    have h1 := distFromOne_pathHolonomy_le Y' (refineSite c.1)
      (fun v => v ∈ FlatPairing.twoBlockHull F.blockSide c.2) (T c.1) (hT0 _)
      (distFromOne_linkValue_le Y' (refineSite c.1) (FlatPairing.twoBlockHull F.blockSide c.2) (T c.1)
        (stepHull c hc)) _ 0
      (bondContour_spec π c.2 hL1 hh).1
    rw [siteOfCoords_zero, add_zero] at h1
    have h2 : ((bondContour F.blockSide h π c.2).length : ℝ) ≤ 5 * F.blockSide := by
      exact_mod_cast length_bondContour_le π c.2 hL1 hh
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (hT0 _))
  have meanY' : ∀ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.contourAverage Y' c ≠ 0 ∧
      _root_.YangMills.Construction.BlockAverages.distFromOne (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage Y' c)) ≤ 3 * (5 * F.blockSide * T c.1) := fun c hc =>
    contourAverage_near_one hodd Y' c _ (hsmall c.1) (contourY' c hc)
  have meanConj : ∀ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.contourAverage Y c ≠ 0 ∧
      polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage Y' c) = φ (refineSite c.1) * polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage Y c) *
        (φ (refineSite (c.1 + unitStep (j + 1) c.2)))⁻¹ := by
    intro c hc
    have e := hcov φ Y c
    have h0 : _root_.YangMills.Construction.BlockAverages.contourAverage Y c ≠ 0 := by
      intro hz
      apply (meanY' c hc).1
      rw [hY', e, hz]
      simp
    refine ⟨h0, ?_⟩
    rw [hY', e]
    exact polarUnit_conj _ _ h0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    refine _root_.YangMills.Construction.BondHull.distFromOne_balancingGauge_le hodd Y R y (T y) (hT0 y) ?_ ?_
    · have := hsmall y
      nlinarith
    · intro a ha k hk
      have h1 := hTs y hy a ha k hk
      have h2 : 0 ≤ _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform φ R (refineSite y + siteOfCoords j a) k) :=
        _root_.YangMills.Construction.BondHull.distFromOne_nonneg _
      linarith
  · intro y hy h hh π
    have h1 := _root_.YangMills.Construction.BondHull.distFromOne_pathHolonomy_le Y' (refineSite y) (fun v => v ∈ centredCube F.blockSide) (T y) (hT0 _)
      (_root_.YangMills.Construction.BondHull.distFromOne_linkValue_le Y' (refineSite y) {v | v ∈ centredCube F.blockSide} (T y) (stepBlock y hy)) _ 0
      (allAlong_axisPath_centredCube hh π)
    rw [siteOfCoords_zero, add_zero] at h1
    have h2 := length_axisPath_le hh π
    have e := pathHolonomy_gaugeTransform_zero φ Y (refineSite y) (axisPath h π)
    rw [(axisPath_spec h π).2] at e
    rw [← e]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (hT0 _))
  · intro c hc h hh π
    obtain ⟨h0, e2⟩ := meanConj c hc
    have e1 := pathHolonomy_gaugeTransform_zero φ Y (refineSite c.1) (bondContour F.blockSide h π c.2)
    rw [(bondContour_spec π c.2 hL1 hh).2, refineSite_add_blockStep hj c] at e1
    have e3 : pathHolonomy Y' (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage Y' c))⁻¹ =
        φ (refineSite c.1) * (pathHolonomy Y (refineSite c.1) (bondContour F.blockSide h π c.2) *
          (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage Y c))⁻¹) * (φ (refineSite c.1))⁻¹ := by
      rw [e1, e2]
      group
    have h1 : _root_.YangMills.Construction.BlockAverages.distFromOne (pathHolonomy Y (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage Y c))⁻¹) =
        _root_.YangMills.Construction.BlockAverages.distFromOne (pathHolonomy Y' (refineSite c.1) (bondContour F.blockSide h π c.2) *
          (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage Y' c))⁻¹) := by
      rw [e3, _root_.YangMills.Construction.BondHull.distFromOne_conj]
    rw [h1]
    refine (_root_.YangMills.Construction.BondHull.distFromOne_mul_le _ _).trans ?_
    rw [_root_.YangMills.Construction.BondHull.distFromOne_inv]
    have a1 := contourY' c hc h hh π
    have a2 := (meanY' c hc).2
    linarith
  · intro c hc h hh π r hr
    obtain ⟨hp, he⟩ := allAlong_axisPath_append_line hh hL1 c.2 π hr.le
    have h1 := distFromOne_pathHolonomy_le Y' (refineSite c.1)
      (fun v => v ∈ FlatPairing.twoBlockHull F.blockSide c.2) (T c.1) (hT0 _)
      (distFromOne_linkValue_le Y' (refineSite c.1) (FlatPairing.twoBlockHull F.blockSide c.2) (T c.1)
        (stepHull c hc)) _ 0 hp
    rw [siteOfCoords_zero, add_zero] at h1
    have h2 := length_axisPath_append_line_le hh c.2 π hr.le
    have e := pathHolonomy_gaugeTransform_zero φ Y (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true))
    rw [he, ← lineBond_fst] at e
    have e' : (lineBond c h r).1 = refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2 := rfl
    rw [e'] at e
    rw [← e]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (hT0 _))
  · intro c hc
    obtain ⟨h0, e2⟩ := meanConj c hc
    refine ⟨h0, ?_⟩
    rw [← e2]
    have := (meanY' c hc).2
    linarith
end Level
section Sums
variable {a θ del Ca C₁ s : ℝ} {S : Finset F.Cell} {V V' : F.GaugeField F.top} {U : ChainChart F} {z : F.Cell}
open Classical in
def bondsNear (S : Finset F.Cell) (j : ℕ) (p : F.Site 0) (r : ℝ) : Finset (F.Site j × Fin 4) :=
  (innerBonds S j).filter (fun b => (baseDistance b.1 p : ℝ) ≤ r * (F.blockSide : ℝ) ^ j)
theorem sum_referenceGap_pow_four_le (hcrit : IsCriticalChainOverTop a θ del Ca C₁ s S V V' U)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {j : ℕ} (hj : j < F.top) :
    ∑ b ∈ innerBonds (patchCells S z) j,
        _root_.YangMills.Construction.BlockAverages.distFromOne (chartField (referenceFieldChain S V) U j b.1 b.2 *
          (referenceFieldChain S V j b.1 b.2)⁻¹) ^ 4 ≤
      47 ^ 4 * (C₁ * s) ^ 4 := by
  classical
  have hL1 : 1 ≤ F.blockSide := hodd.pos
  have hLR : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL1
  set r : ℝ := (F.blockSide : ℝ) ^ (F.top - j) with hr
  have hr1 : 1 ≤ r := one_le_pow₀ hLR
  set g : F.Site j × Fin 4 → ℝ := fun b =>
    _root_.YangMills.Construction.BlockAverages.distFromOne (chartField (referenceFieldChain S V) U j b.1 b.2 *
      (referenceFieldChain S V j b.1 b.2)⁻¹) ^ 4 with hg
  have hg0 : ∀ b, 0 ≤ g b := fun b => pow_nonneg (distFromOne_nonneg _) 4
  have hsub : innerBonds (patchCells S z) j ⊆
      (patchCells S z).biUnion fun y => bondsNear S j (cellCentre 0 y) r := by
    intro b hb
    have hbS : b ∈ innerBonds S j := by
      have h2 := hb
      rw [innerBonds_patchCells hamb hodd he hj.le] at h2
      exact (Finset.mem_filter.1 h2).1
    have hb1 : b.1 ∈ sitesOfCells (patchCells S z) j := (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1
    obtain ⟨y, hy, h', hh', e⟩ := exists_cell_of_mem_sitesOfCells hodd hj.le hb1 (zero_mem_centredCube hodd.pow)
    rw [_root_.YangMills.Construction.BlockAverages.siteOfCoords_zero, add_zero] at e
    refine Finset.mem_biUnion.2 ⟨y, hy, Finset.mem_filter.2 ⟨hbS, ?_⟩⟩
    have hd : baseDistance b.1 (cellCentre 0 y) ≤ F.blockSide ^ F.top := by
      unfold baseDistance
      refine Finset.sup_le fun i _ => ?_
      rw [e, add_sub_cancel_left]
      refine (PatchPoints.natAbs_valMinAbs_intCast_le _ (h' i)).trans ?_
      have h3 := abs_le_of_mem_centredCube (pow_pos hodd.pos _) hh' i
      rw [Int.abs_eq_natAbs] at h3
      exact_mod_cast h3
    have e2 : r * (F.blockSide : ℝ) ^ j = ((F.blockSide ^ F.top : ℕ) : ℝ) := by
      rw [hr, ← pow_add]
      push_cast
      congr 1
      omega
    rw [e2]
    exact_mod_cast hd
  calc ∑ b ∈ innerBonds (patchCells S z) j, g b
      ≤ ∑ b ∈ (patchCells S z).biUnion fun y => bondsNear S j (cellCentre 0 y) r, g b :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => hg0 b
    _ ≤ ∑ y ∈ patchCells S z, ∑ b ∈ bondsNear S j (cellCentre 0 y) r, g b := sum_biUnion_le_sum_sum _ _ _ hg0
    _ ≤ ∑ _y ∈ patchCells S z, (C₁ * s) ^ 4 := by
        refine Finset.sum_le_sum fun y _ => ?_
        have h1 := hcrit.quartic j (cellCentre 0 y) r hj hr1 le_rfl
        have e3 : r / (F.blockSide : ℝ) ^ (F.top - j) = 1 := by
          rw [hr]
          exact div_self (by positivity)
        rw [e3, Real.one_rpow, mul_one] at h1
        exact h1
    _ = ((patchCells S z).card : ℝ) * (C₁ * s) ^ 4 := by simp
    _ ≤ 47 ^ 4 * (C₁ * s) ^ 4 := by
        have h2 : ((patchCells S z).card : ℝ) ≤ 47 ^ 4 := by
          exact_mod_cast card_patchCells_le hamb hodd he
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
theorem sum_misfit_pow_four_le (hcrit : IsCriticalChainOverTop a θ del Ca C₁ s S V V' U)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hL2 : 2 ≤ F.blockSide) (hcs : 0 ≤ C₁ * s)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {j : ℕ} (hj : j < F.top) :
    ∑ c ∈ innerBonds (patchCells S z) (j + 1),
        _root_.YangMills.Construction.BlockAverages.distFromOne (chartBondMisfit (referenceFieldChain S V) U V' j c) ^ 4 ≤
      47 ^ 4 * (C₁ * s) ^ 4 := by
  classical
  have hLR : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast hL2
  set g : F.Site (j + 1) × Fin 4 → ℝ := fun c =>
    _root_.YangMills.Construction.BlockAverages.distFromOne (chartBondMisfit (referenceFieldChain S V) U V' j c) ^ 4 with hg
  have hg0 : ∀ b, 0 ≤ g b := fun b => pow_nonneg (distFromOne_nonneg _) 4
  have hsub : innerBonds (patchCells S z) (j + 1) ⊆
      (patchCells S z).biUnion fun y => bondsOver S {y} (j + 1) := by
    intro b hb
    have hbS : b ∈ innerBonds S (j + 1) := by
      have h2 := hb
      rw [innerBonds_patchCells hamb hodd he hj] at h2
      exact (Finset.mem_filter.1 h2).1
    have hb1 : b.1 ∈ sitesOfCells (patchCells S z) (j + 1) :=
      (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1
    obtain ⟨y, hy, h, hh, e⟩ := mem_sitesOfCells.1 hb1
    refine Finset.mem_biUnion.2 ⟨y, hy, ?_⟩
    unfold bondsOver
    refine Finset.mem_filter.2 ⟨hbS, Finset.mem_singleton.2 ?_⟩
    rw [e]
    exact PatchPoints.enclosingCell_cellCentre_add hodd y h hh
  calc ∑ b ∈ innerBonds (patchCells S z) (j + 1), g b
      ≤ ∑ b ∈ (patchCells S z).biUnion fun y => bondsOver S {y} (j + 1), g b :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => hg0 b
    _ ≤ ∑ y ∈ patchCells S z, ∑ b ∈ bondsOver S {y} (j + 1), g b := sum_biUnion_le_sum_sum _ _ _ hg0
    _ ≤ ∑ _y ∈ patchCells S z, (C₁ * s) ^ 4 := by
        refine Finset.sum_le_sum fun y _ => ?_
        have h1 := (hcrit.misfits_on_cells j y hj).1
        have hq0 : (0 : ℝ) ≤ 4 / (F.blockSide : ℝ) ^ 2 := by positivity
        have hq1 : 4 / (F.blockSide : ℝ) ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith
        have hp1 : (4 / (F.blockSide : ℝ) ^ 2) ^ (F.top - 1 - j) ≤ 1 := pow_le_one₀ hq0 hq1
        have h2 : C₁ * s * (4 / (F.blockSide : ℝ) ^ 2) ^ (F.top - 1 - j) ≤ C₁ * s := by
          nlinarith
        have h3 := pow_le_pow_left₀ (by positivity) h2 4
        exact h1.trans h3
    _ = ((patchCells S z).card : ℝ) * (C₁ * s) ^ 4 := by simp
    _ ≤ 47 ^ 4 * (C₁ * s) ^ 4 := by
        have h2 : ((patchCells S z).card : ℝ) ≤ 47 ^ 4 := by
          exact_mod_cast card_patchCells_le hamb hodd he
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
theorem sum_misfit_sq_le (hcrit : IsCriticalChainOverTop a θ del Ca C₁ s S V V' U)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hL4 : 4 ≤ F.blockSide) (hcs : 0 ≤ C₁ * s)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {j : ℕ} (hj : j < F.top) :
    ∑ c ∈ innerBonds (patchCells S z) (j + 1),
        _root_.YangMills.Construction.BlockAverages.distFromOne (chartBondMisfit (referenceFieldChain S V) U V' j c) ^ 2 ≤
      47 ^ 4 * (C₁ * s) ^ 2 := by
  classical
  have hLR : (4 : ℝ) ≤ F.blockSide := by exact_mod_cast hL4
  set g : F.Site (j + 1) × Fin 4 → ℝ := fun c =>
    _root_.YangMills.Construction.BlockAverages.distFromOne (chartBondMisfit (referenceFieldChain S V) U V' j c) ^ 2 with hg
  have hg0 : ∀ b, 0 ≤ g b := fun b => pow_nonneg (_root_.YangMills.Construction.BondHull.distFromOne_nonneg _) 2
  have hsub : innerBonds (patchCells S z) (j + 1) ⊆
      (patchCells S z).biUnion fun y => bondsOver S {y} (j + 1) := by
    intro b hb
    have hbS : b ∈ innerBonds S (j + 1) := by
      have h2 := hb
      rw [innerBonds_patchCells hamb hodd he hj] at h2
      exact (Finset.mem_filter.1 h2).1
    have hb1 : b.1 ∈ sitesOfCells (patchCells S z) (j + 1) :=
      (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1
    obtain ⟨y, hy, h, hh, e⟩ := mem_sitesOfCells.1 hb1
    refine Finset.mem_biUnion.2 ⟨y, hy, ?_⟩
    unfold bondsOver
    refine Finset.mem_filter.2 ⟨hbS, Finset.mem_singleton.2 ?_⟩
    rw [e]
    exact PatchPoints.enclosingCell_cellCentre_add hodd y h hh
  calc ∑ b ∈ innerBonds (patchCells S z) (j + 1), g b
      ≤ ∑ b ∈ (patchCells S z).biUnion fun y => bondsOver S {y} (j + 1), g b :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => hg0 b
    _ ≤ ∑ y ∈ patchCells S z, ∑ b ∈ bondsOver S {y} (j + 1), g b := sum_biUnion_le_sum_sum _ _ _ hg0
    _ ≤ ∑ _y ∈ patchCells S z, (C₁ * s) ^ 2 := by
        refine Finset.sum_le_sum fun y _ => ?_
        have h1 := (hcrit.misfits_on_cells j y hj).2
        have hq0 : (0 : ℝ) ≤ 4 / (F.blockSide : ℝ) := by positivity
        have hq1 : 4 / (F.blockSide : ℝ) ≤ 1 := by
          rw [div_le_one (by linarith)]
          exact hLR
        have hp1 : (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j) ≤ 1 := pow_le_one₀ hq0 hq1
        have h2 : C₁ * s * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j) ≤ C₁ * s := by
          nlinarith
        have h3 := pow_le_pow_left₀ (by positivity) h2 2
        exact h1.trans h3
    _ = ((patchCells S z).card : ℝ) * (C₁ * s) ^ 2 := by simp
    _ ≤ 47 ^ 4 * (C₁ * s) ^ 2 := by
        have h2 : ((patchCells S z).card : ℝ) ≤ 47 ^ 4 := by
          exact_mod_cast card_patchCells_le hamb hodd he
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
end Sums
theorem quartic_combine_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    8 * (47 ^ 4 * A ^ 4 + 4 * 47 ^ 4 * B ^ 4) ≤ (8 * 47 * (A + 2 * B)) ^ 4 := by
  have e : (A + 2 * B) ^ 4 = A ^ 4 + 8 * A ^ 3 * B + 24 * A ^ 2 * B ^ 2 + 32 * A * B ^ 3 + 16 * B ^ 4 := by ring
  have h1 : 0 ≤ 8 * A ^ 3 * B + 24 * A ^ 2 * B ^ 2 + 32 * A * B ^ 3 := by positivity
  have h2 : A ^ 4 + 4 * B ^ 4 ≤ (A + 2 * B) ^ 4 := by
    have : 0 ≤ B ^ 4 := by positivity
    rw [e]
    linarith
  have h3 : 0 ≤ (A + 2 * B) ^ 4 := by positivity
  calc 8 * (47 ^ 4 * A ^ 4 + 4 * 47 ^ 4 * B ^ 4) = 8 * 47 ^ 4 * (A ^ 4 + 4 * B ^ 4) := by ring
    _ ≤ 8 * 47 ^ 4 * (A + 2 * B) ^ 4 := by gcongr
    _ ≤ (8 * 47 : ℝ) ^ 4 * (A + 2 * B) ^ 4 := by
        apply mul_le_mul_of_nonneg_right _ h3
        norm_num
    _ = _ := by ring
theorem pow_four_add_pow_four_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) : A ^ 4 + B ^ 4 ≤ (A + B) ^ 4 := by apply _root_.YangMills.Construction.PatchMorrey.pow_four_add_pow_four_le <;> assumption
theorem quartic_siteRate_le {Lr K s C1 : ℝ} (hL : 0 ≤ Lr) (hK : 0 ≤ K) (hs : 0 ≤ s) (hC : 0 ≤ C1) :
    (6 * Lr) ^ 4 * (4 * (3 * Lr) ^ 4 * (K * s) ^ 4) ≤ ((240 * Lr ^ 2 * K + 94 * C1) * s) ^ 4 := by
  have hA : 0 ≤ 240 * Lr ^ 2 * K * s := by positivity
  have hB : 0 ≤ 94 * C1 * s := by positivity
  have h1 := pow_four_add_pow_four_le hA hB
  have e1 : (240 * Lr ^ 2 * K + 94 * C1) * s = 240 * Lr ^ 2 * K * s + 94 * C1 * s := by ring
  rw [e1]
  have hx : 0 ≤ (Lr ^ 2 * K * s) ^ 4 := by positivity
  have e2 : (6 * Lr) ^ 4 * (4 * (3 * Lr) ^ 4 * (K * s) ^ 4) = 419904 * (Lr ^ 2 * K * s) ^ 4 := by ring
  have hB4 : 0 ≤ (94 * C1 * s) ^ 4 := by positivity
  rw [e2]
  linarith
theorem quartic_bondRate_le {Lr K s C1 : ℝ} (hL : 0 ≤ Lr) (hK : 0 ≤ K) (hs : 0 ≤ s) (hC : 0 ≤ C1) :
    8 * ((20 * Lr) ^ 4 * (16 * (3 * Lr) ^ 4 * (K * s) ^ 4) + 47 ^ 4 * (C1 * s) ^ 4) ≤
      ((240 * Lr ^ 2 * K + 94 * C1) * s) ^ 4 := by
  have hA : 0 ≤ 240 * Lr ^ 2 * K * s := by positivity
  have hB : 0 ≤ 94 * C1 * s := by positivity
  have h1 := pow_four_add_pow_four_le hA hB
  have e1 : (240 * Lr ^ 2 * K + 94 * C1) * s = 240 * Lr ^ 2 * K * s + 94 * C1 * s := by ring
  rw [e1]
  have e2 : 8 * ((20 * Lr) ^ 4 * (16 * (3 * Lr) ^ 4 * (K * s) ^ 4) + 47 ^ 4 * (C1 * s) ^ 4) =
      1 / 2 * (240 * Lr ^ 2 * K * s) ^ 4 + 1 / 2 * (94 * C1 * s) ^ 4 := by ring
  have hA4 : 0 ≤ (240 * Lr ^ 2 * K * s) ^ 4 := by positivity
  have hB4 : 0 ≤ (94 * C1 * s) ^ 4 := by positivity
  rw [e2]
  linarith
end PatchRates
set_option maxHeartbeats 1600000 in
open PatchRates LatticePaths BlockLines PatchLocality BondHull in
theorem criticalChainPatchRates_holds (hR : referenceBoundsStatement)
    (hA : averagesAndLocalSizesStatement) (hG : gaugeCovarianceStatement) :
    criticalChainPatchRatesStatement := by
  intro a θ del Ca ha hθ hθ' hd hd' hCa
  obtain ⟨CR, cR, L1, hCR, hcR, hRef⟩ := hR
  refine ⟨max L1 5, fun L hLodd hLL C₁ hC₁ => ?_⟩
  have hL1 : L1 ≤ L := le_trans (le_max_left _ _) hLL
  have hL3 : 5 ≤ L := le_trans (le_max_right _ _) hLL
  have hLR3 : (5 : ℝ) ≤ L := by exact_mod_cast hL3
  set K₀ : ℝ := 8 * 47 * (C₁ + 2 * CR) with hK₀
  have hK₀p : 0 < K₀ := by positivity
  set C₀ : ℝ := 240 * (L : ℝ) ^ 2 * K₀ + 94 * C₁ with hC₀
  have hC₀p : 0 < C₀ := by positivity
  refine ⟨4 * C₀ + 2209 * C₁, min cR (1 / (120 * (L : ℝ) ^ 2 * K₀)), by positivity,
    lt_min hcR (by positivity), ?_⟩
  intro F m S hFL hamb hm hreg s V v hs hsc hcold U hcrit z hz
  subst hFL
  have hodd : Odd F.blockSide := hLodd
  have hLp : (0 : ℝ) < F.blockSide := by linarith
  have hsR : s ≤ cR := hsc.trans (min_le_left _ _)
  have hs1 : 120 * (F.blockSide : ℝ) ^ 2 * K₀ * s ≤ 1 := by
    have h1 : s ≤ 1 / (120 * (F.blockSide : ℝ) ^ 2 * K₀) := hsc.trans (min_le_right _ _)
    calc 120 * (F.blockSide : ℝ) ^ 2 * K₀ * s
        ≤ 120 * (F.blockSide : ℝ) ^ 2 * K₀ * (1 / (120 * (F.blockSide : ℝ) ^ 2 * K₀)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := by field_simp
  obtain ⟨he, -⟩ := closedOrthant_spec hreg (by omega) z
  obtain ⟨r1, -⟩ := hRef F m S hodd hL1 hamb hm hreg s V hs hsR hcold
  have lev : ∀ j, j < F.top → (∑ b ∈ innerBonds (patchCells S z) j,
      _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform (fun x => (patchFrame S V z x)⁻¹) (criticalFieldChain S V v U j) b.1 b.2) ^ 4 ≤
        (C₀ * s) ^ 4) ∧
      ∃ (E : F.Site (j + 1) → ℝ) (e : F.Site (j + 1) × Fin 4 → ℝ),
      (∀ y, 0 ≤ E y) ∧ (∀ c, 0 ≤ e c) ∧
      ∑ y ∈ sitesOfCells (patchCells S z) (j + 1), E y ^ 4 ≤ (C₀ * s) ^ 4 ∧
      ∑ c ∈ innerBonds (patchCells S z) (j + 1), e c ^ 4 ≤ (C₀ * s) ^ 4 ∧
      ∑ c ∈ innerBonds (patchCells S z) (j + 1),
        _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit (criticalFieldChain S V v U j) (criticalGauge S V U (j + 1))
          (criticalFieldChain S V v U (j + 1)) c) ^ 2 ≤ 47 ^ 4 * (C₁ * s) ^ 2 ∧
      HasPatchRates S V z (criticalFieldChain S V v U) (criticalGauge S V U) j E e := by
    intro j hj
    have hj1 : j + 1 ≤ F.top := hj
    have hWj : criticalFieldChain S V v U j = chartField (referenceFieldChain S V) U j := by
      unfold criticalFieldChain chartChain
      exact Function.update_of_ne hj.ne _ _
    set P := patchCells S z with hP
    set W := criticalFieldChain S V v U with hW
    set kW := criticalGauge S V U with hkW
    set φ : F.Site j → UnitQuaternion := fun x => (patchFrame S V z x)⁻¹ with hφ
    set Rj := referenceFieldChain S V j with hRj
    set f : F.Site j → Fin 4 → ℝ :=
      fun x k => _root_.YangMills.Construction.BlockAverages.distFromOne (W j x k * (Rj x k)⁻¹) + _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform φ Rj x k) with hf
    have hf0 : ∀ x i, 0 ≤ f x i := fun x i => add_nonneg (_root_.YangMills.Construction.BondHull.distFromOne_nonneg _) (_root_.YangMills.Construction.BondHull.distFromOne_nonneg _)
    have hsum : ∑ b ∈ innerBonds P j, f b.1 b.2 ^ 4 ≤ (K₀ * s) ^ 4 := by
      have hu := sum_referenceGap_pow_four_le (z := z) hcrit hamb hodd he hj
      rw [← hWj] at hu
      have hr : ∑ b ∈ innerBonds P j, _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform φ Rj b.1 b.2) ^ 4 ≤
          4 * 47 ^ 4 * (CR * s) ^ 4 := by
        have hpt : ∀ b ∈ innerBonds P j, _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform φ Rj b.1 b.2) ^ 4 ≤
            (CR * s * levelScale F j) ^ 4 := by
          intro b hb
          have h2 := hb
          rw [innerBonds_patchCells hamb hodd he hj.le] at h2
          obtain ⟨hbS, hb1, hb2⟩ := Finset.mem_filter.1 h2
          exact pow_le_pow_left₀ (_root_.YangMills.Construction.BondHull.distFromOne_nonneg _) (r1 j hj z hz b hbS hb1 hb2) 4
        refine (Finset.sum_le_sum hpt).trans ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        have hc1 : ((innerBonds P j).card : ℝ) ≤
            4 * (47 ^ 4 * ((F.blockSide : ℝ) ^ (F.top - j)) ^ 4) := by
          have h3 := card_innerBonds_le hodd P j
          have h4 := card_patchCells_le hamb hodd he
          have h5 : ((innerBonds P j).card : ℝ) ≤
              4 * ((P.card : ℝ) * ((F.blockSide : ℝ) ^ (F.top - j)) ^ 4) := by
            exact_mod_cast h3
          have h6 : (P.card : ℝ) ≤ 47 ^ 4 := by exact_mod_cast h4
          refine h5.trans ?_
          gcongr
        have hscale : ((F.blockSide : ℝ) ^ (F.top - j)) * levelScale F j = 1 := by
          unfold levelScale
          rw [← mul_pow]
          rw [mul_one_div_cancel hLp.ne', one_pow]
        calc ((innerBonds P j).card : ℝ) * (CR * s * levelScale F j) ^ 4
            ≤ 4 * (47 ^ 4 * ((F.blockSide : ℝ) ^ (F.top - j)) ^ 4) * (CR * s * levelScale F j) ^ 4 :=
              mul_le_mul_of_nonneg_right hc1 (by positivity)
          _ = 4 * 47 ^ 4 * (CR * s) ^ 4 * (((F.blockSide : ℝ) ^ (F.top - j)) * levelScale F j) ^ 4 := by ring
          _ = 4 * 47 ^ 4 * (CR * s) ^ 4 := by rw [hscale]; ring
      have hA0 : 0 ≤ C₁ * s := by positivity
      have hB0 : 0 ≤ CR * s := by positivity
      calc ∑ b ∈ innerBonds P j, f b.1 b.2 ^ 4
          ≤ ∑ b ∈ innerBonds P j, 8 * (_root_.YangMills.Construction.BlockAverages.distFromOne (W j b.1 b.2 * (Rj b.1 b.2)⁻¹) ^ 4 +
              _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform φ Rj b.1 b.2) ^ 4) :=
            Finset.sum_le_sum fun b _ => add_pow_four_le_eight_mul (_root_.YangMills.Construction.BondHull.distFromOne_nonneg _) (_root_.YangMills.Construction.BondHull.distFromOne_nonneg _)
        _ = 8 * (∑ b ∈ innerBonds P j, _root_.YangMills.Construction.BlockAverages.distFromOne (W j b.1 b.2 * (Rj b.1 b.2)⁻¹) ^ 4 +
              ∑ b ∈ innerBonds P j, _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform φ Rj b.1 b.2) ^ 4) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
        _ ≤ 8 * (47 ^ 4 * (C₁ * s) ^ 4 + 4 * 47 ^ 4 * (CR * s) ^ 4) := by
            have := add_le_add hu hr
            linarith
        _ ≤ (8 * 47 * (C₁ * s + 2 * (CR * s))) ^ 4 := quartic_combine_le hA0 hB0
        _ = (K₀ * s) ^ 4 := by
            rw [hK₀]
            ring
    have hS0 : 0 ≤ ∑ b ∈ innerBonds P j, f b.1 b.2 ^ 4 :=
      Finset.sum_nonneg fun b _ => pow_nonneg (hf0 _ _) 4
    obtain ⟨-, -, -, T, hT0, hTb, hTs, hT1, hT2, hT3⟩ := hA F P j f hodd hj1 hf0
    have hTle : ∀ y, T y ≤ 6 * F.blockSide * (K₀ * s) := by
      intro y
      have h1 : T y ^ 4 ≤ (6 * (F.blockSide : ℝ) * (K₀ * s)) ^ 4 := by
        have h2 : 4 * (3 * (F.blockSide : ℝ)) ^ 4 * ∑ b ∈ innerBonds P j, f b.1 b.2 ^ 4 ≤
            4 * (3 * (F.blockSide : ℝ)) ^ 4 * (K₀ * s) ^ 4 := mul_le_mul_of_nonneg_left hsum (by positivity)
        have h3 : 4 * (3 * (F.blockSide : ℝ)) ^ 4 * (K₀ * s) ^ 4 ≤ (6 * (F.blockSide : ℝ) * (K₀ * s)) ^ 4 := by
          have h4 : 0 ≤ ((F.blockSide : ℝ) * (K₀ * s)) ^ 4 := by positivity
          have e1 : 4 * (3 * (F.blockSide : ℝ)) ^ 4 * (K₀ * s) ^ 4 =
              324 * ((F.blockSide : ℝ) * (K₀ * s)) ^ 4 := by ring
          have e2 : (6 * (F.blockSide : ℝ) * (K₀ * s)) ^ 4 = 1296 * ((F.blockSide : ℝ) * (K₀ * s)) ^ 4 := by ring
          rw [e1, e2]
          linarith
        exact (hT1 y).trans (h2.trans h3)
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h1
    have hsmall : ∀ y, 5 * (F.blockSide : ℝ) * T y ≤ 1 / 4 := by
      intro y
      have h1 := hTle y
      have h2 : 5 * (F.blockSide : ℝ) * T y ≤ 5 * (F.blockSide : ℝ) * (6 * F.blockSide * (K₀ * s)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have e : 5 * (F.blockSide : ℝ) * (6 * F.blockSide * (K₀ * s)) =
          1 / 4 * (120 * (F.blockSide : ℝ) ^ 2 * K₀ * s) := by ring
      rw [e] at h2
      linarith
    obtain ⟨-, hcov, -, -⟩ := hG F j hj hodd.pos
    obtain ⟨q1, q2, q3, q4, q5⟩ := rates_of_blockBounds (W j) Rj φ hodd hj1 hcov hT0 hTb hTs hsmall
    have hk : ∀ y, kW (j + 1) y = balancingGauge (W j) Rj y := by
      intro y
      rw [hWj]
      rfl
    have hsite : ∀ c ∈ innerBonds P (j + 1), c.1 ∈ sitesOfCells P (j + 1) := fun c hc =>
      (Finset.mem_product.1 (Finset.mem_filter.1 hc).1).1
    have hTn : ∀ y, 0 ≤ (F.blockSide : ℝ) * T y := fun y => mul_nonneg hLp.le (hT0 y)
    have hK₀C : K₀ * s ≤ C₀ * s := by
      have h1 : K₀ ≤ C₀ := by
        have h2 : 1 ≤ 240 * (F.blockSide : ℝ) ^ 2 := by nlinarith
        have h3 : K₀ ≤ 240 * (F.blockSide : ℝ) ^ 2 * K₀ := le_mul_of_one_le_left hK₀p.le h2
        have h4 : 0 ≤ 94 * C₁ := by positivity
        rw [hC₀]
        linarith
      exact mul_le_mul_of_nonneg_right h1 hs.le
    refine ⟨?_, fun y => 6 * F.blockSide * T y,
      fun c => 20 * F.blockSide * T c.1 + _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c),
      fun y => mul_nonneg (by positivity) (hT0 y),
      fun c => add_nonneg (mul_nonneg (by positivity) (hT0 _)) (_root_.YangMills.Construction.BondHull.distFromOne_nonneg _), ?_, ?_, ?_, ?_⟩
    · have h1 : ∑ b ∈ innerBonds P j, _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform φ (W j) b.1 b.2) ^ 4 ≤
          ∑ b ∈ innerBonds P j, f b.1 b.2 ^ 4 :=
        Finset.sum_le_sum fun b _ =>
          pow_le_pow_left₀ (_root_.YangMills.Construction.BondHull.distFromOne_nonneg _) (_root_.YangMills.Construction.BlockAverages.PatchRates.distFromOne_gaugeTransform_le (W j) Rj φ b.1 b.2) 4
      exact h1.trans (hsum.trans (pow_le_pow_left₀ (by positivity) hK₀C 4))
    · have e : ∀ y, (6 * (F.blockSide : ℝ) * T y) ^ 4 = (6 * (F.blockSide : ℝ)) ^ 4 * T y ^ 4 :=
        fun y => by ring
      simp only [e]
      rw [← Finset.mul_sum]
      have h1 : ∑ y ∈ sitesOfCells P (j + 1), T y ^ 4 ≤ 4 * (3 * (F.blockSide : ℝ)) ^ 4 * (K₀ * s) ^ 4 :=
        hT3.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
      exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans
        (quartic_siteRate_le hLp.le hK₀p.le hs.le hC₁.le)
    · have hm4 := sum_misfit_pow_four_le (z := z) (V' := rotatedField v V) hcrit hamb hodd (by omega)
        (by positivity) he hj
      have hm4' : ∑ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ^ 4 ≤
          47 ^ 4 * (C₁ * s) ^ 4 := hm4
      have h1 : ∑ c ∈ innerBonds P (j + 1), T c.1 ^ 4 ≤ 16 * (3 * (F.blockSide : ℝ)) ^ 4 * (K₀ * s) ^ 4 :=
        hT2.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
      calc ∑ c ∈ innerBonds P (j + 1), (20 * (F.blockSide : ℝ) * T c.1 +
            _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)) ^ 4
          ≤ ∑ c ∈ innerBonds P (j + 1), 8 * ((20 * (F.blockSide : ℝ)) ^ 4 * T c.1 ^ 4 +
              _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ^ 4) := by
            refine Finset.sum_le_sum fun c _ => ?_
            have := add_pow_four_le_eight_mul (x := 20 * (F.blockSide : ℝ) * T c.1)
              (y := _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c))
              (mul_nonneg (by positivity) (hT0 _)) (_root_.YangMills.Construction.BondHull.distFromOne_nonneg _)
            rwa [mul_pow (20 * (F.blockSide : ℝ)) (T c.1) 4] at this
        _ = 8 * ((20 * (F.blockSide : ℝ)) ^ 4 * ∑ c ∈ innerBonds P (j + 1), T c.1 ^ 4 +
              ∑ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ^ 4) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
        _ ≤ 8 * ((20 * (F.blockSide : ℝ)) ^ 4 * (16 * (3 * (F.blockSide : ℝ)) ^ 4 * (K₀ * s) ^ 4) +
              47 ^ 4 * (C₁ * s) ^ 4) := by
            have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (20 * (F.blockSide : ℝ)) ^ 4)
            linarith
        _ ≤ (C₀ * s) ^ 4 := quartic_bondRate_le hLp.le hK₀p.le hs.le hC₁.le
    · exact sum_misfit_sq_le (z := z) (V' := rotatedField v V) hcrit hamb hodd (by omega) (by positivity) he hj
    · refine ⟨fun y hy => ?_, fun y hy h hh π => ?_, fun c hc h hh π => ?_, fun c hc h hh π r hr => ?_,
        fun c hc => ?_, fun c hc => ?_, fun c hc => ?_⟩
      · rw [hk y]
        exact q1 y hy
      · have h1 := q2 y hy h hh π
        simp only [hφ, inv_inv] at h1
        have := hTn y
        nlinarith
      · have h1 := q3 c hc h hh π
        have h2 := distFromOne_nonneg (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)
        linarith
      · have h1 := q4 c hc h hh π r hr
        simp only [hφ, inv_inv] at h1
        have h2 := distFromOne_nonneg (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)
        have := hTn c.1
        nlinarith
      · obtain ⟨h0, h1⟩ := q5 c hc
        refine ⟨h0, ?_⟩
        simp only [hφ, inv_inv] at h1
        have h2 := distFromOne_nonneg (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)
        have := hTn c.1
        nlinarith
      · rw [hk c.1]
        have h1 := q1 c.1 (hsite c hc)
        have h2 := distFromOne_nonneg (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)
        have := hTn c.1
        nlinarith
      · have := hTn c.1
        have h2 : 0 ≤ 20 * (F.blockSide : ℝ) * T c.1 := mul_nonneg (by positivity) (hT0 _)
        linarith
  have hCCs : 0 < C₀ * s := mul_pos hC₀p hs
  have hC1s : 0 < C₁ * s := mul_pos hC₁ hs
  have hle1 : C₀ * s ≤ (4 * C₀ + 2209 * C₁) * s := by
    have e1 : (4 * C₀ + 2209 * C₁) * s = 4 * (C₀ * s) + 2209 * (C₁ * s) := by ring
    rw [e1]
    linarith
  have hmono : (C₀ * s) ^ 4 ≤ ((4 * C₀ + 2209 * C₁) * s) ^ 4 := pow_le_pow_left₀ hCCs.le hle1 4
  have hmono2 : 47 ^ 4 * (C₁ * s) ^ 2 ≤ ((4 * C₀ + 2209 * C₁) * s) ^ 2 := by
    have e : (47 : ℝ) ^ 4 * (C₁ * s) ^ 2 = (2209 * C₁ * s) ^ 2 := by ring
    rw [e]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    have e1 : (4 * C₀ + 2209 * C₁) * s = 4 * (C₀ * s) + 2209 * C₁ * s := by ring
    rw [e1]
    linarith
  refine ⟨fun j hj => ?_, fun c hc => ?_, fun j hj => (lev j hj).1.trans hmono⟩
  · obtain ⟨-, E, e, h1, h2, h3, h4, h6, h5⟩ := lev j hj
    exact ⟨E, e, h1, h2, h3.trans hmono, h4.trans hmono, h6.trans hmono2, h5⟩
  · obtain ⟨-, E, e, hE0, he0, hE4, he4, -, hr⟩ := lev F.depth (Nat.lt_succ_self _)
    have hc' : c ∈ innerBonds (patchCells S z) (F.depth + 1) := hc
    have hy' : c.1 + unitStep (F.depth + 1) c.2 ∈ sitesOfCells (patchCells S z) (F.depth + 1) :=
      (Finset.mem_filter.1 hc).2
    have hCs : 0 ≤ C₀ * s := by positivity
    have ptE : E (c.1 + unitStep (F.depth + 1) c.2) ≤ C₀ * s := by
      have h1 := Finset.single_le_sum (f := fun y => E y ^ 4) (fun y _ => by have := hE0 y; positivity) hy'
      exact le_of_pow_le_pow_left₀ (by norm_num) hCs (h1.trans hE4)
    have pte : e c ≤ C₀ * s := by
      have h1 := Finset.single_le_sum (f := fun c => e c ^ 4) (fun c _ => by have := he0 c; positivity) hc'
      exact le_of_pow_le_pow_left₀ (by norm_num) hCs (h1.trans he4)
    obtain ⟨hm0, hm1⟩ := hr.average_le c hc'
    have hk1 := hr.bondGauge_le c hc'
    have hmis := hr.misfit_le c hc'
    have hk2 := hr.gauge_le _ hy'
    have hfd : ∀ y : F.Site (F.depth + 1), patchFrame S V z (refineSite y) = patchFrame S V z y := by
      intro y
      unfold patchFrame
      rw [baseSite_refineSite _ (le_refl _)]
    rw [hfd, hfd] at hm1
    set W := criticalFieldChain S V v U with hW
    set kW := criticalGauge S V U with hkW
    set u := polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (W F.depth) c) with hu
    set mm := bondMisfit (W F.depth) (kW (F.depth + 1)) (W (F.depth + 1)) c with hmm
    set f₁ := patchFrame S V z c.1 with hf₁
    set f₂ := patchFrame S V z (c.1 + unitStep (F.depth + 1) c.2) with hf₂
    set k₁ := kW (F.depth + 1) c.1 with hk₁
    set k₂ := kW (F.depth + 1) (c.1 + unitStep (F.depth + 1) c.2) with hk₂
    have eU : polarUnit (gaugedContourAverage (W F.depth) (kW (F.depth + 1)) c) = k₁ * u * k₂⁻¹ :=
      polarUnit_conj _ _ hm0
    have eW : W (F.depth + 1) c.1 c.2 = mm * (k₁ * u * k₂⁻¹) := by
      rw [hmm, ← eU]
      simp only [bondMisfit]
      group
    have eF : f₁⁻¹ * (mm * (k₁ * u * k₂⁻¹)) * f₂ = (f₁⁻¹ * mm * f₁⁻¹⁻¹) * (f₁⁻¹ * k₁ * f₁⁻¹⁻¹) *
        (f₁⁻¹ * u * f₂) * (f₂⁻¹ * k₂⁻¹ * f₂⁻¹⁻¹) := by
      group
    show _root_.YangMills.Construction.BlockAverages.distFromOne (f₁⁻¹ * W (F.depth + 1) c.1 c.2 * f₂) ≤ _
    rw [eW, eF]
    have b1 := _root_.YangMills.Construction.BondHull.distFromOne_mul_le ((f₁⁻¹ * mm * f₁⁻¹⁻¹) * (f₁⁻¹ * k₁ * f₁⁻¹⁻¹) * (f₁⁻¹ * u * f₂))
      (f₂⁻¹ * k₂⁻¹ * f₂⁻¹⁻¹)
    have b2 := _root_.YangMills.Construction.BondHull.distFromOne_mul_le ((f₁⁻¹ * mm * f₁⁻¹⁻¹) * (f₁⁻¹ * k₁ * f₁⁻¹⁻¹)) (f₁⁻¹ * u * f₂)
    have b3 := _root_.YangMills.Construction.BondHull.distFromOne_mul_le (f₁⁻¹ * mm * f₁⁻¹⁻¹) (f₁⁻¹ * k₁ * f₁⁻¹⁻¹)
    rw [distFromOne_conj] at b3
    rw [distFromOne_conj] at b3
    rw [_root_.YangMills.Construction.BondHull.distFromOne_conj, _root_.YangMills.Construction.BondHull.distFromOne_inv] at b1
    have hfin0 : 0 ≤ 2209 * C₁ * s := by positivity
    have hfin : (4 * C₀ + 2209 * C₁) * s = 4 * (C₀ * s) + 2209 * C₁ * s := by ring
    rw [hfin]
    linarith
end YangMills.Construction.BlockAverages
end

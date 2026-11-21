import YangMills.Construction.ColdChainAtEveryLevel.CriticalForAllVariationsProof
import YangMills.Construction.ColdChainAtEveryLevel.BumpsOfTheCellsProof
import YangMills.Construction.ColdChainAtEveryLevel.ShareOfTheCriticalChain
import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
namespace CriticalShare
variable {F : BlockFrame}
theorem re_sq_add_norm_im_sq (g : UnitQuaternion) : ((g : ℍ[ℝ])).re ^ 2 + ‖((g : ℍ[ℝ])).im‖ ^ 2 = 1 := by
  have h1 : Quaternion.normSq (g : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, norm_coe_unitQuaternion]
    norm_num
  have h2 : ‖((g : ℍ[ℝ])).im‖ ^ 2 =
      ((g : ℍ[ℝ])).imI ^ 2 + ((g : ℍ[ℝ])).imJ ^ 2 + ((g : ℍ[ℝ])).imK ^ 2 := by
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    simp
  rw [Quaternion.normSq_def'] at h1
  rw [h2]
  linarith
theorem norm_coe_sub_one_sq (g : UnitQuaternion) : ‖(g : ℍ[ℝ]) - 1‖ ^ 2 = 2 - 2 * ((g : ℍ[ℝ])).re := by apply _root_.YangMills.Construction.GaugeFixing.norm_coe_sub_one_sq <;> assumption
theorem one_sub_re_le_norm_im_sq (g : UnitQuaternion) (hg : ‖(g : ℍ[ℝ]) - 1‖ ≤ 1) :
    1 - ((g : ℍ[ℝ])).re ≤ ‖((g : ℍ[ℝ])).im‖ ^ 2 := by
  have h1 := norm_coe_sub_one_sq g
  have h2 := re_sq_add_norm_im_sq g
  have h3 : ‖(g : ℍ[ℝ]) - 1‖ ^ 2 ≤ 1 := by
    have := norm_nonneg ((g : ℍ[ℝ]) - 1)
    nlinarith
  nlinarith
theorem norm_sub_re_mul_inv_le (M : ℍ[ℝ]) (hM : ‖M‖ ≤ 1) (g : UnitQuaternion) :
    ‖M‖ - (M * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re ≤ normSubOne (g * (polarUnit M)⁻¹) ^ 2 / 2 := by
  by_cases h0 : M = 0
  · subst h0
    simp only [norm_zero, zero_mul, Quaternion.re_zero, sub_zero]
    positivity
  · have hn : 0 < ‖M‖ := norm_pos_iff.2 h0
    have hMu : ‖M‖ • ((polarUnit M : UnitQuaternion) : ℍ[ℝ]) = M := by
      rw [coe_polarUnit h0, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have e1 : M * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
        ‖M‖ • star ((g * (polarUnit M)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      rw [Submonoid.coe_mul, star_mul, coe_unitQuaternion_inv, coe_unitQuaternion_inv, star_star]
      conv_lhs => rw [← hMu]
      rw [smul_mul_assoc]
    have e2 : (M * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re =
        ‖M‖ * ((g * (polarUnit M)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re := by
      rw [e1]
      have hs : ∀ (r : ℝ) (q : ℍ[ℝ]), (r • star q).re = r * q.re := fun r q => by simp
      exact hs _ _
    rw [e2]
    unfold normSubOne
    have h1 := norm_coe_sub_one_sq (g * (polarUnit M)⁻¹)
    rw [h1]
    have h2 := sq_nonneg (‖((g * (polarUnit M)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖)
    rw [h1] at h2
    nlinarith
theorem norm_gaugedContourAverage_le (hodd : Odd F.blockSide) {j : ℕ} (X : F.GaugeField j)
    (k : F.Site (j + 1) → UnitQuaternion) (c : F.Site (j + 1) × Fin 4) :
    ‖gaugedContourAverage X k c‖ ≤ 1 := by
  unfold gaugedContourAverage
  rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, mul_one]
  unfold contourAverage
  rw [norm_smul]
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hs : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])‖ ≤
        24 * (F.blockSide : ℝ) ^ 4 := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun _ _ => norm_sum_le _ _).trans ?_)
    simp only [norm_coe_unitQuaternion, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, LatticePaths.card_centredCube hodd]
    simp [Nat.factorial]
    linarith
  rw [Real.norm_of_nonneg (by positivity)]
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _ ≤
        1 / (24 * (F.blockSide : ℝ) ^ 4) * (24 * (F.blockSide : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 1 := by field_simp
theorem norm_coe_mul_sub_coe_mul_le (x y x' y' : UnitQuaternion) :
    ‖((x * y : UnitQuaternion) : ℍ[ℝ]) - ((x' * y' : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖(x : ℍ[ℝ]) - x'‖ + ‖(y : ℍ[ℝ]) - y'‖ := by
  have e : ((x * y : UnitQuaternion) : ℍ[ℝ]) - ((x' * y' : UnitQuaternion) : ℍ[ℝ]) =
      (x : ℍ[ℝ]) * ((y : ℍ[ℝ]) - y') + ((x : ℍ[ℝ]) - x') * (y' : ℍ[ℝ]) := by
    simp only [Submonoid.coe_mul, mul_sub, sub_mul]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, mul_one]
  linarith
theorem norm_coe_inv_sub_coe_inv (x x' : UnitQuaternion) :
    ‖((x⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((x'⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(x : ℍ[ℝ]) - x'‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
theorem norm_coe_sub_coe_eq (x x' : UnitQuaternion) : ‖(x : ℍ[ℝ]) - x'‖ = normSubOne (x * x'⁻¹) := by apply _root_.YangMills.Construction.GaugedCriticality.norm_coe_sub_coe <;> assumption
theorem plaquetteHolonomy_eq (Y : F.GaugeField 0) (x : F.Site 0) (μ ν : Fin 4) :
    plaquetteHolonomy Y (x, μ, ν) =
      Y x μ * (Y (x + unitStep 0 μ) ν * ((Y (x + unitStep 0 ν) μ)⁻¹ * (Y x ν)⁻¹)) := by
  have s3 : x + unitStep 0 μ + unitStep 0 ν - unitStep 0 μ = x + unitStep 0 ν := by abel
  have s4 : x + unitStep 0 μ + unitStep 0 ν + -unitStep 0 μ - unitStep 0 ν = x := by abel
  simp [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, s3, s4]
theorem norm_plaquetteHolonomy_sub_le {S : Finset F.Cell} {X R : F.GaugeField 0} {ε : ℝ}
    (hb : ∀ b ∈ innerBonds S 0, ‖(X b.1 b.2 : ℍ[ℝ]) - R b.1 b.2‖ ≤ ε) {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ innerPlaquettes S 0) :
    ‖((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ]) - ((plaquetteHolonomy R p : UnitQuaternion) : ℍ[ℝ])‖ ≤
      4 * ε := by
  obtain ⟨x, μ, ν⟩ := p
  have hc := (Finset.mem_filter.1 hp).2.2
  have c1 : x ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c2 : x + unitStep 0 μ ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c3 : x + unitStep 0 ν ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c4 : x + unitStep 0 μ + unitStep 0 ν ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have mk : ∀ (w : F.Site 0) (i : Fin 4), w ∈ sitesOfCells S 0 → w + unitStep 0 i ∈ sitesOfCells S 0 →
      ‖(X w i : ℍ[ℝ]) - R w i‖ ≤ ε := fun w i h1 h2 =>
    hb (w, i) (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h1, Finset.mem_univ _⟩, h2⟩)
  have b1 := mk x μ c1 c2
  have b2 := mk (x + unitStep 0 μ) ν c2 c4
  have b3 := mk (x + unitStep 0 ν) μ c3 (by rwa [add_right_comm])
  have b4 := mk x ν c1 c3
  rw [plaquetteHolonomy_eq, plaquetteHolonomy_eq]
  have t1 := norm_coe_mul_sub_coe_mul_le (X x μ)
    (X (x + unitStep 0 μ) ν * ((X (x + unitStep 0 ν) μ)⁻¹ * (X x ν)⁻¹))
    (R x μ) (R (x + unitStep 0 μ) ν * ((R (x + unitStep 0 ν) μ)⁻¹ * (R x ν)⁻¹))
  have t2 := norm_coe_mul_sub_coe_mul_le (X (x + unitStep 0 μ) ν) ((X (x + unitStep 0 ν) μ)⁻¹ * (X x ν)⁻¹)
    (R (x + unitStep 0 μ) ν) ((R (x + unitStep 0 ν) μ)⁻¹ * (R x ν)⁻¹)
  have t3 := norm_coe_mul_sub_coe_mul_le (X (x + unitStep 0 ν) μ)⁻¹ (X x ν)⁻¹
    (R (x + unitStep 0 ν) μ)⁻¹ (R x ν)⁻¹
  rw [norm_coe_inv_sub_coe_inv, norm_coe_inv_sub_coe_inv] at t3
  linarith
theorem baseSite_zero (x : F.Site 0) : baseSite x = x := by apply _root_.YangMills.Construction.CellBumps.baseSite_zero <;> assumption
theorem natAbs_valMinAbs_intCast_le {p : ℕ} (A : ℤ) : ((A : ZMod p)).valMinAbs.natAbs ≤ A.natAbs := by apply _root_.YangMills.Construction.BlockWeights.natAbs_valMinAbs_intCast_le <;> assumption
theorem sup_natAbs_sub_cellCentre_le {w : F.Site 0} {y : F.Cell} {h : Fin 4 → ℤ} (hodd : Odd F.blockSide)
    (hh : h ∈ centredCube (F.blockSide ^ F.top)) (e : w = cellCentre 0 y + siteOfCoords 0 h) :
    ((Finset.univ.sup fun i => (((w - cellCentre 0 y) i).valMinAbs).natAbs : ℕ) : ℝ) ≤
      (F.blockSide : ℝ) ^ F.top := by
  have hM : 0 < F.blockSide ^ F.top := pow_pos hodd.pos _
  have : (Finset.univ.sup fun i => (((w - cellCentre 0 y) i).valMinAbs).natAbs) ≤ F.blockSide ^ F.top := by
    refine Finset.sup_le fun i _ => ?_
    have e1 : (w - cellCentre 0 y) i = ((h i : ℤ) : ZMod (F.period 0 i)) := by
      rw [e]
      simp [siteOfCoords]
    rw [e1]
    refine (natAbs_valMinAbs_intCast_le (h i)).trans ?_
    have h1 := PatchLocality.abs_le_of_mem_centredCube hM hh i
    have h2 : ((h i).natAbs : ℤ) = |h i| := Int.natCast_natAbs _
    omega
  exact_mod_cast this
theorem sum_actionTerms_filter_enclosingCell (S : Finset F.Cell) (y : F.Cell) (f : F.ActionTerm → ℝ) :
    ∑ t ∈ (actionTerms S).filter (fun t => enclosingCell (actionTermSite t) = y), f t =
      ∑ p ∈ innerPlaquettes S 0, (if enclosingCell p.1 = y then f (Sum.inl p) else 0) +
        ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1),
          (if enclosingCell (baseSite c.1) = y then f (Sum.inr ⟨j, c⟩) else 0) := by
  rw [Finset.sum_filter, PatchLocality.sum_actionTerms]
  rfl
theorem norm_chartField_sub_le {S : Finset F.Cell} {R : F.FieldChain} {U : ChainChart F} {K θ : ℝ}
    (hL : 0 < F.blockSide) (hθ : 0 < θ) (hK : 0 ≤ K)
    (hq : ∀ (p : F.Site 0) (r : ℝ), 1 ≤ r → r ≤ (F.blockSide : ℝ) ^ (F.top - 0) →
      localQuarticSum S R U 0 p r ≤ K ^ 4 * (r / (F.blockSide : ℝ) ^ (F.top - 0)) ^ (4 * θ))
    {b : F.Site 0 × Fin 4} (hb : b ∈ innerBonds S 0) :
    ‖(chartField R U 0 b.1 b.2 : ℍ[ℝ]) - R 0 b.1 b.2‖ ≤ K := by
  classical
  have hLr : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
  have hN : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ (F.top - 0) := one_le_pow₀ hLr
  have h1 := hq (baseSite b.1) 1 le_rfl hN
  have h2 : normSubOne (chartField R U 0 b.1 b.2 * (R 0 b.1 b.2)⁻¹) ^ 4 ≤
      localQuarticSum S R U 0 (baseSite b.1) 1 := by
    unfold localQuarticSum
    refine Finset.single_le_sum (f := fun b : F.Site 0 × Fin 4 =>
      normSubOne (chartField R U 0 b.1 b.2 * (R 0 b.1 b.2)⁻¹) ^ 4) (fun _ _ => by positivity) ?_
    refine Finset.mem_filter.2 ⟨hb, ?_⟩
    have : baseDistance b.1 (baseSite b.1) = 0 := by
      simp [baseDistance]
    rw [this]
    simp
  have h3 : (1 / (F.blockSide : ℝ) ^ (F.top - 0)) ^ (4 * θ) ≤ 1 := by
    refine Real.rpow_le_one (by positivity) ?_ (by positivity)
    rw [div_le_one (by positivity)]
    exact hN
  have h4 : normSubOne (chartField R U 0 b.1 b.2 * (R 0 b.1 b.2)⁻¹) ^ 4 ≤ K ^ 4 := by
    have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ K ^ 4)
    linarith
  rw [norm_coe_sub_coe_eq]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hK (by norm_num)).1 h4
end CriticalShare
open CriticalShare in
theorem criticalCellShareBound (hB : referenceBoundsStatement) : criticalCellShareBoundStatement := by
  obtain ⟨C, c, L1, hC, hc, hB⟩ := hB
  intro a θ del Ca ha hθ _ _ _ _
  refine ⟨max L1 1, fun L hL hL0 C₁ hC₁ => ?_⟩
  refine ⟨C₁ ^ 2 * (1 + a / 2), min c (1 / (C + 4 * C₁)), by positivity, lt_min hc (by positivity), ?_⟩
  intro F m S hFL hamb hm hreg s V v hs hsσ hcold _ U hU y
  have hodd : Odd F.blockSide := hFL ▸ hL
  have hLpos : 0 < F.blockSide := hodd.pos
  have hL1 : L1 ≤ F.blockSide := hFL ▸ le_trans (le_max_left _ _) hL0
  have hsc : s ≤ c := hsσ.trans (min_le_left _ _)
  have hpos : 0 < C + 4 * C₁ := by positivity
  have hs1 : (C + 4 * C₁) * s ≤ 1 := by
    have := hsσ.trans (min_le_right _ _)
    rw [le_div_iff₀ hpos] at this
    linarith
  obtain ⟨-, hcurv, -⟩ := hB F m S hodd hL1 hamb hm hreg s V hs hsc hcold
  have hLr : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hLpos
  have hN1 : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := one_le_pow₀ hLr
  have hNne : ((F.blockSide : ℝ) ^ F.top) ≠ 0 := by positivity
  have hK : 0 ≤ C₁ * s := by positivity
  have hgap : ∀ b ∈ innerBonds S 0, ‖(chartField (referenceFieldChain S V) U 0 b.1 b.2 : ℍ[ℝ]) -
      referenceFieldChain S V 0 b.1 b.2‖ ≤ C₁ * s := fun b hb =>
    norm_chartField_sub_le hLpos hθ hK (fun p r h1 h2 => hU.quartic 0 p r (Nat.succ_pos _) h1 h2) hb
  have hplaq : ∀ p ∈ innerPlaquettes S 0,
      ‖((plaquetteHolonomy (chartField (referenceFieldChain S V) U 0) p : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 1 := by
    intro p hp
    have h1 := norm_plaquetteHolonomy_sub_le hgap hp
    have h2 := hcurv 0 (Nat.succ_pos _) p hp
    have h3 : levelScale F 0 ^ 2 ≤ 1 := by
      unfold levelScale
      rw [← pow_mul]
      refine pow_le_one₀ (by positivity) ?_
      rw [div_le_one (by positivity)]
      exact hLr
    have h4 : C * s * levelScale F 0 ^ 2 ≤ C * s :=
      mul_le_of_le_one_right (by positivity) h3
    have h5 := norm_sub_le_norm_sub_add_norm_sub
      ((plaquetteHolonomy (chartField (referenceFieldChain S V) U 0) p : UnitQuaternion) : ℍ[ℝ])
      ((plaquetteHolonomy (referenceFieldChain S V 0) p : UnitQuaternion) : ℍ[ℝ]) 1
    unfold plaquetteDefect at h2
    nlinarith
  have hfirst : chartChain (referenceFieldChain S V) U (rotatedField v V) 0 =
      chartField (referenceFieldChain S V) U 0 := by
    unfold chartChain
    exact Function.update_of_ne (by simp) _ _
  obtain ⟨hcv, hmf⟩ := hU.curvature_and_misfits (cellCentre 0 y) ((F.blockSide : ℝ) ^ F.top) hN1 le_rfl
  rw [div_self hNne, Real.one_rpow, mul_one] at hcv hmf
  rw [sum_actionTerms_filter_enclosingCell]
  have hA : ∑ p ∈ innerPlaquettes S 0, (if enclosingCell p.1 = y then
      actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) (Sum.inl p) else 0) ≤
      localCurvatureSum S (referenceFieldChain S V) U (cellCentre 0 y) ((F.blockSide : ℝ) ^ F.top) := by
    classical
    unfold localCurvatureSum
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun p hp => ?_
    by_cases hy : enclosingCell p.1 = y
    · have ht : (Sum.inl p : F.ActionTerm) ∈ actionTerms S := Finset.inl_mem_disjSum.2 hp
      obtain ⟨-, h, hh, e⟩ := PatchLocality.enclosingCell_actionTermSite hodd ht
      have e' : p.1 = cellCentre 0 y + siteOfCoords 0 h := by
        rw [← hy]
        exact e
      have hd : (baseDistance p.1 (cellCentre 0 y) : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := by
        unfold baseDistance
        rw [baseSite_zero]
        exact sup_natAbs_sub_cellCentre_le hodd hh e'
      rw [if_pos hy, if_pos hd]
      show 1 - ((plaquetteHolonomy (criticalFieldChain S V v U 0) p : UnitQuaternion) : ℍ[ℝ]).re ≤ _
      unfold criticalFieldChain
      rw [hfirst]
      exact one_sub_re_le_norm_im_sq _ (hplaq p hp)
    · rw [if_neg hy]
      split_ifs <;> positivity
  have hBsum : ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1), (if enclosingCell (baseSite c.1) = y then
      actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) (Sum.inr ⟨j, c⟩) else 0) ≤
      a / 2 * localMisfitSum S (referenceFieldChain S V) U (rotatedField v V) (cellCentre 0 y)
        ((F.blockSide : ℝ) ^ F.top) := by
    classical
    unfold localMisfitSum
    have hfil : (Finset.range F.top).filter
        (fun j => (F.blockSide : ℝ) ^ (j + 1) ≤ (F.blockSide : ℝ) ^ F.top) = Finset.range F.top :=
      Finset.filter_true_of_mem fun j hj => pow_le_pow_right₀ hLr (Finset.mem_range.1 hj)
    rw [hfil, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_le_sum fun c' hc' => ?_
    by_cases hy : enclosingCell (baseSite c'.1) = y
    · have ht : (Sum.inr ⟨j, c'⟩ : F.ActionTerm) ∈ actionTerms S :=
        Finset.inr_mem_disjSum.2 (Finset.mem_sigma.2 ⟨hj, hc'⟩)
      obtain ⟨-, h, hh, e⟩ := PatchLocality.enclosingCell_actionTermSite hodd ht
      have e' : baseSite c'.1 = cellCentre 0 y + siteOfCoords 0 h := by
        rw [← hy]
        exact e
      have hd : (baseDistance c'.1 (cellCentre 0 y) : ℝ) ≤ (F.blockSide : ℝ) ^ F.top :=
        sup_natAbs_sub_cellCentre_le hodd hh e'
      rw [if_pos hy, if_pos hd]
      show a * gaugedBlockFit _ _ _ c' ≤ _
      have hf := norm_sub_re_mul_inv_le _ (norm_gaugedContourAverage_le hodd
        (chartChain (referenceFieldChain S V) U (rotatedField v V) j)
        (chartGauge (referenceFieldChain S V) U (j + 1)) c')
        (chartChain (referenceFieldChain S V) U (rotatedField v V) (j + 1) c'.1 c'.2)
      have hg : gaugedBlockFit (criticalFieldChain S V v U j) (criticalGauge S V U (j + 1))
          (criticalFieldChain S V v U (j + 1)) c' ≤
          normSubOne (chartBondMisfit (referenceFieldChain S V) U (rotatedField v V) j c') ^ 2 / 2 := hf
      have := mul_le_mul_of_nonneg_left hg ha.le
      linarith
    · rw [if_neg hy]
      split_ifs
      · have : 0 ≤ normSubOne (chartBondMisfit (referenceFieldChain S V) U (rotatedField v V) j c') ^ 2 := by
          positivity
        positivity
      · simp
  have hfin : (C₁ * s) ^ 2 + a / 2 * (C₁ * s) ^ 2 = C₁ ^ 2 * (1 + a / 2) * s ^ 2 := by ring
  have h2 := mul_le_mul_of_nonneg_left hmf (by positivity : (0 : ℝ) ≤ a / 2)
  linarith
end BlockAverages
end YangMills.Construction
end

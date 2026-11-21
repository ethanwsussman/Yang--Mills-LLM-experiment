import YangMills.Construction.ColdChainAtEveryLevel.GapsOfAFramingOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.HolonomiesOnTheHullOfABond
import YangMills.Construction.ColdChainAtEveryLevel.MeanOfTheContoursOfABond
import YangMills.Construction.ColdChainAtEveryLevel.OneStepOfAFraming
import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheCriticalChainOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.TopGapOfAFramingOnAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace TopDefectAverage
open BlockAverages BlockLines BondHull
variable {F : BlockFrame} {j : ℕ}
def bondLineMean (g : F.Site j → Fin 4 → ℍ[ℝ]) (c : F.Site (j + 1) × Fin 4) : ℍ[ℝ] :=
  (1 / (F.blockSide : ℝ) ^ 4) • ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
    g (_root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2
theorem bondLineMean_sub (g g' : F.Site j → Fin 4 → ℍ[ℝ]) (c : F.Site (j + 1) × Fin 4) :
    bondLineMean g c - bondLineMean g' c = bondLineMean (fun x i => g x i - g' x i) c := by
  unfold bondLineMean
  simp only [Finset.sum_sub_distrib, smul_sub]
theorem norm_bondLineMean_le (hodd : Odd F.blockSide) (g : F.Site j → Fin 4 → ℍ[ℝ]) (c : F.Site (j + 1) × Fin 4) :
    ‖bondLineMean g c‖ ≤ lineBlockAverage (fun x i => ‖g x i‖) c := by
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  unfold bondLineMean lineBlockAverage
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => norm_sum_le _ _)
theorem bondLineMean_eq_perm_average (hodd : Odd F.blockSide) (g : F.Site j → Fin 4 → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) :
    bondLineMean g c = (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide,
      ∑ _π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide,
        g (_root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2 := by
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hperm : (Fintype.card (Equiv.Perm (Fin 4)) : ℝ) = 24 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  unfold bondLineMean
  simp only [Finset.sum_const, Finset.card_univ]
  simp only [← Nat.cast_smul_eq_nsmul ℝ, ← Finset.smul_sum, smul_smul, hperm]
  congr 1
  field_simp
theorem adjointAction_mul (a b : UnitQuaternion) (w : ℍ[ℝ]) :
    _root_.YangMills.Construction.BlockAverages.adjointAction (a * b) w = _root_.YangMills.Construction.BlockAverages.adjointAction a (_root_.YangMills.Construction.BlockAverages.adjointAction b w) := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_mul <;> assumption
theorem adjointAction_smul (g : UnitQuaternion) (r : ℝ) (w : ℍ[ℝ]) :
    _root_.YangMills.Construction.BlockAverages.adjointAction g (r • w) = r • _root_.YangMills.Construction.BlockAverages.adjointAction g w := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_smul <;> assumption
theorem adjointAction_sum {ι : Type} (g : UnitQuaternion) (s : Finset ι) (f : ι → ℍ[ℝ]) :
    _root_.YangMills.Construction.BlockAverages.adjointAction g (∑ i ∈ s, f i) = ∑ i ∈ s, _root_.YangMills.Construction.BlockAverages.adjointAction g (f i) := by
  simp only [_root_.YangMills.Construction.BlockAverages.adjointAction, Finset.mul_sum, Finset.sum_mul]
theorem norm_adjointAction_parallelAverage_sub_le (hodd : Odd F.blockSide) (R : F.GaugeField j)
    (G : F.Site j → Fin 4 → ℍ[ℝ]) (f : F.Site j → UnitQuaternion) (y : UnitQuaternion)
    (b : F.Site (j + 1) × Fin 4) (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hline : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4), ∀ r, r < F.blockSide →
      distFromOne (y⁻¹ * pathHolonomy R (refineSite b.1) (axisPath h π ++ List.replicate r (b.2, true)) *
        f (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2)) ≤ ε)
    (hg : ∀ h ∈ centredCube F.blockSide, ∀ r, r < F.blockSide →
      ‖G (_root_.YangMills.Construction.BlockAverages.refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2‖ ≤ t) :
    ‖_root_.YangMills.Construction.BlockAverages.adjointAction y⁻¹ (parallelAverage R G b) -
        bondLineMean (fun x i => _root_.YangMills.Construction.BlockAverages.adjointAction (f x)⁻¹ (G x i)) b‖ ≤ 2 * ε * ((F.blockSide : ℝ) * t) := by
  rw [bondLineMean_eq_perm_average hodd]
  unfold parallelAverage
  rw [_root_.YangMills.Construction.TopDefectAverage.adjointAction_smul, _root_.YangMills.Construction.TopDefectAverage.adjointAction_sum, ← smul_sub, ← Finset.sum_sub_distrib]
  have e : ∀ h ∈ centredCube F.blockSide, _root_.YangMills.Construction.BlockAverages.adjointAction y⁻¹ (∑ π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide,
        _root_.YangMills.Construction.BlockAverages.adjointAction (pathHolonomy R (refineSite b.1) (axisPath h π ++ List.replicate r (b.2, true)))
          (G (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2)) -
      ∑ _π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide,
        adjointAction (f (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2))⁻¹
          (G (_root_.YangMills.Construction.BlockAverages.refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2) =
      ∑ π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide,
        (_root_.YangMills.Construction.BlockAverages.adjointAction y⁻¹ (_root_.YangMills.Construction.BlockAverages.adjointAction
            (pathHolonomy R (refineSite b.1) (axisPath h π ++ List.replicate r (b.2, true)))
          (G (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2)) -
        adjointAction (f (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2))⁻¹
          (G (_root_.YangMills.Construction.BlockAverages.refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2)) := by
    intro h _
    rw [adjointAction_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [adjointAction_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl e]
  refine norm_smul_sum_perm_le hodd _ _ fun h hh π => ?_
  have hb : ∀ r ∈ Finset.range F.blockSide,
      ‖_root_.YangMills.Construction.BlockAverages.adjointAction y⁻¹ (_root_.YangMills.Construction.BlockAverages.adjointAction
            (pathHolonomy R (refineSite b.1) (axisPath h π ++ List.replicate r (b.2, true)))
          (G (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2)) -
        adjointAction (f (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2))⁻¹
          (G (_root_.YangMills.Construction.BlockAverages.refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2)‖ ≤ 2 * ε * t := by
    intro r hr
    have hr' := Finset.mem_range.1 hr
    set x := _root_.YangMills.Construction.BlockAverages.refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2 with hx
    set H := pathHolonomy R (_root_.YangMills.Construction.BlockAverages.refineSite b.1) (axisPath h π ++ List.replicate r (b.2, true)) with hH
    have e2 : _root_.YangMills.Construction.BlockAverages.adjointAction y⁻¹ (_root_.YangMills.Construction.BlockAverages.adjointAction H (G x b.2)) =
        _root_.YangMills.Construction.BlockAverages.adjointAction (y⁻¹ * H * f x) (_root_.YangMills.Construction.BlockAverages.adjointAction (f x)⁻¹ (G x b.2)) := by
      rw [← _root_.YangMills.Construction.TopDefectAverage.adjointAction_mul, ← _root_.YangMills.Construction.TopDefectAverage.adjointAction_mul]
      congr 1
      group
    rw [e2]
    refine (norm_adjointAction_sub_le _ _).trans ?_
    rw [_root_.YangMills.Construction.BlockLines.norm_adjointAction]
    have h1 : ‖(((y⁻¹ * H * f x : UnitQuaternion)) : ℍ[ℝ]) - 1‖ ≤ ε := hline h hh π r hr'
    have h2 := hg h hh r hr'
    have h3 := mul_le_mul h1 h2 (norm_nonneg _) hε0
    nlinarith
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hb).trans ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  apply le_of_eq
  ring
theorem norm_pureComponent_upper_sub_le (hodd : Odd F.blockSide) (T R : F.GaugeField j)
    (kR : F.Site (j + 1) → UnitQuaternion) (T' R' : F.GaugeField (j + 1))
    (b : F.Site (j + 1) × Fin 4) (t ε E0 : ℝ) (f : F.Site j → UnitQuaternion) (y : UnitQuaternion)
    (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hneT : gaugedContourAverage T (balancedLinks T R kR) b ≠ 0) (hneR : _root_.YangMills.Construction.BlockAverages.contourAverage R b ≠ 0)
    (m1 : ‖pureComponent ((relativeContourMean T R b : UnitQuaternion) : ℍ[ℝ]) -
      parallelAverage R (pureGap T R) b‖ ≤ E0)
    (hline : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4), ∀ r, r < F.blockSide →
      distFromOne (y⁻¹ * pathHolonomy R (refineSite b.1) (axisPath h π ++ List.replicate r (b.2, true)) *
        f (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2)) ≤ ε)
    (hg : ∀ h ∈ centredCube F.blockSide, ∀ r, r < F.blockSide →
      linkGap T R (_root_.YangMills.Construction.BlockAverages.refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2 ≤ t) :
    ‖_root_.YangMills.Construction.BlockAverages.adjointAction y⁻¹ (pureComponent ((T' b.1 b.2 * (R' b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])) -
        bondLineMean (fun x i => _root_.YangMills.Construction.BlockAverages.adjointAction (f x)⁻¹ (pureGap T R x i)) b‖ ≤
      _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit T (balancedLinks T R kR) T' b * (bondMisfit R kR R' b)⁻¹) +
        (_root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit T (balancedLinks T R kR) T' b * (bondMisfit R kR R' b)⁻¹) +
          2 * _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit R kR R' b) + 2 * _root_.YangMills.Construction.BlockAverages.distFromOne (kR b.1)) *
            _root_.YangMills.Construction.BlockAverages.distFromOne (relativeContourMean T R b) +
        E0 + 2 * ε * ((F.blockSide : ℝ) * t) := by
  have eT : gaugedContourAverage T (balancedLinks T R kR) b =
      (kR b.1 : ℍ[ℝ]) * gaugedContourAverage T (balancingGauge T R) b *
      (((kR (b.1 + unitStep (j + 1) b.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    unfold gaugedContourAverage balancedLinks
    rw [mul_inv_rev, Submonoid.coe_mul, Submonoid.coe_mul]
    simp only [mul_assoc]
  have hne : gaugedContourAverage T (balancingGauge T R) b ≠ 0 := by
    intro h0
    apply hneT
    rw [eT, h0]
    simp
  have eR : gaugedContourAverage R kR b = (kR b.1 : ℍ[ℝ]) * _root_.YangMills.Construction.BlockAverages.contourAverage R b *
      (((kR (b.1 + unitStep (j + 1) b.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := rfl
  have unit_c : ∀ (g g' : UnitQuaternion) {q : ℍ[ℝ]}, q ≠ 0 →
      polarUnit ((g : ℍ[ℝ]) * q * ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ])) = g * polarUnit q * g'⁻¹ := by
    intro g g' q h
    have hg := coe_unitQuaternion_ne_zero g
    have hg' := coe_unitQuaternion_ne_zero g'⁻¹
    rw [polarUnit_mul (mul_ne_zero hg h) hg', polarUnit_mul hg h, BlockLines.polarUnit_coe, BlockLines.polarUnit_coe]
  obtain ⟨uT, huT⟩ : ∃ uT : UnitQuaternion, uT = polarUnit (gaugedContourAverage T (balancingGauge T R) b) :=
    ⟨_, rfl⟩
  obtain ⟨uR, huR⟩ : ∃ uR : UnitQuaternion, uR = polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage R b) := ⟨_, rfl⟩
  obtain ⟨ky, hky⟩ : ∃ ky : UnitQuaternion, ky = kR b.1 := ⟨_, rfl⟩
  obtain ⟨ky', hky'⟩ : ∃ ky' : UnitQuaternion, ky' = kR (b.1 + unitStep (j + 1) b.2) := ⟨_, rfl⟩
  have mT : bondMisfit T (balancedLinks T R kR) T' b = T' b.1 b.2 * (ky * uT * ky'⁻¹)⁻¹ := by
    unfold bondMisfit
    rw [eT, unit_c _ _ hne, ← huT, ← hky, ← hky']
  have mR : bondMisfit R kR R' b = R' b.1 b.2 * (ky * uR * ky'⁻¹)⁻¹ := by
    unfold bondMisfit
    rw [eR, unit_c _ _ hneR, ← huR, ← hky, ← hky']
  have hmA : relativeContourMean T R b = uT * uR⁻¹ := by
    unfold relativeContourMean
    rw [← huT, ← huR]
  set p := bondMisfit T (balancedLinks T R kR) T' b * (bondMisfit R kR R' b)⁻¹ with hp
  set mm := bondMisfit R kR R' b with hmm
  set mA := relativeContourMean T R b with hmAdef
  have ident : T' b.1 b.2 * (R' b.1 b.2)⁻¹ = p * (mm * (ky * mA * ky⁻¹) * mm⁻¹) := by
    rw [hp, mT, hmA, mR]
    group
  rw [ident]
  set w : UnitQuaternion := mm * (ky * mA * ky⁻¹) * mm⁻¹ with hw
  have h1 := norm_pureComponent_mul_sub_le p w
  have hsw : _root_.YangMills.Construction.BlockAverages.distFromOne w = _root_.YangMills.Construction.BlockAverages.distFromOne mA := by
    rw [hw, _root_.YangMills.Construction.BondHull.distFromOne_conj, _root_.YangMills.Construction.BondHull.distFromOne_conj]
  have hcoe : ((w : UnitQuaternion) : ℍ[ℝ]) = _root_.YangMills.Construction.BlockAverages.adjointAction mm (_root_.YangMills.Construction.BlockAverages.adjointAction ky (mA : ℍ[ℝ])) := rfl
  have hpw : pureComponent ((w : UnitQuaternion) : ℍ[ℝ]) =
      _root_.YangMills.Construction.BlockAverages.adjointAction mm (_root_.YangMills.Construction.BlockAverages.adjointAction ky (pureComponent (mA : ℍ[ℝ]))) := by
    rw [hcoe, _root_.YangMills.Construction.BlockLines.pureComponent_adjointAction, _root_.YangMills.Construction.BlockLines.pureComponent_adjointAction]
  set A := pureComponent (mA : ℍ[ℝ]) with hA
  have hA1 : ‖A‖ ≤ _root_.YangMills.Construction.BlockAverages.distFromOne mA := norm_pureComponent_coe_le _
  have h2 : ‖adjointAction mm (adjointAction ky A) - adjointAction ky A‖ ≤ 2 * _root_.YangMills.Construction.BlockAverages.distFromOne mm * _root_.YangMills.Construction.BlockAverages.distFromOne mA := by
    refine (norm_adjointAction_sub_le _ _).trans ?_
    rw [_root_.YangMills.Construction.BlockLines.norm_adjointAction]
    exact mul_le_mul_of_nonneg_left hA1 (mul_nonneg (by norm_num) (norm_nonneg _))
  have h3 : ‖adjointAction ky A - A‖ ≤ 2 * _root_.YangMills.Construction.BlockAverages.distFromOne ky * _root_.YangMills.Construction.BlockAverages.distFromOne mA := by
    refine (norm_adjointAction_sub_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_left hA1 (mul_nonneg (by norm_num) (norm_nonneg _))
  have h4 : ‖pureComponent (p : ℍ[ℝ])‖ ≤ _root_.YangMills.Construction.BlockAverages.distFromOne p := norm_pureComponent_coe_le _
  set tr := parallelAverage R (pureGap T R) b with htr
  have h5 := norm_adjointAction_parallelAverage_sub_le hodd R (pureGap T R) f y b t ε ht0 hε0 hline
    (fun h hh r hr => (norm_pureComponent_coe_le _).trans (hg h hh r hr))
  set Lm := bondLineMean (fun x i => _root_.YangMills.Construction.BlockAverages.adjointAction (f x)⁻¹ (pureGap T R x i)) b with hLm
  set Z := pureComponent ((p * w : UnitQuaternion) : ℍ[ℝ]) with hZ
  have split : _root_.YangMills.Construction.BlockAverages.adjointAction y⁻¹ Z - Lm = _root_.YangMills.Construction.BlockAverages.adjointAction y⁻¹ (Z - tr) + (_root_.YangMills.Construction.BlockAverages.adjointAction y⁻¹ tr - Lm) := by
    rw [_root_.YangMills.Construction.BlockLines.adjointAction_sub]
    abel
  rw [split]
  refine (norm_add_le _ _).trans ?_
  rw [_root_.YangMills.Construction.BlockLines.norm_adjointAction]
  have split2 : Z - tr = (Z - pureComponent (p : ℍ[ℝ]) - pureComponent (w : ℍ[ℝ])) + pureComponent (p : ℍ[ℝ]) +
      (_root_.YangMills.Construction.BlockAverages.adjointAction mm (_root_.YangMills.Construction.BlockAverages.adjointAction ky A) - _root_.YangMills.Construction.BlockAverages.adjointAction ky A) + (_root_.YangMills.Construction.BlockAverages.adjointAction ky A - A) + (A - tr) := by
    rw [hpw]
    abel
  have h6 : ‖Z - tr‖ ≤ ‖Z - pureComponent (p : ℍ[ℝ]) - pureComponent (w : ℍ[ℝ])‖ + ‖pureComponent (p : ℍ[ℝ])‖ +
      ‖_root_.YangMills.Construction.BlockAverages.adjointAction mm (_root_.YangMills.Construction.BlockAverages.adjointAction ky A) - _root_.YangMills.Construction.BlockAverages.adjointAction ky A‖ + ‖_root_.YangMills.Construction.BlockAverages.adjointAction ky A - A‖ + ‖A - tr‖ := by
    rw [split2]
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact norm_add_le _ _
  have h7 : ‖Z - pureComponent (p : ℍ[ℝ]) - pureComponent (w : ℍ[ℝ])‖ ≤ _root_.YangMills.Construction.BlockAverages.distFromOne p * _root_.YangMills.Construction.BlockAverages.distFromOne mA := by
    have := h1
    unfold _root_.YangMills.Construction.BlockAverages.distFromOne at hsw ⊢
    rw [← hsw]
    exact this
  rw [← hky]
  linarith
theorem sqrt_sum_sq_add_le {ι : Type} {s : Finset ι} {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) :
    Real.sqrt (∑ i ∈ s, (f i + g i) ^ 2) ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) + Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  have h := Real.Lp_add_le_of_nonneg (s := s) (f := f) (g := g) (p := 2) (by norm_num) hf hg
  simp only [Real.rpow_two] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact h
theorem sqrt_sum_sq_le_of_le_lineBlockAverage (hA : averagesAndLocalSizesStatement) (hodd : Odd F.blockSide)
    (h5 : 5 ≤ F.blockSide) (hj : j + 1 ≤ F.top)
    {P : Finset F.Cell} {ν : F.Site j → Fin 4 → ℝ} {ν' R : F.Site (j + 1) × Fin 4 → ℝ} {B ρ : ℝ}
    (hν : ∀ x i, 0 ≤ ν x i) (hν' : ∀ c, 0 ≤ ν' c) (hR0 : ∀ c, 0 ≤ R c) (hB0 : 0 ≤ B)
    (hB : Real.sqrt (∑ b ∈ innerBonds P j, ν b.1 b.2 ^ 2) ≤ B)
    (hρ : Real.sqrt (∑ c ∈ innerBonds P (j + 1), R c ^ 2) ≤ ρ)
    (hst : ∀ c ∈ innerBonds P (j + 1), ν' c ≤ lineBlockAverage ν c + R c) :
    Real.sqrt (∑ c ∈ innerBonds P (j + 1), ν' c ^ 2) ≤ 1 / 5 * B + ρ := by
  have hL5 : (5 : ℝ) ≤ F.blockSide := by exact_mod_cast h5
  obtain ⟨-, -, h2, -⟩ := hA F P j ν hodd hj hν
  have hpa0 : ∀ c, 0 ≤ lineBlockAverage ν c := fun c =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hν _ _)
  have hS0 : 0 ≤ ∑ b ∈ innerBonds P j, ν b.1 b.2 ^ 2 := Finset.sum_nonneg fun b _ => by positivity
  have hQ : Real.sqrt (∑ c ∈ innerBonds P (j + 1), lineBlockAverage ν c ^ 2) ≤ 1 / 5 * B := by
    have e1 : (1 / (F.blockSide : ℝ) ^ 2) * ∑ b ∈ innerBonds P j, ν b.1 b.2 ^ 2 =
        ((1 / (F.blockSide : ℝ)) * Real.sqrt (∑ b ∈ innerBonds P j, ν b.1 b.2 ^ 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hS0]
      field_simp
    rw [e1] at h2
    have h3 : Real.sqrt (∑ c ∈ innerBonds P (j + 1), lineBlockAverage ν c ^ 2) ≤
        (1 / (F.blockSide : ℝ)) * Real.sqrt (∑ b ∈ innerBonds P j, ν b.1 b.2 ^ 2) := by
      rw [← Real.sqrt_sq (by positivity :
        0 ≤ (1 / (F.blockSide : ℝ)) * Real.sqrt (∑ b ∈ innerBonds P j, ν b.1 b.2 ^ 2))]
      exact Real.sqrt_le_sqrt h2
    have h4 : 1 / (F.blockSide : ℝ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hL5
    exact h3.trans (mul_le_mul h4 hB (Real.sqrt_nonneg _) (by norm_num))
  have h6 := sqrt_sum_sq_add_le (s := innerBonds P (j + 1)) (f := fun c => lineBlockAverage ν c) (g := R)
    (fun c _ => hpa0 c) (fun c _ => hR0 c)
  have h7 : Real.sqrt (∑ c ∈ innerBonds P (j + 1), ν' c ^ 2) ≤
      Real.sqrt (∑ c ∈ innerBonds P (j + 1), (lineBlockAverage ν c + R c) ^ 2) :=
    Real.sqrt_le_sqrt (Finset.sum_le_sum fun c hc => pow_le_pow_left₀ (hν' c) (hst c hc) 2)
  linarith
theorem sqrt_sum_sq_secondOrder_le {ι : Type} {s : Finset ι} {T ε m : ι → ℝ} {G δ M Lr : ℝ} (hLr : 1 ≤ Lr)
    (hT0 : ∀ i, 0 ≤ T i) (hε0 : ∀ i, 0 ≤ ε i) (hG : 0 ≤ G) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hTs : ∀ i, T i ≤ G) (hT4 : ∑ i ∈ s, T i ^ 4 ≤ G ^ 4) (hε4 : ∑ i ∈ s, ε i ^ 4 ≤ δ ^ 4)
    (hm2 : ∑ i ∈ s, m i ^ 2 ≤ M ^ 2) :
    Real.sqrt (∑ i ∈ s, ((Lr * T i) * (Lr * T i + ε i + m i)) ^ 2) ≤ 2 * Lr ^ 2 * G * (G + δ + M) := by
  have hx : ∀ i, ((Lr * T i) * (Lr * T i + ε i + m i)) ^ 2 ≤
      3 * (Lr ^ 4 * (T i ^ 2) ^ 2 + Lr ^ 2 * (T i ^ 2 * ε i ^ 2) + Lr ^ 2 * (T i ^ 2 * m i ^ 2)) := by
    intro i
    have e' : ∀ x y z : ℝ, (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
      intro x y z
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
    have := e' (Lr * T i * (Lr * T i)) (Lr * T i * ε i) (Lr * T i * m i)
    calc ((Lr * T i) * (Lr * T i + ε i + m i)) ^ 2
        = (Lr * T i * (Lr * T i) + Lr * T i * ε i + Lr * T i * m i) ^ 2 := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have hTε : ∑ i ∈ s, T i ^ 2 * ε i ^ 2 ≤ G ^ 2 * δ ^ 2 := by
    have hc : (∑ i ∈ s, T i ^ 2 * ε i ^ 2) ^ 2 ≤ (∑ i ∈ s, (T i ^ 2) ^ 2) * ∑ i ∈ s, (ε i ^ 2) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have e1 : ∑ i ∈ s, (T i ^ 2) ^ 2 = ∑ i ∈ s, T i ^ 4 := Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i ∈ s, (ε i ^ 2) ^ 2 = ∑ i ∈ s, ε i ^ 4 := Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2] at hc
    have h2 : (∑ i ∈ s, T i ^ 4) * ∑ i ∈ s, ε i ^ 4 ≤ G ^ 4 * δ ^ 4 :=
      mul_le_mul hT4 hε4 (Finset.sum_nonneg fun i _ => by have := hε0 i; positivity) (by positivity)
    have h3 : (∑ i ∈ s, T i ^ 2 * ε i ^ 2) ^ 2 ≤ (G ^ 2 * δ ^ 2) ^ 2 := by
      calc _ ≤ _ := hc.trans h2
        _ = _ := by ring
    exact (abs_le_of_sq_le_sq' h3 (by positivity)).2
  have hTm : ∑ i ∈ s, T i ^ 2 * m i ^ 2 ≤ G ^ 2 * M ^ 2 := by
    calc ∑ i ∈ s, T i ^ 2 * m i ^ 2 ≤ ∑ i ∈ s, G ^ 2 * m i ^ 2 := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact pow_le_pow_left₀ (hT0 i) (hTs i) 2
      _ = G ^ 2 * ∑ i ∈ s, m i ^ 2 := by rw [Finset.mul_sum]
      _ ≤ G ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hm2 (by positivity)
  have hT22 : ∑ i ∈ s, (T i ^ 2) ^ 2 ≤ G ^ 4 := by
    have e1 : ∑ i ∈ s, (T i ^ 2) ^ 2 = ∑ i ∈ s, T i ^ 4 := Finset.sum_congr rfl fun i _ => by ring
    rw [e1]
    exact hT4
  have hL2 : 1 ≤ Lr ^ 2 := one_le_pow₀ hLr
  have hsum : ∑ i ∈ s, ((Lr * T i) * (Lr * T i + ε i + m i)) ^ 2 ≤ (2 * Lr ^ 2 * G * (G + δ + M)) ^ 2 := by
    refine (Finset.sum_le_sum fun i _ => hx i).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
    have k1 : Lr ^ 4 * ∑ i ∈ s, (T i ^ 2) ^ 2 ≤ Lr ^ 4 * G ^ 4 := mul_le_mul_of_nonneg_left hT22 (by positivity)
    have k2 : Lr ^ 2 * ∑ i ∈ s, T i ^ 2 * ε i ^ 2 ≤ Lr ^ 2 * (G ^ 2 * δ ^ 2) :=
      mul_le_mul_of_nonneg_left hTε (by positivity)
    have k3 : Lr ^ 2 * ∑ i ∈ s, T i ^ 2 * m i ^ 2 ≤ Lr ^ 2 * (G ^ 2 * M ^ 2) :=
      mul_le_mul_of_nonneg_left hTm (by positivity)
    have k4 : Lr ^ 2 * (G ^ 2 * δ ^ 2) ≤ Lr ^ 4 * (G ^ 2 * δ ^ 2) := by
      have : Lr ^ 2 ≤ Lr ^ 4 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have k5 : Lr ^ 2 * (G ^ 2 * M ^ 2) ≤ Lr ^ 4 * (G ^ 2 * M ^ 2) := by
      have : Lr ^ 2 ≤ Lr ^ 4 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have k6 : G ^ 2 + δ ^ 2 + M ^ 2 ≤ (G + δ + M) ^ 2 := by
      nlinarith [mul_nonneg hG hδ, mul_nonneg hG hM, mul_nonneg hδ hM]
    have k7 : 0 ≤ Lr ^ 4 * G ^ 2 := by positivity
    have k8 := mul_le_mul_of_nonneg_left k6 k7
    have e3 : (2 * Lr ^ 2 * G * (G + δ + M)) ^ 2 = 4 * (Lr ^ 4 * G ^ 2 * (G + δ + M) ^ 2) := by ring
    rw [e3]
    nlinarith [mul_nonneg k7 (add_nonneg (add_nonneg (sq_nonneg G) (sq_nonneg δ)) (sq_nonneg M))]
  rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * Lr ^ 2 * G * (G + δ + M))]
  exact Real.sqrt_le_sqrt hsum
theorem sqrt_sqrt_pow_four {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) ^ 4 = x := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.sqrt_sqrt_pow_four <;> assumption
theorem secondOrder_bound_le {CM q ε sp sm sk smA Kc ae : ℝ} (hCM : 0 ≤ CM) (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (hsp : 0 ≤ sp) (hsmA0 : 0 ≤ smA) (hmA : smA ≤ (4 + 2 * CM) * q) (hm : sm ≤ ε) (hk : sk ≤ ε)
    (hae : ε ≤ ae) (hK : Kc = 4 * (4 + 2 * CM) + CM + 2) :
    sp + (sp + 2 * sm + 2 * sk) * smA + CM * q * (q + ε) + 2 * ε * q ≤ sp + Kc * (q * (q + ae + sp)) := by
  have h1 : (sp + 2 * sm + 2 * sk) * smA ≤ (sp + 4 * ε) * ((4 + 2 * CM) * q) := by
    have h2 : sp + 2 * sm + 2 * sk ≤ sp + 4 * ε := by linarith
    exact mul_le_mul h2 hmA hsmA0 (by positivity)
  have h3 : q * (q + ε + sp) ≤ q * (q + ae + sp) := mul_le_mul_of_nonneg_left (by linarith) hq
  have hKp : 0 ≤ Kc := by rw [hK]; positivity
  have h4 := mul_le_mul_of_nonneg_left h3 hKp
  have h5 : (sp + 4 * ε) * ((4 + 2 * CM) * q) + CM * q * (q + ε) + 2 * ε * q ≤ Kc * (q * (q + ε + sp)) := by
    rw [hK]
    have a1 : 0 ≤ q * q := by positivity
    have a2 : 0 ≤ q * ε := by positivity
    have a3 : 0 ≤ q * sp := by positivity
    have a4 : 0 ≤ CM * (q * sp) := by positivity
    have a5 : 0 ≤ CM * (q * ε) := by positivity
    have a6 : 0 ≤ CM * (q * q) := by positivity
    nlinarith
  linarith
theorem topDefect_constant_le {a Lr Cr K₁ e s D w ρ₀ Dm G K₂ : ℝ} (ha : 0 < a) (hL : 1 ≤ Lr) (hCr : 0 < Cr)
    (hK₁ : 0 ≤ K₁) (he : 0 ≤ e) (hs : 0 ≤ s) (hw : w = Real.sqrt (2 / a)) (hDm : Dm = Real.sqrt (2 / a * D))
    (hG : G = 4 * (e + Dm)) (hK₂ : K₂ = 2 * Lr ^ 2 * (6 * Lr))
    (hρ₀ : ρ₀ = Dm + K₁ * (2 * Lr ^ 2 * (6 * Lr * G) * (6 * Lr * G + Cr * s + Dm))) :
    5 / 4 * ρ₀ ≤ 4 * Real.sqrt (D / a) +
      (5 / 4 * K₁ * K₂ * (4 * (1 + w)) * (24 * Lr * (1 + w) + 4 + 5 * w + Cr + 6 * Lr * Cr + 1 + w) + 1) *
        (e + s + Real.sqrt D) * (e + Real.sqrt D) := by
  set q := Real.sqrt D with hq
  set x := Real.sqrt (D / a) with hx
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hw0 : 0 ≤ w := by rw [hw]; exact Real.sqrt_nonneg _
  have hDmq : Dm = w * q := by
    rw [hDm, hw, hq, Real.sqrt_mul (by positivity)]
  have hDx : Dm ≤ 2 * x := by
    have e1 : q = Real.sqrt a * x := by
      rw [hx, ← Real.sqrt_mul ha.le, hq]
      congr 1
      field_simp
    have e2 : w * Real.sqrt a = Real.sqrt 2 := by
      rw [hw, ← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    have e3 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    calc Dm = (w * Real.sqrt a) * x := by rw [hDmq, e1]; ring
      _ ≤ 2 * x := by
          rw [e2]
          exact mul_le_mul_of_nonneg_right e3 hx0
  set E := e + q with hE
  set H := e + s + q with hH
  have hEH : E ≤ H := by
    simp only [hE, hH]
    linarith
  have hqH : q ≤ H := by
    simp only [hH]
    linarith
  have hsH : s ≤ H := by
    simp only [hH]
    linarith
  have hG0 : 0 ≤ G := by
    rw [hG, hDmq]
    positivity
  have hG1 : G ≤ 4 * (1 + w) * E := by
    rw [hG, hDmq]
    simp only [hE]
    have p1 : 0 ≤ w * e := by positivity
    nlinarith
  set Wc : ℝ := 24 * Lr * (1 + w) + 4 + 5 * w + Cr + 6 * Lr * Cr + 1 + w with hWc
  have hS : 6 * Lr * G + Cr * s + Dm ≤ Wc * H := by
    have h1 : 6 * Lr * G ≤ 24 * Lr * (1 + w) * H := by
      have h2 := mul_le_mul_of_nonneg_left hG1 (by positivity : 0 ≤ 6 * Lr)
      have h3 : 4 * (1 + w) * E ≤ 4 * (1 + w) * H := mul_le_mul_of_nonneg_left hEH (by positivity)
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 6 * Lr)
      calc 6 * Lr * G ≤ 6 * Lr * (4 * (1 + w) * H) := h2.trans h4
        _ = _ := by ring
    have h5 : Cr * s ≤ Cr * H := mul_le_mul_of_nonneg_left hsH hCr.le
    have h6 : Dm ≤ w * H := by
      rw [hDmq]
      exact mul_le_mul_of_nonneg_left hqH hw0
    have h7 : 0 ≤ (4 + 5 * w + 6 * Lr * Cr + 1) * H := by positivity
    have e1 : Wc * H = 24 * Lr * (1 + w) * H + Cr * H + w * H + (4 + 5 * w + 6 * Lr * Cr + 1) * H := by
      rw [hWc]
      ring
    rw [e1]
    linarith
  have hY0 : 0 ≤ 6 * Lr * G + Cr * s + Dm := by
    rw [hDmq]
    positivity
  have hprod : G * (6 * Lr * G + Cr * s + Dm) ≤ (4 * (1 + w) * E) * (Wc * H) :=
    mul_le_mul hG1 hS hY0 (by positivity)
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  have hKK : 0 ≤ K₁ * K₂ := by positivity
  have hρ : ρ₀ = Dm + K₁ * K₂ * (G * (6 * Lr * G + Cr * s + Dm)) := by
    rw [hρ₀, hK₂]
    ring
  have h8 := mul_le_mul_of_nonneg_left hprod hKK
  have hHE : 0 ≤ H * E := by positivity
  have e9 : (5 / 4 * K₁ * K₂ * (4 * (1 + w)) * Wc + 1) * H * E =
      5 / 4 * (K₁ * K₂ * ((4 * (1 + w) * E) * (Wc * H))) + H * E := by ring
  rw [e9, hρ]
  linarith
end TopDefectAverage
set_option maxHeartbeats 3200000 in
open TopDefectAverage BlockAverages BlockLines BondHull in
theorem TopDefectAverage.topDefectAverageStatement_holds (hGaps : framingDefectsOnPatchStatement)
    (hR : criticalChainPatchRatesStatement) (hA : averagesAndLocalSizesStatement)
    (hMc : contourMeanFirstOrderStatement) (hO : gaugedOneStepComparisonStatement) :
    topDefectAverageStatement := by
  intro a θ del Ca ha hθ hθ' hd hd' hCa
  obtain ⟨LG, hGp⟩ := hGaps a θ del Ca ha hθ hθ' hd hd' hCa
  obtain ⟨LR, hRt⟩ := hR a θ del Ca ha hθ hθ' hd hd' hCa
  obtain ⟨CM, cM, hCM, hcM, hMean⟩ := hMc
  obtain ⟨CO, cO, hCO, hcO, hOne⟩ := hO
  refine ⟨max (max LG LR) 5, fun L hLodd hLL C₁ hC₁ => ?_⟩
  have hLG : LG ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLL
  have hLRl : LR ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLL
  have hL5 : 5 ≤ L := le_trans (le_max_right _ _) hLL
  obtain ⟨CG, cG, hCG, hcG, hGp'⟩ := hGp L hLodd hLG C₁ hC₁
  obtain ⟨Cr, cr, hCr, hcr, hRt'⟩ := hRt L hLodd hLRl C₁ hC₁
  have hLr5 : (5 : ℝ) ≤ L := by exact_mod_cast hL5
  have hLp : (0 : ℝ) < L := by linarith
  set bL : ℝ := min (min cM cO) (1 / 4) with hbL
  have hbLp : 0 < bL := lt_min (lt_min hcM hcO) (by norm_num)
  set bA : ℝ := bL / (6 * (L : ℝ) ^ 2) with hbA
  have hbAp : 0 < bA := by positivity
  set w : ℝ := Real.sqrt (2 / a) with hw
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  set K₁ : ℝ := 4 * (4 + 2 * CM) + CM + 2 with hK₁
  have hK₁p : 0 < K₁ := by positivity
  set K₂ : ℝ := 2 * (L : ℝ) ^ 2 * (6 * L) with hK₂
  refine ⟨5 / 4 * K₁ * K₂ * (4 * (1 + w)) * (24 * (L : ℝ) * (1 + w) + 4 + 5 * w + Cr + 6 * (L : ℝ) * Cr + 1 + w) + 1,
    min cG (bA / (3 * CG)), by positivity, lt_min hcG (by positivity), ?_⟩
  intro e0 he0 he0c
  have hec0 : e0 ≤ cG := he0c.trans (min_le_left _ _)
  obtain ⟨σG, hσG, hGd⟩ := hGp' e0 he0 hec0
  refine ⟨min σG (min cr (min (bA / (3 * CG)) (bL / Cr))),
    lt_min hσG (lt_min hcr (lt_min (by positivity) (by positivity))), ?_⟩
  intro F m S hFL hamb hm hreg s V v hs hsσ hcold hv U hcrit X k z hXn hz hterms γ hγ b hb
  subst hFL
  have hodd : Odd F.blockSide := hLodd
  have hLR1 : (1 : ℝ) ≤ F.blockSide := by linarith
  have hsG : s ≤ σG := hsσ.trans (min_le_left _ _)
  have hscr : s ≤ cr := hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsA : CG * s ≤ bA / 3 := by
    have h1 : s ≤ bA / (3 * CG) :=
      hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hsL : Cr * s ≤ bL := by
    have h1 : s ≤ bL / Cr := hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    rw [le_div_iff₀ hCr] at h1
    linarith
  have he0A : CG * e0 ≤ bA / 3 := by
    have h1 : e0 ≤ bA / (3 * CG) := he0c.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  obtain ⟨he, -⟩ := closedOrthant_spec hreg (by omega) z
  obtain ⟨hlev, -⟩ := hRt' F m S rfl hamb hm hreg s V v hs hscr hcold U hcrit z hz
  choose! Er er hEr0 her0 hEr4 her4 hm2 hrt using hlev
  obtain ⟨-, g2, -, g4, g5⟩ := hGd F m S rfl hamb hm hreg s V v hs hsG hcold hv U hcrit X k z hXn hz hterms γ
    (hγ.trans (min_le_left _ _))
  have hγA : CG * quarticDefectNorm S z (criticalFieldChain S V v U) X
      (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k γ) 0 ≤ bA / 3 := by
    have h1 := hγ.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  set W := criticalFieldChain S V v U with hW
  set kW := criticalGauge S V U with hkW
  set Γ := pinnedGaugeOfBase W kW X k γ with hΓ
  set P := patchCells S z with hP
  set D := relativeEnergy a S z W kW X k Γ with hD
  set e := quarticDefectNorm S z W X Γ 0 with hedef
  have he0' : 0 ≤ e := Real.sqrt_nonneg _
  have hbp : ∀ j, j ≤ F.top → innerBonds P j = patchInnerBonds S z j :=
    fun j hj => innerBonds_patchCells hamb hodd he hj
  set Dm := Real.sqrt (2 / a * D) with hDm
  have hDm0 : 0 ≤ Dm := Real.sqrt_nonneg _
  set G : ℝ := 4 * (e + Dm) with hG
  have hG0 : 0 ≤ G := by positivity
  set G₀ : ℝ := CG * (e + e0 + s) with hG₀
  have hG₀b : G₀ ≤ bA := by
    have e1 : G₀ = CG * e + CG * e0 + CG * s := by rw [hG₀]; ring
    rw [e1]
    linarith
  have hG₀0 : 0 ≤ G₀ := by positivity
  set gp : (j : ℕ) → F.Site j → Fin 4 → ℝ := fun j x i => _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X Γ j x i) with hgp
  have hgp0 : ∀ j x i, 0 ≤ gp j x i := fun j x i => _root_.YangMills.Construction.BondHull.distFromOne_nonneg _
  have hS0 : ∀ j, 0 ≤ ∑ b ∈ innerBonds P j, gp j b.1 b.2 ^ 4 := fun j =>
    Finset.sum_nonneg fun b _ => pow_nonneg (_root_.YangMills.Construction.BondHull.distFromOne_nonneg _) 4
  have hq : ∀ j, j < F.top →
      Real.sqrt (Real.sqrt (∑ b ∈ innerBonds P j, gp j b.1 b.2 ^ 4)) = quarticDefectNorm S z W X Γ j := by
    intro j hj
    rw [hbp j hj.le]
    rfl
  have hsum1 : ∀ j, j < F.top → ∑ b ∈ innerBonds P j, gp j b.1 b.2 ^ 4 ≤ G ^ 4 := by
    intro j hj
    have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg _) ((hq j hj).le.trans (g5 j hj)) 4
    rwa [sqrt_sqrt_pow_four (hS0 j)] at h1
  have hsum2 : ∀ j, j < F.top → ∑ b ∈ innerBonds P j, gp j b.1 b.2 ^ 4 ≤ G₀ ^ 4 := by
    intro j hj
    have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg _) ((hq j hj).le.trans (g2 j hj)) 4
    rwa [sqrt_sqrt_pow_four (hS0 j)] at h1
  have hD0 : 0 ≤ D := by
    simp only [hD, relativeEnergy]
    exact add_nonneg (Finset.sum_nonneg fun p _ => by positivity)
      (mul_nonneg ha.le (Finset.sum_nonneg fun j' _ => Finset.sum_nonneg fun c _ => by positivity))
  set ρ₀ : ℝ := Dm + K₁ * (2 * (F.blockSide : ℝ) ^ 2 * (6 * F.blockSide * G) *
    (6 * F.blockSide * G + Cr * s + Dm)) with hρ₀
  have hρ₀0 : 0 ≤ ρ₀ := by positivity
  have h6L : 6 * (F.blockSide : ℝ) ^ 2 * bA = bL := by
    rw [hbA]
    field_simp
  have hlevel : ∀ j, j < F.top → ∃ Rf : F.Site (j + 1) × Fin 4 → ℝ, (∀ c, 0 ≤ Rf c) ∧
      Real.sqrt (∑ c ∈ innerBonds P (j + 1), Rf c ^ 2) ≤ ρ₀ ∧
      ∀ c ∈ innerBonds P (j + 1), ‖_root_.YangMills.Construction.BlockAverages.adjointAction (GaugeMap.frameChange S V z (baseSite c.1))⁻¹
          (pureComponent ((framedUpperField W kW X k Γ j c.1 c.2 * (W (j + 1) c.1 c.2)⁻¹ : UnitQuaternion) :
            ℍ[ℝ])) -
        bondLineMean (framedPureDefect S V z W X Γ j) c‖ ≤ Rf c := by
    intro j hj
    have hj1 : j + 1 ≤ F.top := hj
    obtain ⟨-, -, -, T₀, hT0, hTb, -, hT1, hT2, -⟩ := hA F P j (gp j) hodd hj1 (hgp0 j)
    have htop : ∀ (B : ℝ), 0 ≤ B → ∑ b ∈ innerBonds P j, gp j b.1 b.2 ^ 4 ≤ B ^ 4 →
        ∀ y, T₀ y ≤ 6 * F.blockSide * B := by
      intro B hB0 hB y
      have h2 := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 4 * (3 * (F.blockSide : ℝ)) ^ 4)
      have h3 : 4 * (3 * (F.blockSide : ℝ)) ^ 4 * B ^ 4 ≤ (6 * (F.blockSide : ℝ) * B) ^ 4 := by
        have h4 : 0 ≤ ((F.blockSide : ℝ) * B) ^ 4 := by positivity
        have e1 : 4 * (3 * (F.blockSide : ℝ)) ^ 4 * B ^ 4 = 324 * ((F.blockSide : ℝ) * B) ^ 4 := by ring
        have e2 : (6 * (F.blockSide : ℝ) * B) ^ 4 = 1296 * ((F.blockSide : ℝ) * B) ^ 4 := by ring
        rw [e1, e2]
        linarith
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) ((hT1 y).trans (h2.trans h3))
    have hT4 : ∑ c ∈ innerBonds P (j + 1), T₀ c.1 ^ 4 ≤ (6 * (F.blockSide : ℝ) * G) ^ 4 := by
      refine hT2.trans ?_
      have h2 := mul_le_mul_of_nonneg_left (hsum1 j hj) (by positivity : 0 ≤ 16 * (3 * (F.blockSide : ℝ)) ^ 4)
      refine h2.trans (le_of_eq ?_)
      ring
    have hLT : ∀ y, (F.blockSide : ℝ) * T₀ y ≤ bL := by
      intro y
      have h1 := htop G₀ hG₀0 (hsum2 j hj) y
      have h2 : 6 * (F.blockSide : ℝ) * G₀ ≤ 6 * (F.blockSide : ℝ) * bA :=
        mul_le_mul_of_nonneg_left hG₀b (by positivity)
      have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hLp.le
      calc (F.blockSide : ℝ) * T₀ y ≤ (F.blockSide : ℝ) * (6 * (F.blockSide : ℝ) * bA) := h3
        _ = 6 * (F.blockSide : ℝ) ^ 2 * bA := by ring
        _ = bL := h6L
    have hbM : bL ≤ cM := (min_le_left _ _).trans (min_le_left _ _)
    have hbO : bL ≤ cO := (min_le_left _ _).trans (min_le_right _ _)
    have hb4 : bL ≤ 1 / 4 := min_le_right _ _
    have hec : ∀ c ∈ innerBonds P (j + 1), er j c ≤ Cr * s := by
      intro c hc
      have h1 := Finset.single_le_sum (f := fun c => er j c ^ 4)
        (fun c _ => by have := her0 j hj c; positivity) hc
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) (h1.trans (her4 j hj))
    set pm : F.Site (j + 1) × Fin 4 → ℝ := fun c => _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfitDefect W kW X k Γ j c) with hpm
    have hpm0 : ∀ c, 0 ≤ pm c := fun c => _root_.YangMills.Construction.BondHull.distFromOne_nonneg _
    have hpm2 : ∑ c ∈ innerBonds P (j + 1), pm c ^ 2 ≤ Dm ^ 2 := by
      rw [hDm, Real.sq_sqrt (mul_nonneg (by positivity) hD0), hbp (j + 1) hj]
      exact g4 j hj
    set Q : F.Site (j + 1) × Fin 4 → ℝ := fun c =>
      ((F.blockSide : ℝ) * T₀ c.1) * ((F.blockSide : ℝ) * T₀ c.1 + |er j c| + pm c) with hQ
    have hQ0 : ∀ c, 0 ≤ Q c := fun c =>
      mul_nonneg (mul_nonneg hLp.le (hT0 _))
        (add_nonneg (add_nonneg (mul_nonneg hLp.le (hT0 _)) (abs_nonneg _)) (hpm0 c))
    have hQ2 : Real.sqrt (∑ c ∈ innerBonds P (j + 1), Q c ^ 2) ≤
        2 * (F.blockSide : ℝ) ^ 2 * (6 * F.blockSide * G) * (6 * F.blockSide * G + Cr * s + Dm) := by
      refine sqrt_sum_sq_secondOrder_le (s := innerBonds P (j + 1)) (T := fun c => T₀ c.1)
        (ε := fun c => |er j c|) (m := pm)
        hLR1 (fun c => hT0 _) (fun c => abs_nonneg _) (by positivity) (by positivity) hDm0
        (fun c => htop G hG0 (hsum1 j hj) c.1) hT4 ?_ hpm2
      refine le_trans (le_of_eq ?_) (her4 j hj)
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [abs_of_nonneg (her0 j hj c)]
    refine ⟨fun c => pm c + K₁ * Q c, fun c => add_nonneg (hpm0 c) (mul_nonneg hK₁p.le (hQ0 c)), ?_, ?_⟩
    · have h1 := sqrt_sum_sq_add_le (s := innerBonds P (j + 1)) (f := pm) (g := fun c => K₁ * Q c)
        (fun c _ => hpm0 c) (fun c _ => mul_nonneg hK₁p.le (hQ0 c))
      have h2 : Real.sqrt (∑ c ∈ innerBonds P (j + 1), pm c ^ 2) ≤ Dm := by
        rw [← Real.sqrt_sq hDm0]
        exact Real.sqrt_le_sqrt hpm2
      have h3 : Real.sqrt (∑ c ∈ innerBonds P (j + 1), (K₁ * Q c) ^ 2) =
          K₁ * Real.sqrt (∑ c ∈ innerBonds P (j + 1), Q c ^ 2) := by
        have e1 : ∑ c ∈ innerBonds P (j + 1), (K₁ * Q c) ^ 2 = K₁ ^ 2 * ∑ c ∈ innerBonds P (j + 1), Q c ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
        rw [e1, Real.sqrt_mul (by positivity), Real.sqrt_sq hK₁p.le]
      have h4 := mul_le_mul_of_nonneg_left hQ2 hK₁p.le
      rw [hρ₀]
      linarith
    · intro c hc
      set t := T₀ c.1 with ht
      have ht0 : 0 ≤ t := hT0 _
      set ε := er j c with hε
      have hε0 : 0 ≤ ε := her0 j hj c
      have hεb : ε ≤ bL := (hec c hc).trans hsL
      have hLt := hLT c.1
      have hB := hTb c hc
      have hr := hrt j hj
      obtain ⟨m0, m1, m2⟩ := hMean F j (gaugedChainFields X Γ j) (W j) c t ε hodd hj1 ht0 hε0
        (hLt.trans hbM) (hεb.trans hbM) (le_of_mem_twoBlockHull hodd hj1 hB) (hr.contour_le c hc)
      have hN := (hOne F j (gaugedChainFields X Γ j) (W j) (kW (j + 1)) (framedUpperField W kW X k Γ j)
        (W (j + 1)) c t ε hodd hj1 ht0 hε0 (hLt.trans hbO) (hεb.trans hbO) hB (hr.contour_le c hc)).1
      have hneT : gaugedContourAverage (gaugedChainFields X Γ j)
          (balancedLinks (gaugedChainFields X Γ j) (W j) (kW (j + 1))) c ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hN
        linarith
      have hfd : patchFrame S V z (_root_.YangMills.Construction.BlockAverages.refineSite c.1) = GaugeMap.frameChange S V z (baseSite c.1) := by
        unfold patchFrame
        rw [baseSite_refineSite _ hj1]
      have hv := norm_pureComponent_upper_sub_le hodd (gaugedChainFields X Γ j) (W j) (kW (j + 1))
        (framedUpperField W kW X k Γ j) (W (j + 1)) c t ε
        (CM * ((F.blockSide : ℝ) * t) * ((F.blockSide : ℝ) * t + ε)) (patchFrame S V z)
        (GaugeMap.frameChange S V z (baseSite c.1)) ht0 hε0
        hneT (hr.average_le c hc).1 m1
        (fun h hh π r hrL => by
          have := hr.bondLine_le c hc h hh π r hrL
          rwa [hfd] at this)
        (fun h hh r hrL => hB.2 h hh r (Finset.mem_range.2 hrL))
      have hsp : _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit (gaugedChainFields X Γ j)
            (balancedLinks (gaugedChainFields X Γ j) (W j) (kW (j + 1)))
            (framedUpperField W kW X k Γ j) c * (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)⁻¹) = pm c := rfl
      rw [hsp] at hv
      refine hv.trans ?_
      have hmm := hr.misfit_le c hc
      have hkk := hr.bondGauge_le c hc
      have hq0 : 0 ≤ (F.blockSide : ℝ) * t := mul_nonneg hLp.le ht0
      have hq1 : (F.blockSide : ℝ) * t + ε ≤ 2 := by linarith
      have hE0 : CM * ((F.blockSide : ℝ) * t) * ((F.blockSide : ℝ) * t + ε) ≤ 2 * CM * ((F.blockSide : ℝ) * t) := by
        have : 0 ≤ CM * ((F.blockSide : ℝ) * t) := by positivity
        nlinarith
      have hmA : _root_.YangMills.Construction.BlockAverages.distFromOne (relativeContourMean (gaugedChainFields X Γ j) (W j) c) ≤
          (4 + 2 * CM) * ((F.blockSide : ℝ) * t) := by
        have h2 : _root_.YangMills.Construction.BlockAverages.distFromOne (relativeContourMean (gaugedChainFields X Γ j) (W j) c) ≤
            4 * ‖parallelAverage (W j) (pureGap (gaugedChainFields X Γ j) (W j)) c‖ +
              CM * ((F.blockSide : ℝ) * t) * ((F.blockSide : ℝ) * t + ε) := m2
        nlinarith
      exact secondOrder_bound_le hCM.le hq0 hε0 (hpm0 c) (_root_.YangMills.Construction.BondHull.distFromOne_nonneg _) hmA hmm hkk (le_abs_self _) hK₁
  set f0 := framedPureDefect S V z W X Γ 0 with hf0
  set ν : (j : ℕ) → F.Site j → Fin 4 → ℝ := fun j x i =>
    ‖framedPureDefect S V z W X Γ j x i - iteratedBlockAverage f0 j x i‖ with hν
  have hν0 : ∀ j x i, 0 ≤ ν j x i := fun j x i => norm_nonneg _
  have hL5' : 5 ≤ F.blockSide := hL5
  have hstep : ∀ j, j < F.top → ∀ (Rf : F.Site (j + 1) × Fin 4 → ℝ) (A : F.Site (j + 1) × Fin 4 → ℍ[ℝ]),
      ∀ c, ‖A c - bondLineMean (framedPureDefect S V z W X Γ j) c‖ ≤ Rf c →
        ‖A c - bondLineMean (iteratedBlockAverage f0 j) c‖ ≤ lineBlockAverage (ν j) c + Rf c := by
    intro j hj Rf A c h1
    have e1 : A c - bondLineMean (iteratedBlockAverage f0 j) c =
        (A c - bondLineMean (framedPureDefect S V z W X Γ j) c) +
        (bondLineMean (framedPureDefect S V z W X Γ j) c - bondLineMean (iteratedBlockAverage f0 j) c) := by abel
    rw [e1, bondLineMean_sub]
    have h2 := norm_bondLineMean_le hodd
      (fun x i => framedPureDefect S V z W X Γ j x i - iteratedBlockAverage f0 j x i) c
    have h3 := norm_add_le (A c - bondLineMean (framedPureDefect S V z W X Γ j) c)
      (bondLineMean (fun x i => framedPureDefect S V z W X Γ j x i - iteratedBlockAverage f0 j x i) c)
    have h4 : lineBlockAverage (fun x i => ‖framedPureDefect S V z W X Γ j x i - iteratedBlockAverage f0 j x i‖) c =
        lineBlockAverage (ν j) c := rfl
    linarith
  have hnu : ∀ j, j < F.top → Real.sqrt (∑ b ∈ innerBonds P j, ν j b.1 b.2 ^ 2) ≤ 5 / 4 * ρ₀ := by
    intro j
    induction j with
    | zero =>
      intro _
      have : ∑ b ∈ innerBonds P 0, ν 0 b.1 b.2 ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun b _ => ?_
        have e1 : ν 0 b.1 b.2 = 0 := by
          show ‖framedPureDefect S V z W X Γ 0 b.1 b.2 - f0 b.1 b.2‖ = 0
          rw [hf0, sub_self, norm_zero]
        rw [e1]
        norm_num
      rw [this, Real.sqrt_zero]
      positivity
    | succ j ih =>
      intro hj
      have hj' : j < F.top := by omega
      obtain ⟨Rf, hR0, hR2, hRb⟩ := hlevel j hj'
      have hne : j ≠ F.depth := by
        have : F.top = F.depth + 1 := rfl
        omega
      have hup : framedUpperField W kW X k Γ j = gaugedChainFields X Γ (j + 1) := by
        simp only [framedUpperField, dif_neg hne]
      have h1 := sqrt_sum_sq_le_of_le_lineBlockAverage (j := j) (P := P) (ν := ν j)
        (ν' := fun c => ν (j + 1) c.1 c.2) (R := Rf) (B := 5 / 4 * ρ₀)
        (ρ := ρ₀) hA hodd hL5' hj' (hν0 j) (fun c => norm_nonneg _) hR0 (by positivity) (ih hj') hR2
        (fun c hc => by
          have h2 := hRb c hc
          rw [hup] at h2
          exact hstep j hj' Rf (fun c' => framedPureDefect S V z W X Γ (j + 1) c'.1 c'.2) c h2)
      have e2 : 1 / 5 * (5 / 4 * ρ₀) + ρ₀ = 5 / 4 * ρ₀ := by ring
      rw [e2] at h1
      exact h1
  obtain ⟨Rf, hR0, hR2, hRb⟩ := hlevel F.depth (Nat.lt_succ_self _)
  have hb' : b ∈ innerBonds P (F.depth + 1) := by
    rw [hbp _ (le_refl _)]
    exact hb
  have h1 := sqrt_sum_sq_le_of_le_lineBlockAverage (j := F.depth) (P := P) (ν := ν F.depth)
    (ν' := fun c => ‖_root_.YangMills.Construction.BlockAverages.adjointAction (GaugeMap.frameChange S V z (baseSite c.1))⁻¹
      (pureComponent ((topDefect W kW X k Γ c.1 c.2 : UnitQuaternion) : ℍ[ℝ])) -
      iteratedBlockAverage f0 F.top c.1 c.2‖) (R := Rf) (B := 5 / 4 * ρ₀) (ρ := ρ₀) hA hodd hL5' (le_refl _)
    (hν0 F.depth) (fun c => norm_nonneg _) hR0 (by positivity) (hnu F.depth (Nat.lt_succ_self _)) hR2
    (fun c hc => hstep F.depth (Nat.lt_succ_self _) Rf
      (fun c' => _root_.YangMills.Construction.BlockAverages.adjointAction (GaugeMap.frameChange S V z (baseSite c'.1))⁻¹
        (pureComponent ((topDefect W kW X k Γ c'.1 c'.2 : UnitQuaternion) : ℍ[ℝ]))) c (hRb c hc))
  have e2 : 1 / 5 * (5 / 4 * ρ₀) + ρ₀ = 5 / 4 * ρ₀ := by ring
  rw [e2] at h1
  have h2 := Finset.single_le_sum (f := fun c : F.Site (F.depth + 1) × Fin 4 =>
    ‖_root_.YangMills.Construction.BlockAverages.adjointAction (GaugeMap.frameChange S V z (baseSite c.1))⁻¹
      (pureComponent ((topDefect W kW X k Γ c.1 c.2 : UnitQuaternion) : ℍ[ℝ])) -
      iteratedBlockAverage f0 F.top c.1 c.2‖ ^ 2) (fun c _ => by positivity) hb'
  have h3 := (Real.le_sqrt_of_sq_le h2).trans h1
  refine h3.trans ?_
  exact topDefect_constant_le ha hLR1 hCr hK₁p.le he0' hs.le hw hDm hG hK₂ hρ₀
end YangMills.Construction
end

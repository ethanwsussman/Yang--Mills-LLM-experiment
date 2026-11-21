import YangMills.Construction.ColdChainAtEveryLevel.ChangesOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.HolonomiesOnTheHullOfABond
import YangMills.Construction.ColdChainAtEveryLevel.MeanOfTheContoursOfABond
import YangMills.Construction.ColdChainAtEveryLevel.OneStepOfAFraming
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.GaugedOneStep
open BlockAverages LatticePaths BlockLines LatticeFractionalIntegration
variable {F : BlockFrame} {j : ℕ}
def relLink (X R : F.GaugeField j) (x : F.Site j) (st : PathStep) : UnitQuaternion :=
  linkValue X x st * (linkValue R x st)⁻¹
def relHolonomy (X R : F.GaugeField j) (x : F.Site j) (l : List PathStep) : UnitQuaternion :=
  pathHolonomy X x l * (pathHolonomy R x l)⁻¹
theorem stepDisplacement_eq_siteOfCoords (st : PathStep) :
    BlockAverages.stepDisplacement (F := F) j st = siteOfCoords j (FlatPairing.stepDisplacement st) := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.stepDisplacement_eq_siteOfCoords <;> assumption
theorem distFromOne_relHolonomy_le (X R : F.GaugeField j) (x₀ : F.Site j) (p : Lattice4 → Prop) (t : ℝ)
    (ht0 : 0 ≤ t)
    (ht : ∀ u st, p u → p (u + FlatPairing.stepDisplacement st) →
      normSubOne (relLink X R (x₀ + siteOfCoords j u) st) ≤ t) :
    ∀ (l : List PathStep) (u : Lattice4), AllAlong p u l →
      normSubOne (relHolonomy X R (x₀ + siteOfCoords j u) l) ≤ l.length * t := by apply _root_.YangMills.Construction.BondHull.distFromOne_pathRatio_le <;> assumption
theorem distFromOne_relLink_le_of_mem (X R : F.GaugeField j) (x₀ : F.Site j) (H : Set Lattice4) (t : ℝ)
    (hcl : ∀ a ∈ H, ∀ k, a + basisVector k ∈ H →
      normSubOne (X (x₀ + siteOfCoords j a) k * (R (x₀ + siteOfCoords j a) k)⁻¹) ≤ t)
    (u : Lattice4) (st : PathStep) (hu : u ∈ H) (hv : u + FlatPairing.stepDisplacement st ∈ H) :
    normSubOne (relLink X R (x₀ + siteOfCoords j u) st) ≤ t := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.normSubOne_linkDiscrepancy_le <;> assumption
theorem bound_on_twoBlockHull (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {f : F.Site j → Fin 4 → ℝ}
    {b : F.Site (j + 1) × Fin 4} {t : ℝ} (hB : BoundedOnAdjacentBlocks f b t) :
    ∀ a ∈ FlatPairing.twoBlockHull F.blockSide b.2, ∀ k, a + basisVector k ∈ FlatPairing.twoBlockHull F.blockSide b.2 →
      f (refineSite b.1 + siteOfCoords j a) k ≤ t := by apply _root_.YangMills.Construction.BondHull.le_of_mem_twoBlockHull <;> assumption
theorem norm_contourSum_le (hodd : Odd F.blockSide) (φ : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]) (B : ℝ)
    (hB : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖φ h π‖ ≤ B) :
    ‖(1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), φ h π‖ ≤ B := by apply _root_.YangMills.Construction.BondHull.norm_smul_sum_perm_le <;> assumption
theorem contourSum_const (hodd : Odd F.blockSide) (q : ℍ[ℝ]) :
    (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), q = q := by apply _root_.YangMills.Construction.BondHull.smul_sum_perm_const <;> assumption
theorem polarUnit_conj (g g' : UnitQuaternion) {q : ℍ[ℝ]} (h : q ≠ 0) :
    polarUnit ((g : ℍ[ℝ]) * q * ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ])) = g * polarUnit q * g'⁻¹ := by apply _root_.YangMills.Construction.GaugeMotions.polarUnit_coe_mul_mul_coe_inv <;> assumption
theorem distFromOne_le_pure (g : UnitQuaternion) :
    normSubOne g ≤ ‖pureComponent (g : ℍ[ℝ])‖ + normSubOne g ^ 2 / 2 := by
  have h1 := _root_.YangMills.Construction.BlockAverages.distFromOne_sq g
  have e : (g : ℍ[ℝ]) - 1 = ((((g : ℍ[ℝ]).re - 1 : ℝ)) : ℍ[ℝ]) + pureComponent (g : ℍ[ℝ]) := by
    conv_lhs => rw [← re_add_pureComponent (g : ℍ[ℝ])]
    push_cast
    abel
  have h2 : normSubOne g ≤ |(g : ℍ[ℝ]).re - 1| + ‖pureComponent (g : ℍ[ℝ])‖ := by
    unfold normSubOne
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Quaternion.norm_coe, Real.norm_eq_abs]
  have h3 : |(g : ℍ[ℝ]).re - 1| = normSubOne g ^ 2 / 2 := by
    have h4 : (g : ℍ[ℝ]).re - 1 = - (normSubOne g ^ 2 / 2) := by rw [h1]; ring
    rw [h4, abs_neg, abs_of_nonneg (by positivity)]
  linarith
theorem quotient_factorization (t' r' ky ky' uT uR : UnitQuaternion) :
    t' * r'⁻¹ = (t' * (ky * uT * ky'⁻¹)⁻¹ * (r' * (ky * uR * ky'⁻¹)⁻¹)⁻¹) *
      ((r' * (ky * uR * ky'⁻¹)⁻¹) * (ky * (uT * uR⁻¹) * ky⁻¹) * (r' * (ky * uR * ky'⁻¹)⁻¹)⁻¹) := by
  group
theorem le_of_pure_estimates {P Q E τ ε g p CM : ℝ} (hτ0 : 0 ≤ τ) (hε0 : 0 ≤ ε) (hτ : τ ≤ 1) (hε : ε ≤ 1)
    (hCM : 0 ≤ CM) (hE : E = CM * τ * (τ + ε)) (hQ0 : 0 ≤ Q) (hQP : Q ≤ P) (hP : P ≤ τ) (hp : p ≤ Q + E)
    (hg : g ≤ 4 * Q + E) (hg0 : 0 ≤ g) (hgp : g ≤ p + g ^ 2 / 2) :
    g ≤ P + (CM + (4 + 2 * CM) ^ 2 / 2) * τ * (τ + ε) := by
  have h1 : E ≤ 2 * CM * τ := by
    rw [hE]
    have : τ + ε ≤ 2 := by linarith
    have h2 : 0 ≤ CM * τ := by positivity
    nlinarith
  have h2 : g ≤ (4 + 2 * CM) * τ := by nlinarith
  have h3 : g ^ 2 ≤ ((4 + 2 * CM) * τ) ^ 2 := pow_le_pow_left₀ hg0 h2 2
  have h4 : ((4 + 2 * CM) * τ) ^ 2 ≤ (4 + 2 * CM) ^ 2 * τ * (τ + ε) := by
    have : 0 ≤ (4 + 2 * CM) ^ 2 * τ := by positivity
    nlinarith
  rw [hE] at hp
  nlinarith
theorem gaugedOneStepComparison (hM : contourMeanFirstOrderStatement) : gaugedOneStepComparisonStatement := by
  obtain ⟨CM, cM, hCM, hcM, hMain⟩ := hM
  refine ⟨CM + (4 + 2 * CM) ^ 2 / 2, min cM (1 / 12), by positivity, lt_min hcM (by norm_num), ?_⟩
  intro F j T R kR T' R' b t ε hodd hj ht0 hε0 hτ hε hB hsp
  have hτ1 : (F.blockSide : ℝ) * t ≤ 1 / 12 := hτ.trans (min_le_right _ _)
  have hε1 : ε ≤ 1 / 12 := hε.trans (min_le_right _ _)
  have hLpos : 1 ≤ F.blockSide := hodd.pos
  have hcl := bound_on_twoBlockHull hodd hj hB
  obtain ⟨m0, m1, m2⟩ := hMain F j T R b t ε hodd hj ht0 hε0 (hτ.trans (min_le_left _ _))
    (hε.trans (min_le_left _ _)) hcl hsp
  obtain ⟨uR, huR⟩ : ∃ uR : UnitQuaternion, uR = polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage R b) := ⟨_, rfl⟩
  rw [← huR] at hsp
  have hRc : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2) : UnitQuaternion) : ℍ[ℝ]) -
        (uR : ℍ[ℝ])‖ ≤ ε := by
    intro h hh π
    have e : ((pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2) : UnitQuaternion) : ℍ[ℝ]) -
        (uR : ℍ[ℝ]) =
        (((pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2) * uR⁻¹ : UnitQuaternion) :
          ℍ[ℝ]) - 1) * (uR : ℍ[ℝ]) := by
      rw [sub_mul, Submonoid.coe_mul, mul_assoc, one_mul]
      congr 1
      have : ((uR⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (uR : ℍ[ℝ]) = ((uR⁻¹ * uR : UnitQuaternion) : ℍ[ℝ]) := rfl
      rw [this, inv_mul_cancel]
      simp
    rw [e, norm_mul, norm_coe_unitQuaternion, mul_one]
    exact hsp h hh π
  have hTc : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy T (refineSite b.1) (bondContour F.blockSide h π b.2) : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2) : UnitQuaternion) : ℍ[ℝ])‖ ≤
          5 * ((F.blockSide : ℝ) * t) := by
    intro h hh π
    obtain ⟨hp, -⟩ := bondContour_spec (h := h) π b.2 hLpos hh
    have h1 := _root_.YangMills.Construction.GaugedOneStep.distFromOne_relHolonomy_le T R (refineSite b.1)
      (fun v => v ∈ FlatPairing.twoBlockHull F.blockSide b.2) t ht0
      (_root_.YangMills.Construction.GaugedOneStep.distFromOne_relLink_le_of_mem T R (refineSite b.1) (FlatPairing.twoBlockHull F.blockSide b.2) t hcl)
      _ 0 hp
    rw [_root_.YangMills.Construction.BlockAverages.siteOfCoords_zero, add_zero] at h1
    have h2 : ((bondContour F.blockSide h π b.2).length : ℝ) ≤ 5 * F.blockSide := by
      exact_mod_cast length_bondContour_le π b.2 hLpos hh
    have e : ((pathHolonomy T (refineSite b.1) (bondContour F.blockSide h π b.2) : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2) : UnitQuaternion) : ℍ[ℝ]) =
        (((relHolonomy T R (refineSite b.1) (bondContour F.blockSide h π b.2) : UnitQuaternion) : ℍ[ℝ]) - 1) *
          ((pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2) : UnitQuaternion) : ℍ[ℝ]) := by
      unfold relHolonomy
      rw [sub_mul, Submonoid.coe_mul, mul_assoc, one_mul]
      congr 1
      have : (((pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2))⁻¹ : UnitQuaternion) :
          ℍ[ℝ]) *
          ((pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2) : UnitQuaternion) : ℍ[ℝ]) =
          (((pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2))⁻¹ *
            pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2) : UnitQuaternion) : ℍ[ℝ]) := rfl
      rw [this, inv_mul_cancel]
      simp
    rw [e, norm_mul, norm_coe_unitQuaternion, mul_one]
    unfold normSubOne at h1
    nlinarith
  have hqR : ‖_root_.YangMills.Construction.BlockAverages.contourAverage R b - (uR : ℍ[ℝ])‖ ≤ ε := by
    have e : _root_.YangMills.Construction.BlockAverages.contourAverage R b - (uR : ℍ[ℝ]) = (1 / (24 * (F.blockSide : ℝ) ^ 4)) •
        ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
          (((pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2) : UnitQuaternion) : ℍ[ℝ]) -
            (uR : ℍ[ℝ])) := by
      simp only [Finset.sum_sub_distrib, smul_sub]
      rw [contourSum_const hodd]
      rfl
    rw [e]
    exact norm_contourSum_le hodd _ ε hRc
  have hqT : ‖_root_.YangMills.Construction.BlockAverages.contourAverage T b - (uR : ℍ[ℝ])‖ ≤ 5 * ((F.blockSide : ℝ) * t) + ε := by
    have e : _root_.YangMills.Construction.BlockAverages.contourAverage T b - (uR : ℍ[ℝ]) = (1 / (24 * (F.blockSide : ℝ) ^ 4)) •
        ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
          (((pathHolonomy T (refineSite b.1) (bondContour F.blockSide h π b.2) : UnitQuaternion) : ℍ[ℝ]) -
            (uR : ℍ[ℝ])) := by
      simp only [Finset.sum_sub_distrib, smul_sub]
      rw [contourSum_const hodd]
      rfl
    rw [e]
    refine norm_contourSum_le hodd _ _ fun h hh π => ?_
    have := norm_sub_le_norm_sub_add_norm_sub
      ((pathHolonomy T (refineSite b.1) (bondContour F.blockSide h π b.2) : UnitQuaternion) : ℍ[ℝ])
      ((pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2) : UnitQuaternion) : ℍ[ℝ])
      (uR : ℍ[ℝ])
    linarith [hTc h hh π, hRc h hh π]
  have hnorm : ∀ q : ℍ[ℝ], ‖q - (uR : ℍ[ℝ])‖ ≤ 1 / 2 → 1 / 2 ≤ ‖q‖ := by
    intro q hq
    have h1 := norm_sub_norm_le (uR : ℍ[ℝ]) q
    rw [_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, norm_sub_rev] at h1
    linarith
  have hqT' : 1 / 2 ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage T b‖ := hnorm _ (by linarith)
  have hqR' : 1 / 2 ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage R b‖ := hnorm _ (by linarith)
  have hne : gaugedContourAverage T (balancingGauge T R) b ≠ 0 := by
    intro h0
    have h1 : ‖gaugedContourAverage T (balancingGauge T R) b‖ = ‖_root_.YangMills.Construction.BlockAverages.contourAverage T b‖ := by
      unfold gaugedContourAverage
      rw [norm_mul, norm_mul, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, one_mul, mul_one]
    rw [h0, norm_zero] at h1
    linarith
  have hneR : _root_.YangMills.Construction.BlockAverages.contourAverage R b ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hqR'
    linarith
  have eT : gaugedContourAverage T (balancedLinks T R kR) b =
      (kR b.1 : ℍ[ℝ]) * gaugedContourAverage T (balancingGauge T R) b *
        (((kR (b.1 + unitStep (j + 1) b.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    unfold gaugedContourAverage balancedLinks
    rw [mul_inv_rev, Submonoid.coe_mul, Submonoid.coe_mul]
    simp only [mul_assoc]
  have eR : gaugedContourAverage R kR b = (kR b.1 : ℍ[ℝ]) * _root_.YangMills.Construction.BlockAverages.contourAverage R b *
      (((kR (b.1 + unitStep (j + 1) b.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := rfl
  have hN1 : 1 / 2 ≤ ‖gaugedContourAverage T (balancedLinks T R kR) b‖ := by
    unfold gaugedContourAverage
    rw [norm_mul, norm_mul, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, one_mul, mul_one]
    exact hqT'
  refine ⟨hN1, ?_⟩
  obtain ⟨uT, huT⟩ : ∃ uT : UnitQuaternion,
      uT = polarUnit (gaugedContourAverage T (balancingGauge T R) b) := ⟨_, rfl⟩
  have mT : bondMisfit T (balancedLinks T R kR) T' b = T' b.1 b.2 *
      (kR b.1 * uT * (kR (b.1 + unitStep (j + 1) b.2))⁻¹)⁻¹ := by
    unfold bondMisfit
    rw [eT, polarUnit_conj _ _ hne, ← huT]
  have mR : bondMisfit R kR R' b = R' b.1 b.2 *
      (kR b.1 * uR * (kR (b.1 + unitStep (j + 1) b.2))⁻¹)⁻¹ := by
    unfold bondMisfit
    rw [eR, polarUnit_conj _ _ hneR, ← huR]
  have hmA : relativeContourMean T R b = uT * uR⁻¹ := by
    unfold relativeContourMean
    rw [← huT, ← huR]
  rw [mT, mR]
  rw [quotient_factorization (T' b.1 b.2) (R' b.1 b.2) (kR b.1) (kR (b.1 + unitStep (j + 1) b.2)) uT uR]
  have s1 := norm_coe_mul_sub_one_le
    (T' b.1 b.2 * (kR b.1 * uT * (kR (b.1 + unitStep (j + 1) b.2))⁻¹)⁻¹ *
      (R' b.1 b.2 * (kR b.1 * uR * (kR (b.1 + unitStep (j + 1) b.2))⁻¹)⁻¹)⁻¹)
    ((R' b.1 b.2 * (kR b.1 * uR * (kR (b.1 + unitStep (j + 1) b.2))⁻¹)⁻¹) * (kR b.1 * (uT * uR⁻¹) * (kR b.1)⁻¹) *
      (R' b.1 b.2 * (kR b.1 * uR * (kR (b.1 + unitStep (j + 1) b.2))⁻¹)⁻¹)⁻¹)
  rw [norm_coe_conj_sub_one, norm_coe_conj_sub_one, ← hmA] at s1
  obtain ⟨Pa, hPa⟩ : ∃ Pa : ℝ, Pa = lineBlockAverage (linkGap T R) b := ⟨_, rfl⟩
  have hta : ‖parallelAverage R (pureGap T R) b‖ ≤ Pa := by
    refine (norm_parallelAverage_le hodd R (pureGap T R) b).trans ?_
    rw [hPa]
    unfold lineBlockAverage
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.sum_le_sum fun h _ => Finset.sum_le_sum fun r _ => ?_
    exact norm_pureComponent_coe_le _
  have hPaτ : Pa ≤ (F.blockSide : ℝ) * t := by
    rw [hPa]
    unfold lineBlockAverage
    have h1 : ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
        linkGap T R (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2 ≤
          (F.blockSide : ℝ) ^ 4 * ((F.blockSide : ℝ) * t) := by
      have h2 : ∀ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
          linkGap T R (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2 ≤
            (F.blockSide : ℝ) * t := by
        intro h hh
        have := Finset.sum_le_sum (s := Finset.range F.blockSide) fun r hr => hB.2 h hh r hr
        rwa [Finset.sum_const, nsmul_eq_mul, Finset.card_range] at this
      have h3 := Finset.sum_le_sum h2
      rw [Finset.sum_const, nsmul_eq_mul, card_centredCube hodd] at h3
      push_cast at h3
      exact h3
    calc 1 / (F.blockSide : ℝ) ^ 4 * _ ≤
          1 / (F.blockSide : ℝ) ^ 4 * ((F.blockSide : ℝ) ^ 4 * ((F.blockSide : ℝ) * t)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (F.blockSide : ℝ) * t := by field_simp
  have hp : ‖pureComponent ((relativeContourMean T R b : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖parallelAverage R (pureGap T R) b‖ +
        CM * ((F.blockSide : ℝ) * t) * ((F.blockSide : ℝ) * t + ε) := by
    have := norm_sub_norm_le (pureComponent ((relativeContourMean T R b : UnitQuaternion) : ℍ[ℝ]))
      (parallelAverage R (pureGap T R) b)
    linarith
  have hfin := le_of_pure_estimates (P := Pa) (Q := ‖parallelAverage R (pureGap T R) b‖)
    (E := CM * ((F.blockSide : ℝ) * t) * ((F.blockSide : ℝ) * t + ε)) (τ := (F.blockSide : ℝ) * t) (ε := ε)
    (g := normSubOne (relativeContourMean T R b))
    (p := ‖pureComponent ((relativeContourMean T R b : UnitQuaternion) : ℍ[ℝ])‖) (CM := CM)
    (by positivity) hε0 (by linarith) (by linarith) hCM.le rfl (norm_nonneg _) hta hPaτ hp m2
    (norm_nonneg _) (_root_.YangMills.Construction.GaugedOneStep.distFromOne_le_pure _)
  rw [← hPa, ← hmA]
  unfold normSubOne at hfin ⊢
  linarith
end YangMills.Construction.GaugedOneStep
end

import YangMills.Construction.ColdChainAtEveryLevel.ChangesOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.DensityUnderAChangeOfFraming
import YangMills.Construction.ColdChainAtEveryLevel.GaugeCovarianceOfAContour
import YangMills.Construction.ColdChainAtEveryLevel.SizesAtAGoodCell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
namespace GaugeChangeDensity
variable {F : BlockFrame}
theorem im_eq_pureComponent (q : ℍ[ℝ]) : q.im = pureComponent q := by
  ext <;> simp [pureComponent] <;> ring
theorem norm_im_le_norm (q : ℍ[ℝ]) : ‖q.im‖ ≤ ‖q‖ := by
  rw [im_eq_pureComponent]
  exact norm_pureComponent_le q
theorem unitQuaternion_mul_star (g : UnitQuaternion) : (g : ℍ[ℝ]) * star (g : ℍ[ℝ]) = 1 :=
  Unitary.mul_star_self_of_mem g.2
theorem norm_star_unitQuaternion (g : UnitQuaternion) : ‖star (g : ℍ[ℝ])‖ = 1 := by
  rw [norm_star, norm_coe_unitQuaternion]
theorem norm_conjugate (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖(g : ℍ[ℝ]) * q * star (g : ℍ[ℝ])‖ = ‖q‖ := by
  rw [norm_mul, norm_mul, norm_star_unitQuaternion, norm_coe_unitQuaternion]
  simp
theorem commutator_eq_im (q f : ℍ[ℝ]) : q * f - f * q = (q - 1) * f.im - f.im * (q - 1) := by
  ext <;> simp <;> ring
theorem norm_commutator_le (g : UnitQuaternion) (f : ℍ[ℝ]) :
    ‖(g : ℍ[ℝ]) * f - f * g‖ ≤ 2 * distFromOne g * ‖f.im‖ := by
  rw [commutator_eq_im]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have : distFromOne g = ‖(g : ℍ[ℝ]) - 1‖ := rfl
  rw [this]
  linarith
theorem norm_conjugate_sub_le (g : UnitQuaternion) (f : ℍ[ℝ]) :
    ‖(g : ℍ[ℝ]) * f * star (g : ℍ[ℝ]) - f‖ ≤ 2 * distFromOne g * ‖f.im‖ := by
  have h : (g : ℍ[ℝ]) * f * star (g : ℍ[ℝ]) - f = ((g : ℍ[ℝ]) * f - f * g) * star (g : ℍ[ℝ]) := by
    rw [sub_mul, mul_assoc f, unitQuaternion_mul_star, mul_one]
  rw [h, norm_mul, norm_star_unitQuaternion, mul_one]
  exact norm_commutator_le g f
theorem pureComponent_conjugate (a b : ℍ[ℝ]) : pureComponent (a * b * star a) = a * pureComponent b * star a := by
  have h : star (a * b * star a) = a * star b * star a := by
    simp [star_mul, mul_assoc]
  simp only [pureComponent, h, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul]
theorem conjugate_sub_le (g P f : UnitQuaternion) :
    ‖((g * P * g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - (f : ℍ[ℝ])‖ ≤
      ‖(P : ℍ[ℝ]) - (f : ℍ[ℝ])‖ + 2 * distFromOne g * ‖(f : ℍ[ℝ]).im‖ := by
  have h : ((g * P * g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - (f : ℍ[ℝ]) =
      (g : ℍ[ℝ]) * ((P : ℍ[ℝ]) - f) * star (g : ℍ[ℝ]) + ((g : ℍ[ℝ]) * f * star (g : ℍ[ℝ]) - f) := by
    simp only [Submonoid.coe_mul, coe_unitQuaternion_inv, mul_sub, sub_mul]
    abel
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_conjugate]
  linarith [norm_conjugate_sub_le g (f : ℍ[ℝ])]
theorem distFromOne_groupCommutator_le (c m : UnitQuaternion) :
    ‖((c * m * c⁻¹ * m⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * distFromOne c * distFromOne m := by
  have h2 : (m : ℍ[ℝ]) * c * (star (c : ℍ[ℝ]) * star (m : ℍ[ℝ])) = 1 := by
    rw [mul_assoc, ← mul_assoc (c : ℍ[ℝ]), unitQuaternion_mul_star, one_mul, unitQuaternion_mul_star]
  have h : ((c * m * c⁻¹ * m⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 =
      ((c : ℍ[ℝ]) * m - m * c) * (star (c : ℍ[ℝ]) * star (m : ℍ[ℝ])) := by
    rw [sub_mul, h2]
    simp only [Submonoid.coe_mul, coe_unitQuaternion_inv, mul_assoc]
  rw [h, norm_mul, norm_mul, norm_star_unitQuaternion, norm_star_unitQuaternion]
  have h3 := norm_commutator_le c (m : ℍ[ℝ])
  have h4 : ‖(m : ℍ[ℝ]).im‖ ≤ distFromOne m := by
    have h5 : (m : ℍ[ℝ]).im = ((m : ℍ[ℝ]) - 1).im := by
      ext <;> simp
    rw [h5]
    exact norm_im_le_norm _
  have h6 : 0 ≤ distFromOne c := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 2 * distFromOne c)]
theorem norm_im_conjugate_le (c M m : UnitQuaternion) :
    ‖((c * M * c⁻¹ * m⁻¹ : UnitQuaternion) : ℍ[ℝ]).im‖ ≤
      ‖((M * m⁻¹ : UnitQuaternion) : ℍ[ℝ]).im‖ + 2 * distFromOne c * distFromOne m := by
  set B : UnitQuaternion := M * m⁻¹ with hB
  set T : UnitQuaternion := c * m * c⁻¹ * m⁻¹ with hT
  have hg : c * M * c⁻¹ * m⁻¹ = c * B * c⁻¹ * T := by
    rw [hB, hT]
    group
  have hq : ((c * B * c⁻¹ * T : UnitQuaternion) : ℍ[ℝ]) =
      (c : ℍ[ℝ]) * (B : ℍ[ℝ]) * star (c : ℍ[ℝ]) +
        ((c * B * c⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((T : ℍ[ℝ]) - 1) := by
    rw [mul_sub, mul_one]
    simp only [Submonoid.coe_mul, coe_unitQuaternion_inv]
    abel
  rw [hg, hq, im_eq_pureComponent, pureComponent_add, im_eq_pureComponent, pureComponent_conjugate]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(c : ℍ[ℝ]) * pureComponent (B : ℍ[ℝ]) * star (c : ℍ[ℝ])‖ = ‖pureComponent (B : ℍ[ℝ])‖ :=
    norm_conjugate _ _
  have h2 : ‖pureComponent (((c * B * c⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((T : ℍ[ℝ]) - 1))‖ ≤
      ‖(T : ℍ[ℝ]) - 1‖ := by
    refine (norm_pureComponent_le _).trans ?_
    rw [norm_mul, norm_coe_unitQuaternion, one_mul]
  have h3 := distFromOne_groupCommutator_le c m
  rw [h1]
  linarith
theorem polarUnit_mul_mul (g h : UnitQuaternion) {q : ℍ[ℝ]} (hq : q ≠ 0) :
    polarUnit ((g : ℍ[ℝ]) * q * (h : ℍ[ℝ])) = g * polarUnit q * h := by
  have hne : (g : ℍ[ℝ]) * q * (h : ℍ[ℝ]) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (coe_unitQuaternion_ne_zero g) hq) (coe_unitQuaternion_ne_zero h)
  apply Subtype.ext
  rw [coe_polarUnit hne, Submonoid.coe_mul, Submonoid.coe_mul, coe_polarUnit hq, norm_mul, norm_mul,
    norm_coe_unitQuaternion, norm_coe_unitQuaternion, mul_smul_comm, smul_mul_assoc]
  simp
theorem bondMisfit_gaugeTransform {j : ℕ} (hj : j < F.top) (hL : 0 < F.blockSide) (hg : gaugeCovarianceStatement)
    (γ : F.Site j → UnitQuaternion) (u k l : F.Site (j + 1) → UnitQuaternion) (X : F.GaugeField j)
    (X' Y : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) (h1 : l c.1 = u c.1 * k c.1 * (γ (refineSite c.1))⁻¹)
    (h2 : l (c.1 + unitStep (j + 1) c.2) = u (c.1 + unitStep (j + 1) c.2) * k (c.1 + unitStep (j + 1) c.2) *
      (γ (refineSite (c.1 + unitStep (j + 1) c.2)))⁻¹)
    (h3 : Y c.1 c.2 = u c.1 * X' c.1 c.2 * (u (c.1 + unitStep (j + 1) c.2))⁻¹)
    (h0 : gaugedContourAverage X k c ≠ 0) :
    bondMisfit (gaugeTransform γ X) l Y c = u c.1 * bondMisfit X k X' c * (u c.1)⁻¹ := by
  have hm : gaugedContourAverage (gaugeTransform γ X) l c =
      (u c.1 : ℍ[ℝ]) * gaugedContourAverage X k c *
        (((u (c.1 + unitStep (j + 1) c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    unfold gaugedContourAverage
    rw [(hg F j hj hL).2.1 γ X c, h1, h2]
    have e1 : ((u c.1 * k c.1 * (γ (refineSite c.1))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
        (γ (refineSite c.1) : ℍ[ℝ]) = (u c.1 : ℍ[ℝ]) * (k c.1 : ℍ[ℝ]) := by
      rw [← Submonoid.coe_mul, ← Submonoid.coe_mul]
      congr 1
      group
    have e2 : (((γ (refineSite (c.1 + unitStep (j + 1) c.2)))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
        (((u (c.1 + unitStep (j + 1) c.2) * k (c.1 + unitStep (j + 1) c.2) *
          (γ (refineSite (c.1 + unitStep (j + 1) c.2)))⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
        (((k (c.1 + unitStep (j + 1) c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          (((u (c.1 + unitStep (j + 1) c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      rw [← Submonoid.coe_mul, ← Submonoid.coe_mul]
      congr 1
      group
    calc _ = (((u c.1 * k c.1 * (γ (refineSite c.1))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
            (γ (refineSite c.1) : ℍ[ℝ])) * contourAverage X c *
          ((((γ (refineSite (c.1 + unitStep (j + 1) c.2)))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
            (((u (c.1 + unitStep (j + 1) c.2) * k (c.1 + unitStep (j + 1) c.2) *
              (γ (refineSite (c.1 + unitStep (j + 1) c.2)))⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by
          simp only [mul_assoc]
      _ = _ := by
          rw [e1, e2]
          simp only [mul_assoc]
  unfold bondMisfit
  rw [hm, h3, polarUnit_mul_mul _ _ h0]
  group
theorem enclosingCell_baseSite (hL : Odd F.blockSide) {l : ℕ} (hl : l ≤ F.top) (y : F.Site l) :
    enclosingCell (baseSite y) = enclosingCell y := by
  funext i
  have hLpos : (0 : ℤ) < F.blockSide := by exact_mod_cast hL.pos
  have hLodd : Odd (F.blockSide : ℤ) := by exact_mod_cast hL
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = siteCoords y i := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℤ, P = (F.blockSide : ℤ) ^ l := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℤ, M = (F.blockSide : ℤ) ^ (F.top - l) := ⟨_, rfl⟩
  have hPpos : 0 < P := by
    rw [hP]
    positivity
  have hMpos : 0 < M := by
    rw [hM]
    positivity
  have hPM : (F.blockSide : ℤ) ^ (F.top - 0) = P * M := by
    rw [hP, hM, ← pow_add]
    congr 1
    omega
  have hper : ((F.period 0 i : ℕ) : ℤ) = P * (F.period l i : ℕ) := by
    simp only [BlockFrame.period]
    push_cast
    rw [hPM, hM, hP]
    ring
  have hcm : c % ((F.period l i : ℕ) : ℤ) = c := by
    have h0 : ((c : ℤ) : ZMod (F.period l i)) = y i := by
      rw [hc]
      exact ZMod.intCast_zmod_cast (y i)
    have h := ZMod.coe_intCast (n := F.period l i) c
    rw [h0] at h
    rw [← h, hc]
    rfl
  have hb : siteCoords (baseSite y) i = P * c := by
    have h : siteCoords (baseSite y) i = (P * c) % ((F.period 0 i : ℕ) : ℤ) := by
      have h' : siteCoords (baseSite y) i = ZMod.cast (((P * c : ℤ)) : ZMod (F.period 0 i)) := by
        rw [hP, hc]
        rfl
      rw [h']
      exact ZMod.coe_intCast _
    rw [h, hper, Int.mul_emod_mul_of_pos _ _ hPpos, hcm]
  obtain ⟨u, hu⟩ : Odd M := by
    rw [hM]
    exact hLodd.pow
  obtain ⟨w, hw⟩ : Odd P := by
    rw [hP]
    exact hLodd.pow
  have h1 : (M - 1) / 2 = u := by omega
  have hw0 : 0 ≤ w := by omega
  have h2 : (P * M - 1) / 2 = P * u + w := by
    have h : P * M - 1 = 2 * (P * u + w) := by
      rw [hu]
      linear_combination hw
    rw [h]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have h3 : (P * c + (P * u + w)) / (P * M) = (c + u) / M := by
    have hq := Int.emod_add_mul_ediv (c + u) M
    have hr0 := Int.emod_nonneg (c + u) hMpos.ne'
    have hr1 := Int.emod_lt_of_pos (c + u) hMpos
    obtain ⟨q, hqd⟩ : ∃ q : ℤ, q = (c + u) / M := ⟨_, rfl⟩
    obtain ⟨r, hrd⟩ : ∃ r : ℤ, r = (c + u) % M := ⟨_, rfl⟩
    rw [← hqd, ← hrd] at hq
    rw [← hrd] at hr0 hr1
    have e : P * c + (P * u + w) = (w + P * r) + (P * M) * q := by
      linear_combination (-P) * hq
    rw [e, Int.add_mul_ediv_left _ _ (mul_pos hPpos hMpos).ne', ← hqd,
      Int.ediv_eq_zero_of_lt (add_nonneg hw0 (mul_nonneg hPpos.le hr0))
        (by nlinarith [mul_le_mul_of_nonneg_left (show r + 1 ≤ M by omega) hPpos.le]), zero_add]
  show (((siteCoords (baseSite y) i + ((F.blockSide : ℤ) ^ (F.top - 0) - 1) / 2) /
      (F.blockSide : ℤ) ^ (F.top - 0) : ℤ) : ZMod (F.period F.top i)) =
    (((siteCoords y i + ((F.blockSide : ℤ) ^ (F.top - l) - 1) / 2) /
      (F.blockSide : ℤ) ^ (F.top - l) : ℤ) : ZMod (F.period F.top i))
  rw [hb, hPM, h2, h3, ← hc, ← hM, h1]
theorem zero_mem_centredCube {M : ℕ} (hM : 0 < M) : (0 : Fin 4 → ℤ) ∈ centredCube M := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.zero_mem_centredCube <;> assumption
theorem siteOfCoords_zero (j : ℕ) : siteOfCoords (F := F) j 0 = 0 := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_zero <;> assumption
theorem baseSite_mem_of_mem_patchFitBonds (hL : Odd F.blockSide) {S : Finset F.Cell} {z : F.Cell} {j : ℕ}
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ patchFitBonds S z j) :
    baseSite c.1 ∈ patchBaseSites S z ∧ baseSite (c.1 + unitStep (j + 1) c.2) ∈ patchBaseSites S z := by
  have h := (Finset.mem_filter.1 hc).2 0 (zero_mem_centredCube (pow_pos hL.pos _))
  simpa [siteOfCoords_zero] using h
open Classical in
def upperRotation (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k Γ : F.SiteGauge) (j : ℕ)
    (y : F.Site (j + 1)) : UnitQuaternion :=
  if j = F.depth then balancedRotation W kW X k Γ j y else Γ (j + 1) y
theorem gaugeChangeAbove_eq (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k Γ Γ' : F.SiteGauge)
    (j : ℕ) (y : F.Site (j + 1)) :
    gaugeChangeAbove W kW X k Γ Γ' j y = upperRotation W kW X k Γ j y * (upperRotation W kW X k Γ' j y)⁻¹ := by
  by_cases h : j = F.depth
  · simp [gaugeChangeAbove, upperRotation, h]
  · simp [gaugeChangeAbove, upperRotation, h, gaugeChange]
theorem bondMisfit_of_pinned (hL : Odd F.blockSide) (hg : gaugeCovarianceStatement) {a C : ℝ}
    {S : Finset F.Cell} {z : F.Cell} {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain} {k Γ : F.SiteGauge}
    (hΓ : IsPinnedGauge a C S z W kW X k Γ)
    {j : ℕ} (hj : j < F.top) {c : F.Site (j + 1) × Fin 4} (hc : c ∈ patchFitBonds S z j)
    (h0 : gaugedContourAverage (X j) (k (j + 1)) c ≠ 0) :
    bondMisfit (gaugedChainFields X Γ j) (balancedLinkAgainst W kW (gaugedChainFields X Γ) j)
        (framedUpperField W kW X k Γ j) c =
      upperRotation W kW X k Γ j c.1 * bondMisfit (X j) (k (j + 1)) (X (j + 1)) c *
        (upperRotation W kW X k Γ j c.1)⁻¹ := by
  obtain ⟨hy, hy'⟩ := baseSite_mem_of_mem_patchFitBonds hL hc
  by_cases h : j = F.depth
  · subst h
    have hA : ∀ y, upperRotation W kW X k Γ F.depth y = topCorrection W kW X k Γ y := by
      intro y
      simp [upperRotation, balancedRotation, topCorrection]
    have hl : ∀ y, balancedLinkAgainst W kW (gaugedChainFields X Γ) F.depth y =
        upperRotation W kW X k Γ F.depth y * k (F.depth + 1) y * (Γ F.depth (refineSite y))⁻¹ := by
      intro y
      rw [hA]
      unfold topCorrection gaugedLink
      rw [hΓ.1 y]
      group
    have hu : framedUpperField W kW X k Γ F.depth = gaugeTransform (topCorrection W kW X k Γ) (X F.top) := by
      simp [framedUpperField]
    refine bondMisfit_gaugeTransform hj hL.pos hg (Γ F.depth) (upperRotation W kW X k Γ F.depth) (k (F.depth + 1)) _
      (X F.depth) (X (F.depth + 1)) _ c (hl _) (hl _) ?_ h0
    rw [hu, hA, hA]
    rfl
  · have hj1 : j + 1 < F.top := by
      have : j ≠ F.depth := h
      simp only [BlockFrame.top] at hj ⊢
      omega
    have hA : ∀ y, upperRotation W kW X k Γ j y = Γ (j + 1) y := by
      intro y
      simp [upperRotation, h]
    have hu : framedUpperField W kW X k Γ j = gaugedChainFields X Γ (j + 1) := by
      simp [framedUpperField, h]
    refine bondMisfit_gaugeTransform hj hL.pos hg (Γ j) (upperRotation W kW X k Γ j) (k (j + 1)) _ (X j) (X (j + 1)) _ c
      ?_ ?_ ?_ h0
    · rw [hA, ← hΓ.2.1 j hj1 c.1 hy]
      rfl
    · rw [hA, ← hΓ.2.1 j hj1 _ hy']
      rfl
    · rw [hu, hA, hA]
      rfl
theorem sq_le_of_le_add {A B g m : ℝ} (hA : 0 ≤ A) (h : A ≤ B + 2 * g * m) :
    A ^ 2 ≤ 3 * B ^ 2 + 8 * (g * m) ^ 2 := by
  have h1 : A ^ 2 ≤ (B + 2 * g * m) ^ 2 := pow_le_pow_left₀ hA h 2
  nlinarith [sq_nonneg (B - g * m), sq_nonneg (g * m)]
def gaugeChangeRemainder (a : ℝ) (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain)
    (k Γ Γ' : F.SiteGauge) : F.ActionTerm → ℝ
  | Sum.inl p => 8 * (distFromOne (gaugeChange Γ Γ' 0 p.1) *
      ‖((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).im‖) ^ 2
  | Sum.inr c => 8 * a * (distFromOne (gaugeChangeAbove W kW X k Γ Γ' c.1 c.2.1) *
      distFromOne (bondMisfit (W c.1) (kW (c.1 + 1)) (W (c.1 + 1)) c.2)) ^ 2
theorem gaugeChangeRemainder_nonneg {a : ℝ} (ha : 0 < a) (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain)
    (k Γ Γ' : F.SiteGauge) (t : F.ActionTerm) : 0 ≤ gaugeChangeRemainder a W kW X k Γ Γ' t := by
  rcases t with p | c
  · simp only [gaugeChangeRemainder]
    positivity
  · simp only [gaugeChangeRemainder]
    positivity
theorem energyDensity_plaquette_le (hL : 0 < F.blockSide) (hg : gaugeCovarianceStatement) (a : ℝ)
    (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k Γ Γ' : F.SiteGauge) (p : F.Site 0 × Fin 4 × Fin 4) :
    relativeEnergyDensity a W kW X k Γ (Sum.inl p) ≤
      3 * relativeEnergyDensity a W kW X k Γ' (Sum.inl p) + gaugeChangeRemainder a W kW X k Γ Γ' (Sum.inl p) := by
  have hcov := (hg F 0 (Nat.succ_pos _) hL).2.2.1
  have h1 : plaquetteHolonomy (gaugedChainFields X Γ 0) p = gaugeChange Γ Γ' 0 p.1 *
      plaquetteHolonomy (gaugedChainFields X Γ' 0) p * (gaugeChange Γ Γ' 0 p.1)⁻¹ := by
    show plaquetteHolonomy (gaugeTransform (Γ 0) (X 0)) p = _ * plaquetteHolonomy (gaugeTransform (Γ' 0) (X 0)) p * _
    rw [hcov, hcov, gaugeChange]
    group
  simp only [relativeEnergyDensity, gaugeChangeRemainder]
  rw [h1]
  exact sq_le_of_le_add (norm_nonneg _)
    (conjugate_sub_le (gaugeChange Γ Γ' 0 p.1) (plaquetteHolonomy (gaugedChainFields X Γ' 0) p)
      (plaquetteHolonomy (W 0) p))
theorem energyDensity_bond_le (hL : Odd F.blockSide) (hg : gaugeCovarianceStatement) {a C C' : ℝ} (ha : 0 < a)
    {S : Finset F.Cell} {z z' : F.Cell} {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain}
    {k Γ Γ' : F.SiteGauge}
    (hΓ : IsPinnedGauge a C S z W kW X k Γ) (hΓ' : IsPinnedGauge a C' S z' W kW X k Γ')
    {j : ℕ} (hj : j < F.top) {c : F.Site (j + 1) × Fin 4} (hc : c ∈ patchFitBonds S z j)
    (hc' : c ∈ patchFitBonds S z' j)
    (h0 : gaugedContourAverage (X j) (k (j + 1)) c ≠ 0) :
    relativeEnergyDensity a W kW X k Γ (Sum.inr ⟨j, c⟩) ≤
      3 * relativeEnergyDensity a W kW X k Γ' (Sum.inr ⟨j, c⟩) +
        gaugeChangeRemainder a W kW X k Γ Γ' (Sum.inr ⟨j, c⟩) := by
  have h1 := bondMisfit_of_pinned hL hg hΓ hj hc h0
  have h2 := bondMisfit_of_pinned hL hg hΓ' hj hc' h0
  have h3 : bondMisfit (gaugedChainFields X Γ j) (balancedLinkAgainst W kW (gaugedChainFields X Γ) j)
        (framedUpperField W kW X k Γ j) c =
      gaugeChangeAbove W kW X k Γ Γ' j c.1 *
        bondMisfit (gaugedChainFields X Γ' j) (balancedLinkAgainst W kW (gaugedChainFields X Γ') j)
          (framedUpperField W kW X k Γ' j) c *
        (gaugeChangeAbove W kW X k Γ Γ' j c.1)⁻¹ := by
    rw [h1, h2, gaugeChangeAbove_eq]
    group
  simp only [relativeEnergyDensity, gaugeChangeRemainder]
  rw [h3]
  have h4 := norm_im_conjugate_le (gaugeChangeAbove W kW X k Γ Γ' j c.1)
    (bondMisfit (gaugedChainFields X Γ' j) (balancedLinkAgainst W kW (gaugedChainFields X Γ') j)
      (framedUpperField W kW X k Γ' j) c)
    (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)
  have h5 := mul_le_mul_of_nonneg_left (sq_le_of_le_add (norm_nonneg _) h4) ha.le
  nlinarith [h5]
theorem sum_sq_le_sq_sum (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  have h : ∀ i ∈ s, f i ^ 2 ≤ f i * ∑ j ∈ s, f j := fun i hi => by
    rw [sq]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => hf j) hi) (hf i)
  calc ∑ i ∈ s, f i ^ 2 ≤ ∑ i ∈ s, f i * ∑ j ∈ s, f j := Finset.sum_le_sum h
    _ = (∑ i ∈ s, f i) ^ 2 := by rw [← Finset.sum_mul, sq]
theorem sum_gaugeChangeRemainder_le (hL : Odd F.blockSide) {a C₂ s d : ℝ} (ha : 0 < a) (hb : 0 ≤ C₂ * s * d)
    {S : Finset F.Cell} {z z' y : F.Cell} {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain}
    {k Γ Γ' : F.SiteGauge}
    (hsz : GaugeChangeBounds C₂ s S z z' y W kW X k Γ Γ' d) :
    ∑ t ∈ (patchActionTerms S z ∩ patchActionTerms S z').filter (fun t => enclosingCell (actionTermSite t) = y),
        gaugeChangeRemainder a W kW X k Γ Γ' t ≤ 8 * (1 + a) * (C₂ * s * d) ^ 2 := by
  have hsub : (patchActionTerms S z ∩ patchActionTerms S z').filter
      (fun t => enclosingCell (actionTermSite t) = y) ⊆
      ((patchPlaquettes S z ∩ patchPlaquettes S z').filter (fun p => enclosingCell p.1 = y)).disjSum
        ((Finset.range F.top).sigma fun j => (patchFitBonds S z j ∩ patchFitBonds S z' j).filter
          (fun c => enclosingCell c.1 = y)) := by
    intro t ht
    rcases t with p | ⟨j, c⟩
    · obtain ⟨hin, hy⟩ := Finset.mem_filter.1 ht
      obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hin
      exact Finset.inl_mem_disjSum.2 (Finset.mem_filter.2
        ⟨Finset.mem_inter.2 ⟨Finset.inl_mem_disjSum.1 h1, Finset.inl_mem_disjSum.1 h2⟩, hy⟩)
    · obtain ⟨hin, hy⟩ := Finset.mem_filter.1 ht
      obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hin
      obtain ⟨hj, hc⟩ := Finset.mem_sigma.1 (Finset.inr_mem_disjSum.1 h1)
      obtain ⟨_, hc'⟩ := Finset.mem_sigma.1 (Finset.inr_mem_disjSum.1 h2)
      have hy' : enclosingCell c.1 = y := by
        rw [← enclosingCell_baseSite hL (Nat.succ_le_of_lt (Finset.mem_range.1 hj))]
        exact hy
      exact Finset.inr_mem_disjSum.2 (Finset.mem_sigma.2
        ⟨hj, Finset.mem_filter.2 ⟨Finset.mem_inter.2 ⟨hc, hc'⟩, hy'⟩⟩)
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
    fun t _ _ => gaugeChangeRemainder_nonneg ha W kW X k Γ Γ' t).trans ?_
  rw [Finset.sum_disjSum, Finset.sum_sigma]
  simp only [gaugeChangeRemainder]
  have hp := hsz.curvature_le
  have hm := hsz.misfit_le
  rw [← Finset.mul_sum]
  have hq : ∑ j ∈ Finset.range F.top, ∑ c ∈ (patchFitBonds S z j ∩ patchFitBonds S z' j).filter
        (fun c => enclosingCell c.1 = y),
      (distFromOne (gaugeChangeAbove W kW X k Γ Γ' j c.1) *
        distFromOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)) ^ 2 ≤
      (C₂ * s * d) ^ 2 := by
    refine le_trans ?_ (pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _) hm 2)
    refine le_trans (le_of_eq ?_) (sum_sq_le_sq_sum _ _ fun j => Real.sqrt_nonneg _)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.sq_sqrt (Finset.sum_nonneg fun c _ => sq_nonneg _)]
  have hr : ∑ x ∈ Finset.range F.top, ∑ c ∈ (patchFitBonds S z x ∩ patchFitBonds S z' x).filter
        (fun c => enclosingCell c.1 = y),
      8 * a * (distFromOne (gaugeChangeAbove W kW X k Γ Γ' x c.1) *
        distFromOne (bondMisfit (W x) (kW (x + 1)) (W (x + 1)) c)) ^ 2 =
      8 * a * ∑ j ∈ Finset.range F.top, ∑ c ∈ (patchFitBonds S z j ∩ patchFitBonds S z' j).filter
        (fun c => enclosingCell c.1 = y),
        (distFromOne (gaugeChangeAbove W kW X k Γ Γ' j c.1) *
          distFromOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)) ^ 2 := by
    simp only [Finset.mul_sum]
  rw [hr]
  nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 8 * a)]
theorem relativeEnergy_nonneg {a : ℝ} (ha : 0 < a) (S : Finset F.Cell) (z : F.Cell) (W : F.FieldChain)
    (kW : F.SiteGauge) (X : F.FieldChain) (k Γ : F.SiteGauge) : 0 ≤ relativeEnergy a S z W kW X k Γ := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.relativeEnergy_nonneg <;> assumption
theorem mul_sq_mul_sqrt (a C s D : ℝ) (hD : 0 ≤ D) :
    8 * (1 + a) * (C * s * Real.sqrt D) ^ 2 = 8 * (1 + a) * C ^ 2 * s ^ 2 * D := by
  rw [mul_pow, mul_pow, Real.sq_sqrt hD]
  ring
theorem relativeEnergyDensity_le (hL : Odd F.blockSide) (hg : gaugeCovarianceStatement) {a C C₂ s : ℝ}
    (ha : 0 < a) (hC₂ : 0 < C₂) (hs : 0 < s) {S : Finset F.Cell} {z z' y : F.Cell} {W : F.FieldChain}
    {kW : F.SiteGauge} {X : F.FieldChain} {k Γ Γ' : F.SiteGauge} (hΓ : IsPinnedGauge a C S z W kW X k Γ)
    (hΓ' : IsPinnedGauge a C S z' W kW X k Γ')
    (hmeans : ∀ j, j < F.top → ∀ b ∈ patchFitBonds S z j, 1 / 2 ≤ ‖gaugedContourAverage (X j) (k (j + 1)) b‖)
    (hsizes : GaugeChangeBounds C₂ s S z z' y W kW X k Γ Γ'
      (Real.sqrt (relativeEnergy a S z W kW X k Γ + relativeEnergy a S z' W kW X k Γ'))) :
    ∃ e : F.ActionTerm → ℝ, (∀ t ∈ patchActionTerms S z ∩ patchActionTerms S z',
        enclosingCell (actionTermSite t) = y →
        relativeEnergyDensity a W kW X k Γ t ≤ 3 * relativeEnergyDensity a W kW X k Γ' t + e t) ∧
      (∀ t, 0 ≤ e t) ∧
      ∑ t ∈ (patchActionTerms S z ∩ patchActionTerms S z').filter
          (fun t => enclosingCell (actionTermSite t) = y), e t ≤
        8 * (1 + a) * C₂ ^ 2 * s ^ 2 *
          (relativeEnergy a S z W kW X k Γ + relativeEnergy a S z' W kW X k Γ') := by
  have hE := relativeEnergy_nonneg ha S z W kW X k Γ
  have hE' := relativeEnergy_nonneg ha S z' W kW X k Γ'
  refine ⟨gaugeChangeRemainder a W kW X k Γ Γ', ?_, gaugeChangeRemainder_nonneg ha W kW X k Γ Γ', ?_⟩
  · intro t ht _
    obtain ⟨h1, h2⟩ := Finset.mem_inter.1 ht
    rcases t with p | ⟨j, c⟩
    · exact energyDensity_plaquette_le hL.pos hg a W kW X k Γ Γ' p
    · obtain ⟨hj, hc⟩ := Finset.mem_sigma.1 (Finset.inr_mem_disjSum.1 h1)
      obtain ⟨_, hc'⟩ := Finset.mem_sigma.1 (Finset.inr_mem_disjSum.1 h2)
      have hj' : j < F.top := Finset.mem_range.1 hj
      have hne : gaugedContourAverage (X j) (k (j + 1)) c ≠ 0 := by
        intro h0
        have := hmeans j hj' c hc
        rw [h0, norm_zero] at this
        norm_num at this
      exact energyDensity_bond_le hL hg ha hΓ hΓ' hj' hc hc' hne
  · exact (sum_gaugeChangeRemainder_le hL ha (mul_nonneg (mul_nonneg hC₂.le hs.le) (Real.sqrt_nonneg _))
      hsizes).trans (le_of_eq (mul_sq_mul_sqrt a C₂ s _ (add_nonneg hE hE')))
end GaugeChangeDensity
theorem relativeDensityComparison (hch : gaugeChangeBoundStatement) (hsz : lowCostPatchBoundsStatement)
    (hg : gaugeCovarianceStatement) : relativeDensityComparisonStatement := by
  intro a θ del Ca ha hθ hθ' hdel hdel' hCa
  obtain ⟨L₁, h1⟩ := hch a θ del Ca ha hθ hθ' hdel hdel' hCa
  obtain ⟨L₂, h2⟩ := hsz a ha
  refine ⟨max L₁ L₂, fun L hodd hL C₁ C Cd hC₁ hC hCd => ?_⟩
  obtain ⟨C₂, c₁, hC₂, hc₁, h1⟩ := h1 L hodd (le_trans (le_max_left _ _) hL) C₁ C Cd hC₁ hC hCd
  obtain ⟨c₂, hc₂, h2⟩ := h2 L hodd (le_trans (le_max_right _ _) hL)
  refine ⟨8 * (1 + a) * C₂ ^ 2, min c₁ c₂, by positivity, lt_min hc₁ hc₂, fun e0 he he' => ?_⟩
  obtain ⟨σ, hσ, h1⟩ := h1 e0 he (le_trans he' (min_le_left _ _))
  refine ⟨σ, hσ, ?_⟩
  intro F m S hFL hamb hm hreg s V v hs hsσ hcold hv U hU X k Γ Γ' z z' y hX hz hz' hy hzz hyz hyz' ht ht' hΓ hΓ'
  exact GaugeChangeDensity.relativeEnergyDensity_le (hFL ▸ hodd) hg ha hC₂ hs hΓ.1 hΓ'.1
    (h2 e0 he (le_trans he' (min_le_right _ _)) F m S hFL hamb hm hreg X k z hz ht).1
    (h1 F m S hFL hamb hm hreg s V v hs hsσ hcold hv U hU X k Γ Γ' z z' y hX hz hz' hy hzz hyz hyz' hΓ hΓ')
end BlockAverages
end YangMills.Construction
end

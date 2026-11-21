import YangMills.Construction.ClusterExpansionOfAStep.OneNumberOfACarriedFamily
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderAtAbelianFields
import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasTheExpansionProof
import YangMills.Construction.SummableBoundsOfTheFlow.OneNumberOfOneTotal
import YangMills.Construction.SummableBoundsOfTheFlow.SumsOfFamilies
import YangMills.Construction.SummableBoundsOfTheFlow.TiltOfTheImage
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.FamilyNorms
open TorusLumps TorusFields BlockAverages
private theorem stepWeight_pos (ℓ : StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
private theorem isCurvatureFamily_of_normBounded {ℓ : StepParameters} {ε ε₃ C : ℝ} {h : LocalDensity}
    (H : IsNormBoundedFamily ℓ ε ε₃ h) (h1 : ε ≤ C) (h3 : ε₃ ≤ C) : IsCurvatureFamily ℓ C h := by
  refine ⟨H.admissible.smooth, H.admissible.gauge, H.admissible.translation, ?_, ?_⟩
  · intro n _ hn y W hW k c X k1 k3 hX
    refine (H.decay n hn y W hW k c X k1 k3 hX).trans ?_
    refine div_le_div_of_nonneg_right ?_ (stepWeight_pos ℓ _).le
    split_ifs <;> assumption
  · intro n n' _ _ hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX
    refine (H.comparison n n' hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX).trans ?_
    exact div_le_div_of_nonneg_right h1 (stepWeight_pos ℓ _).le
private theorem normBounded_of_isCurvatureFamily {ℓ : StepParameters} {C : ℝ} {h : LocalDensity}
    (H : IsCurvatureFamily ℓ C h) : IsNormBoundedFamily ℓ C C h := by
  refine ⟨⟨H.smooth, H.gauge, H.translation⟩, ?_, ?_⟩
  · intro n _ hn y W hW k c X k1 k3 hX
    have := H.decay n hn y W hW k c X k1 k3 hX
    simpa using this
  · intro n n' _ _ hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX
    exact H.local_density n n' hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX
abbrev _root_.YangMills.SharedProofs.p9598 := @normBounded_of_isCurvatureFamily
private theorem normBounded_of_coldExpansion {ℓ : StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional}
    {f : LocalDensity} (hE : ℓ.E ≤ ℓ.E₃) (H : ColdExpansion ℓ t x D f) :
    IsNormBoundedFamily ℓ ℓ.E ℓ.E₃ f := by
  refine ⟨⟨H.smooth, H.gauge, H.translation⟩, ?_, ?_⟩
  · intro n _ hn y W hW k c X k1 k3 hX
    exact H.decay n hn y W hW k c X k1 k3 hX
  · intro n n' _ _ hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX
    exact H.local_density n n' hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX
private theorem centered_add (h h' : LocalDensity) (n : ℕ) (y : TorusSite n) (W : TorusField n) :
    centered (h + h') n y W = centered h n y W + centered h' n y W := by
  simp only [centered, Pi.add_apply]
  ring
private theorem centered_smul (r : ℝ) (h : LocalDensity) (n : ℕ) (y : TorusSite n) (W : TorusField n) :
    centered (r • h) n y W = r * centered h n y W := by
  simp only [centered, Pi.smul_apply, smul_eq_mul]
  ring
private theorem exists_common_curvatureFamily {ℓ : StepParameters} {ε ε₃ ε' ε₃' : ℝ} {h h' : LocalDensity}
    (H : IsNormBoundedFamily ℓ ε ε₃ h) (H' : IsNormBoundedFamily ℓ ε' ε₃' h') :
    ∃ C : ℝ, IsCurvatureFamily ℓ C h ∧ IsCurvatureFamily ℓ C h' :=
  ⟨max (max ε ε₃) (max ε' ε₃'),
    isCurvatureFamily_of_normBounded H ((le_max_left _ _).trans (le_max_left _ _))
      ((le_max_right _ _).trans (le_max_left _ _)),
    isCurvatureFamily_of_normBounded H' ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _))⟩
private theorem unitPlaneCurvature_antisymm (μ ν : Fin 4) :
    unitPlaneCurvature μ ν = - unitPlaneCurvature ν μ := by
  unfold unitPlaneCurvature planeCurvature
  by_cases h1 : μ = 0 ∧ ν = 1
  · obtain ⟨rfl, rfl⟩ := h1
    simp
  · by_cases h2 : μ = 1 ∧ ν = 0
    · obtain ⟨rfl, rfl⟩ := h2
      simp
    · have h1' : ¬ (ν = 0 ∧ μ = 1) := fun h => h2 ⟨h.2, h.1⟩
      have h2' : ¬ (ν = 1 ∧ μ = 0) := fun h => h1 ⟨h.2, h.1⟩
      simp [h1, h2, h1', h2']
abbrev _root_.YangMills.SharedProofs.p4715 := @unitPlaneCurvature_antisymm
private theorem curvaturePairing_unitPlane :
    curvaturePairing unitPlaneCurvature unitPlaneCurvature = 1 := by
  have hq : ‖((quaternionI : imaginaryQuaternions) : ℍ[ℝ])‖ *
      ‖((quaternionI : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    simp [quaternionI]
  have hq1 : ‖((quaternionI : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by
    nlinarith [norm_nonneg ((quaternionI : imaginaryQuaternions) : ℍ[ℝ])]
  unfold curvaturePairing
  rw [Finset.sum_eq_single (0 : Fin 4), Finset.sum_eq_single (1 : Fin 4)]
  · simp [unitPlaneCurvature, planeCurvature, hq1]
  · intro j _ hj
    by_cases h : (0 : Fin 4) < j
    · simp [h, unitPlaneCurvature, planeCurvature, hj]
    · simp [h]
  · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h : i < j
    · have h2 : ¬ (i = 1 ∧ j = 0) := by
        rintro ⟨rfl, rfl⟩
        exact absurd h (by decide)
      simp [h, unitPlaneCurvature, planeCurvature, hi, h2]
    · simp [h]
  · simp
abbrev _root_.YangMills.SharedProofs.p11741 := @curvaturePairing_unitPlane
private theorem coldExpansion_unitPlaneValue (hA : SecondOrderAtAbelianFields) {ℓ : StepParameters}
    (hf : ℓ.Admissible) {t : ℕ} {x : ℝ} {D : TorusFunctional} {f : LocalDensity} {C : ℝ}
    (H : ColdExpansion ℓ t x D f) (Hc : IsCurvatureFamily ℓ C f) : HasUnitPlaneValue f 0 := by
  obtain ⟨a1, -⟩ := hA ℓ hf C f Hc
  exact ⟨fun c c' X X' => ⟨_, a1 c c' X X'⟩,
    H.no_curvature_term unitPlaneCurvature unitPlaneCurvature
      unitPlaneCurvature_antisymm unitPlaneCurvature_antisymm⟩
set_option maxHeartbeats 1000000 in
theorem imageTiltStatement_holds (hs : normBoundedFamilyClosureStatement)
    (hn : curvatureValueLinearityStatement) (ho : equalTotalsEqualLimitStatement)
    (hc : InvariantFamilyCurvatureForm) (hA : SecondOrderAtAbelianFields) : imageTiltStatement := by
  intro ℓ t x x' ε C₀ Na M b₀ d₀ Dp f' c m e g a P hD
  have hf := P.admissible
  have hE3 := P.E_le_E₃
  have hx1 := P.one_le_x
  have hx0 : 0 < x := by linarith
  have hε := P.ε_pos
  have hC₀ := P.C₀_nonneg
  have hNa := P.Na_nonneg
  obtain ⟨hArr, f₂, hcold, -⟩ := hD
  obtain ⟨hmono, hadd, hsmul, -⟩ := hs ℓ
  obtain ⟨nadd, nsmul, fadd, fsmul⟩ := hn ℓ hf
  set b : ℝ := x - x' with hb
  set v : ℝ := x ^ (-(1 / 2 : ℝ)) with hv
  set u : ℝ := x ^ (-(3 / 4 : ℝ)) with hu
  set w : ℝ := x ^ (-(3 / 2 : ℝ)) with hw
  set z : ℝ := x ^ (-(2 : ℝ)) with hz
  have v0 : 0 < v := Real.rpow_pos_of_pos hx0 _
  have u0 : 0 < u := Real.rpow_pos_of_pos hx0 _
  have w0 : 0 < w := Real.rpow_pos_of_pos hx0 _
  have z0 : 0 < z := Real.rpow_pos_of_pos hx0 _
  have zw : z ≤ w := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have wu : w ≤ u := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have qu : x⁻¹ ≤ u := by
    have : x ^ (-(1 : ℝ)) ≤ u := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rwa [Real.rpow_neg_one] at this
  have hfloor := P.small_constants
  have Fa : IsNormBoundedFamily ℓ Na Na a := normBounded_of_isCurvatureFamily P.share_curvatureFamily
  have Fr := P.reference_norm
  have FX := P.excess_norm
  have Fm := P.mean_norm
  have Fe := P.frameChange_norm
  have Fg := P.gas_norm
  have Ff₂ := normBounded_of_coldExpansion hE3 hcold
  have cEq : c = ((c - f' - b₀ • a) + f') + b₀ • a := by
    funext n y W
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have Fc : IsNormBoundedFamily ℓ (C₀ * u + ℓ.E / 2 + |b₀| * Na) (C₀ * u + ℓ.E₃ / 2 + |b₀| * Na) c := by
    rw [cEq]
    exact hadd _ _ _ _ _ _ (hadd _ _ _ _ _ _ FX Fr) (hsmul b₀ _ _ _ Fa)
  have FG := hadd _ _ _ _ _ _ (hadd _ _ _ _ _ _ (hadd _ _ _ _ _ _ Fc Fm) Fe) Fg
  have FJ := hadd _ _ _ _ _ _ (hsmul b _ _ _ Fa) Ff₂
  obtain ⟨vc, nc, bc⟩ := P.value_c
  obtain ⟨vm, nm, bm⟩ := P.value_m
  obtain ⟨ve, ne, be⟩ := P.value_e
  obtain ⟨vg, ng, bg⟩ := P.value_g
  have nG := nadd _ _ _ _ ((hadd _ _ _ _ _ _ (hadd _ _ _ _ _ _ Fc Fm) Fe).admissible) Fg.admissible
    (nadd _ _ _ _ (hadd _ _ _ _ _ _ Fc Fm).admissible Fe.admissible
      (nadd _ _ _ _ Fc.admissible Fm.admissible nc nm) ne) ng
  have na : HasUnitPlaneValue a 1 := by
    refine ⟨P.share_curvatureForm.1, ?_⟩
    have := P.share_curvatureForm.2 unitPlaneCurvature unitPlaneCurvature
      unitPlaneCurvature_antisymm unitPlaneCurvature_antisymm
    rwa [curvaturePairing_unitPlane, one_mul] at this
  have nf₂ : HasUnitPlaneValue f₂ 0 :=
    coldExpansion_unitPlaneValue hA hf hcold (isCurvatureFamily_of_normBounded Ff₂ hE3 le_rfl)
  have nJ := nadd _ _ _ _ ((hsmul b _ _ _ Fa).admissible) Ff₂.admissible (nsmul b a 1 Fa.admissible na) nf₂
  have totA : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ V : TorusField n, IsCold ℓ.threshold V →
      ∑ y, centered (c + m + e + g) n y V = b * ∑ y, centered a n y V + ∑ y, centered f₂ n y V := by
    intro n _ hn' V hV
    rw [← P.log_density_eq n hn' V hV, P.share_sum n hn' V hV]
    have := hcold.form n hn' V hV
    rw [this, hb]
    ring
  have totGJ : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ V : TorusField n, IsCold ℓ.threshold V →
      ∑ y, centered (c + m + e + g) n y V = ∑ y, centered (b • a + f₂) n y V := by
    intro n _ hn' V hV
    rw [totA n hn' V hV]
    simp only [centered_add, centered_smul, Finset.sum_add_distrib, Finset.mul_sum]
  obtain ⟨CG, cG, cJ⟩ := exists_common_curvatureFamily FG FJ
  have hvb : vc + vm + ve + vg = b * 1 + 0 := ho ℓ hf CG _ _ _ _ cG cJ totGJ nG.2 nJ.2
  have hbound : |b - (b₀ + d₀ / x)| ≤ C₀ * w + C₀ * ε * v + 2 * (C₀ * z) := by
    have e1 := abs_le.mp bc
    have e2 := abs_le.mp bm
    have e3 := abs_le.mp be
    have e4 := abs_le.mp bg
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]
  have Czw : C₀ * z ≤ C₀ * w := mul_le_mul_of_nonneg_left zw hC₀
  have hK : C₀ * w + C₀ * ε * v + 2 * (C₀ * z) ≤ 3 * C₀ * (v * ε + w) := by
    have : 0 ≤ C₀ * ε * v := by positivity
    nlinarith
  have hM : 0 ≤ M := (abs_nonneg _).trans P.abs_d₀_le
  have hdx : |d₀ / x| ≤ M * x⁻¹ := by
    rw [abs_div, abs_of_pos hx0, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right P.abs_d₀_le (inv_pos.mpr hx0).le
  have hD : |(-(b - b₀))| ≤ M * x⁻¹ + 3 * C₀ * (v * ε + w) := by
    rw [abs_neg]
    have e1 := abs_le.mp (hbound.trans hK)
    have e2 := abs_le.mp hdx
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [e1.1, e1.2, e2.1, e2.2]
  obtain ⟨H, hH⟩ : ∃ H : LocalDensity, H = imageTilt b₀ b f' c m e g a := ⟨_, rfl⟩
  set εp : ℝ := ε / 8 + imageTiltConstant C₀ Na M * u with hεp
  have FH0 := hadd _ _ _ _ _ _ (hadd _ _ _ _ _ _ (hadd _ _ _ _ _ _
    (hadd _ _ _ _ _ _ FX Fm) Fe) Fg) (hsmul (-(b - b₀)) _ _ _ Fa)
  have hDNa : |(-(b - b₀))| * Na ≤ Na * M * u + 3 * C₀ * Na * (v * ε) + 3 * C₀ * Na * u := by
    have e1 : |(-(b - b₀))| * Na ≤ (M * x⁻¹ + 3 * C₀ * (v * ε + w)) * Na :=
      mul_le_mul_of_nonneg_right hD hNa
    have e2 : Na * M * x⁻¹ ≤ Na * M * u := mul_le_mul_of_nonneg_left qu (by positivity)
    have e3 : 3 * C₀ * Na * w ≤ 3 * C₀ * Na * u := mul_le_mul_of_nonneg_left wu (by positivity)
    nlinarith
  have hfε : (C₀ + 3 * C₀ * Na) * v * ε ≤ 1 / 16 * ε := mul_le_mul_of_nonneg_right hfloor hε.le
  have Czu : C₀ * z ≤ C₀ * u := mul_le_mul_of_nonneg_left (zw.trans wu) hC₀
  set R : ℝ := C₀ * u + C₀ * ε * v + C₀ * z + C₀ * z + |(-(b - b₀))| * Na with hR
  have hR0 : 0 ≤ R := by positivity
  have hα : ε / 16 + R ≤ εp := by
    rw [hεp, hR]
    unfold imageTiltConstant
    nlinarith
  set r : ℝ := ℓ.E₃ / ℓ.E with hr
  have hE0 : 0 < ℓ.E := hf.E_pos
  have hr1 : 1 ≤ r := by
    rw [hr, le_div_iff₀ hE0]
    linarith
  have third : ∀ y : ℝ, thirdOrderSize ℓ y = y * r := by
    intro y
    unfold thirdOrderSize
    rw [hr]
    ring
  have FH : IsNormBoundedFamily ℓ εp (thirdOrderSize ℓ εp) H := by
    rw [hH]
    refine hmono _ _ _ _ _ ?_ ?_ FH0
    · linarith
    · rw [third, third]
      have : ε / 16 * r + R ≤ (ε / 16 + R) * r := by nlinarith
      have h2 : (ε / 16 + R) * r ≤ εp * r := mul_le_mul_of_nonneg_right hα (by linarith)
      linarith
  have GK : c + m + e + g = (f' + H) + b • a := by
    funext n y W
    simp only [hH, imageTilt, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have dK : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ V : TorusField n, IsCold ℓ.threshold V →
      Real.log (Dp n V) - Real.log (Dp n (trivialField n)) =
        -x' * actionAtLevel ℓ.coupling ℓ.side (t + 1) Finset.univ V + ∑ y, centered (f' + H) n y V := by
    intro n _ hn' V hV
    have e1 := P.log_density_eq n hn' V hV
    have e2 := P.share_sum n hn' V hV
    have e3 : ∑ y, centered (c + m + e + g) n y V =
        ∑ y, centered (f' + H) n y V + b * ∑ y, centered a n y V := by
      rw [GK]
      simp only [centered_add (f' + H), centered_smul, Finset.sum_add_distrib, Finset.mul_sum]
    rw [e3, e2, hb] at e1
    linarith
  have carK : SumInvariantUnderIsometries ℓ (f' + H) := by
    intro n _ hn' γ W W' hW hW' hCar
    have a1 := dK n hn' W hW
    have a2 := dK n hn' W' hW'
    have a3 : Dp n W' = Dp n W := (hArr n hn').2.2.2 γ W W' hCar
    have a4 := P.share_invariant n hn' γ W W' hW hW' hCar
    rw [← P.share_sum n hn' W hW] at a1
    rw [← P.share_sum n hn' W' hW', a3, a4] at a2
    linarith
  have FK := hadd _ _ _ _ _ _ Fr FH
  obtain ⟨CK, cK, cf₂⟩ := exists_common_curvatureFamily FK Ff₂
  obtain ⟨lim, bK, hsum⟩ := hc ℓ hf CK (f' + H) cK carK
  have hsumU : HasSum (limitFormTerm (f' + H) unitPlaneCurvature unitPlaneCurvature) bK := by
    have := hsum unitPlaneCurvature unitPlaneCurvature unitPlaneCurvature_antisymm unitPlaneCurvature_antisymm
    rw [curvaturePairing_unitPlane, mul_one] at this
    exact this
  have totK : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ V : TorusField n, IsCold ℓ.threshold V →
      ∑ y, centered (f' + H) n y V = ∑ y, centered f₂ n y V := by
    intro n _ hn' V hV
    have a1 := dK n hn' V hV
    have a2 := hcold.form n hn' V hV
    linarith
  have bK0 : bK = 0 := ho ℓ hf CK _ _ _ _ cK cf₂ totK hsumU nf₂.2
  have formK : HasCurvatureForm (f' + H) 0 := by
    refine ⟨fun c c' X X' => ⟨_, lim c c' X X'⟩, fun A A' hA' hA'' => ?_⟩
    have := hsum A A' hA' hA''
    rw [bK0] at this
    exact this
  have formH : HasVanishingCurvatureForm H := by
    have h1 := fadd _ _ _ _ FK.admissible (hsmul (-1) _ _ _ Fr).admissible formK
      (fsmul (-1) f' 0 Fr.admissible P.reference_curvatureForm)
    have e : (f' + H) + (-1 : ℝ) • f' = H := by
      funext n y W
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e] at h1
    have e0 : (0 : ℝ) + -1 * 0 = 0 := by ring
    rw [e0] at h1
    exact h1
  rw [← hH]
  refine ⟨⟨FH, formH, dK⟩, ?_⟩
  have : x' - (x - b₀ - d₀ / x) = -(b - (b₀ + d₀ / x)) := by
    rw [hb]
    ring
  rw [this, abs_neg]
  exact hbound.trans hK
end YangMills.Construction.FamilyNorms
end

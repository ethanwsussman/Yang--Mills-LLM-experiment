import YangMills.Construction.InfiniteLattice.CoarseStepsAndTheFivePointInequalityProof
import YangMills.Construction.InfiniteLattice.DataOfADiagonalPicture
import YangMills.Construction.InfiniteLattice.DiagonalPictureAtAMirror
import YangMills.Construction.InfiniteLattice.RulesForObservablesIsometriesAndMirrors
import YangMills.Construction.JointSpectrum.ConeRegionIdentity
import YangMills.Construction.JointSpectrum.DiscTwoConstants
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open MeasureTheory Set Filter Topology
open YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert YangMills.Construction.ContractionUnitary
open YangMills.Construction.JointSpectrum YangMills.Construction.DiscGeometry YangMills.Construction.FamilyPolynomials YangMills.Construction.ScalarSpectralMeasures YangMills.Construction.JointSpectrum.SpectralIntegral
open scoped ENNReal ComplexConjugate InnerProductSpace ComplexOrder
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
namespace LinkConeProof
section Abstract
variable {𝒦 𝒦' : Type} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
  [NormedAddCommGroup 𝒦'] [InnerProductSpace ℂ 𝒦'] [CompleteSpace 𝒦']
  {J J' : Type} [Fintype J] [Nonempty J] [Unique J] [Fintype J'] [Nonempty J'] [Unique J']
theorem unitaryMonomial_of_unique (S : CommutingFamily 𝒦 J) (y : J → ℤ) :
    S.unitaryMonomial y = ((S.B default ^ y default : unitary (𝒦 →L[ℂ] 𝒦)) : 𝒦 →L[ℂ] 𝒦) := by
  unfold CommutingFamily.unitaryMonomial
  congr 1
  exact (Finset.noncommProd_congr Finset.univ_unique (fun _ _ => rfl) (by simp)).trans
    (Finset.noncommProd_singleton _ _)
theorem spectralMonomial_of_unique (n : ℕ) (y : J → ℤ) (x : SpectralDomain J) :
    spectralMonomial n y x = (((x.1 : ℝ)) : ℂ) ^ n * (x.2 default : ℂ) ^ y default := by
  simp [spectralMonomial, torusMonomial, Fintype.prod_unique]
theorem continuous_circle_coe : Continuous fun ζ : Circle => (ζ : ℂ) := by
  fun_prop
theorem continuous_spectralMonomial (n : ℕ) (y : J → ℤ) :
    Continuous (spectralMonomial (J := J) n y) := by apply _root_.YangMills.Construction.LatticeConventions.CoarseStepFivePoint.continuous_spectralMonomial <;> assumption
theorem supNormE_ne_top_and_le {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] (f : Y → ℂ)
    (hf : Continuous f) :
    LatticeBasics.supNormE f ≠ ∞ ∧ ∀ y, ‖f y‖ ≤ (LatticeBasics.supNormE f).toReal := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y, ‖f y‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_univ.image hf.norm).bddAbove
    exact ⟨C, fun y => hC ⟨y, mem_univ y, rfl⟩⟩
  have hfin : LatticeBasics.supNormE f ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C)) (iSup_le fun y => ?_)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC y)
  refine ⟨hfin, fun y => ?_⟩
  have h₁ : ‖f y‖ₑ ≤ LatticeBasics.supNormE f := le_iSup (fun y => ‖f y‖ₑ) y
  have h₂ := ENNReal.toReal_mono hfin h₁
  simpa [toReal_enorm] using h₂
def toUnitDisc (x : SpectralDomain J) : closedUnitDisc :=
  ⟨polarToDisc (x.1, x.2 default), polarToDisc_mem_closedUnitDisc _⟩
theorem continuous_toUnitDisc : Continuous (toUnitDisc (J := J)) := by
  refine Continuous.subtype_mk ?_ _
  unfold polarToDisc
  exact (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
    (continuous_circle_coe.comp ((continuous_apply _).comp continuous_snd))
def powerWeight (D : ℕ) (x : SpectralDomain J) : ℝ≥0∞ := ENNReal.ofReal ((x.1 : ℝ) ^ D)
theorem measurable_powerWeight (D : ℕ) : Measurable (powerWeight (J := J) D) := by
  refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
  exact (continuous_subtype_val.comp continuous_fst).pow D
theorem normSq_eval_mul_pow_eq_sum (p : Polynomial ℂ) (D : ℕ) (x : SpectralDomain J) :
    (((‖Polynomial.eval ((toUnitDisc x : closedUnitDisc) : ℂ) p‖ ^ 2 * (x.1 : ℝ) ^ D : ℝ)) : ℂ) =
      ∑ k ∈ Finset.range (p.natDegree + 1), ∑ l ∈ Finset.range (p.natDegree + 1),
        (p.coeff k * conj (p.coeff l)) *
          spectralMonomial (D + k + l) (fun _ => (k : ℤ) - (l : ℤ)) x := by
  set t : ℂ := (((x.1 : ℝ)) : ℂ) with ht
  set ζ : ℂ := (x.2 default : ℂ) with hζ
  have hζ0 : ζ ≠ 0 := Circle.coe_ne_zero _
  have hconj : conj ζ = ζ⁻¹ := by
    rw [hζ, ← Circle.coe_inv_eq_conj, Circle.coe_inv]
  have htc : conj t = t := Complex.conj_ofReal _
  have hz : ((toUnitDisc x : closedUnitDisc) : ℂ) = t * ζ := rfl
  rw [hz, Polynomial.eval_eq_sum_range]
  set P : ℂ := ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * (t * ζ) ^ k with hP
  have hPc : conj P = ∑ l ∈ Finset.range (p.natDegree + 1), conj (p.coeff l) * (t * ζ⁻¹) ^ l := by
    rw [hP, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, map_pow, map_mul, htc, hconj]
  have h₁ : (((‖P‖ ^ 2 * (x.1 : ℝ) ^ D : ℝ)) : ℂ) = P * conj P * t ^ D := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [h₁, hPc, hP, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [spectralMonomial_of_unique, ← ht, ← hζ, zpow_sub₀ hζ0, zpow_natCast, zpow_natCast, mul_pow,
    mul_pow, inv_pow, pow_add, pow_add]
  field_simp
theorem norm_polynomial_A_le (h_poly : FamilyPolynomials.PolynomialCalculusStatement)
    (T : CommutingFamily 𝒦' J') (p : Polynomial ℂ) :
    ‖∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • T.A ^ k‖ ≤
      (LatticeBasics.supNormE fun t : unitInterval => Polynomial.eval ((t : ℝ) : ℂ) p).toReal := by
  obtain ⟨-, -, hsum, -, -, -, -, -, -, -, -, -, -, hnorm⟩ := h_poly 𝒦' J' T
  set s : Finset (ℕ × (J' → ℤ)) :=
    (Finset.range (p.natDegree + 1)).image fun k => (k, (0 : J' → ℤ)) with hs
  set c : ℕ × (J' → ℤ) → ℂ := fun i => p.coeff i.1 with hc
  have hinj : Set.InjOn (fun k : ℕ => (k, (0 : J' → ℤ)))
      (Finset.range (p.natDegree + 1) : Set ℕ) := fun a _ b _ h => (Prod.ext_iff.mp h).1
  have hop : familySum T s c =
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • T.A ^ k := by
    rw [familySum, hs, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hc, familyMonomial, unitaryMonomial_of_unique]
  have hfun : ∀ x : SpectralDomain J', spectralSum s c x =
      Polynomial.eval (((x.1 : ℝ)) : ℂ) p := by
    intro x
    rw [spectralSum, hs, Finset.sum_image hinj, Polynomial.eval_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hc, spectralMonomial_of_unique]
  rw [← hop, ← hsum s c]
  refine (hnorm _ ⟨s, c, fun _ => rfl⟩).trans (ciSup_le fun x => ?_)
  change ‖spectralSum s c x‖ ≤ _
  rw [hfun]
  exact (supNormE_ne_top_and_le (fun t : unitInterval => Polynomial.eval ((t : ℝ) : ℂ) p)
    (by fun_prop)).2 x.1
theorem norm_conj_polynomial_B_le (h_poly : FamilyPolynomials.PolynomialCalculusStatement)
    (T : CommutingFamily 𝒦' J') (p : Polynomial ℂ) :
    ‖∑ l ∈ Finset.range (p.natDegree + 1),
        conj (p.coeff l) • (T.B default : 𝒦' →L[ℂ] 𝒦') ^ l‖ ≤
      (LatticeBasics.supNormE fun ζ : Circle => Polynomial.eval (ζ : ℂ) p).toReal := by
  obtain ⟨-, -, hsum, -, -, -, -, -, -, -, -, -, -, hnorm⟩ := h_poly 𝒦' J' T
  set s : Finset (ℕ × (J' → ℤ)) :=
    (Finset.range (p.natDegree + 1)).image fun l : ℕ => (0, fun _ => (l : ℤ)) with hs
  set c : ℕ × (J' → ℤ) → ℂ := fun i => conj (p.coeff (i.2 default).toNat) with hc
  have hinj : Set.InjOn (fun l : ℕ => ((0 : ℕ), fun _ : J' => (l : ℤ)))
      (Finset.range (p.natDegree + 1) : Set ℕ) := by
    intro a _ b _ h
    have h₁ : (a : ℤ) = b := congrFun (Prod.ext_iff.mp h).2 default
    exact_mod_cast h₁
  have hop : familySum T s c =
      ∑ l ∈ Finset.range (p.natDegree + 1),
        conj (p.coeff l) • (T.B default : 𝒦' →L[ℂ] 𝒦') ^ l := by
    rw [familySum, hs, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [hc, familyMonomial, unitaryMonomial_of_unique]
  have hfun : ∀ x : SpectralDomain J', spectralSum s c x =
      conj (Polynomial.eval (((x.2 default)⁻¹ : Circle) : ℂ) p) := by
    intro x
    rw [spectralSum, hs, Finset.sum_image hinj, Polynomial.eval_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hz : conj (((x.2 default)⁻¹ : Circle) : ℂ) = (x.2 default : ℂ) := by
      rw [Circle.coe_inv_eq_conj, Complex.conj_conj]
    rw [map_mul, map_pow, hz]
    simp [hc, spectralMonomial_of_unique]
  rw [← hop, ← hsum s c]
  refine (hnorm _ ⟨s, c, fun _ => rfl⟩).trans (ciSup_le fun x => ?_)
  change ‖spectralSum s c x‖ ≤ _
  rw [hfun, RCLike.norm_conj]
  exact (supNormE_ne_top_and_le (fun ζ : Circle => Polynomial.eval (ζ : ℂ) p)
    (by fun_prop)).2 (x.2 default)⁻¹
theorem sqIntegralLeSupProduct_of_matrixElements
    (h_scalar : ScalarSpectralMeasures.ScalarSpectralMeasuresStatement)
    (h_poly : FamilyPolynomials.PolynomialCalculusStatement)
    (S : CommutingFamily 𝒦 J) (T : CommutingFamily 𝒦' J') (ψ : 𝒦) (β α : 𝒦') (D : ℕ)
    (hread : ∀ k l : ℕ,
      inner ℂ ψ (familyMonomial S (D + k + l) (fun _ => (k : ℤ) - (l : ℤ)) ψ) =
        inner ℂ β ((T.A ^ k * (T.B default : 𝒦' →L[ℂ] 𝒦') ^ l) α))
    (p : Polynomial ℂ) :
    DiscTwoConstants.SqIntegralLeSupProduct
      (((spectralMeasure S ψ).withDensity (powerWeight D)).map toUnitDisc) (‖β‖ * ‖α‖) p := by
  obtain ⟨-, -, -, hψ, -⟩ := h_scalar 𝒦 J S
  obtain ⟨⟨hfin, hmom⟩, -⟩ := hψ ψ
  set m := spectralMeasure S ψ with hm
  set I : SpectralDomain J → ℝ := fun x =>
    ‖Polynomial.eval ((toUnitDisc x : closedUnitDisc) : ℂ) p‖ ^ 2 * (x.1 : ℝ) ^ D with hI
  have hIc : Continuous I := by
    have h₁ : Continuous fun x : SpectralDomain J =>
        Polynomial.eval ((toUnitDisc x : closedUnitDisc) : ℂ) p :=
      (Polynomial.continuous p).comp (continuous_subtype_val.comp continuous_toUnitDisc)
    exact (h₁.norm.pow 2).mul ((continuous_subtype_val.comp continuous_fst).pow D)
  have hIint : Integrable I m :=
    hIc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI0 : ∀ x, 0 ≤ I x := fun x =>
    mul_nonneg (sq_nonneg _) (pow_nonneg x.1.2.1 D)
  have hleft : ∫⁻ z, ‖Polynomial.eval ((z : closedUnitDisc) : ℂ) p‖ₑ ^ 2
      ∂(((spectralMeasure S ψ).withDensity (powerWeight D)).map toUnitDisc) =
      ENNReal.ofReal (∫ x, I x ∂m) := by
    have hg : Measurable fun z : closedUnitDisc => ‖Polynomial.eval (z : ℂ) p‖ₑ ^ 2 :=
      (((Polynomial.continuous p).comp continuous_subtype_val).measurable.enorm).pow_const 2
    rw [lintegral_map hg continuous_toUnitDisc.measurable,
      ofReal_integral_eq_lintegral_ofReal hIint (Eventually.of_forall hI0)]
    refine (lintegral_withDensity_eq_lintegral_mul _ (measurable_powerWeight D)
      (hg.comp continuous_toUnitDisc.measurable)).trans (lintegral_congr fun x => ?_)
    have ht : 0 ≤ (x.1 : ℝ) ^ D := pow_nonneg x.1.2.1 D
    simp only [Pi.mul_apply, Function.comp_apply, powerWeight, hI]
    rw [ENNReal.ofReal_mul (sq_nonneg _), mul_comm, ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm]
  set Pop : 𝒦' →L[ℂ] 𝒦' := ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • T.A ^ k with hPop
  set Qop : 𝒦' →L[ℂ] 𝒦' := ∑ l ∈ Finset.range (p.natDegree + 1),
    conj (p.coeff l) • (T.B default : 𝒦' →L[ℂ] 𝒦') ^ l with hQop
  have hint : ((∫ x, I x ∂m : ℝ) : ℂ) = inner ℂ β ((Pop * Qop) α) := by
    rw [← integral_complex_ofReal]
    have hfun : (fun x => ((I x : ℝ) : ℂ)) = fun x =>
        ∑ k ∈ Finset.range (p.natDegree + 1), ∑ l ∈ Finset.range (p.natDegree + 1),
          (p.coeff k * conj (p.coeff l)) *
            spectralMonomial (D + k + l) (fun _ => (k : ℤ) - (l : ℤ)) x := by
      funext x
      exact normSq_eval_mul_pow_eq_sum p D x
    have hmint : ∀ (n : ℕ) (y : J → ℤ), Integrable (spectralMonomial n y) m := fun n y =>
      (continuous_spectralMonomial n y).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [hfun, integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (hmint _ _).const_mul _]
    have hprod : (Pop * Qop) α = ∑ k ∈ Finset.range (p.natDegree + 1),
        ∑ l ∈ Finset.range (p.natDegree + 1), (p.coeff k * conj (p.coeff l)) •
          (T.A ^ k * (T.B default : 𝒦' →L[ℂ] 𝒦') ^ l) α := by
      rw [hPop, hQop, Finset.sum_mul_sum]
      simp only [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [smul_mul_smul_comm]
      rfl
    rw [hprod, inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => (hmint _ _).const_mul _, inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, inner_smul_right, ← hread k l, hmom]
  have hsup₁ := supNormE_ne_top_and_le (fun t : unitInterval => Polynomial.eval ((t : ℝ) : ℂ) p)
    (by fun_prop)
  have hsup₂ := supNormE_ne_top_and_le (fun ζ : Circle => Polynomial.eval (ζ : ℂ) p) (by fun_prop)
  have hP := norm_polynomial_A_le h_poly T p
  have hQ := norm_conj_polynomial_B_le h_poly T p
  set M₁ := (LatticeBasics.supNormE
    fun t : unitInterval => Polynomial.eval ((t : ℝ) : ℂ) p).toReal with hM₁
  set M₂ := (LatticeBasics.supNormE
    fun ζ : Circle => Polynomial.eval (ζ : ℂ) p).toReal with hM₂
  have hbound : (∫ x, I x ∂m) ≤ ‖β‖ * ‖α‖ * M₁ * M₂ := by
    have h₁ : (∫ x, I x ∂m) = ‖inner ℂ β ((Pop * Qop) α)‖ := by
      rw [← hint, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg hI0)]
    have h₂ : ‖(Pop * Qop) α‖ ≤ M₁ * M₂ * ‖α‖ :=
      ((Pop * Qop).le_opNorm α).trans (mul_le_mul_of_nonneg_right
        ((norm_mul_le _ _).trans (mul_le_mul hP hQ (norm_nonneg _)
          ((norm_nonneg _).trans hP))) (norm_nonneg _))
    rw [h₁]
    calc ‖inner ℂ β ((Pop * Qop) α)‖ ≤ ‖β‖ * ‖(Pop * Qop) α‖ := norm_inner_le_norm _ _
      _ ≤ ‖β‖ * (M₁ * M₂ * ‖α‖) := mul_le_mul_of_nonneg_left h₂ (norm_nonneg _)
      _ = ‖β‖ * ‖α‖ * M₁ * M₂ := by ring
  unfold DiscTwoConstants.SqIntegralLeSupProduct
  rw [hleft]
  have hM₁0 : 0 ≤ M₁ := ENNReal.toReal_nonneg
  have hM₂0 : 0 ≤ M₂ := ENNReal.toReal_nonneg
  calc ENNReal.ofReal (∫ x, I x ∂m) ≤ ENNReal.ofReal (‖β‖ * ‖α‖ * M₁ * M₂) :=
        ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (‖β‖ * ‖α‖) * ENNReal.ofReal M₁ * ENNReal.ofReal M₂ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    _ = _ := by
        rw [hM₁, hM₂, ENNReal.ofReal_toReal hsup₁.1, ENNReal.ofReal_toReal hsup₂.1]
theorem spectralMeasure_coneExterior_eq_zero
    (h_scalar : ScalarSpectralMeasures.ScalarSpectralMeasuresStatement)
    (h_poly : FamilyPolynomials.PolynomialCalculusStatement)
    (h_two : DiscTwoConstants.DiscTwoConstantsStatement)
    (h_disc : ConeIdentity.ConeIdentityStatement)
    (S : CommutingFamily 𝒦 J) (T : CommutingFamily 𝒦' J') (ψ : 𝒦) (β α : 𝒦') (D : ℕ)
    (hread : ∀ k l : ℕ,
      inner ℂ ψ (familyMonomial S (D + k + l) (fun _ => (k : ℤ) - (l : ℤ)) ψ) =
        inner ℂ β ((T.A ^ k * (T.B default : 𝒦' →L[ℂ] 𝒦') ^ l) α)) :
    spectralMeasure S ψ (coneExteriorOf J) = 0 := by
  obtain ⟨-, -, -, hψ, -⟩ := h_scalar 𝒦 J S
  obtain ⟨⟨hfin, -⟩, -⟩ := hψ ψ
  set m := spectralMeasure S ψ with hm
  have hw : IsFiniteMeasure (m.withDensity (powerWeight D)) := by
    refine isFiniteMeasure_withDensity (ne_top_of_le_ne_top (measure_ne_top m univ) ?_)
    calc ∫⁻ x, powerWeight D x ∂m ≤ ∫⁻ _, 1 ∂m := lintegral_mono fun x => ?_
      _ = m univ := by simp
    have h₁ : (x.1 : ℝ) ^ D ≤ 1 := pow_le_one₀ x.1.2.1 x.1.2.2
    simpa [powerWeight] using h₁
  have hregion : MeasurableSet nearRegion := by
    have h₁ : MeasurableSet closedUnitDisc :=
      (isClosed_le continuous_norm continuous_const).measurableSet
    have h₂ : MeasurableSet {z : ℂ | ‖1 + z‖ ^ 2 < 4 * ‖z‖} :=
      (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
    exact h₁.inter h₂
  have hzero := h_two (m.withDensity (powerWeight D) |>.map toUnitDisc)
    ⟨‖β‖ * ‖α‖, by positivity,
      sqIntegralLeSupProduct_of_matrixElements h_scalar h_poly S T ψ β α D hread⟩
  have hpre : MeasurableSet (toUnitDisc (J := J) ⁻¹' (Subtype.val ⁻¹' nearRegion)) :=
    continuous_toUnitDisc.measurable (measurable_subtype_coe hregion)
  rw [Measure.map_apply continuous_toUnitDisc.measurable (measurable_subtype_coe hregion),
    withDensity_apply _ hpre, lintegral_eq_zero_iff (measurable_powerWeight D),
    EventuallyEq, ae_restrict_iff' hpre, ae_iff] at hzero
  refine measure_mono_null (fun x hx => ?_) hzero
  have hmaps := h_disc.2.2.2.2.2.1
  have hx' : (x.1, x.2 default) ∈ coneExterior := hx
  simp only [mem_setOf_eq, not_forall]
  refine ⟨hmaps hx', ?_⟩
  have ht : 0 < (x.1 : ℝ) := hx'.1
  simp only [powerWeight, Pi.zero_apply, ENNReal.ofReal_eq_zero, not_le]
  exact pow_pos ht D
def coneDefectOf (x : SpectralDomain J) : ℝ := coneDefect x.1 (x.2 default)
theorem continuous_coneDefectOf : Continuous (coneDefectOf (J := J)) := by
  have h₁ : Continuous fun x : SpectralDomain J => (x.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have h₂ : Continuous fun x : SpectralDomain J => ((x.2 default : Circle) : ℂ) :=
    continuous_circle_coe.comp ((continuous_apply _).comp continuous_snd)
  unfold coneDefectOf coneDefect
  exact ((continuous_const.sub h₁).pow 2).sub (h₁.mul ((continuous_const.sub h₂).norm.pow 2))
theorem coneExteriorOf_eq (h_disc : ConeIdentity.ConeIdentityStatement) :
    coneExteriorOf J = {x | coneDefectOf x < 0} := by
  ext x
  change (x.1, x.2 default) ∈ coneExterior ↔ _
  rw [h_disc.2.2.2.2.1]
  rfl
theorem coneInteriorOf_eq_nonnegSet :
    coneInteriorOf J = coneDefectNonnegSet J := by
  ext x
  simp [coneInteriorOf, coneDefectNonnegSet, coneDefect]
theorem coneDefectNonnegSet_eq :
    coneDefectNonnegSet J = {x | 0 ≤ coneDefectOf x} := rfl
theorem coneInteriorOf_eq_compl (h_disc : ConeIdentity.ConeIdentityStatement) :
    coneInteriorOf J = (coneExteriorOf J)ᶜ := by
  rw [coneInteriorOf_eq_nonnegSet, coneDefectNonnegSet_eq, coneExteriorOf_eq h_disc]
  ext x
  simp
theorem isClosed_coneInteriorOf : IsClosed (coneInteriorOf J) := by
  rw [coneInteriorOf_eq_nonnegSet, coneDefectNonnegSet_eq]
  exact isClosed_le continuous_const continuous_coneDefectOf
theorem spectralIntegral_coneDefect (h_calc : JointSpectrum.BorelCalculus.BorelCalculusStatement)
    (h_poly : FamilyPolynomials.PolynomialCalculusStatement)
    (h_disc : ConeIdentity.ConeIdentityStatement) (S : CommutingFamily 𝒦 J) :
    spectralIntegral S (fun x => ((coneDefectOf x : ℝ) : ℂ)) =
      ⇑((ContinuousLinearMap.id ℂ 𝒦 - S.A) ^ 2 -
        S.A * ((2 : ℂ) • ContinuousLinearMap.id ℂ 𝒦 - (S.B default : 𝒦 →L[ℂ] 𝒦) -
          ContinuousLinearMap.adjoint (S.B default : 𝒦 →L[ℂ] 𝒦))) := by
  obtain ⟨-, hb, hc, -⟩ := h_calc 𝒦 J S
  obtain ⟨-, -, -, -, hadd, hsmul, -, -, hopadd, hopsmul, -, -, -, -⟩ := h_poly 𝒦 J S
  have hmem : ∀ (n : ℕ) (y : J → ℤ), spectralMonomial (J := J) n y ∈ spectralPolynomials J :=
    fun n y => ⟨{(n, y)}, fun _ => 1, fun p => by simp⟩
  have hop : ∀ (n : ℕ) (y : J → ℤ),
      polynomialCalculus S (spectralMonomial n y) = familyMonomial S n y := fun n y =>
    DFunLike.coe_injective ((hb _ (hmem n y)).2.symm.trans (hc n y).2)
  set q : SpectralDomain J → ℂ :=
    spectralMonomial 0 0 + (-4 : ℂ) • spectralMonomial 1 0 + spectralMonomial 2 0 +
      spectralMonomial 1 (fun _ => 1) + spectralMonomial 1 (fun _ => -1) with hq
  have hfun : (fun x => ((coneDefectOf x : ℝ) : ℂ)) = q := by
    funext x
    have hn := h_disc.2.2.2.1 (x.2 default : ℂ) (Circle.norm_coe _)
    have hconj : conj ((x.2 default : Circle) : ℂ) = ((x.2 default : Circle) : ℂ)⁻¹ := by
      rw [← Circle.coe_inv_eq_conj, Circle.coe_inv]
    simp only [hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, spectralMonomial_of_unique,
      coneDefectOf, coneDefect]
    push_cast at hn ⊢
    rw [hn, hconj]
    simp only [Pi.zero_apply, zpow_zero, zpow_one, zpow_neg, pow_zero, pow_one]
    ring
  have hqmem : q ∈ spectralPolynomials J :=
    hadd _ (hadd _ (hadd _ (hadd _ (hmem _ _) _ (hsmul _ _ (hmem _ _))) _ (hmem _ _)) _ (hmem _ _))
      _ (hmem _ _)
  rw [hfun, (hb q hqmem).2]
  congr 1
  have h₀ : familyMonomial S 0 0 = 1 := by
    simp [familyMonomial, unitaryMonomial_of_unique]
  have h₁ : familyMonomial S 1 0 = S.A := by
    simp [familyMonomial, unitaryMonomial_of_unique]
  have h₂ : familyMonomial S 2 0 = S.A ^ 2 := by
    simp [familyMonomial, unitaryMonomial_of_unique]
  have h₃ : familyMonomial S 1 (fun _ => 1) = S.A * (S.B default : 𝒦 →L[ℂ] 𝒦) := by
    simp [familyMonomial, unitaryMonomial_of_unique]
  have h₄ : familyMonomial S 1 (fun _ => -1) =
      S.A * ContinuousLinearMap.adjoint (S.B default : 𝒦 →L[ℂ] 𝒦) := by
    simp only [familyMonomial, unitaryMonomial_of_unique, pow_one, zpow_neg, zpow_one]
    rfl
  rw [hq, hopadd _ (hadd _ (hadd _ (hadd _ (hmem _ _) _ (hsmul _ _ (hmem _ _))) _ (hmem _ _)) _
    (hmem _ _)) _ (hmem _ _), hopadd _ (hadd _ (hadd _ (hmem _ _) _ (hsmul _ _ (hmem _ _))) _
    (hmem _ _)) _ (hmem _ _), hopadd _ (hadd _ (hmem _ _) _ (hsmul _ _ (hmem _ _))) _ (hmem _ _),
    hopadd _ (hmem _ _) _ (hsmul _ _ (hmem _ _)), hopsmul _ _ (hmem _ _), hop, hop, hop, hop, hop,
    h₀, h₁, h₂, h₃, h₄]
  have h₅ : (-4 : ℂ) • S.A = -S.A - S.A - S.A - S.A := by module
  have h₆ : (2 : ℂ) • ContinuousLinearMap.id ℂ 𝒦 = 1 + 1 := by
    rw [two_smul]
    rfl
  have h₇ : ContinuousLinearMap.id ℂ 𝒦 = 1 := rfl
  rw [h₅, h₆, h₇]
  noncomm_ring
theorem opGE_of_coneExterior (h_calc : JointSpectrum.BorelCalculus.BorelCalculusStatement)
    (h_facts : JointSpectrum.CalculusApplications.CalculusApplicationsStatement)
    (h_poly : FamilyPolynomials.PolynomialCalculusStatement)
    (h_disc : ConeIdentity.ConeIdentityStatement)
    (S : CommutingFamily 𝒦 J) (h₀ : jointSpectralMeasure S (coneExteriorOf J) = 0) :
    OpGE ((idOp 𝒦 - S.A) ^ 2)
      (S.A * ((2 : ℂ) • idOp 𝒦 - (S.B default : 𝒦 →L[ℂ] 𝒦) -
        ContinuousLinearMap.adjoint (S.B default : 𝒦 →L[ℂ] 𝒦))) := by
  obtain ⟨hfa, -⟩ := h_facts 𝒦 J S
  have hbdd : ∃ M : ℝ, ∀ x : SpectralDomain J, |coneDefectOf x| ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_univ.image (continuous_coneDefectOf (J := J)).norm).bddAbove
    exact ⟨M, fun x => hM ⟨x, mem_univ x, rfl⟩⟩
  obtain ⟨C, hC, hsa, hiff⟩ := hfa coneDefectOf continuous_coneDefectOf.measurable hbdd
  have hCeq : C = (ContinuousLinearMap.id ℂ 𝒦 - S.A) ^ 2 -
      S.A * ((2 : ℂ) • ContinuousLinearMap.id ℂ 𝒦 - (S.B default : 𝒦 →L[ℂ] 𝒦) -
        ContinuousLinearMap.adjoint (S.B default : 𝒦 →L[ℂ] 𝒦)) :=
    DFunLike.coe_injective (hC.trans (spectralIntegral_coneDefect h_calc h_poly h_disc S))
  have hpos : 0 ≤ C := hiff.mpr (by rw [← coneExteriorOf_eq h_disc]; exact h₀)
  set X : 𝒦 →L[ℂ] 𝒦 := S.A * ((2 : ℂ) • ContinuousLinearMap.id ℂ 𝒦 -
    (S.B default : 𝒦 →L[ℂ] 𝒦) - ContinuousLinearMap.adjoint (S.B default : 𝒦 →L[ℂ] 𝒦)) with hX
  set Y : 𝒦 →L[ℂ] 𝒦 := (ContinuousLinearMap.id ℂ 𝒦 - S.A) ^ 2 with hY
  have hAstar : star S.A = S.A := S.isSelfAdjoint_A
  have hcomm : Commute S.A (star (S.B default : 𝒦 →L[ℂ] 𝒦)) := by
    have := (S.commute_A_B default).star_star
    rwa [hAstar] at this
  have hXsa : IsSelfAdjoint X := by
    rw [IsSelfAdjoint, hX, star_mul, hAstar]
    have hW : star ((2 : ℂ) • ContinuousLinearMap.id ℂ 𝒦 - (S.B default : 𝒦 →L[ℂ] 𝒦) -
        ContinuousLinearMap.adjoint (S.B default : 𝒦 →L[ℂ] 𝒦)) =
        (2 : ℂ) • ContinuousLinearMap.id ℂ 𝒦 - (S.B default : 𝒦 →L[ℂ] 𝒦) -
          ContinuousLinearMap.adjoint (S.B default : 𝒦 →L[ℂ] 𝒦) := by
      have h₁ : star (ContinuousLinearMap.id ℂ 𝒦) = ContinuousLinearMap.id ℂ 𝒦 := star_one _
      rw [← ContinuousLinearMap.star_eq_adjoint, star_sub, star_sub, star_smul, h₁, star_star]
      simp only [star_trivial, RCLike.star_def, map_ofNat]
      abel
    rw [hW]
    refine Commute.eq ?_ |>.symm
    refine ((Commute.sub_right ?_ (S.commute_A_B default)).sub_right ?_)
    · exact (Commute.one_right S.A).smul_right (2 : ℂ)
    · rw [← ContinuousLinearMap.star_eq_adjoint]
      exact hcomm
  have hYsa : IsSelfAdjoint Y := by
    have h₁ : IsSelfAdjoint (ContinuousLinearMap.id ℂ 𝒦 - S.A) :=
      (IsSelfAdjoint.one _).sub S.isSelfAdjoint_A
    exact h₁.pow 2
  have hXb := (isSymmetricOp_iff X).mpr hXsa
  have hYb := (isSymmetricOp_iff Y).mpr hYsa
  have hCb := (isSymmetricOp_iff C).mpr hsa
  refine ⟨hXb, hYb, fun ψ => ?_⟩
  have hre : 0 ≤ (inner ℂ ψ (C ψ)).re := by
    have h₁ := (ContinuousLinearMap.isPositive_def.mp
      ((ContinuousLinearMap.nonneg_iff_isPositive C).mp hpos)).2 ψ
    change 0 ≤ (inner ℂ (C ψ) ψ).re at h₁
    rwa [← inner_conj_symm, Complex.conj_re] at h₁
  have hin : inner ℂ ψ (C ψ) = inner ℂ ψ (Y ψ) - inner ℂ ψ (X ψ) := by
    rw [hCeq, ContinuousLinearMap.sub_apply, inner_sub_right]
  rw [Complex.le_def]
  refine ⟨?_, ?_⟩
  · rw [hin, Complex.sub_re] at hre
    linarith
  · rw [hXb.inner_self_apply_im_eq_zero, hYb.inner_self_apply_im_eq_zero]
theorem jointSpectralMeasure_eq_zero_of_denseRange
    (h_calc : JointSpectrum.BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily 𝒦 J) {ι : Type*} (cls : ι → 𝒦) (hd : DenseRange cls)
    (Δ : Set (SpectralDomain J)) (hΔ : MeasurableSet Δ)
    (h : ∀ i, spectralMeasure S (cls i) Δ = 0) : jointSpectralMeasure S Δ = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨P, hP, -⟩, hT, -⟩ := h_calc 𝒦 J S
  have hPE : ⇑(P.E ⟨Δ, hΔ⟩) = jointSpectralMeasure S Δ := hP ⟨Δ, hΔ⟩
  have hzero : ∀ i, P.E ⟨Δ, hΔ⟩ (cls i) = 0 := fun i => by
    have h₁ := (hT Δ (cls i) hΔ).2
    rw [h i, ← hPE] at h₁
    simpa using h₁
  have hC : ⇑(P.E ⟨Δ, hΔ⟩) = fun _ => 0 :=
    hd.equalizer (P.E ⟨Δ, hΔ⟩).continuous continuous_const (funext hzero)
  rw [← hPE, hC]
  rfl
end Abstract
section Lattice
open NormalHyperplane
open InfiniteLattice (GaugeField IsSymmetricUnder IsBoundedObservable LatticeSymmetry LatticePoint
  localRegionObservables boundedRegionObservables axisStep shift)
open ObservableRules
theorem exists_cube_radius (a : Spacing) (Q : Set Point) (hQ : Bornology.IsBounded Q) :
    ∃ R : ℕ, ∀ x ∈ Q, ∀ κ, |x κ| ≤ (R : ℝ) * (a : ℝ) := by
  obtain ⟨r, hr⟩ := hQ.subset_closedBall (0 : Point)
  obtain ⟨R, hR⟩ := exists_nat_ge (r / (a : ℝ))
  refine ⟨R, fun x hx κ => ?_⟩
  have h₁ : ‖x‖ ≤ r := by simpa using hr hx
  have h₂ : |x κ| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x κ
  exact (h₂.trans h₁).trans ((div_le_iff₀ a.2).mp hR)
theorem euclidDot_diagonal {μ lam : Direction} (x : Point) :
    euclidDot (basisVector μ + basisVector lam) x = x μ + x lam := by
  simp [euclidDot, basisVector, add_mul, Finset.sum_add_distrib, Pi.single_apply]
theorem euclidNorm_diagonal_sq {μ lam : Direction} (hne : μ ≠ lam) :
    euclidNorm (basisVector μ + basisVector lam) ^ 2 = 2 := by
  rw [euclidNorm_sq_eq_dotProduct]
  change euclidDot (basisVector μ + basisVector lam) (basisVector μ + basisVector lam) = 2
  rw [euclidDot_diagonal]
  simp [basisVector, Pi.single_apply, hne, hne.symm]
  norm_num
theorem reflect_diagonal_add {μ lam : Direction} (hne : μ ≠ lam) (c : ℝ) (x : Point) :
    (NormalHyperplane.diagonal μ lam hne c).reflect x μ +
        (NormalHyperplane.diagonal μ lam hne c).reflect x lam =
      2 * c - (x μ + x lam) := by
  have h₁ : (NormalHyperplane.diagonal μ lam hne c).normal = basisVector μ + basisVector lam := rfl
  have h₂ : (NormalHyperplane.diagonal μ lam hne c).level = c := rfl
  simp only [NormalHyperplane.reflect, h₁, h₂, euclidNorm_diagonal_sq hne, euclidDot_diagonal]
  simp [basisVector, Pi.single_apply, hne, hne.symm]
  ring
theorem coe_zpow_eq_zpowOp {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (u : unitary (H →L[ℂ] H))
    (hu : IsUnitaryMap ((u : H →L[ℂ] H) : H →ₗ[ℂ] H)) (y : ℤ) :
    ((u ^ y : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = zpowOp (u : H →L[ℂ] H) y := by
  rcases le_or_gt 0 y with hy | hy
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hy
    rw [zpowOp_natCast, zpow_natCast]
    rfl
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, y = -(n : ℤ) := ⟨(-y).toNat, by omega⟩
    rw [zpowOp_of_neg _ hy, zpow_neg, zpow_natCast, ← inv_pow]
    have hinv : opInv (u : H →L[ℂ] H) = ((u⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
      have h₁ := (isTwoSidedInverse_opInv hu).2
      have h₂ : (u : H →L[ℂ] H) * ((u⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = 1 :=
        congrArg Subtype.val (mul_inv_cancel u)
      exact left_inv_eq_right_inv h₁ h₂
    have hn : (-(-(n : ℤ))).toNat = n := by simp
    rw [hinv, hn]
    rfl
theorem coe_nsmul_axisStep_apply (a : Spacing) (n : ℕ) (μ κ : Direction) :
    ((n • axisStep (a : ℝ) μ : LatticePoint (a : ℝ)) : Point) κ =
      (n : ℝ) * (Pi.single μ (a : ℝ) : Point) κ := by
  simp [axisStep]
theorem nsmul_steps_eq (a : Spacing) {μ lam : Direction} (hne : μ ≠ lam) (D k l : ℕ) :
    (k • DiagonalMirror.normalStep a μ lam +
        ∑ _i : Fin 1, (l : ℤ) • DiagonalMirror.tangentStep a μ lam) + D • axisStep (a : ℝ) μ =
      (D + k + l) • axisStep (a : ℝ) μ + ((k : ℤ) - (l : ℤ)) • axisStep (a : ℝ) lam := by
  apply Subtype.ext
  funext κ
  simp only [DiagonalMirror.normalStep, DiagonalMirror.tangentStep, axisStep, Finset.univ_unique,
    Finset.sum_singleton, AddSubgroup.coe_add, AddSubgroupClass.coe_nsmul, AddSubgroupClass.coe_zsmul,
    Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, nsmul_eq_mul, zsmul_eq_mul, basisVector]
  by_cases h₁ : κ = μ
  · subst h₁
    simp [Pi.single_apply, hne]
    ring
  · by_cases h₂ : κ = lam
    · subst h₂
      simp [Pi.single_apply, h₁]
      ring
    · simp [Pi.single_apply, h₁, h₂]
theorem spectralMeasure_linkClass_coneExterior
    (h_rec : MirrorReconstruction)
    (h_diag : DiagonalPictureExpansion.Statement)
    (h_action : InfiniteLattice.SymmetryActionOnObservables)
    (h_rules : ObservableRules.AllRules)
    (h_scalar : ScalarSpectralMeasures.ScalarSpectralMeasuresStatement)
    (h_poly : FamilyPolynomials.PolynomialCalculusStatement)
    (h_two : DiscTwoConstants.DiscTwoConstantsStatement)
    (h_disc : ConeIdentity.ConeIdentityStatement)
    (a : Spacing) {μ lam : Direction} (hne : μ ≠ lam)
    (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν]
    (hcond : PairConditions hne ν)
    (hlink : LinkFrame.TransferMatrixElements a μ ν)
    (F : LinkFrame.upperAlgebra a μ) :
    spectralMeasure (LinkFrame.singleShiftFamily a μ ν ⟨lam, hne.symm⟩)
        (LinkFrame.linkClass a μ ν F)
        (coneExteriorOf (SingleTransverse (μ := μ) ⟨lam, hne.symm⟩)) = 0 := by
  have ha : (0 : ℝ) < (a : ℝ) := a.2
  obtain ⟨hgrow, -, -, hinvr, hcarry, hadd, -, hrefl, -, -⟩ := h_rules a
  obtain ⟨-, -, hkeeps, -⟩ := h_action a
  have hFmem : F.1 ∈ localRegionObservables (a : ℝ) (LinkFrame.linkPlane a μ).upperHalfSpace := F.2
  obtain ⟨Qb, hQb, hF⟩ := Set.mem_iUnion₂.mp hFmem
  have hQb' : Bornology.IsBounded Qb := hQb
  obtain ⟨R, hR⟩ := exists_cube_radius a Qb hQb'
  set QA : Set Point := (LinkFrame.linkPlane a μ).upperHalfSpace ∩ Qb with hQA
  have hFobs : IsBoundedObservable F.1 := hF.1
  have hFloc : F.1 ∈ localRegionObservables (a : ℝ) QA :=
    Set.mem_iUnion₂.mpr ⟨QA, hQb'.subset inter_subset_right, by rwa [inter_self]⟩
  have hxμ : ∀ x ∈ QA, -((a : ℝ) / 2) ≤ x μ := fun x hx => by
    have h₁ : -((a : ℝ) / 2) ≤ euclidDot (basisVector μ) x := hx.1
    simpa [euclidDot, basisVector, Pi.single_apply] using h₁
  have hxl : ∀ x ∈ QA, |x lam| ≤ (R : ℝ) * (a : ℝ) := fun x hx => hR x hx.2 lam
  set c : ℝ := ((R : ℤ) : ℝ) * (a : ℝ) with hcdef
  have hcR : c = (R : ℝ) * (a : ℝ) := by rw [hcdef]; push_cast; rfl
  have hc : ∃ q : ℤ, c = (q : ℝ) * (a : ℝ) := ⟨R, rfl⟩
  have hS := DiagonalMirror.diagonal_isLatticeMirror a hne hc
  have hS' := DiagonalMirror.shifted_isLatticeMirror a hne hc
  have hrp : NormalHyperplane.IsReflectionPositiveAcrossMirror hS ν := hcond.2.2 (R : ℤ)
  have hrp' : NormalHyperplane.IsReflectionPositiveAcrossMirror hS' ν :=
    LinkFrame.isReflectionPositiveAcrossMirror_congr a ν
      (congrArg (NormalHyperplane.diagonal μ lam hne) (by rw [hcdef]; push_cast; ring)) _ _
      (hcond.2.2 ((R : ℤ) + 1))
  have hcond' := (h_diag a μ lam hne c hc).hyps
  set hst : LatticePoint (a : ℝ) := DiagonalMirror.normalStep a μ lam with hhst
  set wst : LatticePoint (a : ℝ) := DiagonalMirror.tangentStep a μ lam with hwst
  have hcond₁ : MirrorReconstructionHyps (a : ℝ) (NormalHyperplane.diagonal μ lam hne c)
      (hst : Point) (NormalHyperplane.diagonal μ lam hne (c + (a : ℝ)))
      (fun _ : Fin 1 => (wst : Point)) :=
    ⟨hcond'.isMidPlane, hcond'.midPlane_isLatticeMirror, by simp,
      fun _ => hcond'.step_mem (), fun _ => hcond'.euclidDot_step ()⟩
  obtain ⟨-, hT, hV, hM⟩ := h_rec a _ _ hS hS' hst 1 (fun _ => wst) ν hcond₁ (hcond.1 hst)
    (fun _ => hcond.1 wst) hrp hrp'
  have hsys : IsCommutingFamilyData (NormalHyperplane.stepOperator hS ν hst)
      (fun _ : Unit => NormalHyperplane.vectorUnitary hS ν wst) :=
    { isSymmetric := hT.2.2.1
      nonneg := hT.2.2.2.1
      le_one := hT.2.2.2.2
      unitary := fun _ => (hV 0).2.1
      commute_T_U := fun _ => hM.1 0
      commute_U_U := fun _ _ => hM.2.1 0 0 }
  set D : ℕ := 2 * R + 1 with hD
  set r₀ : LatticeSymmetry (a : ℝ) := shift (D • axisStep (a : ℝ) μ) with hr₀
  set θl : LatticeSymmetry (a : ℝ) := LinkFrame.linkReflection a μ with hθl
  set θd : LatticeSymmetry (a : ℝ) := NormalHyperplane.reflectSymmetry hS with hθd
  set F₀ : GaugeField (a : ℝ) → ℂ := r₀.actOn F.1 with hF₀def
  set G : GaugeField (a : ℝ) → ℂ := θl.actOn F.1 with hGdef
  set B : GaugeField (a : ℝ) → ℂ := θd.actOn G with hBdef
  have hsideF₀ : r₀.setImage QA ⊆ (NormalHyperplane.diagonal μ lam hne c).upperHalfSpace := by
    rintro _ ⟨x, hx, rfl⟩
    rw [DiagonalMirror.upperHalfSpace_diagonal]
    have h₁ := hxμ x hx
    have h₂ := abs_le.mp (hxl x hx)
    change c ≤ (x + ((D • axisStep (a : ℝ) μ : LatticePoint (a : ℝ)) : Point)) μ +
      (x + ((D • axisStep (a : ℝ) μ : LatticePoint (a : ℝ)) : Point)) lam
    simp only [Pi.add_apply, coe_nsmul_axisStep_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hne.symm, mul_zero, add_zero, hD]
    push_cast
    rw [hcR]
    nlinarith [h₂.1]
  have hsideB : θd.setImage (θl.setImage QA) ⊆
      (NormalHyperplane.diagonal μ lam hne c).upperHalfSpace := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [DiagonalMirror.upperHalfSpace_diagonal]
    have h₁ := hxμ x hx
    have h₂ := abs_le.mp (hxl x hx)
    have hθ : θl.toFun x = LinkFrame.linkReflectionMap a μ x :=
      congrFun (LinkFrame.linkReflection_toFun a μ) x
    change c ≤ (NormalHyperplane.diagonal μ lam hne c).reflect (θl.toFun x) μ +
      (NormalHyperplane.diagonal μ lam hne c).reflect (θl.toFun x) lam
    rw [reflect_diagonal_add hne, hθ]
    simp only [LinkFrame.linkReflectionMap, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, basisVector,
      Pi.single_eq_same, Pi.single_eq_of_ne hne.symm]
    rw [hcR] at *
    nlinarith [h₂.2]
  have hF₀ : F₀ ∈ localRegionObservables (a : ℝ)
      (NormalHyperplane.diagonal μ lam hne c).upperHalfSpace := by
    have h₁ : F₀ ∈ (fun F : GaugeField (a : ℝ) → ℂ => r₀.actOn F) ''
        localRegionObservables (a : ℝ) QA := ⟨F.1, hFloc, rfl⟩
    rw [hcarry] at h₁
    exact (hgrow _ _ hsideF₀).2.1 h₁
  have hB : B ∈ localRegionObservables (a : ℝ)
      (NormalHyperplane.diagonal μ lam hne c).upperHalfSpace := by
    have h₁ : G ∈ (fun F : GaugeField (a : ℝ) → ℂ => θl.actOn F) ''
        localRegionObservables (a : ℝ) QA := ⟨F.1, hFloc, rfl⟩
    rw [hcarry] at h₁
    have h₂ : B ∈ (fun F : GaugeField (a : ℝ) → ℂ => θd.actOn F) ''
        localRegionObservables (a : ℝ) (θl.setImage QA) := ⟨G, h₁, rfl⟩
    rw [hcarry] at h₂
    exact (hgrow _ _ hsideB).2.1 h₂
  have hGobs : IsBoundedObservable G := ((hkeeps θl).1 F.1 F.1 hFobs hFobs).1
  have hinv : θd.IsInverse θd := by
    obtain ⟨-, -, -, hinvol, -⟩ := hrefl (NormalHyperplane.diagonal μ lam hne c)
    have h₁ : ∀ x, (NormalHyperplane.diagonal μ lam hne c).reflect
        ((NormalHyperplane.diagonal μ lam hne c).reflect x) = x := fun x => congrFun hinvol x
    exact ⟨h₁, h₁⟩
  have hBB : θd.actOn B = G := ((hinvr θd).2 θd hinv G hGobs).1
  refine spectralMeasure_coneExterior_eq_zero h_scalar h_poly h_two h_disc _ hsys.toFamily _
    (NormalHyperplane.mirrorClass hS ν ⟨B, hB⟩) (NormalHyperplane.mirrorClass hS ν ⟨F₀, hF₀⟩) D ?_
  intro k l
  obtain ⟨hA', hB'⟩ := LinkFrame.TransferMatrixElements.singleShiftFamily_ops hlink
    ⟨lam, hne.symm⟩
  have hu : IsUnitaryMap
      (((LinkFrame.singleShiftFamily a μ ν ⟨lam, hne.symm⟩).B default :
        LinkFrame.LinkHilbertSpace a μ ν →L[ℂ] LinkFrame.LinkHilbertSpace a μ ν) :
          LinkFrame.LinkHilbertSpace a μ ν →ₗ[ℂ] LinkFrame.LinkHilbertSpace a μ ν) := by
    rw [hB' default]
    exact hlink.2.2.2.1 _
  have e₁ := hlink.2.2.2.2.2.2.2 F F ⟨lam, hne.symm⟩ (D + k + l) ((k : ℤ) - (l : ℤ))
  have e₂ := hM.2.2 ⟨B, hB⟩ ⟨F₀, hF₀⟩ k (fun _ => (l : ℤ))
  have hleft : familyMonomial (LinkFrame.singleShiftFamily a μ ν ⟨lam, hne.symm⟩) (D + k + l)
      (fun _ => (k : ℤ) - (l : ℤ)) =
      LinkFrame.transferOperator a μ ν ^ (D + k + l) *
        zpowOp (LinkFrame.transverseShift a μ ν ⟨lam, hne.symm⟩) ((k : ℤ) - (l : ℤ)) := by
    rw [familyMonomial, hA', unitaryMonomial_of_unique, coe_zpow_eq_zpowOp _ hu, hB' default]
  have hright : (hsys.toFamily.A ^ k * (hsys.toFamily.B default :
        NormalHyperplane.MirrorHilbertSpace hS ν →L[ℂ] NormalHyperplane.MirrorHilbertSpace hS ν) ^ l) =
      NormalHyperplane.stepOperator hS ν hst ^ k *
        (List.ofFn fun _ : Fin 1 =>
          zpowOp (NormalHyperplane.vectorUnitary hS ν wst) (l : ℤ)).prod := by
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      zpowOp_natCast]
    rfl
  rw [hleft, hright]
  change inner ℂ (LinkFrame.linkClass a μ ν F) _ = _
  rw [e₁]
  refine Eq.trans ?_ e₂.symm
  have hsum := hadd (k • hst + ∑ i : Fin 1, (l : ℤ) • wst) (D • axisStep (a : ℝ) μ) F.1 hFobs
  rw [nsmul_steps_eq a hne] at hsum
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  simp only []
  rw [hBB]
  congr 1
  exact (congrFun hsum U).symm
end Lattice
theorem linkConeInequality_holds
    (h_matrix : CoordinatePictureOperators)
    (h_rec : MirrorReconstruction)
    (h_diag : DiagonalPictureExpansion.Statement)
    (h_action : InfiniteLattice.SymmetryActionOnObservables)
    (h_rules : ObservableRules.AllRules)
    (h_calc : JointSpectrum.BorelCalculus.BorelCalculusStatement)
    (h_facts : JointSpectrum.CalculusApplications.CalculusApplicationsStatement)
    (h_scalar : ScalarSpectralMeasures.ScalarSpectralMeasuresStatement)
    (h_poly : FamilyPolynomials.PolynomialCalculusStatement)
    (h_two : DiscTwoConstants.DiscTwoConstantsStatement)
    (h_disc : ConeIdentity.ConeIdentityStatement) :
    LinkConeInequality := by
  intro a μ lam hne ν _ hcond
  have hstate : LinkFrame.IsAdmissibleState a μ ν := ⟨hcond.1, hcond.2.1⟩
  obtain ⟨-, hlink, -⟩ := h_matrix a μ ν hstate
  obtain ⟨hA, hB⟩ := LinkFrame.TransferMatrixElements.singleShiftFamily_ops hlink
    ⟨lam, hne.symm⟩
  have hmeas : MeasurableSet (coneExteriorOf (SingleTransverse (μ := μ) ⟨lam, hne.symm⟩)) := by
    rw [coneExteriorOf_eq h_disc]
    exact (isOpen_lt continuous_coneDefectOf continuous_const).measurableSet
  have h₀ : jointSpectralMeasure (LinkFrame.singleShiftFamily a μ ν ⟨lam, hne.symm⟩)
      (coneExteriorOf (SingleTransverse (μ := μ) ⟨lam, hne.symm⟩)) = 0 :=
    jointSpectralMeasure_eq_zero_of_denseRange h_calc _ (LinkFrame.linkClass a μ ν)
      hlink.2.2.2.2.2.2.1 _ hmeas fun F =>
        spectralMeasure_linkClass_coneExterior h_rec h_diag h_action h_rules h_scalar h_poly
          h_two h_disc a hne ν hcond hlink F
  have hab := opGE_of_coneExterior h_calc h_facts h_poly h_disc
    (LinkFrame.singleShiftFamily a μ ν ⟨lam, hne.symm⟩) h₀
  rw [hA, hB default] at hab
  refine ⟨hab, isClosed_coneInteriorOf, coneInteriorOf_eq_nonnegSet, ⟨?_, ?_⟩, h₀⟩
  · exact isClosed_coneInteriorOf.measurableSet
  · change jointSpectralMeasure (LinkFrame.singleShiftFamily a μ ν ⟨lam, hne.symm⟩) _ = 0
    rw [coneInteriorOf_eq_compl h_disc, compl_compl]
    exact h₀
end LinkConeProof
end LatticeConventions
end YangMills.Construction
end

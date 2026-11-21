import YangMills.Construction.PeriodicOperators.BoundsOfTheNumbersOfAJet
import YangMills.Construction.Towers.TraceNumberOfJetsWithHolomorphicComponentsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetNumberBounds
open JetQuad
variable {I : PeriodicData}
private theorem sqrtOf_div_self_le_one (t : ℝ) :
    RealPower.sqrtOf (t / t) ≤ 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.JetTraceHolomorphy.sqrtOf_div_self_le_one <;> assumption
private theorem trace_eq_sum_diag_entries {J : Type} [Fintype J] (A : (J → ℂ) →ₗ[ℂ] (J → ℂ)) :
    LinearMap.trace ℂ (J → ℂ) A = ∑ c, linearMapEntry A c c := by apply _root_.YangMills.SharedProofs.p9894 <;> assumption
private theorem norm_trace_le_finrank_mul (hN : HomNorm.Claim) (hI : IsPeriodic I)
    (A : QuotHom I I) :
    ENNReal.ofReal ‖LinearMap.trace ℂ (I.UnitQuot → ℂ) A‖ ≤
      (Module.finrank ℂ (I.UnitQuot → ℂ) : ℝ≥0∞) * quotHomNorm A := by
  have := hI.finite_quot
  have := Fintype.ofFinite I.UnitQuot
  have hfin : quotHomNorm A ≠ ∞ := ((hN I I hI hI).1 A).2.ne
  have hdiag : ∀ c, ‖linearMapEntry A c c‖ ≤ (quotHomNorm A).toReal := fun c => by
    have h := (hN I I hI hI).2.2.2.1 A c c
    exact h.trans (mul_le_of_le_one_right ENNReal.toReal_nonneg (sqrtOf_div_self_le_one _))
  have hsum : ‖LinearMap.trace ℂ (I.UnitQuot → ℂ) A‖ ≤
      (Fintype.card I.UnitQuot : ℝ) * (quotHomNorm A).toReal := by
    rw [trace_eq_sum_diag_entries]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun c _ => hdiag c).trans ?_
    simp
  rw [Module.finrank_fintype_fun_eq_card]
  calc ENNReal.ofReal ‖LinearMap.trace ℂ (I.UnitQuot → ℂ) A‖
      ≤ ENNReal.ofReal ((Fintype.card I.UnitQuot : ℝ) * (quotHomNorm A).toReal) :=
        ENNReal.ofReal_le_ofReal hsum
    _ = (Fintype.card I.UnitQuot : ℝ≥0∞) * quotHomNorm A := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_toReal hfin]
private theorem torusAverage_le_of_bound (f : (Fin 4 → ℝ) → ℂ) (B : ℝ≥0∞)
    (h : ∀ k ∈ Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), ENNReal.ofReal ‖f k‖ ≤ B) :
    ENNReal.ofReal ‖torusAverage f‖ ≤ B := by
  by_cases hB : B = ∞
  · simp [hB]
  have hb : ∀ k ∈ Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), ‖f k‖ ≤ B.toReal :=
    fun k hk => (ENNReal.ofReal_le_iff_le_toReal hB).1 (h k hk)
  have hvol : (volume : Measure (Fin 4 → ℝ)) (Icc (fun _ : Fin 4 => -Real.pi) fun _ => Real.pi) =
      ENNReal.ofReal ((2 * Real.pi) ^ 4) := by
    rw [Real.volume_Icc_pi]
    have : ENNReal.ofReal (Real.pi - -Real.pi) = ENNReal.ofReal (2 * Real.pi) := by
      congr 1; ring
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [this, ENNReal.ofReal_pow (by positivity)]
  have hreal : (volume : Measure (Fin 4 → ℝ)).real
      (Icc (fun _ : Fin 4 => -Real.pi) fun _ => Real.pi) = (2 * Real.pi) ^ 4 := by
    rw [Measure.real, hvol, ENNReal.toReal_ofReal (by positivity)]
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (by rw [hvol]; exact ENNReal.ofReal_lt_top) hb
  rw [hreal] at hint
  have hpos : (0 : ℝ) < (2 * Real.pi) ^ 4 := by positivity
  rw [← ENNReal.ofReal_toReal hB]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold torusAverage
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
  calc ((2 * Real.pi) ^ 4)⁻¹ * ‖∫ k in Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), f k‖
      ≤ ((2 * Real.pi) ^ 4)⁻¹ * (B.toReal * (2 * Real.pi) ^ 4) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hpos.le)
    _ = B.toReal := by field_simp
private theorem toComplexVec_mem_imStrip_two_mul {δ : ℝ} (hδ : 0 < δ) (x : Fin 4 → ℝ) :
    toComplexVec x ∈ imStrip (2 * δ) := fun μ => by
  have : 0 ≤ 2 * δ := by positivity
  simpa [toComplexVec] using this
private theorem toComplexVec_sub_mem_imStrip {δ : ℝ} {q : Fin 4 → ℂ} (hδ : 0 < δ)
    (hq : q ∈ imStrip δ) (x : Fin 4 → ℝ) : toComplexVec x - q ∈ imStrip (2 * δ) := fun μ => by
  have h := hq μ
  have e : ((toComplexVec x - q) μ).im = -(q μ).im := by simp [toComplexVec]
  rw [e, abs_neg]
  linarith
private theorem norm_f10_le {δ : ℝ} {q : Fin 4 → ℂ} (F : JetQuad I I) {k : Fin 4 → ℂ}
    (h : k ∈ stripAddShift δ q) : quotHomNorm (F.f10 k) ≤ jetNorm δ q F :=
  (le_iSup₂ (f := fun k (_ : k ∈ stripAddShift δ q) => quotHomNorm (F.f10 k)) k h).trans
    (le_add_self.trans (le_self_add.trans le_self_add))
private theorem norm_f01_le {δ : ℝ} {q : Fin 4 → ℂ} (F : JetQuad I I) {k : Fin 4 → ℂ}
    (h : k ∈ stripSubShift δ q) : quotHomNorm (F.f01 k) ≤ jetNorm δ q F :=
  (le_iSup₂ (f := fun k (_ : k ∈ stripSubShift δ q) => quotHomNorm (F.f01 k)) k h).trans
    (le_add_self.trans le_self_add)
private theorem norm_f11_le {δ : ℝ} {q : Fin 4 → ℂ} (F : JetQuad I I) (x : Fin 4 → ℝ) :
    quotHomNorm (F.f11 (toComplexVec x)) ≤ jetNorm δ q F :=
  (le_iSup₂ (f := fun k (_ : k ∈ realDualPoints) => quotHomNorm (F.f11 k)) (toComplexVec x)
    (fun μ => by simp [toComplexVec])).trans le_add_self
private theorem norm_schur_integrand_le (hN : HomNorm.Claim)
    (hI : IsPeriodic I) {δ : ℝ} {q : Fin 4 → ℂ} (hδ : 0 < δ) (hq : q ∈ imStrip δ)
    (F : JetQuad I I) (x : Fin 4 → ℝ) :
    quotHomNorm
        ((quotHomInverse (F.f00 (toComplexVec x))).comp (F.f11 (toComplexVec x)) -
          (quotHomInverse (F.f00 (toComplexVec x))).comp
            ((F.f10 (toComplexVec x - q)).comp
              ((quotHomInverse (F.f00 (toComplexVec x - q))).comp
                (F.f01 (toComplexVec x))))) ≤
      (⨆ k ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse (F.f00 k))) * jetNorm δ q F +
        (⨆ k ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse (F.f00 k))) ^ 2 *
          jetNorm δ q F ^ 2 := by
  set s : ℝ≥0∞ := ⨆ k ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse (F.f00 k)) with hs
  set N : ℝ≥0∞ := jetNorm δ q F with hNdef
  have hx := toComplexVec_mem_imStrip_two_mul hδ x
  have hxq := toComplexVec_sub_mem_imStrip hδ hq x
  have hadd : toComplexVec x - q ∈ stripAddShift δ q :=
    ⟨hxq, by simpa using hx⟩
  have hsubs : toComplexVec x ∈ stripSubShift δ q := ⟨hx, hxq⟩
  have hinv : ∀ k ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse (F.f00 k)) ≤ s := fun k h =>
    le_iSup₂ (f := fun k (_ : k ∈ imStrip (2 * δ)) => quotHomNorm (quotHomInverse (F.f00 k))) k h
  have hcomp : ∀ A B : QuotHom I I, quotHomNorm (A.comp B) ≤ quotHomNorm A * quotHomNorm B :=
    fun A B => ((hN I I hI hI).2.2.2.2.2.2.1 I hI).2 A B
  have hsums := (hN I I hI hI).2.2.2.2.2.1
  have hsub : ∀ A B : QuotHom I I, quotHomNorm (A - B) ≤ quotHomNorm A + quotHomNorm B := by
    intro A B
    rw [((hN I I hI hI).2.2.2.2.2.2.2.2 A B 0).1]
    refine (hsums.2.2.2.1 _ _).trans ?_
    rw [hsums.2.2.2.2]
    simp
  refine (hsub _ _).trans (add_le_add ?_ ?_)
  · exact (hcomp _ _).trans (mul_le_mul' (hinv _ hx) (norm_f11_le F x))
  · calc _ ≤ quotHomNorm (quotHomInverse (F.f00 (toComplexVec x))) *
            (quotHomNorm (F.f10 (toComplexVec x - q)) *
              (quotHomNorm (quotHomInverse (F.f00 (toComplexVec x - q))) *
                quotHomNorm (F.f01 (toComplexVec x)))) :=
          (hcomp _ _).trans (mul_le_mul_right
            ((hcomp _ _).trans (mul_le_mul_right (hcomp _ _) _)) _)
      _ ≤ s * (N * (s * N)) :=
          mul_le_mul' (hinv _ hx) (mul_le_mul' (norm_f10_le F hadd)
            (mul_le_mul' (hinv _ hxq) (norm_f01_le F hsubs)))
      _ = s ^ 2 * N ^ 2 := by ring
theorem claim_holds (hJ : JetCalculus.Claim) (hN : HomNorm.Claim) :
    Claim := by
  intro δ q hδ hq I hI F
  refine ⟨fun _ => ?_, fun hF => ?_⟩
  · refine torusAverage_le_of_bound _ _ fun x _ => (norm_trace_le_finrank_mul hN hI _).trans ?_
    exact mul_le_mul_right (norm_f11_le F x) _
  · rw [((hJ δ q hδ hq).2.2.2.2.2.2.1 I hI).2 F hF]
    refine torusAverage_le_of_bound _ _ fun x _ => ?_
    refine (norm_trace_le_finrank_mul hN hI _).trans ?_
    exact mul_le_mul_right (norm_schur_integrand_le hN hI hδ hq F x) _
end YangMills.Construction.PeriodicOperators.JetNumberBounds
end

import YangMills.Construction.PeriodicOperators.NormOfTheSymbolProof
import YangMills.Construction.PeriodicOperators.KernelOfTheSymbolOfAPeriodicOperator
import YangMills.Construction.PeriodicOperators.SeriesOfTheSymbol
import YangMills.Construction.PeriodicOperators.SymbolAtAPoint
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SymbolKernel
open InfiniteLattice (AmbientSpace)
theorem integral_cexp_I_mul_int (k : ℤ) :
    ∫ t in Icc (-Real.pi) Real.pi, Complex.exp (Complex.I * ((t : ℂ) * (k : ℂ))) =
      if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  split_ifs with hk
  · subst hk
    simp
    ring
  · have hne : Complex.I * (k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)
    have hfun : (fun t : ℝ => Complex.exp (Complex.I * ((t : ℂ) * (k : ℂ)))) =
        fun t : ℝ => Complex.exp (Complex.I * (k : ℂ) * t) := by
      funext t
      congr 1
      ring
    rw [hfun, integral_exp_mul_complex hne]
    have hper : Complex.exp (Complex.I * (k : ℂ) * ((Real.pi : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (k : ℂ) * ((-Real.pi : ℝ) : ℂ)) := by
      refine Complex.exp_eq_exp_iff_exists_int.2 ⟨k, ?_⟩
      push_cast
      ring
    rw [hper]
    simp
theorem integral_cexp_bilinDot_cube (v : Fin 4 → ℤ) :
    ∫ ξ in Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi),
        Complex.exp (Complex.I * bilinDot (toComplexVec ξ) (toComplexVec (castVec v))) =
      if v = 0 then (2 * Real.pi : ℂ) ^ 4 else 0 := by
  have hprod : ∀ ξ : Fin 4 → ℝ,
      Complex.exp (Complex.I * bilinDot (toComplexVec ξ) (toComplexVec (castVec v))) =
        ∏ μ, Complex.exp (Complex.I * ((ξ μ : ℂ) * (v μ : ℂ))) := by
    intro ξ
    rw [← Complex.exp_sum, ← Finset.mul_sum]
    simp [bilinDot, toComplexVec, castVec]
  have hbox : Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi) =
      Set.pi univ fun _ => Icc (-Real.pi) Real.pi := (Set.pi_univ_Icc _ _).symm
  simp_rw [hprod]
  rw [hbox, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (𝕜 := ℂ)
      (fun μ (t : ℝ) => Complex.exp (Complex.I * ((t : ℂ) * (v μ : ℂ))))]
  simp_rw [integral_cexp_I_mul_int]
  split_ifs with hv
  · subst hv
    simp
  · obtain ⟨μ, hμ⟩ := Function.ne_iff.1 hv
    exact Finset.prod_eq_zero (Finset.mem_univ μ) (if_neg hμ)
theorem norm_cexp_I_bilinDot (ξ y : Fin 4 → ℝ) :
    ‖Complex.exp (Complex.I * bilinDot (toComplexVec ξ) (toComplexVec y))‖ = 1 := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolNorm.norm_exp_I_bilinDot <;> assumption
theorem symbolSummand_mul_cexp {P P' : PeriodicData} (hP : IsPeriodic P)
    (A : P'.Carrier → P.Carrier → ℂ) (ξ : Fin 4 → ℝ) (b : P'.Carrier) (a : P.Carrier)
    (v : Fin 4 → ℤ) :
    symbolSummand P P' A (toComplexVec ξ) b a v *
        Complex.exp (-Complex.I *
          bilinDot (toComplexVec ξ) (toComplexVec (P.pos a - P'.pos b))) =
      A b (P.translate v a) *
        Complex.exp (Complex.I * bilinDot (toComplexVec ξ) (toComplexVec (castVec v))) := by
  have hsplit : bilinDot (toComplexVec ξ) (toComplexVec (P.pos (P.translate v a) - P'.pos b)) =
      bilinDot (toComplexVec ξ) (toComplexVec (P.pos a - P'.pos b)) +
        bilinDot (toComplexVec ξ) (toComplexVec (castVec v)) := by
    rw [hP.pos_translate]
    simp only [bilinDot, toComplexVec, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [Pi.add_apply, Pi.sub_apply]
    push_cast
    ring
  rw [symbolSummand, hsplit, mul_assoc, ← Complex.exp_add]
  congr 2
  ring
theorem kernelOfSymbol_holds (hSeries : SymbolSeriesClaim) (hPoint : SymbolPointwise.Properties) :
    KernelOfSymbol := by
  intro P P' hP hP' A hA
  obtain ⟨C, δ, hC, hδ, hbound⟩ := hA.2
  have hsumm : ∀ ξ : Fin 4 → ℝ, SymbolSummableAt P P' A (toComplexVec ξ) := fun ξ =>
    (hSeries P P' hP hP' A δ ⟨hδ, C, hC, hbound⟩).summableOn_strip _ (by
      simp [strictImStrip, imVec, toComplexVec, TorusMetric.euclidNormVec, hδ])
  funext b a
  let G : (Fin 4 → ℤ) → (Fin 4 → ℝ) → ℂ := fun v ξ =>
    A b (P.translate v a) *
      Complex.exp (Complex.I * bilinDot (toComplexVec ξ) (toComplexVec (castVec v)))
  have hintegrand : ∀ ξ : Fin 4 → ℝ,
      matFunIntegrand P P' (symbolHom P P' A) b a ξ = ∑' v, G v ξ := by
    intro ξ
    have hξ := (hPoint P P' hP hP' A _ hA (hsumm ξ)).2.2.1 b a
    simp only [matFunIntegrand]
    rw [hξ]
    simp only [fourierSymbol]
    rw [← tsum_mul_right]
    exact tsum_congr fun v => symbolSummand_mul_cexp hP A ξ b a v
  have hnormsum : Summable fun v : Fin 4 → ℤ => ‖A b (P.translate v a)‖ := by
    refine (hsumm 0 b a).congr fun v => ?_
    rw [symbolSummand, norm_mul, norm_cexp_I_bilinDot, mul_one]
  have hcont : ∀ v, Continuous (G v) := fun v => by
    simp only [G, bilinDot, toComplexVec]
    fun_prop
  have hGnorm : ∀ v ξ, ‖G v ξ‖ = ‖A b (P.translate v a)‖ := fun v ξ => by
    simp only [G]
    rw [norm_mul, norm_cexp_I_bilinDot, mul_one]
  let box : Set (Fin 4 → ℝ) := Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi)
  have hGint : ∀ v, Integrable (G v) (volume.restrict box) := fun v =>
    (hcont v).integrableOn_Icc
  have hGsum : Summable fun v => ∫ ξ in box, ‖G v ξ‖ := by
    simp only [hGnorm, integral_const, smul_eq_mul]
    exact hnormsum.mul_left _
  have hhas := hasSum_integral_of_summable_integral_norm hGint hGsum
  have hvanish : ∀ v, v ≠ 0 → ∫ ξ in box, G v ξ = 0 := fun v hv => by
    simp only [G]
    rw [integral_const_mul, integral_cexp_bilinDot_cube, if_neg hv, mul_zero]
  have hsingle := hasSum_single (f := fun v => ∫ ξ in box, G v ξ) 0 hvanish
  have heq := hhas.unique hsingle
  have hG0 : ∫ ξ in box, G 0 ξ = A b a * (2 * Real.pi : ℂ) ^ 4 := by
    simp only [G]
    rw [integral_const_mul, integral_cexp_bilinDot_cube, if_pos rfl, hP.translate_zero]
  simp only [matFunKernel, torusAverage]
  have hbox : ∫ ξ in box, matFunIntegrand P P' (symbolHom P P' A) b a ξ =
      A b a * (2 * Real.pi : ℂ) ^ 4 := by
    rw [← hG0, ← heq]
    exact integral_congr_ae (Filter.Eventually.of_forall hintegrand)
  change (((2 * Real.pi) ^ 4)⁻¹ : ℝ) * ∫ ξ in box, _ = A b a
  rw [hbox]
  push_cast
  field_simp
end YangMills.Construction.PeriodicOperators.SymbolKernel
end

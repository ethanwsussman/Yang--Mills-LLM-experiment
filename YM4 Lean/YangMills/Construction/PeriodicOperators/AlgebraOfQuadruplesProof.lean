import YangMills.Construction.PeriodicOperators.AdditivityAndIntegralOfTheLogarithmicNumberProof
import YangMills.Construction.PeriodicOperators.AlgebraOfQuadruples
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.QuadAlgebra
open JetQuad (IsJet)
open QuotMatrixNorms
variable {I I' I'' : PeriodicData}
private theorem mulBilinearUnital_holds (p : Fin 4 → ℂ) :
    MulBilinearUnital p I I' I'' := by
  refine ⟨fun T T' S => ?_, fun T S S' => ?_, fun a T S => ?_, fun a T S => ?_, fun T => ⟨?_, ?_⟩⟩
  · refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
      simp only [JetQuad.mul, JetQuad.add, Pi.add_apply, LinearMap.add_comp] <;> abel
  · refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
      simp only [JetQuad.mul, JetQuad.add, Pi.add_apply, LinearMap.comp_add] <;> abel
  · refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
      simp only [JetQuad.mul, JetQuad.smul, Pi.smul_apply, LinearMap.smul_comp, smul_add]
  · refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
      simp only [JetQuad.mul, JetQuad.smul, Pi.smul_apply, LinearMap.comp_smul, smul_add]
  · refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
      simp [JetQuad.mul, JetQuad.one]
  · refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
      simp [JetQuad.mul, JetQuad.one]
private theorem biSup_norm_add_le (hadd : ∀ M N : QuotHom I I',
    quotHomNorm (M + N) ≤ quotHomNorm M + quotHomNorm N)
    (D : Set (Fin 4 → ℂ)) (A B : (Fin 4 → ℂ) → QuotHom I I') :
    (⨆ κ ∈ D, quotHomNorm ((A + B) κ)) ≤
      (⨆ κ ∈ D, quotHomNorm (A κ)) + ⨆ κ ∈ D, quotHomNorm (B κ) :=
  iSup₂_le fun κ h => (hadd (A κ) (B κ)).trans
    (add_le_add (le_iSup₂ (f := fun κ (_ : κ ∈ D) => quotHomNorm (A κ)) κ h)
      (le_iSup₂ (f := fun κ (_ : κ ∈ D) => quotHomNorm (B κ)) κ h))
private theorem biSup_norm_smul_le (a : ℂ) (hsmul : ∀ M : QuotHom I I',
    quotHomNorm (a • M) ≤ ENNReal.ofReal ‖a‖ * quotHomNorm M)
    (D : Set (Fin 4 → ℂ)) (A : (Fin 4 → ℂ) → QuotHom I I') :
    (⨆ κ ∈ D, quotHomNorm ((a • A) κ)) ≤
      ENNReal.ofReal ‖a‖ * ⨆ κ ∈ D, quotHomNorm (A κ) :=
  iSup₂_le fun κ h => (hsmul (A κ)).trans <| by
    gcongr
    exact le_iSup₂ (f := fun κ (_ : κ ∈ D) => quotHomNorm (A κ)) κ h
private theorem biSup_norm_zero (h0 : quotHomNorm (0 : QuotHom I I') = 0)
    (D : Set (Fin 4 → ℂ)) :
    (⨆ κ ∈ D, quotHomNorm ((0 : (Fin 4 → ℂ) → QuotHom I I') κ)) = 0 := by
  simp [h0]
private theorem trace_eq_sum_diag [Fintype I.UnitQuot] (M : QuotHom I I) :
    LinearMap.trace ℂ (I.UnitQuot → ℂ) M = ∑ c, linearMapEntry M c c := by apply _root_.YangMills.SharedProofs.p55196 <;> assumption
private theorem toComplexVec_continuous : Continuous toComplexVec := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.continuous_toComplexVec <;> assumption
private theorem trace_f11_integrableOn (hI : IsPeriodic I) {δ : ℝ} {p : Fin 4 → ℂ}
    {T : JetQuad I I} (hT : IsJet δ p T) :
    IntegrableOn (fun κ => LinearMap.trace ℂ (I.UnitQuot → ℂ) (T.f11 (toComplexVec κ)))
      (Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi)) := by
  have := hI.finite_quot
  have := Fintype.ofFinite I.UnitQuot
  obtain ⟨O, -, hRO, hO⟩ := hT.holo_f11
  have hmem : ∀ y, toComplexVec y ∈ O := fun y => hRO fun μ => Complex.ofReal_im (y μ)
  have hcont : Continuous fun y => LinearMap.trace ℂ (I.UnitQuot → ℂ) (T.f11 (toComplexVec y)) := by
    simp only [trace_eq_sum_diag]
    refine continuous_finsetSum _ fun c _ => ?_
    have h1 : ContinuousOn (fun κ => linearMapEntry (T.f11 κ) c c) O :=
      (continuous_apply (0 : Fin 1)).comp_continuousOn (hO c c).2.1
    exact h1.comp_continuous toComplexVec_continuous hmem
  exact hcont.continuousOn.integrableOn_compact isCompact_Icc
abbrev _root_.YangMills.SharedProofs.p41810 := @trace_f11_integrableOn
private theorem jetNormTrace_holds {δ : ℝ} {p : Fin 4 → ℂ} (hI : IsPeriodic I)
    (hN : NormAxioms I I') (hN' : NormAxioms I I) (hU : UnitTraceBound I) :
    JetNormTrace δ p I I' := by
  obtain ⟨-, hadd, hsmul, -, -⟩ := hN
  obtain ⟨-, -, -, h0, -⟩ := hN'
  refine ⟨fun T S _ _ => ?_, fun a T _ => ?_, ?_, fun T S hT hS => ?_, fun a T _ => ?_⟩
  · unfold JetQuad.jetNorm
    calc _ ≤ ((⨆ κ ∈ imStrip (2 * δ), quotHomNorm (T.f00 κ)) +
              ⨆ κ ∈ imStrip (2 * δ), quotHomNorm (S.f00 κ)) +
            ((⨆ κ ∈ stripAddShift δ p, quotHomNorm (T.f10 κ)) +
              ⨆ κ ∈ stripAddShift δ p, quotHomNorm (S.f10 κ)) +
            ((⨆ κ ∈ stripSubShift δ p, quotHomNorm (T.f01 κ)) +
              ⨆ κ ∈ stripSubShift δ p, quotHomNorm (S.f01 κ)) +
            ((⨆ κ ∈ realDualPoints, quotHomNorm (T.f11 κ)) +
              ⨆ κ ∈ realDualPoints, quotHomNorm (S.f11 κ)) :=
          add_le_add (add_le_add (add_le_add (biSup_norm_add_le hadd _ _ _)
            (biSup_norm_add_le hadd _ _ _)) (biSup_norm_add_le hadd _ _ _))
            (biSup_norm_add_le hadd _ _ _)
      _ = _ := by abel
  · unfold JetQuad.jetNorm
    rw [mul_add, mul_add, mul_add]
    exact add_le_add (add_le_add (add_le_add (biSup_norm_smul_le a (hsmul a) _ _)
      (biSup_norm_smul_le a (hsmul a) _ _)) (biSup_norm_smul_le a (hsmul a) _ _))
      (biSup_norm_smul_le a (hsmul a) _ _)
  · unfold JetQuad.jetNorm
    have h1 : (⨆ κ ∈ imStrip (2 * δ), quotHomNorm ((JetQuad.one I).f00 κ)) ≤ 1 :=
      iSup₂_le fun _ _ => hU.1
    have h2 := biSup_norm_zero h0 (stripAddShift δ p)
    have h3 := biSup_norm_zero h0 (stripSubShift δ p)
    have h4 := biSup_norm_zero h0 realDualPoints
    show (⨆ κ ∈ imStrip (2 * δ), quotHomNorm ((JetQuad.one I).f00 κ)) +
        (⨆ κ ∈ stripAddShift δ p, quotHomNorm ((0 : (Fin 4 → ℂ) → QuotHom I I) κ)) +
        (⨆ κ ∈ stripSubShift δ p, quotHomNorm ((0 : (Fin 4 → ℂ) → QuotHom I I) κ)) +
        (⨆ κ ∈ realDualPoints, quotHomNorm ((0 : (Fin 4 → ℂ) → QuotHom I I) κ)) ≤ 1
    rw [h2, h3, h4]
    simpa using h1
  · unfold JetQuad.traceNumber torusAverage
    have hsum : (fun κ => LinearMap.trace ℂ (I.UnitQuot → ℂ) ((JetQuad.add T S).f11 (toComplexVec κ)))
        = fun κ => LinearMap.trace ℂ (I.UnitQuot → ℂ) (T.f11 (toComplexVec κ)) +
          LinearMap.trace ℂ (I.UnitQuot → ℂ) (S.f11 (toComplexVec κ)) := by
      funext κ
      exact map_add _ _ _
    rw [hsum, integral_add (trace_f11_integrableOn hI hT) (trace_f11_integrableOn hI hS), mul_add]
  · unfold JetQuad.traceNumber torusAverage
    have hsum : (fun κ => LinearMap.trace ℂ (I.UnitQuot → ℂ) ((JetQuad.smul a T).f11 (toComplexVec κ)))
        = fun κ => a * LinearMap.trace ℂ (I.UnitQuot → ℂ) (T.f11 (toComplexVec κ)) := by
      funext κ
      exact (map_smul _ _ _).trans (smul_eq_mul _ _)
    rw [hsum, integral_const_mul]
    ring
theorem claim_of_quotMatrixNorms (h : QuotMatrixNorms.Claim) : Claim := by
  refine ⟨fun p I I' I'' => mulBilinearUnital_holds p, fun δ p _ _ I I' hI hI' => ?_⟩
  exact jetNormTrace_holds hI (h I I' I hI hI' hI).1 (h I I I hI hI hI).1 (h I I I hI hI hI).2.2
end YangMills.Construction.PeriodicOperators.QuadAlgebra
end

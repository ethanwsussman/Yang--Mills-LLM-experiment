import YangMills.Construction.PeriodicOperators.ActionAndProductsOnTheTorusProof
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNormProof
import YangMills.Construction.PeriodicOperators.TransposeOfAPeriodicOperator
import YangMills.Construction.PeriodicOperators.TransposesAndCombinationsOnTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TorusPeriodization
variable {I I' : PeriodicData}
theorem exists_decayRate {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) :
    ∃ δ, IsDecayRate I I' T δ := by apply _root_.YangMills.Construction.PeriodicOperators.TorusAction.exists_decayRate <;> assumption
theorem weightOf_translate (hP : IsPeriodic I) (n : Fin 4 → ℤ) (x : I.Carrier) :
    I.weightOf (I.translate n x) = I.weightOf x := by apply _root_.YangMills.Construction.PeriodicOperators.Quotients.weightOf_translate <;> assumption
theorem quotWeight_mkQuot (hQ : QuotOrbits.Claim)
    (hP : IsPeriodic I) (s : ℕ) (x : I.Carrier) :
    I.quotWeight s (I.mkQuot s x) = I.weightOf x := by
  have hw : ∀ y, I.mkQuot s y = I.mkQuot s x → I.weightOf y = I.weightOf x := by
    intro y hy
    obtain ⟨n, rfl⟩ := ((hQ I hP).1 s x y).1 hy.symm
    exact weightOf_translate hP _ _
  exact (Classical.epsilon_spec
    (p := fun w => ∀ y, I.mkQuot s y = I.mkQuot s x → I.weightOf y = w) ⟨_, hw⟩ x rfl).symm
theorem apply_translate_left {T : I'.Carrier → I.Carrier → ℂ} (hP' : IsPeriodic I')
    (hT : IsShiftInvariant I I' T) (m : Fin 4 → ℤ) (y : I'.Carrier) (x : I.Carrier) :
    T (I'.translate m y) x = T y (I.translate (-m) x) := by
  rw [← hT (-m) (I'.translate m y) x, ← hP'.translate_add, add_neg_cancel, hP'.translate_zero]
theorem periodization_kernelTranspose {T : I'.Carrier → I.Carrier → ℂ} (hP' : IsPeriodic I')
    (hT : IsShiftInvariant I I' T) (s : ℕ) (x : I.Carrier) (y : I'.Carrier) :
    periodization I' I (kernelTranspose I I' T) s x y =
      ((I'.weightOf y / I.weightOf x : ℝ) : ℂ) * periodization I I' T s y x := by
  have hterm : ∀ n : Fin 4 → ℤ, kernelTranspose I I' T x (I'.translate (s • n) y) =
      ((I'.weightOf y / I.weightOf x : ℝ) : ℂ) * T y (I.translate (s • (-n)) x) := by
    intro n
    simp only [kernelTranspose, wTranspose]
    rw [weightOf_translate hP', apply_translate_left hP' hT, smul_neg]
  simp only [periodization, hterm]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.neg (Fin 4 → ℤ)).tsum_eq fun n => T y (I.translate (s • n) x)
theorem periodicMatrix_im_eq_zero {T : I'.Carrier → I.Carrier → ℂ}
    (hF : Periodized.Properties I I' T) {s : ℕ} (hs : 0 < s)
    (hr : ∀ y x, (T y x).im = 0) (b : I'.QuotMod s) (a : I.QuotMod s) :
    (periodicMatrix I I' T s b a).im = 0 := by
  obtain ⟨y, rfl⟩ := Quot.exists_rep b
  obtain ⟨x, rfl⟩ := Quot.exists_rep a
  change (periodicMatrix I I' T s (I'.mkQuot s y) (I.mkQuot s x)).im = 0
  rw [hF.matrix_entries s hs y x]
  have hsum : Summable fun n : Fin 4 → ℤ => T y (I.translate (s • n) x) :=
    (hF.summable s hs y x).of_norm
  simp only [periodization]
  rw [Complex.im_tsum hsum]
  simp [hr]
theorem kernelLinComb_isPeriodicKernel {T T' : I'.Carrier → I.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hT' : IsPeriodicKernel I I' T') (c c' : ℂ) :
    IsPeriodicKernel I I' (kernelLinComb c c' T T') := by
  obtain ⟨hv, C, δ, hC, hδ, hb⟩ := hT
  obtain ⟨hv', C', δ', hC', hδ', hb'⟩ := hT'
  refine ⟨fun n y x => ?_, ‖c‖ * C + ‖c'‖ * C' + 1, min δ δ', by positivity, lt_min hδ hδ',
    fun y x => ?_⟩
  · simp only [kernelLinComb, hv n y x, hv' n y x]
  · have hd : 0 ≤ YangMills.Construction.TorusMetric.euclidNormVec (I'.pos y - I.pos x) :=
      Real.sqrt_nonneg _
    have e1 : Real.exp (-δ * YangMills.Construction.TorusMetric.euclidNormVec (I'.pos y - I.pos x)) ≤
        Real.exp (-min δ δ' * YangMills.Construction.TorusMetric.euclidNormVec (I'.pos y - I.pos x)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) hd)
    have e2 : Real.exp (-δ' * YangMills.Construction.TorusMetric.euclidNormVec (I'.pos y - I.pos x)) ≤
        Real.exp (-min δ δ' * YangMills.Construction.TorusMetric.euclidNormVec (I'.pos y - I.pos x)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) hd)
    have hE : 0 < Real.exp (-min δ δ' *
        YangMills.Construction.TorusMetric.euclidNormVec (I'.pos y - I.pos x)) :=
      Real.exp_pos _
    have b1 : ‖T y x‖ ≤
        C * Real.exp (-min δ δ' * YangMills.Construction.TorusMetric.euclidNormVec (I'.pos y - I.pos x)) :=
      (hb y x).trans (mul_le_mul_of_nonneg_left e1 hC.le)
    have b2 : ‖T' y x‖ ≤
        C' * Real.exp (-min δ δ' * YangMills.Construction.TorusMetric.euclidNormVec (I'.pos y - I.pos x)) :=
      (hb' y x).trans (mul_le_mul_of_nonneg_left e2 hC'.le)
    calc ‖kernelLinComb c c' T T' y x‖ ≤ ‖c‖ * ‖T y x‖ + ‖c'‖ * ‖T' y x‖ := by
          simp only [kernelLinComb]
          exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
      _ ≤ ‖c‖ * (C * Real.exp (-min δ δ' *
              YangMills.Construction.TorusMetric.euclidNormVec (I'.pos y - I.pos x))) +
            ‖c'‖ * (C' * Real.exp (-min δ δ' *
              YangMills.Construction.TorusMetric.euclidNormVec (I'.pos y - I.pos x))) :=
          add_le_add (mul_le_mul_of_nonneg_left b1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_left b2 (norm_nonneg _))
      _ ≤ (‖c‖ * C + ‖c'‖ * C' + 1) *
            Real.exp (-min δ δ' *
              YangMills.Construction.TorusMetric.euclidNormVec (I'.pos y - I.pos x)) := by
          nlinarith
theorem periodization_kernelLinComb {T T' : I'.Carrier → I.Carrier → ℂ} {s : ℕ}
    {y : I'.Carrier} {x : I.Carrier}
    (h : PeriodizationSummableAt I I' T s y x) (h' : PeriodizationSummableAt I I' T' s y x)
    (c c' : ℂ) :
    periodization I I' (kernelLinComb c c' T T') s y x =
      c * periodization I I' T s y x + c' * periodization I I' T' s y x := by
  have hsum : Summable fun n : Fin 4 → ℤ => T y (I.translate (s • n) x) := Summable.of_norm h
  have hsum' : Summable fun n : Fin 4 → ℤ => T' y (I.translate (s • n) x) := Summable.of_norm h'
  simp only [periodization, kernelLinComb]
  rw [(hsum.mul_left c).tsum_add (hsum'.mul_left c'), tsum_mul_left, tsum_mul_left]
theorem translate_smul_injective (hP : IsPeriodic I) {s : ℕ} (hs : 0 < s) (x : I.Carrier)
    {m n : Fin 4 → ℤ} (e : I.translate (s • m) x = I.translate (s • n) x) : m = n := by
  have hz : I.translate (s • m + -(s • n)) x = x := by
    rw [hP.translate_add, e, ← hP.translate_add, add_neg_cancel, hP.translate_zero]
  have hsub : s • m + -(s • n) = 0 := hP.free _ x hz
  have hmn : s • m = s • n := by
    rw [← sub_eq_zero, sub_eq_add_neg]
    exact hsub
  funext μ
  have hμ := congrFun hmn μ
  simp only [Pi.smul_apply, nsmul_eq_mul] at hμ
  exact mul_left_cancel₀ (by exact_mod_cast hs.ne') hμ
open Classical in
theorem periodization_idKernel (hQ : QuotOrbits.Claim)
    (hP : IsPeriodic I) {s : ℕ} (hs : 0 < s) (y x : I.Carrier) :
    periodization I I (idKernel I) s y x =
      if I.mkQuot s y = I.mkQuot s x then 1 else 0 := by
  simp only [periodization, idKernel]
  split_ifs with e
  · obtain ⟨n, hn⟩ := ((hQ I hP).1 s x y).1 e.symm
    rw [tsum_eq_single n]
    · exact if_pos hn
    · intro m hm
      refine if_neg fun e₂ => hm ?_
      exact translate_smul_injective hP hs x (e₂.symm.trans hn)
  · have hno : ∀ n : Fin 4 → ℤ, ¬ y = I.translate (s • n) x :=
      fun n hn => e (((hQ I hP).1 s x y).2 ⟨n, hn⟩).symm
    exact (tsum_congr fun n => if_neg (hno n)).trans tsum_zero
theorem claim_holds (hPer : Periodized.Claim)
    (hTr : Transpose.Claim)
    (hQ : QuotOrbits.Claim) : TorusPeriodization.Claim := by
  intro I I' hP hP' s hs1
  have hs : 0 < s := hs1
  refine ⟨fun T hT => ?_, periodization_idKernel hQ hP hs⟩
  obtain ⟨δ, hδ⟩ := exists_decayRate hT
  have hF := hPer I I' hP hP' T δ hT hδ
  have hG := hTr I I' hP hP' T δ hT hδ
  have hF' := hPer I' I hP' hP (kernelTranspose I I' T) δ hG.periodic hG.decay
  refine ⟨?_, periodicMatrix_im_eq_zero hF hs, fun T' hT' c c' =>
    ⟨kernelLinComb_isPeriodicKernel hT hT' c c', fun y x => ?_⟩⟩
  · funext a b
    obtain ⟨x, rfl⟩ := Quot.exists_rep a
    obtain ⟨y, rfl⟩ := Quot.exists_rep b
    change periodicMatrix I' I (kernelTranspose I I' T) s (I.mkQuot s x) (I'.mkQuot s y) =
      ((I'.quotWeight s (I'.mkQuot s y) / I.quotWeight s (I.mkQuot s x) : ℝ) : ℂ) *
        periodicMatrix I I' T s (I'.mkQuot s y) (I.mkQuot s x)
    rw [hF'.matrix_entries s hs x y, hF.matrix_entries s hs y x,
      quotWeight_mkQuot hQ hP, quotWeight_mkQuot hQ hP',
      periodization_kernelTranspose hP' hT.1]
  · obtain ⟨δ', hδ'⟩ := exists_decayRate hT'
    exact periodization_kernelLinComb (hF.summable s hs y x)
      ((hPer I I' hP hP' T' δ' hT' hδ').summable s hs y x) c c'
end YangMills.Construction.PeriodicOperators.TorusPeriodization
end

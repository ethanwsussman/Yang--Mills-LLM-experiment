import YangMills.Construction.PeriodicOperators.AdditivityAndIntegralOfTheLogarithmicNumberProof
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHomProof
import YangMills.Construction.PeriodicOperators.OrderOfHermitianMatricesUnderARootProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.QuotMatrixNorms
section WeightedFinite
variable {α β : Type} [Fintype α]
theorem wNorm_smul {w : α → ℝ} (hw : ∀ i, 0 ≤ w i) (a : ℂ) (f : α → ℂ) :
    wNorm w (a • f) = ‖a‖ * wNorm w f := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.wNorm_smul <;> assumption
theorem sqrt_weight_mul_norm_le {w : α → ℝ} (hw : ∀ i, 0 ≤ w i) (f : α → ℂ) (i : α) :
    Real.sqrt (w i) * ‖f i‖ ≤ wNorm w f := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.sqrt_weight_mul_norm_le_wNorm <;> assumption
theorem wNorm_pi_single [DecidableEq α] {w : α → ℝ} (i : α) :
    wNorm w (Pi.single i 1 : α → ℂ) = Real.sqrt (w i) := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.wNorm_single_one <;> assumption
theorem wNorm_map_le [Fintype β] {w : α → ℝ} {v : β → ℝ} (hw : ∀ i, 0 < w i)
    (hv : ∀ i, 0 ≤ v i) (T : (α → ℂ) →ₗ[ℂ] (β → ℂ)) (f : α → ℂ) :
    ENNReal.ofReal (wNorm v (T f)) ≤
      wOpNorm w v univ (fun f => T f) * ENNReal.ofReal (wNorm w f) := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.wNorm_apply_le_wOpNorm_mul <;> assumption
end WeightedFinite
section OnQuotients
variable {P Q R : PeriodicData}
theorem map_le_quotHomNorm (T : QuotHom P Q) {f : P.UnitQuot → ℂ}
    (hf : f ∈ wUnitBall (P.quotWeight 1) univ) :
    ENNReal.ofReal (wNorm (Q.quotWeight 1) (T f)) ≤ quotHomNorm T := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.ofReal_wNorm_apply_le_of_mem <;> assumption
theorem quotHomNorm_add_le [Fintype Q.UnitQuot] (hv : ∀ c, 0 < Q.quotWeight 1 c)
    (S T : QuotHom P Q) : quotHomNorm (S + T) ≤ quotHomNorm S + quotHomNorm T := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.quotHomNorm_add_le <;> assumption
theorem quotHomNorm_smul_le [Fintype Q.UnitQuot] (hv : ∀ c, 0 < Q.quotWeight 1 c) (a : ℂ)
    (T : QuotHom P Q) : quotHomNorm (a • T) ≤ ENNReal.ofReal ‖a‖ * quotHomNorm T := by
  refine iSup₂_le fun f hf => ?_
  show ENNReal.ofReal (wNorm (Q.quotWeight 1) (a • T f)) ≤ _
  rw [wNorm_smul (fun c => (hv c).le), ENNReal.ofReal_mul (norm_nonneg a)]
  have := map_le_quotHomNorm T hf
  gcongr
theorem quotHomNorm_zero : quotHomNorm (0 : QuotHom P Q) = 0 := by
  refine le_antisymm (iSup₂_le fun f _ => ?_) zero_le
  show ENNReal.ofReal (wNorm (Q.quotWeight 1) (0 : Q.UnitQuot → ℂ)) ≤ 0
  simp [wNorm]
theorem quotHomNorm_comp_le [Fintype P.UnitQuot] [Fintype Q.UnitQuot]
    (hw : ∀ c, 0 < P.quotWeight 1 c) (hv : ∀ c, 0 < Q.quotWeight 1 c)
    (S : QuotHom P Q) (T : QuotHom R P) :
    quotHomNorm (S.comp T) ≤ quotHomNorm S * quotHomNorm T := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.quotHomNorm_comp_le <;> assumption
theorem quotHomNorm_id_le : quotHomNorm (LinearMap.id : QuotHom P P) ≤ 1 := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.quotHomNorm_id_le <;> assumption
theorem norm_linearMapEntry_le [Fintype P.UnitQuot] [Fintype Q.UnitQuot]
    (hw : ∀ c, 0 < P.quotWeight 1 c) (hv : ∀ c, 0 < Q.quotWeight 1 c)
    (T : QuotHom P Q) (hT : quotHomNorm T < ∞) (d : Q.UnitQuot) (c : P.UnitQuot) :
    ‖linearMapEntry T d c‖ ≤
      Real.sqrt (P.quotWeight 1 c) / Real.sqrt (Q.quotWeight 1 d) *
        (quotHomNorm T).toReal := by
  classical
  have hsd : 0 < Real.sqrt (Q.quotWeight 1 d) := Real.sqrt_pos.2 (hv d)
  have hent : linearMapEntry T d c = T (Pi.single c 1) d := by
    simp only [linearMapEntry]
  have hpt := sqrt_weight_mul_norm_le (fun c => (hv c).le) (T (Pi.single c 1)) d
  have hop := wNorm_map_le hw (fun c => (hv c).le) T (Pi.single c 1)
  rw [wNorm_pi_single] at hop
  have hreal : wNorm (Q.quotWeight 1) (T (Pi.single c 1)) ≤
      (quotHomNorm T).toReal * Real.sqrt (P.quotWeight 1 c) := by
    have hne : quotHomNorm T * ENNReal.ofReal (Real.sqrt (P.quotWeight 1 c)) ≠ ∞ :=
      ENNReal.mul_ne_top hT.ne ENNReal.ofReal_ne_top
    have hto := ENNReal.toReal_mono hne hop
    have hnn : 0 ≤ wNorm (Q.quotWeight 1) (T (Pi.single c 1)) := Real.sqrt_nonneg _
    rwa [ENNReal.toReal_ofReal hnn, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hto
  rw [hent, div_mul_eq_mul_div, le_div_iff₀ hsd]
  calc ‖T (Pi.single c 1) d‖ * Real.sqrt (Q.quotWeight 1 d)
      = Real.sqrt (Q.quotWeight 1 d) * ‖T (Pi.single c 1) d‖ := mul_comm _ _
    _ ≤ (quotHomNorm T).toReal * Real.sqrt (P.quotWeight 1 c) := hpt.trans hreal
    _ = Real.sqrt (P.quotWeight 1 c) * (quotHomNorm T).toReal := mul_comm _ _
theorem exists_uniform_entry_bound [Fintype P.UnitQuot] [Fintype Q.UnitQuot]
    (hw : ∀ c, 0 < P.quotWeight 1 c) (hv : ∀ c, 0 < Q.quotWeight 1 c)
    (hfin : ∀ T : QuotHom P Q, quotHomNorm T < ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : QuotHom P Q) (d : Q.UnitQuot) (c : P.UnitQuot),
      ‖linearMapEntry T d c‖ ≤ C * (quotHomNorm T).toReal := by
  have hq : ∀ (d : Q.UnitQuot) (c : P.UnitQuot),
      0 ≤ Real.sqrt (P.quotWeight 1 c) / Real.sqrt (Q.quotWeight 1 d) :=
    fun _ _ => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨∑ d, ∑ c, Real.sqrt (P.quotWeight 1 c) / Real.sqrt (Q.quotWeight 1 d),
    Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun c _ => hq d c, fun T d c => ?_⟩
  refine (norm_linearMapEntry_le hw hv T (hfin T) d c).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
  calc Real.sqrt (P.quotWeight 1 c) / Real.sqrt (Q.quotWeight 1 d)
      ≤ ∑ c₁, Real.sqrt (P.quotWeight 1 c₁) / Real.sqrt (Q.quotWeight 1 d) :=
        Finset.single_le_sum (f := fun c₁ =>
          Real.sqrt (P.quotWeight 1 c₁) / Real.sqrt (Q.quotWeight 1 d))
          (fun c₁ _ => hq d c₁) (Finset.mem_univ c)
    _ ≤ ∑ d₁, ∑ c₁, Real.sqrt (P.quotWeight 1 c₁) / Real.sqrt (Q.quotWeight 1 d₁) :=
        Finset.single_le_sum (f := fun d₁ =>
          ∑ c₁, Real.sqrt (P.quotWeight 1 c₁) / Real.sqrt (Q.quotWeight 1 d₁))
          (fun d₁ _ => Finset.sum_nonneg fun c₁ _ => hq d₁ c₁) (Finset.mem_univ d)
theorem trace_eq_sum_diag_entries [Fintype P.UnitQuot] (T : QuotHom P P) :
    LinearMap.trace ℂ (P.UnitQuot → ℂ) T = ∑ c, linearMapEntry T c c := by apply _root_.YangMills.SharedProofs.p55196 <;> assumption
end OnQuotients
theorem quotWeight_pos_of_transposeNorm (hQ : Quotients.QuotientTransposeNorm) (P : PeriodicData)
    (hP : IsPeriodic P) (c : P.UnitQuot) : 0 < P.quotWeight 1 c := by apply _root_.YangMills.Construction.PeriodicOperators.RootConjugationOrder.quotWeight_one_pos <;> assumption
theorem claim_holds (hQ : Quotients.QuotientTransposeNorm) : Claim := by
  intro P Q R hP hQ' hR
  have := hP.finite_quot
  have := hQ'.finite_quot
  have := Fintype.ofFinite P.UnitQuot
  have := Fintype.ofFinite Q.UnitQuot
  have hw := quotWeight_pos_of_transposeNorm hQ P hP
  have hv := quotWeight_pos_of_transposeNorm hQ Q hQ'
  have hfin : ∀ {K L : PeriodicData}, IsPeriodic K → IsPeriodic L →
      ∀ T : QuotHom K L, quotHomNorm T < ∞ := fun hK hL T =>
    (((hQ _ _ hK hL 1 one_pos).2.2.1 1 1 (Or.inl rfl) (Or.inl rfl)).1 T).2
  refine ⟨⟨hfin hP hQ', quotHomNorm_add_le hv, quotHomNorm_smul_le hv, quotHomNorm_zero,
    exists_uniform_entry_bound hw hv (hfin hP hQ')⟩, quotHomNorm_comp_le hw hv,
    quotHomNorm_id_le, ?_⟩
  obtain ⟨C, hC0, hC⟩ := exists_uniform_entry_bound hw hw (hfin hP hP)
  refine ⟨Fintype.card P.UnitQuot * C, mul_nonneg (Nat.cast_nonneg _) hC0, fun T => ?_⟩
  rw [trace_eq_sum_diag_entries]
  calc ‖∑ c, linearMapEntry T c c‖ ≤ ∑ c, ‖linearMapEntry T c c‖ := norm_sum_le _ _
    _ ≤ ∑ _c : P.UnitQuot, C * (quotHomNorm T).toReal :=
        Finset.sum_le_sum fun c _ => hC T c c
    _ = Fintype.card P.UnitQuot * C * (quotHomNorm T).toReal := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
end YangMills.Construction.PeriodicOperators.QuotMatrixNorms
end

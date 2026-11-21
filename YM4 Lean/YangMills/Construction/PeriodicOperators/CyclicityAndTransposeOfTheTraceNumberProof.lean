import YangMills.Construction.PeriodicOperators.AdditivityAndIntegralOfTheLogarithmicNumberProof
import YangMills.Construction.PeriodicOperators.CyclicityAndTransposeOfTheTraceNumber
import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.PeriodicOperators.ShiftInTheTraceOfTwoJets
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TraceNumberSymmetry
open JetQuad (IsJet)
open JetTraceShift (shiftedTrace)
section Entries
variable {J J' : Type}
private theorem linearMapEntry_ofEntries [Finite J] (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
private theorem trace_eq_sum_diag [Fintype J] (M : (J → ℂ) →ₗ[ℂ] (J → ℂ)) :
    LinearMap.trace ℂ (J → ℂ) M = ∑ j, linearMapEntry M j j := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ J) M]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr,
    linearMapEntry]
abbrev _root_.YangMills.SharedProofs.p9894 := @trace_eq_sum_diag
private theorem linearMapEntry_comp [Fintype J'] (A : (J' → ℂ) →ₗ[ℂ] (J → ℂ))
    (B : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (j k : J) :
    linearMapEntry (A.comp B) j k = ∑ m, linearMapEntry A j m * linearMapEntry B m k := by
  classical
  have hg : ∀ g : J' → ℂ, g = ∑ m, g m • (Pi.single m (1 : ℂ) : J' → ℂ) := by
    intro g
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  simp only [linearMapEntry, LinearMap.comp_apply]
  conv_lhs => rw [hg (B (Pi.single k 1))]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _
private theorem continuous_trace_of_comp [Finite J] [Finite J']
    {A : (Fin 4 → ℝ) → (J' → ℂ) →ₗ[ℂ] (J → ℂ)}
    {B : (Fin 4 → ℝ) → (J → ℂ) →ₗ[ℂ] (J' → ℂ)}
    (hA : ∀ j m, Continuous fun y => linearMapEntry (A y) j m)
    (hB : ∀ m j, Continuous fun y => linearMapEntry (B y) m j) :
    Continuous fun y => LinearMap.trace ℂ (J → ℂ) ((A y).comp (B y)) := by
  cases nonempty_fintype J
  cases nonempty_fintype J'
  simp only [trace_eq_sum_diag, linearMapEntry_comp]
  exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun m _ => (hA j m).mul (hB m j)
end Entries
private theorem quotWeight_pos {I : PeriodicData} (hI : IsPeriodic I) (q : I.UnitQuot) :
    0 < I.quotWeight 1 q := by
  induction q using Quot.ind with
  | mk x =>
    have hcompat : ∀ a b : I.Carrier, (∃ n : Fin 4 → ℤ, b = I.translate (1 • n) a) →
        I.weightOf a = I.weightOf b := by
      rintro a _ ⟨n, rfl⟩
      simp only [PeriodicData.weightOf, hI.componentOf_translate]
    have hex : ∀ x', I.mkQuot 1 x' = Quot.mk _ x → I.weightOf x' = I.weightOf x :=
      fun x' h => congrArg (Quot.lift I.weightOf hcompat) h
    have hspec := Classical.epsilon_spec
      (p := fun w => ∀ x', I.mkQuot 1 x' = Quot.mk _ x → I.weightOf x' = w) ⟨_, hex⟩
    have hw := hspec x rfl
    unfold PeriodicData.quotWeight
    rw [← hw]
    exact hI.weight_pos _
abbrev _root_.YangMills.SharedProofs.p9241 := @quotWeight_pos
private theorem trace_quotHomTranspose {I : PeriodicData} (hI : IsPeriodic I)
    (M : QuotHom I I) :
    LinearMap.trace ℂ (I.UnitQuot → ℂ) (quotHomTranspose M) =
      LinearMap.trace ℂ (I.UnitQuot → ℂ) M := by
  have := hI.finite_quot
  have := Fintype.ofFinite I.UnitQuot
  rw [trace_eq_sum_diag, trace_eq_sum_diag]
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold quotHomTranspose
  rw [linearMapEntry_ofEntries]
  have hw : I.quotWeight 1 q ≠ 0 := (quotWeight_pos hI q).ne'
  simp [wTranspose, div_self hw]
private theorem continuous_toComplexVec : Continuous toComplexVec := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.continuous_toComplexVec <;> assumption
private theorem toComplexVec_mem_realDualPoints (y : (Fin 4 → ℝ)) :
    toComplexVec y ∈ realDualPoints := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.toComplexVec_mem_realDualPoints <;> assumption
private theorem toComplexVec_mem_imStrip {δ : ℝ} (hδ : 0 < δ) (y : (Fin 4 → ℝ)) :
    toComplexVec y ∈ imStrip (2 * δ) := by
  intro μ
  have h : (toComplexVec y μ).im = 0 := Complex.ofReal_im (y μ)
  rw [h, abs_zero]
  positivity
private theorem continuous_entry_of_holomorphic {I I' : PeriodicData} {D : Set (Fin 4 → ℂ)}
    {A : (Fin 4 → ℂ) → QuotHom I I'} (hA : IsHolomorphicNbhd D A)
    (hD : ∀ y, toComplexVec y ∈ D) (q' : I'.UnitQuot) (q : I.UnitQuot) :
    Continuous fun y => linearMapEntry (A (toComplexVec y)) q' q := by
  obtain ⟨O, -, hDO, hO⟩ := hA
  have h1 : ContinuousOn (fun κ => linearMapEntry (A κ) q' q) O :=
    (continuous_apply (0 : Fin 1)).comp_continuousOn (hO q' q).2.1
  exact h1.comp_continuous continuous_toComplexVec fun y => hDO (hD y)
private theorem torusAverage_add {f g : (Fin 4 → ℝ) → ℂ} (hf : Continuous f) (hg : Continuous g) :
    torusAverage (fun y => f y + g y) = torusAverage f + torusAverage g := by apply _root_.YangMills.DeltaSharedProofs.p501029 <;> assumption
private theorem torusAverage_comp_neg (f : (Fin 4 → ℝ) → ℂ) :
    torusAverage (fun y => f (-y)) = torusAverage f := by
  unfold torusAverage
  congr 1
  have h := (Measure.measurePreserving_neg (volume : Measure (Fin 4 → ℝ))).setIntegral_preimage_emb
    (MeasurableEquiv.neg (Fin 4 → ℝ)).measurableEmbedding f
    (Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi))
  have hs : (fun y : (Fin 4 → ℝ) => -y) ⁻¹' Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi) =
      Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi) := by
    ext y
    simp only [mem_preimage, mem_Icc, Pi.le_def, Pi.neg_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun i => by linarith [h2 i], fun i => by linarith [h1 i]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun i => by linarith [h2 i], fun i => by linarith [h1 i]⟩
  erw [hs] at h
  exact h
private theorem traceNumber_mul_swap {δ : ℝ} {p : Fin 4 → ℂ} (hδ : 0 < δ) (hp : p ∈ imStrip δ)
    (hShift : JetTraceShift.Claim) {I₁ I₂ : PeriodicData}
    (hI₁ : IsPeriodic I₁) (hI₂ : IsPeriodic I₂)
    {T : JetQuad I₁ I₂} {S : JetQuad I₂ I₁} (hT : IsJet δ p T) (hS : IsJet δ p S) :
    JetQuad.traceNumber (JetQuad.mul p T S) = JetQuad.traceNumber (JetQuad.mul p S T) := by
  have := hI₁.finite_quot
  have := hI₂.finite_quot
  obtain ⟨hg₁, hg₁', hs₁⟩ := hShift δ p hδ hp I₂ I₁ hI₂ hI₁ T S hT hS
  obtain ⟨hg₂, hg₂', hs₂⟩ := hShift δ p hδ hp I₁ I₂ hI₁ hI₂ S T hS hT
  have hreal := toComplexVec_mem_realDualPoints
  have hstrip := toComplexVec_mem_imStrip hδ
  have ha : Continuous fun y => LinearMap.trace ℂ (I₂.UnitQuot → ℂ)
      ((T.f11 (toComplexVec y)).comp (S.f00 (toComplexVec y))) :=
    continuous_trace_of_comp (continuous_entry_of_holomorphic hT.holo_f11 hreal)
      (continuous_entry_of_holomorphic hS.holo_f00 hstrip)
  have hb : Continuous fun y => LinearMap.trace ℂ (I₂.UnitQuot → ℂ)
      ((T.f00 (toComplexVec y)).comp (S.f11 (toComplexVec y))) :=
    continuous_trace_of_comp (continuous_entry_of_holomorphic hT.holo_f00 hstrip)
      (continuous_entry_of_holomorphic hS.holo_f11 hreal)
  have e₁ : (fun y => LinearMap.trace ℂ (I₂.UnitQuot → ℂ) ((JetQuad.mul p T S).f11 (toComplexVec y))) =
      fun y => ((LinearMap.trace ℂ (I₂.UnitQuot → ℂ)
          ((T.f11 (toComplexVec y)).comp (S.f00 (toComplexVec y))) +
        LinearMap.trace ℂ (I₂.UnitQuot → ℂ)
          ((T.f00 (toComplexVec y)).comp (S.f11 (toComplexVec y)))) +
        shiftedTrace p T S (toComplexVec y)) + shiftedTrace p S T (toComplexVec y + p) := by
    funext y
    simp only [JetQuad.mul, map_add, shiftedTrace, add_sub_cancel_right]
    rw [LinearMap.trace_comp_comm' (S.f10 (toComplexVec y))]
  have e₂ : (fun y => LinearMap.trace ℂ (I₁.UnitQuot → ℂ) ((JetQuad.mul p S T).f11 (toComplexVec y))) =
      fun y => ((LinearMap.trace ℂ (I₂.UnitQuot → ℂ)
          ((T.f11 (toComplexVec y)).comp (S.f00 (toComplexVec y))) +
        LinearMap.trace ℂ (I₂.UnitQuot → ℂ)
          ((T.f00 (toComplexVec y)).comp (S.f11 (toComplexVec y)))) +
        shiftedTrace p S T (toComplexVec y)) + shiftedTrace p T S (toComplexVec y + p) := by
    funext y
    simp only [JetQuad.mul, map_add, shiftedTrace, add_sub_cancel_right]
    rw [LinearMap.trace_comp_comm' (S.f11 (toComplexVec y)),
      LinearMap.trace_comp_comm' (S.f00 (toComplexVec y)),
      LinearMap.trace_comp_comm' (S.f01 (toComplexVec y + p))]
    ring
  unfold JetQuad.traceNumber
  have hab : Continuous fun y => LinearMap.trace ℂ (I₂.UnitQuot → ℂ)
        ((T.f11 (toComplexVec y)).comp (S.f00 (toComplexVec y))) +
      LinearMap.trace ℂ (I₂.UnitQuot → ℂ)
        ((T.f00 (toComplexVec y)).comp (S.f11 (toComplexVec y))) := ha.add hb
  have h₁ : Continuous fun y => (LinearMap.trace ℂ (I₂.UnitQuot → ℂ)
        ((T.f11 (toComplexVec y)).comp (S.f00 (toComplexVec y))) +
      LinearMap.trace ℂ (I₂.UnitQuot → ℂ)
        ((T.f00 (toComplexVec y)).comp (S.f11 (toComplexVec y)))) +
      shiftedTrace p T S (toComplexVec y) := hab.add hg₁
  have h₂ : Continuous fun y => (LinearMap.trace ℂ (I₂.UnitQuot → ℂ)
        ((T.f11 (toComplexVec y)).comp (S.f00 (toComplexVec y))) +
      LinearMap.trace ℂ (I₂.UnitQuot → ℂ)
        ((T.f00 (toComplexVec y)).comp (S.f11 (toComplexVec y)))) +
      shiftedTrace p S T (toComplexVec y) := hab.add hg₂
  rw [e₁, e₂, torusAverage_add h₁ hg₂', torusAverage_add hab hg₁,
    torusAverage_add h₂ hg₁', torusAverage_add hab hg₂, hs₁, hs₂]
  ring
private theorem traceNumber_transposeAt {p : Fin 4 → ℂ} {I : PeriodicData}
    (hI : IsPeriodic I) (T : JetQuad I I) :
    JetQuad.traceNumber (JetQuad.transposeAt p T) = JetQuad.traceNumber T := by
  unfold JetQuad.traceNumber
  rw [← torusAverage_comp_neg fun y => LinearMap.trace ℂ (I.UnitQuot → ℂ) (T.f11 (toComplexVec y))]
  congr 1
  funext y
  have hneg : toComplexVec (-y) = -toComplexVec y := by
    funext μ
    simp [toComplexVec]
  rw [hneg]
  exact trace_quotHomTranspose hI _
theorem claim_of_jetTraceShift (hShift : JetTraceShift.Claim) : Claim :=
  fun _ _ hδ hp _ _ hI₁ hI₂ =>
    ⟨fun _ _ hT hS => traceNumber_mul_swap hδ hp hShift hI₁ hI₂ hT hS,
      fun T _ => traceNumber_transposeAt hI₁ T⟩
end YangMills.Construction.PeriodicOperators.TraceNumberSymmetry
end

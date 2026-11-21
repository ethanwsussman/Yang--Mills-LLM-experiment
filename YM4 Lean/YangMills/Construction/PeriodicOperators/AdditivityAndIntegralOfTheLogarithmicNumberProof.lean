import YangMills.Construction.PeriodicOperators.AdditivityAndIntegralOfTheLogarithmicNumber
import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.NormsAndTracesOfMatricesOnTheClasses
import YangMills.Construction.PeriodicOperators.ShiftInTheTraceOfTwoJets
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetLogNumber
open JetQuad
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open JetTraceShift (shiftedTrace)
variable {I : PeriodicData}
private theorem trace_prod_expand {V : Type} [AddCommGroup V] [Module ℂ V]
    (a ai a' ai' b bi b' bi' A11 A10 A01 A01' B11 B10 B01 B10' : Module.End ℂ V)
    (ha : ai * a = 1) (ha' : ai' * a' = 1) (hb : b * bi = 1) (hb' : b' * bi' = 1) :
    LinearMap.trace ℂ V ((bi * ai) * (A11 * b + a * B11 + A10 * B01 + A01' * B10') -
        (bi * ai) * ((A10 * b' + a * B10) * ((bi' * ai') * (A01 * b + a' * B01)))) =
      LinearMap.trace ℂ V (ai * A11 - ai * (A10 * (ai' * A01))) +
        LinearMap.trace ℂ V (bi * B11 - bi * (B10 * (bi' * B01))) +
        (LinearMap.trace ℂ V (B10' * (bi * (ai * A01'))) -
          LinearMap.trace ℂ V (B10 * (bi' * (ai' * A01)))) := by
  have hla : ∀ x, ai * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have hla' : ∀ x, ai' * (a' * x) = x := fun x => by rw [← mul_assoc, ha', one_mul]
  have hlb' : ∀ x, b' * (bi' * x) = x := fun x => by rw [← mul_assoc, hb', one_mul]
  have hcyc : ∀ x, LinearMap.trace ℂ V (bi * (x * b)) = LinearMap.trace ℂ V x := fun x => by
    rw [← mul_assoc, LinearMap.trace_mul_comm ℂ (bi * x) b, ← mul_assoc, hb, one_mul]
  have h1 := hcyc (ai * A11)
  have h2 := hcyc (ai * (A10 * (ai' * A01)))
  have h3 := hcyc (B10 * (bi' * (ai' * A01)))
  have h4 : LinearMap.trace ℂ V (bi * (ai * (A01' * B10'))) =
      LinearMap.trace ℂ V (B10' * (bi * (ai * A01'))) := by
    rw [LinearMap.trace_mul_comm ℂ B10']
    simp only [mul_assoc]
  simp only [mul_assoc] at h1 h2 h3
  simp only [mul_add, add_mul, mul_assoc, hla, hla', hlb', map_add, map_sub]
  linear_combination h1 + h4 - h2 - h3
private theorem quotHomInverse_comp {M N : QuotHom I I}
    (hM : IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ)))
    (hN : IsUnit (N : Module.End ℂ (I.UnitQuot → ℂ))) :
    quotHomInverse (M.comp N) = (quotHomInverse N).comp (quotHomInverse M) := by
  obtain ⟨u, rfl⟩ := hM
  obtain ⟨v, rfl⟩ := hN
  show Ring.inverse ((u : Module.End ℂ (I.UnitQuot → ℂ)) * v) = Ring.inverse _ * Ring.inverse _
  rw [← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, Ring.inverse_unit, mul_inv_rev,
    Units.val_mul]
private theorem trace_eq_sum_diag [Fintype I.UnitQuot] (M : QuotHom I I) :
    LinearMap.trace ℂ (I.UnitQuot → ℂ) M = ∑ c, linearMapEntry M c c := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ I.UnitQuot) M]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr,
    linearMapEntry]
abbrev _root_.YangMills.SharedProofs.p55196 := @trace_eq_sum_diag
private theorem toComplexVec_mem_real (x : AmbientSpace) : toComplexVec x ∈ realDualPoints := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.toComplexVec_mem_realDualPoints <;> assumption
private theorem continuous_trace_f11 (hI : IsPeriodic I) {δ : ℝ} {p : Fin 4 → ℂ}
    {T : JetQuad I I} (hT : IsJet δ p T) :
    Continuous fun x => LinearMap.trace ℂ (I.UnitQuot → ℂ) (T.f11 (toComplexVec x)) := by
  have := hI.finite_quot
  have := Fintype.ofFinite I.UnitQuot
  obtain ⟨O, -, hRO, hO⟩ := hT.holo_f11
  simp only [trace_eq_sum_diag]
  refine continuous_finsetSum _ fun c _ => ?_
  have hc : ContinuousOn (fun κ => linearMapEntry (T.f11 κ) c c) O :=
    (continuous_apply (0 : Fin 1)).comp_continuousOn (hO c c).2.1
  exact hc.comp_continuous
    (continuous_pi fun μ => Complex.continuous_ofReal.comp (continuous_apply μ))
    fun x => hRO (toComplexVec_mem_real x)
private theorem integrableOn_torusBox {f : AmbientSpace → ℂ} (hf : Continuous f) :
    IntegrableOn f (Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi)) :=
  hf.continuousOn.integrableOn_compact isCompact_Icc
private theorem torusAverage_add {f g : AmbientSpace → ℂ} (hf : Continuous f)
    (hg : Continuous g) :
    torusAverage (fun x => f x + g x) = torusAverage f + torusAverage g := by
  unfold torusAverage
  rw [integral_add (integrableOn_torusBox hf) (integrableOn_torusBox hg), mul_add]
abbrev _root_.YangMills.DeltaSharedProofs.p501029 := @torusAverage_add
abbrev _root_.YangMills.SharedProofs.p18494 := @torusAverage_add
private theorem torusAverage_add_smul_sub {f g h : AmbientSpace → ℂ} (a : ℂ)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (heq : torusAverage g = torusAverage h) :
    torusAverage (fun x => f x + a * (g x - h x)) = torusAverage f := by
  have hd : Continuous fun x => a * (g x - h x) := continuous_const.mul (hg.sub hh)
  rw [torusAverage_add hf hd]
  have hsplit : torusAverage (fun x => a * (g x - h x)) =
      a * (torusAverage g - torusAverage h) := by
    unfold torusAverage
    rw [integral_const_mul, integral_sub (integrableOn_torusBox hg) (integrableOn_torusBox hh)]
    ring
  rw [hsplit, heq]
  ring
section Components
variable (p : Fin 4 → ℂ) (T : JetQuad I I)
private theorem normalize_f10 (κ : Fin 4 → ℂ) :
    (normalize p T).f10 κ = (quotHomInverse (T.f00 (κ + p))).comp (T.f10 κ) := by
  simp [JetQuad.normalize, JetQuad.add, JetQuad.smul, JetQuad.mul, JetQuad.one,
    JetQuad.zeroPartInv]
private theorem normalize_f01 (κ : Fin 4 → ℂ) :
    (normalize p T).f01 κ = (quotHomInverse (T.f00 (κ - p))).comp (T.f01 κ) := by
  simp [JetQuad.normalize, JetQuad.add, JetQuad.smul, JetQuad.mul, JetQuad.one,
    JetQuad.zeroPartInv]
private theorem normalize_f11 (κ : Fin 4 → ℂ) :
    (normalize p T).f11 κ = (quotHomInverse (T.f00 κ)).comp (T.f11 κ) := by
  simp [JetQuad.normalize, JetQuad.add, JetQuad.smul, JetQuad.mul, JetQuad.one,
    JetQuad.zeroPartInv]
private theorem normalize_f00 (κ : Fin 4 → ℂ)
    (h : IsUnit (T.f00 κ : Module.End ℂ (I.UnitQuot → ℂ))) : (normalize p T).f00 κ = 0 := by
  have e : (quotHomInverse (T.f00 κ)).comp (T.f00 κ) = LinearMap.id :=
    Ring.inverse_mul_cancel _ h
  have e' : (normalize p T).f00 κ =
      (quotHomInverse (T.f00 κ)).comp (T.f00 κ) + (-1 : ℂ) • (LinearMap.id : QuotHom I I) := rfl
  rw [e', e]
  refine LinearMap.ext fun f => ?_
  simp
private theorem mul_self_f11 (κ : Fin 4 → ℂ) (h : (normalize p T).f00 κ = 0) :
    (JetQuad.mul p (normalize p T) (normalize p T)).f11 κ =
      ((normalize p T).f10 (κ - p)).comp ((normalize p T).f01 κ) +
        ((normalize p T).f01 (κ + p)).comp ((normalize p T).f10 κ) := by
  simp [JetQuad.mul, h]
private theorem logDensity_eq (κ : Fin 4 → ℂ) :
    logDensity p T κ =
      LinearMap.trace ℂ (I.UnitQuot → ℂ) ((normalize p T).f11 κ) -
        shiftedTrace p (normalize p T) (normalize p T) κ := by
  unfold logDensity shiftedTrace
  rw [normalize_f11, normalize_f10, normalize_f01, sub_add_cancel κ p, map_sub]
  simp only [LinearMap.comp_assoc]
private theorem trace_swap_term (κ : Fin 4 → ℂ) :
    LinearMap.trace ℂ (I.UnitQuot → ℂ)
        (((normalize p T).f01 (κ + p)).comp ((normalize p T).f10 κ)) =
      shiftedTrace p (normalize p T) (normalize p T) (κ + p) := by
  unfold shiftedTrace
  rw [add_sub_cancel_right κ p]
  exact LinearMap.trace_mul_comm ℂ _ _
private theorem trace_logSeries_f11 (κ : Fin 4 → ℂ) :
    LinearMap.trace ℂ (I.UnitQuot → ℂ) ((logSeries p T).f11 κ) =
      LinearMap.trace ℂ (I.UnitQuot → ℂ) ((normalize p T).f11 κ) + -(1 / 2) *
        LinearMap.trace ℂ (I.UnitQuot → ℂ)
          ((JetQuad.mul p (normalize p T) (normalize p T)).f11 κ) := by
  show LinearMap.trace ℂ (I.UnitQuot → ℂ) ((normalize p T).f11 κ + (-(1 / 2) : ℂ) •
    (JetQuad.mul p (normalize p T) (normalize p T)).f11 κ) = _
  rw [map_add, map_smul, smul_eq_mul]
end Components
private theorem logNumber_eq_average {δ : ℝ} {p : Fin 4 → ℂ} (hI : IsPeriodic I)
    {T : JetQuad I I} (hN : IsJet δ p (normalize p T))
    (hunit : ∀ x : AmbientSpace,
      IsUnit (T.f00 (toComplexVec x) : Module.End ℂ (I.UnitQuot → ℂ)))
    (hc : Continuous fun x => shiftedTrace p (normalize p T) (normalize p T) (toComplexVec x))
    (hc' : Continuous fun x =>
      shiftedTrace p (normalize p T) (normalize p T) (toComplexVec x + p))
    (heq : torusAverage (fun x =>
        shiftedTrace p (normalize p T) (normalize p T) (toComplexVec x + p)) =
      torusAverage fun x => shiftedTrace p (normalize p T) (normalize p T) (toComplexVec x)) :
    logNumber p T = torusAverage (fun x => logDensity p T (toComplexVec x)) ∧
      Continuous fun x => logDensity p T (toComplexVec x) := by
  have hcont : Continuous fun x => logDensity p T (toComplexVec x) := by
    simp only [logDensity_eq]
    exact (continuous_trace_f11 hI hN).sub hc
  refine ⟨?_, hcont⟩
  have key : (fun x => LinearMap.trace ℂ (I.UnitQuot → ℂ)
        ((logSeries p T).f11 (toComplexVec x))) =
      fun x => logDensity p T (toComplexVec x) + (-(1 / 2) : ℂ) *
        (shiftedTrace p (normalize p T) (normalize p T) (toComplexVec x + p) -
          shiftedTrace p (normalize p T) (normalize p T) (toComplexVec x)) := by
    funext x
    have h1 : LinearMap.trace ℂ (I.UnitQuot → ℂ)
        (((normalize p T).f10 (toComplexVec x - p)).comp
          ((normalize p T).f01 (toComplexVec x))) =
        shiftedTrace p (normalize p T) (normalize p T) (toComplexVec x) := rfl
    rw [trace_logSeries_f11, mul_self_f11 p T _ (normalize_f00 p T _ (hunit x)), map_add, h1,
      trace_swap_term, logDensity_eq]
    ring
  unfold logNumber traceNumber
  rw [key, torusAverage_add_smul_sub _ hcont hc' hc heq]
private theorem shiftedTrace_parts (p : Fin 4 → ℂ) (T S : JetQuad I I) (κ : Fin 4 → ℂ) :
    shiftedTrace p (JetQuad.mul p S (zeroPartInv S))
        (JetQuad.mul p (zeroPartInv T) T) κ =
      LinearMap.trace ℂ (I.UnitQuot → ℂ) ((S.f10 (κ - p)).comp
        ((quotHomInverse (S.f00 (κ - p))).comp
          ((quotHomInverse (T.f00 (κ - p))).comp (T.f01 κ)))) := by
  simp [shiftedTrace, JetQuad.mul, zeroPartInv, LinearMap.comp_assoc]
private theorem logDensity_mul (p : Fin 4 → ℂ) (T S : JetQuad I I) (κ : Fin 4 → ℂ)
    (hT : IsUnit (T.f00 κ : Module.End ℂ (I.UnitQuot → ℂ)))
    (hS : IsUnit (S.f00 κ : Module.End ℂ (I.UnitQuot → ℂ)))
    (hT' : IsUnit (T.f00 (κ - p) : Module.End ℂ (I.UnitQuot → ℂ)))
    (hS' : IsUnit (S.f00 (κ - p) : Module.End ℂ (I.UnitQuot → ℂ))) :
    logDensity p (JetQuad.mul p T S) κ =
      logDensity p T κ + logDensity p S κ +
        (shiftedTrace p (JetQuad.mul p S (zeroPartInv S))
            (JetQuad.mul p (zeroPartInv T) T) (κ + p) -
          shiftedTrace p (JetQuad.mul p S (zeroPartInv S))
            (JetQuad.mul p (zeroPartInv T) T) κ) := by
  rw [shiftedTrace_parts, shiftedTrace_parts, add_sub_cancel_right κ p]
  have e := trace_prod_expand (T.f00 κ) (quotHomInverse (T.f00 κ)) (T.f00 (κ - p))
    (quotHomInverse (T.f00 (κ - p))) (S.f00 κ) (quotHomInverse (S.f00 κ)) (S.f00 (κ - p))
    (quotHomInverse (S.f00 (κ - p))) (T.f11 κ) (T.f10 (κ - p)) (T.f01 κ) (T.f01 (κ + p))
    (S.f11 κ) (S.f10 (κ - p)) (S.f01 κ) (S.f10 κ) (Ring.inverse_mul_cancel _ hT)
    (Ring.inverse_mul_cancel _ hT') (Ring.mul_inverse_cancel _ hS)
    (Ring.mul_inverse_cancel _ hS')
  unfold logDensity
  simp only [JetQuad.mul]
  rw [quotHomInverse_comp hT hS, quotHomInverse_comp hT' hS', sub_add_cancel κ p]
  exact e
theorem claim_holds (hArgs : JetArgumentsAndEqualJets)
    (hLoc : JetDomains.OpFunJetTheory)
    (hNorm : QuotMatrixNorms.Claim)
    (hShift : JetTraceShift.Claim) : Claim := by
  intro δ p hδ hp I hI
  have hF : JetDomains.JetAlgebra I I I δ p :=
    hLoc.2.2 I I I hI hI hI δ p hδ hp
  have hpts := (hArgs.1 δ p hδ hp).1
  have hin : ∀ x : AmbientSpace, toComplexVec x ∈ imStrip (2 * δ) ∧
      toComplexVec x - p ∈ imStrip (2 * δ) := fun x => by
    have h := hpts.mem_real _ (toComplexVec_mem_real x)
    exact ⟨h.1.1.1, (hpts.mem_addShift _ h.2.1).1⟩
  have hform : ∀ T : JetQuad I I, IsInvertibleJet δ p T →
      logNumber p T =
          torusAverage (fun x => logDensity p T (toComplexVec x)) ∧
        Continuous fun x => logDensity p T (toComplexVec x) := fun T hT => by
    have hN := (hF.invertible_derived_isJet T hT).2.1
    obtain ⟨c1, c2, ceq⟩ := hShift δ p hδ hp I I hI hI _ _ hN hN
    exact logNumber_eq_average hI hN (fun x => hT.isUnit_f00 _ (hin x).1) c1 c2 ceq
  have hprod : QuotMatrixNorms.NormSubmul I I I :=
    (hNorm I I I hI hI hI).2.1
  have hinv : ∀ T S : JetQuad I I, IsInvertibleJet δ p T → IsInvertibleJet δ p S →
      IsInvertibleJet δ p (JetQuad.mul p T S) := fun T S hT hS => by
    refine ⟨hF.mul_isJet T S hT.isJet hS.isJet,
      fun κ hκ => (hT.isUnit_f00 κ hκ).mul (hS.isUnit_f00 κ hκ), ?_⟩
    calc (⨆ κ ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse ((JetQuad.mul p T S).f00 κ)))
        ≤ (⨆ κ ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse (S.f00 κ))) *
            ⨆ κ ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse (T.f00 κ)) :=
          iSup₂_le fun κ hκ => by
            show quotHomNorm (quotHomInverse ((T.f00 κ).comp (S.f00 κ))) ≤ _
            rw [quotHomInverse_comp (hT.isUnit_f00 κ hκ) (hS.isUnit_f00 κ hκ)]
            exact (hprod _ _).trans (mul_le_mul'
              (le_iSup₂ (f := fun κ (_ : κ ∈ imStrip (2 * δ)) =>
                quotHomNorm (quotHomInverse (S.f00 κ))) κ hκ)
              (le_iSup₂ (f := fun κ (_ : κ ∈ imStrip (2 * δ)) =>
                quotHomNorm (quotHomInverse (T.f00 κ))) κ hκ))
      _ < ⊤ := ENNReal.mul_lt_top hS.bdd_inverse hT.bdd_inverse
  refine ⟨fun T S hT hS => ⟨hinv T S hT hS, ?_⟩, fun T hT => (hform T hT).1⟩
  have hA : IsJet δ p (JetQuad.mul p S (zeroPartInv S)) :=
    hF.mul_isJet _ _ hS.isJet (hF.zeroPart_isJet S hS).2
  have hB : IsJet δ p (JetQuad.mul p (zeroPartInv T) T) :=
    (hF.invertible_derived_isJet T hT).1
  obtain ⟨c1, c2, ceq⟩ := hShift δ p hδ hp I I hI hI _ _ hA hB
  have key : (fun x => logDensity p (JetQuad.mul p T S) (toComplexVec x)) =
      fun x => (logDensity p T (toComplexVec x) +
          logDensity p S (toComplexVec x)) + (1 : ℂ) *
        (shiftedTrace p (JetQuad.mul p S (zeroPartInv S))
            (JetQuad.mul p (zeroPartInv T) T) (toComplexVec x + p) -
          shiftedTrace p (JetQuad.mul p S (zeroPartInv S))
            (JetQuad.mul p (zeroPartInv T) T) (toComplexVec x)) := by
    funext x
    rw [one_mul]
    exact logDensity_mul p T S _ (hT.isUnit_f00 _ (hin x).1) (hS.isUnit_f00 _ (hin x).1)
      (hT.isUnit_f00 _ (hin x).2) (hS.isUnit_f00 _ (hin x).2)
  have hsum : Continuous fun x => logDensity p T (toComplexVec x) +
      logDensity p S (toComplexVec x) := (hform T hT).2.add (hform S hS).2
  rw [(hform _ (hinv T S hT hS)).1, key, torusAverage_add_smul_sub _ hsum c2 c1 ceq,
    torusAverage_add (hform T hT).2 (hform S hS).2, ← (hform T hT).1, ← (hform S hS).1]
end YangMills.Construction.PeriodicOperators.JetLogNumber
end

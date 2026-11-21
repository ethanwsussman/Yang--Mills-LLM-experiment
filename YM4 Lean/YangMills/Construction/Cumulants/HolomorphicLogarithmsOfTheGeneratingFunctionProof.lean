import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionFacts
import YangMills.Construction.Cumulants.ExponentialMomentSeries
import YangMills.Construction.Cumulants.HolomorphicLogsOfMomentGeneratingFunction
import YangMills.Construction.Cumulants.TupleGeneratingFunctionAndItsLogarithm
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.Cumulants.HolomorphicLog
open YangMills.Construction.Probability (IsBoundedRealRV supModulus complexExpectation)
open YangMills.Construction.ComplexVariables (IsHolomorphicScalar absMonomial)
open YangMills.Construction.Coordinates (ComplexCoordinates)
open YangMills.Construction.PowerSeries (MultiIndex)
private theorem IsHolomorphicScalar.continuousOn' {n : ℕ} {U : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ} (hF : IsHolomorphicScalar U F) : ContinuousOn F U :=
  (continuous_apply (0 : Fin 1)).comp_continuousOn hF.2.1
private theorem norm_monomial_eq_absMonomial {n : ℕ} (w : ComplexCoordinates n)
    (β : MultiIndex n) : ‖MultiIndex.monomial w β‖ = absMonomial w β := by
  simp [MultiIndex.monomial, absMonomial, norm_prod, norm_pow]
private theorem absMonomial_nonneg' {n : ℕ} (w : ComplexCoordinates n) (β : MultiIndex n) :
    0 ≤ absMonomial w β :=
  norm_monomial_eq_absMonomial w β ▸ norm_nonneg _
private theorem norm_mgf_sub_one_le (hSer : ExponentialMomentSeriesExpansion)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hn : 1 ≤ n) (hX : ∀ i, IsBoundedRealRV (X i))
    (w : ComplexCoordinates n) :
    ‖tupleMomentGeneratingFunction μ X w - 1‖ ≤ Real.exp (weightedModulusSum X w) - 1 := by
  obtain ⟨-, -, -, hExp, -⟩ := hSer Ω μ n X hn hX
  obtain ⟨hNormSum, hEq, hMom, hMaj⟩ := hExp w
  let B : Fin n → ℝ := fun i => supModulus fun ω => (X i ω : ℂ)
  let M : MultiIndex n → ℂ := fun β =>
    complexExpectation μ fun ω => ((MultiIndex.monomial X β ω : ℝ) : ℂ)
  let T : MultiIndex n → ℂ := fun β =>
    MultiIndex.monomial w β / (MultiIndex.factorial β : ℂ) * M β
  let R : MultiIndex n → ℝ := fun β =>
    absMonomial w β / (MultiIndex.factorial β : ℝ) * MultiIndex.monomial B β
  have hTsum : Summable T := Summable.of_norm hNormSum
  have hEq' : tupleMomentGeneratingFunction μ X w = ∑' β, T β := hEq
  have hMom' : ∀ β, ‖M β‖ ≤ MultiIndex.monomial B β := hMom
  have hR : HasSum R (Real.exp (weightedModulusSum X w)) := hMaj
  have hM0 : M 0 = 1 := by
    simp [M, complexExpectation, MultiIndex.monomial]
  have hT0 : T 0 = 1 := by
    simp [T, hM0, MultiIndex.monomial, MultiIndex.factorial]
  have hR0 : R 0 = 1 := by
    simp [R, absMonomial, MultiIndex.monomial, MultiIndex.factorial]
  have hTsub : HasSum (fun β => T β - if β = 0 then (1 : ℂ) else 0)
      (tupleMomentGeneratingFunction μ X w - 1) := by
    rw [hEq']
    exact hTsum.hasSum.sub (hasSum_ite_eq 0 1)
  have hRsub : HasSum (fun β => R β - if β = 0 then (1 : ℝ) else 0)
      (Real.exp (weightedModulusSum X w) - 1) :=
    hR.sub (hasSum_ite_eq 0 1)
  refine hTsub.norm_le_of_bounded hRsub fun β => ?_
  by_cases hβ : β = 0
  · subst hβ
    simp [hT0, hR0]
  · simp only [hβ, if_false, sub_zero]
    change ‖MultiIndex.monomial w β / (MultiIndex.factorial β : ℂ) * M β‖ ≤
      absMonomial w β / (MultiIndex.factorial β : ℝ) * MultiIndex.monomial B β
    rw [norm_mul, norm_div, norm_monomial_eq_absMonomial, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hMom' β)
      (div_nonneg (absMonomial_nonneg' w β) (Nat.cast_nonneg _))
private theorem logarithmRecoversCumulant_of_log
    (hTup : TupleLogMGF.TupleMGFAndLogTheorem)
    (hHol : ComplexVariables.HolomorphicFacts.StandardFacts)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hn : 1 ≤ n) (hX : ∀ i, IsBoundedRealRV (X i))
    (V : Set (ComplexCoordinates n)) (G : ComplexCoordinates n → ℂ) (hV : IsOpen V)
    (hV0 : (0 : ComplexCoordinates n) ∈ V) (hG : IsHolomorphicScalar V G)
    (hGexp : ∀ w ∈ V, Complex.exp (G w) = tupleMomentGeneratingFunction μ X w) (hG0 : G 0 = 0) :
    LogarithmRecoversCumulant μ X V G := by
  obtain ⟨-, hK, -, -, -⟩ := hTup Ω μ n X hn hX
  have hOpen : IsOpen (V ∩ logDomain μ X) := hV.inter hK.isOpen
  have hZero : (0 : ComplexCoordinates n) ∈ V ∩ logDomain μ X := ⟨hV0, hK.zero_mem⟩
  obtain ⟨-, -, -, -, -, hComp, hConst, hExpEq⟩ := hHol n hn (V ∩ logDomain μ X) hOpen
  have hCC := hComp (V ∩ logDomain μ X) hOpen 0 hZero
  have hSub : connectedComponentIn (V ∩ logDomain μ X) 0 ⊆ V ∩ logDomain μ X :=
    connectedComponentIn_subset _ _
  have hMem : (0 : ComplexCoordinates n) ∈ connectedComponentIn (V ∩ logDomain μ X) 0 :=
    mem_connectedComponentIn hZero
  have hDiffCont : ContinuousOn (fun w => G w - logMomentGeneratingFunction μ X w)
      (connectedComponentIn (V ∩ logDomain μ X) 0) :=
    ((IsHolomorphicScalar.continuousOn' hG).mono (hSub.trans inter_subset_left)).sub
      ((IsHolomorphicScalar.continuousOn' hK.holomorphic).mono (hSub.trans inter_subset_right))
  have hDiffVal : ∀ w ∈ connectedComponentIn (V ∩ logDomain μ X) 0,
      G w - logMomentGeneratingFunction μ X w ∈ ComplexVariables.twoPiIMultiples := fun w hw =>
    hExpEq _ (by
      rw [Complex.exp_sub, hGexp w (hSub hw).1, hK.exp_log w (hSub hw).2,
        div_self (hK.mgf_ne_zero w (hSub hw).2)])
  obtain ⟨k, hk⟩ := (hConst _ hCC.1 hCC.2).2 _ hDiffCont hDiffVal
  have hk0 : k = 0 := by
    have h := hk 0 hMem
    rw [hG0, hK.apply_zero, sub_zero] at h
    exact h.symm
  have hAgree : ∀ w ∈ connectedComponentIn (V ∩ logDomain μ X) 0,
      G w = logMomentGeneratingFunction μ X w := fun w hw =>
    sub_eq_zero.1 ((hk w hw).trans hk0)
  obtain ⟨hDeriv, -⟩ := hHol n hn V hV
  obtain ⟨-, -, hPartial, -, -, -, -, hRestr⟩ := hDeriv G hG
  refine ⟨hAgree, (hPartial Finset.univ).1, ?_⟩
  have h := (hRestr _ hCC.1 (hSub.trans inter_subset_left) (logMomentGeneratingFunction μ X)
    (fun w hw => (hAgree w hw).symm)).2 Finset.univ hMem
  rw [ComplexVariables.mixedPartialAtOrigin, ← h, hK.mixedCumulant_eq]
theorem holomorphicLogsOfMomentGeneratingFunction_holds
    (hTup : TupleLogMGF.TupleMGFAndLogTheorem)
    (hSer : ExponentialMomentSeriesExpansion)
    (hHol : ComplexVariables.HolomorphicFacts.StandardFacts) :
    HolomorphicLogsOfMomentGeneratingFunction := by
  intro Ω _ μ _ n X hn hX
  refine ⟨⟨norm_mgf_sub_one_le hSer μ X hn hX, fun w hw => ?_⟩,
    fun V G hV hV0 hG hGexp hG0 =>
      logarithmRecoversCumulant_of_log hTup hHol μ X hn hX V G hV hV0 hG hGexp hG0⟩
  have hTwo : Real.exp (weightedModulusSum X w) < 2 := by
    have h := Real.exp_lt_exp.2 (show weightedModulusSum X w < Real.log 2 from hw)
    rwa [Real.exp_log (by norm_num)] at h
  have h := norm_mgf_sub_one_le hSer μ X hn hX w
  change ‖tupleMomentGeneratingFunction μ X w - 1‖ < 1
  linarith
end YangMills.Construction.Cumulants.HolomorphicLog

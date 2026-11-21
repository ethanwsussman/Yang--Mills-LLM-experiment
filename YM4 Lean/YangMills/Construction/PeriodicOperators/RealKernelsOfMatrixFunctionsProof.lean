import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.RealKernels
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators.Quotients (conjKernel)
open ComplexConjugate
theorem setIntegral_Icc_comp_neg (f : AmbientSpace → ℂ) :
    ∫ k in Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), f (-k) =
      ∫ k in Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), f k := by
  have hm : MeasurableSet (Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi)) := measurableSet_Icc
  rw [← integral_indicator hm, ← integral_indicator hm,
    ← integral_neg_eq_self (Set.indicator _ f) volume]
  congr 1
  funext k
  have hiff : -k ∈ Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi) ↔
      k ∈ Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi) := by
    simp only [mem_Icc, Pi.le_def, Pi.neg_apply]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun i => by linarith [h₂ i], fun i => by linarith [h₁ i]⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun i => by linarith [h₂ i], fun i => by linarith [h₁ i]⟩
  by_cases h : k ∈ Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi)
  · rw [indicator_of_mem h, indicator_of_mem (hiff.2 h)]
  · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hiff.1 h'))]
theorem toComplexVec_mem_realDualPoints (k : AmbientSpace) : toComplexVec k ∈ realDualPoints := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.toComplexVec_mem_realDualPoints <;> assumption
theorem conj_matFunIntegrand {I I' : PeriodicData} {A : (Fin 4 → ℂ) → QuotHom I I'}
    (hbar : ∀ k ∈ realDualPoints, conjKernel (linearMapEntry (A k)) = linearMapEntry (A (-star k)))
    (j : I'.Carrier) (i : I.Carrier) (k : AmbientSpace) :
    conj (matFunIntegrand I I' A j i k) = matFunIntegrand I I' A j i (-k) := by
  have hneg : -star (toComplexVec k) = toComplexVec (-k) := by
    funext μ
    simp [toComplexVec]
  have hentry : conj (carrierEntry (A (toComplexVec k)) j i) =
      carrierEntry (A (toComplexVec (-k))) j i := by
    have h := congrFun (congrFun (hbar _ (toComplexVec_mem_realDualPoints k))
      (I'.mkQuot 1 j)) (I.mkQuot 1 i)
    rw [hneg] at h
    exact h
  have hexp : conj (Complex.exp (-Complex.I *
        bilinDot (toComplexVec k) (toComplexVec (I.pos i - I'.pos j)))) =
      Complex.exp (-Complex.I *
        bilinDot (toComplexVec (-k)) (toComplexVec (I.pos i - I'.pos j))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [bilinDot, toComplexVec, map_sum]
  unfold matFunIntegrand
  rw [map_mul, hentry, hexp]
theorem claim_holds : Claim := by
  intro I I' _ _ A _ hbar j i
  have hconj : conj (matFunKernel I I' A j i) = matFunKernel I I' A j i := by
    unfold matFunKernel torusAverage
    rw [map_mul, Complex.conj_ofReal, ← integral_conj]
    congr 1
    rw [← setIntegral_Icc_comp_neg (matFunIntegrand I I' A j i)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    exact conj_matFunIntegrand hbar j i k
  exact Complex.conj_eq_iff_im.1 hconj
end YangMills.Construction.PeriodicOperators.RealKernels
end

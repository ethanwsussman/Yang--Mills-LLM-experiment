import YangMills.Construction.Matrices.FunctionsAndOperatorsOfSeveralVariablesOnG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
section PeterWeylBasis
variable {I : Type} [Finite I]
def IsHilbertSchmidtPW (T : HaarL2 I →L[ℂ] HaarL2 I) : Prop :=
  Summable fun k : PeterWeylIndex I => ‖T (peterWeylVec k)‖ ^ 2
def IsTraceClassPW (T : HaarL2 I →L[ℂ] HaarL2 I) : Prop :=
  ∃ S R : HaarL2 I →L[ℂ] HaarL2 I,
    IsHilbertSchmidtPW S ∧ IsHilbertSchmidtPW R ∧ T = S * R
def TraceSummablePW (T : HaarL2 I →L[ℂ] HaarL2 I) : Prop :=
  Summable fun k : PeterWeylIndex I => ‖peterWeylEntry T k k‖
def tracePW (T : HaarL2 I →L[ℂ] HaarL2 I) : ℂ :=
  ∑' k : PeterWeylIndex I, peterWeylEntry T k k
end PeterWeylBasis
section FiniteDim
variable {𝕜 : Type*} [Field 𝕜]
def linearMapTrace {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (T : V →ₗ[𝕜] V) : 𝕜 :=
  LinearMap.trace 𝕜 V T
end FiniteDim
end YangMills.Construction.SpinHarmonics

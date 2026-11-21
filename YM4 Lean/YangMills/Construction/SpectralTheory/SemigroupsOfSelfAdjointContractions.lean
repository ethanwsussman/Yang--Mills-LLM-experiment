import YangMills.Construction.SpectralTheory.FunctionsOfSelfAdjointOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal
noncomputable section
namespace YangMills.Construction.ContractionSemigroups
open BorelSpectral HilbertSpaceBasics SpectralTheorem SelfAdjointFunctions
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
structure IsSelfAdjointContractionSemigroup (T : ℝ≥0 → K →L[ℂ] K) : Prop where
  semigroup : IsOpSemigroup T
  selfAdjoint : ∀ t, IsSelfAdjoint (T t)
  contraction : ∀ t, IsContraction (T t)
  tendsto_zero : ∀ v, Tendsto (fun t => T t v) (𝓝[>] 0) (𝓝 v)
def semigroupGenerator (T : ℝ≥0 → K →L[ℂ] K) : UnboundedOp K := negLogOp (T 1)
def negLogIoc (y : RealLineSet) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun x => -Real.log x) (y.1 0)
theorem measurable_negLogIoc : Measurable negLogIoc :=
  (Real.measurable_log.neg.indicator measurableSet_Ioc).comp
    ((measurable_pi_apply 0).comp measurable_subtype_coe)
def singletonZero : BorelSubsets RealLineSet := realLineSet ⟨{0}, measurableSet_singleton 0⟩
def ContractionSemigroupTheorem : Prop :=
  ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : ℝ≥0 → K →L[ℂ] K), IsSelfAdjointContractionSemigroup T →
    (IsStronglyCont T ∧
      (∀ t, IsPositiveOp (T t) ∧ IsGE 1 (T t)) ∧
      ∀ t, LinearMap.ker (T t : K →ₗ[ℂ] K) = ⊥) ∧
    ((∀ (n : ℕ) (Y : Set (Fin n → ℝ)) (F : SpectralMeasure Y K) (f : Y → ℝ)
        (hf : Measurable f), (∀ y, f y ∈ Icc (0 : ℝ) 1) →
        T 1 = F.integralOp (fun y => ((f y : ℝ) : ℂ)) →
          F ⟨f ⁻¹' {0}, hf (measurableSet_singleton 0)⟩ = 0 ∧
          ∀ t : ℝ≥0, T t = F.integralOp fun y => ((f y ^ (t : ℝ) : ℝ) : ℂ)) ∧
      ∀ t : ℝ≥0, T t = rpowOp (T 1) t) ∧
    ((∃! A : UnboundedOp K, IsNonnegOp A ∧ ∀ t, T t = expNeg A t) ∧
      IsNonnegOp (semigroupGenerator T) ∧
      (∀ t, T t = expNeg (semigroupGenerator T) t) ∧
      (∀ A : UnboundedOp K, IsNonnegOp A → expNeg A 1 = T 1 → A = semigroupGenerator T) ∧
      spectralMeasure (semigroupGenerator T) =
        pushforwardToLine (spectralMeasure (ofBounded (T 1))) negLogIoc
          measurable_negLogIoc) ∧
    (((opKernel (semigroupGenerator T) : Submodule ℂ K) : Set K) = {v | T 1 v = v} ∧
      {v | T 1 v = v} = {v | ∀ t, T t v = v} ∧
      TendstoStrongly T atTop (spectralMeasure (semigroupGenerator T) singletonZero) ∧
      IsOrthProjOnto (spectralMeasure (semigroupGenerator T) singletonZero)
        (opKernel (semigroupGenerator T) : Set K) ∧
      spectralMeasure (semigroupGenerator T) singletonZero =
        orthProjOnto (opKernel (semigroupGenerator T) : Set K)) ∧
    (∀ B : K →L[ℂ] K, Commute B (T 1) →
        (∀ S, Commute B (spectralMeasure (semigroupGenerator T) S)) ∧ ∀ t, Commute B (T t)) ∧
    ∀ U : K →L[ℂ] K, IsUnitaryOp U → Commute U (T 1) →
      conjByUnitary U (semigroupGenerator T) = semigroupGenerator T
end YangMills.Construction.ContractionSemigroups

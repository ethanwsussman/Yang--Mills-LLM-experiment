import YangMills.Construction.SpectralCalculus.JointSpectralMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate ComplexOrder NNReal ENNReal
noncomputable section
namespace YangMills.Construction.SpectralCalculus
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def fstStrip (B : MeasurableSubtype ℝ≥0) : MeasurableSubtype SpectralPlane :=
  ⟨B.1 ×ˢ univ, B.2.prod MeasurableSet.univ⟩
structure IsBoundedExhaustion (F : SpectralPlane → ℂ) (B : ℕ → MeasurableSubtype SpectralPlane) :
    Prop where
  monotone : Monotone fun n => (B n).1
  iUnion_eq : ⋃ n, (B n).1 = univ
  isBounded : ∀ n, ∃ C : ℝ, ∀ p ∈ (B n).1, ‖F p‖ ≤ C
structure SpectralIntegralProperties [CompleteSpace H] (P : ProjValuedMeasure H) : Prop where
  nonneg : ∀ v (B : MeasurableSubtype SpectralPlane), 0 ≤ P.matrixCoeff v v B.1
  variation_eq : ∀ v (B : MeasurableSubtype SpectralPlane),
    (P.matrixCoeff v v).variation.real B.1 = (P.matrixCoeff v v B.1).re
  mass : ∀ v, P.matrixCoeff v v univ = ((‖v‖ ^ 2 : ℝ) : ℂ)
  conj_symm : ∀ u v, P.matrixCoeff v u = conjMeasure (P.matrixCoeff u v)
  variation_le : ∀ u v, (P.matrixCoeff u v).variation.real univ ≤ ‖u‖ * ‖v‖
  isBoundedSpectralIntegral : ∀ F, IsBoundedMeasurable F →
    P.IsBoundedSpectralIntegral F (P.boundedSpectralIntegral F)
  eq_boundedSpectralIntegral : ∀ F (B : H →L[ℂ] H), IsBoundedMeasurable F →
    P.IsBoundedSpectralIntegral F B → B = P.boundedSpectralIntegral F
  boundedSpectralIntegral_add : ∀ F F', IsBoundedMeasurable F → IsBoundedMeasurable F' →
    P.boundedSpectralIntegral (fun p => F p + F' p) =
      P.boundedSpectralIntegral F + P.boundedSpectralIntegral F'
  boundedSpectralIntegral_smul : ∀ (a : ℂ) F, IsBoundedMeasurable F →
    P.boundedSpectralIntegral (fun p => a * F p) = a • P.boundedSpectralIntegral F
  norm_boundedSpectralIntegral_le : ∀ F, IsBoundedMeasurable F →
    ‖P.boundedSpectralIntegral F‖ ≤ ⨆ p, ‖F p‖
  inner_boundedSpectralIntegral : ∀ F, IsBoundedMeasurable F → ∀ u v,
    inner ℂ (P.boundedSpectralIntegral F u) v =
      inner ℂ u (P.boundedSpectralIntegral (fun p => conj (F p)) v)
  boundedSpectralIntegral_mul : ∀ F F', IsBoundedMeasurable F → IsBoundedMeasurable F' →
    P.boundedSpectralIntegral F * P.boundedSpectralIntegral F' =
      P.boundedSpectralIntegral fun p => F p * F' p
  norm_sq_boundedSpectralIntegral : ∀ F, IsBoundedMeasurable F → ∀ v,
    ((‖P.boundedSpectralIntegral F v‖ ^ 2 : ℝ) : ℂ) =
      complexIntegral (P.matrixCoeff v v) fun p => ((‖F p‖ ^ 2 : ℝ) : ℂ)
  boundedSpectralIntegral_indicator : ∀ B : MeasurableSubtype SpectralPlane,
    P.boundedSpectralIntegral (B.1.indicator fun _ => 1) = P B
  exists_submodule : ∀ F, Measurable F → ∃ D : Submodule ℂ H, (D : Set H) = P.spectralDomain F
  isSeqDense_spectralDomain : ∀ F, Measurable F → IsSeqDense (P.spectralDomain F)
  isSpectralIntegral : ∀ F, Measurable F → P.IsSpectralIntegral F (P.spectralIntegral F)
  eq_spectralIntegral : ∀ F (A : PartialOperator H), Measurable F → P.IsSpectralIntegral F A →
    A = P.spectralIntegral F
  tendsto_boundedSpectralIntegral_indicator : ∀ F (B : ℕ → MeasurableSubtype SpectralPlane),
    Measurable F → IsBoundedExhaustion F B → ∀ v : (P.spectralIntegral F).domain,
      Tendsto (fun n => P.boundedSpectralIntegral ((B n).1.indicator F) (v : H)) atTop
        (𝓝 (P.spectralIntegral F v))
  enorm_sq_spectralIntegral : ∀ F, Measurable F → ∀ v : (P.spectralIntegral F).domain,
    ‖P.spectralIntegral F v‖ₑ ^ 2 = ∫⁻ p, ‖F p‖ₑ ^ 2 ∂(P.matrixCoeff (v : H) (v : H)).variation
  spectralIntegral_of_isBoundedMeasurable : ∀ F, IsBoundedMeasurable F →
    (P.spectralIntegral F).domain = ⊤ ∧
      ∀ v : (P.spectralIntegral F).domain,
        P.spectralIntegral F v = P.boundedSpectralIntegral F (v : H)
  spectralIntegral_add : ∀ F F', Measurable F → Measurable F' → ∀ v
    (hv : v ∈ (P.spectralIntegral F).domain) (hv' : v ∈ (P.spectralIntegral F').domain),
    ∃ hs : v ∈ (P.spectralIntegral fun p => F p + F' p).domain,
      (P.spectralIntegral fun p => F p + F' p) ⟨v, hs⟩ =
        P.spectralIntegral F ⟨v, hv⟩ + P.spectralIntegral F' ⟨v, hv'⟩
  isSelfAdjoint_spectralIntegral : ∀ F, Measurable F → (∀ p, (F p).im = 0) →
    IsSelfAdjointPartial (P.spectralIntegral F)
  isPositive_spectralIntegral : ∀ F, Measurable F → (∀ p, 0 ≤ F p) →
    IsPositivePartial (P.spectralIntegral F)
def semigroupDiffQuot (T : ℝ≥0 → H →L[ℂ] H) (v : H) (t : ℝ≥0) : H :=
  (((t : ℝ)⁻¹ : ℝ) : ℂ) • (v - T t v)
def groupDiffQuot (U : ℝ → H →L[ℂ] H) (v : H) (s : ℝ) : H :=
  (Complex.I * (s : ℂ))⁻¹ • (U s v - v)
structure GeneratorProperties [CompleteSpace H] (T : ℝ≥0 → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H)
    (P : ProjValuedMeasure H) : Prop where
  isSelfAdjoint_energy : IsSelfAdjointPartial (P.spectralIntegral coordFst)
  isSelfAdjoint_momentum : IsSelfAdjointPartial (P.spectralIntegral coordSnd)
  isPositive_energy : IsPositivePartial (P.spectralIntegral coordFst)
  mem_domain_energy_iff : ∀ v, v ∈ (P.spectralIntegral coordFst).domain ↔
    ∃ w, Tendsto (semigroupDiffQuot T v) (𝓝[>] 0) (𝓝 w)
  tendsto_energy : ∀ v : (P.spectralIntegral coordFst).domain,
    Tendsto (semigroupDiffQuot T (v : H)) (𝓝[>] 0) (𝓝 (P.spectralIntegral coordFst v))
  mem_domain_momentum_iff : ∀ v, v ∈ (P.spectralIntegral coordSnd).domain ↔
    ∃ w, Tendsto (groupDiffQuot U v) (𝓝[≠] 0) (𝓝 w)
  tendsto_momentum : ∀ v : (P.spectralIntegral coordSnd).domain,
    Tendsto (groupDiffQuot U (v : H)) (𝓝[≠] 0) (𝓝 (P.spectralIntegral coordSnd v))
  commute_strips : ∀ (B : MeasurableSubtype ℝ≥0) (B' : MeasurableSubtype ℝ),
    Commute (P (fstStrip B)) (P (cylinderSet B'))
end
def SpectralIntegralTheorem : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    (∀ P : ProjValuedMeasure H, SpectralIntegralProperties P) ∧
    ∀ (T : ℝ≥0 → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H) (P : ProjValuedMeasure H),
      IsCommutingSemigroupGroup T U → IsJointSpectralPVM T U P → GeneratorProperties T U P
end YangMills.Construction.SpectralCalculus
end

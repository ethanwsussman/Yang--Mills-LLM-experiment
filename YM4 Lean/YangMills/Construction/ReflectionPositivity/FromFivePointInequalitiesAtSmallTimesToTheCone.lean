import YangMills.Construction.ReflectionPositivity.HamiltonianAndMomentaFromThePairMeasures
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ComplexOrder InnerProductSpace NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.SmallTimeCone
open YangMills.Construction.ReflectionPositivity.TupleForm YangMills.Construction.SpectralTheory YangMills.Construction.ReflectionPositivity.ContractionFunctionals YangMills.Construction.ReflectionPositivity.PairMeasureOperators
open YangMills.Construction.SeparatedTuples (TupleFunctional)
open YangMills.Construction.ReflectionPositivity.Reconstruction (PhysicalSpace fivePointCombination)
open YangMills.Construction.HilbertSpaceBasics (IsPosSemidef ofBounded)
def FivePointNonnegAt (σ : TupleFunctional) (i : Fin 3) (t : ℝ≥0) : Prop :=
  ∀ Z : PositiveSpan, 0 ≤ fivePointCombination σ Z t i
section Objects
variable (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ)) (i : Fin 3)
def HeatMomentumInequalityAt (t : ℝ≥0) : Prop :=
  ∃ (F G : ProjectionMeasure 1 (PhysicalSpace σ h))
    (S U V : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h),
    HasSpectralResolution (pairHamiltonian σ h) F ∧ F.IsConcentratedOn nonnegReals ∧
      HasSpectralResolution (pairMomentum σ h i) G ∧
      ofBounded S = F.expNegMulOp t ∧ ofBounded U = G.expIMulOp t ∧
      ofBounded V = G.expIMulOp (-(t : ℝ)) ∧
      LoewnerGe ((1 - S) ^ 2) (S * ((2 : ℂ) • 1 - U - V))
def DomainInclusion : Prop :=
  (pairHamiltonian σ h).domain ≤ (pairMomentum σ h i).domain
def FormBound : Prop :=
  ∃ G : ProjectionMeasure 1 (PhysicalSpace σ h),
    HasSpectralResolution (pairMomentum σ h i) G ∧
      ∀ ψ : (pairHamiltonian σ h).domain, ∃ hψ : (ψ : PhysicalSpace σ h) ∈ G.absValueOp.domain,
        ⟪(ψ : PhysicalSpace σ h), G.absValueOp ⟨ψ, hψ⟩⟫_ℂ ≤
          ⟪(ψ : PhysicalSpace σ h), pairHamiltonian σ h ψ⟫_ℂ
def GroundStateInvariance : Prop :=
  ∃ G : ProjectionMeasure 1 (PhysicalSpace σ h),
    HasSpectralResolution (pairMomentum σ h i) G ∧
      ∀ ψ : (pairHamiltonian σ h).domain, pairHamiltonian σ h ψ = 0 → ∀ u : ℝ,
        ∃ hψ : (ψ : PhysicalSpace σ h) ∈ (G.expIMulOp u).domain,
          G.expIMulOp u ⟨ψ, hψ⟩ = ψ
end Objects
def SmallTimeConeTheorem : Prop :=
  ∀ σ : TupleFunctional, IsAdmissible σ → ∃ h : IsPosSemidef (reflectionForm σ), ∀ i : Fin 3,
    (∀ t : ℕ → ℝ≥0, (∀ k, 0 < t k) → Antitone t → Tendsto t atTop (𝓝 0) →
      (∀ k, FivePointNonnegAt σ i (t k)) →
      (∀ k, HeatMomentumInequalityAt σ h i (t k)) ∧ HamiltonianDominatesMomentum σ h i ∧
        DomainInclusion σ h i ∧ FormBound σ h i ∧ GroundStateInvariance σ h i) ∧
    ∀ t : ℝ≥0, 0 < t → FivePointNonnegAt σ i t → HeatMomentumInequalityAt σ h i t
end YangMills.Construction.ReflectionPositivity.SmallTimeCone

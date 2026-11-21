import YangMills.Construction.EnergyMomentum.JointSpectralMeasure
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open scoped NNReal
noncomputable section
namespace YangMills.Construction.EnergyMomentum.Generators
open YangMills.Construction.EnergyMomentum YangMills.Construction.EuclideanSpectral YangMills.Construction.EnergyMomentum.JointSpectral
def zeroEnergySet : BorelSubsets EnergyMomentumSpace :=
  ⟨({0} : Set ℝ≥0) ×ˢ (univ : Set Momentum3), (measurableSet_singleton 0).prod MeasurableSet.univ⟩
def zeroMomentumSet (i : Fin 3) : BorelSubsets EnergyMomentumSpace :=
  ⟨{p | p.2 i = 0}, (isClosed_eq (by fun_prop) continuous_const).measurableSet⟩
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
def hamiltonian (T : ℝ≥0 → 𝓗 →L[ℂ] 𝓗) (U : Momentum3 → 𝓗 →L[ℂ] 𝓗) : 𝓗 →ₗ.[ℂ] 𝓗 :=
  (jointSpectralMeasure T U).calculusOperator coordEnergy
def momentumOp (T : ℝ≥0 → 𝓗 →L[ℂ] 𝓗) (U : Momentum3 → 𝓗 →L[ℂ] 𝓗) (i : Fin 3) :
    𝓗 →ₗ.[ℂ] 𝓗 :=
  (jointSpectralMeasure T U).calculusOperator (coordMomentum i)
def energyDiffQuot (T : ℝ≥0 → 𝓗 →L[ℂ] 𝓗) (x : 𝓗) (t : ℝ≥0) : 𝓗 :=
  (((t : ℝ)⁻¹ : ℝ) : ℂ) • (x - T t x)
def momentumDiffQuot (U : Momentum3 → 𝓗 →L[ℂ] 𝓗) (i : Fin 3) (x : 𝓗) (s : ℝ) : 𝓗 :=
  (Complex.I * (s : ℂ))⁻¹ • (U (s • EuclideanSpace.single i (1 : ℝ)) x - x)
structure GeneratorsSelfAdjoint (T : ℝ≥0 → 𝓗 →L[ℂ] 𝓗) (U : Momentum3 → 𝓗 →L[ℂ] 𝓗) : Prop where
  hamiltonian_selfAdjoint : IsSelfAdjointPartial (hamiltonian T U)
  momentumOp_selfAdjoint : ∀ i, IsSelfAdjointPartial (momentumOp T U i)
  hamiltonian_nonneg : IsNonnegPartial (hamiltonian T U)
structure HamiltonianGenerates (T : ℝ≥0 → 𝓗 →L[ℂ] 𝓗) (U : Momentum3 → 𝓗 →L[ℂ] 𝓗) :
    Prop where
  mem_domain_iff : ∀ x, x ∈ (hamiltonian T U).domain ↔
    ∃ y, Tendsto (energyDiffQuot T x) (𝓝[>] 0) (𝓝 y)
  tendsto_apply : ∀ x : (hamiltonian T U).domain,
    Tendsto (energyDiffQuot T (x : 𝓗)) (𝓝[>] 0) (𝓝 (hamiltonian T U x))
structure MomentumGenerates (T : ℝ≥0 → 𝓗 →L[ℂ] 𝓗) (U : Momentum3 → 𝓗 →L[ℂ] 𝓗)
    (i : Fin 3) : Prop where
  mem_domain_iff : ∀ x, x ∈ (momentumOp T U i).domain ↔
    ∃ y, Tendsto (momentumDiffQuot U i x) (𝓝[≠] 0) (𝓝 y)
  tendsto_apply : ∀ x : (momentumOp T U i).domain,
    Tendsto (momentumDiffQuot U i (x : 𝓗)) (𝓝[≠] 0) (𝓝 (momentumOp T U i x))
structure HamiltonianKernel (T : ℝ≥0 → 𝓗 →L[ℂ] 𝓗) (U : Momentum3 → 𝓗 →L[ℂ] 𝓗) : Prop where
  tfae : ∀ x : 𝓗, List.TFAE
    [x ∈ pmapKernel (hamiltonian T U),
      ∀ t, T t x = x,
      MeasureIsCarriedBy ((jointSpectralMeasure T U).diagMeasure x) zeroEnergySet,
      jointSpectralMeasure T U zeroEnergySet x = x]
  isOrthProjection : IsOrthProjection (jointSpectralMeasure T U zeroEnergySet)
  fixedSet_eq : fixedSet (jointSpectralMeasure T U zeroEnergySet) =
    pmapKernel (hamiltonian T U)
  tendstoStrongly : TendstoStrongly atTop T (jointSpectralMeasure T U zeroEnergySet)
def MomentumKernel (T : ℝ≥0 → 𝓗 →L[ℂ] 𝓗) (U : Momentum3 → 𝓗 →L[ℂ] 𝓗) (i : Fin 3) : Prop :=
  ∀ x : 𝓗, List.TFAE
    [x ∈ pmapKernel (momentumOp T U i),
      ∀ s : ℝ, U (s • EuclideanSpace.single i (1 : ℝ)) x = x,
      MeasureIsCarriedBy ((jointSpectralMeasure T U).diagMeasure x) (zeroMomentumSet i)]
def GeneratorsTheorem : Prop :=
  ∀ (𝓗 : Type) [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
    (T : ℝ≥0 → 𝓗 →L[ℂ] 𝓗) (U : Momentum3 → 𝓗 →L[ℂ] 𝓗), IsContractionSemigroupWithUnitaryGroup T U →
    GeneratorsSelfAdjoint T U ∧ HamiltonianGenerates T U ∧
      (∀ i, MomentumGenerates T U i) ∧ HamiltonianKernel T U ∧
      ∀ i, MomentumKernel T U i
end YangMills.Construction.EnergyMomentum.Generators

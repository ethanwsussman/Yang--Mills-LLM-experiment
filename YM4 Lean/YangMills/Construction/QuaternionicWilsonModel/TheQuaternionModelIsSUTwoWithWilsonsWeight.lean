import YangMills.Construction.ClusterExpansionOfAStep.BottomOfTheChainIsWilsonsMeasure
import YangMills.Construction.ClusterExpansionOfAStep.WilsonsMeasureOnTheFieldsOfATorus
import YangMills.Construction.FourPointCondition.ObservablesOfTheExpansionCoincide
import YangMills.Construction.WindowOfTheParameters.FlowOfTheTotalDensities
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction.QuaternionModel
open BlockAverages (UnitQuaternion)
open ClusterExpansionOfAStep TorusFields TorusLumps WeightedResponses
open SoftAverages (quaternionToMatrix)
structure UnitQuaternionMatrixCorrespondence : Prop where
  toMatrix_eq : ∀ u : UnitQuaternion, (((unitQuaternionEquivSpecialUnitary : UnitQuaternion ≃ₜ* Matrix.specialUnitaryGroup (Fin 2) ℂ) u :
    Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrices.ComplexMatrix2) = quaternionToMatrix (u : ℍ[ℝ])
  map_haar : haarUnit.map unitQuaternionEquivSpecialUnitary = Matrices.ComplexMatrix2.haarProb
  energy_eq : ∀ u : UnitQuaternion, 1 - (u : ℍ[ℝ]).re =
    1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (unitQuaternionEquivSpecialUnitary u : Matrices.ComplexMatrix2)).re
  trace_im_eq_zero : ∀ u : UnitQuaternion,
    (Matrices.ComplexMatrix2.fullTrace (unitQuaternionEquivSpecialUnitary u : Matrices.ComplexMatrix2)).im = 0
  operatorNorm_eq : ∀ q : ℍ[ℝ], Matrices.ComplexMatrix2.operatorNorm (quaternionToMatrix q) = ‖q‖
def plaquetteOfOriented (L m K : ℕ) {n : ℕ} (q : OrientedPlaquette n) : PeriodicLattice.Plaquette L m (K : ℤ) :=
  ⟨periodicLatticeSite L m (K : ℤ) q.1.1, q.1.2.1, q.1.2.2, q.2⟩
structure CubicTorusEmbedsInLattice (L m K n : ℕ) [NeZero n] : Prop where
  fields : TorusFieldsAreGaugeFields L m K n
  site_coe : ∀ (x : TorusSite n) (μ : Fin 4),
    ((periodicLatticeSite L m (K : ℤ) x : PeriodicLattice.Site L m (K : ℤ)) : PeriodicLattice.FourTorus L m) μ =
      ((((x μ).val : ℝ) * PeriodicLattice.meshSize L (K : ℤ) : ℝ) : AddCircle (PeriodicLattice.torusSide L m))
  site_add_unitStep : ∀ (x : TorusSite n) (μ : Fin 4),
    periodicLatticeSite L m (K : ℤ) (x + unitStep n μ) =
      periodicLatticeSite L m (K : ℤ) x + PeriodicLattice.unitStep L m (K : ℤ) μ
  isPositivelyOriented_iff : ∀ b : PeriodicLattice.Bond L m (K : ℤ), b.IsPositivelyOriented ↔
    ∃ (x : TorusSite n) (μ : Fin 4), b = PeriodicLattice.Bond.forwardFrom (periodicLatticeSite L m (K : ℤ) x) μ
  forwardFrom_injective : Function.Injective fun p : TorusSite n × Fin 4 =>
    PeriodicLattice.Bond.forwardFrom (periodicLatticeSite L m (K : ℤ) p.1) p.2
  xor_opposite : ∀ b : PeriodicLattice.Bond L m (K : ℤ), Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  opposite_eq : ∀ (W : TorusField n) (x : TorusSite n) (μ : Fin 4),
    gaugeFieldOfTorusField L m (K : ℤ) W
        (PeriodicLattice.Bond.forwardFrom (periodicLatticeSite L m (K : ℤ) x) μ).opposite =
      quaternionToMatrix (((W x μ)⁻¹ : UnitQuaternion) : ℍ[ℝ])
  isClosedEmbedding : Topology.IsClosedEmbedding (gaugeFieldOfTorusField (n := n) L m (K : ℤ))
  plaquette_bijective : Function.Bijective (plaquetteOfOriented L m K (n := n))
  barycenter_eq : ∀ (q : OrientedPlaquette n) (i : Fin 4), (plaquetteOfOriented L m K q).barycenter i =
    (((((q.1.1 i).val : ℝ) + (if i = q.1.2.1 then 1 / 2 else 0) + (if i = q.1.2.2 then 1 / 2 else 0)) *
      PeriodicLattice.meshSize L (K : ℤ) : ℝ) : AddCircle (PeriodicLattice.torusSide L m))
  plaquetteCost_eq : ∀ (W : TorusField n) (q : OrientedPlaquette n),
    PeriodicLattice.plaquetteCost (gaugeFieldOfTorusField L m (K : ℤ) W) (plaquetteOfOriented L m K q) =
      plaquetteEnergy W q.1.1 q.1.2.1 q.1.2.2
  smearedObservable_eq : ∀ (f : PeriodicLattice.FourTorus L m → ℝ) (W : TorusField n),
    PeriodicLattice.smearedObservable f (gaugeFieldOfTorusField L m (K : ℤ) W) =
      ∑ q : OrientedPlaquette n, plaquetteEnergy W q.1.1 q.1.2.1 q.1.2.2 * f (plaquetteOfOriented L m K q).barycenter
  partition_pos : ∀ β : ℝ, 0 < ∫ W, wilsonWeight β n W ∂(fieldHaar n)
  wilsonLaw_eq : ∀ β : ℝ, wilsonLaw β n = (fieldHaar n).withDensity fun W =>
    ENNReal.ofReal (wilsonWeight β n W / ∫ W', wilsonWeight β n W' ∂(fieldHaar n))
  wilsonLaw_isProbability : ∀ β : ℝ, IsProbabilityMeasure (wilsonLaw β n)
  wilsonGibbs_isProbability : ∀ β : ℝ, IsProbabilityMeasure (PeriodicLattice.wilsonGibbsMeasure L m K β)
  wilsonGibbs_eq_map : ∀ β : ℝ, PeriodicLattice.wilsonGibbsMeasure L m K β =
    (wilsonLaw β n).map (gaugeFieldOfTorusField L m (K : ℤ))
def quaternionModelIsWilsonSU2Statement : Prop :=
  UnitQuaternionMatrixCorrespondence ∧
    (∀ (L m K n : ℕ) [NeZero n], n = 2 * L ^ (m + K) → 2 < n → CubicTorusEmbedsInLattice L m K n) ∧
    (∀ (L m K : ℕ), 2 ≤ L → 1 ≤ m → fineSide L K (2 * L ^ m) = 2 * L ^ (m + K) ∧ 2 < 2 * L ^ (m + K)) ∧
    (∀ (ℓ : TorusLumps.StepParameters) (β : ℝ), TotalDensityFlow.coupling ℓ β 0 = β ∧
      (TotalDensityFlow.flowData ℓ β 0).2 = wilsonWeight β ∧
      ∀ t : ℕ, (TotalDensityFlow.flowData ℓ β t).2 = chainFunctional ℓ β (TotalDensityFlow.coupling ℓ β) t) ∧
    FourPointCondition.torusUrsellEqWeightedCurvatureStatement ∧
    ClusterExpansionOfAStep.bottomChainLawIsWilsonGibbsStatement
end YangMills.Construction.QuaternionModel
end

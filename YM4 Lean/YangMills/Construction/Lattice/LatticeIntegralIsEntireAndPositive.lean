import YangMills.Construction.Lattice.PlaquetteWeightsAndTheLatticeIntegral
import YangMills.Construction.Lattice.SourcedPartitionFunctionOfALattice
import YangMills.Construction.Lattice.SourcesAndGeneratingFunction
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PartitionFunctionAnalyticity
open YangMills.Construction.PeriodicLattice YangMills.Construction.SeveralComplexVariables
def IsRealVector {I : Type*} (c : I → ℂ) : Prop := ∀ q, (c q).im = 0
def sourcedPartitionFunctionInArgs (L m J : ℕ) {n : ℕ} (f : Fin n → FourTorus L m → ℝ)
    (x : Fin 2 ⊕ Fin n → ℂ) : ℂ :=
  sourcedPartitionFunction L m J (x (.inl 0))
    fun y => x (.inl 1) + complexSource f (fun i => x (.inr i)) y
def PartitionFunctionEntireAndBoundedBelow (L m J : ℕ) : Prop :=
  IsEntire (latticeGaugeIntegral : (Plaquette L m (J : ℤ) → ℂ) → ℂ) ∧
    (∀ c : Plaquette L m (J : ℤ) → ℂ, IsRealVector c →
      ∃ t : ℝ, latticeGaugeIntegral c = t ∧ Real.exp (-2 * weightL1Norm c) ≤ t ∧
        0 < Real.exp (-2 * weightL1Norm c)) ∧
    IsOpen (partitionFunctionNonvanishing L m (J : ℤ)) ∧
    ∀ c : Plaquette L m (J : ℤ) → ℂ, IsRealVector c → c ∈ partitionFunctionNonvanishing L m (J : ℤ)
def BarycenterWeightsRepresent (L m J : ℕ) : Prop :=
  IsLinearMap ℂ (weightsAtBarycenters : (FourTorus L m → ℂ) → Plaquette L m (J : ℤ) → ℂ) ∧
    (∀ φ : FourTorus L m → ℂ, IsRealVector φ →
      IsRealVector (weightsAtBarycenters φ : Plaquette L m (J : ℤ) → ℂ)) ∧
    (weightsAtBarycenters (fun _ => 1) : Plaquette L m (J : ℤ) → ℂ) = constantOneWeights ∧
    (∀ (φ : FourTorus L m → ℂ) (U : CompactGaugeField L m (J : ℤ)),
      barycenterWeightedEnergy φ U.1 = plaquetteWeightedEnergy (weightsAtBarycenters φ) U.1) ∧
    ∀ (β : ℂ) (w : FourTorus L m → ℂ), torusSupNorm w ≠ ⊤ →
      sourcedPartitionFunction L m J β w =
        latticeGaugeIntegral (β • constantOneWeights - weightsAtBarycenters w :
          Plaquette L m (J : ℤ) → ℂ)
def SourcedEntireAndPositive (L m J : ℕ) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ f : Fin n → FourTorus L m → ℝ, (∀ i, torusSupNorm (f i) ≠ ⊤) →
    IsEntire (sourcedPartitionFunctionInArgs L m J f) ∧
      ∀ x : Fin 2 ⊕ Fin n → ℂ, IsRealVector x →
        ∃ t : ℝ, 0 < t ∧ sourcedPartitionFunctionInArgs L m J f x = t
def ConstantSourceShiftsCoupling (L m J : ℕ) : Prop :=
  ∀ (β c : ℂ) (w : FourTorus L m → ℂ), torusSupNorm w ≠ ⊤ →
    sourcedPartitionFunction L m J β (fun y => c + w y) =
      sourcedPartitionFunction L m J (β - c) w
def NonvanishingSetOpenContainsReals (L m J : ℕ) : Prop :=
  nonvanishingCouplings L m J =
      {β : ℂ | latticeGaugeIntegral (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) ≠ 0} ∧
    IsOpen (nonvanishingCouplings L m J) ∧
    ∀ t : ℝ, (t : ℂ) ∈ nonvanishingCouplings L m J
def SourcesBoundedAndComplexCombinations (L m : ℕ) : Prop :=
  (∀ f : FourTorus L m → ℝ, torusLipConst f ≠ ⊤ → torusSupNorm f ≠ ⊤) ∧
    (∀ f : FourTorus L m → ℂ, torusLipConst f ≠ ⊤ → torusSupNorm f ≠ ⊤) ∧
    (∀ w : FourTorus L m → ℂ, IsLipschitzSource w → torusSupNorm w ≠ ⊤) ∧
    ∀ w : FourTorus L m → ℂ, IsLipschitzSource w ↔
      ∃ n : ℕ, 1 ≤ n ∧ ∃ f : Fin n → FourTorus L m → ℝ, (∀ i, torusLipConst (f i) ≠ ⊤) ∧
        ∃ z : Fin n → ℂ, w = complexSource f z
def Statement : Prop :=
  ∀ L m J : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    PartitionFunctionEntireAndBoundedBelow L m J ∧ BarycenterWeightsRepresent L m J ∧
      SourcedEntireAndPositive L m J ∧ ConstantSourceShiftsCoupling L m J ∧
      NonvanishingSetOpenContainsReals L m J ∧ SourcesBoundedAndComplexCombinations L m
end YangMills.Construction.PartitionFunctionAnalyticity

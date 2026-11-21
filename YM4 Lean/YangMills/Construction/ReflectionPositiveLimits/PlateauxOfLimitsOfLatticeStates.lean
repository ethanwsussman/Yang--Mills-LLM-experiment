import YangMills.Construction.InfiniteLattice.ErgodicPhases
import YangMills.Construction.Lattice.LatticesCubesDoubleBlocksAndLocalityOfAveragesProof
import YangMills.Construction.ReflectionPositiveLimits.LAdicNumbersAndLAdicMirrors
import YangMills.Construction.ReflectionPositiveLimits.RepresentativesOfSeparatedTuples
import YangMills.Construction.ReflectionPositiveLimits.VacuumErgodicityAndClusteringInTime
import YangMills.Construction.ReflectionPositivity.PicturesCubeVectorsAndReflectionSizesAtASpacing
import YangMills.Construction.ReflectionPositivity.RateConstantAndRateFunction
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
open InfiniteLattice (condExpShiftInvariant scaledCube regionObservables plateauPairing)
open DirectionPictures (scaledCubeReflectionSize)
open SmearingFilter (spectralRateConst spectralRateFn)
open EuclidIsometry (translate)
open TorusMetric (euclidNormVec)
open Conventions (IsAdmissibleBlockingFactor)
def reflectionGroupIsometry (g : reflectionGroup) : EuclidIsometry where
  toFun := g.1
  preserves_dist x y := by
    obtain ⟨s, hs⟩ := (mem_reflectionGroup_iff g.1).1 g.2
    have hsq : ∀ i, ((s i : ℤ) : ℝ) ^ 2 = 1 := fun i => by
      rw [sq]
      exact intUnit_cast_mul_self (s i)
    simp only [hs, euclidNormVec, Pi.sub_apply, flipSigns_apply, ← mul_sub, mul_pow, hsq, one_mul]
def axisReflectionElem (i : Fin 4) : reflectionGroup :=
  ⟨axisReflection i, Subgroup.subset_closure (Set.mem_range_self i)⟩
def mirrorTuple (i : Fin 4) (g : reflectionGroup) (X : Tuple) : Tuple :=
  push (reflectionGroupIsometry (axisReflectionElem i)) (push (reflectionGroupIsometry g) X)
def translatedTuple (w : ℝ) (i : Fin 4) (g : reflectionGroup) (X : Tuple) : Tuple :=
  push (translate ((2 * w) • PeriodicLattice.coordVec i)) (push (reflectionGroupIsometry g) X)
def mirrorCorrelation (σ : Tuple → ℝ) (w : ℝ) (X : Tuple) (p : Fin 4 × reflectionGroup) : ℝ :=
  open Classical in
  if h : Concatenable (mirrorTuple p.1 p.2 X) (translatedTuple w p.1 p.2 X) then
    σ (concat _ _ h)
  else 0
def functionalSize (σ : Tuple → ℝ) (w : ℝ) (X : Tuple) : ℝ :=
  sSup (Set.range (mirrorCorrelation σ w X))
theorem isGreatest_functionalSize (σ : Tuple → ℝ) (w : ℝ) (X : Tuple) :
    IsGreatest (Set.range (mirrorCorrelation σ w X)) (functionalSize σ w X) := by
  have : Finite reflectionGroup :=
    Nat.finite_of_card_ne_zero (by rw [card_reflectionGroup]; norm_num)
  exact (Set.finite_range _).isCompact.isGreatest_sSup (Set.range_nonempty _)
theorem meshSize_pos {L : ℕ} (hL : IsAdmissibleBlockingFactor L) (j : ℤ) :
    0 < PeriodicLattice.meshSize L j := by apply _root_.YangMills.Construction.PeriodicLattice.GeometryAndLocalityOfBlockAverages.meshSize_pos <;> assumption
namespace LatticeSequence
variable {L : ℕ} (A : LatticeSequence L)
def plateauAt (j : ℕ+) (X Y : Tuple) : ℂ :=
  plateauPairing (A.measure j).1 (A.complexRep j X) (A.complexRep j Y)
def condExpProductAt (j : ℕ+) (X Y : Tuple) : ℂ :=
  ∫ U, condExpShiftInvariant (A.measure j).1 (A.complexRep j X) U *
    condExpShiftInvariant (A.measure j).1 (A.complexRep j Y) U ∂(A.measure j).1
def IsPlateauLimit (X Y : Tuple) (l : ℝ) : Prop :=
  Tendsto (fun j => A.plateauAt j X Y) atTop (𝓝 (l : ℂ))
def limitPlateau (X Y : Tuple) : ℝ :=
  Classical.epsilon (A.IsPlateauLimit X Y)
def cubeIndex (w : ℝ) (j : ℕ+) : ℕ+ :=
  Nat.toPNat' ⌊w / A.mesh j⌋₊
def InCubeAt (w : ℝ) (j : ℕ+) (X : Tuple) : Prop :=
  ((A.cubeIndex w j : ℕ) : ℝ) * A.mesh j = w ∧
    A.complexRep j X ∈ regionObservables (A.mesh j) (scaledCube (A.mesh j) (A.cubeIndex w j))
def sizeAt (hL : IsAdmissibleBlockingFactor L) (w : ℝ) (j : ℕ+) (X : Tuple) : ℝ :=
  scaledCubeReflectionSize (meshSize_pos hL _) (A.measure j).1
    (A.cubeIndex w j) (A.complexRep j X)
end LatticeSequence
namespace LimitPlateaux
open TimeClustering
structure SizeAndPlateauLimits {L : ℕ} (hL : IsAdmissibleBlockingFactor L) (A : LatticeSequence L)
    (σ : Tuple → ℝ) (w : ℝ) (X Y : Tuple) : Prop where
  products_defined : ∀ (i : Fin 4) (g : reflectionGroup),
    Concatenable (mirrorTuple i g X) (translatedTuple w i g X)
  size_nonneg : 0 ≤ functionalSize σ w X
  plateau_tendsto : A.IsPlateauLimit X Y (A.limitPlateau X Y)
  condExpProduct_tendsto :
    Tendsto (fun j => A.condExpProductAt j X Y) atTop (𝓝 (A.limitPlateau X Y : ℂ))
  eventually_inCube : ∀ᶠ j in atTop, A.InCubeAt w j X
  size_tendsto :
    Tendsto (fun j => A.sizeAt hL w j X) atTop (𝓝 (functionalSize σ w X))
structure InverseSquareDecay {L : ℕ} (A : LatticeSequence L) (σ : Tuple → ℝ) (w : ℝ)
    (X Y : Tuple) : Prop where
  maxNorm_bound : ∀ v : Space, 2 * w < maxNorm v →
    ∃ h : Concatenable X (push (translate v) Y),
      |σ (concat X _ h) - A.limitPlateau X Y| ≤
        spectralRateFn (w / (maxNorm v - 2 * w)) * √(functionalSize σ w X) *
          √(functionalSize σ w Y)
  euclid_bound : ∀ v : Space, 8 * w ≤ euclidNormVec v →
    ∃ h : Concatenable X (push (translate v) Y),
      |σ (concat X _ h) - A.limitPlateau X Y| ≤
        32 * spectralRateConst * √(functionalSize σ w X) * √(functionalSize σ w Y) *
          (w / euclidNormVec v) ^ 2
structure VacuumUniqueness {L : ℕ} (A : LatticeSequence L) (σ : Tuple → ℝ) : Prop where
  plateau_eq_mul : ∀ w ∈ posAdicGridPoints L, ∀ X ∈ tuplesSupportedIn (centredCube w),
    ∀ Y ∈ tuplesSupportedIn (centredCube w), A.limitPlateau X Y = σ X * σ Y
  reconstruction : FunctionalReconstruction.ReconstructionData σ
  kernel_eq_vacuumRay : KernelIsVacuumRay σ reconstruction
  ergodic : FunctionalReconstruction.IsErgodic σ reconstruction
  clusters : ClustersInTime σ
  clustersInMean : ClustersInMean σ
def LimitPlateauxTheorem : Prop :=
  ∀ (L : ℕ) (hL : IsAdmissibleBlockingFactor L) (A : LatticeSequence L) (σ : Tuple → ℝ),
    IsAdmissiblyContinuous σ → A.IsRP → A.HasLimit σ →
      (∀ w ∈ posAdicGridPoints L, ∀ X ∈ tuplesSupportedIn (centredCube w),
        ∀ Y ∈ tuplesSupportedIn (centredCube w),
          SizeAndPlateauLimits hL A σ w X Y ∧ InverseSquareDecay A σ w X Y) ∧
      (A.IsErgodicSeq → VacuumUniqueness A σ)
end LimitPlateaux
end YangMills.Construction.ReflectionPositivity

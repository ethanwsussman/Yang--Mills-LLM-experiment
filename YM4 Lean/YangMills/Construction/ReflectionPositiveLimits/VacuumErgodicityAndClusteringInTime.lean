import YangMills.Construction.ReflectionPositiveLimits.ReconstructionOfAFunctional
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open scoped InnerProductSpace NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
open EuclidIsometry
theorem push_translate_mem {v : Space} (hv : 0 ≤ v timeAxis) {Y : Tuple}
    (hY : Y ∈ tuplesSupportedIn upperHalfSpace) :
    push (translate v) Y ∈ tuplesSupportedIn upperHalfSpace := by
  intro g hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  rw [tsupport_pushFn]
  intro y hy
  have hz := hY f hf hy
  rw [symm_translate] at hz
  change 0 < y timeAxis
  have hz' : 0 < (y - v) timeAxis := hz
  have e : (y - v) timeAxis = y timeAxis - v timeAxis := rfl
  linarith
theorem concatenable_timeShift {X Y : Tuple}
    (hX : X ∈ tuplesSupportedIn upperHalfSpace) (hY : Y ∈ tuplesSupportedIn upperHalfSpace)
    (t : ℝ≥0) :
    Concatenable (push timeZeroMirror.reflectIso X) (push (translate (timeShiftVec t)) Y) :=
  NormalMirror.concatenable_reflectIso (by rw [timeZeroMirror_posSide]; exact hX)
    (by
      rw [timeZeroMirror_posSide]
      exact push_translate_mem (by rw [timeShiftVec_timeAxis]; exact t.2) hY)
def timeCorrelation (σ : Tuple → ℝ) {X Y : Tuple}
    (hX : X ∈ tuplesSupportedIn upperHalfSpace) (hY : Y ∈ tuplesSupportedIn upperHalfSpace)
    (t : ℝ≥0) : ℝ :=
  σ (concat (push timeZeroMirror.reflectIso X) (push (translate (timeShiftVec t)) Y)
    (concatenable_timeShift hX hY t))
end YangMills.Construction.ReflectionPositivity
namespace YangMills.Construction.ReflectionPositivity.TimeClustering
open YangMills.Construction.ReflectionPositivity
open YangMills.Construction.ReflectionPositivity.FunctionalReconstruction
open YangMills.Construction.EuclideanSpectral
def ClustersInTime (σ : Tuple → ℝ) : Prop :=
  ∀ (X Y : Tuple) (hX : X ∈ tuplesSupportedIn upperHalfSpace)
    (hY : Y ∈ tuplesSupportedIn upperHalfSpace),
    Tendsto (timeCorrelation σ hX hY) atTop (𝓝 (σ X * σ Y))
def ClustersInMean (σ : Tuple → ℝ) : Prop :=
  ∀ (X Y : Tuple) (hX : X ∈ tuplesSupportedIn upperHalfSpace)
    (hY : Y ∈ tuplesSupportedIn upperHalfSpace),
    Tendsto (fun t : ℝ => (1 / t) * ∫ s in (0 : ℝ)..t, timeCorrelation σ hX hY s.toNNReal) atTop
      (𝓝 (σ X * σ Y))
variable (σ : Tuple → ℝ) (hσ : ReconstructionData σ)
def GroundStateIsStrongLimit : Prop :=
  TendstoStrongly atTop (heatOperator σ hσ) (groundStateProjection σ hσ)
structure GroundStateRange : Prop where
  fixedSet_eq : fixedSet (groundStateProjection σ hσ) = {ψ | IsInvariant σ hσ ψ}
  vacuum_mem : vacuum σ hσ.reflectionPositive ∈ fixedSet (groundStateProjection σ hσ)
  rep_mul : ∀ v, spatialTranslationRep σ hσ.reflectionPositive v *
    groundStateProjection σ hσ = groundStateProjection σ hσ
  mul_rep : ∀ v, groundStateProjection σ hσ *
    spatialTranslationRep σ hσ.reflectionPositive v = groundStateProjection σ hσ
def CorrelationLimit : Prop :=
  ∀ (X Y : Tuple) (hX : X ∈ tuplesSupportedIn upperHalfSpace)
    (hY : Y ∈ tuplesSupportedIn upperHalfSpace),
    Tendsto (fun t : ℝ≥0 => ((timeCorrelation σ hX hY t : ℝ) : ℂ)) atTop
      (𝓝 ⟪toReconstruction σ hσ.reflectionPositive (tupleToComb X hX),
        groundStateProjection σ hσ
          (toReconstruction σ hσ.reflectionPositive (tupleToComb Y hY))⟫_ℂ)
def KernelIsVacuumRay : Prop :=
  pmapKernel (hamiltonianOp σ hσ) =
    Set.range fun c : ℂ => c • vacuum σ hσ.reflectionPositive
def VacuumClusteringHolds : Prop :=
  ∀ (σ : Tuple → ℝ) (hσ : ReconstructionData σ),
    GroundStateIsStrongLimit σ hσ ∧ CorrelationLimit σ hσ ∧
      (KernelIsVacuumRay σ hσ ↔ ClustersInTime σ) ∧
      (ClustersInTime σ ↔ ClustersInMean σ) ∧
      (ClustersInMean σ → IsErgodic σ hσ) ∧
      ((∀ i, EnergyDominatesMomentum σ hσ i) →
        GroundStateRange σ hσ ∧
          List.TFAE [KernelIsVacuumRay σ hσ, IsErgodic σ hσ, ClustersInTime σ,
            ClustersInMean σ])
end YangMills.Construction.ReflectionPositivity.TimeClustering

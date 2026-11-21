import YangMills.Construction.ReflectionPositiveLimits.FromFivePointInequalitiesToTheCone
import YangMills.Construction.ReflectionPositiveLimits.LAdicNumbersAndLAdicMirrors
import YangMills.Construction.ReflectionPositiveLimits.LatticeApproximationsRepresentativesAndLimits
import Mathlib
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LatticeLimits
open YangMills.Construction.ReflectionPositivity
open YangMills.Construction.ReflectionPositivity.FunctionalReconstruction
def translationHyperoctahedralGroup : Subgroup (Equiv.Perm Space) :=
  Subgroup.closure
    (Set.range (fun v : Space => (EuclidIsometry.translate v).toPerm) ∪ hyperoctahedral)
structure SymmetricInvariantRP (σ : Tuple → ℝ) : Prop where
  permInvariant : IsPermInvariant σ
  slotLinear : IsSlotLinear σ
  invariant_of_mem : ∀ r : EuclidIsometry, r.toPerm ∈ translationHyperoctahedralGroup →
    IsIsomInvariant r σ
  invariant_reflect : ∀ M : NormalMirror, IsIsomInvariant M.reflectIso σ
  reflectionPositive : ∀ M : NormalMirror, ReflectionPositiveAt M σ
def posAdicTimes (L : ℕ) : Set ℝ≥0 := {t | (t : ℝ) ∈ posAdicGridPoints L}
def VacuumHypotheses (σ : Tuple → ℝ) : Prop :=
  ∃ hσ : ReconstructionData σ, ∀ i, EnergyDominatesMomentum σ hσ i
structure ContractionConeVacuum (L : ℕ) (σ : Tuple → ℝ) : Prop where
  contracts : ∀ t ∈ posAdicTimes L, ContractsAtTime σ t
  fivePoint : ∀ i, FivePointPositive σ i (posAdicTimes L)
  reconstructs : ∃ hσ : ReconstructionData σ, (∀ i, EnergyDominatesMomentum σ hσ i) ∧
    ∀ ψ ∈ YangMills.Construction.EuclideanSpectral.pmapKernel (hamiltonianOp σ hσ),
      IsInvariant σ hσ ψ
  vacuumHypotheses : VacuumHypotheses σ
def LatticeLimitProperties : Prop :=
  ∀ L : ℕ, Odd L → 13 ≤ L →
    ∀ (A : LatticeSequence L) (σ : Tuple → ℝ), A.IsRP → A.HasLimit σ →
      IsAdmissiblyContinuous σ → SymmetricInvariantRP σ ∧ ContractionConeVacuum L σ
end YangMills.Construction.ReflectionPositivity.LatticeLimits

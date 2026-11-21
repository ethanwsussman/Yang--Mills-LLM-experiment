import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.FamiliesOfCriticalBranches
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
structure Geometry.CurveData.HasLocalCurves {X T : Type} [TopologicalSpace X]
    (R : Geometry.CurveData X T) : Prop where
  isCurve_local : ∀ (I : Set ℝ) (γ : ℝ → X), R.IsCurve I γ →
    Tower.IsOpenIntervalAroundZero I ∧ ContinuousAt γ 0 ∧
      ∀ J, Tower.IsOpenIntervalAroundZero J → J ⊆ I → R.IsCurve J γ
  isTwiceDiffCurve_local : ∀ (I : Set ℝ) (γ : ℝ → X), R.IsTwiceDiffCurve I γ →
    Tower.IsOpenIntervalAroundZero I ∧ ContinuousAt γ 0 ∧
      ∀ J, Tower.IsOpenIntervalAroundZero J → J ⊆ I → R.IsTwiceDiffCurve J γ
namespace Tower
variable {L n k : ℕ}
namespace CriticalBranchData
def EnergyIsActionAtBase (b : CriticalBranchData L n k) :
    ∀ i : ℕ, Set (Edge L n k i → Matrices.ComplexMatrix2) → Prop
  | 0, U => ∀ V ∈ U, b.energy 0 V = plaquetteAction L n k V
  | _ + 1, _ => True
structure IsFibreNhd (b : CriticalBranchData L n k) (i : ℕ)
    (U : Set (Edge L n k i → Matrices.ComplexMatrix2)) : Prop where
  isOpenNhd : IsOpenNhdOfOne U
  analytic_smoothing : IsAnalyticFieldMap U (smoothingStep L n k i)
  subset_domain : U ⊆ axialFunctionDomain L n k i
  analytic_gaugeFixedEnergy : IsAnalyticFieldFunction U (b.gaugeFixedEnergy i)
  differential_surjective : ∀ V ∈ U, ∀ B' ∈ edgeFormSpace L n k (i + 1),
    ∃ B ∈ edgeFormSpace L n k i, leftDifferential (smoothingStep L n k i) V B = B'
  fibre_structure : ∀ W ∈ fieldSpace L n k (i + 1), levelFibre U W = ∅ ∨
    (IsAnalyticFieldSubmanifold (levelFibre U W) ∧ TangentSpacesAreKernels i (levelFibre U W))
  unique_critical : EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
    IsUniqueCriticalPointIn (levelFibre U W) (levelFibre U W) (b.gaugeFixedEnergy i) (b.prolong i W) ∧
      HasPosDefHessian (levelFibre U W) (b.gaugeFixedEnergy i) (b.prolong i W)
  base_action : b.EnergyIsActionAtBase i U
end CriticalBranchData
def FibreNeighbourhoodsOfSteps : Prop :=
  (∀ (X T : Type) [TopologicalSpace X] [AddCommGroup T] [Module ℝ T] (R : Geometry.CurveData X T),
      R.HasLocalCurves → ∀ (N N' : Set X) (F : X → ℝ), Matrices.ComplexMatrix2.IsRelativelyOpen N N' →
      ∀ x, (R.IsCriticalOn N' F x ↔ x ∈ N' ∧ R.IsCriticalOn N F x) ∧
        (R.IsCriticalOn N' F x → R.tangentSpan N' x = R.tangentSpan N x ∧
          ∀ (S : Type) [AddCommGroup S] [Module ℝ S] (ι : S → T),
            R.hessianForm ι N' F x = R.hessianForm ι N F x)) ∧
  (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E],
    (Matrices.EmbeddedSubmanifold.vectorCurveData E).HasLocalCurves) ∧
  (∀ L n k j : ℕ, (fieldCurveData L n k j).HasLocalCurves) ∧
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    ∀ b : CriticalBranchData L n k, b.IsCritical →
      ∀ i < k, ∃ U : Set (Edge L n k i → Matrices.ComplexMatrix2), b.IsFibreNhd i U
end Tower
end YangMills.Construction
end

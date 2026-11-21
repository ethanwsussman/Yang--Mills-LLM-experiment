import YangMills.Construction.Towers.FamiliesOfCriticalBranches
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
variable {L n k : ℕ}
def nearIdentityBall (L n k i : ℕ) (ε : ℝ) : Set (Edge L n k i → Matrices.ComplexMatrix2) :=
  {V | V ∈ fieldSpace L n k i ∧ ∀ e, ‖V e - 1‖ < ε}
structure IsFibreCriticalSection {i : ℕ} (F : (Edge L n k i → Matrices.ComplexMatrix2) → ℝ)
    (U : Set (Edge L n k i → Matrices.ComplexMatrix2)) (ε : ℝ)
    (s : (Edge L n k (i + 1) → Matrices.ComplexMatrix2) → Edge L n k i → Matrices.ComplexMatrix2) :
    Prop where
  isOpenNhd : IsOpenNhdOfOne U
  radius_pos : 0 < ε
  ball_subset : nearIdentityBall L n k i ε ⊆ U
  ball_mem_nhds : nearIdentityBall L n k i ε ∈ 𝓝[fieldSpace L n k i] trivialField L n k i
  analytic_section : ∃ W : Set (Edge L n k (i + 1) → Matrices.ComplexMatrix2),
    IsOpenNhdOfOne W ∧ IsAnalyticFieldMap W s
  section_trivial : s (trivialField L n k (i + 1)) = trivialField L n k i
  smoothing_section : EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
    smoothingStep L n k i (s W) = W
  fibre_structure : EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
    IsAnalyticFieldSubmanifold (CriticalBranchData.levelFibre U W) ∧
      TangentSpacesAreKernels i (CriticalBranchData.levelFibre U W)
  unique_critical : EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
    IsUniqueCriticalPointIn (nearIdentityBall L n k i ε) (CriticalBranchData.levelFibre U W) F (s W) ∧
      HasPosDefHessian (CriticalBranchData.levelFibre U W) F (s W)
  isMin_fibre : EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
    ∀ V ∈ CriticalBranchData.levelFibre U W, V ≠ s W → F (s W) < F V
  deriv_section : ∀ B ∈ edgeFormSpace L n k (i + 1),
    leftDifferential s (trivialField L n k (i + 1)) B ∈ edgeFormSpace L n k i ∧
      linearSmoothing L n k i (leftDifferential s (trivialField L n k (i + 1)) B) = B
  deriv_orthogonal : ∀ B ∈ edgeFormSpace L n k (i + 1), ∀ ξ ∈ edgeFormSpace L n k i,
    linearSmoothing L n k i ξ = 0 →
      leftSecondDeriv F (trivialField L n k i)
        (leftDifferential s (trivialField L n k (i + 1)) B) ξ = 0
namespace CriticalBranchData
def extendLevel (b : CriticalBranchData L n k) (i : ℕ)
    (s : (Edge L n k (i + 1) → Matrices.ComplexMatrix2) → Edge L n k i → Matrices.ComplexMatrix2) :
    CriticalBranchData L n k where
  energy := Function.update b.energy (i + 1) fun W => b.gaugeFixedEnergy i (s W)
  prolong := Function.update b.prolong i s
end CriticalBranchData
end YangMills.Construction.Tower
end

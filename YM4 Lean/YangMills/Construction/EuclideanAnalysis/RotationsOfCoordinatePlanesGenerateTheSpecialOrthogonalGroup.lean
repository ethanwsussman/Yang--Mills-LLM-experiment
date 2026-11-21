import YangMills.Construction.EuclideanAnalysis.FunctionsAndDistributions
import Mathlib
set_option autoImplicit false
open Matrix
noncomputable section
namespace YangMills.Construction.EuclideanAnalysis
namespace PlaneRotations
def coordPlane {n : ℕ} (a b : Fin n) :
    Submodule ℝ (YangMills.Construction.EuclideanAnalysis.RealSpace n) :=
  Submodule.span ℝ {YangMills.Construction.EuclideanAnalysis.stdBasisVector a,
    YangMills.Construction.EuclideanAnalysis.stdBasisVector b}
def IsPlaneRotation {n : ℕ} (Q : specialOrthogonalGroup (Fin n) ℝ) : Prop :=
  ∃ a b : Fin n, a ≠ b ∧
    (coordPlane a b).map (toEuclideanLin (Q : Matrix (Fin n) (Fin n) ℝ)) = coordPlane a b ∧
    ∀ c : Fin n, c ≠ a → c ≠ b →
      toEuclideanLin (Q : Matrix (Fin n) (Fin n) ℝ)
          (YangMills.Construction.EuclideanAnalysis.stdBasisVector c) =
        YangMills.Construction.EuclideanAnalysis.stdBasisVector c
def lastCoordReflection : Matrix (Fin 4) (Fin 4) ℝ := diagonal ![1, 1, 1, -1]
theorem lastCoordReflection_mulVec (v : Fin 4 → ℝ) :
    lastCoordReflection *ᵥ v = ![v 0, v 1, v 2, -v 3] := by
  funext i
  fin_cases i <;> simp [lastCoordReflection, mulVec_diagonal]
end PlaneRotations
open PlaneRotations in
def PlaneRotationsGenerate : Prop :=
  (∀ n : ℕ, 2 ≤ n → ∀ Q : specialOrthogonalGroup (Fin n) ℝ,
    ∃ qs : List (specialOrthogonalGroup (Fin n) ℝ),
      (∀ P ∈ qs, IsPlaneRotation P) ∧ qs.prod = Q) ∧
  ((orthogonalGroup (Fin 4) ℝ : Set (Matrix (Fin 4) (Fin 4) ℝ)) =
    (specialOrthogonalGroup (Fin 4) ℝ : Set (Matrix (Fin 4) (Fin 4) ℝ)) ∪
      (fun Q => Q * lastCoordReflection) ''
        (specialOrthogonalGroup (Fin 4) ℝ : Set (Matrix (Fin 4) (Fin 4) ℝ))) ∧
  ∀ L k : ℕ, ∃ g ∈ YangMills.Construction.PeriodicLattice.hyperoctahedralGroup L k,
    ∀ v : Fin 4 → ℝ,
      g (fun i => (v i : AddCircle (YangMills.Construction.PeriodicLattice.torusSide L k))) =
        fun i => ((lastCoordReflection *ᵥ v) i :
          AddCircle (YangMills.Construction.PeriodicLattice.torusSide L k))
end YangMills.Construction.EuclideanAnalysis

import YangMills.Construction.Towers.TheFunctionOfTheMassiveJets
import YangMills.Construction.Towers.TheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Coordinates
namespace Tower.FullSpace.BackgroundJets.MassiveFunctionalAndJets
open PeriodicOperators
def ofRealMomentum (q : Fin 4 → ℝ) : Fin 4 → ℂ := fun ν => (q ν : ℂ)
def realPartialDeriv (ν : Fin 4) (F : (Fin 4 → ℝ) → ℂ) (q : Fin 4 → ℝ) : ℂ :=
  deriv (fun s : ℝ => F (Function.update q ν s)) (q ν)
def mixedPartialAtZero (F : (Fin 4 → ℝ) → ℂ) : ℂ := realPartialDeriv 0 (realPartialDeriv 1 F) 0
def pointOfMassAndMomentum (m : ℝ) (q : Fin 4 → ℂ) : ComplexCoordinates 5 :=
  fun j => Fin.cases (m : ℂ) q j
def withinMassWidth : Set (ComplexCoordinates 5) :=
  {x | x ∈ ComplexCoordinates.realLocus 5 ∧ 0 < (x 0).re ∧
    ∀ ν : Fin 4, ‖x ν.succ‖ < massWidth (x 0).re}
def massiveLogFnCoords (L k : ℕ) (x : ComplexCoordinates 5) : ComplexCoordinates 1 :=
  fun _ => massiveLogFn L k (fun ν => x ν.succ) 0 1 (x 0).re
def massiveLogFnSharpCoords (L k : ℕ) (q : ComplexCoordinates 4) : ComplexCoordinates 1 :=
  fun _ => massiveLogFnSharp L k q 0 1
def positiveReals : Set (ComplexCoordinates 1) :=
  {x | x ∈ ComplexCoordinates.realLocus 1 ∧ 0 < (x 0).re}
def stiffnessCoords {L : ℕ} (hpos : 0 < L) (x : ComplexCoordinates 1) : ComplexCoordinates 1 :=
  fun _ => (massiveStiffness hpos (x 0).re : ℂ)
def TemperedForAllMasses {L : ℕ} (hpos : 0 < L) : Prop :=
  ∀ m : ℝ, 0 < m →
    Tempered.IsTemperedFunctional L (massiveFieldFamily L m) ∧ MassiveStiffnessExists hpos m
def AtLevel {L : ℕ} (hpos : 0 < L) (k : ℕ) : Prop :=
  (∃ U : Set (ComplexCoordinates 5),
      ComplexCoordinates.IsRealAnalyticIn U (massiveLogFnCoords L k) ∧
      (∀ m : ℝ, 0 < m → pointOfMassAndMomentum m 0 ∈ U) ∧ U ⊆ withinMassWidth) ∧
    ∀ m : ℝ, 0 < m →
      -mixedPartialAtZero (fun q => massiveLogFn L k (ofRealMomentum q) 0 1 m) =
        (massiveStiffness hpos (finestMesh L k ^ 2 * m) : ℂ)
def StiffnessAnalytic {L : ℕ} (hpos : 0 < L) : Prop :=
  ComplexCoordinates.IsRealAnalyticIn positiveReals (stiffnessCoords hpos) ∧
    ∀ m : ℝ, 0 < m →
      DifferentiableAt ℝ (massiveStiffness hpos) m ∧
        DifferentiableAt ℝ (deriv (massiveStiffness hpos)) m
def SharpAtLevel {L : ℕ} (hpos : 0 < L) (k : ℕ) : Prop :=
  ExistsOpenNear (Matrices.ComplexMatrix2.IsRelativelyOpen (ComplexCoordinates.realLocus 4)) {0}
      (fun U =>
        U ⊆ momentumPolydisc stripHalfWidth ∧
          ComplexCoordinates.IsRealAnalyticIn U (massiveLogFnSharpCoords L k)) ∧
    -mixedPartialAtZero (fun q => massiveLogFnSharp L k (ofRealMomentum q) 0 1) =
      ((massiveStiffness hpos (finestMesh L k ^ 2) -
          finestMesh L k ^ 2 * massiveStiffnessDeriv hpos (finestMesh L k ^ 2) +
          1 / 2 * finestMesh L k ^ 4 *
            massiveStiffnessDeriv2 hpos (finestMesh L k ^ 2) : ℝ) : ℂ)
def Claim : Prop :=
  ∀ (L : ℕ) (hpos : 0 < L), Conventions.IsAdmissibleBlockingFactor L →
    TemperedForAllMasses hpos ∧ (∀ k : ℕ, 1 ≤ k → AtLevel hpos k) ∧
      StiffnessAnalytic hpos ∧ ∀ k : ℕ, 1 ≤ k → SharpAtLevel hpos k
end Tower.FullSpace.BackgroundJets.MassiveFunctionalAndJets
end YangMills.Construction
end

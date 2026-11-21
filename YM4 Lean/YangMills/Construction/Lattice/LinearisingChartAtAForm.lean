import YangMills.Construction.Lattice.LinearisedConstraint
import Mathlib
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K k : ℕ}
structure IsChartData (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (Γ : Set (BondAtLevel L m K (k + 1))) : Prop where
  finite : Γ.Finite
  positivelyOriented : ∀ c ∈ Γ, c.IsPositivelyOriented
  mem_domain : ∀ c ∈ Γ, V ∈ complexAveragingDomainNearOne c
  pivot_invertible : ∀ c ∈ Γ, PivotCoeffInvertible V c
def coarseBondFunctions (Γ : Set (BondAtLevel L m K (k + 1))) :
    Submodule ℂ (↥Γ → Matrices.ComplexMatrix2) :=
  Submodule.pi univ fun _ => Matrices.ComplexMatrix2.traceless
def constraintDomain (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (Γ : Set (BondAtLevel L m K (k + 1))) :
    Set (SupportBond (levelDepth K k) Γ → Matrices.ComplexMatrix2) :=
  {B' | B' ∈ supportForms (levelDepth K k) Γ ∧
    ∀ c ∈ Γ, ConstraintMapDefined V (extendForm B') c}
def restrictedConstraintMap (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (Γ : Set (BondAtLevel L m K (k + 1)))
    (B' : SupportBond (levelDepth K k) Γ → Matrices.ComplexMatrix2) :
    ↥Γ → Matrices.ComplexMatrix2 :=
  fun c => constraintMap V (extendForm B') (c : BondAtLevel L m K (k + 1))
def restrictedLinearizedConstraint (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (Γ : Set (BondAtLevel L m K (k + 1)))
    (B : SupportBond (levelDepth K k) Γ → Matrices.ComplexMatrix2) :
    ↥Γ → Matrices.ComplexMatrix2 :=
  fun c => linearizedConstraint V (extendForm B) (c : BondAtLevel L m K (k + 1))
structure IsCorrectionContinuation (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (Γ : Set (BondAtLevel L m K (k + 1)))
    (O : Set (SupportBond (levelDepth K k) Γ → Matrices.ComplexMatrix2))
    (D : (SupportBond (levelDepth K k) Γ → Matrices.ComplexMatrix2) →
      ↥Γ → Matrices.ComplexMatrix2) : Prop where
  chartData : IsChartData V Γ
  zero_mem : 0 ∈ O
  smul_mem_of_mem_Icc : ∀ B ∈ O, ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → (τ : ℂ) • B ∈ O
  holomorphic : IsHolomorphicOnSupportForms O D
  mapsTo : ∀ B ∈ O, D B ∈ coarseBondFunctions Γ
  map_zero : D 0 = 0
  sub_mem_constraintDomain : ∀ B ∈ O,
    B - pivotCorrectionLift V Γ (D B) ∈ constraintDomain V Γ
  constraint_sub_eq : ∀ B ∈ O,
    restrictedConstraintMap V Γ (B - pivotCorrectionLift V Γ (D B)) =
      (L : ℂ) • restrictedLinearizedConstraint V Γ B
def chosenContinuation (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (Γ : Set (BondAtLevel L m K (k + 1)))
    (B : SupportBond (levelDepth K k) Γ → Matrices.ComplexMatrix2) :
    Set (SupportBond (levelDepth K k) Γ → Matrices.ComplexMatrix2) ×
      ((SupportBond (levelDepth K k) Γ → Matrices.ComplexMatrix2) →
        ↥Γ → Matrices.ComplexMatrix2) :=
  Classical.epsilon fun p => IsCorrectionContinuation V Γ p.1 p.2 ∧ B ∈ p.1
def continuationCorrectionDeriv (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (Γ : Set (BondAtLevel L m K (k + 1)))
    (B X : SupportBond (levelDepth K k) Γ → Matrices.ComplexMatrix2) :
    ↥Γ → Matrices.ComplexMatrix2 :=
  fun c => deriv (fun t : ℂ => (chosenContinuation V Γ B).2 (B + t • X) c) 0
end YangMills.Construction.PeriodicLattice

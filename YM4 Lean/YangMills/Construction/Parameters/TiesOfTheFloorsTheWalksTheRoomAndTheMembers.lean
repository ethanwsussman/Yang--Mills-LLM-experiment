import YangMills.Construction.Parameters.FamiliesOfTheDeterminedAndNamedNumbers
import YangMills.Construction.Parameters.LeastFloorOfTheOddBlockingFactors
import Mathlib
import YangMills.Construction.Constants.KernelComparisonNumbers
import YangMills.Construction.FreeKernel.ConstantsOfTheTwoBoundsOnTheFreeLatticeField
set_option autoImplicit false

section
open Set
noncomputable section
namespace YangMills.Construction.TwoPointLaw
def FluctuationBound (L : ℕ) (t : ℝ) : Prop :=
  YangMills.Construction.Constants.KernelComparison.fixedCutoffFirst *
    YangMills.Construction.PeriodicLattice.freeFieldConstant L * (Real.pi ^ 2 / 16) * t ^ 4 *
    Real.exp (-(YangMills.Construction.PeriodicLattice.freeFieldRate L * t / 2)) ≤ 1 / 16
def fluctuationThresholds (L : ℕ) : Set ℝ :=
  {t | 8 / YangMills.Construction.PeriodicLattice.freeFieldRate L ≤ t ∧ FluctuationBound L t}
def fluctuationThreshold (L : ℕ) : ℝ := sInf (fluctuationThresholds L)
end YangMills.Construction.TwoPointLaw
end
end

noncomputable section
namespace YangMills.Construction.TreeGraphs
abbrev LatticePoint : Type := Fin 4 → ℤ
def Adjacent (x y : LatticePoint) : Prop := ∃ i, |x i - y i| = 1 ∧ ∀ j, j ≠ i → x j = y j
def blockIndex (M : ℕ) (x : LatticePoint) : LatticePoint := fun i => x i / (M : ℤ)
def Connected (T : Finset LatticePoint) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, Relation.ReflTransGen (fun u v => u ∈ T ∧ v ∈ T ∧ Adjacent u v) x y
def HitsBlocks (M : ℕ) (T C : Finset LatticePoint) : Prop :=
  ∀ c ∈ C, ∃ x ∈ T, blockIndex M x = c
def edgeCount (T : Finset LatticePoint) : ℝ := (T.card : ℝ) - 1
def IsDecayRate (δ₀ δ₁ : ℝ) : Prop :=
  0 < δ₁ ∧ ∀ (M : ℕ) (T C : Finset LatticePoint), 0 < M → Connected T → HitsBlocks M T C →
    2 ^ 4 < C.card → δ₁ * (C.card : ℝ) * (M : ℝ) ≤ δ₀ * edgeCount T
def decayRate (δ₀ : ℝ) : ℝ := Classical.epsilon (IsDecayRate δ₀)
end YangMills.Construction.TreeGraphs
end

open Set
noncomputable section
namespace YangMills.Construction.ParameterChoice
def BaseFactorAboveThreshold (T : DerivedConstants) (N : ExternalConstants) : Prop :=
  ∀ s : InitialChoice, InitialConstraints s → leastOddBlockingFactorThreshold N s T.o ≤ T.L₀ s
def TreeDecayRateMatches (T : DerivedConstants) : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    T.δ₁Ring L = TreeGraphs.decayRate (T.δ₀Ring L)
def RoomConstantAboveFloors (N : ExternalConstants) : Prop :=
  ∀ t ∈ Ioc (0 : ℝ) 1, ∀ (c : ChoiceUpToCoupling) (ρ κ : ℝ),
    Conventions.IsAdmissibleBlockingFactor c.L → 0 < c.A₀ →
      max 2 (TwoPointLaw.fluctuationThreshold c.L) ≤ N.CW0TwoPoint t c ρ κ * c.A₀ ^ 2
structure ExtremalBounds (T : DerivedConstants) : Prop where
  one_le_fifth : ∀ L M R : ℕ, BlockingFactorAdmissible L → IsPositivePowerOf L M →
    IsPositivePowerOf L R → 1 ≤ T.B₅ L M R
  epsilon_le_one : ∀ L M R : ℕ, BlockingFactorAdmissible L → IsPositivePowerOf L M →
    IsPositivePowerOf L R → T.εBarG L M R ≤ 1
  radius_le_one : ∀ L M R : ℕ, BlockingFactorAdmissible L → IsPositivePowerOf L M →
    IsPositivePowerOf L R → T.rB L M R ≤ 1
  epsilon_add_radius_le : ∀ L M R : ℕ, BlockingFactorAdmissible L → IsPositivePowerOf L M →
    IsPositivePowerOf L R → T.εBarG L M R + 4 * T.rB L M R ≤ firstRadiusScaled T L M R
structure CompatibilityConditions (T : DerivedConstants) (N : ExternalConstants) : Prop where
  baseFactor : BaseFactorAboveThreshold T N
  treeRate : TreeDecayRateMatches T
  roomConstant : RoomConstantAboveFloors N
  extremalBounds : ExtremalBounds T
end YangMills.Construction.ParameterChoice
end

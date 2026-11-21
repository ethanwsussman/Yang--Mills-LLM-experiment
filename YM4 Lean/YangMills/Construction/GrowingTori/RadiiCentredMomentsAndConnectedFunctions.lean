import YangMills.Construction.GrowingTori.BoundFunctionsHierarchiesAndCentredMomentsOfFourSpace
import YangMills.Construction.GrowingTori.DataAndSequencesOfTheLimitsAlongGrowingTori
import Mathlib
set_option autoImplicit false
open Filter Set
noncomputable section
namespace YangMills.Construction.ToriLimits
namespace Setup
variable (D : Setup)
def transportData (K m : ℕ+) : TorusTransport.TransportData where
  L := D.L
  isAdmissible := D.admissible
  K := K
  m := m
  M := D.M
  one_le_M := by exact_mod_cast D.one_le_M
def centredProductExpectation (K m : ℕ+) (β : ℝ) {q : ℕ}
    (h : Fin q → RealFn) : ℝ :=
  D.expectation K m β fun U => ∏ l,
    (PeriodicLattice.smearedObservable (SchwingerFunctions.periodizeAll D.L m h l) U -
      D.expectation K m β (PeriodicLattice.smearedObservable (SchwingerFunctions.periodizeAll D.L m h l)))
def partitionSumOfConnected (K m : ℕ+) (β : ℝ) {q : ℕ}
    (h : Fin q → RealFn) : ℂ :=
  ∑ π ∈ SetPartition.singletonFree q, ∏ B ∈ π.parts,
    D.connectedOnFourSpace K m β (subfamily h B)
def ConnectedRealSymmMultilinear (K m : ℕ+) (β ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (hn : 2 ≤ n) :
    Prop :=
  ∃ Ψ : (TestTupleClass.ball ρ hρ).members (D.transportData K m).toStandingParameters n → ℝ,
    (∀ f, ((Ψ f : ℝ) : ℂ) = D.connectedOnFourSpace K m β f.1) ∧
    IsClassSymmetric (D.transportData K m).toStandingParameters (.ball ρ hρ) Ψ ∧
    IsClassMultilinear (D.transportData K m) (.ball ρ hρ) (by omega : 1 ≤ n) Ψ
end Setup
namespace ToriSequence
variable {D : Setup} (S : ToriSequence D)
theorem radius_pos (k : ℕ+) : 0 < S.radius k := by
  have hL : (13 : ℝ) ≤ D.L := by exact_mod_cast D.admissible.2
  have h₁ : (D.L : ℝ) ^ 1 ≤ (D.L : ℝ) ^ (S.m k : ℕ) :=
    pow_le_pow_right₀ (by linarith) (S.m k).pos
  unfold radius
  rw [pow_one] at h₁
  linarith
def centredProductExpectation (k : ℕ+) {q : ℕ} (h : Fin q → RealFn) : ℝ :=
  S.expectation k fun U => ∏ l,
    (PeriodicLattice.smearedObservable (SchwingerFunctions.periodizeAll D.L (S.m k) h l) U -
      S.expectation k (PeriodicLattice.smearedObservable (SchwingerFunctions.periodizeAll D.L (S.m k) h l)))
def partitionSumOfConnected (k : ℕ+) {q : ℕ} (h : Fin q → RealFn) : ℂ :=
  ∑ π ∈ SetPartition.singletonFree q, ∏ B ∈ π.parts, S.connected k (subfamily h B)
end ToriSequence
namespace MomentsAndConnected
def RadiusProperties {D : Setup} (S : ToriSequence D) : Prop :=
  (∀ k, S.radius k ∈ Ioi (0 : ℝ)) ∧ Tendsto S.radius atTop atTop ∧
    ∀ (k : ℕ+) (ρ : ℝ), 0 < ρ →
      (2 * ρ + 2 ≤ (D.L : ℝ) ^ (S.m k : ℕ) ↔ ρ ≤ S.radius k)
def CentredMomentsAtCutoff (D : Setup) : Prop :=
  ∀ (K m : ℕ+) (β ρ : ℝ) (_hβ : 0 < β) (hρ : 0 < ρ), ρ ≤ ((D.L : ℝ) ^ (m : ℕ) - 2) / 2 →
    ∀ (q : ℕ) (h : Fin q → RealFn),
      h ∈ sepLipTuplesInBall q ρ hρ →
        D.centredOnFourSpace K m β h = (D.centredProductExpectation K m β h : ℝ) ∧
        ((D.centredProductExpectation K m β h : ℝ) : ℂ) =
          D.partitionSumOfConnected K m β h
def CentredMomentsAlongSequence {D : Setup} (S : ToriSequence D) : Prop :=
  ∀ (k : ℕ+) (q : ℕ) (h : Fin q → RealFn),
    h ∈ sepLipTuplesInBall q (S.radius k) (S.radius_pos k) →
      S.centred k h = (S.centredProductExpectation k h : ℝ) ∧
      ((S.centredProductExpectation k h : ℝ) : ℂ) = S.partitionSumOfConnected k h
def MomentBoundLowOrders : Prop :=
  ∀ (C : PeriodicSpace.BoundFamily) (d R : ℝ), 0 < d → 0 < R →
    momentBoundSum C 0 d R = 1 ∧ momentBoundSum C 1 d R = 0
def ConnectedFunctionalsRealSymmMultilinear (D : Setup) : Prop :=
  ∀ (K m : ℕ+) (β ρ : ℝ) (_hβ : 0 < β) (hρ : 0 < ρ), ρ ≤ ((D.L : ℝ) ^ (m : ℕ) - 2) / 2 →
    ∀ (n : ℕ) (hn : 2 ≤ n), D.ConnectedRealSymmMultilinear K m β ρ hρ n hn
def PartialHierarchyAlongSequence {D : Setup} (S : ToriSequence D) : Prop :=
  ∀ k : ℕ+, ∃ Φ : PartialHierarchy D.L (S.radius k),
    (∀ (n : ℕ) (hn : 2 ≤ n) (f : GrowingTori.lipTuplesInBall D.L n (S.radius k)),
      ((Φ.phi n hn f : ℝ) : ℂ) = S.functionals k n hn f) ∧
    ∀ (q : ℕ) (h : sepLipTuplesInBall q (S.radius k) Φ.radius_pos),
      S.centred k h.1 = (centredMomentOf Φ h : ℝ)
def Statement : Prop :=
  ∀ (D : Setup) (S : ToriSequence D),
    RadiusProperties S ∧ CentredMomentsAtCutoff D ∧ CentredMomentsAlongSequence S ∧
      MomentBoundLowOrders ∧ ConnectedFunctionalsRealSymmMultilinear D ∧
        PartialHierarchyAlongSequence S
end MomentsAndConnected
end YangMills.Construction.ToriLimits
end

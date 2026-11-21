import YangMills.Construction.GrowingTori.CentredTensorMomentsOnATorusAndTheReflectionOfTestFunctions
import YangMills.Construction.GrowingTori.DataAndSequencesOfTheLimitsAlongGrowingTori
import YangMills.Construction.TorusOrFourSpace.TensorsOfSeparatedTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.TorusTransport.TestFunctionOrders
namespace ToriLimits
open PeriodicSpace
def sepTensorSpanOn (P : PeriodicSpace.Params) (q : ℕ)
    (O : Set (Kind.euclidean.Pt P)) :
    Submodule ℂ ((Fin q → Kind.euclidean.Pt P) → ℂ) :=
  Submodule.span ℂ
    {F | ∃ f ∈ Kind.sepC1TuplesWithin P Kind.euclidean q O,
      F = Kind.tensorFn P Kind.euclidean fun i y => ((f i y : ℝ) : ℂ)}
theorem sepTensorSpanOn_univ (P : PeriodicSpace.Params) (q : ℕ) :
    sepTensorSpanOn P q Set.univ = Kind.sepTensorSpan P Kind.euclidean q := by
  unfold sepTensorSpanOn Kind.sepTensorSpan
  congr 1
  ext F
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf.1, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, ⟨hf, fun _ => Set.subset_univ _⟩, rfl⟩
namespace Setup
variable (D : Setup)
abbrev momentSetup (K m : ℕ+) (β : ℝ) (hβ : 0 < β) : CentredTensorMoments.MomentData where
  L := D.L
  isAdmissible := D.admissible
  m := m
  M := D.M
  one_le_M := by exact_mod_cast D.one_le_M
  K := K
  β := β
  β_pos := hβ
def latticeRadius (m : ℕ+) : ℝ := ((D.L : ℝ) ^ (m : ℕ) - 2) / 2
theorem latticeRadius_eq_ballRadius (K m : ℕ+) (β : ℝ) (hβ : 0 < β) :
    D.latticeRadius m = BallPeriodization.ballRadius (D.momentSetup K m β hβ).toParams := by
  rw [(BallPeriodization.ballRadius_eq (D.momentSetup K m β hβ).toParams).2.1]
  simp only [latticeRadius, BallPeriodization.radiusOffset]
  ring
theorem latticeRadius_pos (m : ℕ+) : 0 < D.latticeRadius m := by
  have hL : 8 * 105 ^ 4 ≤ D.L := D.large_L
  have hpow : D.L ≤ D.L ^ (m : ℕ) := Nat.le_self_pow m.pos.ne' D.L
  have hthree : (3 : ℝ) ≤ (D.L : ℝ) ^ (m : ℕ) := by
    have : 3 ≤ D.L ^ (m : ℕ) := by omega
    exact_mod_cast this
  unfold latticeRadius
  linarith
theorem isRadius_latticeRadius (K m : ℕ+) (β : ℝ) (hβ : 0 < β) :
    (D.momentSetup K m β hβ).IsRadius (D.latticeRadius m) :=
  ⟨D.latticeRadius_pos m, (D.latticeRadius_eq_ballRadius K m β hβ).le⟩
def centredPolynomial (K m : ℕ+) (β : ℝ) (hβ : 0 < β) {q : ℕ} (F : OrderedTestFun q) :
    (D.momentSetup K m β hβ).BondField → ℂ :=
  (D.momentSetup K m β hβ).tensorObservable (D.latticeRadius m) F
theorem centredPolynomial_succ (K m : ℕ+) (β : ℝ) (hβ : 0 < β) {q : ℕ}
    (F : OrderedTestFun (q + 1)) (U : (D.momentSetup K m β hβ).BondField) :
    D.centredPolynomial K m β hβ F U =
      ∑ᶠ p : Fin (q + 1) → (D.momentSetup K m β hβ).PlaquetteInBall (D.latticeRadius m),
        F (fun l => CentredTensorMoments.MomentData.ballPoint (p l)) *
          ∏ l, (((D.momentSetup K m β hβ).centredPlaquetteCost (p l).1 U : ℝ) : ℂ) :=
  rfl
def tensorMoment (K m : ℕ+) (β : ℝ) (hβ : 0 < β) {q : ℕ} (F : OrderedTestFun q) : ℂ :=
  D.expectation K m β (D.centredPolynomial K m β hβ F)
theorem tensorMoment_eq_centredTensorMoment (K m : ℕ+) (β : ℝ) (hβ : 0 < β) {q : ℕ}
    (F : OrderedTestFun q) :
    D.tensorMoment K m β hβ F =
      (D.momentSetup K m β hβ).centredTensorMoment (D.latticeRadius m) F :=
  rfl
end Setup
namespace ToriSequence
variable {D : Setup} (S : ToriSequence D)
theorem radius_eq_latticeRadius (k : ℕ+) : S.radius k = D.latticeRadius (S.m k) :=
  rfl
def tensorMoment (k : ℕ+) {q : ℕ} (F : OrderedTestFun q) : ℂ :=
  D.tensorMoment (S.K k) (S.m k) (S.β k) (S.β_pos k) F
end ToriSequence
end ToriLimits
end YangMills.Construction
end

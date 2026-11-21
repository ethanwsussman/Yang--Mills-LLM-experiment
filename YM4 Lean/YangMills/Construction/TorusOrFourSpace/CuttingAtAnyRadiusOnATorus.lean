import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsAndSetsAtPositiveDistance
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.CutAtRadius
variable (D : Params)
structure IsCuttingFamily {A : Type} [Fintype A] (R : ℝ) (χ : A → Pt D torus → ℝ) : Prop where
  mem_unitInterval : ∀ a, χ a ∈ smoothUnitIntervalSet D torus
  sum_eq_one : ∀ y, ∑ a, χ a y = 1
  support_subset_ball : ∀ a, ∃ S, IsClosedBallWithRadius D torus S R ∧ supportQ D torus (χ a) ⊆ S
def cuttingTheta {A : Type} [Fintype A] (χ : A → Pt D torus → ℝ) : ℝ :=
  ∑ a, (1 + 40 * D.M * lipConstQ D torus (χ a))
def IsSpacedBallTuple (n : ℕ) (d R : ℝ) (g : FnTuple D torus n) : Prop :=
  g ∈ sepC1Tuples D torus n ∧ ENNReal.ofReal d ≤ supportGap D torus g ∧
    ∀ i, ∃ S, IsClosedBallWithRadius D torus S R ∧ supportQ D torus (g i) ⊆ S
def TorusCutAtAnyRadius : Prop :=
  ∀ (D : Params) (R : ℝ), 0 < R →
    (∃ (A : Type) (_ : Fintype A) (χ : A → Pt D torus → ℝ), IsCuttingFamily D R χ) ∧
    ∀ (A : Type) [Fintype A] (χ : A → Pt D torus → ℝ), IsCuttingFamily D R χ →
      (∀ a, IsLipschitzQ D torus (χ a)) ∧
      cuttingTheta D χ ∈ Set.Ici (1 : ℝ) ∧
      ∀ (n : ℕ), 2 ≤ n → ∀ d : ℝ, 0 < d →
        (R < D.side / 4 → ∀ g : FnTuple D torus n,
          IsSpacedBallTuple D n d R g ↔
            g ∈ sepC1Tuples D torus n ∩ lipTuplesSpacedInBalls D torus n d R) ∧
        ∀ c : ℝ, 0 ≤ c → ∀ Ψ : sepC1Tuples D torus n → ℝ,
          IsMultilinearOn D torus (sepC1Tuples D torus n) Ψ →
          (∀ g : sepC1Tuples D torus n, IsSpacedBallTuple D n d R g.1 →
            ENNReal.ofReal |Ψ g| ≤ ENNReal.ofReal c * ∏ i, sharpNormQ D torus (g.1 i)) →
          ∀ h : sepC1Tuples D torus n, ENNReal.ofReal d ≤ supportGap D torus h.1 →
            ENNReal.ofReal |Ψ h| ≤
              ENNReal.ofReal (cuttingTheta D χ ^ n * c) * ∏ i, sharpNormQ D torus (h.1 i)
end YangMills.Construction.PeriodicSpace.Kind.CutAtRadius

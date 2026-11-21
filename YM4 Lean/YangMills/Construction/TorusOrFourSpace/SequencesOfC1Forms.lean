import YangMills.Construction.TorusOrFourSpace.ConvergenceOnSeparatedTuplesAndPartialHierarchies
import YangMills.Construction.TorusOrFourSpace.EffectiveConstantsAtEveryRadius
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (P : Params) (Y : Kind)
structure C1FormSeq (J : Sequences.PNatIndexSet) (ρ : J.carrier → ℝ≥0∞) where
  radii : RadiiTendToTop Y J ρ
  func : (j : J.carrier) → (n : ℕ) → 2 ≤ n → sepC1TuplesInBall P Y n (ρ j) → ℝ
  multilinear : ∀ j n (hn : 2 ≤ n),
    IsMultilinearOn P Y (sepC1TuplesInBall P Y n (ρ j)) (func j n hn)
  symmetric : ∀ j n (hn : 2 ≤ n),
    IsPermSymmetricOn P Y (sepC1TuplesInBall P Y n (ρ j)) (func j n hn)
namespace C1FormSeq
variable {P Y} {J : Sequences.PNatIndexSet} {ρ : J.carrier → ℝ≥0∞}
def BoundedFrom (Ψ : C1FormSeq P Y J ρ) (C : BoundFamily) (n : ℕ) (hn : 2 ≤ n)
    (R : ℝ) (k : ℤ) : Prop :=
  ∀ j : J.carrier, k ≤ (((j.1 : ℕ+) : ℕ) : ℤ) → ∀ d : ℝ, 0 < d →
    ∀ f : sepC1TuplesInBall P Y n (ρ j),
      f.1 ∈ lipTuplesSpacedInBalls P Y n d R →
        ENNReal.ofReal |Ψ.func j n hn f| ≤
          ENNReal.ofReal (C.val n d R) * ∏ i, sharpNormQ P Y (f.1 i)
end C1FormSeq
structure BoundedC1FormSeq (J : Sequences.PNatIndexSet) (ρ : J.carrier → ℝ≥0∞)
    (C : BoundFamily) extends C1FormSeq P Y J ρ where
  threshold : (n : ℕ) → 2 ≤ n → (R : ℝ) → R ∈ allowedRadii P Y → ℤ
  boundedFrom : ∀ (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (hR : R ∈ allowedRadii P Y),
    toC1FormSeq.BoundedFrom C n hn R (threshold n hn R hR)
namespace BoundedC1FormSeq
variable {P Y} {J : Sequences.PNatIndexSet} {ρ : J.carrier → ℝ≥0∞} {C : BoundFamily}
open Classical in
def thresholdAtRadius (Ψ : BoundedC1FormSeq P Y J ρ C) (θ : RadiusRatio)
    (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (_hR : 0 < R) : ℤ :=
  if h : R ∈ allowedRadii P Y then Ψ.threshold n hn R h
  else Ψ.threshold n hn (ballRadius P θ Y) (ballRadius_mem_allowedRadii P θ Y)
def IsRestrictionOf (Ψ : BoundedC1FormSeq P Y J ρ C)
    (Φ : BoundedPartialHierarchySeq P Y J ρ C) : Prop :=
  (∀ (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (hR : R ∈ allowedRadii P Y),
    Ψ.threshold n hn R hR = Φ.threshold n hn R hR) ∧
  ∀ (j : J.carrier) (n : ℕ) (hn : 2 ≤ n) (f : sepC1TuplesInBall P Y n (ρ j)),
    ∃ hf : f.1 ∈ sepLipTuplesWithin P Y n (centredBall P Y (ρ j)),
      Ψ.func j n hn f = Φ.func j n hn ⟨f.1, hf⟩
def IsHierarchyFamily (Ψ : BoundedC1FormSeq P Y J (fun _ => ∞) C) : Prop :=
  (∀ (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (hR : R ∈ allowedRadii P Y), Ψ.threshold n hn R hR = 1) ∧
  ∃ Φ : J.carrier → Hierarchy P Y, (∀ j, Φ j ∈ boundedHierarchies P Y C) ∧
    ∀ (j : J.carrier) (n : ℕ) (hn : 2 ≤ n) (f : sepC1TuplesInBall P Y n ∞),
      Ψ.func j n hn f = (Φ j).func n hn ⟨f.1, f.2.1⟩
end BoundedC1FormSeq
theorem sepC1TuplesInBall_top (n : ℕ) :
    sepC1TuplesInBall P Y n ∞ = sepC1Tuples P Y n := by
  ext f
  simp [mem_sepC1TuplesInBall_iff, centredBall]
end YangMills.Construction.PeriodicSpace.Kind

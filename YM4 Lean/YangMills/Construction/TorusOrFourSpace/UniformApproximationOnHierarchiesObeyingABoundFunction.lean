import YangMills.Construction.TorusOrFourSpace.ApproximationByMembersOfTheFamily
import YangMills.Construction.TorusOrFourSpace.EffectiveConstantsAtEveryRadius
import YangMills.Construction.TorusOrFourSpace.FactsOnTheRadiusThetaAndUnitFamilies
import YangMills.Construction.TorusOrFourSpace.HierarchiesCentredMomentsAndObeyingABoundFunction
import Mathlib
set_option autoImplicit false
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.UniformHierarchyApprox
open Kind
section Numbers
variable (D : Params) (E : Kind)
def cappedGap {n : ℕ} (f : FnTuple D E n) : ℝ :=
  (min 1 (supportGap D E f)).toReal
def tupleConstant {θ : RadiusRatio} (P : TorusPartitionChoice D θ) (C : BoundFamily)
    {n : ℕ} (f : FnTuple D E n) (r : ℝ) : ℝ :=
  effConstAt P E C n (cappedGap D E f / 3)
    (r + cappedGap D E f / 3)
def UniformOnHierarchies {θ : RadiusRatio} (P : TorusPartitionChoice D θ)
    (F : DenseChoiceFamily D E) (C : BoundFamily) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (f : FnTuple D E n) (hf : f ∈ sepC1Tuples D E n) (r : ℝ), 0 < r →
    f ∈ sepC1TuplesInBall D E n (ENNReal.ofReal r) →
    ∃ hd : 0 < cappedGap D E f,
      cappedGap D E f ≤ 1 ∧
      ENNReal.ofReal (cappedGap D E f) ≤ supportGap D E f ∧
      (∀ s : ℕ+, ∃ φ : FnTuple D E n,
        DiagonalLimits.IsFamilyApproximant D E f hf (cappedGap D E f) hd F
          (1 / ((s : ℕ) : ℝ)) φ) ∧
      0 ≤ tupleConstant D E P C f r ∧
      ∀ φ : ℕ+ → FnTuple D E n,
        (∀ s : ℕ+, DiagonalLimits.IsFamilyApproximant D E f hf (cappedGap D E f) hd F
          (1 / ((s : ℕ) : ℝ)) (φ s)) →
        (∀ s : ℕ+, (⟨n, φ s⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ F.tuplesGeTwo) ∧
        (∀ s : ℕ+, ∃ hφ : φ s ∈ sepC1Tuples D E n, ∀ Φ ∈ boundedHierarchies D E C,
          |Φ.func n hn ⟨f, hf⟩ - Φ.func n hn ⟨φ s, hφ⟩| ≤
            tupleConstant D E P C f r *
              DiagonalLimits.approxDefect D E f (1 / ((s : ℕ) : ℝ))) ∧
        Filter.Tendsto
          (fun s : ℕ+ => tupleConstant D E P C f r *
            DiagonalLimits.approxDefect D E f (1 / ((s : ℕ) : ℝ)))
          Filter.atTop (𝓝 0)
end Numbers
def TupleConstantDependence : Prop :=
  ∀ (D D' : Params) (E E' : Kind) (θ θ' : RadiusRatio) (P : TorusPartitionChoice D θ)
    (P' : TorusPartitionChoice D' θ') (C : BoundFamily) (n : ℕ), 2 ≤ n →
    ∀ (f : FnTuple D E n) (f' : FnTuple D' E' n) (r : ℝ), 0 < r →
      f ∈ sepC1TuplesInBall D E n (ENNReal.ofReal r) →
      f' ∈ sepC1TuplesInBall D' E' n (ENNReal.ofReal r) →
      supportGap D E f = supportGap D' E' f' →
      allowedRadii D E = allowedRadii D' E' →
      ballRadius D θ E = ballRadius D' θ' E' →
      thetaNumber P E = thetaNumber P' E' →
      tupleConstant D E P C f r = tupleConstant D' E' P' C f' r
def AllowedRadiiDependence : Prop :=
  ∀ (D D' : Params) (E : Kind), D.L = D'.L → D.m = D'.m → allowedRadii D E = allowedRadii D' E
def DefectDependence : Prop :=
  ∀ (D D' : Params) (E E' : Kind) (n : ℕ), 2 ≤ n →
    ∀ (f : FnTuple D E n) (f' : FnTuple D' E' n), f ∈ sepC1Tuples D E n →
      f' ∈ sepC1Tuples D' E' n → D.M = D'.M →
      (∀ l, sharpNormQ D E (f l) = sharpNormQ D' E' (f' l)) →
      ∀ s : ℕ+, DiagonalLimits.approxDefect D E f (1 / ((s : ℕ) : ℝ)) =
        DiagonalLimits.approxDefect D' E' f' (1 / ((s : ℕ) : ℝ))
def Claim : Prop :=
  (∀ (D : Params) (E : Kind) (θ : RadiusRatio) (P : TorusPartitionChoice D θ)
      (F : DenseChoiceFamily D E) (C : BoundFamily), UniformOnHierarchies D E P F C) ∧
    TupleConstantDependence ∧ AllowedRadiiDependence ∧
    RadiusThetaDependence ∧ DefectDependence
end YangMills.Construction.PeriodicSpace.UniformHierarchyApprox

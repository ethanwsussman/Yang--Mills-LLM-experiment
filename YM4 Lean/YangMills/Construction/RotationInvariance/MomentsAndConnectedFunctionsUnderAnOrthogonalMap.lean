import YangMills.Construction.EuclideanFunctionals.ElementOfTheOrthogonalGroupAsAnIsometry
import YangMills.Construction.RotationInvariance.ComplexTuplesAndPlaneData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.OrthogonalInvariance
def multiBlockPartitions (n : ℕ) : Finset (Finpartition (Finset.univ : Finset (Fin n))) :=
  (SetPartition.nonSingletonPartitions n).filter fun π => 2 ≤ π.parts.card
def MomentCumulantExpansion (S : ConnFamily) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ f : Fin n → R4 → ℝ, List.ofFn f ∈ sepN n →
    centeredAt S (List.ofFn f) =
      S.evalAt n (List.ofFn f) +
        ∑ π ∈ multiBlockPartitions n, ∏ J ∈ π.parts,
          S.evalAt J.card (List.ofFn fun k => f (J.orderEmbOfFin rfl k))
def MultiBlockPartitionSizes : Prop :=
  (∀ n : ℕ, 2 ≤ n → ∀ π ∈ multiBlockPartitions n, ∀ J ∈ π.parts,
    2 ≤ J.card ∧ J.card + 2 ≤ n) ∧
  multiBlockPartitions 2 = ∅ ∧ multiBlockPartitions 3 = ∅
def CumulantsInvariant (S : ConnFamily) (Q : EuclidMotion) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ f : Fin n → R4 → ℝ, List.ofFn f ∈ sepN n →
    S.evalAt n (List.ofFn fun l => Q.actFn (f l)) = S.evalAt n (List.ofFn f)
def MomentsInvariant (S : ConnFamily) (Q : EuclidMotion) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ X ∈ sepN n, centeredAt S (Q.actList X) = centeredAt S X
def InvariantOnFree (S : ConnFamily) (Q : EuclidMotion) : Prop :=
  ∀ X : FreeSep, centeredFnFree S (Q.actFree X) = centeredFnFree S X
def InvariantOnComplexTuples (S : ConnFamily) (Q : EuclidMotion) : Prop :=
  ∀ n : ℕ, ∀ h ∈ disjointComplexTuples n,
    centeredFnFree S (Q.actFree (complexTuple h)) =
      centeredFnFree S (complexTuple h)
def EntrywiseLinear (S : ConnFamily) : Prop :=
  ∀ (n : ℕ) (i : Fin n) (z : ℂ) (h : Fin n → R4 → ℂ) (g : R4 → ℂ),
    h ∈ disjointComplexTuples n → Function.update h i g ∈ disjointComplexTuples n →
    Function.update h i (h i + z • g) ∈ disjointComplexTuples n ∧
      centeredFnFree S (complexTuple (Function.update h i (h i + z • g))) =
        centeredFnFree S (complexTuple h) +
          z * centeredFnFree S (complexTuple (Function.update h i g))
def ZeroAtZeroEntry (S : ConnFamily) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ X ∈ sepN n, (∃ f ∈ X, ∀ x, f x = 0) → centeredAt S X = 0
def EqAtComplexification (S : ConnFamily) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ X ∈ sepN n,
    (centeredAt S X : ℂ) =
      centeredFnFree S (complexTuple (complexify X))
def MulOfComplexTuples (S : ConnFamily) : Prop :=
  ∀ (p p' : ℕ), ∀ a ∈ disjointComplexTuples p, ∀ b ∈ disjointComplexTuples p',
    (∀ l l', Disjoint (supp (a l)) (supp (b l'))) →
    centeredFnFree S
        (freeMul (complexTuple a) (complexTuple b)) =
      centeredFnFree S (complexTuple (Fin.append a b))
def OrthogonalMapStatement : Prop :=
  ∀ (c : SharpScale) (S : ConnFamily) (_ : EuclidFunctionalWithRecon c S)
    (Q : Matrix.orthogonalGroup (Fin 4) ℝ),
    (MomentCumulantExpansion S ∧ MultiBlockPartitionSizes) ∧
    (CumulantsInvariant S (EuclidMotion.ofOrthogonalMatrix Q) ↔
      MomentsInvariant S (EuclidMotion.ofOrthogonalMatrix Q)) ∧
    (CumulantsInvariant S (EuclidMotion.ofOrthogonalMatrix Q) →
      MomentsInvariant S (EuclidMotion.ofOrthogonalMatrix Q) →
      InvariantOnFree S (EuclidMotion.ofOrthogonalMatrix Q) ∧
        InvariantOnComplexTuples S (EuclidMotion.ofOrthogonalMatrix Q)) ∧
    EntrywiseLinear S ∧
    (ZeroAtZeroEntry S ∧ EqAtComplexification S ∧ MulOfComplexTuples S)
end YangMills.Construction.EuclideanFunctionals.OrthogonalInvariance

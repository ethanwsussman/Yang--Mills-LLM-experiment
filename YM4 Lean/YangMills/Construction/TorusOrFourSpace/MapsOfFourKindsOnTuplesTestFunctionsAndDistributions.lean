import YangMills.Construction.TorusOrFourSpace.FourKindsOfMapsOfSeveralPoints
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
open PeriodicLattice (SignedFrame)
namespace ExtendedTupleMap
variable {D : Params} {E : Kind} {n : ℕ+}
def IsSameKindInverse : ExtendedTupleMap D E n → ExtendedTupleMap D E n → Prop
  | ofTupleMap (.permute σ), φ => φ = ofTupleMap (.permute σ⁻¹)
  | ofTupleMap (.frameDiag w), φ => φ = ofTupleMap (.frameDiag (frameInv w))
  | ofTupleMap (.translate a), φ => φ = ofTupleMap (.translate (-a))
  | ofIsometry s _, φ => ∃ hs, φ = ofIsometry (isometryInverse D E s) hs
def sameKindInv (ψ : ExtendedTupleMap D E n) : ExtendedTupleMap D E n :=
  haveI : Nonempty (ExtendedTupleMap D E n) := ⟨ψ⟩
  Classical.epsilon ψ.IsSameKindInverse
def SameActions (ψ ψ' : ExtendedTupleMap D E n) : Prop :=
  ψ.actPts = ψ'.actPts ∧
    ∀ (Z : Type) (f : Fin (n : ℕ) → E.Pt D → Z), ψ.actFns f = ψ'.actFns f
def IsTupleMapKind (ψ : ExtendedTupleMap D E n) : Prop :=
  ∃ ψ₀ : TupleMap D E n, ψ.actPts = ψ₀.actPts
def IsAffineLift (ψ : ExtendedTupleMap D E n)
    (A : Matrix (Fin (4 * (n : ℕ))) (Fin (4 * (n : ℕ))) ℝ) (b : Coords n) : Prop :=
  ∀ x : Coords n, ψ.actPts (Tuple.proj D E x) =
    Tuple.proj D E (A.mulVec x + b)
def IsSupDistIsometry (ψ : ExtendedTupleMap D E n) : Prop :=
  Function.Bijective ψ.actPts ∧ ∀ x x', Tuple.supDist D E
    (ψ.actPts x) (ψ.actPts x') = Tuple.supDist D E x x'
def HasSameKindInv (ψ : ExtendedTupleMap D E n) : Prop :=
  ψ.IsSameKindInverse ψ.sameKindInv ∧ Function.LeftInverse ψ.sameKindInv.actPts ψ.actPts ∧
    Function.RightInverse ψ.sameKindInv.actPts ψ.actPts
def TensorCompat (ψ : ExtendedTupleMap D E n) : Prop :=
  (∀ f : Fin (n : ℕ) → E.Pt D → ℂ, Tuple.tensorProd D E (ψ.actFns f) =
    Tuple.tensorProd D E f ∘ ψ.sameKindInv.actPts) ∧
  ∀ (Z : Type) (f : Fin (n : ℕ) → E.Pt D → Z), ψ.sameKindInv.actFns (ψ.actFns f) = f
def HasOrthogonalLift (ψ : ExtendedTupleMap D E n) : Prop :=
  ∃ A ∈ Matrix.orthogonalGroup (Fin (4 * (n : ℕ))) ℝ,
    (∀ j, (Finset.univ.filter fun i => A i j ≠ 0).card ≤ 4) ∧ ∃ b, ψ.IsAffineLift A b
def HasSignedPermLift (ψ : ExtendedTupleMap D E n) : Prop :=
  ∃ A ∈ Matrix.orthogonalGroup (Fin (4 * (n : ℕ))) ℝ,
    (∀ j, ∃ i, (A i j = 1 ∨ A i j = -1) ∧ ∀ i', i' ≠ i → A i' j = 0) ∧ ∃ b, ψ.IsAffineLift A b
def CompNormLE (ψ : ExtendedTupleMap D E n) : Prop :=
  ∀ (ν : ℕ) (F : E.Tuple D n → ℂ), Tuple.IsClassC D E ν F →
    Tuple.IsClassC D E ν (F ∘ ψ.actPts) ∧
      Tuple.cNorm D E ν (F ∘ ψ.actPts) ≤
        (2 : ℝ≥0∞) ^ ν * Tuple.cNorm D E ν F ∧
      Tuple.supportT D E (F ∘ ψ.actPts) = ψ.actPts ⁻¹' Tuple.supportT D E F
def CompNormEq (ψ : ExtendedTupleMap D E n) : Prop :=
  ∀ (ν : ℕ) (F : E.Tuple D n → ℂ), Tuple.IsClassC D E ν F →
    Tuple.cNorm D E ν (F ∘ ψ.actPts) = Tuple.cNorm D E ν F ∧
      Tuple.supportT D E (F ∘ ψ.actPts) = ψ.actPts ⁻¹' Tuple.supportT D E F
def PreservesTupleClasses (ψ : ExtendedTupleMap D E n) : Prop :=
  (∀ f ∈ sepC1Tuples D E (n : ℕ), ψ.actFns f ∈ sepC1Tuples D E (n : ℕ)) ∧
    ∀ f : FnTuple D E (n : ℕ), (∀ i, IsSmoothFn D E (f i)) → ∀ i, IsSmoothFn D E (ψ.actFns f i)
def ActsOnTestFnsAndDistribs (ψ : ExtendedTupleMap D E n) : Prop :=
  ∃ h : ∀ F : Tuple.testFns D E (pairwiseDistinct D E n),
      F.1 ∘ ψ.actPts ∈ Tuple.testFns D E (pairwiseDistinct D E n),
    (∀ F G : E.Tuple D n → ℂ, (F + G) ∘ ψ.actPts = F ∘ ψ.actPts + G ∘ ψ.actPts) ∧
    (∀ (c : ℂ) (F : E.Tuple D n → ℂ), (c • F) ∘ ψ.actPts = c • (F ∘ ψ.actPts)) ∧
    ∀ T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ,
      (Tuple.IsDistrib T → Tuple.IsDistrib fun F => T ⟨_, h F⟩) ∧
      ∀ ν₀, Tuple.IsDistribOfOrderLE ν₀ T →
        Tuple.IsDistribOfOrderLE ν₀ fun F => T ⟨_, h F⟩
def InvarianceIffInv (ψ : ExtendedTupleMap D E n) : Prop :=
  (∀ (Z : Type) (Φ : sepC1Tuples D E (n : ℕ) → Z),
    ψ.InvariantFunctional Φ ↔ ψ.sameKindInv.InvariantFunctional Φ) ∧
  ∀ T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ,
    Tuple.IsDistrib T → (ψ.InvariantDistrib T ↔ ψ.sameKindInv.InvariantDistrib T)
end ExtendedTupleMap
namespace ExtendedTupleMapFacts
open ExtendedTupleMap
def FrameAndShiftAsIsometries (D : Params) (E : Kind) (n : ℕ+) : Prop :=
  (∀ w : SignedFrame, ∃ hs : IsIsometry D E (frameAct D E w),
    (ofTupleMap (.frameDiag w) : ExtendedTupleMap D E n).SameActions (ofIsometry _ hs)) ∧
  ∀ a : E.Pt D, ∃ hs : IsIsometry D E (fun y => addPt D E y a),
    (ofTupleMap (.translate a) : ExtendedTupleMap D E n).SameActions (ofIsometry _ hs)
def MainProperties : Prop :=
  ∀ (D : Params) (E : Kind) (n : ℕ+), 2 ≤ (n : ℕ) →
    FrameAndShiftAsIsometries D E n ∧
    ∀ ψ : ExtendedTupleMap D E n,
      ψ.IsSupDistIsometry ∧ ψ.HasSameKindInv ∧
      ψ.actPts '' pairwiseDistinct D E n = pairwiseDistinct D E n ∧
      ψ.TensorCompat ∧
      ψ.HasOrthogonalLift ∧
      (ψ.IsTupleMapKind ∨ E = torus → ψ.HasSignedPermLift) ∧
      ψ.CompNormLE ∧
      (ψ.IsTupleMapKind ∨ E = torus → ψ.CompNormEq) ∧
      ψ.PreservesTupleClasses ∧
      ψ.ActsOnTestFnsAndDistribs ∧
      ψ.InvarianceIffInv
end ExtendedTupleMapFacts
end YangMills.Construction.PeriodicSpace.Kind

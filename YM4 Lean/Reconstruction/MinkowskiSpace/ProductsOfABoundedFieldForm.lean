import Reconstruction.MinkowskiSpace.WightmanTheoriesOfOneHermitianScalarField
import Reconstruction.MinkowskiSpace.FunctionsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FieldForms
open MinkowskiSpace OneLoopNotation HilbertToolkit ProjectionMeasures WightmanTheory
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def fieldProductAt (P : FourBorelSet → BddOp H) (B : ℝ → BddOp H) (t : ℝ)
    {n : ℕ} (z : Fin (n + 2) → ComplexVec4) : BddOp H :=
  spectralTranslation P (z 0 - imagTimeShift t) * B t *
    (List.ofFn fun k : Fin n =>
      spectralTranslation P (z k.castSucc.succ - imagTimeShift (2 * t)) * B t).prod *
    spectralTranslation P (z (Fin.last (n + 1)) - imagTimeShift t)
theorem fieldProduct_succ_eq (P : FourBorelSet → BddOp H) (B : ℝ → BddOp H)
    {n : ℕ} (z : Fin (n + 2) → ComplexVec4) :
    fieldProduct P B (n + 1) z = fieldProductAt P B (halfMinTubeGap z) z :=
  rfl
def IsAdmissibleGap {n : ℕ} (z : Fin (n + 2) → ComplexVec4) (t : ℝ) : Prop :=
  0 < t ∧ t ≤ tubeGap (z 0) ∧ t ≤ tubeGap (z (Fin.last (n + 1))) ∧
    ∀ k : Fin n, 2 * t ≤ tubeGap (z k.castSucc.succ)
def joinAt {n n' : ℕ} (z : Fin n → ComplexVec4) (b : ComplexVec4)
    (z' : Fin n' → ComplexVec4) : Fin (n + n' + 1) → ComplexVec4 :=
  fun i => Fin.append (snocPoint z b) z' (Fin.cast (by omega) i)
def diffCoordsOfLength : (n : ℕ) → (Fin n → ComplexVec4) → Fin n → ComplexVec4
  | 0, z => z
  | _ + 1, z => diffCoords z
def successiveDiffsOfLength : (n : ℕ) → (Fin n → ComplexVec4) → Fin (n - 1) → ComplexVec4
  | 0, z => z
  | _ + 1, z => successiveDiffs z
def diffCoordsInTube (n : ℕ) : Set (Fin n → ComplexVec4) :=
  {z | diffCoordsOfLength n z ∈ tubeTuples n}
def reflectTuple {m : ℕ} (z : Fin m → ComplexVec4) : Fin m → ComplexVec4 :=
  fun k => -conjPoint (z (Fin.rev k))
def FieldProductIndepOfGap (P : FourBorelSet → BddOp H) (B : ℝ → BddOp H) :
    Prop :=
  ∀ (n : ℕ) (z : Fin (n + 2) → ComplexVec4), z ∈ tubeTuples (n + 2) →
    ∀ t t' : ℝ, IsAdmissibleGap z t → IsAdmissibleGap z t' →
      fieldProductAt P B t z = fieldProductAt P B t' z
def FieldProductTranslateEnds (P : FourBorelSet → BddOp H) (B : ℝ → BddOp H) :
    Prop :=
  ∀ (n : ℕ) (a b : ComplexVec4) (z : Fin n → ComplexVec4),
    a ∈ futureTube → z ∈ tubeTuples n → b ∈ futureTube →
    ∀ w w' : ComplexVec4, MinkowskiSpace.imPart w ∈ closedFutureCone →
      MinkowskiSpace.imPart w' ∈ closedFutureCone →
      spectralTranslation P w * fieldProduct P B (n + 1)
          (consPoint a (snocPoint z b)) * spectralTranslation P w' =
        fieldProduct P B (n + 1) (consPoint (a + w) (snocPoint z (b + w')))
def FieldProductMulJoin (P : FourBorelSet → BddOp H) (B : ℝ → BddOp H) :
    Prop :=
  ∀ (n n' : ℕ) (z : Fin n → ComplexVec4) (a a' : ComplexVec4) (z' : Fin n' → ComplexVec4),
    z ∈ tubeTuples n → a ∈ futureTube → a' ∈ futureTube → z' ∈ tubeTuples n' →
      fieldProduct P B n (snocPoint z a) *
          fieldProduct P B n' (consPoint a' z') =
        fieldProduct P B (n + n') (joinAt z (a + a') z')
def FieldProductAdjoint (P : FourBorelSet → BddOp H) (B : ℝ → BddOp H) :
    Prop :=
  ∀ (n : ℕ) (z : Fin (n + 1) → ComplexVec4), z ∈ tubeTuples (n + 1) →
    adjointOp (fieldProduct P B n z) = fieldProduct P B n (reflectTuple z)
def StateIndepOfLast (P : FourBorelSet → BddOp H) (v : H)
    (B : ℝ → BddOp H) : Prop :=
  ∀ (n : ℕ) (z : Fin n → ComplexVec4), z ∈ tubeTuples n →
    ∀ w w' : ComplexVec4, w ∈ futureTube → w' ∈ futureTube →
      fieldProduct P B n (snocPoint z w) v =
        fieldProduct P B n (snocPoint z w') v
def FieldProductNormBound (P : FourBorelSet → BddOp H) (B : ℝ → BddOp H) (p c : ℝ) :
    Prop :=
  ∀ (n : ℕ) (z : Fin (n + 1) → ComplexVec4), z ∈ tubeTuples (n + 1) →
    opNormOf (fieldProduct P B n z) ≤
      ((2 : ℝ) ^ p * c) ^ n *
        ∏ k, min 1 (tubeGap (z k)) ^ (-ceilExponent p n)
def FieldProductHolomorphic (P : FourBorelSet → BddOp H)
    (B : ℝ → BddOp H) : Prop :=
  ∀ n : ℕ, ContinuousOn (fieldProduct P B n) (tubeTuples (n + 1)) ∧
    ∀ x y : H, IsHolomorphicOnTube (m := n + 1)
      fun z => inner ℂ x (fieldProduct P B n z y)
def ExpectationsStatesHolomorphic (P : FourBorelSet → BddOp H) (v : H)
    (B : ℝ → BddOp H) : Prop :=
  ∀ n : ℕ,
    IsHolomorphicOnTube (m := n) (vacuumExpectation P v B (n + 1)) ∧
    Convex ℝ (diffCoordsInTube (n + 1)) ∧ IsOpen (diffCoordsInTube (n + 1)) ∧
    (∀ x : H, Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1)
      (coordsToTuple ⁻¹' diffCoordsInTube (n + 1))
      fun z _ => inner ℂ x (stateVector P v B (n + 1) (coordsToTuple z))) ∧
    ContinuousOn (stateVector P v B (n + 1)) (diffCoordsInTube (n + 1))
def ExpectationsStatesBounded (P : FourBorelSet → BddOp H) (v : H)
    (B : ℝ → BddOp H) (p c : ℝ) : Prop :=
  ∀ n : ℕ,
    (∀ z ∈ tubeTuples (n - 1), ‖vacuumExpectation P v B n z‖ ≤
      ((2 : ℝ) ^ p * c) ^ n *
        ∏ k, min 1 (tubeGap (z k)) ^ (-ceilExponent p n)) ∧
    ∀ z ∈ diffCoordsInTube n, ‖stateVector P v B n z‖ ≤
      ((2 : ℝ) ^ p * c) ^ n *
        ∏ k, min 1 (tubeGap (diffCoordsOfLength n z k)) ^ (-ceilExponent p n)
def StatesTranslateInner (P : FourBorelSet → BddOp H) (v : H)
    (B : ℝ → BddOp H) : Prop :=
  ∀ (n n' : ℕ) (z : Fin n → ComplexVec4) (y : Fin n' → ComplexVec4) (w : ComplexVec4),
    z ∈ diffCoordsInTube n → y ∈ diffCoordsInTube n' → MinkowskiSpace.imPart w ∈ closedFutureCone →
      spectralTranslation P w (stateVector P v B n z) =
        stateVector P v B n (fun k => z k + w) ∧
      inner ℂ v (stateVector P v B n z) =
        vacuumExpectation P v B n (successiveDiffsOfLength n z) ∧
      inner ℂ (stateVector P v B n' y) (stateVector P v B n z) =
        vacuumExpectation P v B (n' + n)
          (successiveDiffsOfLength (n' + n) (Fin.append (fun k => conjPoint (y (Fin.rev k))) z))
def ExpectationConj (P : FourBorelSet → BddOp H) (v : H)
    (B : ℝ → BddOp H) : Prop :=
  ∀ (n : ℕ) (z : Fin (n - 1) → ComplexVec4), z ∈ tubeTuples (n - 1) →
    (starRingEnd ℂ) (vacuumExpectation P v B n z) = vacuumExpectation P v B n (reflectTuple z)
def FieldProductProperties : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : FourBorelSet → BddOp H) (v : H) (B : ℝ → BddOp H) (p c : ℝ),
    IsBoundedFieldForm P v B p c →
      FieldProductIndepOfGap P B ∧
      FieldProductTranslateEnds P B ∧
      FieldProductMulJoin P B ∧
      FieldProductAdjoint P B ∧
      StateIndepOfLast P v B ∧
      FieldProductNormBound P B p c ∧
      FieldProductHolomorphic P B ∧
      ExpectationsStatesHolomorphic P v B ∧
      ExpectationsStatesBounded P v B p c ∧
      StatesTranslateInner P v B ∧
      ExpectationConj P v B
end YangMills.Construction.FieldForms

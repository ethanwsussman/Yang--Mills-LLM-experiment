import Reconstruction.Continuum.OrderedTimes
import YangMills.Construction.MinkowskiSpace.BoundedFieldForms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FieldForms
open YangMills.Construction.MinkowskiSpace YangMills.Construction.OneLoopNotation YangMills.Construction.ProjectionMeasures
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
def halfMinTubeGap {n : ℕ} (ζ : Fin (n + 1) → ComplexVec4) : ℝ :=
  (1 / 2) * Finset.univ.inf' Finset.univ_nonempty fun k => tubeGap (ζ k)
def fieldProduct (E : FourBorelSet → BddOp K) (A : ℝ → BddOp K) :
    (n : ℕ) → (Fin (n + 1) → ComplexVec4) → BddOp K
  | 0, ζ => spectralTranslation E (ζ 0)
  | n + 1, ζ =>
    spectralTranslation E (ζ 0 - imagTimeShift (halfMinTubeGap ζ)) *
      A (halfMinTubeGap ζ) *
      (List.ofFn fun k : Fin n =>
        spectralTranslation E
            (ζ k.castSucc.succ - imagTimeShift (2 * halfMinTubeGap ζ)) *
          A (halfMinTubeGap ζ)).prod *
      spectralTranslation E (ζ (Fin.last (n + 1)) - imagTimeShift (halfMinTubeGap ζ))
def snocPoint {n : ℕ} (ζ : Fin n → ComplexVec4) (ω : ComplexVec4) :
    Fin (n + 1) → ComplexVec4 :=
  Fin.snoc (α := fun _ => ComplexVec4) ζ ω
def consPoint {n : ℕ} (ω : ComplexVec4) (ζ : Fin n → ComplexVec4) :
    Fin (n + 1) → ComplexVec4 :=
  Fin.cons (α := fun _ => ComplexVec4) ω ζ
def stateVector (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) :
    (n : ℕ) → (Fin n → ComplexVec4) → K
  | 0, _ => Ω
  | n + 1, z => fieldProduct E A (n + 1) (snocPoint (diffCoords z) (imagTimeShift 1)) Ω
def vacuumExpectation (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) :
    (n : ℕ) → (Fin (n - 1) → ComplexVec4) → ℂ
  | 0, _ => 1
  | n + 1, ζ =>
    inner ℂ Ω (fieldProduct E A (n + 1)
      (consPoint (imagTimeShift 1) (snocPoint ζ (imagTimeShift 1))) Ω)
def wickDiffs {n : ℕ} (x : TestSpaces.PointTuple (n + 1)) : Fin n → ComplexVec4 :=
  successiveDiffs (wickMapTuple (tupleToComplex x))
theorem wickDiffs_mem_futureTube {n : ℕ} {x : TestSpaces.PointTuple (n + 1)}
    (hx : x ∈ TestSpaces.increasingTimes (n + 1)) (i : Fin n) :
    wickDiffs x i ∈ futureTube := by
  have hlt : x i.castSucc 3 < x i.succ 3 := hx Fin.castSucc_lt_succ
  have him : MinkowskiSpace.imPart (wickDiffs x i) =
      mkTimeSpace (x i.succ 3 - x i.castSucc 3) 0 := by
    funext μ
    fin_cases μ <;>
      simp [MinkowskiSpace.imPart, wickDiffs, successiveDiffs,
        wickMapTuple, tupleToComplex, wickMap, toComplex, mkTimeSpace,
        Fin.cons]
    all_goals rfl
  change coneGap (MinkowskiSpace.imPart (wickDiffs x i)) > 0
  rw [him]
  simpa [coneGap, spacePart, mkTimeSpace, spaceNorm] using hlt
def orderedSchwinger (E : FourBorelSet → BddOp K) (Ω : K)
    (A : ℝ → BddOp K) (n : ℕ) (x : TestSpaces.PointTuple (n + 1)) : ℂ :=
  vacuumExpectation E Ω A (n + 1) (wickDiffs x)
def ceilExponent (℘ : ℝ) (n : ℕ) : ℤ := ⌈(n : ℝ) * ℘⌉
def boundOrder (℘ : ℝ) (n : ℕ) : ℤ := (n : ℤ) * ceilExponent ℘ n + 1
end YangMills.Construction.FieldForms

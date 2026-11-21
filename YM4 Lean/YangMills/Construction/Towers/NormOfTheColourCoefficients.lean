import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace PauliCoefficientNorm
open YangMills.Construction.Matrices.GroupLieProduct (tracelessFunctions)
open YangMills.Construction.PeriodicOperators (PeriodicData descendFn colourEdges colourFaces
  colourVertices shiftEdge shiftFace intShift)
def halfTraceInner (X Y : Matrices.ComplexMatrix2.traceless) : ℂ :=
  Matrices.ComplexMatrix2.halfTrace
    (Matrix.conjTranspose (X : Matrices.ComplexMatrix2) * (Y : Matrices.ComplexMatrix2))
def HalfTraceInnerIsCoordInner : Prop :=
  (∀ (X Y : Matrices.ComplexMatrix2.traceless) (x y : Fin 3 → ℂ),
    (X : Matrices.ComplexMatrix2) = ∑ a, x a • Matrices.ComplexMatrix2.pauliFamily a →
      (Y : Matrices.ComplexMatrix2) = ∑ a, y a • Matrices.ComplexMatrix2.pauliFamily a →
        halfTraceInner X Y = ∑ a, conj (x a) * y a) ∧
  (∀ X : Matrices.ComplexMatrix2.traceless, pauliNorm X = Real.sqrt (halfTraceInner X X).re) ∧
  (∃ c : InnerProductSpace.Core ℂ Matrices.ComplexMatrix2.traceless,
    ∀ X Y : Matrices.ComplexMatrix2.traceless, c.inner X Y = halfTraceInner X Y) ∧
  (∀ a b : Fin 3, halfTraceInner (OneLoop.pauliBasis a)
    (OneLoop.pauliBasis b) = if a = b then 1 else 0) ∧
  ∀ X Y : Matrices.ComplexMatrix2.traceless,
    ‖OneLoop.traceForm X Y‖ ≤ pauliNorm X * pauliNorm Y
def OperatorNormComparison : Prop :=
  (∀ X : Matrices.ComplexMatrix2.traceless,
    pauliNorm X ≤ Matrices.ComplexMatrix2.operatorNorm X ∧
      Matrices.ComplexMatrix2.operatorNorm X ≤ Real.sqrt 2 * pauliNorm X) ∧
  ∀ (z : ℂ) (X : Matrices.ComplexMatrix2), X ∈ Matrices.ComplexMatrix2.hermitianTraceless →
    Matrices.ComplexMatrix2.operatorNorm (z • X) = pauliNorm (z • X) ∧
      pauliNorm (z • X) = ‖z‖ * Matrices.ComplexMatrix2.operatorNorm X
section Places
variable {σ : Type}
theorem apply_mem_traceless {f : σ → Matrices.ComplexMatrix2} (hf : f ∈ tracelessFunctions σ)
    (x : σ) : f x ∈ Matrices.ComplexMatrix2.traceless :=
  Submodule.mem_pi.1 hf x (Set.mem_univ x)
def pointwisePairing {f g : σ → Matrices.ComplexMatrix2} (hf : f ∈ tracelessFunctions σ)
    (hg : g ∈ tracelessFunctions σ) (x : σ) : ℂ :=
  OneLoop.traceForm ⟨f x, apply_mem_traceless hf x⟩ ⟨g x, apply_mem_traceless hg x⟩
def FiniteLatticeFormulas (a : ℝ) (σ : Type) : Prop :=
  ∀ (f g : σ → Matrices.ComplexMatrix2) (hf : f ∈ tracelessFunctions σ)
    (hg : g ∈ tracelessFunctions σ),
    meshNorm a f ^ 2 = a ^ 4 * ∑ᶠ x, pauliNorm (f x) ^ 2 ∧
    meshPairing a f g = ((a ^ 4 : ℝ) : ℂ) * ∑ᶠ x, pointwisePairing hf hg x
def InfiniteLatticeFormulas (a : ℝ) (σ : Type) : Prop :=
  ∀ (f g : σ → Matrices.ComplexMatrix2) (hf : f ∈ tracelessFunctions σ)
    (hg : g ∈ tracelessFunctions σ),
    ((Summable fun p : Fin 3 × σ => ‖toPauliCoeffs f p‖ ^ 2) ↔
      Summable fun x => pauliNorm (f x) ^ 2) ∧
    ((Summable fun p : Fin 3 × σ => ‖toPauliCoeffs f p‖ ^ 2) →
      meshNorm a f ^ 2 = a ^ 4 * ∑' x, pauliNorm (f x) ^ 2) ∧
    ((Summable fun p : Fin 3 × σ => ‖toPauliCoeffs f p * toPauliCoeffs g p‖) →
      (Summable fun x => ‖pointwisePairing hf hg x‖) ∧
      meshPairing a f g = ((a ^ 4 : ℝ) : ℂ) * ∑' x, pointwisePairing hf hg x)
abbrev OrbitSpace (act : (Fin 4 → ℤ) → σ → σ) : Type :=
  Quot fun x y : σ => ∃ t : Fin 4 → ℤ, y = act t x
def IsTranslationPeriodic (act : (Fin 4 → ℤ) → σ → σ) (f : σ → Matrices.ComplexMatrix2) : Prop :=
  ∀ (t : Fin 4 → ℤ) (x : σ), f (act t x) = f x
def PeriodicFormulas (a : ℝ) (act : (Fin 4 → ℤ) → σ → σ) (I : PeriodicData)
    (read : (σ → Matrices.ComplexMatrix2) → I.Carrier → ℂ) : Prop :=
  ∀ (f g : σ → Matrices.ComplexMatrix2) (hf : f ∈ tracelessFunctions σ)
    (hg : g ∈ tracelessFunctions σ),
    IsTranslationPeriodic act f → IsTranslationPeriodic act g →
      PeriodicOperators.wNorm (I.quotWeight 1) (descendFn I (read f)) ^ 2 =
        a ^ 4 * ∑ᶠ c : OrbitSpace act, pauliNorm (f (Quot.out c)) ^ 2 ∧
      PeriodicOperators.wPairing (I.quotWeight 1) (descendFn I (read f))
          (descendFn I (read g)) =
        ((a ^ 4 : ℝ) : ℂ) * ∑ᶠ c : OrbitSpace act, pointwisePairing hf hg (Quot.out c)
end Places
def Claim : Prop :=
  HalfTraceInnerIsCoordInner ∧ OperatorNormComparison ∧
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ, j ≤ k →
    (∀ n : ℕ, 0 < n →
      FiniteLatticeFormulas (meshAt L k j) (Vertex L n k j) ∧
      FiniteLatticeFormulas (meshAt L k j) (PositiveEdge L n k j) ∧
      FiniteLatticeFormulas (meshAt L k j) (Face L n k j)) ∧
    InfiniteLatticeFormulas (meshAt L k j) (FullSpace.Vertex L k j) ∧
    InfiniteLatticeFormulas (meshAt L k j) (PeriodicOperators.PosEdge L k j) ∧
    InfiniteLatticeFormulas (meshAt L k j) (FullSpace.Face L k j) ∧
    PeriodicFormulas (meshAt L k j)
      (fun t x => FullSpace.vertexImage (intShift t) x) (colourVertices L k j) toPauliCoeffs ∧
    PeriodicFormulas (meshAt L k j) shiftEdge (colourEdges L k j) toPauliCoeffs ∧
    PeriodicFormulas (meshAt L k j) shiftFace (colourFaces L k j) toPauliCoeffs
end PauliCoefficientNorm
end Tower
end YangMills.Construction
end

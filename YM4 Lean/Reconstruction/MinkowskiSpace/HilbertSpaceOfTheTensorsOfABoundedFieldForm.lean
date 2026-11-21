import Reconstruction.MinkowskiSpace.VectorsAtRealPointsDefs
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.FieldFormHilbert
def poincareActR4 (g : WightmanTheory.PoincareElt) (f : (Fin 4 → ℝ) → ℂ) : (Fin 4 → ℝ) → ℂ :=
  fun x => MinkowskiSpace.poincarePullback g.1 (WightmanTheory.asOnePointFn f) fun _ => x
section Form
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp K) (Ω : K)
  (A : ℝ → OneLoopNotation.BddOp K)
def tensorHilbert : Submodule ℂ K := (RealPointVectors.tensorDomain E Ω A).topologicalClosure
theorem coe_tensorHilbert :
    (tensorHilbert E Ω A : Set K) = RealPointVectors.tensorDomainClosure E Ω A := by
  ext χ
  simp only [tensorHilbert, Submodule.topologicalClosure_coe]
  rw [mem_closure_iff_seq_limit]
  rfl
instance : CompleteSpace (tensorHilbert E Ω A) :=
  Submodule.topologicalClosure.completeSpace (RealPointVectors.tensorDomain E Ω A)
def tensorDomainIn : Submodule ℂ (tensorHilbert E Ω A) :=
  (RealPointVectors.tensorDomain E Ω A).comap (tensorHilbert E Ω A).subtype
def tensorVec {k : ℕ} (f : Fin k → WightmanTheory.TestFn) : tensorHilbert E Ω A :=
  ⟨RealPointVectors.testState E Ω A k (RealPointVectors.tensorVal fun i => (f i).1),
    Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨k, fun i => (f i).1, fun i => (f i).2, rfl⟩)⟩
def IsFieldOp (D : Submodule ℂ (tensorHilbert E Ω A)) (f : WightmanTheory.TestFn)
    (L : D →ₗ[ℂ] D) : Prop :=
  ∀ (k : ℕ) (h : Fin k → WightmanTheory.TestFn) (hD : tensorVec E Ω A h ∈ D),
    ((L ⟨_, hD⟩ : D) : tensorHilbert E Ω A) =
      tensorVec E Ω A (Fin.cons f h : Fin (k + 1) → WightmanTheory.TestFn)
def IsPoincareOp (g : WightmanTheory.PoincareElt)
    (U : FormsOperators.UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A)) : Prop :=
  ∀ (k : ℕ) (f : Fin k → WightmanTheory.TestFn),
    ((U (tensorVec E Ω A f) : tensorHilbert E Ω A) : K) =
      RealPointVectors.testState E Ω A k
        (RealPointVectors.tensorVal fun i => poincareActR4 g (f i).1)
def IsMeasureRestriction
    (F : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp (tensorHilbert E Ω A)) : Prop :=
  ∀ (Δ : ProjectionMeasures.FourBorelSet) (χ : tensorHilbert E Ω A),
    ((F Δ χ : tensorHilbert E Ω A) : K) = E Δ χ
end Form
end YangMills.Construction.FieldFormHilbert

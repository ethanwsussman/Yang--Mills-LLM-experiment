import YangMills.Construction.RotationInvariance.ApertureTimeGapsAndComplexAnalysisInThePlane
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus (scalarEquiv)
noncomputable section
namespace YangMills.Construction
namespace ForwardTube
def vecRe (w : ℂ × ℂ) : RealPlane := !₂[w.1.re, w.2.re]
theorem vecRe_embedPlane (x : RealPlane) : vecRe (embedPlane x) = x := by
  ext k
  fin_cases k <;> simp [vecRe, embedPlane]
def embedPlaneTuple {q : ℕ} (x : Fin q → RealPlane) : Fin q → ℂ × ℂ := fun k => embedPlane (x k)
def tupleRe {q : ℕ} (z : Fin q → ℂ × ℂ) : Fin q → RealPlane :=
  fun k => vecRe (z k)
def scalarPairTupleEquiv (q : ℕ) : ℂ × (Fin q → ℂ × ℂ) ≃ Coordinates.ComplexCoordinates (1 + q * 2) :=
  (Equiv.prodCongr scalarEquiv (pairTupleEquiv q)).trans
    ((Equiv.sumArrowEquivProdArrow (Fin 1) (Fin (q * 2)) ℂ).symm.trans
      (Equiv.arrowCongr finSumFinEquiv (Equiv.refl ℂ)))
def IsHolomorphicScalarPairMap {q q' : ℕ} (U : Set (ℂ × (Fin q → ℂ × ℂ)))
    (f : ℂ × (Fin q → ℂ × ℂ) → Fin q' → ℂ × ℂ) : Prop :=
  Coordinates.ComplexCoordinates.IsHolomorphicVia (scalarPairTupleEquiv q) (pairTupleEquiv q') U f
def IsRealAnalyticTupleFun {q : ℕ} (U : Set (Fin q → RealPlane))
    (f : (Fin q → RealPlane) → ℂ) : Prop :=
  Coordinates.ComplexCoordinates.IsRealAnalyticIn (pairTupleEquiv q '' (embedPlaneTuple '' U))
    fun z => scalarEquiv (f (tupleRe ((pairTupleEquiv q).symm z)))
end ForwardTube
namespace RealPlane
def injectiveTuplesIn (S : Set RealPlane) (n : ℕ) : Set (Fin n → RealPlane) :=
  {x | x ∈ injectivePointTuples n ∧ ∀ k, x k ∈ S}
def openLeftHalf : Set RealPlane := {x | x 0 < 0}
variable {n : ℕ}
def TimesCoincide (x : Fin n → RealPlane) : Prop := ∃ k l, k ≠ l ∧ x k 0 = x l 0
def AbscissasCoincide (x : Fin n → RealPlane) : Prop := ∃ k l, k ≠ l ∧ x k 1 = x l 1
def labelLinComb (c : ℝ) (u : realLabels) (c' : ℝ) (u' : realLabels) : realLabels :=
  ⟨c • u.1 + c' • u'.1, (u.2.1.const_smul c).add (u'.2.1.const_smul c'),
    (u.2.2.smul_left (f := fun _ => c)).add (u'.2.2.smul_left (f := fun _ => c'))⟩
def IsMultilinearLabels (g : (Fin n → realLabels) → ℂ) : Prop :=
  ∀ (φ : Fin n → realLabels) (k : Fin n) (c c' : ℝ) (u u' : realLabels),
    g (Function.update φ k (labelLinComb c u c' u')) =
      c * g (Function.update φ k u) + c' * g (Function.update φ k u')
end RealPlane
end YangMills.Construction
end

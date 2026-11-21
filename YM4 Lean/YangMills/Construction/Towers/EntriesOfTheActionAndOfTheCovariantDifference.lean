import YangMills.Construction.Towers.TheTwoOperatorFunctionsAsFunctionsOfValues
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def vertexBasisFunction {L k j : ℕ} (a : Fin 3) (x : Vertex L k j) :
    Vertex L k j → Matrices.ComplexMatrix2 :=
  open Classical in fun y => if y = x then Matrices.ComplexMatrix2.pauliFamily a else 0
namespace FieldValueFunctions.LocalComponents
open PeriodicOperators
open FaceEdgeFinsets.Unbounded (facesMeeting)
variable {L k : ℕ}
def edgesOfFacesMeeting (e' e : Edge L k 0) : Set (Edge L k 0) :=
  {c | ∃ p ∈ facesMeeting ({e', e} : Set (Edge L k 0)), c ∈ faceEdges p}
def hessianEntry (L k : ℕ) (hL : 0 < L) (a' : Fin 3) (e' : PositiveEdge (meshAt L k 0))
    (a : Fin 3) (e : PositiveEdge (meshAt L k 0)) : ((fieldPeriodicData L k hL).Carrier → ℂ) → ℂ :=
  fun f => complexActionHessian (gaugeFieldOfCoeffs hL f) (basisForm a' e') (basisForm a e)
def covDiffEntry (L k : ℕ) (hL : 0 < L) (a' : Fin 3) (e' : PositiveEdge (meshAt L k 0))
    (a : Fin 3) (x : Vertex L k 0) : ((fieldPeriodicData L k hL).Carrier → ℂ) → ℂ :=
  fun f => pauliCoeff a'
    (covDiff (gaugeFieldOfCoeffs hL f) (vertexBasisFunction a x) e'.1)
def bracketEntry (L k : ℕ) (hL : 0 < L) (a' : Fin 3) (e' : PositiveEdge (meshAt L k 0))
    (a : Fin 3) (x : Vertex L k 0) (c : Fin 3) (e : PositiveEdge (meshAt L k 0)) :
    ((fieldPeriodicData L k hL).Carrier → ℂ) → ℂ :=
  fun f => pauliCoeff a'
    (levelBracketTerm (gaugeFieldOfCoeffs hL f) (vertexBasisFunction a x)
      (basisForm c e) e'.1)
def EntriesAreLocalAndEntire : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ,
    (∀ (a' a : Fin 3) (e' e : PositiveEdge (meshAt L k 0)),
      ((¬ ∃ p : Face L k 0, e'.1 ∈ faceEdges p ∧ e.1 ∈ faceEdges p) →
        ∀ f, hessianEntry L k hL a' e' a e f = 0) ∧
      ∀ ρ : ℝ, 0 < ρ → HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
        (backgroundCoords L k hL (edgesOfFacesMeeting e'.1 e.1))
        (hessianEntry L k hL a' e' a e)) ∧
    (∀ (a' a : Fin 3) (e' : PositiveEdge (meshAt L k 0)) (x : Vertex L k 0),
      (x ≠ e'.1.initial → x ≠ e'.1.terminal → ∀ f, covDiffEntry L k hL a' e' a x f = 0) ∧
      ∀ ρ : ℝ, 0 < ρ → HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
        (backgroundCoords L k hL {e'.1}) (covDiffEntry L k hL a' e' a x)) ∧
    ∀ (a' a c : Fin 3) (e' e : PositiveEdge (meshAt L k 0)) (x : Vertex L k 0)
      (ρ : ℝ), 0 < ρ → HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
        (backgroundCoords L k hL {e'.1}) (bracketEntry L k hL a' e' a x c e)
end FieldValueFunctions.LocalComponents
end YangMills.Construction.Tower.FullSpace
end

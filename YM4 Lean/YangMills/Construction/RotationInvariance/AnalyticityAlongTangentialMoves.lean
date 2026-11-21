import YangMills.Construction.RotationInvariance.ComplexTuplesAndPlaneData
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror YangMills.Construction.RealPlane
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TangentialAnalyticity
def tangentialNorm (μ : Fin 4) (u : R4) : ℝ := ∑ ν ∈ Finset.univ.erase μ, |u ν|
def stripOf (δ s : ℝ) : Set ℂ := {r | |r.im| * s < 2 * δ}
def translatedTuple {q : ℕ} (b : Fin q → R4 → ℂ) (u : R4) (r : ℝ) : FreeSep :=
  (EuclidMotion.transl (r • u)).actFree (complexTuple b)
def valueAlongShift (S : ConnFamily) {p q : ℕ} (a : Fin p → R4 → ℂ) (b : Fin q → R4 → ℂ)
    (u : R4) (r : ℝ) : ℂ :=
  centeredFnFree S (freeMul (complexTuple a) (translatedTuple b u r))
def shiftedComponents {p q : ℕ} (a : Fin p → R4 → ℂ) (b : Fin q → R4 → ℂ) (u : R4) (r : ℝ) :
    Fin (p + q) → R4 → ℂ :=
  Fin.append a fun k => (EuclidMotion.transl (r • u)).actFn (b k)
def MulIsAppendedTuple (S : ConnFamily) {p q : ℕ} (a : Fin p → R4 → ℂ)
    (b : Fin q → R4 → ℂ) (u : R4) (r : ℝ) : Prop :=
  MulDefined (complexTuple a) (translatedTuple b u r) ∧
    shiftedComponents a b u r ∈ disjointComplexTuples (p + q) ∧
    valueAlongShift S a b u r =
      centeredFnFree S (complexTuple (shiftedComponents a b u r))
def HasHolomorphicExtension (O : Set ℂ) (f : ℝ → ℂ) : Prop :=
  ∃ G : ℂ → ℂ, YangMills.Construction.ForwardTube.HolomorphicOnComplex O G ∧ ∀ r : ℝ, G r = f r
def IsRealAnalyticOnReal (f : ℝ → ℂ) : Prop :=
  YangMills.Construction.Coordinates.ComplexCoordinates.IsRealAnalyticIn (N := 1) (N' := 1)
    (YangMills.Construction.Coordinates.ComplexCoordinates.realLocus 1)
    fun z _ => f (z 0).re
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S),
    σ.ConeCondition →
    ∀ (μ : Fin 4) (c δ : ℝ), 0 < δ →
    ∀ (p q : ℕ), 1 ≤ p → 1 ≤ q →
    ∀ a ∈ disjointComplexTuples p, ∀ b ∈ disjointComplexTuples q,
      (∀ l, supp (a l) ⊆ {x | x μ < c - δ}) →
      (∀ k, supp (b k) ⊆ {x | c + δ < x μ}) →
    ∀ u : R4, u μ = 0 →
      (∀ r : ℝ, MulIsAppendedTuple S a b u r) ∧
      HasHolomorphicExtension (stripOf δ (tangentialNorm μ u)) (valueAlongShift S a b u) ∧
      (u = 0 → stripOf δ (tangentialNorm μ u) = Set.univ) ∧
      IsRealAnalyticOnReal (valueAlongShift S a b u)
end YangMills.Construction.EuclideanFunctionals.TangentialAnalyticity
end

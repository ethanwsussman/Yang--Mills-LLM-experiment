import YangMills.Construction.ComplexAnalysis.BanachValuedHolomorphy
import YangMills.Construction.EuclideanFunctionals.StandingDataOfThePlane
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMaps
import YangMills.Construction.RotationInvariance.PencilsOfThePlane
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus (scalarEquiv)
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace EuclideanFunctionals
structure PlaneDataWithAperture (m : SharpScale) (S : ConnFamily) where
  base : PlaneStandingData m S
  angle : RealPlane.openingAngles
end EuclideanFunctionals
namespace ForwardTube
def pairTupleEquiv (p : ℕ) : (Fin p → ℂ × ℂ) ≃ Coordinates.ComplexCoordinates (p * 2) :=
  (Equiv.piCongrRight fun _ => (finTwoArrowEquiv ℂ).symm).trans
    ((Equiv.curry (Fin p) (Fin 2) ℂ).symm.trans
      (Equiv.arrowCongr finProdFinEquiv (Equiv.refl ℂ)))
theorem pairTupleEquiv_apply_fst {p : ℕ} (w : Fin p → ℂ × ℂ) (k : Fin p) :
    pairTupleEquiv p w (finProdFinEquiv (k, 0)) = (w k).1 := by
  simp [pairTupleEquiv, Equiv.arrowCongr, Equiv.curry]
theorem pairTupleEquiv_apply_snd {p : ℕ} (w : Fin p → ℂ × ℂ) (k : Fin p) :
    pairTupleEquiv p w (finProdFinEquiv (k, 1)) = (w k).2 := by
  simp [pairTupleEquiv, Equiv.arrowCongr, Equiv.curry]
def HolomorphicOnTuples {p : ℕ} (U : Set (Fin p → ℂ × ℂ)) (g : (Fin p → ℂ × ℂ) → ℂ) : Prop :=
  Coordinates.ComplexCoordinates.IsHolomorphicVia (pairTupleEquiv p) scalarEquiv U g
def HolomorphicOnComplex (U : Set ℂ) (g : ℂ → ℂ) : Prop :=
  Coordinates.ComplexCoordinates.IsHolomorphicVia scalarEquiv scalarEquiv U g
def Entire (g : ℂ → ℂ) : Prop := HolomorphicOnComplex Set.univ g
def HolomorphicVectorOnTuples {p : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (U : Set (Fin p → ℂ × ℂ)) (g : (Fin p → ℂ × ℂ) → E) : Prop :=
  BanachValued.IsHolomorphicOnOpen (pairTupleEquiv p '' U) (g ∘ (pairTupleEquiv p).symm)
def realLocus {p : ℕ} (K : Set (Fin p → ℂ × ℂ)) : Set (Fin p → ℂ × ℂ) :=
  {w | w ∈ K ∧ ∃ z : Fin p → RealPlane, ∀ k, w k = embedPlane (z k)}
end ForwardTube
namespace RealPlane
def minTime (K : Set RealPlane) : ℝ := sInf ((fun z : RealPlane => z 0) '' K)
def maxTime (K : Set RealPlane) : ℝ := sSup ((fun z : RealPlane => z 0) '' K)
def TimeSeparated {n : ℕ} (δ : ℝ) (g : Fin n → RealPlane → ℂ) : Prop :=
  (∀ k, Continuous (g k)) ∧ (∀ k, HasCompactSupport (g k)) ∧ (∀ k, g k ≠ 0) ∧
    ∀ (k : ℕ) (hk : k + 1 < n),
      δ < minTime (tsupport (g ⟨k + 1, hk⟩)) -
        maxTime (tsupport (g ⟨k, Nat.lt_of_succ_lt hk⟩))
def profileIntegrand {n : ℕ} (a : Fin n → RealPlane → ℂ)
    (F : (Fin n → RealPlane) → ℂ) : (Fin n → RealPlane) → ℂ :=
  (Set.univ.pi fun k => tsupport (a k)).indicator fun z => (∏ k, a k (z k)) * F z
def profileIntegral {n : ℕ} (a : Fin n → RealPlane → ℂ)
    (F : (Fin n → RealPlane) → ℂ) : ℂ :=
  ∫ z, profileIntegrand a F z
end RealPlane
end YangMills.Construction
end

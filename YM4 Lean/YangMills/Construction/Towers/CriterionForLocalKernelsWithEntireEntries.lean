import YangMills.Construction.Towers.EntireCoordinatesOfAField
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.EntireLocalCriterion
open PeriodicOperators
open Tower.FullSpace.EntireDependence
open TorusMetric (euclidNormVec)
def Criterion : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ (k : ℕ) (I I' : PeriodicData)
    (T : ((Tower.remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ),
    (∀ j, ∃ c : (Tower.remainderIndex L k).Carrier,
      (Tower.remainderIndex L k).pos c = I'.pos j) →
    (∀ a j i, ¬ euclidNormVec (I.pos i - I'.pos j) ≤ 2 * Tower.finestMesh L k →
      T a j i = 0) →
    (∀ j i, ∃ S : Finset (Tower.remainderIndex L k).Carrier,
      (∀ c ∈ S, euclidNormVec ((Tower.remainderIndex L k).pos c - I'.pos j) ≤
        2 * Tower.finestMesh L k) ∧ IsEntireOn (Tower.remainderIndex L k) S fun a => T a j i) →
    (∀ a (n : Fin 4 → ℤ) j i,
      T (shiftField (Tower.remainderIndex L k) n a) (I'.translate n j) (I.translate n i) = T a j i) →
    IsLocalAllRadii L k I I' T
end YangMills.Construction.Tower.FullSpace.EntireLocalCriterion
end

import YangMills.Construction.TorusOrFourSpace.OriginClosedBallsAndBallsAboutTheOrigin
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefinedProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.EuclideanCase
open Kind TorusMetric
variable (D : Params)
theorem quotDist_euclidean_eq (y y' : Fin 4 → ℝ) :
    Kind.quotDist D Kind.euclidean y y' = euclidNormVec (y - y') := by apply _root_.YangMills.Construction.PeriodicSpace.QuotientGeometry.quotDist_euclidean <;> assumption
theorem closedBallAbout_euclidean (x : Fin 4 → ℝ) (R : ℝ) :
    Kind.closedBallAbout D Kind.euclidean x R = {y : Fin 4 → ℝ | euclidNormVec (y - x) ≤ R} := by
  ext (y : Fin 4 → ℝ)
  change Kind.quotDist D Kind.euclidean y x ≤ R ↔ euclidNormVec (y - x) ≤ R
  rw [quotDist_euclidean_eq]
end YangMills.Construction.PeriodicSpace.EuclideanCase
end

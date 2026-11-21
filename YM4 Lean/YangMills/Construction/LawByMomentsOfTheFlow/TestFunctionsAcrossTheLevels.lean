import YangMills.Construction.ClusterExpansionOfAStep.FlowOfTheExpansion
import YangMills.Construction.ClusterExpansionOfAStep.TheExpansionReturns
import YangMills.Construction.LawByMomentsOfTheFlow.TestFunctionsOnTheSpace
import YangMills.Construction.ResponseInTheExpansion.SeveralSupportsInOneStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
structure AdmissibleStep (ℓ : TorusLumps.StepParameters) : Prop where
  admissible : ℓ.Admissible
  returns : StepReturn.ExpansionReturnsAt ℓ
  wilson_hasExpansion : ∀ β : ℝ, ℓ.y₁ ≤ β → TorusLumps.HasExpansion ℓ 0 β (TorusLumps.wilsonWeight β)
def circleRep (c v : ℝ) : ℝ := v - c * round (v / c)
def barycenterCoord {m : ℕ} (p : TorusFields.TorusPlaquette m) (a : Fin 4) : ℝ :=
  ((p.1 a).val : ℝ) + (if a = p.2.1 then 1 / 2 else 0) + (if a = p.2.2 then 1 / 2 else 0)
structure LevelData (k : ℕ) where
  fn : Fin k → TestFunctions.EuclideanFourSpace → ℝ
  windowLevel : ℕ
  scaleLevel : ℕ
  sideExponent : ℕ
  center : Fin 4 → ℝ
variable {k : ℕ}
def LevelData.period (P : LevelData k) (L : ℕ) : ℕ := 2 * L ^ P.sideExponent
def LevelData.sideAt (P : LevelData k) (L t : ℕ) : ℕ := P.period L * L ^ (P.windowLevel - t)
instance (P : LevelData k) (L t : ℕ) [NeZero L] : NeZero (P.sideAt L t) :=
  ⟨mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (NeZero.ne L))) (pow_ne_zero _ (NeZero.ne L))⟩
def LevelData.testWeight (P : LevelData k) (L : ℕ) (i : Fin k) (m : ℕ) : WeightedResponses.PlaquetteWeight m := fun p =>
  P.fn i (WithLp.toLp 2 fun a => (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ P.scaleLevel *
    circleRep (P.period L) (barycenterCoord p a / (L : ℝ) ^ P.windowLevel - P.center a))
def LevelData.supportSites (P : LevelData k) (L : ℕ) [NeZero L] (t : ℕ) (i : Fin k) :
    Finset (TorusFields.TorusSite (P.sideAt L t)) :=
  ResponseInTheExpansion.weightSupportSites L t (P.sideAt L t)
    (P.testWeight L i (WeightedResponses.fineSide L t (P.sideAt L t)))
def minSeparation {N : ℕ} [NeZero N] (A : Fin k → Finset (TorusFields.TorusSite N)) : ℕ :=
  sInf {e | ∃ i j, i ≠ j ∧ ∃ y ∈ TorusLumps.thickening 2 (A i), ∃ y' ∈ TorusLumps.thickening 2 (A j),
    TorusFields.supDist y y' = e}
def LevelData.separation (P : LevelData k) (L : ℕ) [NeZero L] (u : ℕ) : ℕ :=
  minSeparation fun i => P.supportSites L (u + 1) i
def LevelData.SeparatedBelow (P : LevelData k) (ℓ : TorusLumps.StepParameters) (β : ℝ) (t : ℕ) : Prop :=
  ∀ u < t, 2 ^ 10 * TorusLumps.clusterRange (TorusLumps.couplingFlow ℓ β u).1 ≤ P.separation ℓ.side u ∧
    8 < P.separation ℓ.side u
open Classical in
def LevelData.separationLevel (P : LevelData k) (ℓ : TorusLumps.StepParameters) (β : ℝ) : ℕ :=
  Nat.findGreatest (P.SeparatedBelow ℓ β) P.windowLevel
def LevelData.distFromCenter (P : LevelData k) (L t : ℕ) (y : TorusFields.TorusSite (P.sideAt L t)) : ℝ :=
  ⨆ a : Fin 4, |circleRep (P.period L) (((y a).val : ℝ) * (L : ℝ) ^ t / (L : ℝ) ^ P.windowLevel - P.center a)| *
    (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ t
structure LevelData.Admissible (P : LevelData k) (L : ℕ) (R d : ℝ) : Prop where
  isTestFamily : TestFunctions.IsSeparatedLipschitzFamily R d P.fn
  scaleLevel_le : P.scaleLevel ≤ P.windowLevel
  support_small : R * (L : ℝ) ^ P.scaleLevel ≤ (P.period L : ℝ) / 4 * (L : ℝ) ^ P.windowLevel
  exists_ne_zero : ∀ i, ∃ p : WeightedResponses.OrientedPlaquette (P.period L * L ^ P.windowLevel),
    P.testWeight L i _ p.1 ≠ 0
end YangMills.Construction.LevelTestFunctions
end

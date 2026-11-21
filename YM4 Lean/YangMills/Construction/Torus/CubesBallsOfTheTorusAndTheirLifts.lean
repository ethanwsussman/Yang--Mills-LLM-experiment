import YangMills.Construction.Lattice.PlaquettesInAxisPlanes
import YangMills.Construction.Torus.CubesCellsNeighbourhoodsAndLiftsOfBalls
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TorusCubesAndBalls
open PeriodicLattice TorusMetric TestFunctions TorusMeasure CubesAndBallLifts
variable (s : Conventions.StandingParameters)
def TranslatedCubesTileTorus : Prop :=
  ∀ v : s.Torus,
    (∀ y : PeriodicLattice.Site s.L s.m ((s.K : ℕ) : ℤ),
      IsMeasurableTorusSet (translatedSiteCube y v) ∧
      TorusMeasure.torusVolume (translatedSiteCube y v) = PlaquetteSupports.latticeSpacing s ^ 4 ∧
      cellAround ((y : s.Torus) + v) ⊆ translatedSiteCube y v) ∧
    (⋃ y : PeriodicLattice.Site s.L s.m ((s.K : ℕ) : ℤ), translatedSiteCube y v) = univ ∧
    ∀ y y' : PeriodicLattice.Site s.L s.m ((s.K : ℕ) : ℤ), y ≠ y' →
      TorusMeasure.torusVolume (translatedSiteCube y v ∩ translatedSiteCube y' v) = 0
def TranslatedCubeSpecialCases : Prop :=
  (∀ y : PeriodicLattice.Site s.L s.m ((s.K : ℕ) : ℤ), translatedSiteCube y 0 = siteCube y) ∧
  ∀ (y : PeriodicLattice.Site s.L s.m ((s.K : ℕ) : ℤ)) (P : AxisPlane),
    (fun x => TorusMeasure.addVec s x
        (PlaquetteSupports.latticeSpacing s • planeCenterOffset P)) '' siteCube y =
      translatedSiteCube y (proj s (PlaquetteSupports.latticeSpacing s • planeCenterOffset P))
def CubePointsNearCenter : Prop :=
  (∀ (y : PeriodicLattice.Site s.L s.m ((s.K : ℕ) : ℤ)), ∀ x ∈ siteCube y,
    pointDist x (y : s.Torus) ≤ PlaquetteSupports.latticeSpacing s) ∧
  ∀ y : Fin 4 → ℝ, ∀ t ∈ (fun τ => y + τ) '' Set.pi univ fun _ : Fin 4 =>
      Icc (-(PlaquetteSupports.latticeSpacing s / 2))
        (PlaquetteSupports.latticeSpacing s / 2),
    euclidNormVec (t - y) ≤ PlaquetteSupports.latticeSpacing s
def meshGrid : Set (Fin 4 → ℝ) :=
  {t | ∃ k : Fin 4 → ℤ, ∀ μ, t μ = PlaquetteSupports.latticeSpacing s * (k μ : ℝ)}
def HalfOpenCubesPartition : Prop :=
  (meshGrid s).PairwiseDisjoint (halfOpenCubeR4 s) ∧
  (⋃ y ∈ meshGrid s, halfOpenCubeR4 s y) = univ ∧
  ∀ y ∈ meshGrid s,
    volumeR4 (halfOpenCubeR4 s y) =
      ENNReal.ofReal (PlaquetteSupports.latticeSpacing s ^ 4)
def OffsetNormBounds : Prop :=
  ∀ P Q : AxisPlane,
    euclidNormVec (planeCenterOffset P) = 1 / Real.sqrt 2 ∧
    euclidNormVec (planeCenterOffset P - planeCenterOffset Q) ≤ 1
def TorusBallIsImageOfBall : Prop :=
  ∀ (z : s.Torus) (t : Fin 4 → ℝ) (ϱ : ℝ), proj s t = z → 0 < ϱ →
    {x | pointDist x z ≤ ϱ} = proj s '' closedBallR4 t ϱ ∧
    IsMeasurableTorusSet {x | pointDist x z ≤ ϱ} ∧
    TorusMeasure.torusVolume {x | pointDist x z ≤ ϱ} ≤ omega4 * ϱ ^ 4
def LiftProperties (z : s.Torus) (ϱ : ℝ) (B : Set (Fin 4 → ℝ)) : Prop :=
  (∀ x ∈ B, ∀ x' ∈ B,
    pointDist (proj s x) (proj s x') = euclidNormVec (x - x')) ∧
  (∀ u ∈ closedBallTorus z ϱ, ∃! t, IsLiftWithin B u t) ∧
  ∀ u ∈ closedBallTorus z ϱ, ∀ w ∈ closedBallTorus z ϱ, ∀ t t' : Fin 4 → ℝ,
    IsLiftWithin B u t → IsLiftWithin B w t' →
    proj s (t - t') = u - w ∧
    euclidNormVec (t - t') = pointDist u w ∧
    euclidNormVec (t - t') < s.side / 2 ∧
    ∀ r : Fin 4 → ℝ, proj s r = u - w → euclidNormVec r < s.side / 2 → r = t - t'
def LiftsDifferByPeriod (z : s.Torus) (ϱ : ℝ) (B B' : Set (Fin 4 → ℝ)) : Prop :=
  ∃ k : Fin 4 → ℤ,
    B' = (fun x => x + s.side • (fun μ => (k μ : ℝ))) '' B ∧
    ∀ u ∈ closedBallTorus z ϱ, ∀ t t' : Fin 4 → ℝ, IsLiftWithin B u t → IsLiftWithin B' u t' →
      t' = t + s.side • (fun μ => (k μ : ℝ))
def SmallBallLifts : Prop :=
  ∀ (z : s.Torus) (ϱ : ℝ), 0 < ϱ → ϱ < s.side / 4 →
    (∀ B : Set (Fin 4 → ℝ),
      IsBallLift z ϱ B ↔ ∃ t : Fin 4 → ℝ, proj s t = z ∧ B = closedBallR4 t ϱ) ∧
    (∀ B : Set (Fin 4 → ℝ), IsBallLift z ϱ B → LiftProperties s z ϱ B) ∧
    ∀ B B' : Set (Fin 4 → ℝ), IsBallLift z ϱ B → IsBallLift z ϱ B' →
      LiftsDifferByPeriod s z ϱ B B'
def LipschitzImpliesBounded : Prop :=
  ∀ f : s.Torus → ℝ, IsLipschitzFor pointDist f → IsBoundedFun f
def FunctionLiftProperties : Prop :=
  ∀ (z : s.Torus) (ϱ : ℝ) (B : Set (Fin 4 → ℝ)) (f : s.Torus → ℝ),
    IsBallLift z ϱ B → IsBoundedFun f → metricSupport f ⊆ closedBallTorus z ϱ →
    uniformNorm (functionLiftTo B f) = uniformNorm f ∧
    euclidSupport (functionLiftTo B f) = setLiftWithin B (metricSupport f) ∧
    (∀ (c : Fin 4 → ℝ) (ϱ' : ℝ), B = closedBallR4 c ϱ → ϱ ≤ ϱ' → ϱ' < s.side / 4 →
      functionLiftTo (closedBallR4 c ϱ') f = functionLiftTo B f) ∧
    (IsLipschitzFor pointDist f →
      IsLipschitzFor euclidDistR4 (functionLiftTo B f) ∧
      lipConstR4 (functionLiftTo B f) ≤ lipConstTorus (ℓ := PeriodicLattice.torusSide s.L s.m) f ∧
      integralR4 (functionLiftTo B f) = torusIntegral f)
def CubesBallsAndLifts : Prop :=
  ∀ s : Conventions.StandingParameters,
    TranslatedCubesTileTorus s ∧ TranslatedCubeSpecialCases s ∧
    CubePointsNearCenter s ∧ HalfOpenCubesPartition s ∧ OffsetNormBounds ∧
    TorusBallIsImageOfBall s ∧ SmallBallLifts s ∧
    LipschitzImpliesBounded s ∧ FunctionLiftProperties s
end YangMills.Construction.TorusCubesAndBalls
end

import YangMills.Construction.SourcesAndGluing.SeparatedLipschitzTuplesAndTheirClasses
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
open Set TorusMetric TestFunctions TorusPeriodization
namespace TorusPeriodizationOfBall
variable (G : GluingSetup) (m : ℕ+) (r : ℝ)
def ProjIsometricOnBall : Prop :=
  (∀ x ∈ ballR4 r, ∀ y ∈ ballR4 r, ∀ k : Fin 4 → ℤ, k ≠ 0 →
      euclidNorm (x - y) < euclidNorm (x - y - latticeTranslate (G.torusSideAt m) k)) ∧
    (∀ x ∈ ballR4 r, ∀ y ∈ ballR4 r,
      G.torusDist m (G.projAt m x) (G.projAt m y) = euclidNorm (x - y)) ∧
    InjOn (G.projAt m) (ballR4 r) ∧
    Pairwise fun k k' : Fin 4 → ℤ =>
      Disjoint ((fun x => x + latticeTranslate (G.torusSideAt m) k) '' ballR4 r)
        ((fun x => x + latticeTranslate (G.torusSideAt m) k') '' ballR4 r)
section Functions
variable (𝕜 : Type) [RCLike 𝕜]
def BallPeriodizeValues : Prop :=
  ∀ f : (Fin 4 → ℝ) → 𝕜, HasCompactSupportIn f (ballR4 r) →
    (∀ g, G.IsBallPeriodization m r f g ↔ g = G.ballPeriodize m r f) ∧
    (∀ x, G.ballPeriodize m r f (G.projAt m x) =
        ∑' k : Fin 4 → ℤ, f (x + latticeTranslate (G.torusSideAt m) k)) ∧
    (∀ (x : Fin 4 → ℝ) (k k' : Fin 4 → ℤ), f (x + latticeTranslate (G.torusSideAt m) k) ≠ 0 →
      f (x + latticeTranslate (G.torusSideAt m) k') ≠ 0 → k = k') ∧
    (∀ r' : ℝ, 0 < r' → 2 * r' + 2 ≤ (G.L : ℝ) ^ (m : ℕ) →
      HasCompactSupportIn f (ballR4 r') → G.ballPeriodize m r' f = G.ballPeriodize m r f) ∧
    (G.withCutoffAndSide G.K m).suppTorus (G.ballPeriodize m r f) =
      G.projAt m '' GluingSetup.suppR4 f
def BallPeriodizeLinear : Prop :=
  ∀ (f g : (Fin 4 → ℝ) → 𝕜) (a b : 𝕜), HasCompactSupportIn f (ballR4 r) →
    HasCompactSupportIn g (ballR4 r) →
      HasCompactSupportIn (a • f + b • g) (ballR4 r) ∧
        G.ballPeriodize m r (a • f + b • g) =
          a • G.ballPeriodize m r f + b • G.ballPeriodize m r g
def BallPeriodizeNormsAndRegularity : Prop :=
  ∀ f : (Fin 4 → ℝ) → 𝕜, HasCompactSupportIn f (ballR4 r) →
    (IsLipschitzFor euclidDistR4 f →
      IsLipschitzFor euclidDistTorus (G.ballPeriodize m r f) ∧
        uniformNorm (G.ballPeriodize m r f) = uniformNorm f ∧
        lipConstTorus (ℓ := G.torusSideAt m) (G.ballPeriodize m r f) = lipConstR4 f ∧
        G.sharpNormTorus (ℓ' := G.torusSideAt m) (G.ballPeriodize m r f) =
          G.sharpNormR4 f) ∧
    (IsC1R4 f → (G.withCutoffAndSide G.K m).IsC1 (G.ballPeriodize m r f)) ∧
    (ContDiff ℝ ∞ f → (G.withCutoffAndSide G.K m).IsSmooth (G.ballPeriodize m r f))
def BallPeriodizeSuppNear : Prop :=
  ∀ f : (Fin 4 → ℝ) → 𝕜, HasCompactSupportIn f (ballR4 r) →
    ∀ (x : Fin 4 → ℝ) (R : ℝ), 0 < R → GluingSetup.suppR4 f ⊆ closedBallAt x R →
      ∀ u ∈ (G.withCutoffAndSide G.K m).suppTorus (G.ballPeriodize m r f),
        G.torusDist m u (G.projAt m x) ≤ R
def BallPeriodizeComp : Prop :=
  ∀ (f : (Fin 4 → ℝ) → 𝕜) (s : euclideanMotions), HasCompactSupportIn f (ballR4 r) →
    HasCompactSupportIn (f ∘ (s : Equiv.Perm (Fin 4 → ℝ))) (ballR4 r) →
      G.ballPeriodize m r (f ∘ (s : Equiv.Perm (Fin 4 → ℝ))) =
        G.ballPeriodize m r f ∘ G.inducedMotion m s
def BallPeriodizeSuppDist (𝕜' : Type) [RCLike 𝕜'] : Prop :=
  ∀ (f : (Fin 4 → ℝ) → 𝕜) (g : (Fin 4 → ℝ) → 𝕜'), HasCompactSupportIn f (ballR4 r) →
    HasCompactSupportIn g (ballR4 r) →
      setEuclidDist ((G.withCutoffAndSide G.K m).suppTorus (G.ballPeriodize m r f))
          ((G.withCutoffAndSide G.K m).suppTorus (G.ballPeriodize m r g)) =
        setDistR4 (GluingSetup.suppR4 f) (GluingSetup.suppR4 g)
end Functions
open Ambient
def sepLipBall (n : ℕ+) : Set (euclidean.FunTuple G n) :=
  {f | euclidean.IsSepLip f ∧ euclidean.SuppSubset f (ballR4 r)}
def BallPeriodizeTuples (n : ℕ+) : Prop :=
  (∀ f ∈ sepLipBall G r n, (torus m).IsSepLip (S := G)
      (G.ballPeriodizeTuple m r f)) ∧
    IsMultilinearOn G m (sepLipBall G r n) (G.ballPeriodizeTuple m r) ∧
    (∀ f ∈ sepLipBall G r n, ∀ i,
      G.sharpNormTorus (ℓ' := G.torusSideAt m) (G.ballPeriodizeTuple m r f i) =
        G.sharpNormR4 (f i)) ∧
    (2 ≤ (n : ℕ) → ∀ f ∈ sepLipBall G r n,
      (torus m).minGap (S := G) (G.ballPeriodizeTuple m r f) = euclidean.minGap f) ∧
    (∀ f ∈ sepLipBall G r n, ∀ (J : Finset (Fin n)) (hJ : J.Nonempty),
      G.ballPeriodizeTuple m r (restrictTuple f J hJ) = restrictTuple (G.ballPeriodizeTuple m r f) J hJ) ∧
    (∀ f ∈ sepC1Ball G n r,
      G.ballPeriodizeTuple m r f ∈ (torus m).sepC1 G n) ∧
    ∀ d R : ℝ, 0 < d → 0 < R → R < (G.L : ℝ) ^ (m : ℕ) / 2 →
      ∀ f ∈ euclidean.lipClass G n d R,
        euclidean.SuppSubset f (ballR4 r) →
          G.ballPeriodizeTuple m r f ∈ (torus m).lipClass G n d R
def Statement : Prop :=
  ∀ (G : GluingSetup) (m : ℕ+) (r : ℝ), 0 < r → 2 * r + 2 ≤ (G.L : ℝ) ^ (m : ℕ) →
    ProjIsometricOnBall G m r ∧
      (∀ (𝕜 : Type) [RCLike 𝕜],
        BallPeriodizeValues G m r 𝕜 ∧ BallPeriodizeLinear G m r 𝕜 ∧
          BallPeriodizeNormsAndRegularity G m r 𝕜 ∧ BallPeriodizeSuppNear G m r 𝕜 ∧
          BallPeriodizeComp G m r 𝕜) ∧
      (∀ (𝕜 𝕜' : Type) [RCLike 𝕜] [RCLike 𝕜'], BallPeriodizeSuppDist G m r 𝕜 𝕜') ∧
      ∀ n : ℕ+, BallPeriodizeTuples G m r n
end TorusPeriodizationOfBall
end YangMills.Construction.SourcesAndGluing
end

import YangMills.Construction.GrowingTori.TuplesOfFourSpaceAndTheirRestrictionToATorus
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric YangMills.Construction.TestFunctions YangMills.Construction.TorusPeriodization
open YangMills.Construction.SourcesAndGluing (ballR4)
open YangMills.Construction.BallPeriodization (IsPeriodizableInBall ptInfDist)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodizationThroughBall
variable (P : PeriodicSpace.Params)
def unitCutoffData : ReflectionPositivity.CutoffMirrors.MirrorData :=
  ⟨BallTuples.cutoffOneParams P, 1, one_pos, 0⟩
abbrev torusSupp {E : Type*} [Zero E] (u : P.Torus → E) : Set P.Torus :=
  (unitCutoffData P).supp u
abbrev euclidSupp {𝕜 : Type*} [RCLike 𝕜] (f : (Fin 4 → ℝ) → 𝕜) : Set (Fin 4 → ℝ) :=
  SourcesAndGluing.GluingSetup.suppR4 f
abbrev torusDist (u v : P.Torus) : ℝ≥0∞ := ptInfDist P .torus u v
def ProjectionOnBall (ρ : ℝ) : Prop :=
  (∀ x y : Fin 4 → ℝ,
    IsLeast (range fun k : Fin 4 → ℤ =>
        ENNReal.ofReal (euclidNormVec (x - y - latticeTranslate P.side k)))
      (torusDist P (torusProj P.side x) (torusProj P.side y)) ∧
    torusDist P (torusProj P.side x) (torusProj P.side y) ≤
      ENNReal.ofReal (euclidNormVec (x - y))) ∧
  (∀ x ∈ ballR4 ρ, ∀ y ∈ ballR4 ρ, ∀ k : Fin 4 → ℤ, k ≠ 0 →
    euclidNormVec (x - y) < euclidNormVec (x - y - latticeTranslate P.side k)) ∧
  (∀ x ∈ ballR4 ρ, ∀ y ∈ ballR4 ρ,
    torusDist P (torusProj P.side x) (torusProj P.side y) =
      ENNReal.ofReal (euclidNormVec (x - y))) ∧
  InjOn (torusProj P.side) (ballR4 ρ) ∧
  Pairwise fun k k' : Fin 4 → ℤ =>
    Disjoint ((fun x => x + latticeTranslate P.side k) '' ballR4 ρ)
      ((fun x => x + latticeTranslate P.side k') '' ballR4 ρ)
section Functions
variable (ρ : ℝ) (𝕜 : Type) [RCLike 𝕜]
variable {𝕜} in
def IsPeriodizationOn (S : Set (Fin 4 → ℝ)) (f : (Fin 4 → ℝ) → 𝕜) (g : P.Torus → 𝕜) : Prop :=
  (∀ x ∈ S, g (torusProj P.side x) = f x) ∧ ∀ u, u ∉ torusProj P.side '' S → g u = 0
def fundamentalCube : Set (Fin 4 → ℝ) := univ.pi fun _ => Ico (-P.side / 2) (P.side / 2)
def PeriodizeValues : Prop :=
  ∀ f : (Fin 4 → ℝ) → 𝕜, IsPeriodizableInBall P ρ f →
    (∀ x, {k : Fin 4 → ℤ | f (x + latticeTranslate P.side k) ≠ 0}.Subsingleton) ∧
    (∀ x x', torusProj P.side x = torusProj P.side x' →
      ∑' k : Fin 4 → ℤ, f (x + latticeTranslate P.side k) =
        ∑' k : Fin 4 → ℤ, f (x' + latticeTranslate P.side k)) ∧
    (∀ x, periodize P.side f (torusProj P.side x) =
      ∑' k : Fin 4 → ℤ, f (x + latticeTranslate P.side k)) ∧
    (∀ g, IsPeriodizationOn P (ballR4 ρ) f g ↔ g = periodize P.side f) ∧
    (∀ ρ', IsPeriodizableInBall P ρ' f →
      IsPeriodizationOn P (ballR4 ρ') f (periodize P.side f)) ∧
    (∀ S : Set (Fin 4 → ℝ), euclidSupp f ⊆ S → HasDiameterLE S (P.side / 2) →
      IsPeriodizable P.side S f ∧ IsPeriodizationOn P S f (periodize P.side f)) ∧
    ∀ g : P.Torus → 𝕜, (∀ y ∈ fundamentalCube P, g (torusProj P.side y) = f y) ↔
      g = periodize P.side f
def PeriodizeLinear : Prop :=
  ∀ (f h : (Fin 4 → ℝ) → 𝕜) (c' c'' : 𝕜), IsPeriodizableInBall P ρ f →
    IsPeriodizableInBall P ρ h →
      IsPeriodizableInBall P ρ (c' • f + c'' • h) ∧
        periodize P.side (c' • f + c'' • h) =
          c' • periodize P.side f + c'' • periodize P.side h
def PeriodizeNorms : Prop :=
  ∀ f : (Fin 4 → ℝ) → 𝕜, IsPeriodizableInBall P ρ f → IsLipschitzFor euclidDistR4 f →
    IsLipschitzFor euclidDistTorus (periodize P.side f) ∧
      uniformNorm (periodize P.side f) = uniformNorm f ∧
      lipConstTorus (periodize P.side f) = lipConstR4 f ∧
      sharpNormTorus P.M (periodize P.side f) = sharpNormR4 P.M f
def PeriodizeSupport : Prop :=
  ∀ f : (Fin 4 → ℝ) → 𝕜, IsPeriodizableInBall P ρ f →
    torusSupp P (periodize P.side f) = torusProj P.side '' euclidSupp f ∧
    (unitCutoffData P).IsCompactSubset (torusSupp P (periodize P.side f)) ∧
    ρ < P.side / 2 ∧
    torusSupp P (periodize P.side f) ⊆ closedBallTorus (torusProj P.side 0) ρ ∧
    ∀ (R : ℝ) (x : Fin 4 → ℝ), 0 < R → euclidSupp f ⊆ closedBallR4 x R →
      torusSupp P (periodize P.side f) ⊆
        {u | torusDist P u (torusProj P.side x) ≤ ENNReal.ofReal R}
def PeriodizeDeriv : Prop :=
  ∀ f : (Fin 4 → ℝ) → 𝕜, IsPeriodizableInBall P ρ f → IsC1R4 f →
    BallPeriodization.IsC1Torus P (periodize P.side f) ∧
      ∀ μ : Fin 4, IsPeriodizableInBall P ρ (partialDerivR4 μ f) ∧
        BallPeriodization.partialDerivTorus P μ (periodize P.side f) =
          periodize P.side (partialDerivR4 μ f)
def PeriodizeComp : Prop :=
  ∀ (f : (Fin 4 → ℝ) → 𝕜) (s : euclideanMotions), IsPeriodizableInBall P ρ f →
    IsPeriodizableInBall P ρ (f ∘ (s : Equiv.Perm (Fin 4 → ℝ))) →
      periodize P.side (f ∘ (s : Equiv.Perm (Fin 4 → ℝ))) =
        periodize P.side f ∘ BallPeriodization.torusMap P s
def PeriodizeSuppDist (𝕜' : Type) [RCLike 𝕜'] : Prop :=
  ∀ (f : (Fin 4 → ℝ) → 𝕜) (h : (Fin 4 → ℝ) → 𝕜'), IsPeriodizableInBall P ρ f →
    IsPeriodizableInBall P ρ h →
      setEuclidDist (torusSupp P (periodize P.side f)) (torusSupp P (periodize P.side h)) =
        setDistR4 (euclidSupp f) (euclidSupp h) ∧
      (euclidSupp f = ∅ ∨ euclidSupp h = ∅ →
        setEuclidDist (torusSupp P (periodize P.side f))
            (torusSupp P (periodize P.side h)) = ⊤ ∧
          setDistR4 (euclidSupp f) (euclidSupp h) = ⊤) ∧
      (Disjoint (euclidSupp f) (euclidSupp h) →
        Disjoint (torusSupp P (periodize P.side f)) (torusSupp P (periodize P.side h)))
end Functions
def DescendedMotions : Prop :=
  ∀ s : euclideanMotions,
    (∃! t : P.Torus → P.Torus,
      t ∘ torusProj P.side = torusProj P.side ∘ (s : Equiv.Perm (Fin 4 → ℝ))) ∧
    ∀ t : P.Torus → P.Torus, t ∘ torusProj P.side = torusProj P.side ∘ (s : Equiv.Perm (Fin 4 → ℝ)) →
      Function.Bijective t ∧
        ∀ u v, torusDist P (t u) (t v) = torusDist P u v
def PeriodizeTuples (ρ : ℝ) (n : ℕ) : Prop :=
  ∀ X : BallTuples.FnTuple n, BallTuples.IsPeriodizable P ρ X →
    (∀ l, IsLipschitzFor euclidDistTorus (BallTuples.periodize P X l)) ∧
    (∀ l, (unitCutoffData P).IsCompactSubset
      (torusSupp P (BallTuples.periodize P X l))) ∧
    (∀ l l', l ≠ l' → Disjoint (torusSupp P (BallTuples.periodize P X l))
      (torusSupp P (BallTuples.periodize P X l'))) ∧
    (∀ (l : Fin n) (g g' : BallTuples.R4Fun) (a b : ℝ),
      BallTuples.IsPeriodizable P ρ (Function.update X l g) →
      BallTuples.IsPeriodizable P ρ (Function.update X l g') →
      BallTuples.IsPeriodizable P ρ (Function.update X l (a • g + b • g')) →
        BallTuples.periodize P (Function.update X l (a • g + b • g')) =
          Function.update (BallTuples.periodize P X) l
            (a • periodize P.side g + b • periodize P.side g')) ∧
    (∀ J : Finset (Fin n),
      BallTuples.periodize P (BallTuples.subTupleOn X J) =
        AmbientPoints.restrictTuple (BallTuples.periodize P X) J) ∧
    (2 ≤ n →
      (⨅ (l : Fin n) (l' : Fin n) (_ : l ≠ l'),
        setEuclidDist (torusSupp P (BallTuples.periodize P X l))
          (torusSupp P (BallTuples.periodize P X l'))) =
        BallTuples.minSupportDist X) ∧
    (∀ R : ℝ, 0 < R → BallTuples.IsBallSupported P.L R X → ∀ l, ∃ u : P.Torus,
      torusSupp P (BallTuples.periodize P X l) ⊆
        {v | torusDist P v u ≤ ENNReal.ofReal R}) ∧
    (X ∈ BallTuples.sepTuplesBall P n ρ →
      BallTuples.periodize P X ∈ BallTuples.sepTuples P .torus n)
def PeriodizationLemma : Prop :=
  ∀ (P : PeriodicSpace.Params) (ρ : ℝ), 0 < ρ → ρ ≤ BallPeriodization.ballRadius P →
    ProjectionOnBall P ρ ∧
    (∀ (𝕜 : Type) [RCLike 𝕜],
      PeriodizeValues P ρ 𝕜 ∧ PeriodizeLinear P ρ 𝕜 ∧ PeriodizeNorms P ρ 𝕜 ∧
        PeriodizeSupport P ρ 𝕜 ∧ PeriodizeDeriv P ρ 𝕜 ∧
        PeriodizeComp P ρ 𝕜) ∧
    (∀ (𝕜 𝕜' : Type) [RCLike 𝕜] [RCLike 𝕜'], PeriodizeSuppDist P ρ 𝕜 𝕜') ∧
    DescendedMotions P ∧
    ∀ n : ℕ, 1 ≤ n → PeriodizeTuples P ρ n
end YangMills.Construction.PeriodizationThroughBall
end

import YangMills.Construction.InfiniteLattice.StateTransportedByDilation
import YangMills.Construction.ReflectionPositivity.OneLatticeAtEverySpacing
import YangMills.Construction.ReflectionPositivity.PicturesCubeVectorsAndReflectionSizesAtASpacing
import YangMills.Construction.ReflectionPositivity.RateConstantAndRateFunction
import YangMills.Construction.ReflectionPositivity.SitePicturesOfADirection
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ComplexConjugate ComplexOrder ENNReal Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare
open InfiniteLattice (GaugeField AmbientSpace LatticePoint Link axisStep shift regionObservables
  IsLocalObservable IsBoundedObservable observableSupNorm closedHalfSpace scaledCube plateauPairing
  condExpShiftInvariant pullToUnit IsPeriodicGibbs gaugeFieldRescale gaugeFieldUnrescale
  pointOfUnit pointToUnit)
open GibbsAtFixedSpacing (BorelProb linfNorm)
open LatticeAtSpacing (reflectionPositiveSet coordinateReflect IsErgodicState cubeHalfWidth)
open SmearingFilter (spectralRateConst spectralRateFn)
variable {a : ℝ}
def localHalfSpaceObs (a : ℝ) (μ : Fin 4) : Set (GaugeField a → ℂ) :=
  {F | F ∈ regionObservables a (closedHalfSpace μ) ∧ IsLocalObservable F}
def convexMix (t : unitInterval) (ν₁ ν₂ : BorelProb a) : BorelProb a :=
  (⟨ENNReal.ofReal t • ν₁.1 + ENNReal.ofReal (1 - t) • ν₂.1, by
    have := ν₁.2
    have := ν₂.2
    refine ⟨?_⟩
    have h : ENNReal.ofReal (t : ℝ) + ENNReal.ofReal (1 - (t : ℝ)) = 1 := by
      rw [← ENNReal.ofReal_add t.2.1 (sub_nonneg.mpr t.2.2)]
      simp
    simpa using h⟩ : InfiniteLattice.GaugeFieldProbability a)
def IsAffineInMeasure (G : GaugeField a → ℂ) : Prop :=
  IsBoundedObservable G ∧ ∀ (ν₁ ν₂ : BorelProb a) (t : unitInterval),
    (convexMix t ν₁ ν₂).integral G =
      ((t : ℝ) : ℂ) * ν₁.integral G + ((1 - (t : ℝ) : ℝ) : ℂ) * ν₂.integral G
def reflectShiftProduct (μ : Fin 4) (F : GaugeField a → ℂ) (v : LatticePoint a) :
    GaugeField a → ℂ :=
  fun U => conj ((coordinateReflect a μ).actOn F U) * (shift v).actOn F U
def reflectedCorrelation (ν : BorelProb a) (μ : Fin 4) (F : GaugeField a → ℂ)
    (v : LatticePoint a) : ℂ :=
  ν.integral (reflectShiftProduct μ F v)
def fivePointCombination (ν : BorelProb a) (μ : Fin 4) (l : TransverseAxis μ) (k : ℕ)
    (F : GaugeField a → ℂ) : ℂ :=
  reflectedCorrelation ν μ F 0 - 4 * reflectedCorrelation ν μ F (k • axisStep a μ) +
    reflectedCorrelation ν μ F ((2 * k) • axisStep a μ) +
    reflectedCorrelation ν μ F (k • axisStep a μ + k • axisStep a l.1) +
    reflectedCorrelation ν μ F (k • axisStep a μ - k • axisStep a l.1)
def energyOpCoarse (ν : BorelProb a) (μ : Fin 4) (k : ℕ) :
    ScaledPair.Hilb ν.1 μ →L[ℂ] ScaledPair.Hilb ν.1 μ :=
  (1 - ScaledPair.transferOp ν.1 μ ^ k) ^ 2
def momentumOpCoarse (ν : BorelProb a) (μ : Fin 4) (l : TransverseAxis μ) (k : ℕ) :
    ScaledPair.Hilb ν.1 μ →L[ℂ] ScaledPair.Hilb ν.1 μ :=
  ScaledPair.transferOp ν.1 μ ^ k *
    ((2 : ℂ) • 1 - ScaledPair.shiftOp ν.1 μ l ^ k -
      star (ScaledPair.shiftOp ν.1 μ l) ^ k)
def expDecayAt (k : ℕ) (E : ℝ≥0∞) : ℝ :=
  if E = ⊤ then 0 else Real.exp (-((k : ℝ) * E.toReal))
def coarseSpectralBracket {μ : Fin 4} (l : TransverseAxis μ) (k : ℕ)
    (x : ℝ≥0∞ × (TransverseAxis μ → ℝ)) : ℝ :=
  1 - 4 * expDecayAt k x.1 + expDecayAt (2 * k) x.1 +
    2 * expDecayAt k x.1 * Real.cos ((k : ℝ) * x.2 l)
def CoarseOpInequality (ν : BorelProb a) (μ : Fin 4) (l : TransverseAxis μ) (k : ℕ) : Prop :=
  energyOpCoarse ν μ k ≥ momentumOpCoarse ν μ l k
def FivePointNonneg (ν : BorelProb a) (μ : Fin 4) (l : TransverseAxis μ) (k : ℕ) : Prop :=
  ∀ F ∈ localHalfSpaceObs a μ, 0 ≤ fivePointCombination ν μ l k F
def FivePointSpectralForm (ha : 0 < a) (ν : BorelProb a) (μ : Fin 4) (l : TransverseAxis μ)
    (k : ℕ) : Prop :=
  (∀ F ∈ localHalfSpaceObs a μ,
    fivePointCombination ν μ l k F =
      ∫ q, pullToSpectrum μ (fun x => ((coarseSpectralBracket l k x : ℝ) : ℂ)) q
        ∂(ScaledPair.spectralMeasureOf ν.1 μ (ScaledPair.obsClass ν.1 μ ha F))) ∧
  ∀ x : ℝ≥0∞ × (TransverseAxis μ → ℝ), x.1 ≠ ⊤ →
    coarseSpectralBracket l k x =
      2 * expDecayAt k x.1 *
        (Real.cosh ((k : ℝ) * x.1.toReal) + Real.cos ((k : ℝ) * x.2 l) - 2)
def FivePointConverse (ha : 0 < a) (ν : BorelProb a) (μ : Fin 4) (l : TransverseAxis μ)
    (k : ℕ) : Prop :=
  (FivePointNonneg ν μ l k ↔ CoarseOpInequality ν μ l k) ∧
  (∀ F ∈ localHalfSpaceObs a μ,
    fivePointCombination ν μ l k F =
      inner ℂ (ScaledPair.obsClass ν.1 μ ha F)
        ((energyOpCoarse ν μ k - momentumOpCoarse ν μ l k)
          (ScaledPair.obsClass ν.1 μ ha F))) ∧
  IsSelfAdjoint (energyOpCoarse ν μ k - momentumOpCoarse ν μ l k) ∧
  Dense (ScaledPair.obsClass ν.1 μ ha '' localHalfSpaceObs a μ)
def CoarseStepConditions (ha : 0 < a) (ν : BorelProb a) : Prop :=
  ∀ (μ : Fin 4) (l : TransverseAxis μ) (k : ℕ), 1 ≤ k →
    CoarseOpInequality ν μ l k ∧
    FivePointNonneg ν μ l k ∧
    (∀ F ∈ localHalfSpaceObs a μ, ∀ v : LatticePoint a, 0 ≤ v.1 μ →
      IsAffineInMeasure (reflectShiftProduct μ F v)) ∧
    FivePointSpectralForm ha ν μ l k ∧
    FivePointConverse ha ν μ l k
def cubeObsSubmodule (a : ℝ) (r : ℕ+) : Submodule ℂ (GaugeField a → ℂ) where
  carrier := regionObservables a (scaledCube a r)
  add_mem' := by
    rintro A B ⟨oA, mA⟩ ⟨oB, mB⟩
    exact ⟨oA.add oB, Measurable.add mA mB⟩
  zero_mem' := ⟨⟨measurable_const, 0, fun _ => by simp⟩, measurable_const⟩
  smul_mem' := by
    rintro c A ⟨oA, mA⟩
    exact ⟨oA.const_smul c, Measurable.const_smul mA c⟩
def axisReflectObs (γ : axisReflectionGroup) (A : GaugeField a → ℂ) : GaugeField a → ℂ :=
  (axisReflectionGroup.toLatticeSymmetry a γ).actOn A
def cubeReflectedCorrelation (ν : BorelProb a) (μ : Fin 4) (r : ℕ+) (A : GaugeField a → ℂ) : ℂ :=
  reflectedCorrelation ν μ A ((2 * (r : ℕ)) • axisStep a μ)
def cubeVecNorm (ha : 0 < a) (ν : BorelProb a) (μ : Fin 4) (r : ℕ+) (A : GaugeField a → ℂ) : ℝ :=
  ‖ScaledPair.cubeVector ν.1 μ ha r A‖
def reflectionSize (ha : 0 < a) (ν : BorelProb a) (r : ℕ+) (A : GaugeField a → ℂ) : ℝ :=
  scaledCubeReflectionSize ha ν.1 r A
def ReflectionGroupPreservesCube (a : ℝ) (r : ℕ+) : Prop :=
  (∀ γ : axisReflectionGroup,
    (axisReflectionGroup.toLatticeSymmetry a γ).setImage (scaledCube a r) =
        scaledCube a r ∧
      axisReflectObs γ '' regionObservables a (scaledCube a r) = regionObservables a (scaledCube a r)) ∧
  (∀ g : Equiv.Perm AmbientSpace, g ∈ axisReflectionGroup ↔ ∃ ε, ⇑g = axisSignFlip ε) ∧
  Nat.card axisReflectionGroup = 16
def ReflectionSizeAsCorrelations (ha : 0 < a) (ν : BorelProb a) (r : ℕ+) (A : GaugeField a → ℂ) :
    Prop :=
  (∀ μ : Fin 4, ((cubeVecNorm ha ν μ r A ^ 2 : ℝ) : ℂ) = cubeReflectedCorrelation ν μ r A) ∧
  IsGreatest (scaledCubeVectorNormsSq ha ν.1 r A) (reflectionSize ha ν r A) ∧
  (∀ (μ : Fin 4) (γ : axisReflectionGroup),
    cubeVecNorm ha ν μ r (axisReflectObs γ A) ^ 2 =
        ‖cubeVector (unitRepresentative ν.1) μ r
          ((axisReflectionGroup.toUnitLatticeSymmetry γ).actOn
            (pullToUnit ha A))‖ ^ 2 ∧
      ((cubeVecNorm ha ν μ r (axisReflectObs γ A) ^ 2 : ℝ) : ℂ) =
        cubeReflectedCorrelation ν μ r (axisReflectObs γ A)) ∧
  Nat.card (Fin 4 × axisReflectionGroup) = 64 ∧
  IsGreatest
    (Set.range fun p : Fin 4 × axisReflectionGroup =>
      (cubeReflectedCorrelation ν p.1 r (axisReflectObs p.2 A)).re)
    (reflectionSize ha ν r A) ∧
  (∀ (μ : Fin 4) (γ : axisReflectionGroup),
    0 ≤ cubeReflectedCorrelation ν μ r (axisReflectObs γ A)) ∧
  reflectionSize ha ν r A =
    cubeReflectionNorm (unitRepresentative ν.1) r (pullToUnit ha A)
def ReflectionSizeSeminorm (ha : 0 < a) (ν : BorelProb a) (r : ℕ+) : Prop :=
  (∃ p : Seminorm ℂ (cubeObsSubmodule a r), ∀ A : cubeObsSubmodule a r,
    p A = reflectionSize ha ν r (A : GaugeField a → ℂ) ^ (1 / 2 : ℝ)) ∧
  ∀ A ∈ regionObservables a (scaledCube a r),
    (∀ γ : axisReflectionGroup, reflectionSize ha ν r (axisReflectObs γ A) = reflectionSize ha ν r A) ∧
    reflectionSize ha ν r A = reflectionSize ha ν r (fun U => conj (A U)) ∧
    reflectionSize ha ν r A ≤ observableSupNorm A ^ 2
def ReflectionSizeConvex (ha : 0 < a) (r : ℕ+) : Prop :=
  (∀ A ∈ regionObservables a (scaledCube a r), ∀ (μ : Fin 4) (γ : axisReflectionGroup),
    IsAffineInMeasure (reflectShiftProduct μ (axisReflectObs γ A) ((2 * (r : ℕ)) • axisStep a μ))) ∧
  ∀ ν₁ ∈ reflectionPositiveSet a, ∀ ν₂ ∈ reflectionPositiveSet a, ∀ t : unitInterval,
    convexMix t ν₁ ν₂ ∈ reflectionPositiveSet a ∧
    ∀ A ∈ regionObservables a (scaledCube a r),
      reflectionSize ha (convexMix t ν₁ ν₂) r A ≤
        (t : ℝ) * reflectionSize ha ν₁ r A + (1 - (t : ℝ)) * reflectionSize ha ν₂ r A
def ReflectionSizeConditions (ha : 0 < a) (ν : BorelProb a) (r : ℕ+) : Prop :=
  ReflectionGroupPreservesCube a r ∧
  (∀ A ∈ regionObservables a (scaledCube a r), ReflectionSizeAsCorrelations ha ν r A) ∧
  ReflectionSizeSeminorm ha ν r ∧
  reflectionSize ha ν r (fun _ => 1) = 1 ∧
  ReflectionSizeConvex ha r
def transferDecayForm (ha : 0 < a) (ν : BorelProb a) (μ : Fin 4) (r : ℕ+) (A : GaugeField a → ℂ)
    (n : ℕ) : ℂ :=
  inner ℂ (ScaledPair.cubeVector ν.1 μ ha r A)
    ((ScaledPair.transferOp ν.1 μ ^ n * (1 - ScaledPair.groundProjection ν.1 μ))
      (ScaledPair.cubeVector ν.1 μ ha r A))
def cubeGap (a : ℝ) (r : ℕ+) (y : LatticePoint a) : ℝ :=
  linfNorm y.1 / a - 2 * ((r : ℕ) : ℝ)
def shiftedCorrelation (ν : BorelProb a) (A B : GaugeField a → ℂ) (y : LatticePoint a) : ℂ :=
  ν.integral fun U => conj (A U) * (shift y).actOn B U
def reflectionSizeRoots (ha : 0 < a) (ν : BorelProb a) (r : ℕ+) (A B : GaugeField a → ℂ) : ℝ :=
  reflectionSize ha ν r A ^ (1 / 2 : ℝ) * reflectionSize ha ν r B ^ (1 / 2 : ℝ)
def invariantPartPairing (ν : BorelProb a) (A B : GaugeField a → ℂ) : ℂ :=
  ν.integral fun U => A U * condExpShiftInvariant ν.1 B U
def CubeVectorDecay (ha : 0 < a) (ν : BorelProb a) (μ : Fin 4) (r : ℕ+)
    (A : GaugeField a → ℂ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    0 ≤ transferDecayForm ha ν μ r A n ∧
      transferDecayForm ha ν μ r A n ≤
        ((spectralRateFn (((r : ℕ) : ℝ) / (n : ℝ)) * reflectionSize ha ν r A : ℝ) : ℂ)
def SeparatedCubeBound (ha : 0 < a) (ν : BorelProb a) (r : ℕ+) (A B : GaugeField a → ℂ) : Prop :=
  ∀ y : LatticePoint a, 1 ≤ cubeGap a r y →
    ‖shiftedCorrelation ν A B y - plateauPairing ν.1 A B‖ ≤
      spectralRateFn (((r : ℕ) : ℝ) / cubeGap a r y) * reflectionSizeRoots ha ν r A B
def UnconjugatedBound (ha : 0 < a) (ν : BorelProb a) (r : ℕ+) (A B : GaugeField a → ℂ) : Prop :=
  ∀ y : LatticePoint a, 1 ≤ cubeGap a r y →
    plateauPairing ν.1 (fun U => conj (A U)) B = invariantPartPairing ν A B ∧
    ‖(ν.integral fun U => A U * (shift y).actOn B U) -
        invariantPartPairing ν A B‖ ≤
      spectralRateFn (((r : ℕ) : ℝ) / cubeGap a r y) * reflectionSizeRoots ha ν r A B
def largeDistanceBound (ha : 0 < a) (ν : BorelProb a) (r : ℕ+) (A B : GaugeField a → ℂ)
    (y : LatticePoint a) : ℝ :=
  6 * spectralRateConst * (((r : ℕ) : ℝ) * a / linfNorm y.1) ^ 2 * reflectionSizeRoots ha ν r A B
def cocompactSites (a : ℝ) : Filter (LatticePoint a) :=
  comap (fun y : LatticePoint a => TorusMetric.euclidNormVec y.1) atTop
def LargeDistanceBound (ha : 0 < a) (ν : BorelProb a) (r : ℕ+) (A B : GaugeField a → ℂ) : Prop :=
  0 ≤ spectralRateConst ∧
  (∀ y : LatticePoint a, 4 * ((r : ℕ) : ℝ) * a ≤ linfNorm y.1 →
    linfNorm y.1 / (2 * a) ≤ cubeGap a r y ∧
    2 * ((r : ℕ) : ℝ) ≤ linfNorm y.1 / (2 * a) ∧
    ((r : ℕ) : ℝ) / cubeGap a r y ≤ 2 * ((r : ℕ) : ℝ) * a / linfNorm y.1 ∧
    2 * ((r : ℕ) : ℝ) * a / linfNorm y.1 ≤ 1 / 2 ∧
    spectralRateFn (((r : ℕ) : ℝ) / cubeGap a r y) ≤
      6 * spectralRateConst * (((r : ℕ) : ℝ) * a / linfNorm y.1) ^ 2 ∧
    ‖shiftedCorrelation ν A B y - plateauPairing ν.1 A B‖ ≤ largeDistanceBound ha ν r A B y) ∧
  (∀ y : LatticePoint a, TorusMetric.euclidNormVec y.1 / 2 ≤ linfNorm y.1) ∧
  Tendsto (largeDistanceBound ha ν r A B) (cocompactSites a) (𝓝 0) ∧
  Tendsto (shiftedCorrelation ν A B) (cocompactSites a) (𝓝 (plateauPairing ν.1 A B))
def respace (a : ℝ) {b : ℝ} (hb : 0 < b) : GaugeField a → GaugeField b :=
  gaugeFieldUnrescale hb ∘ gaugeFieldRescale a
def respaceState {b : ℝ} (hb : 0 < b) (ν : BorelProb a) : BorelProb b :=
  (⟨ν.1.map (respace a hb), by
    have := ν.2
    exact Measure.isProbabilityMeasure_map
      ((InfiniteLattice.continuous_gaugeFieldUnrescale hb).comp
        (InfiniteLattice.continuous_gaugeFieldRescale a)).measurable.aemeasurable⟩ :
    InfiniteLattice.GaugeFieldProbability b)
def respacePoint (ha : 0 < a) (b : ℝ) (y : LatticePoint a) : LatticePoint b :=
  pointOfUnit b (pointToUnit ha y)
def RespaceInvertible (ha : 0 < a) {b : ℝ} (hb : 0 < b) : Prop :=
  (∀ (U : GaugeField a) (e : Link b) (e' : Link a),
    (e'.initial : AmbientSpace) = (a / b) • (e.initial : AmbientSpace) →
    (e'.terminal : AmbientSpace) = (a / b) • (e.terminal : AmbientSpace) →
      respace a hb U e = U e') ∧
  Function.LeftInverse (respace b ha) (respace a hb) ∧
  Function.RightInverse (respace b ha) (respace a hb)
def ScaleInvariantQuantities (ha : 0 < a) {b : ℝ} (hb : 0 < b) (ν : BorelProb a) (ν' : BorelProb b)
    (μ : Fin 4) (r : ℕ+) (A B : GaugeField a → ℂ) (A' B' : GaugeField b → ℂ) (y : LatticePoint a)
    (y' : LatticePoint b) : Prop :=
  cubeVecNorm hb ν' μ r A' ^ 2 = cubeVecNorm ha ν μ r A ^ 2 ∧
  cubeReflectedCorrelation ν' μ r A' = cubeReflectedCorrelation ν μ r A ∧
  reflectionSize hb ν' r A' = reflectionSize ha ν r A ∧
  (∀ n : ℕ, 1 ≤ n →
    transferDecayForm hb ν' μ r A' n = transferDecayForm ha ν μ r A n ∧
    spectralRateFn (((r : ℕ) : ℝ) / (n : ℝ)) * reflectionSize hb ν' r A' =
      spectralRateFn (((r : ℕ) : ℝ) / (n : ℝ)) * reflectionSize ha ν r A) ∧
  (1 ≤ cubeGap a r y →
    ‖shiftedCorrelation ν' A' B' y' - plateauPairing ν'.1 A' B'‖ =
        ‖shiftedCorrelation ν A B y - plateauPairing ν.1 A B‖ ∧
    spectralRateFn (((r : ℕ) : ℝ) / cubeGap b r y') * reflectionSizeRoots hb ν' r A' B' =
      spectralRateFn (((r : ℕ) : ℝ) / cubeGap a r y) * reflectionSizeRoots ha ν r A B)
def ScaleInvariance (ha : 0 < a) (ν : BorelProb a) (μ : Fin 4) (r : ℕ+)
    (A B : GaugeField a → ℂ) : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (y : LatticePoint a),
    RespaceInvertible ha hb ∧
    respaceState hb ν ∈ reflectionPositiveSet b ∧
    A ∘ respace b ha ∈ regionObservables b (scaledCube b r) ∧
    B ∘ respace b ha ∈ regionObservables b (scaledCube b r) ∧
    (respacePoint ha b y).1 = (b / a) • y.1 ∧
    cubeGap b r (respacePoint ha b y) = cubeGap a r y ∧
    ScaleInvariantQuantities ha hb ν (respaceState hb ν) μ r A B (A ∘ respace b ha)
      (B ∘ respace b ha) y (respacePoint ha b y) ∧
    (cubeGap a r y ≠ 0 ↔ linfNorm y.1 ≠ 2 * cubeHalfWidth a r) ∧
    (cubeGap a r y ≠ 0 →
      ((r : ℕ) : ℝ) / cubeGap a r y =
        cubeHalfWidth a r / (linfNorm y.1 - 2 * cubeHalfWidth a r))
def InverseSquareDecay (ha : 0 < a) (ν : BorelProb a) (μ : Fin 4) (r : ℕ+)
    (A B : GaugeField a → ℂ) : Prop :=
  CubeVectorDecay ha ν μ r A ∧
  SeparatedCubeBound ha ν r A B ∧
  UnconjugatedBound ha ν r A B ∧
  LargeDistanceBound ha ν r A B ∧
  (IsErgodicState ν → plateauPairing ν.1 A B = conj (ν.integral A) * ν.integral B) ∧
  ScaleInvariance ha ν μ r A B
def WeakClosed (a : ℝ) : Prop :=
  IsClosed (reflectionPositiveSet a) ∧
    IsClosed {ν : BorelProb a | ν ∈ reflectionPositiveSet a ∧ IsErgodicState ν}
def PeriodicGibbsReflectionPositive (a : ℝ) : Prop :=
  ∀ β : ℝ, 0 < β → ∀ ν : BorelProb a, IsPeriodicGibbs β ν.1 → ν ∈ reflectionPositiveSet a
end YangMills.Construction.ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare

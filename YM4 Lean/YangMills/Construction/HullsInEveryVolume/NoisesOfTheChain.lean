import YangMills.Construction.HullsInEveryVolume.GridsOfAMirror
import YangMills.Construction.HullsInEveryVolume.LocalHullOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ChainNoise
variable {ℓ : TorusLumps.StepParameters}
abbrev StepNoise (ℓ : TorusLumps.StepParameters) (n : ℕ) : Type :=
  (TorusFields.TorusSite n → unitInterval) × (TorusFields.TorusBond n → unitInterval) ×
    (TorusFields.TorusBond (n * ℓ.side) → unitInterval)
def stepNoiseLaw (ℓ : TorusLumps.StepParameters) (n : ℕ) [NeZero n] : Measure (StepNoise ℓ n) :=
  (Measure.pi fun _ : TorusFields.TorusSite n => (volume : Measure unitInterval)).prod
    ((Measure.pi fun _ : TorusFields.TorusBond n => (volume : Measure unitInterval)).prod
      (Measure.pi fun _ : TorusFields.TorusBond (n * ℓ.side) => (volume : Measure unitInterval)))
def ChainNoise (ℓ : TorusLumps.StepParameters) : ℕ → ℕ → Type
  | 0, _ => Unit
  | s + 1, n => ChainNoise ℓ s (n * ℓ.side) × StepNoise ℓ n
instance instMeasurableSpaceChainNoise (ℓ : TorusLumps.StepParameters) :
    (s n : ℕ) → MeasurableSpace (ChainNoise ℓ s n)
  | 0, _ => inferInstanceAs (MeasurableSpace Unit)
  | s + 1, n =>
    letI := instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)
    inferInstanceAs (MeasurableSpace (ChainNoise ℓ s (n * ℓ.side) × StepNoise ℓ n))
def chainNoiseLaw (ℓ : TorusLumps.StepParameters) : (s n : ℕ) → [NeZero n] → Measure (ChainNoise ℓ s n)
  | 0, _, _ => Measure.dirac ()
  | s + 1, n, _ =>
    letI := instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)
    (chainNoiseLaw ℓ s (n * ℓ.side)).prod (stepNoiseLaw ℓ n)
def baseChoiceOfOffsets {n : ℕ} [NeZero n] (o : TorusFields.TorusSite n → TorusLumps.BlockOffset ℓ.side) :
    StepCosts.BaseChoice ℓ.side n :=
  fun y => StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 0
    (StepSettings.blockSite (TorusLumps.toTorusSite n y) (o (TorusLumps.toTorusSite n y)))
structure NoiseRule (ℓ : TorusLumps.StepParameters) where
  base : (s n : ℕ) → [NeZero n] → TorusFields.TorusField (n * ℓ.side) → TorusFields.TorusSite n → unitInterval →
    TorusLumps.BlockOffset ℓ.side
  value : (s n : ℕ) → [NeZero n] → TorusFields.TorusField (n * ℓ.side) →
    (TorusFields.TorusSite n → TorusLumps.BlockOffset ℓ.side) → TorusFields.TorusBond n → unitInterval →
    BlockAverages.UnitQuaternion
def NoiseRule.stepOutcome (rule : NoiseRule ℓ) (T : WeightedResponses.StageTower ℓ) (s n : ℕ) [NeZero n]
    (W : TorusFields.TorusField (n * ℓ.side)) (U : StepNoise ℓ n) : WeightedResponses.StepOutcome ℓ n :=
  open Classical in
  let o : TorusFields.TorusSite n → TorusLumps.BlockOffset ℓ.side := fun y => rule.base s n W y (U.1 y)
  let V : TorusFields.TorusField n := fun y i => rule.value s n W o (y, i) (U.2.1 (y, i))
  (baseChoiceOfOffsets o, V, (show Finset (TorusFields.TorusBond (n * ℓ.side)) from
    (StepSettings.markedBonds (T.stage s).toStepSetup
      (StepSettings.hotCoreSites (T.stage s).toStepSetup V)).filter fun b =>
      ¬ ((U.2.2 b : ℝ) < StepSettings.bondMark (T.stage s).toStepSetup V W b)))
def NoiseRule.chain (rule : NoiseRule ℓ) (T : WeightedResponses.StageTower ℓ) :
    (s n : ℕ) → [NeZero n] → TorusFields.TorusField (WeightedResponses.fineSide ℓ.side s n) →
      ChainNoise ℓ s n → WeightedResponses.MarkedSample ℓ s n
  | 0, _, _, W, _ => W
  | s + 1, n, _, W, U =>
    (NoiseRule.chain rule T s (n * ℓ.side) W U.1,
      rule.stepOutcome T s n
        (WeightedResponses.topField ℓ s (n * ℓ.side) (NoiseRule.chain rule T s (n * ℓ.side) W U.1)) U.2)
def AgreeAbove (L : ℕ) [NeZero L] {n : ℕ} [NeZero n] (Q : Finset (TorusFields.TorusSite n))
    (W W' : TorusFields.TorusField (n * L)) : Prop :=
  ∀ b : TorusFields.TorusBond (n * L), TorusLumps.parentBlock L b.1 ∈ Q →
    TorusLumps.parentBlock L (b.1 + TorusFields.unitStep (n * L) b.2) ∈ Q → W b.1 b.2 = W' b.1 b.2
structure NoiseRule.IsAdmissible (rule : NoiseRule ℓ) (T : WeightedResponses.StageTower ℓ) : Prop where
  base_measurable : ∀ (s n : ℕ) [NeZero n] (y : TorusFields.TorusSite n),
    Measurable fun p : TorusFields.TorusField (n * ℓ.side) × unitInterval => rule.base s n p.1 y p.2
  value_measurable : ∀ (s n : ℕ) [NeZero n] (o : TorusFields.TorusSite n → TorusLumps.BlockOffset ℓ.side)
      (c : TorusFields.TorusBond n),
    Measurable fun p : TorusFields.TorusField (n * ℓ.side) × unitInterval => rule.value s n p.1 o c p.2
  base_law : ∀ (s n : ℕ) [NeZero n] (W : TorusFields.TorusField (n * ℓ.side))
      (o : TorusFields.TorusSite n → TorusLumps.BlockOffset ℓ.side),
    (Measure.pi fun _ : TorusFields.TorusSite n => (volume : Measure unitInterval)).real
        {U | ∀ y, rule.base s n W y (U y) = o y} =
      StepSettings.baseLaw (R := (T.stage s).toStepSetup) W (baseChoiceOfOffsets o)
  value_law : ∀ (s n : ℕ) [NeZero n] (W : TorusFields.TorusField (n * ℓ.side))
      (o : TorusFields.TorusSite n → TorusLumps.BlockOffset ℓ.side) (c : TorusFields.TorusBond n),
    (volume : Measure unitInterval).map (rule.value s n W o c) =
      TorusFields.haarUnit.withDensity fun h => ENNReal.ofReal
        (TorusLumps.bondKernel ℓ (T.stage s).coupling
          (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0 W)
          (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 (fun _ _ => h : TorusFields.TorusField n))
          (baseChoiceOfOffsets o)
          (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 c.1, c.2))
  base_depends : ∀ (s n : ℕ) [NeZero n] (W W' : TorusFields.TorusField (n * ℓ.side)) (y : TorusFields.TorusSite n)
      (v : unitInterval),
    AgreeAbove ℓ.side (HullTrees.box y 3) W W' → rule.base s n W y v = rule.base s n W' y v
  value_depends : ∀ (s n : ℕ) [NeZero n] (W W' : TorusFields.TorusField (n * ℓ.side))
      (o o' : TorusFields.TorusSite n → TorusLumps.BlockOffset ℓ.side) (c : TorusFields.TorusBond n)
      (v : unitInterval), AgreeAbove ℓ.side (HullTrees.box c.1 4) W W' → o c.1 = o' c.1 →
      o (c.1 + TorusFields.unitStep n c.2) = o' (c.1 + TorusFields.unitStep n c.2) →
    rule.value s n W o c v = rule.value s n W' o' c v
  base_translate : ∀ (s n : ℕ) [NeZero n] (W : TorusFields.TorusField (n * ℓ.side)) (h : Fin 4 → ℤ)
      (y : TorusFields.TorusSite n) (v : unitInterval),
    rule.base s n (TorusFields.translate (TorusFields.siteOfInt fun i => (ℓ.side : ℤ) * h i) W) y v =
      rule.base s n W (y + TorusFields.siteOfInt h) v
  value_translate : ∀ (s n : ℕ) [NeZero n] (W : TorusFields.TorusField (n * ℓ.side))
      (o : TorusFields.TorusSite n → TorusLumps.BlockOffset ℓ.side) (h : Fin 4 → ℤ)
      (c : TorusFields.TorusBond n) (v : unitInterval),
    rule.value s n (TorusFields.translate (TorusFields.siteOfInt fun i => (ℓ.side : ℤ) * h i) W)
        (fun y => o (y + TorusFields.siteOfInt h)) c v =
      rule.value s n W o (c.1 + TorusFields.siteOfInt h, c.2) v
def sitesUnder (L : ℕ) [NeZero L] : (u n : ℕ) → [NeZero n] → Finset (TorusFields.TorusSite n) →
    Finset (TorusFields.TorusSite (WeightedResponses.fineSide L u n))
  | 0, _, _, Q => Q
  | u + 1, n, _, Q => sitesUnder L u (n * L) (TorusLumps.sitesInBlocks L Q)
def NoiseAgreeAbove (ℓ : TorusLumps.StepParameters) : (u n : ℕ) → [NeZero n] → Finset (TorusFields.TorusSite n) →
    ChainNoise ℓ u n → ChainNoise ℓ u n → Prop
  | 0, _, _, _, _, _ => True
  | u + 1, n, _, Q, U, U' => NoiseAgreeAbove ℓ u (n * ℓ.side) (TorusLumps.sitesInBlocks ℓ.side Q) U.1 U'.1 ∧
      (∀ y ∈ Q, U.2.1 y = U'.2.1 y) ∧ (∀ c : TorusFields.TorusBond n, c.1 ∈ Q → U.2.2.1 c = U'.2.2.1 c) ∧
      ∀ b : TorusFields.TorusBond (n * ℓ.side), TorusLumps.parentBlock ℓ.side b.1 ∈ Q → U.2.2.2 b = U'.2.2.2 b
def DependsAbove (ℓ : TorusLumps.StepParameters) (u n : ℕ) [NeZero n] (Q : Finset (TorusFields.TorusSite n))
    (Φ : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ) : Prop :=
  ∀ (W W' : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n)) (U U' : ChainNoise ℓ u n),
    (∀ b : TorusFields.TorusBond (WeightedResponses.fineSide ℓ.side u n), b.1 ∈ sitesUnder ℓ.side u n Q →
      b.1 + TorusFields.unitStep (WeightedResponses.fineSide ℓ.side u n) b.2 ∈ sitesUnder ℓ.side u n Q →
        W b.1 b.2 = W' b.1 b.2) →
    NoiseAgreeAbove ℓ u n Q U U' → Φ (W, U) = Φ (W', U')
def noiseTranslate (ℓ : TorusLumps.StepParameters) :
    (u n : ℕ) → [NeZero n] → (Fin 4 → ℤ) → ChainNoise ℓ u n → ChainNoise ℓ u n
  | 0, _, _, _, U => U
  | u + 1, n, _, h, U =>
    (noiseTranslate ℓ u (n * ℓ.side) (fun i => (ℓ.side : ℤ) * h i) U.1,
      (fun y => U.2.1 (y + TorusFields.siteOfInt h), fun c => U.2.2.1 (c.1 + TorusFields.siteOfInt h, c.2),
        fun b => U.2.2.2 (b.1 + TorusFields.siteOfInt (fun i => (ℓ.side : ℤ) * h i), b.2)))
def pairTranslate (ℓ : TorusLumps.StepParameters) (u n : ℕ) [NeZero n] (h : Fin 4 → ℤ)
    (p : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n) × ChainNoise ℓ u n) :
    TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n) × ChainNoise ℓ u n :=
  (TorusFields.translate (TorusFields.siteOfInt fun i => (ℓ.side : ℤ) ^ u * h i) p.1, noiseTranslate ℓ u n h p.2)
def noiseExpectation (ℓ : TorusLumps.StepParameters) (u n : ℕ) [NeZero n]
    (Φ : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ)
    (W : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n)) : ℝ :=
  ∫ U, Φ (W, U) ∂(chainNoiseLaw ℓ u n)
def pairExpectation (ℓ : TorusLumps.StepParameters) (β : ℝ) (u n : ℕ) [NeZero n]
    (Φ : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ) : ℝ :=
  ∫ W, noiseExpectation ℓ u n Φ W ∂(WeightedResponses.wilsonLaw β (WeightedResponses.fineSide ℓ.side u n))
structure IsCellObservable (ℓ : TorusLumps.StepParameters) (g : ChessboardGrids.MirrorGrid) (u n : ℕ) [NeZero n]
    (c : Fin 4 → ℕ)
    (Φ : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ) : Prop where
  measurable : Measurable Φ
  bounded : ∃ C : ℝ, ∀ p, |Φ p| ≤ C
  nonneg : ∀ p, 0 ≤ Φ p
  depends : DependsAbove ℓ u n (g.cellSites n c) Φ
open Classical in
def unitIndicator (rule : NoiseRule ℓ) (T : WeightedResponses.StageTower ℓ) (u n : ℕ) [NeZero n]
    (z : TorusFields.TorusSite n)
    (p : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n) × ChainNoise ℓ u n) : ℝ :=
  if HullTrees.IsUnit T u n (rule.chain T u n p.1 p.2) z then 1 else 0
def localScore (rule : NoiseRule ℓ) (T : WeightedResponses.StageTower ℓ) (s₁ : ℝ) (u n : ℕ) [NeZero n]
    (z : TorusFields.TorusSite n) (D : ℝ) (k : ℕ)
    (p : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n) × ChainNoise ℓ u n) : ℝ :=
  HullTrees.localScoreMoment T s₁ u n z D k (rule.chain T u n p.1 p.2)
end YangMills.Construction.ChainNoise
end

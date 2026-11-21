import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped unitInterval
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps RenormalizationStepParameters StepSettings StepCosts WeightedResponses BlockAverages LumpContours
variable {ℓ : StepParameters}
abbrev StepNoise (ℓ : StepParameters) (n : ℕ) : Type :=
  (TorusSite n → I) × (TorusBond n → I) × (TorusBond (n * ℓ.side) → I)
def stepNoiseMeasure (ℓ : StepParameters) (n : ℕ) [NeZero n] : Measure (StepNoise ℓ n) :=
  (Measure.pi fun _ : TorusSite n => (volume : Measure I)).prod
    ((Measure.pi fun _ : TorusBond n => (volume : Measure I)).prod
      (Measure.pi fun _ : TorusBond (n * ℓ.side) => (volume : Measure I)))
def ChainNoise (ℓ : StepParameters) : ℕ → ℕ → Type
  | 0, _ => Unit
  | s + 1, n => ChainNoise ℓ s (n * ℓ.side) × StepNoise ℓ n
instance instMeasurableSpaceChainNoise (ℓ : StepParameters) : (s n : ℕ) → MeasurableSpace (ChainNoise ℓ s n)
  | 0, _ => inferInstanceAs (MeasurableSpace Unit)
  | s + 1, n =>
    letI := instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)
    inferInstanceAs (MeasurableSpace (ChainNoise ℓ s (n * ℓ.side) × StepNoise ℓ n))
def chainNoiseMeasure (ℓ : StepParameters) : (s n : ℕ) → [NeZero n] → Measure (ChainNoise ℓ s n)
  | 0, _, _ => Measure.dirac ()
  | s + 1, n, _ =>
    letI := instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)
    (chainNoiseMeasure ℓ s (n * ℓ.side)).prod (stepNoiseMeasure ℓ n)
def NoiseAgreesOn (ℓ : StepParameters) :
    (s n : ℕ) → [NeZero n] → Finset (TorusSite n) → ChainNoise ℓ s n → ChainNoise ℓ s n → Prop
  | 0, _, _, _, _, _ => True
  | s + 1, n, _, c, ξ, ξ' =>
      NoiseAgreesOn ℓ s (n * ℓ.side) (sitesInBlocks ℓ.side c) ξ.1 ξ'.1 ∧
      (∀ y ∈ c, ξ.2.1 y = ξ'.2.1 y) ∧
      (∀ b : TorusBond n, b.1 ∈ c → b.1 + TorusFields.unitStep n b.2 ∈ c → ξ.2.2.1 b = ξ'.2.2.1 b) ∧
      (∀ b : TorusBond (n * ℓ.side), b.1 ∈ sitesInBlocks ℓ.side c →
        b.1 + TorusFields.unitStep (n * ℓ.side) b.2 ∈ sitesInBlocks ℓ.side c →
        ξ.2.2.2 b = ξ'.2.2.2 b)
def FieldsAgreeOn {m : ℕ} (c : Finset (TorusSite m)) (W W' : TorusField m) : Prop :=
  ∀ b : TorusBond m, b.1 ∈ c → b.1 + TorusFields.unitStep m b.2 ∈ c → W b.1 b.2 = W' b.1 b.2
structure StepSampler (R : StepSetup) where
  sampleBase : ∀ (n : ℕ) [NeZero n], TorusField (n * R.params.side) → TorusSite n → I →
    (stepBlockFrame R.params.side n).Site 0
  sampleLink : ∀ (n : ℕ) [NeZero n], TorusField (n * R.params.side) → BaseChoice R.params.side n →
    TorusBond n → I → UnitQuaternion
section Sampling
variable {R : StepSetup} {n : ℕ} [NeZero n]
def StepSampler.sampledBases (S : StepSampler R) (W : TorusField (n * R.params.side)) (ξ : StepNoise R.params n) :
    BaseChoice R.params.side n :=
  fun y => S.sampleBase n W (toTorusSite n y) (ξ.1 (toTorusSite n y))
def StepSampler.sampledField (S : StepSampler R) (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n)
    (ξ : StepNoise R.params n) : TorusField n :=
  fun x i => S.sampleLink n W b (x, i) (ξ.2.1 (x, i))
open Classical in
def markedBadBonds (R : StepSetup) (W : TorusField (n * R.params.side)) (V : TorusField n) (ξ : StepNoise R.params n) :
    BondSet (n * R.params.side) :=
  (markedBonds R (hotCoreSites R V)).filter fun b => StepSettings.bondMark R V W b < ((ξ.2.2 b : I) : ℝ)
def StepSampler.sample (S : StepSampler R) (W : TorusField (n * R.params.side)) (ξ : StepNoise R.params n) :
    StepOutcome R.params n :=
  (S.sampledBases W ξ, S.sampledField W (S.sampledBases W ξ) ξ,
    markedBadBonds R W (S.sampledField W (S.sampledBases W ξ) ξ) ξ)
end Sampling
structure StepSampler.IsFaithful {R : StepSetup} (S : StepSampler R) : Prop where
  measurable_base : ∀ (n : ℕ) [NeZero n] (y : TorusSite n),
    Measurable fun p : TorusField (n * R.params.side) × I => S.sampleBase n p.1 y p.2
  measurable_link : ∀ (n : ℕ) [NeZero n] (c : TorusBond n),
    Measurable fun p : TorusField (n * R.params.side) × BaseChoice R.params.side n × I =>
      S.sampleLink n p.1 p.2.1 c p.2.2
  base_distribution : ∀ (n : ℕ) [NeZero n] (W : TorusField (n * R.params.side)) (y : TorusSite n)
    (z : (stepBlockFrame R.params.side n).Site 0),
    (volume : Measure I) {u | S.sampleBase n W y u = z} =
      ENNReal.ofReal (blockBaseWeight R.params
        (LumpContours.hotLumps R.params.grid R.params.threshold (levelSites (stepBlockFrame R.params.side n) 0)
          (readAtLevel (stepBlockFrame R.params.side n) 0 W))
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) z)
  link_distribution : ∀ (n : ℕ) [NeZero n] (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n)
    (c : TorusBond n) (A : Set UnitQuaternion),
    MeasurableSet A → (volume : Measure I) {u | S.sampleLink n W b c u ∈ A} =
      ∫⁻ g in A, ENNReal.ofReal (bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 (fun _ _ => g : TorusField n)) b
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2)) ∂haarUnit
  base_mem_sitesBelow : ∀ (n : ℕ) [NeZero n] (W : TorusField (n * R.params.side)) (y : TorusSite n) (u : I),
    S.sampleBase n W y u ∈ sitesBelow 0 (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
  base_local : ∀ (n : ℕ) [NeZero n] (W W' : TorusField (n * R.params.side)) (y : TorusSite n) (u : I),
    FieldsAgreeOn (sitesInBlocks R.params.side (thickening 3 {y})) W W' → S.sampleBase n W y u = S.sampleBase n W' y u
  link_local : ∀ (n : ℕ) [NeZero n] (W W' : TorusField (n * R.params.side)) (b b' : BaseChoice R.params.side n)
    (c : TorusBond n) (u : I),
    FieldsAgreeOn (sitesInBlocks R.params.side (thickening 3 {c.1, c.1 + TorusFields.unitStep n c.2})) W W' →
    b (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1) ∈
      sitesBelow 0 (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1) →
    b (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (c.1 + TorusFields.unitStep n c.2)) ∈
      sitesBelow 0 (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (c.1 + TorusFields.unitStep n c.2)) →
    b (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1) =
      b' (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1) →
    b (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (c.1 + TorusFields.unitStep n c.2)) =
      b' (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (c.1 + TorusFields.unitStep n c.2)) →
    S.sampleLink n W b c u = S.sampleLink n W' b' c u
abbrev ChainSampler (T : StageTower ℓ) : Type := ∀ s : ℕ, StepSampler (T.stage s).toStepSetup
def sampleChain (T : StageTower ℓ) (S : ChainSampler T) :
    (s n : ℕ) → [NeZero n] → TorusField (fineSide ℓ.side s n) → ChainNoise ℓ s n → MarkedSample ℓ s n
  | 0, _, _, U, _ => U
  | s + 1, n, _, U, ξ =>
      (sampleChain T S s (n * ℓ.side) U ξ.1,
        (S s).sample (topField ℓ s (n * ℓ.side) (sampleChain T S s (n * ℓ.side) U ξ.1)) ξ.2)
open Classical in
def cellEventProb (T : StageTower ℓ) (S : ChainSampler T) (k n : ℕ) [NeZero n] (c : Finset (TorusSite n))
    (U : TorusField (fineSide ℓ.side k n)) : ℝ :=
  (chainNoiseMeasure ℓ k n {ξ | CellEvent T k n (sampleChain T S k n U ξ) c}).toReal
def lowerSumExpMean (T : StageTower ℓ) (S : ChainSampler T) (s₀ s₁ : ℝ) (k n : ℕ) [NeZero n]
    (c : Finset (TorusSite n)) (U : TorusField (fineSide ℓ.side k n)) : ℝ :=
  ∫ ξ, Real.exp (lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n U ξ) c) ∂(chainNoiseMeasure ℓ k n)
def CellEventIsLocal {ℓ : StepParameters} (T : StageTower ℓ) (S : ChainSampler T) (k n : ℕ) [NeZero n]
    (c : Finset (TorusSite n)) : Prop :=
  MeasurableSet {p : TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n |
      CellEvent T k n (sampleChain T S k n p.1 p.2) c} ∧
    ∀ (U U' : TorusField (fineSide ℓ.side k n)) (ξ ξ' : ChainNoise ℓ k n),
      FieldsAgreeOn (cellBelow ℓ.side k n c) U U' →
      NoiseAgreesOn ℓ k n c ξ ξ' →
      (CellEvent T k n (sampleChain T S k n U ξ) c ↔ CellEvent T k n (sampleChain T S k n U' ξ') c)
def LowerSumIsLocal {ℓ : StepParameters} (T : StageTower ℓ) (S : ChainSampler T) (s₀ s₁ : ℝ) (k n : ℕ) [NeZero n]
    (c : Finset (TorusSite n)) : Prop :=
  Measurable (fun p : TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n =>
      lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n p.1 p.2) c) ∧
    ∀ (U U' : TorusField (fineSide ℓ.side k n)) (ξ ξ' : ChainNoise ℓ k n),
      FieldsAgreeOn (cellBelow ℓ.side k n c) U U' →
      NoiseAgreesOn ℓ k n c ξ ξ' →
      lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n U ξ) c =
        lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n U' ξ') c
end YangMills.Construction.CellWindows
end

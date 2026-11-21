import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
section Canonical
variable {V : Type} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V]
def gaussianVariance (E : V → ℝ) (f : V →ₗ[ℝ] ℝ) : ℝ := sSup {w | ∃ x, 0 < E x ∧ w = f x ^ 2 / E x}
structure IsCanonicalGaussian (E : V → ℝ) (μ : Measure V) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  map_eq : ∀ f : V →ₗ[ℝ] ℝ, (∀ x, E x = 0 → f x = 0) →
    μ.map f = gaussianReal 0 (gaussianVariance E f).toNNReal
end Canonical
section Chain
variable (L : ℕ) [NeZero L]
def LevelBond : ℕ → ℕ → Type
  | 0, n => TorusFields.TorusBond n
  | s + 1, n => LevelBond s (n * L) ⊕ TorusFields.TorusBond n
abbrev LevelChain (s n : ℕ) : Type := Fin 3 → LevelBond L s n → ℝ
variable {L}
def chainLower {s n : ℕ} (X : LevelChain L (s + 1) n) : LevelChain L s (n * L) := fun e c => X e (Sum.inl c)
def chainTop : (s n : ℕ) → LevelChain L s n → ColourForm n
  | 0, _, X => X
  | _ + 1, _, X => fun e b => X e (Sum.inr b)
def chainDescend (s : ℕ) : (d n : ℕ) → LevelChain L (s + d) n → LevelChain L s (WeightedResponses.fineSide L d n)
  | 0, _, X => X
  | d + 1, n, X => chainDescend s d (n * L) (chainLower X)
def chainBottom : (s n : ℕ) → LevelChain L s n → ColourForm (WeightedResponses.fineSide L s n)
  | 0, _, X => X
  | s + 1, n, X => chainBottom s (n * L) (chainLower X)
def chainDefect {s n : ℕ} [NeZero n] (X : LevelChain L (s + 1) n) : ColourForm n := fun e c =>
  chainTop (s + 1) n X e c - contourAverage L (chainTop s (n * L) (chainLower X) e) c
def levelEnergy (a : ℝ) : (s n : ℕ) → [NeZero n] → LevelChain L s n → ℝ
  | 0, n, _, X => ∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite n)),
      curlNorm (chainTop 0 n X) p ^ 2
  | s + 1, n, _, X => levelEnergy a s (n * L) (chainLower X) +
      a * ∑ c : TorusFields.TorusBond n, ∑ e : Fin 3, chainDefect X e c ^ 2
def IsTreeGauge : (s n : ℕ) → [NeZero n] → LevelChain L s n → Prop
  | 0, _, _, _ => True
  | s + 1, n, _, X => (∀ e, ∀ b ∉ StepCosts.chartBonds L n, chainTop s (n * L) (chainLower X) e b = 0) ∧
      IsTreeGauge s (n * L) (chainLower X)
def ChainNoise (L : ℕ) : ℕ → ℕ → Type
  | 0, n => Fin 3 × TorusFields.TorusPlaquette n
  | s + 1, n => ChainNoise L s (n * L) ⊕ (Fin 3 × TorusFields.TorusBond n)
def noisePairing : (s n : ℕ) → [NeZero n] → (ChainNoise L s n → ℝ) → LevelChain L s n → ℝ
  | 0, n, _, c, X => ∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite n)),
      ∑ e : Fin 3, c (e, p) * WeightedResponses.curl (chainTop 0 n X e) p
  | s + 1, n, _, c, X => noisePairing s (n * L) (fun i => c (Sum.inl i)) (chainLower X) +
      ∑ b : TorusFields.TorusBond n, ∑ e : Fin 3, c (Sum.inr (e, b)) * chainDefect X e b
def kineticForm (a : ℝ) (L u : ℕ) {n : ℕ} [NeZero n] (X : ColourForm n) : ℝ :=
  colourEval (WeightedResponses.maxwellKernel a L u) X X
end Chain
section Fluctuations
variable (a ρA : ℝ) (L : ℕ) [NeZero L]
abbrev ChartBondIndex (u n : ℕ) : Type :=
  ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u n)))
abbrev StepFluctuation (u n : ℕ) : Type := EuclideanSpace ℝ (Fin 3 × ChartBondIndex L u n)
variable {L}
open Classical in
def extendChart {u n : ℕ} [NeZero n] (η : ChartBondIndex L u n → ℝ) : TorusFields.TorusBond (n * L) → ℝ := fun c =>
  ∑ b : ChartBondIndex L u n,
    if (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).depth c.1, c.2) = b.1
    then η b else 0
def extendFluctuation {u n : ℕ} [NeZero n] (η : StepFluctuation L u n) : ColourForm (n * L) := fun e =>
  extendChart fun b => η (e, b)
def chartValues {u n : ℕ} [NeZero n] (X : ColourForm (n * L)) (e : Fin 3) (b : ChartBondIndex L u n) : ℝ :=
  ∑ c : TorusFields.TorusBond (n * L), open Classical in
    if (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).depth c.1, c.2) = b.1
    then X e c else 0
variable (L)
open Classical in
def fluctuationCov (x : ℝ) (u n : ℕ) :
    Matrix (Fin 3 × ChartBondIndex L u n) (Fin 3 × ChartBondIndex L u n) ℝ :=
  fun i j => if i.1 = j.1 then x⁻¹ * (WeightedResponses.trivialHessian a L u n)⁻¹ i.2 j.2 else 0
open Classical in
def fluctuationGaussian (x : ℝ) (u n : ℕ) : Measure (StepFluctuation L u n) :=
  multivariateGaussian 0 (fluctuationCov a L x u n)
def FluctuationSample (t : ℕ) : ℕ → ℕ → Type
  | 0, _ => Unit
  | d + 1, n => StepFluctuation L (t + d) n × FluctuationSample t d (n * L)
instance instMeasurableSpaceFluctuationSample (t : ℕ) : (d n : ℕ) → MeasurableSpace (FluctuationSample L t d n)
  | 0, _ => inferInstanceAs (MeasurableSpace Unit)
  | d + 1, n =>
    letI := instMeasurableSpaceFluctuationSample t d (n * L)
    inferInstanceAs (MeasurableSpace (StepFluctuation L (t + d) n × FluctuationSample L t d (n * L)))
def fluctuationSampleLaw (t : ℕ) : (d n : ℕ) → Measure (FluctuationSample L t d n)
  | 0, _ => Measure.dirac ()
  | d + 1, n =>
    letI := instMeasurableSpaceFluctuationSample L t d (n * L)
    (fluctuationGaussian a L 1 (t + d) n).prod (fluctuationSampleLaw t d (n * L))
variable {L}
def descendWithNoise (t : ℕ) (c : ℝ) : (d n : ℕ) → [NeZero n] → ColourForm n → FluctuationSample L t d n →
    ColourForm (WeightedResponses.fineSide L d n)
  | 0, _, _, A, _ => A
  | d + 1, n, _, A, w => descendWithNoise t c d (n * L)
      (fun e b => pushColours a ρA L (t + d) A e b + c * extendFluctuation w.1 e b) w.2
def descend (t : ℕ) : (d n : ℕ) → [NeZero n] → ColourForm n → ColourForm (WeightedResponses.fineSide L d n)
  | 0, _, _, A => A
  | d + 1, n, _, A => descend t d (n * L) (pushColours a ρA L (t + d) A)
end Fluctuations
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
def formProduct (t n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) (Z : ColourForm n) : ℝ :=
  ∏ i ∈ B, S.scaleCoupling / 2 * colourEval (S.supportForm t n i) Z Z
def formProductMean (d n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) (A : ColourForm n) : ℝ :=
  ∫ w, S.formProduct S.lastSeparated (WeightedResponses.fineSide Λ.stepParams.side d n) B
      (descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d n A w)
    ∂(fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n)
end MomentPoint
end YangMills.Construction.MomentLaw
end

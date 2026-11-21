import YangMills.Construction.LawByMomentsOfTheFlow.CyclicFormulaOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
section Torus
variable {m : ℕ} [NeZero m]
def curlVec (A : TorusFields.TorusBond m → ℝ) : EuclideanSpace ℝ (WeightedResponses.OrientedPlaquette m) :=
  WithLp.toLp 2 fun p => WeightedResponses.curl A p.1
def curvatureSubspace (m : ℕ) [NeZero m] : Submodule ℝ (EuclideanSpace ℝ (WeightedResponses.OrientedPlaquette m)) :=
  Submodule.span ℝ (Set.range curlVec)
open Classical in
def torusCurvatureProjection (p p' : WeightedResponses.OrientedPlaquette m) : ℝ :=
  inner ℝ (EuclideanSpace.single p (1 : ℝ)) ((curvatureSubspace m).starProjection (EuclideanSpace.single p' (1 : ℝ)))
variable (m) in
def curvatureVariance (c : TorusFields.TorusPlaquette m → ℝ) : ℝ :=
  ∑ p : WeightedResponses.OrientedPlaquette m, ∑ p' : WeightedResponses.OrientedPlaquette m,
    c p.1 * torusCurvatureProjection p p' * c p'.1
end Torus
section Lattice
abbrev IntPlaquette : Type := (Fin 4 → ℤ) × CyclicFormula.OrderedDirectionPair
abbrev IntBond : Type := (Fin 4 → ℤ) × Fin 4
def intCurl (A : IntBond →₀ ℝ) (p : IntPlaquette) : ℝ :=
  A (p.1, p.2.1.1) + A (p.1 + Pi.single p.2.1.1 1, p.2.1.2) - A (p.1 + Pi.single p.2.1.2 1, p.2.1.1) - A (p.1, p.2.1.2)
abbrev PlaquetteL2 : Type := lp (fun _ : IntPlaquette => ℝ) 2
def intCurvatures : Submodule ℝ PlaquetteL2 :=
  (Submodule.span ℝ {v : PlaquetteL2 | ∃ A : IntBond →₀ ℝ, ∀ p, v p = intCurl A p}).topologicalClosure
instance : CompleteSpace intCurvatures :=
  (show IsClosed (intCurvatures : Set PlaquetteL2) from Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe
open Classical in
def intCurvatureProjection (p p' : IntPlaquette) : ℝ :=
  inner ℝ (lp.single 2 p (1 : ℝ) : PlaquetteL2) (intCurvatures.starProjection (lp.single 2 p' (1 : ℝ)))
def intBarycenter (p : IntPlaquette) : TestFunctions.EuclideanFourSpace :=
  WithLp.toLp 2 fun a => (p.1 a : ℝ) + (if a = p.2.1.1 then 1 / 2 else 0) + (if a = p.2.1.2 then 1 / 2 else 0)
def scaledWeight (L s : ℕ) (φ : TestFunctions.EuclideanFourSpace → ℝ) (p : IntPlaquette) : ℝ :=
  φ (((L : ℝ) ^ s)⁻¹ • intBarycenter p)
def plaquetteBox (b : ℕ) : Finset IntPlaquette :=
  Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(b : ℤ)) (b : ℤ)) ×ˢ Finset.univ
variable {k : ℕ} [NeZero k]
def latticeCycleSum (L s b : ℕ) (φ : Fin k → TestFunctions.EuclideanFourSpace → ℝ) : ℝ :=
  3 * (if k = 2 then 1 / 2 else 1) * ∑ σ ∈ CyclicFormula.unorientedCyclicOrders k,
    ∑ p ∈ Fintype.piFinset (fun _ : Fin k => plaquetteBox b),
    (∏ i, scaledWeight L s (φ i) (p i)) * ∏ c : Fin k, intCurvatureProjection (p (σ c)) (p (σ (c + 1)))
def IsLift {m : ℕ} (P : IntPlaquette) (p : WeightedResponses.OrientedPlaquette m) : Prop :=
  (∀ a, ((P.1 a : ℤ) : ZMod m) = p.1.1 a) ∧ P.2.1 = p.1.2
end Lattice
section Observable
variable {L : ℕ} [NeZero L]
def completedObservable (a : ℝ) : (s n : ℕ) → [NeZero n] →
    WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide L s n) → LevelChain L s n → ℝ
  | 0, n, _, h, X => (1 / 2) * ∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite n)),
      h p * curlNorm (chainTop 0 n X) p ^ 2
  | s + 1, n, _, h, X => completedObservable a s (n * L) h (chainLower X) +
      a * ∑ c : TorusFields.TorusBond n, ResponseInTheExpansion.bondBlockMean L (s + 1) n h c *
        ((1 / 2) * ∑ e : Fin 3, chainDefect X e c ^ 2 - 3 / (2 * a))
def noiseVariance (a : ℝ) : (s n : ℕ) → [NeZero n] → (ChainNoise L s n → ℝ) → ℝ
  | 0, n, _, c => ∑ e : Fin 3, curvatureVariance n fun p => c (e, p)
  | s + 1, n, _, c => noiseVariance a s (n * L) (fun i => c (Sum.inl i)) +
      a⁻¹ * ∑ b : TorusFields.TorusBond n, ∑ e : Fin 3, c (Sum.inr (e, b)) ^ 2
def baseObservable {s n : ℕ} [NeZero n] (h : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide L s n))
    (X : LevelChain L s n) : ℝ :=
  (1 / 2) * ∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite (WeightedResponses.fineSide L s n))),
    h p * curlNorm (chainBottom s n X) p ^ 2
def stepDefect (a ρA : ℝ) (u m : ℕ) [NeZero m] (Z : LevelChain L (u + 1) m) : ColourForm (m * L) := fun e b =>
  chainTop u (m * L) (chainLower Z) e b - pushColours a ρA L u (chainTop (u + 1) m Z) e b
end Observable
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
def torusCumulant : ℂ :=
  WeightedResponses.connectedCurvature S.β
    (WeightedResponses.fineSide Λ.stepParams.side S.data.windowLevel (S.data.period Λ.stepParams.side)) fun i => S.weight i _
def responseCumulant : ℝ :=
  jointCumulant (S.law S.lastSeparated (S.levelSide S.lastSeparated)) fun i w =>
    S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)
def latticeCycleSumAt (s : ℕ) : ℝ :=
  latticeCycleSum Λ.stepParams.side s (⌈Λ.R * (Λ.stepParams.side : ℝ) ^ s⌉₊ + 2) S.data.fn
def cyclicLimit : ℝ := CyclicFormula.cyclicMomentFormula Λ.k S.data.fn
abbrev energy (s n : ℕ) [NeZero n] : LevelChain Λ.stepParams.side s n → ℝ := levelEnergy Λ.stepParams.coupling s n
def halfForm (d n : ℕ) [NeZero n] (i : Fin Λ.k) (X : LevelChain Λ.stepParams.side (S.lastSeparated + d) n) : ℝ :=
  (1 / 2) * colourEval (S.supportForm S.lastSeparated (WeightedResponses.fineSide Λ.stepParams.side d n) i)
    (chainTop S.lastSeparated _ (chainDescend S.lastSeparated d n X))
    (chainTop S.lastSeparated _ (chainDescend S.lastSeparated d n X))
def completedAt (d n : ℕ) [NeZero n] (i : Fin Λ.k) (X : LevelChain Λ.stepParams.side (S.lastSeparated + d) n) : ℝ :=
  completedObservable Λ.stepParams.coupling S.lastSeparated (WeightedResponses.fineSide Λ.stepParams.side d n) (S.weight i _)
    (chainDescend S.lastSeparated d n X)
def observableAt (s n : ℕ) [NeZero n] (i : Fin Λ.k) (X : LevelChain Λ.stepParams.side s n) : ℝ :=
  baseObservable (S.weight i _) X
end MomentPoint
end YangMills.Construction.MomentLaw
end

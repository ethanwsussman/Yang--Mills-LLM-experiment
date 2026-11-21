import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOverContoursOfAFormForm
import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
noncomputable section
open scoped Topology
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps StepCosts WeightedResponses
namespace TwoLevelMixtures
variable {n : ℕ}
def contourMean (L : ℕ) (W : TorusBond (n * L) → ℝ) (c : TorusBond n) : ℝ :=
  contourAverage (F := stepBlockFrame L n) (j := 0) (fun x i => W (toTorusSite (n * L) x, i))
    (torusSiteInFrame (stepBlockFrame L n) 1 c.1) c.2
def bondSiteDist (L : ℕ) (b : TorusBond (n * L)) (Y : TorusSite n) : ℕ := supDist (parentBlock L b.1) Y
def VanishesOnTrees (L : ℕ) [NeZero n] [NeZero L] (A : TorusBond (n * L) → ℝ) : Prop :=
  ∀ b, b ∉ chartBonds L n → A b = 0
section Forms
variable [NeZero n]
def contourPairing (L : ℕ) (W W' : TorusBond (n * L) → ℝ) : ℝ :=
  ∑ c : TorusBond n, contourMean L W c * contourMean L W' c
variable (a : ℝ) (L t : ℕ) (θ : ℝ) [NeZero L]
def interpKinetic (A A' : TorusBond (n * L) → ℝ) : ℝ :=
  (1 - θ) * maxwellForm a L t A A' + θ * maxwellForm a L (t + 1) A A'
def interpForm (A A' : TorusBond (n * L) → ℝ) : ℝ :=
  interpKinetic a L t θ A A' + a * contourPairing L A A'
def shiftedInterpForm (τ lam : ℝ) (A A' : TorusBond (n * L) → ℝ) : ℝ :=
  τ * interpForm a L t θ A A' + (1 - τ) * lam * ∑ b, A b * A' b
open Classical in
structure IsInterpResponse (a : ℝ) (L t : ℕ) (θ : ℝ) [NeZero L]
    (c : TorusBond n) (W : TorusBond (n * L) → ℝ) : Prop where
  vanishes : VanishesOnTrees L W
structure SolvesShiftedEq (τ lam : ℝ) (J g : TorusBond (n * L) → ℝ) : Prop where
  vanishes : VanishesOnTrees L g
  eq : ∀ φ : TorusBond (n * L) → ℝ, VanishesOnTrees L φ →
    shiftedInterpForm a L t θ τ lam g φ = ∑ b, J b * φ b
def interpEnergy (W : TorusField (n * L)) (V : TorusField n) : ℝ :=
  (1 - θ) * actionAtLevel a L t Finset.univ W + θ * actionAtLevel a L (t + 1) Finset.univ W +
    a * ∑ c : TorusBond n, blockFit (F := stepBlockFrame L n) (readAtLevel (stepBlockFrame L n) 0 W)
      (readAtLevel (stepBlockFrame L n) 1 V)
      (torusSiteInFrame (stepBlockFrame L n) 1 c.1, c.2)
end Forms
def torusChartField (L : ℕ) (w : TorusBond (n * L) → imaginaryQuaternions) (V : TorusField n) :
    TorusField (n * L) :=
  restrictToTorus (F := stepBlockFrame L n) (n * L)
    (chartedField (F := stepBlockFrame L n) (fun x i => w (toTorusSite (n * L) x, i))
      (readAtLevel (stepBlockFrame L n) (stepBlockFrame L n).top V))
section Germs
variable [NeZero n] (a : ℝ) (L t : ℕ) (θ : ℝ) [NeZero L]
def interpChartEnergy (w : TorusBond (n * L) → imaginaryQuaternions) (V : TorusField n) : ℝ :=
  interpEnergy a L t θ (torusChartField L w V) V
open Classical in
def singleBondCoord (b : TorusBond (n * L)) (X : imaginaryQuaternions) :
    TorusBond (n * L) → imaginaryQuaternions := fun b' => if b' = b then X else 0
structure IsCriticalGerm (w : TorusField n → TorusBond (n * L) → imaginaryQuaternions) : Prop where
  at_trivial : w (trivialField n) = 0
  vanishes_off_chart : ∀ V b, b ∉ chartBonds L n → w V b = 0
  analyticAt : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (b : TorusBond (n * L)),
    AnalyticAt ℝ (fun σ : Fin k → ℝ => w (perturb c X σ (trivialField n)) b) 0
  critical : ∀ᶠ V in 𝓝 (trivialField n), ∀ b ∈ chartBonds L n, ∀ X : imaginaryQuaternions,
    deriv (fun s : ℝ => interpChartEnergy a L t θ (w V + s • singleBondCoord L b X) V) 0 = 0
open Classical in
def germResponse (w : TorusField n → TorusBond (n * L) → imaginaryQuaternions) (c : TorusBond n)
    (X : imaginaryQuaternions) (b : TorusBond (n * L)) : ℝ :=
  - (((mixedDeriv (fun V => w V b) (trivialField n) ![c] ![X] : imaginaryQuaternions) : Quaternion ℝ) *
      (X : Quaternion ℝ)).re +
    if IsCrossingBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 b.1, b.2) ∧
        parentBlock L b.1 = c.1 ∧ b.2 = c.2
    then 1 else 0
def minimizerCoord (ρ : ℝ) (t : ℕ) (V : TorusField n) (b : TorusBond (n * L)) : imaginaryQuaternions :=
  torusCoordinate (F := torusFrame L t n) a ρ
    (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth b.1, b.2)
    (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)
end Germs
end TwoLevelMixtures
end
end YangMills.Construction

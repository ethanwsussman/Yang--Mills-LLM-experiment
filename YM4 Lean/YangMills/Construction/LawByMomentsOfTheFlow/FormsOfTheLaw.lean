import YangMills.Construction.ClusterExpansionOfAStep.ContoursOnTheTorus
import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusPaths TorusContours TorusLumps StepSettings StepCosts WeightedResponses BlockAverages
section Forms
variable {n : ℕ}
abbrev ColourForm (n : ℕ) : Type := Fin 3 → TorusBond n → ℝ
abbrev BondBilinear (n : ℕ) : Type := TorusBond n → TorusBond n → ℝ
variable [NeZero n]
def bilinearEval (q : BondBilinear n) (A A' : TorusBond n → ℝ) : ℝ :=
  ∑ b : TorusBond n, ∑ b' : TorusBond n, A b * q b b' * A' b'
def colourEval (q : BondBilinear n) (X X' : ColourForm n) : ℝ := ∑ e : Fin 3, bilinearEval q (X e) (X' e)
def curlNorm (X : ColourForm n) (p : TorusPlaquette n) : ℝ := Real.sqrt (∑ e : Fin 3, curl (X e) p ^ 2)
open Classical in
def bondIndicator (b : TorusBond n) : TorusBond n → ℝ := fun c => if c = b then 1 else 0
def latticeGradient (φ : TorusSite n → ℝ) : TorusBond n → ℝ := fun b => φ (b.1 + TorusFields.unitStep n b.2) - φ b.1
def constantOneForm (v : Fin 4 → ℝ) : TorusBond n → ℝ := fun b => v b.2
def AnnihilatesGradients (q : BondBilinear n) : Prop :=
  ∀ (φ : TorusSite n → ℝ) (A : TorusBond n → ℝ),
    bilinearEval q (latticeGradient φ) A = 0 ∧ bilinearEval q A (latticeGradient φ) = 0
def AnnihilatesClosedForms (q : BondBilinear n) : Prop :=
  AnnihilatesGradients q ∧ ∀ (v : Fin 4 → ℝ) (A : TorusBond n → ℝ),
    bilinearEval q (constantOneForm v) A = 0 ∧ bilinearEval q A (constantOneForm v) = 0
def hessianAtIdentity (G : TorusField n → ℝ) : BondBilinear n := fun b b' =>
  mixedDeriv G (trivialField n) ![b, b'] ![unitGenerator, unitGenerator]
def HasQuadraticFormAtIdentity (ψ : TorusField n → ℝ) : Prop :=
  (∀ (b : TorusBond n) (X : imaginaryQuaternions), mixedDeriv ψ (trivialField n) ![b] ![X] = 0) ∧
    ∃ q : BondBilinear n, (∀ b b', q b b' = q b' b) ∧ AnnihilatesGradients q ∧
      ∀ (b b' : TorusBond n) (X X' : imaginaryQuaternions), mixedDeriv ψ (trivialField n) ![b, b'] ![X, X'] =
        (∑ e : Fin 3, imaginaryComponent e X * imaginaryComponent e X') * q b b'
def tripleDiam (y : TorusSite n) (b b' : TorusBond n) : ℕ := supportDiam y ![b, b']
def IsDecayingAbout (ℓ : StepParameters) (sz : ℝ) (y : TorusSite n) (q : BondBilinear n) : Prop :=
  ∀ b b' : TorusBond n, |q b b'| ≤ sz / ℓ.weight (tripleDiam y b b')
end Forms
section Carried
variable (a ρA : ℝ) (L u : ℕ) [NeZero L] {n : ℕ} [NeZero n]
def pullbackForm (q : BondBilinear (n * L)) : BondBilinear n := fun c c' =>
  ∑ b : TorusBond (n * L), ∑ b' : TorusBond (n * L),
    responseKernel a ρA L u b c * q b b' * responseKernel a ρA L u b' c'
def pushColours (X : ColourForm n) : ColourForm (n * L) := fun e => responseMap a ρA L u (X e)
end Carried
section Contours
variable {m : ℕ}
def sumAlongWord (A : TorusBond m → ℝ) (w : BondWord m) : ℝ :=
  (w.map fun e => if e.2 then A e.1 else -A e.1).sum
variable (L : ℕ) {n : ℕ} [NeZero n]
def contourAverage (A : TorusBond (n * L) → ℝ) (c : TorusBond n) : ℝ :=
  contourWeight L * ∑ e ∈ contourIndex L, sumAlongWord A (contourWord L c.1 c.2 e)
def fitDefect (a ρA : ℝ) (u : ℕ) [NeZero L] (c'' c : TorusBond n) : ℝ :=
  contourAverage L (fun b => responseKernel a ρA L u b c) c'' - bondIndicator c c''
end Contours
section Classical
variable {ℓ : StepParameters} (T : StageTower ℓ) (A : ∀ t, ResponseSetup (T.stage t).toStepSetup)
def shareHessian (a : ℝ) (L u : ℕ) {n : ℕ} [NeZero n] (y : TorusSite n) : BondBilinear n :=
  hessianAtIdentity (levelShare a L u Finset.univ y)
def remainderHessian {R : StepSetup} (Z : ResponseSetup R) (n : ℕ) [NeZero n] (y : TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side R.depth n)) : BondBilinear n :=
  hessianAtIdentity (responseRemainder Z.cold n y h)
def responseHessian {R : StepSetup} (Z : ResponseSetup R) (n : ℕ) [NeZero n] (y : TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side R.depth n)) : BondBilinear n :=
  hessianAtIdentity fun W => Z.cold n y W h
def classicalRemainder : (t n : ℕ) → [NeZero n] →
    PlaquetteWeight (fineSide ℓ.side (T.stage t).depth n) → TorusSite n → BondBilinear n
  | 0, n, _, h, y => remainderHessian (A 0) n y h
  | t + 1, n, _, h, Y => fun c c' => ∑ y ∈ TorusLumps.sitesInBlocks ℓ.side {Y},
      pullbackForm ℓ.coupling (T.stage t).anchorRadius ℓ.side (T.stage t).depth (n := n) (fun b b' =>
        (blockMean ℓ.side (T.stage t).depth (n * ℓ.side) y h - blockMean ℓ.side ((T.stage t).depth + 1) n Y h) *
            shareHessian ℓ.coupling ℓ.side (T.stage t).depth y b b' +
          classicalRemainder t (n * ℓ.side) h y b b') c c'
def classicalQuadratic (t n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (T.stage t).depth n))
    (y : TorusSite n) : BondBilinear n :=
  fun b b' => blockMean ℓ.side (T.stage t).depth n y h * shareHessian ℓ.coupling ℓ.side (T.stage t).depth y b b' +
    classicalRemainder T A t n h y b b'
end Classical
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
def supportForm (u n : ℕ) [NeZero n] (i : Fin Λ.k) : BondBilinear n := fun b b' =>
  ∑ y ∈ S.supportAt u n i, classicalQuadratic S.tower S.resp u n (S.weight i _) y b b'
end MomentPoint
end YangMills.Construction.MomentLaw
end

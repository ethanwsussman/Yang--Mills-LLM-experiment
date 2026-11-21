import YangMills.Construction.Splines.TentAndCubicSplineDensity
import YangMills.Construction.TwoPoints.ThirdPropertyAndFamiliesOfSpectralMeasures
import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints.Shapes
def smoothedIcc (a b : ℝ) : ℝ → ℝ :=
  Splines.realConvolution ((Icc a b).indicator 1) Splines.splineDensity
def timeBump : ℝ → ℝ := smoothedIcc (9 / 4) (11 / 4)
def planePartitionOfUnity (z : Fin 2 → ℝ) : ℝ :=
  ∏ i, smoothedIcc (-(1 / 2)) (1 / 2) (z i)
def planePlateau (z : Fin 2 → ℝ) : ℝ :=
  ∏ i, smoothedIcc (-(5 / 4)) (5 / 4) (z i)
def ofRealFun {X : Type*} (f : X → ℝ) : X → ℂ := fun x => (f x : ℂ)
def openSquare (r : ℝ) : Set (Fin 2 → ℝ) := univ.pi fun _ => Ioo (-r) r
def closedSquare (r : ℝ) : Set (Fin 2 → ℝ) := univ.pi fun _ => Icc (-r) r
def SmoothedIccSpec (a b : ℝ) : Prop :=
  (∀ s, smoothedIcc a b s ∈ Icc (0 : ℝ) 1) ∧
  ContDiff ℝ 1 (smoothedIcc a b) ∧
  (∀ s, HasDerivAt (smoothedIcc a b)
    (Splines.splineDensity (s - a) - Splines.splineDensity (s - b)) s) ∧
  (∀ s, s ∉ Icc (a - 1 / 8) (b + 1 / 8) → smoothedIcc a b s = 0) ∧
  (∀ s, a + 1 / 8 ≤ s → s ≤ b - 1 / 8 → smoothedIcc a b s = 1) ∧
  ∫ s, smoothedIcc a b s = b - a
def IsTimeBump (f : ℝ → ℝ) : Prop :=
  ofRealFun f ∈ realCc1In (Ioo (2 : ℝ) 3) ∧
  (∀ s, 0 ≤ f s) ∧ IsGreatest (range f) 1 ∧ 1 / 2 ≤ ∫ s, f s
def IsPlanePartitionOfUnity (φ : (Fin 2 → ℝ) → ℝ) : Prop :=
  ofRealFun φ ∈ realCc1In (openSquare 1) ∧
  (∀ z, φ z ∈ Icc (0 : ℝ) 1) ∧
  ∀ z, HasSum (fun n : Fin 2 → ℤ => φ (z - fun i => (n i : ℝ))) 1
def IsPlanePlateau (φ : (Fin 2 → ℝ) → ℝ) : Prop :=
  ofRealFun φ ∈ realCc1In (openSquare (3 / 2)) ∧
  (∀ z, φ z ∈ Icc (0 : ℝ) 1) ∧
  ∀ z ∈ closedSquare 1, φ z = 1
def BddDeriv (f : ℝ → ℝ) : Prop :=
  BddAbove (range fun s => ‖deriv (ofRealFun f) s‖)
def ShapesExist.Statement : Prop :=
  (∀ a b : ℝ, a < b → SmoothedIccSpec a b) ∧
  IsTimeBump timeBump ∧
  IsPlanePartitionOfUnity planePartitionOfUnity ∧
  IsPlanePlateau planePlateau ∧
  BddDeriv timeBump ∧
  BddDeriv Splines.cubicSpline ∧
  gradPlaneEsup (ofRealFun planePartitionOfUnity) ≠ ∞ ∧
  gradPlaneEsup (ofRealFun planePlateau) ≠ ∞ ∧
  0 < derivUniformNorm (ofRealFun timeBump) ∧
  Integrable planePlateau ∧
  4 ≤ ∫ z, planePlateau z
end YangMills.Construction.TwoPoints.Shapes

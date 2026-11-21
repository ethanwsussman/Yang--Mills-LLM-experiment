import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.StepSettings YangMills.Construction.StepGas YangMills.Construction.WeightedResponses YangMills.Construction.ResponseInTheExpansion YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
section Boxes
variable {n : ℕ} [NeZero n]
def PlaquetteInBox (o : TorusSite n) (r : ℝ) (p : TorusPlaquette n) : Prop :=
  p.2.1 < p.2.2 ∧ ∀ c ∈ plaquetteVertices p.1 p.2.1 p.2.2, c ∈ supBall o r
def boxCurvature (o : TorusSite n) (r : ℝ) (W : TorusField n) : ℝ :=
  ⨆ p : {p : TorusPlaquette n // PlaquetteInBox o r p}, curvature W p.1.1 p.1.2.1 p.1.2.2
def axialCoords (ℓ : YangMills.Construction.TorusLumps.StepParameters) (W : TorusField n) (o : TorusSite n)
    (b : TorusBond n) : imaginaryQuaternions :=
  minimalLog (gaugeTransform (axialGaugeAt ℓ W o) W b)
def cutoffProfile (o : TorusSite n) (m : ℕ) (z : TorusSite n) : ℝ :=
  max 0 (min 1 ((2 * (m : ℝ) - 1 - (TorusFields.supDist z o : ℝ)) / ((m : ℝ) - 1)))
def cutoffCoords (ℓ : YangMills.Construction.TorusLumps.StepParameters) (W : TorusField n) (o : TorusSite n)
    (m : ℕ) (b : TorusBond n) : imaginaryQuaternions :=
  cutoffProfile o m b.1 • axialCoords ℓ W o b
def toColourForm (B : TorusBond n → imaginaryQuaternions) : ColourForm n := fun e b => imaginaryComponent e (B b)
def expField (v : ℝ) (B : TorusBond n → imaginaryQuaternions) : TorusField n := fun x i => expUnit (v • B (x, i))
def weightedCurvatureNorm {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (ω : TorusPlaquette n → ℝ) (q : ENNReal)
    (X : Ω → ColourForm n) : ENNReal :=
  ⨆ p : OrientedPlaquette n, ENNReal.ofReal (ω p.1) * eLpNorm (fun e => curlNorm (X e) p.1) q μ
end Boxes
section ColdSituation
variable {n : ℕ} [NeZero n]
def coldGroundOver (R : StepSetup) (V : TorusField n) : GasGround R n := ⟨Finset.univ, ∅, V, emptyCoarseState R⟩
def coldSettingOver (R : StepSetup) (V : TorusField n) : ChartSetting R n := (coldGroundOver R V).groundSetting
def coldExpectation (R : StepSetup) (V : TorusField n) (G : FreeCoords (coldSettingOver R V).free → ℝ) : ℝ :=
  weightedMean (chartDensity (coldSettingOver R V)) G
def coldFreeLaw (R : StepSetup) (V : TorusField n) : Measure (FreeCoords (coldSettingOver R V).free) :=
  ((∫⁻ η, ENNReal.ofReal (chartDensity (coldSettingOver R V) η))⁻¹) •
    (volume.withDensity fun η => ENNReal.ofReal (chartDensity (coldSettingOver R V) η))
def freeCoordForm {R : StepSetup} (s : ChartSetting R n) (η : FreeCoords s.free) :
    ColourForm (n * R.params.side) := fun e b =>
  open Classical in if hb : b ∈ s.free then η ⟨b, hb⟩ e else 0
def IsSlowlyVaryingPair (L : ℕ) (c : ℝ) (ω : TorusPlaquette (n * L) → ℝ) (ω' : TorusPlaquette n → ℝ) : Prop :=
  ∀ (p : TorusPlaquette (n * L)) (p' : TorusPlaquette n),
    ω p ≤ Real.exp (c * (1 + (TorusFields.supDist (parentBlock L p.1) p'.1 : ℝ))) * ω' p'
def finsetDist (A : Finset (TorusSite n)) (x : TorusSite n) : ℕ :=
  sInf ((fun z => TorusFields.supDist x z) '' (A : Set (TorusSite n)))
def ancestor (L e m : ℕ) (x : TorusSite n) : TorusSite m := fun a =>
  ((round (((x a).val : ℝ) / (L : ℝ) ^ e) : ℤ) : ZMod m)
end ColdSituation
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
def NoLumpNear (v : ℕ) (ρ : ℝ) : (d n : ℕ) → [NeZero n] → MarkedSample Λ.stepParams (v + d) n → Prop
  | 0, n, _, w => Disjoint (stageState S.tower v n w).2.1 (supBall (S.originSite v n) ρ)
  | d + 1, n, _, w => Disjoint (stageState S.tower (v + d + 1) n w).2.1 (supBall (S.originSite (v + d + 1) n) ρ) ∧
      NoLumpNear v ρ d (n * Λ.stepParams.side) w.1
variable (u n : ℕ) [NeZero n]
def localCurvature (W : TorusField n) : ℝ := boxCurvature (S.originSite u n) (2 * S.rangeSq) W
structure IsGoodConfig (W : TorusField n) (Y : Finset (TorusSite n)) : Prop where
  disjoint_lumps : Disjoint Y (supBall (S.originSite u n) (8 * S.rangeSq))
  curvature_le : S.localCurvature u n W ≤ S.scaleCoupling ^ (-(1 / 4) : ℝ)
def cutoffLie (W : TorusField n) : TorusBond n → imaginaryQuaternions :=
  cutoffCoords Λ.stepParams W (S.originSite u n) S.rangeSq
def smoothedField (W : TorusField n) : TorusField n := expField 1 (S.cutoffLie u n W)
def cutoffColourForm (W : TorusField n) : ColourForm n := toColourForm (S.cutoffLie u n W)
def distanceWeight (p : TorusPlaquette n) : ℝ :=
  Real.exp (-(Λ.stepParams.weightRate / 8 * max 0 ((TorusFields.supDist p.1 (S.originSite u n) : ℝ) - (S.radius : ℝ))))
end MomentPoint
end YangMills.Construction.MomentLaw
end

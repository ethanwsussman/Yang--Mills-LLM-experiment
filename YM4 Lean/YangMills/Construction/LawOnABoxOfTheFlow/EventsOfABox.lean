import YangMills.Construction.ClusterExpansionOfAStep.MirrorOfABox
import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxEvents
abbrev flowCoupling (ℓ : TorusLumps.StepParameters) (β : ℝ) (k : ℕ) : ℝ :=
  (TorusLumps.couplingFlow ℓ β k).1
structure IsBoxDatum (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ)
    (T : WeightedResponses.StageTower (Tb.stepParameters y)) (β κ₀ xs : ℝ) (k n : ℕ) : Prop where
  le_coupling : xs ≤ flowCoupling (Tb.stepParameters y) β k
  onFamily : ResponseInTheExpansion.IsTowerAtParameters Tb y T β
    (k + BoxGaussian.coarseningSteps (Tb.stepParameters y).side
      (BoxGaussian.boxRadius κ₀ (flowCoupling (Tb.stepParameters y) β k)))
  measurable : T.MarksMeasurable
  side_eq : ∃ e : ℕ, n = 2 * (Tb.stepParameters y).side ^ e
  coupling_rpow_le : flowCoupling (Tb.stepParameters y) β k ^ (1 / 10 : ℝ) ≤ n
variable {n : ℕ} [NeZero n]
def IsColdOnBox (o : TorusFields.TorusSite n) (R : ℕ) (δ : ℝ) (W : TorusFields.TorusField n)
    (Y : Finset (TorusFields.TorusSite n)) : Prop :=
  Disjoint Y (ResponseInTheExpansion.supBall o (3 * R)) ∧
    ∀ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)),
      TorusFields.curvature W p.1 p.2.1 p.2.2 ≤ δ
def descendingRadius (L top : ℕ) : ℕ → ℕ
  | 0 => top
  | i + 1 => L * descendingRadius L top i + 4 * L
def apexRadius (L s R : ℕ) : ℕ := R / (8 * L ^ s) + 8
def IsGoodSample (ℓ : TorusLumps.StepParameters) (k s top : ℕ) (δ f : ℝ) :
    (d n : ℕ) → [NeZero n] → WeightedResponses.MarkedSample ℓ (k + d) n →
      TorusFields.TorusSite (WeightedResponses.fineSide ℓ.side d n) → Prop
  | 0, n, _, u, o => ∀ p ∈ TorusFields.plaquettesIn
        (ResponseInTheExpansion.supBall o (descendingRadius ℓ.side top s)),
      TorusFields.curvature (WeightedResponses.topField ℓ k n u) p.1 p.2.1 p.2.2 ≤ δ
  | d + 1, n, _, u, o =>
    (∀ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall
        (ResponseInTheExpansion.siteAbove ℓ.side (d + 1) n o) (descendingRadius ℓ.side top (s - (d + 1)))),
      TorusFields.curvature u.2.2.1 p.1 p.2.1 p.2.2 ≤ δ) ∧
    (∀ c ∈ BoxGaussian.bondsWithin (ResponseInTheExpansion.supBall
        (ResponseInTheExpansion.siteAbove ℓ.side (d + 1) n o) (descendingRadius ℓ.side top (s - (d + 1)))),
      StepCosts.bondFit ℓ (WeightedResponses.topField ℓ (k + d) (n * ℓ.side) u.1) u.2.2.1 u.2.1 c ≤ f) ∧
    IsGoodSample ℓ k s top δ f d (n * ℓ.side) u.1 o
open Classical in
def blockWeight (L s : ℕ) {m : ℕ} [NeZero m] [NeZero (WeightedResponses.fineSide L s m)]
    (P : TorusFields.TorusPlaquette m) (p : TorusFields.TorusPlaquette (WeightedResponses.fineSide L s m)) : ℝ :=
  (1 / (L : ℝ) ^ (4 * s)) * ∑ y ∈ Finset.univ.filter
      (fun y : TorusFields.TorusSite (WeightedResponses.fineSide L s m) =>
        ResponseInTheExpansion.siteAbove L s m y = P.1),
    ∑ i ∈ Finset.range (L ^ s), ∑ j ∈ Finset.range (L ^ s),
      if p = (y + i • TorusFields.unitStep _ P.2.1 + j • TorusFields.unitStep _ P.2.2, P.2.1, P.2.2)
      then 1 else 0
def mirrorSum (f : TorusLumps.LocalDensity) (o : TorusFields.TorusSite n) (R : ℕ) (g : ℝ → ℝ)
    (W : TorusFields.TorusField n) : ℝ :=
  if h : 4 * (2 * R) = 0 then 0 else
    haveI : NeZero (4 * (2 * R)) := ⟨h⟩
    ∑ z ∈ ResponseInTheExpansion.supBall (0 : TorusFields.TorusSite (4 * (2 * R))) (3 * R / 2),
      g (TorusLumps.centered f (4 * (2 * R)) z (TorusMirror.mirrorField (2 * R) o W))
end YangMills.Construction.BoxEvents
end

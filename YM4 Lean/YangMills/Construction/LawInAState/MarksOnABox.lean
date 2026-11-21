import YangMills.Construction.LawInAState.AveragesInACell
import YangMills.Construction.LawInAState.ResponsesInOneBox
import YangMills.Construction.LawOnABoxOfTheFlow.ChartOfABox
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.BoxMarks
open Classical
def curlPairing {n : ℕ} (v : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions)
    (p p' : TorusFields.TorusPlaquette n) : ℝ :=
  ∑ e : Fin 3, BlockAverages.imaginaryComponent e (ResponseInTheExpansion.lieFormCurl v p) *
    BlockAverages.imaginaryComponent e (ResponseInTheExpansion.lieFormCurl v p')
def weightSitesOf (L K k : ℕ) [NeZero L] (f : InfiniteLattice.AmbientSpace → ℝ) :
    Finset (TorusFields.TorusSite (BoxResponses.boxSide L K k)) :=
  ResponseInTheExpansion.weightSupportSites L k (BoxResponses.boxSide L K k) (BoxResponses.unitTorusWeight L K k f)
structure IsWeightKernel (L k : ℕ) [NeZero L] {N : ℕ} [NeZero N] (α C c err : ℝ)
    (h : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide L k N))
    (κ : TorusFields.TorusSite N → TorusFields.TorusPlaquette N → TorusFields.TorusPlaquette N → ℝ) : Prop where
  symm : ∀ y p p', κ y p p' = κ y p' p
  decay : ∀ y p p', |κ y p p'| ≤
    C * Real.exp (-(c * max (TorusFields.supDist p.1 y : ℝ) (TorusFields.supDist p'.1 y : ℝ)))
  vanish_far : ∀ y, (∀ z ∈ ResponseInTheExpansion.weightSupportSites L k N h, 2 < TorusFields.supDist y z) →
    ∀ p p', κ y p p' = 0
  plane_sums : ∀ (y : TorusFields.TorusSite N) (μ ν ρ τ : Fin 4), μ < ν → ρ < τ →
    |∑ p ∈ (TorusFields.plaquettesIn Finset.univ).filter (fun p : TorusFields.TorusPlaquette N => p.2 = (μ, ν)),
        ∑ p' ∈ (TorusFields.plaquettesIn Finset.univ).filter
          (fun p' : TorusFields.TorusPlaquette N => p'.2 = (ρ, τ)), κ y p p' -
      (if (μ, ν) = (ρ, τ) then α * WeightedResponses.blockMean L k N y h else 0)| ≤ err
def totalKernel {N : ℕ} [NeZero N]
    (κ : TorusFields.TorusSite N → TorusFields.TorusPlaquette N → TorusFields.TorusPlaquette N → ℝ)
    (p p' : TorusFields.TorusPlaquette N) : ℝ := ∑ y, κ y p p'
variable {ℓ : TorusLumps.StepParameters}
def outerDataAt (T : WeightedResponses.StageTower ℓ) (K k : ℕ)
    (o : TorusFields.TorusSite (BoxResponses.boxSide ℓ.side K k)) (R : ℕ)
    (u : WeightedResponses.MarkedSample ℓ k (BoxResponses.boxSide ℓ.side K k)) :
    BoxGaussian.OuterData T k o R :=
  BoxGaussian.outerData T k o R (WeightedResponses.stageState T k (BoxResponses.boxSide ℓ.side K k) u)
def chartConnection {T : WeightedResponses.StageTower ℓ} {K k : ℕ}
    {o : TorusFields.TorusSite (BoxResponses.boxSide ℓ.side K k)} {R : ℕ} (c : BoxGaussian.BoxChart T k o R)
    (u : WeightedResponses.MarkedSample ℓ k (BoxResponses.boxSide ℓ.side K k)) :
    TorusFields.TorusBond (BoxResponses.boxSide ℓ.side K k) → BlockAverages.imaginaryQuaternions :=
  c.background (outerDataAt T K k o R u) +
    c.coord (outerDataAt T K k o R u)
      (BoxGaussian.restrictInner o R (WeightedResponses.stageState T k (BoxResponses.boxSide ℓ.side K k) u).1)
structure IsBoxKernelFamily (T : WeightedResponses.StageTower ℓ) (β : ℝ) (α : ℕ → ℝ) (K k m : ℕ)
    {o : TorusFields.TorusSite (BoxResponses.boxSide ℓ.side K k)} {R : ℕ}
    (c : BoxGaussian.BoxChart T k o R) (C cc errK err : ℝ)
    (w : (Fin 4 → ℤ) → InfiniteLattice.AmbientSpace → ℝ)
    (κ : (Fin 4 → ℤ) → TorusFields.TorusSite (BoxResponses.boxSide ℓ.side K k) →
      TorusFields.TorusPlaquette (BoxResponses.boxSide ℓ.side K k) →
      TorusFields.TorusPlaquette (BoxResponses.boxSide ℓ.side K k) → ℝ)
    (κ₀ : (Fin 4 → ℤ) → ℝ) : Prop where
  isWeightKernel : ∀ v ∈ StateLaws.shiftSet m,
    IsWeightKernel ℓ.side k (α k) C cc errK (BoxResponses.unitTorusWeight ℓ.side K k (w v)) (κ v)
  response_approx : ∀ᵐ u ∂BoxResponses.stageLaw T β K k, u ∈ c.event → ∀ v ∈ StateLaws.shiftSet m,
    |BoxResponses.boxResponse T β α K k (w v) u - κ₀ v -
        (1 / 2) * ∑ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)),
          ∑ p' ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)),
            totalKernel (κ v) p p' * curlPairing (chartConnection c u) p p'| ≤ err
def boxTrace (a : ℝ) (L k : ℕ) {N : ℕ} [NeZero N] (o : TorusFields.TorusSite N) (R : ℕ)
    (A A' : TorusFields.TorusPlaquette N → TorusFields.TorusPlaquette N → ℝ) : ℝ :=
  ∑ p₁ ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)),
    ∑ p₂ ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)),
      ∑ p₃ ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)),
        ∑ p₄ ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)),
          A p₁ p₂ * BoxGaussian.curlCovariance a L k o R p₂ p₃ * A' p₃ p₄ *
            BoxGaussian.curlCovariance a L k o R p₄ p₁
def boxCoefficient (a : ℝ) (L k m : ℕ) {N : ℕ} [NeZero N] (o : TorusFields.TorusSite N) (R : ℕ) (x : ℝ)
    (κ κ' : (Fin 4 → ℤ) → TorusFields.TorusSite N → TorusFields.TorusPlaquette N →
      TorusFields.TorusPlaquette N → ℝ) : ℝ :=
  CellAverages.shiftAverage m fun v =>
    (3 / 2) * (x ^ 2)⁻¹ * boxTrace a L k o R (totalKernel (κ v)) (totalKernel (κ' v))
structure IsGoodChart (T : WeightedResponses.StageTower ℓ) (β : ℝ) (K k : ℕ)
    {o : TorusFields.TorusSite (BoxResponses.boxSide ℓ.side K k)} {R : ℕ}
    (c : BoxGaussian.BoxChart T k o R) (x C₁ c₀ ε φ₀ : ℝ) (Cj : ℕ → ℝ) (xp : ℕ → ℝ) : Prop where
  measurable : c.IsMeasurable
  prob_event_ge : ∀ p : ℕ, xp p ≤ x → 1 - x ^ (-(p : ℝ)) ≤ (BoxResponses.stageLaw T β K k).real c.event
  support_disjoint : ∀ u ∈ c.event,
    Disjoint (WeightedResponses.stageState T k (BoxResponses.boxSide ℓ.side K k) u).2.1
      (ResponseInTheExpansion.supBall o (3 * R))
  gauge : c.IsInGauge C₁ (BoxGaussian.boxScale x) c₀
  law : c.HasLaw (BoxResponses.stageLaw T β K k) x c₀ ε
  curl : c.HasCurl x C₁ (BoxGaussian.boxScale x) φ₀ Cj
  quadForm_bounds : ∀ w : TorusFields.TorusPlaquette (BoxResponses.boxSide ℓ.side K k) → Fin 3 → ℝ,
    0 ≤ BoxGaussian.curlQuadForm ℓ.coupling ℓ.side k o R w ∧
    BoxGaussian.curlQuadForm ℓ.coupling ℓ.side k o R w ≤
      C₁ * ∑ e : Fin 3, ∑ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)), w p e ^ 2
def IsLocalizedNear (L K k m R : ℕ) [NeZero L] (o : TorusFields.TorusSite (BoxResponses.boxSide L K k))
    (f : InfiniteLattice.AmbientSpace → ℝ) : Prop :=
  ∀ v ∈ StateLaws.shiftSet m,
    weightSitesOf L K k (StateLaws.translateBy L K k v f) ⊆ ResponseInTheExpansion.supBall o ((R : ℝ) / 8)
end YangMills.Construction.BoxMarks
end

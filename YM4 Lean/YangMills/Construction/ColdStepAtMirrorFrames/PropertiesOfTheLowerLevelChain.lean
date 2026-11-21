import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def bondListDiameter {j k : ℕ} (c : Fin k → F.Site j × Fin 4) : ℕ :=
  Finset.univ.sup fun l : Fin k => Finset.univ.sup fun l' : Fin k => siteSupDist (c l).1 (c l').1
def bondListDist {j k : ℕ} (y : F.Site j) (c : Fin k → F.Site j × Fin 4) : ℕ :=
  Finset.univ.sup fun l : Fin k => siteSupDist y (c l).1
structure ColdEstimatesBelow (a δ s : ℝ) (N : ℕ → ℝ) (W : F.GaugeField F.depth) : Prop where
  minimalAction_analytic : ∀ (k : ℕ) (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions),
    AnalyticAt ℝ (fun τ : Fin k → ℝ => minimalAction a (finiteCells F) F.depth (leftTranslate (bondSpread c X τ) W)) 0
  siteShare_analytic : ∀ (y : F.Site F.depth) (k : ℕ) (c : Fin k → F.Site F.depth × Fin 4)
    (X : Fin k → imaginaryQuaternions),
    AnalyticAt ℝ (fun τ : Fin k → ℝ => minimalSiteShare a y (leftTranslate (bondSpread c X τ) W)) 0
  chainShare_eq : ∀ (X : F.FieldChain), IsMinimizingChainBelow a (finiteCells F) W X → ∀ y : F.Site F.depth,
    chainSiteShare a (finiteCells F) y X = minimalSiteShare a y W
  minimalAction_deriv_decay : ∀ (k : ℕ) (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions),
    1 ≤ k → AreUnitVectors X →
    |bondDeriv (minimalAction a (finiteCells F) F.depth) W c X| ≤ N k * Real.exp (-δ * bondListDiameter c)
  minimalAction_firstDeriv_le : ∀ (c : Fin 1 → F.Site F.depth × Fin 4) (X : Fin 1 → imaginaryQuaternions),
    AreUnitVectors X →
    |bondDeriv (minimalAction a (finiteCells F) F.depth) W c X| ≤ N 1 * s
  siteShare_deriv_decay : ∀ (y : F.Site F.depth) (k : ℕ) (c : Fin k → F.Site F.depth × Fin 4)
    (X : Fin k → imaginaryQuaternions), 1 ≤ k →
    AreUnitVectors X → |bondDeriv (minimalSiteShare a y) W c X| ≤ N k * Real.exp (-δ * bondListDist y c)
  siteShare_bounds : ∀ y : F.Site F.depth, 0 ≤ minimalSiteShare a y W ∧ minimalSiteShare a y W ≤ N 0 * s ^ 2
  siteShare_firstDeriv_le : ∀ (y : F.Site F.depth) (c : Fin 1 → F.Site F.depth × Fin 4)
    (X : Fin 1 → imaginaryQuaternions), AreUnitVectors X →
    |bondDeriv (minimalSiteShare a y) W c X| ≤ N 1 * s * Real.exp (-δ * bondListDist y c)
  siteShare_gauge_invariant : ∀ (y : F.Site F.depth) (γ : F.Site F.depth → UnitQuaternion),
    minimalSiteShare a y (gaugeTransform γ W) = minimalSiteShare a y W
  siteShare_translate : ∀ y h : F.Site F.depth,
    minimalSiteShare a (y + h) (translateField h W) = minimalSiteShare a y W
structure ColdComparisonBelow (a δ δ₂ s s₀ : ℝ) (N : ℕ → ℝ) {F' : BlockFrame} (W : F.GaugeField F.depth)
    (W' : F'.GaugeField F'.depth) (y : F.Site F.depth) (y' : F'.Site F'.depth) (r : ℕ) : Prop where
  siteShare_deriv_close : ∀ (k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
    (∀ l, BondWithinRadius r (h l)) → AreUnitVectors X →
    |bondDeriv (minimalSiteShare a y) W (bondsAt y h) X - bondDeriv (minimalSiteShare a y') W' (bondsAt y' h) X| ≤
      derivativeScale s k * N k * Real.exp (-δ * r)
  minimalAction_firstDeriv_close : s ≤ s₀ → ∀ (b : (Fin 4 → ℤ) × Fin 4) (X : Fin 1 → imaginaryQuaternions),
    BondWithinRadius r b → AreUnitVectors X →
    |bondDeriv (minimalAction a (finiteCells F) F.depth) W (bondsAt y fun _ => b) X -
      bondDeriv (minimalAction a (finiteCells F') F'.depth) W' (bondsAt y' fun _ => b) X| ≤
      N 0 * s * Real.exp (-(δ₂ * ((r : ℝ) - siteSupDist y (y + siteOfCoords F.depth b.1))))
end YangMills.Construction.ColdStepAtMirrorFrames
end

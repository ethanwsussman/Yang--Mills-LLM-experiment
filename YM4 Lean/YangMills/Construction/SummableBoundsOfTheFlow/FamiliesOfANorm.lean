import YangMills.Construction.ClusterExpansionOfAStep.FormsOfAFamily
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.FamilyNorms
open BlockAverages ColdStepAtMirrorFrames
def thirdOrderSize (P : TorusLumps.StepParameters) (ε : ℝ) : ℝ := ε * P.E₃ / P.E
structure IsNormBoundedFamily (P : TorusLumps.StepParameters) (ε ε₃ : ℝ) (h : TorusLumps.LocalDensity) : Prop where
  admissible : TorusLumps.IsAdmissibleDensity P h
  decay : TorusLumps.DerivDecay P h fun k m => (if k = 3 then ε₃ else ε) / P.weight m
  comparison : TorusLumps.LocalComparison P (TorusLumps.centeredFamily h) fun m => ε / P.weight m
def HasVanishingCurvatureForm (h : TorusLumps.LocalDensity) : Prop := TorusLumps.HasCurvatureForm h 0
structure IsNormBoundedLocalFamily (L t n₀ : ℕ) (σ δ ε ε₃ : ℝ) (f : LocalFamily) : Prop where
  smooth : ∀ F, IsCubicTorusAbove L t n₀ F → ∀ (y : F.Site F.depth) (W : F.GaugeField F.depth),
    IsSmallCurvature σ W → ContDiffThreeAlongBonds (f F y) W
  gauge_invariant : ∀ F, IsCubicTorusAbove L t n₀ F → ∀ (y : F.Site F.depth) (W : F.GaugeField F.depth)
    (g : F.Site F.depth → UnitQuaternion), IsSmallCurvature σ W → f F y (gaugeTransform g W) = f F y W
  translation_invariant : ∀ F, IsCubicTorusAbove L t n₀ F → ∀ (y v : F.Site F.depth) (W : F.GaugeField F.depth),
    IsSmallCurvature σ W → f F (y + v) (translateField v W) = f F y W
  decay : ∀ F, IsCubicTorusAbove L t n₀ F → ∀ (y : F.Site F.depth) (W : F.GaugeField F.depth) (k : ℕ)
    (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions), IsSmallCurvature σ W → 1 ≤ k → k ≤ 3 →
    AreUnitVectors X →
    |bondDeriv (f F y) W c X| ≤ (if k = 3 then ε₃ else ε) / torusDecayFactor L δ (bondSpan y c)
  locality : ∀ F F', IsCubicTorusAbove L t n₀ F → IsCubicTorusAbove L t n₀ F' →
    ∀ (y : F.Site F.depth) (y' : F'.Site F'.depth) (W : F.GaugeField F.depth) (W' : F'.GaugeField F'.depth) (r k : ℕ)
      (e : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
    IsSmallCurvature σ W → IsSmallCurvature σ W' → AgreeOnBox W W' y y' r → k ≤ 2 →
    (∀ l, BlockAverages.BondWithinRadius r (e l)) → AreUnitVectors X →
    |bondDeriv (ColdStepAtMirrorFrames.subtractTrivial f F y) W (bondsAt y e) X -
        bondDeriv (ColdStepAtMirrorFrames.subtractTrivial f F' y') W' (bondsAt y' e) X| ≤
      ε / torusDecayFactor L δ r
end YangMills.Construction.FamilyNorms
end

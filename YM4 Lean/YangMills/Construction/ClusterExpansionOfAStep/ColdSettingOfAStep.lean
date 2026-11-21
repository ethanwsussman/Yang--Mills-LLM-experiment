import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.StepSettings
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.TorusFields
open YangMills.Construction.TorusLumps
variable {n : ℕ}
def coldChartSetting (R : StepSetup) [NeZero n] (V : TorusField n) : ChartSetting R n where
  coarse := V
  region := Finset.univ
  fine := trivialField _
  support := ∅
  labelling := fun z => absurd z.2 (Finset.notMem_empty _)
  bases := fun y => cellCentre 0 y
  free := YangMills.Construction.StepCosts.chartBonds R.params.side n
  bad := ∅
def coldImageIntegral (R : StepSetup) [NeZero n] (V : TorusField n) : ℝ :=
  R.functional (n * R.params.side) (trivialField _) *
    ∫ η, (coldChartSetting R V).cutoffProduct η * Real.exp (-(coldChartSetting R V).potential η)
end YangMills.Construction.StepSettings
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
structure IsSmallDensity (ℓ : StepParameters) (e : ℝ) (g : LocalDensity) : Prop where
  smooth : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (V : TorusField n), IsCold ℓ.threshold V →
    ContDiffThreeAt (g n y) V
  gauge : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (γ : TorusSite n → UnitQuaternion) (V : TorusField n),
    IsCold ℓ.threshold V → g n y (gaugeTransform γ V) = g n y V
  translation : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y u : TorusSite n) (V : TorusField n),
    IsCold ℓ.threshold V → g n y (TorusFields.translate u V) = g n (y + u) V
  decay : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (V : TorusField n), IsCold ℓ.threshold V →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
      |mixedDeriv (g n y) V c X| ≤ e / ℓ.weight (supportDiam y c)
  local_density : ∀ n n' [NeZero n] [NeZero n'], ℓ.n₀ ≤ n → ℓ.n₀ ≤ n' →
    ∀ (y : TorusSite n) (y' : TorusSite n') (V : TorusField n) (V' : TorusField n') (m : ℕ),
      2 * m + 2 < n → 2 * m + 2 < n' →
      IsCold ℓ.threshold V → IsCold ℓ.threshold V' → FieldsAgreeNear V V' y y' m →
      ∀ (k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
        (∀ l, BondOffsetInBox m (h l)) → AreUnitVectors X →
        |mixedDeriv (g n y) V (fun l => bondFrom y (h l)) X -
            mixedDeriv (g n' y') V' (fun l => bondFrom y' (h l)) X| ≤ e / ℓ.weight m
end YangMills.Construction.TorusLumps
end

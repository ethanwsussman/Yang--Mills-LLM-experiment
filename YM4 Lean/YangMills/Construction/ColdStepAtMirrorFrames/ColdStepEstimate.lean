import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
abbrev TopLevelFamily : Type := (F : BlockFrame) → F.Cell → F.GaugeField F.top → ℝ
def IsCubicTopTorus (L t n₀ : ℕ) (F : BlockFrame) : Prop :=
  F.blockSide = L ∧ F.depth = t ∧ ∃ n : ℕ, (∀ i, F.extent i = n) ∧ n₀ ≤ n
def frameRadius (x : ℝ) : ℕ := ⌈x ^ (1 / 100 : ℝ)⌉₊ / 2 ^ 11
def centredFamily (g : TopLevelFamily) : TopLevelFamily :=
  fun F Y V => g F Y V - g F Y (uniformField F F.top)
def secondDerivAtUniform (g : TopLevelFamily) (L t n : ℕ) (b b' : (Fin 4 → ℤ) × Fin 4)
    (X X' : imaginaryQuaternions) : ℝ :=
  bondDeriv (g (cubicTorusFrame L t n) 0) (uniformField _ _) (bondsAt 0 ![b, b']) ![X, X']
def constantPlaneCurvature (X : imaginaryQuaternions) (μ ν : Fin 4) :
    Fin 4 → Fin 4 → imaginaryQuaternions :=
  fun α β => if α = μ ∧ β = ν then X else if α = ν ∧ β = μ then -X else 0
structure IsLocalDensity (L t n₀ : ℕ) (s : ℝ) (g : TopLevelFamily) : Prop where
  smooth : ∀ F, IsCubicTopTorus L t n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
    IsSmallCurvature s V → ContDiffThreeAlongBonds (g F Y) V
  gauge_invariant : ∀ F, IsCubicTopTorus L t n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top)
    (γ : F.Cell → UnitQuaternion),
    IsSmallCurvature s V → g F Y (gaugeTransform γ V) = g F Y V
  translation_invariant : ∀ F, IsCubicTopTorus L t n₀ F → ∀ (Y h : F.Cell) (V : F.GaugeField F.top),
    IsSmallCurvature s V → g F (Y + h) (translateField h V) = g F Y V
def IsLocalOnTori (L t n₀ : ℕ) (s : ℝ) (g : TopLevelFamily) (e : ℕ → ℝ) : Prop :=
  ∀ F F', IsCubicTopTorus L t n₀ F → IsCubicTopTorus L t n₀ F' →
    ∀ (Y : F.Cell) (Y' : F'.Cell) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (r k : ℕ)
      (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
    IsSmallCurvature s V → IsSmallCurvature s V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r → k ≤ 2 → (∀ l, BondWithinRadius r (h l)) →
    AreUnitVectors X →
    |bondDeriv (g F Y) V (bondsAt Y h) X - bondDeriv (g F' Y') V' (bondsAt Y' h) X| ≤ e r
def DerivDecay (L t n₀ : ℕ) (s : ℝ) (g : TopLevelFamily) (e : ℕ → ℕ → ℝ) : Prop :=
  ∀ F, IsCubicTopTorus L t n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), IsSmallCurvature s V →
    1 ≤ k → k ≤ 3 → AreUnitVectors X → |bondDeriv (g F Y) V c X| ≤ e k (bondSpan Y c)
end YangMills.Construction.ColdStepAtMirrorFrames
end

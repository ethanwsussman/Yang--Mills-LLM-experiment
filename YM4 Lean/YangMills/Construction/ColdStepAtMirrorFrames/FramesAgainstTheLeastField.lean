import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def frameDecayBound (Cf δ₂ : ℝ) (m : ℕ) : ℝ := Cf * Real.exp (-(δ₂ / 4 * m))
def frameDeviation (a ρ : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) : ℍ[ℝ] :=
  (bondFrameCoord a ρ m b V : ℍ[ℝ]) - torusCoordinate a ρ b V
def frameCoordField (star : Bool) (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun z i => stepFrame star a ρ m (z, i) V
def frameFirstDeriv (star : Bool) (a ρ : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions)
    (V : F.GaugeField F.top) : ℝ :=
  chartedSlope a (frameCoordField star a ρ m V) V b e
def frameActionAlongBond (star : Bool) (a ρ : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions)
    (V : F.GaugeField F.top) (u : ℝ) : ℝ :=
  chartedEnergy a (Function.update (frameCoordField star a ρ m V) b.1
    (Function.update (frameCoordField star a ρ m V b.1) b.2 (stepFrame star a ρ m b V + u • e))) V
def IsCoarseBondInBox (y : F.Cell) (r : ℕ) (c : F.Site F.top × Fin 4) : Prop :=
  ∃ u : (Fin 4 → ℤ) × Fin 4, BondWithinRadius r u ∧ c = (y + siteOfCoords F.top u.1, u.2)
def FrameNearMinimizer (a ρ δ₂ Cf σ : ℝ) (m : ℕ) (V : F.GaugeField F.top) : Prop :=
  ∀ b ∈ chordBonds (finiteCells F), ‖frameDeviation a ρ m b V‖ ≤ frameDecayBound Cf δ₂ m * σ ∧
    ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
      AreUnitVectors X →
      ‖bondDeriv (frameDeviation a ρ m b) V c X‖ ≤
        Cf * Real.exp (-(δ₂ / 4 * ((m : ℝ) + max m (bondListDistance (enclosingCell b.1) c))))
structure FrameSmallness (star : Bool) (a ρ δ₂ κ₂ C σ : ℝ) (Kk : ℕ → ℝ) (m : ℕ) (V : F.GaugeField F.top) :
    Prop where
  minimizer_exists : (∀ i, 4 * m + 5 < F.extent i) → ∀ y : F.Cell,
    IsMinimizingChart a (finiteCells (reflectedFrame F m)) (reflectedField m y V) ρ
      (minimizingCoordinates a (finiteCells (reflectedFrame F m)) (reflectedField m y V) ρ)
  norm_le : ∀ b ∈ chordBonds (finiteCells F), ‖stepFrame star a ρ m b V‖ ≤ C * σ
  norm_add_le : ∀ b ∈ chordBonds (finiteCells F), ‖stepFrame star a ρ m b V‖ + σ / 64 ≤ ρ
  holonomy_ratio : ∀ (c : F.Site F.top × Fin 4) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube F.blockSide →
    ‖contourHolonomyDefect (chartedField (frameCoordField star a ρ m V) V) V c h π - 1‖ ≤ C * σ
  small_curvature : IsSmallCurvature ((if star then 5 / 8 else 41 / 64) * σ)
    (chartedField (frameCoordField star a ρ m V) V)
  deriv_decay : ∀ b ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
    ‖bondDeriv (stepFrame star a ρ m b) V c X‖ ≤
      C * Real.exp (-(δ₂ / 4 * bondListDistance (enclosingCell b.1) c))
  deriv_bound : ∀ b ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X →
    ‖bondDeriv (stepFrame star a ρ m b) V c X‖ ≤
      16 ^ k * Kk k * Real.exp (-(κ₂ * bondListDistance (enclosingCell b.1) c))
  deriv_eq_zero_off_box : star = false → (∀ i, 4 * m + 5 < F.extent i) → ∀ b ∈ chordBonds (finiteCells F),
    ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      (∃ l, ¬ IsCoarseBondInBox (enclosingCell b.1) m (c l)) →
      bondDeriv (stepFrame star a ρ m b) V c X = 0
  analytic : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame star a ρ m b) V
  gauge_covariant : ∀ b ∈ chordBonds (finiteCells F), ∀ γ : F.Cell → UnitQuaternion,
    (stepFrame star a ρ m b (gaugeTransform γ V) : ℍ[ℝ]) =
      (γ (enclosingCell b.1) : ℍ[ℝ]) * (stepFrame star a ρ m b V : ℍ[ℝ]) *
        ((γ (enclosingCell b.1))⁻¹ : UnitQuaternion)
  translation_invariant : ∀ b ∈ chordBonds (finiteCells F), ∀ h : F.Cell,
    stepFrame star a ρ m (b.1 + cellCentre F.depth h, b.2) (translateField h V) = stepFrame star a ρ m b V
structure FrameLocality (star : Bool) (a ρ δ₂ C σ : ℝ) (m : ℕ) {F' : BlockFrame} (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) : Prop where
  value : ∀ (h o : Fin 4 → ℤ) (i : Fin 4), IsFineBondWithinRadius Y r h o i →
    ‖(stepFrame star a ρ m (fineBondAt Y h o i) V : ℍ[ℝ]) -
      stepFrame star a ρ m (fineBondAt Y' h o i) V'‖ ≤
      C * σ * Real.exp (-(δ₂ / 4 * ((r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1))))
  deriv : ∀ (h o : Fin 4 → ℤ) (i : Fin 4) (k : ℕ) (e : Fin k → (Fin 4 → ℤ) × Fin 4)
    (X : Fin k → imaginaryQuaternions), IsFineBondWithinRadius Y r h o i → 1 ≤ k → k ≤ 3 →
    (∀ l, BondWithinRadius r (e l)) → AreUnitVectors X →
    ‖bondDeriv (stepFrame star a ρ m (fineBondAt Y h o i)) V (bondsAt Y e) X -
      bondDeriv (stepFrame star a ρ m (fineBondAt Y' h o i)) V' (bondsAt Y' e) X‖ ≤
      C * Real.exp (-(δ₂ / 4 * ((r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1))))
  eq_of_far : star = false → (∀ i, 4 * m + 5 < F.extent i) → (∀ i, 4 * m + 5 < F'.extent i) →
    ∀ (h o : Fin 4 → ℤ) (i : Fin 4), IsFineBondWithinRadius Y r h o i →
      (m : ℝ) < (r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) →
      stepFrame star a ρ m (fineBondAt Y h o i) V = stepFrame star a ρ m (fineBondAt Y' h o i) V' ∧
      ∀ (k : ℕ) (e : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
        (∀ l, BondWithinRadius r (e l)) →
        bondDeriv (stepFrame star a ρ m (fineBondAt Y h o i)) V (bondsAt Y e) X =
          bondDeriv (stepFrame star a ρ m (fineBondAt Y' h o i)) V' (bondsAt Y' e) X
structure FrameNearlyCritical (star : Bool) (a ρ δ₂ C ω x : ℝ) (m : ℕ) (V : F.GaugeField F.top) : Prop where
  differentiableAt_action : ∀ b ∈ chordBonds (finiteCells F), ∀ e : imaginaryQuaternions,
    DifferentiableAt ℝ (frameActionAlongBond star a ρ m b e V) 0
  contDiff : ∀ b ∈ chordBonds (finiteCells F), ∀ e : imaginaryQuaternions,
    ContDiffThreeAlongBonds (frameFirstDeriv star a ρ m b e) V
  firstDeriv_bound : ∀ b ∈ chordBonds (finiteCells F), ∀ e : imaginaryQuaternions, ‖e‖ = 1 →
    x * |frameFirstDeriv star a ρ m b e V| ≤ 1
  firstDeriv_decay : ∀ b ∈ chordBonds (finiteCells F), ∀ e : imaginaryQuaternions, ‖e‖ = 1 →
    ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
      AreUnitVectors X →
      |bondDeriv (frameFirstDeriv star a ρ m b e) V c X| ≤
        C * ω * Real.exp (-(δ₂ / 8 * bondListDistance (enclosingCell b.1) c))
def FrameFirstDerivLocal (star : Bool) (a ρ κ C x : ℝ) (m : ℕ) {F' : BlockFrame} (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) : Prop :=
  ∀ (h o : Fin 4 → ℤ) (i : Fin 4) (e : imaginaryQuaternions), IsFineBondWithinRadius Y (r / 4) h o i → ‖e‖ = 1 →
    x * |frameFirstDeriv star a ρ m (fineBondAt Y h o i) e V -
      frameFirstDeriv star a ρ m (fineBondAt Y' h o i) e V'| ≤ C * Real.exp (-(2 ^ 8 * κ * r))
def FrameBoundsAt (a : ℝ) (L : ℕ) (c : ColdChainParameters) (Cf C σ κ x : ℝ) (m t n₀ : ℕ) (F : BlockFrame)
    (V : F.GaugeField F.top) : Prop :=
  ((∀ i, 4 * m + 5 < F.extent i) → FrameNearMinimizer a c.ρA c.δ₂ Cf σ m V) ∧
  (∀ star, FrameSmallness star a c.ρA c.δ₂ c.κ₂ C σ c.Kk m V) ∧
  (∀ star, FrameNearlyCritical star a c.ρA c.δ₂ C (frameDecayBound Cf c.δ₂ m) x m V) ∧
  ∀ (F' : BlockFrame) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ),
    IsCubicTopTorus L t n₀ F' → IsSmallCurvature (5 / 4 * σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
    (∀ star, FrameLocality star a c.ρA c.δ₂ C σ m V V' Y Y' r) ∧
    ∀ star, FrameFirstDerivLocal star a c.ρA κ C x m V V' Y Y' r
def FrameBounds (a : ℝ) (L : ℕ) (c : ColdChainParameters) (Cf C σ₀ : ℝ) : Prop :=
  0 < Cf ∧ 1 ≤ C ∧ 0 < σ₀ ∧
    ∀ (κ σ x : ℝ) (m t n₀ : ℕ), 0 < κ → κ ≤ c.δ₂ / 2 ^ 14 → 0 < σ → σ ≤ σ₀ → 1 ≤ x → 16 ≤ m → 64 ≤ n₀ →
      frameDecayBound Cf c.δ₂ m ≤ 2⁻¹ ^ 10 * σ →
      C * x ^ 2 * frameDecayBound Cf c.δ₂ m ≤ Real.exp (-(2 ^ 10 * κ * m)) →
      C * x ^ 2 * Real.exp (-(2 * c.δ₂ * m)) ≤ 1 →
      ∀ (F : BlockFrame) (V : F.GaugeField F.top), IsCubicTopTorus L t n₀ F → IsSmallCurvature (5 / 4 * σ) V →
        FrameBoundsAt a L c Cf C σ κ x m t n₀ F V
def frameBoundsStatement : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ Cf C σ₀ : ℝ, FrameBounds a L c Cf C σ₀
end ColdStepAtMirrorFrames
end YangMills.Construction
end

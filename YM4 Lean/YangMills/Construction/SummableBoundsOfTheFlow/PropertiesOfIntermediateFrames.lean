import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheTermsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.LawsOfTheFramesBetween
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames FamilyNorms
namespace Interpolation
variable {F : BlockFrame}
def frameGapBound (T : StepParameters) (m : ℕ) : ℝ := T.Ct * Real.exp (-(T.chainParams.δ₂ / 4 * m))
structure InterpolatedFrameNearMinimizer (s a ρA δ₂ ω σ : ℝ) (m : ℕ) (V : F.GaugeField F.top) : Prop where
  norm_eq_and_le : ∀ b ∈ chordBonds (finiteCells F),
    ‖interpolatedFrame s a ρA m b V - stepFrame true a ρA m b V‖ = s * ‖frameGap a ρA m b V‖ ∧
      ‖frameGap a ρA m b V‖ ≤ ω * σ
  deriv_decay : ∀ b ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
    ‖bondDeriv (frameGap a ρA m b) V c X‖ ≤ ω * Real.exp (-(δ₂ / 4 * bondListDistance (enclosingCell b.1) c))
  eq_on_small_torus : (¬ ∀ i, 4 * m + 5 < F.extent i) → ∀ b, interpolatedFrame s a ρA m b V = stepFrame true a ρA m b V
structure InterpolatedFrameSmall (s a ρA δ₂ C σ : ℝ) (m : ℕ) (V : F.GaugeField F.top) : Prop where
  norm_le : ∀ b ∈ chordBonds (finiteCells F), ‖interpolatedFrame s a ρA m b V‖ ≤ C * σ
  norm_add_le : ∀ b ∈ chordBonds (finiteCells F), ‖interpolatedFrame s a ρA m b V‖ + σ / 64 ≤ ρA
  contour_near_one : ∀ (c : F.Site F.top × Fin 4) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube F.blockSide →
    ‖contourHolonomyDefect (chartedField (fun z i => interpolatedFrame s a ρA m (z, i) V) V) V c h π - 1‖ ≤ C * σ
  deriv_decay : ∀ b ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
    ‖bondDeriv (interpolatedFrame s a ρA m b) V c X‖ ≤ C * Real.exp (-(δ₂ / 4 * bondListDistance (enclosingCell b.1) c))
  analytic : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (interpolatedFrame s a ρA m b) V
  translation_invariant : ∀ b ∈ chordBonds (finiteCells F), ∀ h : F.Cell,
    interpolatedFrame s a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) = interpolatedFrame s a ρA m b V
  gauge_covariant : ∀ b ∈ chordBonds (finiteCells F), ∀ γ : F.Cell → UnitQuaternion,
    (interpolatedFrame s a ρA m b (gaugeTransform γ V) : ℍ[ℝ]) =
      (γ (enclosingCell b.1) : ℍ[ℝ]) * (interpolatedFrame s a ρA m b V : ℍ[ℝ]) * ((γ (enclosingCell b.1))⁻¹ : UnitQuaternion)
  small_curvature : IsSmallCurvature (41 / 64 * σ) (interpolatedField s a ρA m V 0)
  small_curvature_nearby : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ σ / 64) →
    IsSmallCurvature (3 / 4 * σ) (interpolatedField s a ρA m V η)
structure InterpolatedFrameLocal (s a ρA δ₂ K C σ : ℝ) (m : ℕ) {F' : BlockFrame} (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) : Prop where
  norm_sub_le : ∀ (h o : Fin 4 → ℤ) (i : Fin 4), IsFineBondWithinRadius Y r h o i →
    ‖interpolatedFrame s a ρA m (fineBondAt Y h o i) V - interpolatedFrame s a ρA m (fineBondAt Y' h o i) V'‖ ≤
      C * σ * Real.exp (-(δ₂ / 4 * ((r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1))))
  deriv_sub_le : ∀ (h o : Fin 4 → ℤ) (i : Fin 4) (k : ℕ) (e : Fin k → (Fin 4 → ℤ) × Fin 4)
    (X : Fin k → imaginaryQuaternions), IsFineBondWithinRadius Y r h o i → 1 ≤ k → k ≤ 3 → (∀ l, BondWithinRadius r (e l)) →
    AreUnitVectors X →
    ‖bondDeriv (interpolatedFrame s a ρA m (fineBondAt Y h o i)) V (bondsAt Y e) X -
      bondDeriv (interpolatedFrame s a ρA m (fineBondAt Y' h o i)) V' (bondsAt Y' e) X‖ ≤
      C * Real.exp (-(δ₂ / 4 * ((r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1))))
  eq_far_inside : (∀ i, 4 * m + 5 < F.extent i) → (∀ i, 4 * m + 5 < F'.extent i) →
    ∀ (h o : Fin 4 → ℤ) (i : Fin 4), IsFineBondWithinRadius Y r h o i →
      (m : ℝ) < (r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) →
      interpolatedFrame s a ρA m (fineBondAt Y h o i) V - interpolatedFrame s a ρA m (fineBondAt Y' h o i) V' =
        (1 - s) • (stepFrame true a ρA m (fineBondAt Y h o i) V -
          stepFrame true a ρA m (fineBondAt Y' h o i) V') ∧
      frameGap a ρA m (fineBondAt Y h o i) V - frameGap a ρA m (fineBondAt Y' h o i) V' =
        -(stepFrame true a ρA m (fineBondAt Y h o i) V - stepFrame true a ρA m (fineBondAt Y' h o i) V') ∧
      ‖stepFrame true a ρA m (fineBondAt Y h o i) V - stepFrame true a ρA m (fineBondAt Y' h o i) V'‖ ≤
        2 * K * σ * Real.exp (-(δ₂ * ((r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1))))
structure InterpolatedSlopeSmall (s a ρA δ₂ C ω x : ℝ) (m : ℕ) (V : F.GaugeField F.top) : Prop where
  smooth : ∀ b ∈ chordBonds (finiteCells F), ∀ e : imaginaryQuaternions,
    ContDiffThreeAlongBonds (interpolatedSlope s a ρA m b e) V
  norm_le : ∀ b ∈ chordBonds (finiteCells F), ∀ e : imaginaryQuaternions, ‖e‖ = 1 → x * |interpolatedSlope s a ρA m b e V| ≤ 1
  deriv_decay : ∀ b ∈ chordBonds (finiteCells F), ∀ e : imaginaryQuaternions, ‖e‖ = 1 →
    ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 → AreUnitVectors X →
      |bondDeriv (interpolatedSlope s a ρA m b e) V c X| ≤
        C * ω * Real.exp (-(δ₂ / 8 * bondListDistance (enclosingCell b.1) c))
def InterpolatedSlopeLocal (s a ρA κ C x : ℝ) (m : ℕ) {F' : BlockFrame} (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) : Prop :=
  ∀ (h o : Fin 4 → ℤ) (i : Fin 4) (e : imaginaryQuaternions), IsFineBondWithinRadius Y (r / 4) h o i → ‖e‖ = 1 →
    x * |interpolatedSlope s a ρA m (fineBondAt Y h o i) e V -
      interpolatedSlope s a ρA m (fineBondAt Y' h o i) e V'| ≤ C * Real.exp (-(2 ^ 8 * κ * r))
structure InterpolatedExponentBounds (s a ρA ρ x κ C : ℝ) (m : ℕ) (V : F.GaugeField F.top) : Prop where
  deriv_top : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ < ρ) → k ≤ 3 → AreUnitVectors X →
    |bondDeriv (fun V' => interpolatedBlockExponent s a ρA x m Y V' η) V c X| ≤
      C * (x * localSqNorm κ Y η + 1) * Real.exp (-(2 ^ 6 * κ * bondSpan Y c))
  deriv_top_partial : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F)))
    (e : BondVector) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ < ρ) → k ≤ 3 →
    AreUnitVectors X → ‖e‖ = 1 →
    |bondDeriv (fun V' => bondPartialDeriv (interpolatedBlockExponent s a ρA x m Y V') b η e) V c X| ≤
      C * (x * Real.sqrt (localSqNorm κ Y η) + 1) *
        Real.exp (-(2 ^ 6 * κ * bondSpanWithCell Y (enclosingCell b.1.1) c))
  second_deriv : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (b b' : ↥(chordBonds (finiteCells F)))
    (e e' : BondVector), (∀ b, ‖η b‖ < ρ) → ‖e‖ = 1 → ‖e'‖ = 1 →
    |secondDerivAlong (interpolatedBlockExponent s a ρA x m Y V) η (bondVariation b e) (bondVariation b' e')| ≤
      C * x * Real.exp (-(2 ^ 6 * κ * max (cellSupDist Y (enclosingCell b.1.1))
        (max (cellSupDist Y (enclosingCell b'.1.1)) (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1)))))
def imaginaryCoords (w : imaginaryQuaternions) : BondVector := !₂[(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK]
def IsRightTranslationDeriv (w X u : imaginaryQuaternions) : Prop :=
  HasDerivAt (fun τ : ℝ => NormedSpace.exp ((w : ℍ[ℝ]) + τ • (u : ℍ[ℝ])))
    (NormedSpace.exp (w : ℍ[ℝ]) * (X : ℍ[ℝ])) 0
open Classical in
def topVariationField (Th : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions) (s a ρA : ℝ) (m : ℕ)
    (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions)
    (b : F.Site F.depth × Fin 4) (u : imaginaryQuaternions) (V : F.GaugeField F.top) : imaginaryQuaternions :=
  bondDeriv (interpolatedFrame s a ρA m b) V (fun _ : Fin 1 => c) (fun _ => X) +
    if IsCrossingBond b ∧ (enclosingCell b.1, b.2) = c then Th (interpolatedFrame s a ρA m b V + u) X else 0
structure TopVariationRepresentation (s a ρA ρ κ C : ℝ) (m : ℕ) (V : F.GaugeField F.top) : Prop where
  exists_representation : ∃ Th : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions,
    (∀ w X : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X (Th w X)) ∧
    (∀ (G : F.GaugeField F.depth → ℝ) (η : StepVariable (finiteCells F)) (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions),
      (∀ b, ‖η b‖ < ρ) → ‖X‖ = 1 → ContDiffThreeAlongBonds G (interpolatedField s a ρA m V η) →
      bondDeriv (fun V' => G (interpolatedField s a ρA m V' η)) V (fun _ : Fin 1 => c) (fun _ => X) =
        ∑ b : ↥(chordBonds (finiteCells F)), bondPartialDeriv (fun ζ => G (interpolatedField s a ρA m V ζ)) b η
          (imaginaryCoords (topVariationField Th s a ρA m c X b.1 (toImaginary (η b)) V))) ∧
    ∀ (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions) (b : ↥(chordBonds (finiteCells F))) (u : imaginaryQuaternions) (k : ℕ)
      (c' : Fin k → F.Site F.top × Fin 4) (X' : Fin k → imaginaryQuaternions), ‖X‖ = 1 → ‖u‖ < ρ → k ≤ 2 → AreUnitVectors X' →
      ‖bondDeriv (topVariationField Th s a ρA m c X b.1 u) V c' X'‖ ≤
        C * Real.exp (-(2 ^ 8 * κ * bondSpan (enclosingCell b.1.1) (Fin.cons c c' : Fin (k + 1) → _)))
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def HasUniformlyConvexLaw (ρ lam x κ C : ℝ) (d : ι → ι → ℝ) (Φ : BondField ι → ℝ) : Prop :=
  ∃ (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ),
    (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → Ψ η = Φ η) ∧
    IsUniformlyConvexDecaying ρ (x * lam / 4) κ d Ψ K ∧
    (∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖) ∧
    ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ (b : ι) (e : BondVector),
      |bondPartialDeriv Ψ b η e| ≤ C * x * ‖e‖
structure LawMomentBounds (ρ x κ C : ℝ) (p : ℝ → ℝ) (Cq : ℕ → ℝ) (Cr : ℕ → ℕ → ℕ → ℝ)
    (d : ι → ι → ℝ) (Φ : BondField ι → ℝ) : Prop where
  covariance : ∀ f g : BondField ι → ℝ, ContDiff ℝ 1 f → ContDiff ℝ 1 g →
    |ballCovariance (cutoffFactor ρ p) Φ f g| ≤ C / x * ∑ b, ∑ b',
      ballL2Norm (cutoffFactor ρ p) Φ (bondGradNorm f b) * Real.exp (-(κ * d b b')) *
        ballL2Norm (cutoffFactor ρ p) Φ (bondGradNorm g b')
  moments : ∀ (q : ℕ) (b : ι), ballExpectation (cutoffFactor ρ p) Φ (fun η => ‖η b‖ ^ (2 * q)) ≤
    Cq q * (x ^ q)⁻¹
  cutoff_deriv_moments : ∀ (j q N : ℕ) (b : ι), 1 ≤ j → 1 ≤ q →
    MeasureTheory.Integrable (fun η => |iteratedDeriv j p ‖η b‖| ^ q *
      ballDensity (cutoffFactor ρ p) Φ η) ∧
    ballExpectation (cutoffFactor ρ p) Φ (fun η => |iteratedDeriv j p ‖η b‖| ^ q) ≤ Cr j q N * (x ^ N)⁻¹
structure ObservableSizes (a ρA ρ lam x κ C δ η₃ : ℝ) (L t n₀ m : ℕ) (σ : ℝ) (p : ℝ → ℝ)
    (Cq : ℕ → ℝ) (Φ : BondField ι → ℝ) (M : LawOnBondVariables ι) : Prop where
  exponent_deriv : ∀ (s : ℝ) (Y : M.frame.Cell) (k : ℕ) (c : Fin k → M.frame.Site M.frame.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    0 ≤ s → s ≤ 1 → k ≤ 3 → AreUnitVectors X →
    HasLocalSize ρ (cutoffFactor ρ p) Φ Cq x κ (C * Real.exp (-(2 ^ 5 * κ * bondSpan Y c)))
      (embeddedCellDist M.embed Y) (fun ζ => bondDeriv (fun V' => interpolatedBlockExponent s a ρA x m Y V'
        (extendByZero M.embed M.active ζ)) M.topField c X)
  exponent_sub_quadratic : ∀ (s : ℝ) (Y : M.frame.Cell), 0 ≤ s → s ≤ 1 →
    HasLocalSize ρ (cutoffFactor ρ p) Φ Cq x κ C (embeddedCellDist M.embed Y) (fun ζ =>
      interpolatedBlockExponent s a ρA x m Y M.topField (extendByZero M.embed M.active ζ) -
        cellQuadratic lam x Y (extendByZero M.embed M.active ζ))
  expansion_deriv : ∀ (s ε : ℝ) (h : LocalFamily) (y : M.frame.Site M.frame.depth) (k : ℕ)
    (c : Fin k → M.frame.Site M.frame.top × Fin 4) (X : Fin k → imaginaryQuaternions), 0 ≤ s → s ≤ 1 → 0 < ε →
    IsNormBoundedLocalFamily L t n₀ σ δ ε (ε / η₃) h → k ≤ 2 → AreUnitVectors X →
    HasLocalSize ρ (cutoffFactor ρ p) Φ Cq x κ
      (C * (if k = 2 then ε / η₃ else ε) * x ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(2 ^ 4 * κ * bondSpan (enclosingCell y) c)))
      (embeddedCellDist M.embed (enclosingCell y)) (fun ζ => bondDeriv (interpolatedExpansion s a ρA m h y
        (extendByZero M.embed M.active ζ)) M.topField c X)
end Interpolation
end YangMills.Construction
end

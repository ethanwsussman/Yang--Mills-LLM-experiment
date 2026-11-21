import YangMills.Construction.LawByMomentsOfTheFlow.TestFunctionsOnTheSpace
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def levelSpacing (L K t : ℕ) : ℝ := (L : ℝ) ^ ((t : ℤ) - (K : ℤ))
def cellLength (L K κ : ℕ) : ℝ := (L : ℝ) ^ κ * levelSpacing L K 0
structure IsAdmissibleFlow (ℓ : TorusLumps.StepParameters) (Ξ β : ℝ) (K : ℕ) : Prop where
  two_le : 2 ≤ K
  coupling_ge : ∀ j ≤ K, ℓ.y₁ ≤ (TorusLumps.couplingFlow ℓ β j).1
  coupling_le : (TorusLumps.couplingFlow ℓ β K).1 ≤ Ξ
def rangeAtLevel (ℓ : TorusLumps.StepParameters) (β : ℝ) (t : ℕ) : ℝ :=
  (TorusLumps.clusterRange (TorusLumps.couplingFlow ℓ β t).1 : ℝ)
def FitsAtLevel (ℓ : TorusLumps.StepParameters) (β : ℝ) (K : ℕ) (ρ : ℝ) (t : ℕ) : Prop :=
  2 ^ 11 * rangeAtLevel ℓ β t * levelSpacing ℓ.side K t ≤ ρ
open Classical in
def radiusLevel (ℓ : TorusLumps.StepParameters) (β : ℝ) (K : ℕ) (ρ : ℝ) : Option ℕ :=
  if ∃ t ≤ K, FitsAtLevel ℓ β K ρ t then some (Nat.findGreatest (FitsAtLevel ℓ β K ρ) K) else none
def sourceNorm (ρ H Λ : ℝ) : ℝ := max H (min 1 ρ * Λ)
structure IsLocalizedSource (l ρ H : ℝ) (Λ : NNReal) (h : TestFunctions.EuclideanFourSpace → ℝ) : Prop where
  lipschitz : LipschitzWith Λ h
  abs_le : ∀ x, |h x| ≤ H
  exists_ball : ∃ p : TestFunctions.EuclideanFourSpace, ∀ x, h x ≠ 0 → dist x p ≤ ρ
  away_from_faces : ∀ x, h x ≠ 0 → ∀ μ, |x μ| + ρ ≤ l / 2
variable {m : ℕ}
def reflectedPoint (a₀ : ℝ) (M : ℕ) (k : Fin 4 → ℕ) (p : TorusFields.TorusPlaquette m) :
    TestFunctions.EuclideanFourSpace :=
  WithLp.toLp 2 fun μ => a₀ / 2 *
    ((((-1 : ZMod (2 * m)) ^ k μ * (WeightedResponses.doubledBarycentre p μ
      - 2 * (M : ZMod (2 * m)) * (k μ : ZMod (2 * m)))).valMinAbs : ℤ) : ℝ)
def reflectedWeight (a₀ : ℝ) (M : ℕ) (k : Fin 4 → ℕ) (h : TestFunctions.EuclideanFourSpace → ℝ) :
    WeightedResponses.PlaquetteWeight m :=
  fun p => h (reflectedPoint a₀ M k p)
def reflectedWeightAbout (a₀ : ℝ) (M : ℕ) (z : TorusFields.TorusSite m) (k : Fin 4 → ℕ)
    (h : TestFunctions.EuclideanFourSpace → ℝ) : WeightedResponses.PlaquetteWeight m :=
  WeightedResponses.translateWeight (-z) (reflectedWeight a₀ M k h)
def reflectedProductMean (β a₀ : ℝ) (M c : ℕ) [NeZero M] [NeZero c] (z : TorusFields.TorusSite (c * M))
    (h : TestFunctions.EuclideanFourSpace → ℝ) (κ : ℝ) : ℝ :=
  ∫ W, ∏ k : Fin 4 → Fin c,
    (WeightedResponses.curvatureObservable (reflectedWeightAbout a₀ M z (fun μ => (k μ : ℕ)) h) W - κ)
    ∂(WeightedResponses.wilsonLaw β (c * M))
def twoCellSide (L κ t : ℕ) : ℕ := 2 * L ^ (κ - t)
instance (L κ t : ℕ) [NeZero L] : NeZero (twoCellSide L κ t) :=
  ⟨mul_ne_zero two_ne_zero (pow_ne_zero _ (NeZero.ne L))⟩
def meanAtTrivial (ℓ : TorusLumps.StepParameters) (β : ℝ) (al : ℕ → ℝ) (s n : ℕ) [NeZero n]
    (w : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide ℓ.side s n)) : ℝ :=
  ∑ y : TorusFields.TorusSite n,
    ResponseInTheExpansion.coldResponseChain ℓ β (ResponseInTheExpansion.flowCouplings ℓ β) al s n y (TorusFields.trivialField n) w
def reflectedCentring (ℓ : TorusLumps.StepParameters) (β : ℝ) (al : ℕ → ℝ) (K κ : ℕ) (ρ : ℝ) (k : Fin 4 → ℕ)
    (h : TestFunctions.EuclideanFourSpace → ℝ) : ℝ :=
  match radiusLevel ℓ β K ρ with
  | none => 0
  | some s => meanAtTrivial ℓ β al s (twoCellSide ℓ.side κ s)
      (reflectedWeight (levelSpacing ℓ.side K 0) (ℓ.side ^ κ) k h)
def centring (ℓ : TorusLumps.StepParameters) (β : ℝ) (al : ℕ → ℝ) (K κ : ℕ) (ρ : ℝ)
    (h : TestFunctions.EuclideanFourSpace → ℝ) : ℝ :=
  reflectedCentring ℓ β al K κ ρ 0 h
def ReflectedMeanBounded (ℓ : TorusLumps.StepParameters) (β : ℝ) (K κ c : ℕ) [NeZero c]
    (z : TorusFields.TorusSite (c * ℓ.side ^ κ)) (h : TestFunctions.EuclideanFourSpace → ℝ) (centre Q : ℝ) : Prop :=
  0 ≤ reflectedProductMean β (levelSpacing ℓ.side K 0) (ℓ.side ^ κ) c z h centre ∧
    reflectedProductMean β (levelSpacing ℓ.side K 0) (ℓ.side ^ κ) c z h centre ≤ Q ^ (c ^ 4)
def ForAllSources (ℓ : TorusLumps.StepParameters) (Kr : WeightedResponses.ResponseParameters) (Ξ : ℝ)
    (P : (β : ℝ) → (K κ : ℕ) → (al : ℕ → ℝ) → (ρ H : ℝ) → (Λ : NNReal) →
      (TestFunctions.EuclideanFourSpace → ℝ) → Prop) : Prop :=
  ∀ (β : ℝ) (K : ℕ), IsAdmissibleFlow ℓ Ξ β K → ∃ al : ℕ → ℝ, ResponseInTheExpansion.IsChainResponseCoeff ℓ Kr β K al ∧
    ∀ κ : ℕ, 2 ≤ κ → ∀ (ρ H : ℝ) (Λ : NNReal) (h : TestFunctions.EuclideanFourSpace → ℝ),
      0 < ρ → ρ ≤ cellLength ℓ.side K κ / 4 → IsLocalizedSource (cellLength ℓ.side K κ) ρ H Λ h → P β K κ al ρ H Λ h
def ForAllCeilings (P : TorusLumps.StepParameters → WeightedResponses.ResponseParameters → ℝ → Prop) : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => ∃ Kr : WeightedResponses.ResponseParameters,
    Kr.Admissible (Tb.stepParameters y) ∧
    ∀ Ξ : ℝ, y + 2 * Tb.B ≤ Ξ → P (Tb.stepParameters y) Kr Ξ
end YangMills.Construction.SmallTorusCopies
end

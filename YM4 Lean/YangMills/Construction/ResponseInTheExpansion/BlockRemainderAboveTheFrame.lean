import YangMills.Construction.ResponseInTheExpansion.ColdPartAtTheParameters
import YangMills.Construction.ResponseInTheExpansion.FamiliesOnOneTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace WeightedResponses
variable {F : BlockFrame}
def remainderHat (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (y : F.Site F.depth) (W : F.GaugeField F.depth) : ℝ :=
  r y W - r y (fun _ _ => 1)
structure IsTorusRemainder (L : ℕ) (σ δ e e₃ : ℝ) (r : F.Site F.depth → F.GaugeField F.depth → ℝ) : Prop where
  decaying : IsDecayingSiteFamily L σ δ e e₃ r
  agreement : ∀ (y : F.Site F.depth) (W W' : F.GaugeField F.depth) (m k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4)
    (X : Fin k → imaginaryQuaternions), IsSmallCurvature σ W → IsSmallCurvature σ W' → AgreeOnBox W W' y y m → k ≤ 2 →
    (∀ l, BondWithinRadius m (h l)) → AreUnitVectors X →
    |bondDeriv (remainderHat r y) W (bondsAt y h) X - bondDeriv (remainderHat r y) W' (bondsAt y h) X| ≤
      e / torusDecayFactor L δ m
open Classical in
def blockRemainderHat (Q : ColdHalfLaw) (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (Y : F.Cell) : AboveFrames F :=
  fun η V =>
    Q.blockSum r Y η V - ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
      r y (fun _ _ => 1)
structure BlockRemainderBounds (T : StepParameters) (Q : ColdHalfLaw) (e : ℝ)
    (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (V : F.GaugeField F.top) : Prop where
  low_order : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), InClosedBallProduct T.ballRadius η → 1 ≤ k → k ≤ 2 → AreUnitVectors X →
    |bondDeriv (Q.blockSum r Y η) V c X| ≤
      2⁻¹ ^ 7 * ((T.L : ℝ) * e) / torusDecayFactor T.L T.decayRate (bondSpan Y c)
  third_order : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (c : Fin 3 → F.Site F.top × Fin 4)
    (X : Fin 3 → imaginaryQuaternions), InClosedBallProduct T.ballRadius η → AreUnitVectors X →
    |bondDeriv (Q.blockSum r Y η) V c X| ≤
      2⁻¹ ^ 7 * ((T.L : ℝ) * e / T.η₃) / torusDecayFactor T.L T.decayRate (bondSpan Y c)
  value_bound : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)), InClosedBallProduct T.ballRadius η →
    |blockRemainderHat Q r Y η V| ≤ 2⁻¹ ^ 8 * ((T.L : ℝ) * e) / torusDecayFactor T.L T.decayRate T.blockIndex
def blockRemainderStatementAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x e : ℝ) (f : LocalFamily) (F : BlockFrame) (V V' : F.GaugeField F.top)
    (r : F.Site F.depth → F.GaugeField F.depth → ℝ),
    T.coupling ≤ x → IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
    IsSmallCurvature (5 / 4 * T.σ) V' →
    0 ≤ e → IsTorusRemainder T.L T.σ T.decayRate e (e / T.η₃) r →
    BlockRemainderBounds T (coldHalfLawAt T x f) e r V ∧
    ∀ (Y : F.Cell) (q k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
      AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q → k ≤ 2 → (∀ l, BondWithinRadius q (h l)) →
      AreUnitVectors X →
      |bondDeriv ((coldHalfLawAt T x f).blockSum r Y 0) V (bondsAt Y h) X -
          bondDeriv ((coldHalfLawAt T x f).blockSum r Y 0) V' (bondsAt Y h) X| ≤
        2⁻¹ ^ 6 * ((T.L : ℝ) * e) / torusDecayFactor T.L T.decayRate q
def blockRemainderStatement : Prop := EventuallyInParameters blockRemainderStatementAt
end WeightedResponses
end YangMills.Construction
end

import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def IsBlockTorus (L : ℕ) (F : BlockFrame) : Prop := F.blockSide = L ∧ IsLargeCubicTorus F
def torusCoordinate (a ρ : ℝ) (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) : imaginaryQuaternions :=
  minimizingBondCoordinate a ρ (finiteCells F) b V
def torusMinimizingField (a ρ : ℝ) (V : F.GaugeField F.top) : F.GaugeField F.depth :=
  chartedField (minimizingCoordinates a (finiteCells F) V ρ) V
def contourHolonomyDefect (W : F.GaugeField F.depth) (V : F.GaugeField F.top) (c : F.Site F.top × Fin 4)
    (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) : ℍ[ℝ] :=
  ((pathHolonomy W (refineSite c.1) (bondContour F.blockSide h π c.2) * (V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])
def IsFineBondWithinRadius (Y : F.Cell) (r : ℕ) (h o : Fin 4 → ℤ) (i : Fin 4) : Prop :=
  o ∈ centredCube F.blockSide ∧ fineBondAt Y h o i ∈ chordBonds (finiteCells F) ∧ WithinRadius r h ∧
    cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) ≤ r ∧
    cellSupDist Y (enclosingCell ((fineBondAt Y h o i).1 + unitStep F.depth i)) ≤ r
def HasSmallCoordinatesAndContours (a ρ C s : ℝ) (V : F.GaugeField F.top) : Prop :=
  (∀ b ∈ chordBonds (finiteCells F), ‖torusCoordinate a ρ b V‖ ≤ C * s) ∧
  ∀ (c : F.Site F.top × Fin 4) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube F.blockSide →
    ‖contourHolonomyDefect (torusMinimizingField a ρ V) V c h π - 1‖ ≤ C * s ∧
      1 - C * s ≤ ‖contourAverage (torusMinimizingField a ρ V) c‖
def HasCoordinateDerivativeDecay (a ρ κ₂ : ℝ) (Kk : ℕ → ℝ) (V : F.GaugeField F.top) : Prop :=
  ∀ b ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X →
    ‖bondDeriv (torusCoordinate a ρ b) V c X‖ ≤
      Kk k * Real.exp (-(κ₂ * bondListDistance (enclosingCell b.1) c))
structure ComparesMinimizers (a ρ δ₂ K s s₀ : ℝ) (Kk : ℕ → ℝ) {F' : BlockFrame} (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) : Prop where
  coordinates : ∀ (h o : Fin 4 → ℤ) (i : Fin 4), IsFineBondWithinRadius Y r h o i →
    ‖(torusCoordinate a ρ (fineBondAt Y h o i) V : ℍ[ℝ]) -
      torusCoordinate a ρ (fineBondAt Y' h o i) V'‖ ≤
      K * s * Real.exp (-(δ₂ * ((r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1))))
  firstDerivative : ∀ (b : (Fin 4 → ℤ) × Fin 4) (X : Fin 1 → imaginaryQuaternions),
    BondWithinRadius r b → AreUnitVectors X →
    |bondDeriv (minimalAction a (finiteCells F) F.top) V (bondsAt Y fun _ => b) X -
      bondDeriv (minimalAction a (finiteCells F') F'.top) V' (bondsAt Y' fun _ => b) X| ≤
      K * s * Real.exp (-(δ₂ * ((r : ℝ) - cellSupDist Y (Y + siteOfCoords F.top b.1))))
  coordinateDerivatives : ∀ (h o : Fin 4 → ℤ) (i : Fin 4) (k : ℕ)
    (e : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
    IsFineBondWithinRadius Y r h o i → 1 ≤ k → k ≤ 3 →
    (∀ l, BondWithinRadius r (e l)) → AreUnitVectors X →
    ‖bondDeriv (torusCoordinate a ρ (fineBondAt Y h o i)) V (bondsAt Y e) X -
      bondDeriv (torusCoordinate a ρ (fineBondAt Y' h o i)) V' (bondsAt Y' e) X‖ ≤
      Kk 3 * Real.exp (-(δ₂ / 2 * ((r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1))))
  cellShares : s ≤ s₀ / 2 → ∀ (k : ℕ) (e : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
    k ≤ 3 → (∀ l, BondWithinRadius r (e l)) → AreUnitVectors X →
    |bondDeriv (minimalCellShare a (finiteCells F) Y) V (bondsAt Y e) X -
      bondDeriv (minimalCellShare a (finiteCells F') Y') V' (bondsAt Y' e) X| ≤
      Kk 3 * Real.exp (-(δ₂ / 16 * r))
  action : ∀ (k : ℕ) (e : Fin (k + 1) → (Fin 4 → ℤ) × Fin 4) (X : Fin (k + 1) → imaginaryQuaternions),
    (∀ l, BondWithinRadius r (e l)) → AreUnitVectors X →
    |bondDeriv (minimalAction a (finiteCells F) F.top) V (bondsAt Y e) X -
      bondDeriv (minimalAction a (finiteCells F') F'.top) V' (bondsAt Y' e) X| ≤
      Kk (k + 1) * Real.exp (-(δ₂ / 2 * ((r : ℝ) - cellSupDist Y (Y + siteOfCoords F.top (e 0).1))))
def ClassicalEstimatesHold (a : ℝ) (L : ℕ) (ρ s₀ δ₂ κ₂ K C : ℝ) (Kk : ℕ → ℝ) : Prop :=
  (0 < ρ ∧ ρ ≤ 1 ∧ 0 < s₀ ∧ 0 < δ₂ ∧ 2 ^ 6 * δ₂ ≤ κ₂ ∧ 0 < K ∧ 1 ≤ C ∧ ∀ k, 0 < Kk k) ∧
    ∀ (F : BlockFrame) (s : ℝ) (V : F.GaugeField F.top), IsBlockTorus L F → 0 < s → s ≤ s₀ →
      IsSmallCurvature s V →
      IsMinimizingChart a (finiteCells F) V ρ (minimizingCoordinates a (finiteCells F) V ρ) ∧
      HasSmallCoordinatesAndContours a ρ C s V ∧ HasCoordinateDerivativeDecay a ρ κ₂ Kk V ∧
      ∀ (F' : BlockFrame) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ),
        IsBlockTorus L F' → F'.depth = F.depth → IsSmallCurvature s V' →
        AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
        ComparesMinimizers a ρ δ₂ K s s₀ Kk V V' Y Y' r
structure ColdChainParameters where
  δ₁ : ℝ
  δ' : ℝ
  lam : ℝ
  ρA : ℝ
  σA : ℝ
  cg : ℝ
  s₀ : ℝ
  δ₂ : ℝ
  κ₂ : ℝ
  K : ℝ
  C : ℝ
  N : ℕ → ℝ
  N' : ℕ → ℝ
  Kk : ℕ → ℝ
structure ColdChainParameters.EstimatesAt (c : ColdChainParameters) (a s : ℝ) (V : F.GaugeField F.top) :
    Prop where
  minimizer : HasColdMinimizer a c.ρA (c.N 0) s (finiteCells F) V
  hessian : HasCoerciveHessian a c.lam c.ρA c.σA (finiteCells F) V
  cellShares : HasRegularCellShares a c.δ₁ s c.N (finiteCells F) V
  coordinates : HasRegularCoordinates a c.δ₁ c.ρA c.N (finiteCells F) V
  decay : HasTorusDerivativeDecay a c.δ' c.ρA s c.N' (finiteCells F) V
  hotPlaquettes : ∀ W : F.GaugeField F.depth,
    minimalAction a (finiteCells F) F.top V + c.cg * s ^ 2 * hotPlaquetteCount (finiteCells F) F.depth s W ≤
      blockEnergy a (finiteCells F) F.depth W V
  locality : ∀ (F' : BlockFrame) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ),
    F'.blockSide = F.blockSide → F'.depth = F.depth → IsLargeCubicTorus F' → IsSmallCurvature s V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
    HasComparableCellShares a c.δ₁ s c.N (finiteCells F) V (finiteCells F') V' Y Y' r ∧
    HasComparableCoordinates a c.δ₁ c.ρA s c.N (finiteCells F) V (finiteCells F') V' Y Y' r ∧
    HasTorusComparison a c.δ' c.ρA s c.N' (finiteCells F) V (finiteCells F') V' Y Y' r
structure ColdChainParameters.Admissible (c : ColdChainParameters) (a : ℝ) (L : ℕ) : Prop where
  positivity : 0 < c.δ₁ ∧ 0 < c.δ' ∧ 0 < c.lam ∧ 0 < c.σA ∧ 0 < c.cg ∧ (∀ k, 0 < c.N k) ∧ ∀ k, 0 < c.N' k
  inequalities : c.δ₁ ≤ 1 / 8 ∧ 2 ^ 6 * c.δ₂ ≤ c.δ₁ ∧ 16 * c.s₀ ≤ c.σA ∧ 2 * c.C * c.s₀ ≤ c.ρA ∧
    2 * c.C * c.s₀ ≤ 1 / 16 ∧ 64 * (L : ℝ) * c.C * c.s₀ ≤ 1
  estimates : ∀ (F : BlockFrame) (s : ℝ) (V : F.GaugeField F.top), IsBlockTorus L F → 0 < s → s ≤ c.σA →
    IsSmallCurvature s V → c.EstimatesAt a s V
  classical : ClassicalEstimatesHold a L c.ρA c.s₀ c.δ₂ c.κ₂ c.K c.C c.Kk
end ColdStepAtMirrorFrames
end YangMills.Construction
end

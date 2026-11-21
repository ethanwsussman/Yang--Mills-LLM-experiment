import YangMills.Construction.ColdChainAtEveryLevel.ChartsChainsAndShares
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def WithinRadius (r : ℕ) (h : Fin 4 → ℤ) : Prop := ∀ i, |h i| ≤ (r : ℤ)
def BondWithinRadius (r : ℕ) (b : (Fin 4 → ℤ) × Fin 4) : Prop :=
  WithinRadius r b.1 ∧ WithinRadius r (b.1 + Pi.single b.2 1)
def offsetBonds (Y : F.Cell) {k : ℕ} (h : Fin k → (Fin 4 → ℤ) × Fin 4) :
    Fin k → F.Site F.top × Fin 4 :=
  fun l => (Y + siteOfCoords F.top (h l).1, (h l).2)
def AgreeOnBall {F' : BlockFrame} (S : Finset F.Cell) (V : F.GaugeField F.top) (S' : Finset F'.Cell)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) : Prop :=
  (∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i) ∧ (∀ i, F'.extent i = 0 ∨ 2 * r + 2 < F'.extent i) ∧
    (∀ h, WithinRadius r h → (Y + siteOfCoords F.top h ∈ S ↔ Y' + siteOfCoords F'.top h ∈ S')) ∧
    ∀ b, BondWithinRadius r b →
      V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2
def HasColdMinimizer (a ρ N₀ s : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) : Prop :=
  ∃ w, IsMinimizingChart a S V (min ρ (N₀ * s)) w ∧
    IsCold S F.depth (s / 8) (chartedField w V) ∧
    ∀ W', (∀ W'', blockEnergy a S F.depth W' V ≤ blockEnergy a S F.depth W'' V) →
      ∃ γ : F.Site F.depth → UnitQuaternion, (∀ z, γ (cellCentre F.depth z) = 1) ∧
        AgreeOnBonds S F.depth W' (gaugeTransform γ (chartedField w V))
def HasCoerciveHessian (a κ ρ σ : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) : Prop :=
  ∀ w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions, (∀ b, b ∉ chordBonds S → w b.1 b.2 = 0) →
    (∀ b, b ∉ chordBonds S → dw b.1 b.2 = 0) → (∀ b ∈ chordBonds S, ‖w b.1 b.2‖ ≤ ρ) →
    IsCold S F.depth σ (chartedField w V) →
    κ * ∑ b ∈ chordBonds S, ‖dw b.1 b.2‖ ^ 2 ≤
      deriv (deriv fun τ : ℝ => blockEnergy a S F.depth
        (chartedField (fun x i => w x i + τ • dw x i) V) V) 0
structure CubicSymmetry where
  perm : Equiv.Perm (Fin 4)
  sign : Fin 4 → ℤ
  shift : Fin 4 → ℤ
def CubicSymmetry.actSite (g : CubicSymmetry) (j : ℕ) (x : F.Site j) : F.Site j :=
  siteOfCoords j fun i => g.sign i * siteCoords x (g.perm i) + (F.blockSide : ℤ) ^ (F.top - j) * g.shift i
def CubicSymmetry.actStep (g : CubicSymmetry) (k : Fin 4) : PathStep :=
  (g.perm.symm k, decide (g.sign (g.perm.symm k) = 1))
def CubicSymmetry.TransportsField (g : CubicSymmetry) (V V' : F.GaugeField F.top) : Prop :=
  ∀ x k, linkValue V' (g.actSite F.top x) (g.actStep k) = V x k
def CubicSymmetry.IsSymmetry (g : CubicSymmetry) (G : BlockFrame) : Prop :=
  (∀ i, g.sign i = 1 ∨ g.sign i = -1) ∧ ∀ i j, G.extent i = G.extent j
def HasRegularCellShares (a δ s : ℝ) (N : ℕ → ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) : Prop :=
  IsBondAnalyticAt (minimalAction a S F.top) V ∧ (∀ Y, IsBondAnalyticAt (minimalCellShare a S Y) V) ∧
    (∀ X, IsMinimalChain a S V X → ∀ Y, cellShare a S Y X = minimalCellShare a S Y V) ∧
    (∀ Y (γ : F.Cell → UnitQuaternion), minimalCellShare a S Y (gaugeTransform γ V) = minimalCellShare a S Y V) ∧
    (∀ (g : CubicSymmetry) (S' : Finset F.Cell) (V' : F.GaugeField F.top), g.IsSymmetry F →
      (∀ z, z ∈ S ↔ g.actSite F.top z ∈ S') → g.TransportsField V V' →
      ∀ Y, minimalCellShare a S' (g.actSite F.top Y) V' = minimalCellShare a S Y V) ∧
    (∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 2 ≤ k → AreUnitVectors X →
      |mixedBondDerivative (minimalAction a S F.top) V c X| ≤ N k * Real.exp (-δ * bondListDiameter c)) ∧
    (∀ (Y : F.Cell) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
      AreUnitVectors X →
      |mixedBondDerivative (minimalCellShare a S Y) V c X| ≤ N k * Real.exp (-δ * bondListDistance Y c)) ∧
    (∀ Y, 0 ≤ minimalCellShare a S Y V ∧ minimalCellShare a S Y V ≤ N 0 * s ^ 2) ∧
    ∀ (Y : F.Cell) (c : Fin 1 → F.Site F.top × Fin 4) (X : Fin 1 → imaginaryQuaternions), AreUnitVectors X →
      |mixedBondDerivative (minimalCellShare a S Y) V c X| ≤ N 1 * s * Real.exp (-δ * bondListDistance Y c)
def derivativeScale (s : ℝ) (k : ℕ) : ℝ := if k = 0 then s ^ 2 else if k = 1 then s else 1
def HasComparableCellShares (a δ s : ℝ) (N : ℕ → ℝ) {F' : BlockFrame} (S : Finset F.Cell)
    (V : F.GaugeField F.top) (S' : Finset F'.Cell) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell)
    (r : ℕ) : Prop :=
  ∀ (k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
    (∀ l, BondWithinRadius r (h l)) → AreUnitVectors X →
    |mixedBondDerivative (minimalCellShare a S Y) V (offsetBonds Y h) X -
        mixedBondDerivative (minimalCellShare a S' Y') V' (offsetBonds Y' h) X| ≤
      derivativeScale s k * N k * Real.exp (-δ * r)
def minimizingBondCoordinate (a ρ : ℝ) (S : Finset F.Cell) (b : F.Site F.depth × Fin 4)
    (V : F.GaugeField F.top) : imaginaryQuaternions :=
  minimizingCoordinates a S V ρ b.1 b.2
def HasRegularCoordinates (a δ ρ : ℝ) (N : ℕ → ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) : Prop :=
  ∀ b ∈ chordBonds S, IsBondAnalyticAt (minimizingBondCoordinate a ρ S b) V ∧
    ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
      AreUnitVectors X →
      ‖mixedBondDerivative (minimizingBondCoordinate a ρ S b) V c X‖ ≤
        N k * Real.exp (-δ * bondListDistance (enclosingCell b.1) c)
def fineBondAt (Y : F.Cell) (h o : Fin 4 → ℤ) (i : Fin 4) : F.Site F.depth × Fin 4 :=
  (cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o, i)
def HasComparableCoordinates (a δ ρ s : ℝ) (N : ℕ → ℝ) {F' : BlockFrame} (S : Finset F.Cell)
    (V : F.GaugeField F.top) (S' : Finset F'.Cell) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell)
    (r : ℕ) : Prop :=
  ∀ (h o : Fin 4 → ℤ) (i : Fin 4), o ∈ centredCube F.blockSide → fineBondAt Y h o i ∈ chordBonds S →
    WithinRadius r h →
    cellSupDist Y (enclosingCell ((fineBondAt Y h o i).1 + unitStep F.depth i)) ≤ r →
    ‖(minimizingBondCoordinate a ρ S (fineBondAt Y h o i) V : ℍ[ℝ]) -
        minimizingBondCoordinate a ρ S' (fineBondAt Y' h o i) V'‖ ≤
      N 0 * s * Real.exp (-δ * ((r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1))) ∧
    ∀ (k : ℕ) (h' : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
      (∀ l, BondWithinRadius r (h' l)) → AreUnitVectors X →
      ‖((mixedBondDerivative (minimizingBondCoordinate a ρ S (fineBondAt Y h o i)) V (offsetBonds Y h') X :
            imaginaryQuaternions) : ℍ[ℝ]) -
          ((mixedBondDerivative (minimizingBondCoordinate a ρ S' (fineBondAt Y' h o i)) V'
            (offsetBonds Y' h') X : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        N k * Real.exp (-δ * ((r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1)))
def HasHotPlaquettePenalty (a cg σA s : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) : Prop :=
  ∀ σ, s ≤ σ → σ ≤ σA → ∀ W : F.GaugeField F.depth,
    minimalAction a S F.top V + cg * σ ^ 2 * hotPlaquetteCount S F.depth σ W ≤ blockEnergy a S F.depth W V
def flatTopField : F.GaugeField F.top := fun _ _ => 1
def minimalCoords (y : F.Cell) : Fin 4 → ℤ := fun i => (y i).valMinAbs
def constantCurvaturePotential (A : Fin 4 → Fin 4 → imaginaryQuaternions) (y : F.Cell) (μ : Fin 4) :
    imaginaryQuaternions :=
  (1 / 2 : ℝ) • ∑ ν, ((minimalCoords y ν : ℤ) : ℝ) • A ν μ
def curvatureNormSq (A : Fin 4 → Fin 4 → imaginaryQuaternions) : ℝ :=
  ∑ μ, ∑ ν ∈ Finset.univ.filter (μ < ·), ‖A μ ν‖ ^ 2
def HasFlatSecondVariation (a δ : ℝ) (N₀ : ℝ) (S : Finset F.Cell) : Prop :=
  ∀ (r : ℕ) (A : Fin 4 → Fin 4 → imaginaryQuaternions) (φ : F.Site F.top → Fin 4 → ℝ), 1 ≤ r →
    (∀ h, WithinRadius r h → siteOfCoords F.top h ∈ S) → (∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i) →
    (∀ μ ν, A μ ν = - A ν μ) → (∀ y i, 0 ≤ φ y i ∧ φ y i ≤ 1) →
    (∀ y μ, BondWithinRadius (r / 2) (minimalCoords y, μ) → φ y μ = 1) →
    (∀ y μ, ¬ BondWithinRadius r (minimalCoords y, μ) → φ y μ = 0) →
    |iteratedDeriv 2 (fun τ : ℝ => minimalCellShare a S 0
        (rotatedField (fun y μ => (τ * φ y μ) • constantCurvaturePotential A y μ) flatTopField)) 0 -
      curvatureNormSq A| ≤ N₀ * curvatureNormSq A * (r : ℝ) ^ 4 * Real.exp (-δ * r)
end YangMills.Construction.BlockAverages
end

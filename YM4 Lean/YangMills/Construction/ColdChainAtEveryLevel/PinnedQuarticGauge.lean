import YangMills.Construction.ColdChainAtEveryLevel.LeastQuarticGauge
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.PinnedGauge
open YangMills.Construction.BlockAverages YangMills.Construction.LatticeFractionalIntegration
structure PinnedGaugeData where
  scale : ℕ
  cellSide : ℕ
  corner : Lattice4
  region : Finset Lattice4
  field : Lattice4 → Fin 4 → UnitQuaternion
  target : Lattice4 → Fin 4 → UnitQuaternion
  CellIndex : Type
  cells : Finset CellIndex
  cellSites : CellIndex → Finset Lattice4
  base : CellIndex
  Adj : CellIndex → CellIndex → Prop
  bondAverage : CellIndex → CellIndex → (Lattice4 → Fin 4 → ℍ[ℝ]) → ℍ[ℝ]
  pin : (Lattice4 → UnitQuaternion) → CellIndex → UnitQuaternion
namespace PinnedGaugeData
variable (D : PinnedGaugeData)
def defect (γ : Lattice4 → UnitQuaternion) (x : Lattice4) (i : Fin 4) : UnitQuaternion :=
  latticeGaugeTransform γ D.field x i * (D.target x i)⁻¹
def defectForm (γ : Lattice4 → UnitQuaternion) : Lattice4 → Fin 4 → ℍ[ℝ] :=
  fun x i => pureComponent ((D.defect γ x i : UnitQuaternion) : ℍ[ℝ])
def defectQuarticSum (γ : Lattice4 → UnitQuaternion) : ℝ :=
  ∑ b ∈ bondsOf D.region, ‖((D.defect γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4
def pinnedQuarticSum (γ : Lattice4 → UnitQuaternion) : ℝ :=
  D.defectQuarticSum γ + ∑ y ∈ D.cells, ‖((D.pin γ y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4
def cellMean (y : D.CellIndex) (φ : Lattice4 → ℍ[ℝ]) : ℍ[ℝ] :=
  (1 / (D.cellSide : ℝ) ^ 4) • ∑ x ∈ D.cellSites y, φ x
def targetWeight (x : Lattice4) : ℝ := ∑ i : Fin 4,
  if (x - basisVector i, i) ∈ bondsOf D.region then
    ‖((D.target (x - basisVector i) i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 else 0
def extendByOne (γ : D.region → UnitQuaternion) : Lattice4 → UnitQuaternion := by
  classical exact fun x => if h : x ∈ D.region then γ ⟨x, h⟩ else 1
def rotateAlong (ξ : Lattice4 → imaginaryQuaternions) (τ : ℝ) (γ : Lattice4 → UnitQuaternion) :
    Lattice4 → UnitQuaternion :=
  fun x => expUnit (τ • ξ x) * γ x
end PinnedGaugeData
structure IsPinnedGaugeProblem (D : PinnedGaugeData) (θ C₂ C₃ n₀ n₁ r₀ A η b c₁ : ℝ)
    (d : (Lattice4 → UnitQuaternion) → ℝ) : Prop where
  isFilled : IsFilledToward D.scale D.corner D.region
  one_le_scale : 1 ≤ D.scale
  one_le_cellSide : 1 ≤ D.cellSide
  scale_le : (D.scale : ℝ) ≤ r₀ * D.cellSide
  cellSites_subset : ∀ y ∈ D.cells, D.cellSites y ⊆ D.region
  card_cellSites : ∀ y ∈ D.cells, (D.cellSites y).card = D.cellSide ^ 4
  base_mem : D.base ∈ D.cells
  card_cells_le : (D.cells.card : ℝ) ≤ n₁
  morrey_bound : ∀ (x : Lattice4) (r : ℕ), 1 ≤ r → r ≤ 80 * D.scale →
    ∑ u ∈ D.region.filter (fun u => supNorm (u - x) ≤ r), D.targetWeight u ≤
      A * ((r : ℝ) / ((80 * D.scale : ℕ) : ℝ)) ^ (4 * θ)
  pin_congr : ∀ γ γ' : Lattice4 → UnitQuaternion, (∀ x ∈ D.region, γ x = γ' x) →
    ∀ y ∈ D.cells, D.pin γ y = D.pin γ' y
  pin_continuousOn : ∀ y ∈ D.cells,
    ContinuousOn (fun γ : D.region → UnitQuaternion => ((D.pin (D.extendByOne γ) y : UnitQuaternion) : ℍ[ℝ]))
      {γ | D.defectQuarticSum (D.extendByOne γ) ≤ c₁}
  curl_le : ∀ γ, D.pinnedQuarticSum γ ≤ b →
    (∑ p ∈ orientedPlaquettesOf D.region, ‖plaquetteCurl (D.defectForm γ) p.1 p.2.1 p.2.2‖ ^ 2) ^ 2 ≤
      d γ ^ 4 + η ^ 4 * D.pinnedQuarticSum γ
  pin_hasDerivAt : ∀ γ, D.pinnedQuarticSum γ ≤ b → ∀ (ξ : Lattice4 → imaginaryQuaternions), ∀ y ∈ D.cells,
    ∃ ζ : ℍ[ℝ], ζ.re = 0 ∧
      HasDerivAt (fun τ : ℝ => ((D.pin (PinnedGaugeData.rotateAlong ξ τ γ) y : UnitQuaternion) : ℍ[ℝ]))
        (ζ * ((D.pin γ y : UnitQuaternion) : ℍ[ℝ])) 0 ∧
      ‖ζ - D.cellMean y (fun x => (ξ x : ℍ[ℝ]))‖ ^ 4 ≤
        η ^ 4 * (∑ x ∈ D.cellSites y, ‖(ξ x : ℍ[ℝ])‖ ^ 4) / (D.cellSide : ℝ) ^ 4
  pin_sub_le : ∀ γ, D.pinnedQuarticSum γ ≤ b → ∀ y ∈ D.cells, ∀ y' ∈ D.cells, D.Adj y y' →
    ‖pureComponent ((D.pin γ y : UnitQuaternion) : ℍ[ℝ]) - pureComponent ((D.pin γ y' : UnitQuaternion) : ℍ[ℝ]) -
        D.bondAverage y y' (D.defectForm γ)‖ ^ 4 ≤
      C₂ * d γ ^ 4 + η ^ 4 * D.pinnedQuarticSum γ
  bondAverage_add : ∀ y ∈ D.cells, ∀ y' ∈ D.cells, D.Adj y y' → ∀ f g,
    D.bondAverage y y' (f + g) = D.bondAverage y y' f + D.bondAverage y y' g
  bondAverage_congr : ∀ y ∈ D.cells, ∀ y' ∈ D.cells, D.Adj y y' → ∀ f g : Lattice4 → Fin 4 → ℍ[ℝ],
    (∀ b ∈ bondsOf D.region, f b.1 b.2 = g b.1 b.2) → D.bondAverage y y' f = D.bondAverage y y' g
  bondAverage_difference : ∀ y ∈ D.cells, ∀ y' ∈ D.cells, D.Adj y y' → ∀ φ : Lattice4 → ℍ[ℝ],
    D.bondAverage y y' (latticeDifference φ) = D.cellMean y' φ - D.cellMean y φ
  bondAverage_le : ∀ y ∈ D.cells, ∀ y' ∈ D.cells, D.Adj y y' → ∀ f : Lattice4 → Fin 4 → ℍ[ℝ],
    ‖D.bondAverage y y' f‖ ^ 4 ≤ C₃ * ∑ b ∈ bondsOf D.region, ‖f b.1 b.2‖ ^ 4
  chain_bound : ∀ (κ : D.CellIndex → ℍ[ℝ]) (T : ℝ), 0 ≤ T →
    (∀ y ∈ D.cells, ∀ y' ∈ D.cells, D.Adj y y' → ‖κ y - κ y'‖ ^ 4 ≤ T) → κ D.base = 0 →
      ∀ y ∈ D.cells, ‖κ y‖ ^ 4 ≤ n₀ * T
  exists_start : ∃ γ : Lattice4 → UnitQuaternion, D.pinnedQuarticSum γ ≤ b
def pinnedQuarticGaugeStatement : Prop :=
  ∀ θ C₂ C₃ n₀ n₁ r₀ : ℝ, 0 < θ → 0 ≤ C₂ → 0 ≤ C₃ → 0 ≤ n₀ → 0 ≤ n₁ → 0 ≤ r₀ → ∃ Cs cs : ℝ, 0 < Cs ∧ 0 < cs ∧
    ∀ (D : PinnedGaugeData) (A η b c₁ : ℝ) (d : (Lattice4 → UnitQuaternion) → ℝ),
      0 ≤ A → A ≤ cs → 0 ≤ η → η ≤ cs → 0 ≤ b → b ≤ 1 → b < c₁ →
      (∀ γ, 0 ≤ d γ) → IsPinnedGaugeProblem D θ C₂ C₃ n₀ n₁ r₀ A η b c₁ d →
      ∃ γ : Lattice4 → UnitQuaternion, D.pinnedQuarticSum γ ≤ b ∧ D.pinnedQuarticSum γ ≤ Cs * d γ ^ 4
end YangMills.Construction.PinnedGauge
end

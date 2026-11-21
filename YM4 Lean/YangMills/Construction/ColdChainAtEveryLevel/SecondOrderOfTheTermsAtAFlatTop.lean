import YangMills.Construction.ColdChainAtEveryLevel.NormsOfCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
structure HasFirstOrderOn (S : Finset F.Cell) (T : ℝ → ChainChart F) (D : ChainChart F) : Prop where
  fine_zero : ∀ b ∈ innerBonds S 0, (T 0).fine b.1 b.2 = 0
  coarse_zero : ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds S (j + 1), (T 0).coarse j c.1 c.2 = 0
  fine_deriv : ∀ b ∈ innerBonds S 0,
    HasDerivAt (fun τ : ℝ => (((T τ).fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]))
      ((D.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) 0
  coarse_deriv : ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds S (j + 1),
    HasDerivAt (fun τ : ℝ => (((T τ).coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]))
      ((D.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) 0
def rotatedFlatField (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (τ : ℝ) : F.GaugeField F.top :=
  rotatedField (fun y i => τ • v y i) flatTopField
def weightedChainTerms (a : ℝ) (S : Finset F.Cell) (wp : F.Site 0 × Fin 4 × Fin 4 → ℝ)
    (wc : (j : ℕ) → F.Site (j + 1) × Fin 4 → ℝ) (X : F.FieldChain) (k : F.SiteGauge) : ℝ :=
  ∑ p ∈ innerPlaquettes S 0, wp p * (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) +
    a * ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1),
      wc j c * gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c
def weightedQuadraticEnergy (a : ℝ) (S : Finset F.Cell) (wp : F.Site 0 × Fin 4 × Fin 4 → ℝ)
    (wc : (j : ℕ) → F.Site (j + 1) × Fin 4 → ℝ) (R : F.FieldChain) (D : ChainChart F)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) : ℝ :=
  ∑ p ∈ innerPlaquettes S 0, wp p * ‖linearizedCurl (R 0) D.fine p‖ ^ 2 +
    a * ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
      wc j c * ‖((D.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2 +
    a * ∑ c ∈ innerBonds S F.top,
      wc F.depth c * ‖((v c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) - linearPart R D F.top c.1 c.2‖ ^ 2
def secondOrderAtFlatTopStatement : Prop :=
  ∀ (F : BlockFrame) (S : Finset F.Cell) (R : F.FieldChain) (a : ℝ) (wp : F.Site 0 × Fin 4 × Fin 4 → ℝ)
    (wc : (j : ℕ) → F.Site (j + 1) × Fin 4 → ℝ) (T : ℝ → ChainChart F) (D : ChainChart F)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions), Odd F.blockSide →
    (∀ j, j < F.top → ∀ b ∈ innerBonds S j, R j b.1 b.2 = 1) → HasFirstOrderOn S T D →
    weightedChainTerms a S wp wc (chartChain R (T 0) (rotatedFlatField v 0)) (chartGauge R (T 0)) = 0 ∧
    Filter.Tendsto (fun τ : ℝ => weightedChainTerms a S wp wc (chartChain R (T τ) (rotatedFlatField v τ))
        (chartGauge R (T τ)) / τ ^ 2) (𝓝[≠] 0)
      (𝓝 ((1 / 2) * weightedQuadraticEnergy a S wp wc R D v))
end YangMills.Construction.BlockAverages
end

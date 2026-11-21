import YangMills.Construction.ColdChainAtEveryLevel.PinnedRelativeGauge
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
open Classical in
def highEnergyCells (a ε : ℝ) (S : Finset F.Cell) (X : F.FieldChain) (g : F.SiteGauge) : Finset F.Cell :=
  S.filter fun z => ε ^ 2 < patchAction a S z X g
open Classical in
def cellsFarFromHighEnergy (a ε : ℝ) (S : Finset F.Cell) (X : F.FieldChain) (g : F.SiteGauge) :
    Finset F.Cell :=
  S.filter fun z => ∀ y ∈ highEnergyCells a ε S X g, 100 < cellSupDist z y
def criticalChainMinimalityStatement : Prop :=
  ∀ a θ δ A : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < A →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ K₁ : ℝ, 0 < K₁ →
      ∃ ε σ K c : ℝ, 0 < ε ∧ 0 < σ ∧ 0 < K ∧ 0 < c ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F →
        1024 ≤ m → IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions),
          0 < s → s ≤ σ → IsCold S F.top s V →
          (∀ y i, ‖v y i‖ ≤ s) →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ A K₁ s S V (rotatedField v V) U →
            ∀ (X : F.FieldChain) (g : F.SiteGauge), X F.top = rotatedField v V →
              ∃ Γ : F.Cell → F.SiteGauge,
                (∀ z ∈ cellsFarFromHighEnergy a ε S X g, IsPinnedGauge a K S z
                  (chartChain (referenceFieldChain S V) U (rotatedField v V))
                  (chartGauge (referenceFieldChain S V) U) X g (Γ z)) ∧
                c * ((highEnergyCells a ε S X g).card + ∑ z ∈ cellsFarFromHighEnergy a ε S X g,
                  relativeEnergy a S z (chartChain (referenceFieldChain S V) U (rotatedField v V))
                    (chartGauge (referenceFieldChain S V) U) X g (Γ z)) ≤
                gaugedChainAction a S X g - chartAction a S (referenceFieldChain S V) U (rotatedField v V)
end YangMills.Construction.BlockAverages
end

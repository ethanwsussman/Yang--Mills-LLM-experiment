import YangMills.Construction.ColdChainAtEveryLevel.LocalRestrictionsOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
open Classical in
def topBondsAt (b : F.Site F.depth × Fin 4) : Finset (F.Site F.top × Fin 4) :=
  if IsCrossingBond b then {(enclosingCell b.1, b.2)} else ∅
def chartLocalityStatement : Prop :=
  ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ (c : ℝ) (C : ℕ → ℝ), 0 < c ∧ (∀ k, 0 ≤ C k) ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ U : ChainChart F, (∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤ c) →
          ∀ b ∈ chordBonds S, IsLocalRepresentation S (referenceFieldChain S V) (enclosingCell b.1) (topBondsAt b) C U
            (bondChartCoord (referenceFieldChain S V) V b)
end YangMills.Construction.BlockAverages
end

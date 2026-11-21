import YangMills.Construction.HoleBesideASecondHole.TermsOfAChainAtACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.CellTerms
open BlockAverages LumpContours
def smallChartBoundStatement : Prop :=
  ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ δ : ℝ, 0 < δ → ∃ cL CL : ℝ, 0 < cL ∧ 0 < CL ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (r : ℝ) (V : F.GaugeField F.top), 0 < r → r ≤ cL → IsCold S F.top r V →
        ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ cL → ∀ β : ℝ, 0 ≤ β →
          (∀ (π : Equiv.Perm (Fin 4)), ∀ e ∈ innerBonds S F.depth,
            (∀ y ∈ BlockAverages.cellBall S (enclosingCell e.1) 5,
              unweightedLocalNorm S (referenceFieldChain S V) U y ≤ β) →
            ‖(bondCoordinate π V (chartFieldTopFixed (referenceFieldChain S V) U) e : ℍ[ℝ])‖ ≤ CL * (r + β)) ∧
          ∀ p ∈ innerPlaquettes S F.depth,
            (∀ y ∈ BlockAverages.cellBall S (enclosingCell p.1) 5,
              unweightedLocalNorm S (referenceFieldChain S V) U y ≤ β) →
            plaquetteDefect (chartFieldTopFixed (referenceFieldChain S V) U) p ≤ CL * (r + β)
end YangMills.Construction.CellTerms
end

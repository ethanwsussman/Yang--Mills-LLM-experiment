import YangMills.Construction.ColdChainAtEveryLevel.ChartOfAFramingOnAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.PatchMorrey
open BlockAverages LatticeFractionalIntegration PatchLatticeChart GaugeMap
variable {F : BlockFrame}
def frameDefectWeight (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (W : F.GaugeField 0)
    (x : Lattice4) : ℝ :=
  ∑ i : Fin 4, if (x - basisVector i, i) ∈ bondsOf (patchDomain S z) then
    ‖((framedLatticeField S V z W (x - basisVector i) i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 else 0
def criticalChainMorreyStatement : Prop :=
  ∀ a θ δ Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ : ℝ, 0 < C₁ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions), 0 < s → s ≤ c →
          IsCold S F.top s V →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ Ca C₁ s S V (rotatedField v V) U →
            ∀ z ∈ S, ∀ (x : Lattice4) (r : ℕ), 1 ≤ r → r ≤ 80 * (9 * (cellSideLength F).toNat) →
              ∑ u ∈ (patchDomain S z).filter (fun u => supNorm (u - x) ≤ r),
                  frameDefectWeight S V z (criticalFieldChain S V v U 0) u ≤
                (C * s) ^ 4 * ((r : ℝ) / ((80 * (9 * (cellSideLength F).toNat) : ℕ) : ℝ)) ^ (4 * θ)
end YangMills.Construction.PatchMorrey
end

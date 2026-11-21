import YangMills.Construction.HoleBesideASecondHole.PlacesOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace HoleSavings
open BlockAverages LumpContours HoleBounds
def topHotPlaquettesPaidStatement : Prop :=
  ∃ cP : ℝ, 0 < cP ∧ ∀ J₀ : ℕ, 625 ≤ J₀ → ∃ ε : ℝ, 0 < ε ∧ ∀ (a Θ C CJ : ℝ), 1 ≤ a → 1 ≤ Θ → 0 < C → 0 < CJ → ∃ L₀ : ℕ,
    ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ g : LumpGrid L, ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∀ (F : BlockFrame) (D : HoleData F g a s (Θ * s) J₀) (U : F.FieldChain) (S : Finset F.Cell), F.blockSide = L →
        IsCubicTorus F 4096 → D.IsAdmissibleDomain → D.IsFillingChain C ε CJ U → S ⊆ D.keptCells →
        ∃ v : ℕ, D.HasCoreHotLumps C v ∧ cP * s ^ 2 * v ≤ D.totalEnergy - D.energyOn S ∧
          D.hotTopLumps.card ≤ v + 16 * ((D.excitedCells C).card + (D.crowdedCells).card)
end HoleSavings
end YangMills.Construction
end

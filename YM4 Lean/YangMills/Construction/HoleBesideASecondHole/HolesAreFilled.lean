import YangMills.Construction.HoleBesideASecondHole.PlacesOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HoleFilling
open BlockAverages LumpContours HoleSavings HoleBounds
def holesFilledStatement : Prop :=
  ∀ (a ε Θ C : ℝ) (J₀ : ℕ), 1 ≤ a → 0 < ε → 1 ≤ Θ → 0 < C → 625 ≤ J₀ → ∃ CJ : ℝ, 0 < CJ ∧ ∃ L₀ : ℕ,
    ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ g : LumpGrid L, ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∀ (F : BlockFrame) (D : HoleData F g a s (Θ * s) J₀), F.blockSide = L → IsCubicTorus F 4096 →
        D.IsAdmissibleDomain → ∃ U₂ : F.FieldChain, D.IsFillingChain C ε CJ U₂
end YangMills.Construction.HoleFilling
end

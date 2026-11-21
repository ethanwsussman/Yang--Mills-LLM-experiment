import YangMills.Construction.HoleBesideASecondHole.MeanOfAProductOfGroupVariables
import YangMills.Construction.HoleBesideASecondHole.PlacesOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours GroupMeans HoleBounds
namespace HoleSavings.HoleData
variable {F : BlockFrame} {L : ℕ} {g : LumpGrid L} {a s θ : ℝ} {J₀ : ℕ} (D : HoleData F g a s θ J₀)
structure IsMeanMatchingChain (C CJ ε : ℝ) (U₂ : F.FieldChain) : Prop where
  top_eq : U₂ F.top = D.topField
  polar_close : ∀ c : F.Cell × Fin 4, c.1 ∈ D.coreCells C 5 → c.1 + unitStep F.top c.2 ∈ D.coreCells C 5 →
    ‖((polarPart (contourMean J₀ D.hotFineLumps D.base D.fineField c) : UnitQuaternion) : ℍ[ℝ]) -
        (polarPart (contourAverage (U₂ F.depth) c) : UnitQuaternion)‖ ≤ CJ * s / Real.sqrt L ∧
      1 - ‖contourMean J₀ D.hotFineLumps D.base D.fineField c‖ ≤ CJ * s / Real.sqrt L ∧
      1 - ‖contourAverage (U₂ F.depth) c‖ ≤ CJ * s / Real.sqrt L
  lower_energy_le : ∀ X ⊆ D.coreCells C 5,
    cutChainEnergy a F.depth (cutBelow F.depth X) U₂ + a * ∑ c ∈ cutBonds X, blockFit (U₂ F.depth) D.topField c ≤
      D.energyOn X + ε * s ^ 2 * (D.nearbyFineLumps X).card
  energy_le : ∀ X ⊆ D.coreCells C 5,
    cutChainEnergy a F.top X U₂ ≤ D.energyOn X + ε * s ^ 2 * (D.nearbyFineLumps X).card
  lower_energy_local_le : ∀ y ∈ D.coreCells C 6, ∀ X ⊆ cellBall y 1 ∩ D.coreCells C 5,
    cutChainEnergy a F.depth (cutBelow F.depth X) U₂ + a * ∑ c ∈ cutBonds X, blockFit (U₂ F.depth) D.topField c ≤
      CJ * s ^ 2
  energy_local_le : ∀ y ∈ D.coreCells C 6, ∀ X ⊆ cellBall y 1 ∩ D.coreCells C 5,
    cutChainEnergy a F.top X U₂ ≤ CJ * s ^ 2
  eq_fineField_off_lumps : ∀ b ∈ cutBonds (cutBelow F.depth (D.coreCells C 5)),
    nearbyLumps D.hotFineLumps (enclosingCell b.1) = ∅ →
    nearbyLumps D.hotFineLumps (enclosingCell (b.1 + unitStep F.depth b.2)) = ∅ →
    U₂ F.depth b.1 b.2 = D.fineField b.1 b.2
end HoleSavings.HoleData
namespace ContourMeans
open HoleSavings
def contourMeansStatement : Prop :=
  ∀ (a C : ℝ) (J₀ : ℕ), 1 ≤ a → 0 < C → 1 ≤ J₀ → ∃ CJ : ℝ, 0 < CJ ∧ ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ,
    ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ g : LumpGrid L, ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∀ (θ : ℝ) (F : BlockFrame) (D : HoleData F g a s θ J₀), F.blockSide = L → IsCubicTorus F 4096 →
        ∃ U₂ : F.FieldChain, D.IsMeanMatchingChain C CJ ε U₂
end ContourMeans
end YangMills.Construction
end

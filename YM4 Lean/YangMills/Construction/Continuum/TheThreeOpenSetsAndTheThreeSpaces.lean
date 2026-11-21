import YangMills.Construction.Continuum.SchwartzFunctionsFlatOutsideAnOpenSet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
def OpenLociAndFlatSubspaces : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    distinctArgs n = {x : Config n | 0 < minSeparation x} ∧
    (IsOpen (distinctArgs n) ∧ IsOpen (posTimeSet n) ∧ IsOpen (negTimeSet n) ∧
      posTimeSet n ⊆ distinctArgs n ∧ negTimeSet n ⊆ distinctArgs n) ∧
    ∃ S W Wp Wm : Submodule ℂ (Config n → ℂ),
      (S : Set (Config n → ℂ)) = {φ | IsSchwartz φ} ∧
      (W : Set (Config n → ℂ)) = schwartzFlatOffDiagonal n ∧
      (Wp : Set (Config n → ℂ)) = schwartzFlatOffPosTime n ∧
      (Wm : Set (Config n → ℂ)) = schwartzFlatOffNegTime n ∧
      W ≤ S ∧ Wp ≤ S ∧ Wm ≤ S ∧ Wp ≤ W ∧ Wm ≤ W
end YangMills.Construction.ConfigSpace
end

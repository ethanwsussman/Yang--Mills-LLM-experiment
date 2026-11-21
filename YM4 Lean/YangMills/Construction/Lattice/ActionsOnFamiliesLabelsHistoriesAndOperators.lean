import YangMills.Construction.Lattice.ScaleLabels
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def familyImage (σ : FourTorus L m ≃ FourTorus L m) (I : Set (Set (FourTorus L m))) :
    Set (Set (FourTorus L m)) :=
  (fun X => σ '' X) '' I
def scaleDataImage (σ : FourTorus L m ≃ FourTorus L m) (M : ScaleData L m) : ScaleData L m :=
  ⟨σ '' M.domain, σ '' M.smallFieldRegion, σ '' M.markedSet⟩
def IsScaleLabelImage {K n k : ℕ} {c : ℕ → ℕ} (σ : FourTorus L m ≃ FourTorus L m)
    (S S' : ScaleLabel L m K n c k) : Prop :=
  ∀ j, S'.atScale j = scaleDataImage σ (S.atScale j)
end PeriodicLattice
end YangMills.Construction

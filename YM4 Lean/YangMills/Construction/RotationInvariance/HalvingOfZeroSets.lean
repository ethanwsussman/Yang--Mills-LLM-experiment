import YangMills.Construction.RotationInvariance.ZeroSetsAndReflectedLabelledSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.VanishingSetHalving
open RealPlane ForwardTube
def HalvesVanishingSets : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (d : PlaneDataWithAperture m S) (k : ℕ), 1 ≤ k →
    ∀ (l P : Set RealPlane), IsLine l → IsOpenSide l P →
    ∀ j' : ℕ, j' ≤ k →
    ∀ Q' Q : Set (RealPlane × realLabels),
      IsDistinctLabelledSetIn j' P Q' →
      Q ⊆ reflectLabelled l Q' ∪ Q' →
      IsVanishingSet S d.angle k Q →
      IsVanishingSet S d.angle k Q' ∧ IsVanishingSet S d.angle k (reflectLabelled l Q')
end YangMills.Construction.EuclideanFunctionals.VanishingSetHalving
end

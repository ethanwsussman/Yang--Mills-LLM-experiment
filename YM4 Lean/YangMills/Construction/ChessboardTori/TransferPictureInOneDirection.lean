import YangMills.Construction.ChessboardTori.TransferPicture
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
namespace TransferSetup
variable {D : ChessboardSetup} (T : TransferSetup D)
def wilsonSlabBoltzmann (η : T.SlabConfig) : ℂ :=
  (∏ j : Fin T.ratioNat, ∏ q : T.TransverseFace,
    Complex.exp (-(D.β : ℂ) * (T.faceAction q (η.1 j) : ℂ))) *
  ∏ j : Fin (T.ratioNat - 1), ∏ b : T.PositiveTransverseEdge,
    boltzmannFactor D (T.axialHolonomy (η.1 ⟨j, by have := j.2; omega⟩)
      (η.1 ⟨j + 1, by have := j.2; omega⟩) (η.2 j) b)
theorem slabBoltzmann_zero (m : SlabCount) (k : ZMod (m : ℕ)) :
    T.slabBoltzmann m (fun _ => 0) k = T.wilsonSlabBoltzmann := by
  funext η
  simp only [slabBoltzmann, wilsonSlabBoltzmann, zero_sub, boltzmannFactor, slabFaceAction,
    slabAxialAction]
end TransferSetup
end ChessboardTori
end YangMills.Construction
end

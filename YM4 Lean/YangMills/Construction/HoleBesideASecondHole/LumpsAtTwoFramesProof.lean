import YangMills.Construction.HoleBesideASecondHole.CarriedSitesAndPaths
import YangMills.Construction.HoleBesideASecondHole.LumpsAtTwoFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages TorusFields FrameTransfer
namespace LumpTransfer
theorem lumpTransfer : lumpTransferStatement := by
  intro F F' j j' h
  refine ⟨transferSite_transferSite h, fun m W => transferField_readAtLevel h W, plaquetteDefect_transfer h,
    cutPlaquettes_transferSet h, lumpsNeighbourhood_transferLumps h, ?_⟩
  intro L g
  exact ⟨isLump_transferSet h g, fun s X W => hotLumps_transfer h g s X W⟩
end LumpTransfer
end YangMills.Construction
end

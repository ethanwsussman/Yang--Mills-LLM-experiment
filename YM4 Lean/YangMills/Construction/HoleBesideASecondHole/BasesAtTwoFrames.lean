import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import YangMills.Construction.HoleBesideASecondHole.OneTorusAtTwoFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FrameTransfer
open BlockAverages LumpContours
def BasesAgreeAcrossFrames : Prop :=
  ∀ F F' : BlockFrame, F.blockSide = F'.blockSide → F.extent = F'.extent →
    transferSet F' F'.top (torusCells F) = torusCells F' ∧
    (∀ S : Finset F.Cell,
      cutBelow F'.depth (transferSet F' F'.top S) = transferSet F' F'.depth (cutBelow F.depth S)) ∧
    (∀ S : Finset F.Cell,
      cutBonds (transferSet F' F'.top S) = (cutBonds S).image (transferBond F' F'.top)) ∧
    (∀ x : F.Site F.depth, enclosingCell (transferSite F' F'.depth x) = transferSite F' F'.top (enclosingCell x)) ∧
    (∀ (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth),
      (IsBaseChoice J₀ (transferLumps F' F'.depth h) (transferBases F' b) ↔ IsBaseChoice J₀ h b) ∧
      ∀ (W : F.GaugeField F.depth) (c : F.Cell × Fin 4),
        contourMean J₀ (transferLumps F' F'.depth h) (transferBases F' b) (transferField F' F'.depth W)
            (transferBond F' F'.top c) = contourMean J₀ h b W c ∧
        ∀ V : F.GaugeField F.top,
          contourFit J₀ (transferLumps F' F'.depth h) (transferBases F' b) (transferField F' F'.depth W)
            (transferField F' F'.top V) (transferBond F' F'.top c) = contourFit J₀ h b W V c) ∧
    ∀ (π : Equiv.Perm (Fin 4)) (V : F.GaugeField F.top) (W : F.GaugeField F.depth) (b : F.Site F.depth × Fin 4),
      bondCoordinate π (transferField F' F'.top V) (transferField F' F'.depth W) (transferBond F' F'.depth b) =
        bondCoordinate π V W b
end YangMills.Construction.FrameTransfer
end

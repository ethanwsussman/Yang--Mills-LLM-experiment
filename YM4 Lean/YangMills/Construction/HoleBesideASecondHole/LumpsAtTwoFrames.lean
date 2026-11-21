import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import YangMills.Construction.HoleBesideASecondHole.OneTorusAtTwoFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours FrameTransfer TorusFields
namespace LumpTransfer
def lumpTransferStatement : Prop :=
  ∀ (F F' : BlockFrame) (j j' : ℕ), (∀ i, F.period j i = F'.period j' i) →
    (∀ x : F.Site j, transferSite F j (transferSite F' j' x) = x) ∧
    (∀ (m : ℕ) (W : TorusField m), transferField F' j' (readAtLevel F j W) = readAtLevel F' j' W) ∧
    (∀ (X : F.GaugeField j) (p : F.Site j × Fin 4 × Fin 4),
      BlockAverages.plaquetteDefect (transferField F' j' X) (transferSite F' j' p.1, p.2) =
        BlockAverages.plaquetteDefect X p) ∧
    (∀ X : Finset (F.Site j), (cutPlaquettes (transferSet F' j' X)) =
      (cutPlaquettes X).image fun p => (transferSite F' j' p.1, p.2)) ∧
    (∀ H : Finset (Finset (F.Site j)),
      lumpsNeighbourhood (transferLumps F' j' H) = transferSet F' j' (lumpsNeighbourhood H)) ∧
    ∀ {L : ℕ} (g : LumpGrid L),
      (∀ l : Finset (F.Site j), IsLump g (transferSet F' j' l) ↔ IsLump g l) ∧
      ∀ (s : ℝ) (X : Finset (F.Site j)) (W : F.GaugeField j),
        hotLumps g s (transferSet F' j' X) (transferField F' j' W) =
          transferLumps F' j' (hotLumps g s X W)
end LumpTransfer
end YangMills.Construction
end

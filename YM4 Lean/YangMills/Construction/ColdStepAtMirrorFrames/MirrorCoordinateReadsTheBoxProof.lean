import YangMills.Construction.ColdStepAtMirrorFrames.MirrorCoordinateReadsTheBox
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorReadsItsBox
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem reflectedCoordinateReadsBox (hRR : reflectedFieldReadsBox) :
    ReflectedCoordinateReadsBox := by
  classical
  have hR : ReflectedBondReadsBox := hRR.1
  rintro ⟨L, t, side⟩ ⟨L', t', side'⟩ m a ρ y y' V V' o i hL ht hm hag
  simp only at hL ht
  subst hL
  subst ht
  have hfield : @reflectedField ⟨L, t, side⟩ m y V = @reflectedField ⟨L, t, side'⟩ m y' V' := by
    funext z j
    have h1 := hR ⟨L, t, side⟩ m z j hm
    have h2 := hR ⟨L, t, side'⟩ m z j hm
    rw [h1.2 y V, h2.2 y' V']
    have e := hag (sourceOffset (F := ⟨L, t, side⟩) m z j, j) h1.1
    by_cases hf : IsForwardOriented (F := ⟨L, t, side⟩) m z j
    · have hf' : IsForwardOriented (F := ⟨L, t, side'⟩) m z j := hf
      rw [if_pos hf, if_pos hf']
      exact e
    · have hf' : ¬ IsForwardOriented (F := ⟨L, t, side'⟩) m z j := hf
      rw [if_neg hf, if_neg hf']
      exact congrArg (fun g => g⁻¹) e
  exact congrArg (fun X => minimizingBondCoordinate a ρ (finiteCells (reflectedFrame ⟨L, t, side⟩ m))
    (siteOfCoords (reflectedFrame ⟨L, t, side⟩ m).depth o, i) X) hfield
end YangMills.Construction.ColdStepAtMirrorFrames
end

import YangMills.Construction.ReflectionPositivity.CentredObservableAndFunctionals
import YangMills.Construction.ReflectionPositivity.ReflectionPositiveAtAMirror
import YangMills.Construction.ToriAtArbitraryCouplings.ClassesOfFunctionsSeparatedTuplesAndTheSeparation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient CoordMirror)
namespace TorusSide
variable (s : TorusSide)
def CumulantsInvariantUnder (F : Ambient.ConnectedFamily s.asMirrorData .torus)
    (r : s.asMirrorData.Torus ≃ s.asMirrorData.Torus) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (X : s.sepOfLength .torus n),
    ∃ h : ReflectionPositivity.TorusTuples.transportTuple (s := s.asMirrorData.toStandingParameters) r X.1 ∈
        s.sepOfLength .torus n,
      F.fn n hn ⟨_, h⟩ = F.fn n hn X
structure CumulantsInvariant (F : Ambient.ConnectedFamily s.asMirrorData .torus) : Prop where
  translate : ∀ v : s.asMirrorData.Torus,
    s.CumulantsInvariantUnder F (ReflectionPositivity.TorusTuples.shiftBy v)
  signedPerm : ∀ (w : Matrix (Fin 4) (Fin 4) ℝ) (hw : w ∈ PeriodicLattice.signedPermMatrices),
    s.CumulantsInvariantUnder F
      (ReflectionPositivity.TorusTuples.signedMatrixEquiv s.asMirrorData.toStandingParameters hw)
structure ReflectionPositiveAt
    (F : Ambient.ConnectedFamily s.asMirrorData .torus) (S : CoordMirror) : Prop where
  reflectAppend_mem : ∀ X ∈ Ambient.separatedWithin s.asMirrorData .torus
      (S.upperSide s.asMirrorData .torus),
    ∀ Y ∈ Ambient.separatedWithin s.asMirrorData .torus (S.upperSide s.asMirrorData .torus),
      S.reflectAppend s.asMirrorData .torus X Y ∈ s.sepTuples .torus
  positive : S.IsReflectionPositiveFor s.asMirrorData .torus F.centeredFunctional
end TorusSide
end YangMills.Construction.ToriAtArbitraryCouplings
end

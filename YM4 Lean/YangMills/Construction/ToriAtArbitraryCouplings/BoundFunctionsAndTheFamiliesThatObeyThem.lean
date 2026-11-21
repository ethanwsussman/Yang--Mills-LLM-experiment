import YangMills.Construction.Continuum.ClusterBound
import YangMills.Construction.ToriAtArbitraryCouplings.MultilinearAndSymmetricFunctionalsOnClassesOfTuples
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace TorusSide
variable (s : TorusSide)
def admissibleRadiusSet : Ambient → Set ℝ
  | .torus => Ioo 0 (s.length / 4)
  | .euclidean => Ioi 0
def IsPermInvariantFamily (E : Ambient) (S : Ambient.ConnectedFamily s.asMirrorData E) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), s.IsPermInvariant E (n := n) (S.fn n hn)
def sharpNormProduct (m' : ℕ) (E : Ambient) (X : s.FnTuple E) : ℝ :=
  (X.map (s.sharpNormAt (𝕜 := ℝ) m' E)).prod
def BallSupportedSeparated (E : Ambient) (d R : ℝ) (X : s.FnTuple E) : Prop :=
  (∀ f ∈ X, ∃ B, s.IsBallWithRadius E B R ∧ s.closedSupport E f ⊆ B) ∧
    ∀ i k : Fin X.length, i ≠ k →
      ENNReal.ofReal d ≤ s.setDist E (s.closedSupport E (X.get i)) (s.closedSupport E (X.get k))
def SatisfiesClusterBound (m' : ℕ) (C : Schwinger.ClusterBound) (E : Ambient)
    (S : Ambient.ConnectedFamily s.asMirrorData E) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (d R : ℝ), 0 < d → R ∈ s.admissibleRadiusSet E →
    ∀ X : s.sepOfLength E n, s.BallSupportedSeparated E d R X.1 →
      |S.fn n hn X| ≤ C.value n d R * s.sharpNormProduct m' E X.1
def clusterBoundedFamilies (m' : ℕ) (C : Schwinger.ClusterBound) (E : Ambient) :
    Set (Ambient.ConnectedFamily s.asMirrorData E) :=
  {S | s.IsPermInvariantFamily E S ∧ s.SatisfiesClusterBound m' C E S}
end TorusSide
end YangMills.Construction.ToriAtArbitraryCouplings
end

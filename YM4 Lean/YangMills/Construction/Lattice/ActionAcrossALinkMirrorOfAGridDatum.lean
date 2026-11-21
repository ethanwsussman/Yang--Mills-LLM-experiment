import YangMills.Construction.Lattice.SidesOfALinkMirrorOfAGridDatum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BoxTorus
namespace GridMirror
open TorusDescent
def ActionSplitsAcrossMirror : Prop :=
  ∀ (L : ℕ) (κ : ℤ) (G : CellGrid L κ) (g : G.GridSymmetry) (μ : Fin 4) (c : ℝ),
    IsMirrorReflection g μ c →
      Continuous (halfAction G (posHalf G μ c)) ∧
      (∀ U, 0 ≤ halfAction G (posHalf G μ c) U) ∧
      (∀ U U' : G.GaugeConfig, (∀ b : HalfEdge G (posHalf G μ c), U b.1 = U' b.1) →
        halfAction G (posHalf G μ c) U = halfAction G (posHalf G μ c) U') ∧
      ∀ U : G.GaugeConfig,
        G.wilsonAction U = halfAction G (posHalf G μ c) U +
          halfAction G (posHalf G μ c) (g.pullback U) +
          ∑ᶠ b : TransverseEdge g (posHalf G μ c) μ, mirrorFaceEnergy U b
end GridMirror
end YangMills.Construction
end

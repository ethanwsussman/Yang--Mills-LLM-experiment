import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets
open PeriodicOperators
def addScalarJet {I : PeriodicData} (T : JetQuad I I) (z : ℝ) : JetQuad I I :=
  T.add (JetQuad.smul (z : ℂ) (JetQuad.one I))
def massiveLogFn (L k : ℕ) (p : Fin 4 → ℂ) (μp μm : Fin 4) (z : ℝ) : ℂ :=
  JetQuad.logNumber p (addScalarJet (vertexOperatorJet L k p μp μm) z) -
    1 / 2 * JetQuad.logNumber p (addScalarJet (edgeOperatorJet L k p μp μm) z)
def massiveLogFnSharp (L k : ℕ) (p : Fin 4 → ℂ) (μp μm : Fin 4) : ℂ :=
  massiveLogFn L k p μp μm 1 - deriv (massiveLogFn L k p μp μm) 1 +
    1 / 2 * deriv (deriv (massiveLogFn L k p μp μm)) 1
end YangMills.Construction.Tower.FullSpace.BackgroundJets
end

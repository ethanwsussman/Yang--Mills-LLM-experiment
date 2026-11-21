import YangMills.Construction.PeriodicOperators.PeriodicOperatorsOfFiniteRangeAsLocalOperatorFunctions
import YangMills.Construction.Towers.KernelsFieldsAndPropertiesOfTheTwoOperators
import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.ConstantOpFun (addSmulKernel)
open YangMills.Construction.Tower.FullSpace.BackgroundJets (gaugeFieldOfForm responseAmplitude)
def vertexOpFun (L : ℕ) (z : ℝ) : ((colourEdges L 0 0).Carrier → ℂ) →
    (colourVertices L 0 0).Carrier → (colourVertices L 0 0).Carrier → ℂ :=
  addSmulKernel FullSpace.gaugeLaplacianAt (z : ℂ) (idKernel (colourVertices L 0 0))
def edgeOpFun (L : ℕ) (z : ℝ) : ((colourEdges L 0 0).Carrier → ℂ) →
    (colourEdges L 0 0).Carrier → (colourEdges L 0 0).Carrier → ℂ :=
  addSmulKernel FullSpace.massiveHessianAt (z : ℂ) (idKernel (colourEdges L 0 0))
def scaledVertexOpFun (L k : ℕ) (z : ℝ) : ((remainderIndex L k).Carrier → ℂ) →
    (colourVertices L k 0).Carrier → (colourVertices L k 0).Carrier → ℂ :=
  addSmulKernel (fun f => (FullSpace.rescaledOperators L k (gaugeFieldOfForm L k f)).Delta) (z : ℂ)
    (idKernel (colourVertices L k 0))
def scaledEdgeOpFun (L k : ℕ) (z : ℝ) : ((remainderIndex L k).Carrier → ℂ) →
    (colourEdges L k 0).Carrier → (colourEdges L k 0).Carrier → ℂ :=
  addSmulKernel (fun f => (FullSpace.rescaledOperators L k (gaugeFieldOfForm L k f)).K) (z : ℂ)
    (idKernel (colourEdges L k 0))
open Classical in
def colourDirectionIndicator (L : ℕ) (a : Fin 3) (μ : Fin 4) :
    (colourEdges L 0 0).UnitQuot → ℂ :=
  fun c => if c = (colourEdges L 0 0).mkQuot 1 (a, PlaneWaves.edgeAt L 0 0 μ) then 1 else 0
def logSymbol (L : ℕ) (z : ℝ) (a : Fin 3) (μ ν : Fin 4) (p : Fin 4 → ℂ) : ℂ :=
  JetQuad.logNumber p
      (jetAlong (colourEdges L 0 0) (colourVertices L 0 0) (colourVertices L 0 0) (vertexOpFun L z) p
        (colourDirectionIndicator L a μ) (colourDirectionIndicator L a ν)) -
    1 / 2 * JetQuad.logNumber p
      (jetAlong (colourEdges L 0 0) (colourEdges L 0 0) (colourEdges L 0 0) (edgeOpFun L z) p
        (colourDirectionIndicator L a μ) (colourDirectionIndicator L a ν))
def backgroundCoeff (L k : ℕ) (q : Fin 4 → ℂ) (μ ρ : Fin 4) (m : Fin 4 → ℤ) : ℂ :=
  Classical.epsilon fun b =>
    PlaneWaves.edgeFourierCoeff L k (responseAmplitude L k q μ) ρ m =
      b • Matrices.ComplexMatrix2.pauliFamily 2
end YangMills.Construction.Tower.MassiveOpFunctions
end

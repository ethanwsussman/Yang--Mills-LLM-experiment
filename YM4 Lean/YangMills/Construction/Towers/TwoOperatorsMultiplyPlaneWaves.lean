import YangMills.Construction.Towers.KernelsFieldsAndPropertiesOfTheTwoOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.TwoOperators
def PlaneWaveEigen : Prop :=
  ∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
    (∀ (q : Fin 4 → ℂ) (X : YangMills.Construction.Matrices.ComplexMatrix2),
      X ∈ YangMills.Construction.Matrices.ComplexMatrix2.traceless →
      FullSpace.gaugeLaplacian (fun _ => 1) (FullSpace.vertexPlaneWave L q X) =
        Massive.latticeSymbol q • FullSpace.vertexPlaneWave L q X) ∧
    ∀ (q : Fin 4 → ℂ) (c : Fin 4 → YangMills.Construction.Matrices.ComplexMatrix2),
      (∀ μ, c μ ∈ YangMills.Construction.Matrices.ComplexMatrix2.traceless) →
      FullSpace.massiveHessian (fun _ => 1) (FullSpace.edgePlaneWave L q c) =
        Massive.latticeSymbol q • FullSpace.edgePlaneWave L q c
end YangMills.Construction.Tower.TwoOperators
end

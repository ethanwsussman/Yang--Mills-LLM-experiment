import YangMills.Construction.TestFunctions.LaplacianOfR4
import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TestFunctions (laplacianR4)
def LaplacianCubeParametrix.Statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ ψ ∈ realValuedPart (cc1NearZero ε),
      ∃ χ ∈ realValuedPart (ccInfIn (euclidOpenBall (0 : AmbientSpace) ε)),
        ∀ k ∈ ccInfIn (univ : Set AmbientSpace),
          k = convolve (laplacianR4 (laplacianR4 (laplacianR4 k))) ψ +
            convolve k χ
end YangMills.Construction.TwoPoints
end

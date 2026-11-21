import YangMills.Construction.EuclideanAnalysis.ParametrixOfTheCubedLaplacian
import YangMills.Construction.EuclideanFunctionals.StandingDataOfTheStudyFromOneInsertionToPlates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
structure ProductBoundParams (p C cI cS cPar cCau : ℝ) : Prop where
  exponent_nonneg : 0 ≤ p
  constant_nonneg : 0 ≤ C
  cI_pos : 0 < cI
  cI_lt : cI < 1 / 8
  cS_pos : 0 < cS
  cPar_pos : 0 < cPar
  cCau_pos : 0 < cCau
  cPar_le : cPar ≤ 1 / 2 * cI
  cS_add_cPar_le : cS + cPar ≤ 1 / 8
  cS_add_cCau_le : cS + 4 * cCau ≤ 1 / 8
theorem ProductBoundParams.cS_lt_eighth {p C cI cS cPar cCau : ℝ}
    (h : ProductBoundParams p C cI cS cPar cCau) : cS < 1 / 8 := by
  linarith [h.cPar_pos, h.cS_add_cPar_le]
theorem ProductBoundParams.cS_lt_quarter {p C cI cS cPar cCau : ℝ}
    (h : ProductBoundParams p C cI cS cPar cCau) : cS < 1 / 4 := by
  linarith [h.cS_lt_eighth]
def paramRadius (cPar η : ℝ) : ℝ := cPar * η
def cauchyRadius (cCau η : ℝ) : ℝ := cCau * η
def productExponent (p : ℝ) : ℝ := p + 5
def multiindicesOrderThree : Finset Multiindex := Finset.piAntidiag Finset.univ 3
def laplacianCubedConst : ℝ :=
  ∑ γ ∈ multiindicesOrderThree,
    ((Nat.factorial 3 : ℝ) * (Multiindex.fact (Multiindex.twice γ) : ℝ)) /
      (Multiindex.fact γ : ℝ)
def productAbsConst (cPar cCau : ℝ) : ℝ :=
  80 * max ((cCau ^ 6)⁻¹ * cPar) (cPar ^ 5)⁻¹
def productConst (m : SharpScale) (p C cPar cCau : ℝ) : ℝ :=
  productAbsConst cPar cCau * m.M * (2 : ℝ) ^ p * C *
    (laplacianCubedConst *
        (TestFunctions.uniformNorm EuclideanAnalysis.CubedLaplacian.parametrixOne +
          EuclideanAnalysis.gradUniformNorm EuclideanAnalysis.CubedLaplacian.parametrixOne) +
      TestFunctions.uniformNorm EuclideanAnalysis.CubedLaplacian.remainderDensityOne +
      EuclideanAnalysis.gradUniformNorm EuclideanAnalysis.CubedLaplacian.remainderDensityOne)
end YangMills.Construction.EuclideanFunctionals

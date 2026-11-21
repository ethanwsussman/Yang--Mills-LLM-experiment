import YangMills.Construction.Towers.LinearMapsOnTheRealSpaces
import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower.RealQuadraticTransposes
variable {L n k : ℕ}
def IsRealQuadratic (F : Tower.edgeFormSpace L n k 0 → ℂ) : Prop :=
  ∃ Q : QuadraticForm ℝ (Tower.edgeFormSpace L n k 0), ∀ B, F B = (Q B : ℂ)
def TransposePreservesReal {S S' : Tower.PairedFunctionSpace}
    (T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule)
    (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) : Prop :=
  (∀ h : S'.complexSubmodule, (h : S'.index → Matrices.ComplexMatrix2) ∈ S'.realSubmodule →
    (Tower.PairedFunctionSpace.transposeMap T h : S.index → Matrices.ComplexMatrix2) ∈
      S.realSubmodule) ∧
  (∀ (g : S'.realSubmodule) (h : S'.complexSubmodule),
    (h : S'.index → Matrices.ComplexMatrix2) = g →
    (Tower.PairedFunctionSpace.realTransposeMap T₀ g : S.index → Matrices.ComplexMatrix2) =
      Tower.PairedFunctionSpace.transposeMap T h) ∧
  ∀ (g : S'.realSubmodule) (f : S.realSubmodule),
    S.pair (Tower.PairedFunctionSpace.realTransposeMap T₀ g) f = S'.pair g (T₀ f)
structure TermsRealValued (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) : Prop where
  quadraticTerm_mem : ∀ (B B' : Tower.edgeFormSpace L n k 0) (c : Tower.PositiveEdge L n k k),
    Tower.iterQuadraticTerm U B B' c ∈ Matrices.ComplexMatrix2.hermitianTraceless
  bracketTerm_mem : ∀ (l : Tower.vertexFunctionSpace L n k 0) (B : Tower.edgeFormSpace L n k 0),
    Tower.bracketTerm U (l : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2)
      (B : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) ∈ Tower.edgeFormSpace L n k 0
  bracket_isRealQuadratic : ∀ (J : Tower.edgeFormSpace L n k 0)
      (σ : Tower.edgeFormSpace L n k 0 →ₗ[ℝ] Tower.vertexFunctionSpace L n k 0),
    IsRealQuadratic fun B : Tower.edgeFormSpace L n k 0 =>
      Tower.edgeFormPairing (J : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
        (Tower.bracketTerm U (σ B : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2)
          (B : Tower.Edge L n k 0 → Matrices.ComplexMatrix2))
  bracket_covDiff_isRealQuadratic :
    ∀ (J : Tower.edgeFormSpace L n k 0)
      (σ : Tower.edgeFormSpace L n k 0 →ₗ[ℝ] Tower.vertexFunctionSpace L n k 0),
      IsRealQuadratic fun B : Tower.edgeFormSpace L n k 0 =>
        Tower.edgeFormPairing (J : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
          (Tower.bracketTerm U (σ B : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2)
            (Tower.covDiff U (σ B : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2)))
  quadraticTerm_isRealQuadratic : ∀ (μ : Tower.edgeFormSpace L n k k)
      (τ : Tower.edgeFormSpace L n k 0 →ₗ[ℝ] Tower.edgeFormSpace L n k 0),
    IsRealQuadratic fun B : Tower.edgeFormSpace L n k 0 =>
      Tower.traceFinsumPairing
        (Tower.restrictToPositiveEdges (μ : Tower.Edge L n k k → Matrices.ComplexMatrix2))
        (Tower.iterQuadraticTerm U (τ B) (τ B))
def CovDiffTransposePreservesReal (L n k : ℕ) : Prop :=
  ∀ i ≤ k, ∀ V' ∈ Tower.fieldSpace L n k i,
    ∃ T : (Tower.pairedFunctions (Tower.Vertex L n k i)).complexSubmodule →ₗ[ℂ]
        (Tower.edgePairedSpace L n k i).complexSubmodule,
      (∀ f : (Tower.pairedFunctions (Tower.Vertex L n k i)).complexSubmodule,
        (T f).1 = Tower.covDiff V' f.1) ∧
      TransposePreservesReal (S := Tower.pairedFunctions (Tower.Vertex L n k i))
        (S' := Tower.edgePairedSpace L n k i) T
        (Tower.linearMapWithValues (Tower.vertexFunctionSpace L n k i) (Tower.edgeFormSpace L n k i)
          (Tower.covDiff V'))
structure TransposeProperties (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) : Prop where
  average_transpose :
    ∃ T : (Tower.pairedFunctions (Tower.Vertex L n k 0)).complexSubmodule →ₗ[ℂ]
        (Tower.pairedFunctions (Tower.Vertex L n k k)).complexSubmodule,
      (∀ f : (Tower.pairedFunctions (Tower.Vertex L n k 0)).complexSubmodule,
        (T f).1 = Tower.iterAdjointCubeAverage L n k U k f.1) ∧
      TransposePreservesReal (S := Tower.pairedFunctions (Tower.Vertex L n k 0))
        (S' := Tower.pairedFunctions (Tower.Vertex L n k k)) T (Tower.iterAverageLinear L n k U)
  average_comp_transpose : ∀ g : Tower.vertexFunctionSpace L n k k,
    Tower.iterAverageLinear L n k U (Tower.iterAverageRealTranspose L n k U g) =
      ((L : ℝ) ^ (4 * k))⁻¹ • g
  average_surjective : Function.Surjective (Tower.iterAverageLinear L n k U)
  covariantDeriv_surjective :
    Function.Surjective (Tower.iterCovariantDerivLinear L n k U)
  covDiff_transpose_symmetric : ∀ l l' : Tower.vertexFunctionSpace L n k 0,
    Tower.traceFinsumPairing (l : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2)
        (Tower.covDiffRealTranspose L n k U (Tower.covDiffLinear L n k U l') :
          Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) =
      Tower.traceFinsumPairing
        (Tower.covDiffRealTranspose L n k U (Tower.covDiffLinear L n k U l) :
          Tower.Vertex L n k 0 → Matrices.ComplexMatrix2)
        (l' : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2)
  gaugeFixing_isRealQuadratic : IsRealQuadratic fun B : Tower.edgeFormSpace L n k 0 =>
    ((Tower.traceFinsumNorm
      (Tower.gaugeSliceResidual U B : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) ^ 2 : ℝ) : ℂ)
def hessianFunction (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
    (J : Tower.edgeFormSpace L n k 0) (μ : Tower.edgeFormSpace L n k k)
    (B : Tower.edgeFormSpace L n k 0) : ℂ :=
  ((Tower.leftSecondDeriv (Tower.plaquetteAction L n k) U B B : ℝ) : ℂ) +
    2 * Tower.edgeFormPairing (J : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
      (Tower.bracketTerm U (Tower.backgroundGaugeParameter U B) B) +
    Tower.edgeFormPairing (J : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
      (Tower.bracketTerm U (Tower.backgroundGaugeParameter U B)
        (Tower.covDiff U (Tower.backgroundGaugeParameter U B))) -
    Tower.traceFinsumPairing
      (Tower.restrictToPositiveEdges (μ : Tower.Edge L n k k → Matrices.ComplexMatrix2))
      (Tower.iterQuadraticTerm U (Tower.backgroundShift L n k U B)
        (Tower.backgroundShift L n k U B)) +
    ((Tower.traceFinsumNorm
      (Tower.gaugeSliceResidual U B : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) ^ 2 : ℝ) : ℂ)
structure BackgroundOperatorProperties (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) :
    Prop where
  gaugeParameter_linear :
    ∃ σ : Tower.edgeFormSpace L n k 0 →ₗ[ℝ] Tower.vertexFunctionSpace L n k 0,
      ∀ B : Tower.edgeFormSpace L n k 0,
        (σ B : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) = Tower.RealLinearMaps.extendByZero
            (Tower.iterContourLogDrift L n k U k
              (B : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)) ∧
          (σ B : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) =
            Tower.backgroundGaugeParameter U B
  backgroundShift_apply : ∀ B : Tower.edgeFormSpace L n k 0,
    (Tower.backgroundShift L n k U B : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) =
      (B : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) +
        Tower.covDiff U (Tower.backgroundGaugeParameter U B)
  hessianFunction_isRealQuadratic :
    ∀ (J : Tower.edgeFormSpace L n k 0) (μ : Tower.edgeFormSpace L n k k),
      IsRealQuadratic (hessianFunction U J μ)
  hessianFunction_eq : ∀ (J : Tower.edgeFormSpace L n k 0) (μ : Tower.edgeFormSpace L n k k)
      (B : Tower.edgeFormSpace L n k 0),
    hessianFunction U J μ B = (Tower.backgroundHessianForm U J μ B : ℂ)
  existsUnique_hessian : ∀ (J : Tower.edgeFormSpace L n k 0) (μ : Tower.edgeFormSpace L n k k),
    ∃! X : Tower.edgeFormSpace L n k 0 →ₗ[ℝ] Tower.edgeFormSpace L n k 0,
      Tower.IsBackgroundHessian U J μ X
def Statement : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    CovDiffTransposePreservesReal L n k ∧
      Tower.EventuallyNearIdentity (Tower.fieldSpace L n k 0) fun U =>
        TermsRealValued U ∧ TransposeProperties U ∧ BackgroundOperatorProperties U
end Tower.RealQuadraticTransposes
end YangMills.Construction
end

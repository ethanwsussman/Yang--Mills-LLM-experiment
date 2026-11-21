import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
structure GaugeFixingTransferData (L n k : ℕ)
    (Q Q' : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k)
    (T : QuadraticForm ℝ (LinearMap.ker Q)) (X : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0)
    (r' : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k)
    (Y : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0) where
  grad : vertexFunctionSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0
  gradAdjoint : edgeFormSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0
  topGrad : vertexFunctionSpace L n k k →ₗ[ℝ] edgeFormSpace L n k k
  restr : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k
  restrAdjoint : vertexFunctionSpace L n k k →ₗ[ℝ] vertexFunctionSpace L n k 0
  newRestrAdjoint : vertexFunctionSpace L n k k →ₗ[ℝ] vertexFunctionSpace L n k 0
  shift : edgeFormSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k
  hessForm : QuadraticForm ℝ (LinearMap.ker Q)
  gaugeMap : LinearMap.ker Q →ₗ[ℝ] vertexFunctionsVanishingAtTop L n k
  gaugeMapOnKernel : vertexFunctionsVanishingAtTop L n k →ₗ[ℝ] vertexFunctionsVanishingAtTop L n k
  grad_injective : Function.Injective grad
  topGrad_injective : Function.Injective topGrad
  constraint_surjective : Function.Surjective Q
  restr_surjective : Function.Surjective restr
  restr_apply : ∀ l : vertexFunctionSpace L n k 0,
    (restr l : Vertex L n k k → Matrices.ComplexMatrix2) =
      restrictVertexFunction k (l : Vertex L n k 0 → Matrices.ComplexMatrix2)
  constraint_grad : ∀ l, Q (grad l) = topGrad (restr l)
  gradAdjoint_pair : ∀ (B : edgeFormSpace L n k 0) (l : vertexFunctionSpace L n k 0),
    traceFinsumPairing (gradAdjoint B : Vertex L n k 0 → Matrices.ComplexMatrix2)
        (l : Vertex L n k 0 → Matrices.ComplexMatrix2) =
      edgeFormPairing (B : Edge L n k 0 → Matrices.ComplexMatrix2)
        (grad l : Edge L n k 0 → Matrices.ComplexMatrix2)
  restrAdjoint_pair : ∀ (g : vertexFunctionSpace L n k k) (l : vertexFunctionSpace L n k 0),
    traceFinsumPairing (restrAdjoint g : Vertex L n k 0 → Matrices.ComplexMatrix2)
        (l : Vertex L n k 0 → Matrices.ComplexMatrix2) =
      traceFinsumPairing (g : Vertex L n k k → Matrices.ComplexMatrix2)
        (restr l : Vertex L n k k → Matrices.ComplexMatrix2)
  restr_restrAdjoint : ∀ g, restr (restrAdjoint g) = g
  newRestrAdjoint_pair : ∀ (g : vertexFunctionSpace L n k k) (l : vertexFunctionSpace L n k 0),
    traceFinsumPairing (newRestrAdjoint g : Vertex L n k 0 → Matrices.ComplexMatrix2)
        (l : Vertex L n k 0 → Matrices.ComplexMatrix2) =
      traceFinsumPairing (g : Vertex L n k k → Matrices.ComplexMatrix2)
        (r' l : Vertex L n k k → Matrices.ComplexMatrix2)
  newRestr_eq : ∀ l, r' l = restr l + shift (grad l)
  newConstraint_eq : ∀ B, Q' B = Q B + topGrad (shift B)
  newRestr_newRestrAdjoint : ∀ g, r' (newRestrAdjoint g) = ((L : ℝ) ^ (4 * k))⁻¹ • g
  vertexOp_eq : ∀ l, Y l = gradAdjoint (grad l)
  hessForm_add_grad : ∀ (B : LinearMap.ker Q) (κ : LinearMap.ker restr)
    (h : grad κ ∈ LinearMap.ker Q), hessForm (B + ⟨grad κ, h⟩) = hessForm B
  quadratic_eq : ∀ B : LinearMap.ker Q, T B = hessForm B +
    (traceFinsumPairing (gaugeMap B : Vertex L n k 0 → Matrices.ComplexMatrix2)
      (gaugeMap B : Vertex L n k 0 → Matrices.ComplexMatrix2)).re
  posDef : T.PosDef
  gaugeMapOnKernel_apply : ∀ (κ : vertexFunctionsVanishingAtTop L n k)
    (l : vertexFunctionSpace L n k 0) (h : grad l ∈ LinearMap.ker Q),
    (l : Vertex L n k 0 → Matrices.ComplexMatrix2) = κ →
    gaugeMapOnKernel κ = gaugeMap ⟨grad l, h⟩
  abs_det_gaugeMapOnKernel : |LinearMap.det gaugeMapOnKernel| = 1
  edgeOp_symm : ∀ B B' : edgeFormSpace L n k 0,
    edgeFormPairing (B : Edge L n k 0 → Matrices.ComplexMatrix2)
        (X B' : Edge L n k 0 → Matrices.ComplexMatrix2) =
      edgeFormPairing (X B : Edge L n k 0 → Matrices.ComplexMatrix2)
        (B' : Edge L n k 0 → Matrices.ComplexMatrix2)
  edgeOp_quadratic : ∀ (B : edgeFormSpace L n k 0), Q' B = 0 →
    ∀ h : B + grad (restrAdjoint (shift B)) ∈ LinearMap.ker Q,
      edgeFormPairing (B : Edge L n k 0 → Matrices.ComplexMatrix2)
          (X B : Edge L n k 0 → Matrices.ComplexMatrix2) =
        ((hessForm ⟨_, h⟩ + traceFinsumNorm ((gradAdjoint B -
          ((L : ℝ) ^ (4 * k)) • newRestrAdjoint (r' (gradAdjoint B)) :
            vertexFunctionSpace L n k 0) : Vertex L n k 0 → Matrices.ComplexMatrix2) ^ 2 : ℝ) : ℂ)
end YangMills.Construction.Tower
end

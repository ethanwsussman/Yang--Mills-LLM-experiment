import YangMills.Construction.Towers.BackgroundGaugeFunctionalIsFormedAtTheTrivialPointProof
import YangMills.Construction.Towers.GaussianNumberThroughTwoSaddleDeterminants
import YangMills.Construction.Towers.GaussianNumberThroughTwoSaddlesOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tower GaussianConstraint Matrices
namespace GaussianOnTower
section InnerCores
variable {A C G Gc : Type} [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A]
  [AddCommGroup C] [Module ℝ C] [FiniteDimensional ℝ C]
  [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G]
  [AddCommGroup Gc] [Module ℝ Gc] [FiniteDimensional ℝ Gc]
theorem gaussianNumber_eq_of_cores (hS : GaussianNumberViaTwoSaddleDeterminants)
    (cA : InnerProductSpace.Core ℝ A) (cC : InnerProductSpace.Core ℝ C)
    (cG : InnerProductSpace.Core ℝ G) (cGc : InnerProductSpace.Core ℝ Gc)
    (D : G →ₗ[ℝ] A) (Dt : A →ₗ[ℝ] G) (Dc : Gc →ₗ[ℝ] C) (Q Q' : A →ₗ[ℝ] C)
    (r r' : G →ₗ[ℝ] Gc) (rt rt' : Gc →ₗ[ℝ] G) (m : A →ₗ[ℝ] Gc) (a : ℝ) (ha : 0 < a)
    (H T : QuadraticForm ℝ (LinearMap.ker Q)) (Lf : LinearMap.ker Q →ₗ[ℝ] LinearMap.ker r)
    (v : LinearMap.ker r →ₗ[ℝ] LinearMap.ker r) (X : A →ₗ[ℝ] A) (Y : G →ₗ[ℝ] G)
    (hD : Function.Injective D) (hDc : Function.Injective Dc)
    (hQ : Function.Surjective Q) (hr : Function.Surjective r)
    (hQD : ∀ l, Q (D l) = Dc (r l))
    (hDt : ∀ B l, cG.inner (Dt B) l = cA.inner B (D l))
    (hrt : ∀ g l, cG.inner (rt g) l = cGc.inner g (r l))
    (hrrt : ∀ g, r (rt g) = g)
    (hrt' : ∀ g l, cG.inner (rt' g) l = cGc.inner g (r' l))
    (hr' : ∀ l, r' l = r l + m (D l))
    (hQ' : ∀ B, Q' B = Q B + Dc (m B))
    (hrrt' : ∀ g, r' (rt' g) = a • g)
    (hY : ∀ l, Y l = Dt (D l))
    (hshift : ∀ (B : LinearMap.ker Q) (κ : LinearMap.ker r) (h : D κ ∈ LinearMap.ker Q),
      H (B + ⟨D κ, h⟩) = H B)
    (hT : ∀ B, T B = H B + cG.inner (Lf B : G) (Lf B : G))
    (hTpos : T.PosDef)
    (hv : ∀ (κ : LinearMap.ker r) (h : D κ ∈ LinearMap.ker Q), v κ = Lf ⟨D κ, h⟩)
    (hdet : |LinearMap.det v| = 1)
    (hXs : ∀ B B', cA.inner B (X B') = cA.inner (X B) B')
    (hXf : ∀ B, Q' B = 0 → ∀ h : B + D (rt (m B)) ∈ LinearMap.ker Q,
      cA.inner B (X B) = H ⟨_, h⟩ +
        cG.inner (Dt B - a⁻¹ • rt' (r' (Dt B))) (Dt B - a⁻¹ • rt' (r' (Dt B)))) :
    saddleDetOfCores cA cC X Q' ≠ 0 ∧ saddleDetOfCores cG cGc Y r' ≠ 0 ∧
      constrainedGaussianNumberOfCores cA cC Q T =
        (2 * Real.pi) ^ (((Module.finrank ℝ A : ℝ) - (Module.finrank ℝ C : ℝ)) / 2) *
          a ^ (-(Module.finrank ℝ Gc : ℝ) / 2) *
          |saddleDetOfCores cA cC X Q'| ^ (-(1 / 2) : ℝ) *
          |saddleDetOfCores cG cGc Y r'| := by
  let := cA.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cA.toCore
  let := cC.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cC.toCore
  let := cG.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cG.toCore
  let := cGc.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cGc.toCore
  have hadjD : LinearMap.adjoint D = Dt := ((LinearMap.eq_adjoint_iff Dt D).mpr hDt).symm
  have hadjr : LinearMap.adjoint r = rt := ((LinearMap.eq_adjoint_iff rt r).mpr hrt).symm
  have hadjr' : LinearMap.adjoint r' = rt' := ((LinearMap.eq_adjoint_iff rt' r').mpr hrt').symm
  have hgauge : shiftedGaugeMap r m D = r' := LinearMap.ext fun l => (hr' l).symm
  have hcon : shiftedConstraint Q Dc m = Q' := LinearMap.ext fun B => (hQ' B).symm
  have hDY : LinearMap.adjoint D ∘ₗ D = Y := LinearMap.ext fun l => by
    rw [LinearMap.comp_apply, hadjD, hY]
  have hmain := hS A C G Gc D Dc Q r m a H T Lf v X hD hDc hQ hr (LinearMap.ext hQD)
    (LinearMap.ext fun g => by rw [hadjr]; exact hrrt g) ha
    (LinearMap.ext fun g => by rw [hgauge, hadjr']; exact hrrt' g) hshift
    (fun B => by
      rw [hT B, ← real_inner_self_eq_norm_sq]
      rfl)
    hTpos hv hdet (fun x y => (hXs x y).symm)
    (fun B hB h => by
      have h' : B + D (rt (m B)) ∈ LinearMap.ker Q := by rwa [hadjr] at h
      have hsub : (⟨_, h⟩ : LinearMap.ker Q) = ⟨_, h'⟩ := Subtype.ext (by simp only [hadjr])
      rw [hsub, hgauge, hadjr', hadjD, ← real_inner_self_eq_norm_sq]
      rw [hcon] at hB
      exact hXf B hB h')
  rw [hgauge, hcon, hDY] at hmain
  exact hmain
end InnerCores
theorem log_rpow_mul_abs_det (p q a s t : ℝ) (ha : 0 < a) (hs : s ≠ 0) (ht : t ≠ 0) :
    Real.log ((2 * Real.pi) ^ p * a ^ q * |s| ^ (-(1 / 2) : ℝ) * |t|) =
      (p * Real.log (2 * Real.pi) + q * Real.log a) - (1 / 2) * Real.log |s| + Real.log |t| := by
  have h2 : 0 < 2 * Real.pi := by positivity
  have hs' : 0 < |s| := abs_pos.mpr hs
  have ht' : 0 < |t| := abs_pos.mpr ht
  rw [Real.log_mul (by positivity) ht'.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow h2, Real.log_rpow ha,
    Real.log_rpow hs']
  ring
section TowerSpaces
variable {L n k j : ℕ}
theorem vertexFunctionsEuclidean_of (hP : FaceSums.FacesAndPairings)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    VertexFunctionsEuclidean L n k j := by apply _root_.YangMills.Construction.Tower.TrivialFieldGauge.vertexFunctionsEuclidean_of <;> assumption
theorem edgeFormsEuclidean_of (hF : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    EdgeFormsEuclidean L n k j := by apply _root_.YangMills.Construction.Tower.TrivialFieldGauge.edgeFormsEuclidean_of <;> assumption
variable {Q Q' : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k}
  {T : QuadraticForm ℝ (LinearMap.ker Q)}
  {X : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0}
  {r' : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k}
  {Y : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0}
def restrKerEquiv (d : GaugeFixingTransferData L n k Q Q' T X r' Y) :
    LinearMap.ker d.restr ≃ₗ[ℝ] vertexFunctionsVanishingAtTop L n k where
  toFun x := ⟨((x : vertexFunctionSpace L n k 0) : Vertex L n k 0 → ComplexMatrix2),
    (x : vertexFunctionSpace L n k 0).2, by
    rw [← d.restr_apply, LinearMap.mem_ker.mp x.2]
    rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨⟨(y : Vertex L n k 0 → ComplexMatrix2), y.2.1⟩, LinearMap.mem_ker.mpr
    (Subtype.ext (by
      rw [d.restr_apply]
      exact y.2.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
end TowerSpaces
theorem gaussianLogViaTwoSaddleDets_holds
    (hS : GaussianNumberViaTwoSaddleDeterminants)
    (hP : FaceSums.FacesAndPairings)
    (hF : FiniteSideFormSpaces) :
    GaussianLogViaTwoSaddleDets := by
  intro L n k hL hn _
  have hFF : EdgeFormsEuclidean L n k 0 ∧ EdgeFormsEuclidean L n k k :=
    ⟨edgeFormsEuclidean_of hF hL hn (Nat.zero_le _), edgeFormsEuclidean_of hF hL hn le_rfl⟩
  have hVV : VertexFunctionsEuclidean L n k 0 ∧ VertexFunctionsEuclidean L n k k :=
    ⟨vertexFunctionsEuclidean_of hP hL hn (Nat.zero_le _),
      vertexFunctionsEuclidean_of hP hL hn le_rfl⟩
  have := hFF.1.1
  have := hFF.2.1
  have := hVV.1.1
  have := hVV.2.1
  have hLpos : (0 : ℝ) < (L : ℝ) ^ (4 * k) := by
    have hL2 := hL.2
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hapos : (0 : ℝ) < ((L : ℝ) ^ (4 * k))⁻¹ := inv_pos.mpr hLpos
  refine ⟨(((Module.finrank ℝ (edgeFormSpace L n k 0) : ℝ) -
      (Module.finrank ℝ (edgeFormSpace L n k k) : ℝ)) / 2) * Real.log (2 * Real.pi) +
    (-(Module.finrank ℝ (vertexFunctionSpace L n k k) : ℝ) / 2) *
      Real.log ((L : ℝ) ^ (4 * k))⁻¹, ?_⟩
  rintro Q Q' T X r' Y ⟨d⟩
  have hcA := hFF.1.2.choose_spec
  have hcC := hFF.2.2.choose_spec
  have hcG := hVV.1.2.choose_spec
  have hcGc := hVV.2.2.choose_spec
  have e₁ : constrainedGaussianOnEdgeForms Q T =
      constrainedGaussianNumberOfCores hFF.1.2.choose hFF.2.2.choose Q T := dif_pos hFF
  have e₂ : saddleDetOnEdgeForms X Q' =
      saddleDetOfCores hFF.1.2.choose hFF.2.2.choose X Q' := dif_pos hFF
  have e₃ : saddleDetOnVertexFunctions Y r' =
      saddleDetOfCores hVV.1.2.choose hVV.2.2.choose Y r' := dif_pos hVV
  let e := restrKerEquiv d
  obtain ⟨h₁, h₂, h₃⟩ := gaussianNumber_eq_of_cores hS hFF.1.2.choose hFF.2.2.choose
    hVV.1.2.choose hVV.2.2.choose d.grad d.gradAdjoint d.topGrad Q Q' d.restr r'
    d.restrAdjoint d.newRestrAdjoint d.shift ((L : ℝ) ^ (4 * k))⁻¹ hapos d.hessForm T
    (e.symm.toLinearMap ∘ₗ d.gaugeMap)
    (e.symm.toLinearMap ∘ₗ d.gaugeMapOnKernel ∘ₗ e.symm.symm.toLinearMap) X Y
    d.grad_injective d.topGrad_injective d.constraint_surjective d.restr_surjective
    d.constraint_grad
    (fun B l => (hcG _ _).trans
      ((congrArg Complex.re (d.gradAdjoint_pair B l)).trans (hcA _ _).symm))
    (fun g l => (hcG _ _).trans
      ((congrArg Complex.re (d.restrAdjoint_pair g l)).trans (hcGc _ _).symm))
    d.restr_restrAdjoint
    (fun g l => (hcG _ _).trans
      ((congrArg Complex.re (d.newRestrAdjoint_pair g l)).trans (hcGc _ _).symm))
    d.newRestr_eq d.newConstraint_eq d.newRestr_newRestrAdjoint d.vertexOp_eq
    (fun B κ h => d.hessForm_add_grad B κ h)
    (fun B => by
      rw [d.quadratic_eq B, hcG]
      rfl)
    d.posDef
    (fun κ h => d.gaugeMapOnKernel_apply (e κ) _ h rfl |> fun t => by
      simp only [LinearMap.comp_apply]
      exact congrArg e.symm t)
    (by
      rw [LinearMap.det_conj]
      exact d.abs_det_gaugeMapOnKernel)
    (fun B B' => (hcA _ _).trans
      ((congrArg Complex.re (d.edgeOp_symm B B')).trans (hcA _ _).symm))
    (fun B hB h => by
      have hform := congrArg Complex.re (d.edgeOp_quadratic B hB h)
      rw [Complex.ofReal_re] at hform
      rw [hcA, hform, inv_inv, traceFinsumNorm, hcG, Real.sq_sqrt]
      rw [← hcG]
      exact hVV.1.2.choose.re_inner_nonneg _)
  rw [e₁, e₂, e₃]
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact log_rpow_mul_abs_det _ _ _ _ _ hapos h₁ h₂
end GaussianOnTower
end YangMills.Construction
end

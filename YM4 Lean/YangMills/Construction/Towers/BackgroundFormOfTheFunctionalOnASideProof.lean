import YangMills.Construction.Towers.BackgroundFormOfTheFunctionalOnASide
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.DerivativesOfAPlaquetteTerm
import YangMills.Construction.Towers.PlaquettesAndSumsOfATower
import YangMills.Construction.Towers.QuadraticFormsAndTransposesOnTheRealSpaces
import YangMills.Construction.Towers.WilsonActionIsRealAnalyticOnTheConfigurationsProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide
theorem deriv_ofReal_eq_of_agree {F : ℂ → ℂ} {G : ℝ → ℝ} (hF : Differentiable ℂ F)
    (hagree : ∀ r : ℝ, F r = G r) (r : ℝ) : deriv F r = ((deriv G r : ℝ) : ℂ) := by
  have h1 : HasDerivAt (fun x : ℝ => F x) (deriv F r) r := (hF r).hasDerivAt.comp_ofReal
  have h2 : HasDerivAt (fun x : ℝ => (G x : ℂ)) (deriv F r) r := by
    simpa only [hagree] using h1
  have h3 : HasDerivAt G (deriv F r).re r := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r h2
    have e : (⇑Complex.reCLM ∘ fun x : ℝ => (G x : ℂ)) = G := by
      funext x
      simp
    rw [e] at h
    exact h
  have h4 : HasDerivAt (fun x : ℝ => (G x : ℂ)) ((deriv F r).re : ℂ) r := h3.ofReal_comp
  rw [h3.deriv]
  exact h2.unique h4
theorem deriv_deriv_zero_ofReal_of_agree {F : ℂ → ℂ} {G : ℝ → ℝ} (hF : Differentiable ℂ F)
    (hagree : ∀ r : ℝ, F r = G r) : deriv (deriv F) 0 = ((deriv (deriv G) 0 : ℝ) : ℂ) := by
  have hF' : Differentiable ℂ (deriv F) := by
    have := (hF.differentiableOn (s := Set.univ)).deriv isOpen_univ
    exact differentiableOn_univ.mp this
  have := deriv_ofReal_eq_of_agree hF' (deriv_ofReal_eq_of_agree hF hagree) 0
  simpa using this
section Action
variable {L n k : ℕ}
theorem differentiable_matExp_I_mul_smul (Y : ComplexMatrix2) :
    Differentiable ℂ fun t : ℂ => ComplexMatrix2.matExp ((Complex.I * t) • Y) := by
  intro t
  have h1 : HasDerivAt (fun t : ℂ => Complex.I * t) Complex.I t := by
    simpa using (hasDerivAt_id t).const_mul Complex.I
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℂ) Y (Complex.I * t)
  exact (h2.scomp t h1).differentiableAt
theorem differentiable_expProduct (Y : Fin 4 → ComplexMatrix2) :
    Differentiable ℂ (FaceTermDerivatives.expProduct Y) := by
  unfold FaceTermDerivatives.expProduct
  exact (((differentiable_matExp_I_mul_smul _).mul (differentiable_matExp_I_mul_smul _)).mul
    (differentiable_matExp_I_mul_smul _)).mul (differentiable_matExp_I_mul_smul _)
theorem differentiable_fullTrace_comp {f : ℂ → ComplexMatrix2} (hf : Differentiable ℂ f) :
    Differentiable ℂ fun t => ComplexMatrix2.fullTrace (f t) := by
  let ℓ : ComplexMatrix2 →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
  exact ℓ.differentiable.comp hf
theorem differentiable_complexAction_line (hP : FaceTermDerivatives.HoldsOnPeriodicLevel L n k 0)
    (hfin : Finite (Face L n k 0)) {U B : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k 0) :
    Differentiable ℂ fun t : ℂ => complexAction (PeriodicLattice.expTwist (t • B) U) := by
  cases nonempty_fintype (Face L n k 0)
  have h : (fun t : ℂ => complexAction (PeriodicLattice.expTwist (t • B) U)) = fun t : ℂ =>
      ∑ p : Face L n k 0, (1 - (1 / 2) * ComplexMatrix2.fullTrace
        (FaceTermDerivatives.expProduct (transportedForm U B p) t *
          PeriodicLattice.plaquetteHolonomy U p)) := by
    funext t
    unfold complexAction
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← (((hP B hB).1 U hU).1 p).1 t]
    rfl
  rw [h]
  refine Differentiable.fun_sum fun p _ => ?_
  exact (differentiable_const _).sub ((differentiable_const _).mul
    (differentiable_fullTrace_comp ((differentiable_expProduct _).mul (differentiable_const _))))
theorem isPositivelyOriented_or_reverse (b : Edge L n k 0) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.isPositivelyOriented_or_opposite <;> assumption
theorem inv_mem_specialUnitary {W : ComplexMatrix2} (hW : W ∈ ComplexMatrix2.specialUnitary) :
    W⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
theorem expTwist_real_mem_specialUnitary
    (hC : (LeftChartFields.finiteData L n k 0).LeftExpMulMemGroup)
    {U B : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0)
    (hB : B ∈ edgeFormSpace L n k 0) (r : ℝ) (b : Edge L n k 0) :
    PeriodicLattice.expTwist ((r : ℂ) • B) U b ∈ ComplexMatrix2.specialUnitary := by
  have key : ∀ c : Edge L n k 0, c.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • ((r : ℂ) • B) c) * U c ∈
        ComplexMatrix2.specialUnitary := fun c hc =>
    (hC.1 U hU B hB ⟨c, hc⟩).1 r
  unfold PeriodicLattice.expTwist
  split_ifs with h
  · exact key b h
  · exact inv_mem_specialUnitary (key _ ((isPositivelyOriented_or_reverse b).resolve_left h))
theorem complexAction_eq_ofReal (hfin : Finite (Face L n k 0))
    {V : Edge L n k 0 → ComplexMatrix2} (hV : ∀ b, V b ∈ ComplexMatrix2.specialUnitary) :
    complexAction V = (plaquetteAction L n k V : ℂ) := by
  cases nonempty_fintype (Face L n k 0)
  unfold complexAction plaquetteAction PeriodicLattice.wilsonAction
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp : PeriodicLattice.plaquetteHolonomy V p ∈ ComplexMatrix2.specialUnitary := by
    refine Submonoid.list_prod_mem _ fun x hx => ?_
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
    exact hV b
  have him := ComplexMatrix2.fullTrace_im_eq_zero_of_mem_specialUnitary hp
  apply Complex.ext <;>
    simp [complexFaceTerm, PeriodicLattice.plaquetteEnergy,
      PeriodicLattice.plaquetteCost, him]
theorem mem_complexEdgeForms_of_mem {B : Edge L n k 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k 0) : B ∈ complexEdgeForms L n k 0 :=
  ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
theorem complexActionHessian_diag_eq_deriv (U B : Edge L n k 0 → ComplexMatrix2) :
    complexActionHessian U B B =
      deriv (deriv fun t : ℂ => complexAction (PeriodicLattice.expTwist (t • B) U)) 0 := by
  have h : ∀ s : ℂ, deriv (fun t : ℂ => complexAction (PeriodicLattice.expTwist
      (algebraMap ℂ ℂ s • B + algebraMap ℂ ℂ t • B) U)) 0 =
      deriv (fun t : ℂ => complexAction (PeriodicLattice.expTwist (t • B) U)) s := by
    intro s
    have e : (fun t : ℂ => complexAction (PeriodicLattice.expTwist
        (algebraMap ℂ ℂ s • B + algebraMap ℂ ℂ t • B) U)) =
        fun t : ℂ => (fun z : ℂ => complexAction (PeriodicLattice.expTwist (z • B) U)) (s + t) := by
      funext t
      simp only [Algebra.algebraMap_self, RingHom.id_apply, add_smul]
    have d := deriv_comp_const_add
      (fun z : ℂ => complexAction (PeriodicLattice.expTwist (z • B) U)) s 0
    rw [add_zero] at d
    rw [e]
    exact d
  exact congrArg (fun f : ℂ → ℂ => deriv f 0) (funext h)
theorem leftSecondDeriv_diag_eq_deriv (U B : Edge L n k 0 → ComplexMatrix2) :
    leftSecondDeriv (plaquetteAction L n k) U B B =
      deriv (deriv fun r : ℝ =>
        plaquetteAction L n k (PeriodicLattice.expTwist ((r : ℂ) • B) U)) 0 := by
  have h : ∀ s : ℝ, deriv (fun t : ℝ => plaquetteAction L n k (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B) U)) 0 =
      deriv (fun r : ℝ => plaquetteAction L n k (PeriodicLattice.expTwist ((r : ℂ) • B) U)) s := by
    intro s
    have e : (fun t : ℝ => plaquetteAction L n k (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B) U)) =
        fun t : ℝ => (fun z : ℝ =>
          plaquetteAction L n k (PeriodicLattice.expTwist ((z : ℂ) • B) U)) (s + t) := by
      funext t
      simp only [Complex.coe_algebraMap, Complex.ofReal_add, add_smul]
    have d := deriv_comp_const_add
      (fun z : ℝ => plaquetteAction L n k (PeriodicLattice.expTwist ((z : ℂ) • B) U)) s 0
    rw [add_zero] at d
    rw [e]
    exact d
  exact congrArg (fun f : ℝ → ℝ => deriv f 0) (funext h)
theorem complexActionHessian_diag_eq_ofReal (hP : FaceTermDerivatives.HoldsOnPeriodicLevel L n k 0)
    (hfin : Finite (Face L n k 0))
    (hC : (LeftChartFields.finiteData L n k 0).LeftExpMulMemGroup)
    {U B : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0)
    (hB : B ∈ edgeFormSpace L n k 0) :
    complexActionHessian U B B =
      ((leftSecondDeriv (plaquetteAction L n k) U B B : ℝ) : ℂ) := by
  have hU' : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup :=
    ⟨fun b hb => (Matrix.mem_specialUnitaryGroup_iff.mp (hU.1 b hb)).2, hU.2⟩
  rw [complexActionHessian_diag_eq_deriv, leftSecondDeriv_diag_eq_deriv]
  exact deriv_deriv_zero_ofReal_of_agree
    (differentiable_complexAction_line hP hfin hU' (mem_complexEdgeForms_of_mem hB))
    fun r => complexAction_eq_ofReal hfin (expTwist_real_mem_specialUnitary hC hU hB r)
end Action
section Gauge
variable {L n k : ℕ}
theorem linearOfValues_eq {S S' : PairedFunctionSpace}
    {φ : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2}
    {T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule}
    (hT : ∀ f : S.complexSubmodule, (T f : S'.index → ComplexMatrix2) = φ f) :
    PairedFunctionSpace.linearOfValues S S' φ = T := by
  have h : ∀ f : S.complexSubmodule,
      (PairedFunctionSpace.linearOfValues S S' φ f : S'.index → ComplexMatrix2) = φ f :=
    Classical.epsilon_spec
      (p := fun T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule =>
        ∀ f : S.complexSubmodule, (T f : S'.index → ComplexMatrix2) = φ f) ⟨T, hT⟩
  ext1 f
  exact Subtype.ext ((h f).trans (hT f).symm)
theorem transposeOfValues_eq_realTransposeMap {S S' : PairedFunctionSpace}
    {φ : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2}
    {T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule}
    {T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule}
    (hT : ∀ f : S.complexSubmodule, (T f : S'.index → ComplexMatrix2) = φ f)
    (hK : RealQuadraticTransposes.TransposePreservesReal T T₀)
    (g : S'.realSubmodule) (hg : (g : S'.index → ComplexMatrix2) ∈ S'.complexSubmodule) :
    PairedFunctionSpace.transposeOfValues S S' φ g = PairedFunctionSpace.realTransposeMap T₀ g := by
  unfold PairedFunctionSpace.transposeOfValues
  rw [dif_pos hg, linearOfValues_eq hT]
  exact (hK.2.1 g ⟨g, hg⟩ rfl).symm
theorem linearMapWithValues_apply {α β : Type*} {p : Submodule ℝ (α → ComplexMatrix2)}
    {p' : Submodule ℝ (β → ComplexMatrix2)} {f : (α → ComplexMatrix2) → β → ComplexMatrix2}
    (h : ∃ T : p →ₗ[ℝ] p', ∀ x : p, (T x : β → ComplexMatrix2) = f x) (x : p) :
    (linearMapWithValues p p' f x : β → ComplexMatrix2) = f x :=
  Classical.epsilon_spec (p := fun T : p →ₗ[ℝ] p' => ∀ x : p, (T x : β → ComplexMatrix2) = f x) h x
theorem gaugeFixingTerm_eq_of_transposes
    (hD : RealQuadraticTransposes.CovDiffTransposePreservesReal L n k)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0)
    (hT : RealQuadraticTransposes.TransposeProperties U)
    (hA : ∃ T : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k,
      ∀ l : vertexFunctionSpace L n k 0, (T l : Vertex L n k k → ComplexMatrix2) =
        iterAdjointCubeAverage L n k U k (l : Vertex L n k 0 → ComplexMatrix2))
    (B : edgeFormSpace L n k 0) :
    gaugeFixingTerm L n k U B = gaugeSliceResidual U B := by
  obtain ⟨T, hTv, hTK⟩ := hD 0 (Nat.zero_le k) U hU
  obtain ⟨R, hRv, hRK⟩ := hT.average_transpose
  have e1 : covDiffTranspose L n k U B =
      (covDiffRealTranspose L n k U B : Vertex L n k 0 → ComplexMatrix2) :=
    transposeOfValues_eq_realTransposeMap (S := pairedFunctions (Vertex L n k 0))
      (S' := edgePairedSpace L n k 0) hTv hTK B (mem_complexEdgeForms_of_mem B.2)
  have e2 : iterAdjointCubeAverage L n k U k
      (covDiffRealTranspose L n k U B : Vertex L n k 0 → ComplexMatrix2) =
      (iterAverageLinear L n k U (covDiffRealTranspose L n k U B) :
        Vertex L n k k → ComplexMatrix2) :=
    (linearMapWithValues_apply hA _).symm
  have e3 : ∀ g : vertexFunctionSpace L n k k, iterAverageTranspose L n k U g =
      (iterAverageRealTranspose L n k U g : Vertex L n k 0 → ComplexMatrix2) := fun g =>
    transposeOfValues_eq_realTransposeMap (S := pairedFunctions (Vertex L n k 0))
      (S' := pairedFunctions (Vertex L n k k)) hRv hRK g (fun x _ => (g.2 x (Set.mem_univ x)).2)
  unfold gaugeFixingTerm gaugeSliceResidual
  rw [e1, e2, e3]
  rfl
theorem traceFinsumPairing_self {ι : Type*} {g : ι → ComplexMatrix2}
    (hg : ∀ i, g i ∈ ComplexMatrix2.hermitianTraceless) :
    traceFinsumPairing g g = ((traceFinsumNorm g ^ 2 : ℝ) : ℂ) := by
  have hX : ∀ X ∈ ComplexMatrix2.hermitianTraceless,
      (ComplexMatrix2.halfTrace (X * X)).im = 0 ∧ 0 ≤ (ComplexMatrix2.halfTrace (X * X)).re := by
    intro X hX
    have h : ∀ i j, X j i = star (X i j) := fun i j => by
      conv_lhs => rw [hX.1]
      rfl
    have e : ComplexMatrix2.halfTrace (X * X) =
        ((((1 / 2 : ℝ) * ∑ i, ∑ j, Complex.normSq (X i j) : ℝ)) : ℂ) := by
      simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace, Matrix.diag,
        Matrix.mul_apply]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [h i j]
      exact Complex.mul_conj _
    rw [e]
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    have : 0 ≤ ∑ i, ∑ j, Complex.normSq (X i j) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (X i j)
    linarith
  have h : (traceFinsumPairing g g).im = 0 ∧ 0 ≤ (traceFinsumPairing g g).re := by
    unfold traceFinsumPairing
    refine finsum_induction (fun z : ℂ => z.im = 0 ∧ 0 ≤ z.re) (by simp) ?_ fun i => hX _ (hg i)
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by simp [ha, hb], by simpa using add_nonneg ha' hb'⟩
  unfold traceFinsumNorm
  rw [Real.sq_sqrt h.2]
  exact Complex.ext (by simp) (by simpa using h.1)
end Gauge
theorem statement_holds (hQ : RealQuadraticTransposes.Statement)
    (hM : RealLinearMaps.RealLinearMapsStatement) (hP : FaceTermDerivatives.Statement)
    (hS : FaceSums.FacesAndPairings) (hC : LeftChartFields.Claim) :
    Statement := by
  intro L hL k hk n hn
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  have hP' := ((hP L hL (i + 1) 0 (Nat.zero_le _)).1 n hn)
  have hfin : Finite (Face L n (i + 1) 0) := by
    have h := (((hS L hL (i + 1) 0 (Nat.zero_le _)).1 n hn).2.2.2 Set.univ).2.1
    exact Set.finite_univ_iff.mp h
  have hC' : (LeftChartFields.finiteData L n (i + 1) 0).LeftExpMulMemGroup :=
    ((hC.2.2 L (i + 1) 0 hL (Nat.zero_le _)).1 n hn).1.1
  obtain ⟨hD, hN⟩ := hQ L n (i + 1) hL hn hk
  have hA := ((hM L n (i + 1) hL hn hk).1 i (Nat.lt_succ_self i)).iterAdjointCubeAverage_isLinear
  unfold RescaledConditions.BackgroundFormMatchesHessian
  refine Filter.Eventually.mp (hN.and (hA.and self_mem_nhdsWithin)) ?_
  refine Filter.Eventually.of_forall ?_
  rintro U ⟨⟨-, hT, -⟩, hA', hU⟩ B
  have hg : ∀ x, (gaugeSliceResidual U B : Vertex L n (i + 1) 0 → ComplexMatrix2) x ∈
      ComplexMatrix2.hermitianTraceless := fun x =>
    (gaugeSliceResidual U B).2 x (Set.mem_univ x)
  have e0 : sourceQuadraticForm U 0 0 B = 0 := by
    simp [sourceQuadraticForm, edgeFormPairing, traceFinsumPairing, restrictToPositiveEdges,
      ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
  unfold backgroundForm backgroundHessianForm
  rw [e0, gaugeFixingTerm_eq_of_transposes hD hU hT hA' B, traceFinsumPairing_self hg,
    complexActionHessian_diag_eq_ofReal hP' hfin hC' hU B.2]
  push_cast
  ring
end YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide
end

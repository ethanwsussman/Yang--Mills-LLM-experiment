import YangMills.Construction.Towers.CriticalBranchAtTheBottomLevelProof
import YangMills.Construction.Towers.EntriesOfTheSaddleOperatorAreRealAnalyticNearOneProof
import YangMills.Construction.Towers.PairingOfTheRealTransposeOnForms
import YangMills.Construction.Towers.SurjectiveDifferentialsNearTheTrivialConfigurationProof
import YangMills.Construction.Towers.TheFormOnAFibreOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set Filter Asymptotics YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces YangMills.Construction.Matrices.PowerExpCharts
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
namespace FibreHessian
section Calculus
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']
theorem secondDeriv_comp {G : E → E'} {h : ℝ → E} (hG : ContDiffAt ℝ 2 G (h 0))
    (h1 : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ h t) (h2 : DifferentiableAt ℝ (deriv h) 0) :
    (∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ (G ∘ h) t) ∧
      HasDerivAt (deriv (G ∘ h))
        (fderiv ℝ (fderiv ℝ G) (h 0) (deriv h 0) (deriv h 0) +
          fderiv ℝ G (h 0) (deriv (deriv h) 0)) 0 := by
  have hc : ContinuousAt h 0 := h1.self_of_nhds.continuousAt
  have hGd : ∀ᶠ x in 𝓝 (h 0), DifferentiableAt ℝ G x :=
    (hG.eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ G (h t) := hc.eventually hGd
  refine ⟨(hev.and h1).mono fun t ht => ht.1.comp t ht.2, ?_⟩
  have hderiv : deriv (G ∘ h) =ᶠ[𝓝 0] fun t => fderiv ℝ G (h t) (deriv h t) :=
    (hev.and h1).mono fun t ht => (ht.1.hasFDerivAt.comp_hasDerivAt t ht.2.hasDerivAt).deriv
  have hfd : DifferentiableAt ℝ (fderiv ℝ G) (h 0) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcomp : HasDerivAt (fun t => fderiv ℝ G (h t)) (fderiv ℝ (fderiv ℝ G) (h 0) (deriv h 0)) 0 :=
    hfd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1.self_of_nhds.hasDerivAt
  exact (hcomp.clm_apply h2.hasDerivAt).congr_of_eventuallyEq hderiv
theorem isLittleO_taylor_two {x : ℝ → E} (h1 : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ x t)
    (h2 : DifferentiableAt ℝ (deriv x) 0) (h0 : x 0 = 0) :
    (fun t : ℝ => x t - t • deriv x 0 - (t ^ 2 / 2) • deriv (deriv x) 0) =o[𝓝 0]
      fun t : ℝ => t ^ 2 := by
  set a := deriv x 0 with ha
  set c := deriv (deriv x) 0 with hc
  let r : ℝ → E := fun t => x t - t • a - (t ^ 2 / 2) • c
  have hr : ∀ t, DifferentiableAt ℝ x t → HasDerivAt r (deriv x t - a - t • c) t := by
    intro t ht
    have e1 : HasDerivAt (fun s : ℝ => s • a) a t := by
      simpa using (hasDerivAt_id t).smul_const a
    have e0 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
      have := ((hasDerivAt_id t).pow 2).div_const 2
      simpa using this
    have e2 : HasDerivAt (fun s : ℝ => (s ^ 2 / 2) • c) (t • c) t := e0.smul_const c
    exact (ht.hasDerivAt.sub e1).sub e2
  have hlin : (fun t : ℝ => deriv x t - a - t • c) =o[𝓝 0] fun t : ℝ => t := by
    have := hasDerivAt_iff_isLittleO.1 h2.hasDerivAt
    simpa using this
  rw [isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (h1.and (hlin.def hε))
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
  have htδ : |t| < δ := by simpa using ht
  have hin : ∀ s ∈ Metric.closedBall (0 : ℝ) |t|, dist s 0 < δ := fun s hs =>
    lt_of_le_of_lt (Metric.mem_closedBall.1 hs) htδ
  have hs0 : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) |t| := by simp
  have hst : t ∈ Metric.closedBall (0 : ℝ) |t| := by simp
  have hmv := (convex_closedBall (0 : ℝ) |t|).norm_image_sub_le_of_norm_deriv_le (f := r)
    (C := ε * |t|) (fun s hs => (hr s (hball (hin s hs)).1).differentiableAt)
    (fun s hs => by
      rw [(hr s (hball (hin s hs)).1).deriv]
      refine (hball (hin s hs)).2.trans ?_
      have hs' : |s| ≤ |t| := by simpa using hs
      simpa using mul_le_mul_of_nonneg_left hs' hε.le) hs0 hst
  have hr0 : r 0 = 0 := by simp [r, h0]
  rw [hr0, sub_zero, sub_zero] at hmv
  calc ‖r t‖ ≤ ε * |t| * ‖t‖ := hmv
    _ = ε * ‖t ^ 2‖ := by rw [norm_pow, Real.norm_eq_abs]; ring
theorem line_derivs {ψ : E → ℝ} (hψ : ContDiffAt ℝ 2 ψ 0) (y : E) :
    HasDerivAt (fun u : ℝ => ψ (u • y)) (fderiv ℝ ψ 0 y) 0 ∧
      deriv (deriv fun u : ℝ => ψ (u • y)) 0 = fderiv ℝ (fderiv ℝ ψ) 0 y y := by
  let h : ℝ → E := fun u => u • y
  have hh : ∀ u, HasDerivAt h y u := fun u => by
    simpa using (hasDerivAt_id u).smul_const y
  have hd : deriv h = fun _ => y := funext fun u => (hh u).deriv
  have h0 : h 0 = 0 := by simp [h]
  have hψ2 : ContDiffAt ℝ 2 ψ (h 0) := by
    rw [h0]
    exact hψ
  have hψ1 : DifferentiableAt ℝ ψ (h 0) := hψ2.differentiableAt (by norm_num)
  obtain ⟨-, h2⟩ := secondDeriv_comp hψ2 (Filter.Eventually.of_forall fun u => (hh u).differentiableAt)
    (by rw [hd]; exact differentiableAt_const _)
  refine ⟨?_, ?_⟩
  · have := hψ1.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hh 0)
    rwa [h0] at this
  · have e : (fun u : ℝ => ψ (u • y)) = ψ ∘ h := rfl
    rw [e, h2.deriv, hd, h0]
    simp
end Calculus
section Expansion
variable {E F : Type*}
theorem eq_zero_of_half_sq_smul_isLittleO [NormedAddCommGroup F] [NormedSpace ℝ F] {D : F}
    (h : (fun t : ℝ => (t ^ 2 / 2) • D) =o[𝓝 0] fun t : ℝ => t ^ 2) : D = 0 := by
  by_contra hD
  have hpos : 0 < ‖D‖ := norm_pos_iff.2 hD
  have h1 := h.def (c := ‖D‖ / 4) (by positivity)
  have h2 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖(t ^ 2 / 2) • D‖ ≤ ‖D‖ / 4 * ‖t ^ 2‖ :=
    h1.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, ht0⟩ := (h2.and self_mem_nhdsWithin).exists
  have ht0' : t ≠ 0 := ht0
  have hsq : 0 < t ^ 2 := by positivity
  rw [norm_smul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hsq.le] at ht
  nlinarith [mul_pos hsq hpos]
theorem linear_add_quadratic_eq_zero [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : E →ₗ[ℝ] F) (β : E →ₗ[ℝ] E →ₗ[ℝ] F) {X : ℝ → E} {B ξ : E} {C : ℝ} (hB : l B = 0)
    (hrem : (fun t : ℝ => ‖X t - t • B - (t ^ 2 / 2) • ξ‖) =o[𝓝 0] fun t : ℝ => t ^ 2)
    (hC : ∀ᶠ t in 𝓝 (0 : ℝ), ‖l (X t) + (1 / 2 : ℝ) • β (X t) (X t)‖ ≤ C * ‖X t‖ ^ 3) :
    l ξ + β B B = 0 := by
  obtain ⟨S, hXS⟩ : ∃ S : ℝ → E, ∀ t, X t = t • B + S t :=
    ⟨fun t => X t - t • B, fun t => by simp⟩
  obtain ⟨R, hSR⟩ : ∃ R : ℝ → E, ∀ t, S t = (t ^ 2 / 2) • ξ + R t :=
    ⟨fun t => S t - (t ^ 2 / 2) • ξ, fun t => by simp⟩
  have hR : R =o[𝓝 0] fun t : ℝ => t ^ 2 := by
    refine IsLittleO.of_norm_left (hrem.congr_left fun t => ?_)
    rw [hXS t, hSR t]
    congr 1
    abel
  have hξ : (fun t : ℝ => (t ^ 2 / 2) • ξ) =O[𝓝 0] fun t : ℝ => t ^ 2 := by
    refine IsBigO.of_bound ‖ξ‖ (Eventually.of_forall fun t => ?_)
    rw [norm_smul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    nlinarith [norm_nonneg ξ, sq_nonneg t, mul_nonneg (norm_nonneg ξ) (sq_nonneg t)]
  have hS : S =O[𝓝 0] fun t : ℝ => t ^ 2 :=
    (hξ.add hR.isBigO).congr_left fun t => (hSR t).symm
  have hlin : (fun t : ℝ => t • B) =O[𝓝 0] fun t : ℝ => t := by
    refine IsBigO.of_bound ‖B‖ (Eventually.of_forall fun t => ?_)
    rw [norm_smul, mul_comm]
  have hsq : (fun t : ℝ => t ^ 2) =O[𝓝 0] fun t : ℝ => t :=
    (isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num)).isBigO
  have hX : X =O[𝓝 0] fun t : ℝ => t :=
    (hlin.add (hS.trans hsq)).congr_left fun t => (hXS t).symm
  let lc : E →L[ℝ] F := LinearMap.toContinuousLinearMap l
  let βc : E →L[ℝ] E →L[ℝ] F := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] F) ≃ₗ[ℝ] E →L[ℝ] F).toLinearMap ∘ₗ β)
  have hβ : ∀ x y, ‖β x y‖ ≤ ‖βc‖ * ‖x‖ * ‖y‖ := fun x y => βc.le_opNorm₂ x y
  have bil : ∀ {f g : ℝ → E} {u v : ℝ → ℝ}, f =O[𝓝 0] u → g =O[𝓝 0] v →
      (fun t => β (f t) (g t)) =O[𝓝 0] fun t => u t * v t := by
    intro f g u v hf hg
    refine IsBigO.trans (IsBigO.of_bound ‖βc‖ (Eventually.of_forall fun t => ?_))
      (hf.norm_left.mul hg.norm_left)
    rw [norm_mul, norm_norm, norm_norm, ← mul_assoc]
    exact hβ _ _
  have h3 : (fun t : ℝ => t ^ 3) =o[𝓝 0] fun t : ℝ => t ^ 2 :=
    isLittleO_pow_pow (by norm_num)
  have h4 : (fun t : ℝ => t ^ 4) =o[𝓝 0] fun t : ℝ => t ^ 2 :=
    isLittleO_pow_pow (by norm_num)
  have e1 : (fun t => β (t • B) (S t)) =o[𝓝 0] fun t : ℝ => t ^ 2 :=
    (bil hlin hS).trans_isLittleO (h3.congr_left fun t => by ring)
  have e2 : (fun t => β (S t) (t • B)) =o[𝓝 0] fun t : ℝ => t ^ 2 :=
    (bil hS hlin).trans_isLittleO (h3.congr_left fun t => by ring)
  have e3 : (fun t => β (S t) (S t)) =o[𝓝 0] fun t : ℝ => t ^ 2 :=
    (bil hS hS).trans_isLittleO (h4.congr_left fun t => by ring)
  have e4 : (fun t => l (R t)) =o[𝓝 0] fun t : ℝ => t ^ 2 :=
    (lc.isBigO_comp R (𝓝 0)).trans_isLittleO hR
  have e5 : (fun t => l (X t) + (1 / 2 : ℝ) • β (X t) (X t)) =o[𝓝 0] fun t : ℝ => t ^ 2 := by
    have hb : (fun t => l (X t) + (1 / 2 : ℝ) • β (X t) (X t)) =O[𝓝 0]
        fun t => ‖X t‖ ^ 3 := by
      refine IsBigO.of_bound |C| (hC.mono fun t h => h.trans ?_)
      rw [norm_pow, norm_norm]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    exact (hb.trans (hX.norm_left.pow 3)).trans_isLittleO h3
  refine eq_zero_of_half_sq_smul_isLittleO
    (((e5.sub e4).sub (((e1.add e2).add e3).const_smul_left (1 / 2 : ℝ))).congr_left fun t => ?_)
  have hlS : l (S t) = (t ^ 2 / 2) • l ξ + l (R t) := by rw [hSR t, map_add, map_smul]
  rw [hXS t]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Pi.smul_apply, hB, hlS]
  module
theorem linear_add_quadratic_eq_zero_of_core [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (core : InnerProductSpace.Core ℝ E)
    (N : E → ℝ) (hN : ∀ x, N x = Real.sqrt (core.inner x x))
    (l : E →ₗ[ℝ] F) (β : E →ₗ[ℝ] E →ₗ[ℝ] F) {X : ℝ → E} {B ξ : E} {C : ℝ} (hB : l B = 0)
    (hrem : (fun t : ℝ => N (X t - t • B - (t ^ 2 / 2) • ξ)) =o[𝓝 0] fun t : ℝ => t ^ 2)
    (hC : ∀ᶠ t in 𝓝 (0 : ℝ), ‖l (X t) + (1 / 2 : ℝ) • β (X t) (X t)‖ ≤ C * N (X t) ^ 3) :
    l ξ + β B B = 0 := by
  let _ : NormedAddCommGroup E := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ E := InnerProductSpace.ofCore core.toCore
  have hn : ∀ x, N x = ‖x‖ := fun x => by
    rw [hN x, norm_eq_sqrt_real_inner x]
  simp only [hn] at hrem hC
  exact linear_add_quadratic_eq_zero l β hB hrem hC
theorem exists_norm_bound_of_core [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] (core : InnerProductSpace.Core ℝ F) (N : F → ℝ)
    (hN : ∀ x, N x = Real.sqrt (core.inner x x)) (A : E →ₗ[ℝ] F) :
    ∃ K : ℝ, ∀ r, N (A r) ≤ K * ‖r‖ := by
  let _ : NormedAddCommGroup F := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ F := InnerProductSpace.ofCore core.toCore
  have hn : ∀ x, N x = ‖x‖ := fun x => by
    rw [hN x, norm_eq_sqrt_real_inner x]
  refine ⟨‖LinearMap.toContinuousLinearMap A‖, fun r => ?_⟩
  rw [hn]
  exact (LinearMap.toContinuousLinearMap A).le_opNorm r
theorem exists_inner_representative {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (c : InnerProductSpace.Core ℝ V) (l : V →ₗ[ℝ] ℝ) : ∃ g : V, ∀ v, c.inner g v = l v := by apply _root_.YangMills.Construction.Tower.BottomLevel.exists_inner_eq <;> assumption
end Expansion
section Edges
variable {L m k j i : ℕ}
theorem isPos_or_opposite_isPos (b : Edge L m k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem fieldOfPositiveValues_restrict {V : Edge L m k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L m k j) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
theorem nonempty_positiveEdge (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j ≤ k) :
    Nonempty (PositiveEdge L m k j) := by apply _root_.YangMills.SharedProofs.p12312 <;> assumption
theorem not_isPos_opposite (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j ≤ k) (b : Edge L m k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.NearIdentitySurjectivity.not_isPositivelyOriented_opposite <;> assumption
theorem exists_lieProjection :
    ∃ P : ComplexMatrix2 →L[ℝ] ComplexMatrix2.LieElement,
      ∀ Y : ComplexMatrix2.LieElement, P Y.toMatrix = Y := by apply _root_.YangMills.Construction.Matrices.specialUnitaryPower.Composition.exists_clm_leftInverse_toMatrix <;> assumption
theorem holomorphicScalar_of_coords {σ : Type} [Fintype σ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (σ ⊕ Empty → ComplexMatrix2)}
    {Φ : (σ ⊕ Empty → ComplexMatrix2) → Coordinates.ComplexCoordinates 1}
    (h : IsHolomorphicToCoords b (Equiv.refl _) W Φ) :
    HolomorphicScalar b W fun q => Φ q 0 := by apply _root_.YangMills.SharedProofs.p9409 <;> assumption
theorem edgeForm_pos (w : PositiveEdge L m k j → ComplexMatrix2) {b : Edge L m k j}
    (h : b.IsPositivelyOriented) : edgeFormOfPositiveValues w b = w ⟨b, h⟩ := by
  simp [edgeFormOfPositiveValues, h]
theorem edgeForm_opposite (w : PositiveEdge L m k j → ComplexMatrix2) {b : Edge L m k j}
    (h : ¬ b.IsPositivelyOriented) (h' : b.opposite.IsPositivelyOriented) :
    edgeFormOfPositiveValues w b = -w ⟨b.opposite, h'⟩ := by
  simp [edgeFormOfPositiveValues, h, h']
theorem edgeForm_mem
    (hnb : ∀ b : Edge L m k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    {w : PositiveEdge L m k j → ComplexMatrix2} (hw : ∀ b, w b ∈ ComplexMatrix2.hermitianTraceless) :
    edgeFormOfPositiveValues w ∈ edgeFormSpace L m k j := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [edgeForm_pos _ hb]
    exact hw _
  · by_cases h : b.IsPositivelyOriented
    · rw [edgeForm_pos _ h, edgeForm_opposite _ (hnb b h) h]
      rfl
    · have h' := (isPos_or_opposite_isPos b).resolve_left h
      rw [edgeForm_pos _ h', edgeForm_opposite _ h h', neg_neg]
def positiveValues (L m k j : ℕ) :
    edgeFormSpace L m k j →ₗ[ℝ] PositiveEdge L m k j → ComplexMatrix2.LieElement where
  toFun B b := (⟨(B : Edge L m k j → ComplexMatrix2) b.1, B.2.1 b.1 b.2⟩ :
    ComplexMatrix2.hermitianTraceless)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def formOfLieFamily
    (hnb : ∀ b : Edge L m k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented) :
    (PositiveEdge L m k j → ComplexMatrix2.LieElement) →ₗ[ℝ] edgeFormSpace L m k j where
  toFun y := ⟨edgeFormOfPositiveValues fun b => (y b).toMatrix, edgeForm_mem hnb fun b => (y b).2⟩
  map_add' y y' := by
    apply Subtype.ext
    funext b
    rcases em b.IsPositivelyOriented with h | h
    · simp only [Submodule.coe_add, Pi.add_apply, edgeForm_pos _ h]
      rfl
    · have h' := (isPos_or_opposite_isPos b).resolve_left h
      simp only [Submodule.coe_add, Pi.add_apply, edgeForm_opposite _ h h']
      rw [← neg_add]
      rfl
  map_smul' r y := by
    apply Subtype.ext
    funext b
    rcases em b.IsPositivelyOriented with h | h
    · simp only [Submodule.coe_smul, Pi.smul_apply, edgeForm_pos _ h, RingHom.id_apply]
      rfl
    · have h' := (isPos_or_opposite_isPos b).resolve_left h
      simp only [Submodule.coe_smul, Pi.smul_apply, edgeForm_opposite _ h h', RingHom.id_apply,
        smul_neg]
      rfl
theorem formOfLieFamily_positiveValues
    (hnb : ∀ b : Edge L m k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (B : edgeFormSpace L m k j) : formOfLieFamily hnb (positiveValues L m k j B) = B := by
  apply Subtype.ext
  funext b
  show edgeFormOfPositiveValues (fun c => (B : Edge L m k j → ComplexMatrix2) c.1) b = _
  rcases em b.IsPositivelyOriented with h | h
  · rw [edgeForm_pos _ h]
  · have h' := (isPos_or_opposite_isPos b).resolve_left h
    rw [edgeForm_opposite _ h h']
    have e := B.2.2 b
    rw [e, neg_neg]
theorem positiveValues_formOfLieFamily
    (hnb : ∀ b : Edge L m k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (y : PositiveEdge L m k j → ComplexMatrix2.LieElement) :
    positiveValues L m k j (formOfLieFamily hnb y) = y := by
  funext b
  apply Subtype.ext
  show edgeFormOfPositiveValues (fun c => (y c).toMatrix) b.1 = (y b).toMatrix
  rw [edgeForm_pos _ b.2]
theorem field_of_expChart
    (hnb : ∀ b : Edge L m k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (U : Edge L m k j → ComplexMatrix2) (y : PositiveEdge L m k j → ComplexMatrix2.LieElement) :
    fieldOfPositiveValues (fun b : PositiveEdge L m k j =>
        ComplexMatrix2.matExp (Complex.I • (y b).toMatrix) * U b.1) =
      PeriodicLattice.expTwist (formOfLieFamily hnb y : Edge L m k j → ComplexMatrix2) U := by
  funext b
  have hv : (formOfLieFamily hnb y : Edge L m k j → ComplexMatrix2) =
      edgeFormOfPositiveValues fun c => (y c).toMatrix := rfl
  rcases em b.IsPositivelyOriented with h | h
  · simp only [fieldOfPositiveValues, dif_pos h, PeriodicLattice.expTwist, if_pos h, hv,
      edgeForm_pos _ h]
  · have h' := (isPos_or_opposite_isPos b).resolve_left h
    simp only [fieldOfPositiveValues, dif_neg h, dif_pos h', PeriodicLattice.expTwist, if_neg h, hv,
      edgeForm_pos _ h']
theorem leftGradient_pairing (hF : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j ≤ k)
    {f : (Edge L m k j → ComplexMatrix2) → ℝ} {U : Edge L m k j → ComplexMatrix2}
    (l : edgeFormSpace L m k j →ₗ[ℝ] ℝ)
    (hl : ∀ B : edgeFormSpace L m k j, leftDeriv (fun V => (f V : ℂ)) U
      (B : Edge L m k j → ComplexMatrix2) = ((l B : ℝ) : ℂ)) (ξ : edgeFormSpace L m k j) :
    edgeFormPairing (leftGradient (fieldSpace L m k j) (fun V => (f V : ℂ)) U)
      (ξ : Edge L m k j → ComplexMatrix2) = ((l ξ : ℝ) : ℂ) := by
  obtain ⟨hfin, hfd, -, c, hc⟩ := hF L m k j hL hm hj
  obtain ⟨g, hg⟩ := exists_inner_representative c l
  have hex : ∃ X, IsLeftGradient (fieldSpace L m k j) (fun V => (f V : ℂ)) U X := by
    refine ⟨(g : Edge L m k j → ComplexMatrix2), ⟨fun b hb => (g.2.1 b hb).2, g.2.2⟩, fun _ => g.2,
      fun B hB _ => ?_⟩
    rw [hl ⟨B, hB⟩, ← hg, ← hc]
  have hspec := Classical.epsilon_spec hex
  have := hspec.2.2 ξ ξ.2 (Set.toFinite _)
  exact this.trans (hl ξ)
theorem leftSecondDeriv_eq_line {f : (Edge L m k j → ComplexMatrix2) → ℝ}
    {U B : Edge L m k j → ComplexMatrix2} :
    leftSecondDeriv f U B B =
      deriv (deriv fun u : ℝ => f (PeriodicLattice.expTwist (algebraMap ℝ ℂ u • B) U)) 0 := by
  have key : ∀ s : ℝ, deriv (fun t : ℝ => f (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B) U)) 0 =
      deriv (fun u : ℝ => f (PeriodicLattice.expTwist (algebraMap ℝ ℂ u • B) U)) s := by
    intro s
    have e : (fun t : ℝ => f (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B) U)) = fun t : ℝ =>
        (fun u : ℝ => f (PeriodicLattice.expTwist (algebraMap ℝ ℂ u • B) U)) (s + t) := by
      funext t
      simp only [map_add, add_smul]
    rw [e]
    exact (deriv_comp_const_add (fun u : ℝ => f (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ u • B) U)) s 0).trans (by rw [add_zero])
  exact congrArg (fun g : ℝ → ℝ => deriv g 0) (funext key)
theorem edgeFormNorm_eq_sqrt {c : InnerProductSpace.Core ℝ (edgeFormSpace L m k j)}
    (hc : ∀ B B' : edgeFormSpace L m k j, edgeFormPairing (B : Edge L m k j → ComplexMatrix2)
      (B' : Edge L m k j → ComplexMatrix2) = ((c.inner B B' : ℝ) : ℂ)) (A : edgeFormSpace L m k j) :
    edgeFormNorm (A : Edge L m k j → ComplexMatrix2) = Real.sqrt (c.inner A A) := by
  have h := hc A A
  unfold edgeFormNorm traceFinsumNorm
  unfold edgeFormPairing at h
  rw [h, Complex.ofReal_re]
theorem traceFinsumPairing_neg_right {ι : Type*} (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f (-g) = -traceFinsumPairing f g := by
  unfold traceFinsumPairing
  rw [← finsum_neg_distrib]
  refine finsum_congr fun i => ?_
  simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
theorem tendsto_prolong (hP : diffAtZeroPathsStatement)
    (hA : AnalyticMapsAlongCurves) (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    {b : CriticalBranchData L m k} (hb : b.IsCritical) (hi : i < k) :
    Tendsto (b.prolong i) (𝓝[fieldSpace L m k (i + 1)] trivialField L m k (i + 1))
      (𝓝[fieldSpace L m k i] trivialField L m k i) := by apply _root_.YangMills.Construction.Tower.SaddleAnalytic.tendsto_prolong <;> assumption
theorem second_deriv_along_curve (hC : ExpChartsStatement)
    (hE : BondSetFields.ProductStructureHolds)
    (hA : LeftChartFields.Claim)
    (hS : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j ≤ k)
    {𝒰 : Set (Edge L m k j → ComplexMatrix2)} {F : (Edge L m k j → ComplexMatrix2) → ℝ}
    (hF : IsAnalyticFieldFunction 𝒰 F) {U : Edge L m k j → ComplexMatrix2} (hU : U ∈ 𝒰)
    {I : Set ℝ} {γ : ℝ → Edge L m k j → ComplexMatrix2}
    (hγ : (fieldCurveData L m k j).IsTwiceDiffCurve I γ) (hγ0 : γ 0 = U)
    {B : edgeFormSpace L m k j} (hB : curveTangent γ = B) :
    ∃ (X : ℝ → edgeFormSpace L m k j) (ξ : edgeFormSpace L m k j),
      (∀ᶠ t in 𝓝 (0 : ℝ), γ t = PeriodicLattice.expTwist (X t : Edge L m k j → ComplexMatrix2) U) ∧
      Tendsto X (𝓝 0) (𝓝 0) ∧
      ((fun t : ℝ => edgeFormNorm ((X t - t • B - (t ^ 2 / 2) • ξ : edgeFormSpace L m k j) :
          Edge L m k j → ComplexMatrix2)) =o[𝓝 0] fun t : ℝ => t ^ 2) ∧
      deriv (deriv fun t => F (γ t)) 0 =
        leftSecondDeriv F U (B : Edge L m k j → ComplexMatrix2) B +
          (edgeFormPairing (leftGradient (fieldSpace L m k j) (fun V => (F V : ℂ)) U) ξ).re := by
  obtain ⟨hopen, f₁, hra⟩ := hF
  let := f₁
  have := nonempty_positiveEdge hE hL hm hj
  have hnb : ∀ b : Edge L m k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented :=
    not_isPos_opposite hE hL hm hj
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
  obtain ⟨hcharts, -, -, -, -, -, -, hread⟩ := hC (PositiveEdge L m k j) (PositiveEdge L m k j)
  have hO : specialUnitaryPower.IsOpenSubset (restrictToPositiveEdges '' 𝒰) := hopen.2
  have hconf : ∀ {V}, V ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges V) = V :=
    fun hV => fieldOfPositiveValues_restrict (hopen.1 hV)
  let f : (PositiveEdge L m k j → ComplexMatrix2) → ℝ := fun w => F (fieldOfPositiveValues w)
  have hrest : IsLocallyHolomorphicRestriction (HolomorphicScalar β) Complex.ofReal
      (restrictToPositiveEdges '' 𝒰) f := by
    rintro _ ⟨V, hV, rfl⟩
    have hq : asGroupFactors (restrictToPositiveEdges V) ∈
        {q : PositiveEdge L m k j ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
      show fieldOfPositiveValues (restrictToPositiveEdges V) ∈ 𝒰
      rw [hconf hV]
      exact hV
    obtain ⟨𝒳, hp𝒳, -, -, Φ, hΦ, heq⟩ := hra.2 _ hq
    refine ⟨𝒳, fun q => Φ q 0, hp𝒳, holomorphicScalar_of_coords (hΦ β), ?_⟩
    rintro _ ⟨U', hU', rfl⟩ hx
    have hval := heq ⟨hx, (Submodule.mem_bot ℝ).2 (funext fun e => e.elim),
      fun c => (hopen.1 hU').1 c (mem_univ _)⟩
    exact congrFun hval 0
  let p₀ : PositiveEdge L m k j → ComplexMatrix2 := restrictToPositiveEdges U
  obtain ⟨N, hN, -, hsm, -⟩ :=
    (((hread β).1 _ hO).1 f hrest).1.1 p₀ ⟨U, hU, rfl⟩
  have hp₀ : p₀ ∈ specialUnitaryPower (PositiveEdge L m k j) :=
    fun c => (hopen.1 hU).1 c (mem_univ _)
  obtain ⟨-, hform, hε⟩ := hcharts p₀ hp₀
  have hεpos : 0 < Real.log (19 / 10) := Real.log_pos (by norm_num)
  obtain ⟨-, ⟨Ω, hΩ, himg⟩, hp₀img, -, hlogopen, hlogsm, hsub, hleft, -⟩ :=
    hε _ hεpos (by rw [Real.exp_log (by norm_num)])
  obtain ⟨P, hP⟩ := exists_lieProjection
  let G₁ : (PositiveEdge L m k j → ComplexMatrix2) → PositiveEdge L m k j → ComplexMatrix2.LieElement :=
    fun Z s => P (logChart p₀ Z s)
  have hz : (0 : ComplexMatrix2.LieElement).toMatrix = 0 := rfl
  have hchart0 : expChartI p₀ 0 = p₀ := by
    rw [(hform 0).2.1]
    funext s
    simp [hz]
  have h0small : (0 : PositiveEdge L m k j → ComplexMatrix2.LieElement) ∈
      smallBall (PositiveEdge L m k j) (Real.log (19 / 10)) := by
    intro s
    simpa [hz] using hεpos
  have hG₁0 : G₁ p₀ = 0 := by
    funext s
    have hl := congrFun (hleft 0 h0small) s
    rw [hchart0] at hl
    show P (logChart p₀ p₀ s) = 0
    rw [hl]
    exact hP 0
  have hG₁ : ContDiffAt ℝ 2 G₁ p₀ := by
    have hl : ContDiffAt ℝ 2 (logChart p₀) p₀ :=
      (hlogsm.contDiffAt (hlogopen.mem_nhds (hsub hp₀img))).of_le ENat.LEInfty.out
    exact contDiffAt_pi.2 fun s => P.contDiff.contDiffAt.comp p₀ (contDiffAt_pi.1 hl s)
  let ψ : (PositiveEdge L m k j → ComplexMatrix2.LieElement) → ℝ := f ∘ expChartI p₀
  have hψ : ContDiffAt ℝ 2 ψ 0 := (hsm.contDiffAt hN).of_le ENat.LEInfty.out
  have hψv : ∀ y, ψ y =
      F (PeriodicLattice.expTwist (formOfLieFamily hnb y : Edge L m k j → ComplexMatrix2) U) := by
    intro y
    show F (fieldOfPositiveValues (expChartI p₀ y)) = _
    rw [(hform y).2.1]
    exact congrArg F (field_of_expChart hnb U y)
  let c : ℝ → PositiveEdge L m k j → ComplexMatrix2 := fun t => restrictToPositiveEdges (γ t)
  have hc0 : c 0 = p₀ := by
    show restrictToPositiveEdges (γ 0) = restrictToPositiveEdges U
    rw [hγ0]
  obtain ⟨⟨hI, hmaps, hd⟩, hdd⟩ := hγ
  have hI0 : I ∈ 𝓝 (0 : ℝ) := hI.1.mem_nhds hI.2.2
  have hc1 : ∀ t ∈ I, DifferentiableAt ℝ c t := fun t ht =>
    differentiableAt_pi.2 fun b => (hd b.1 b.2 t ht).differentiableAt (hI.1.mem_nhds ht)
  have hcd : ∀ t ∈ I, deriv c t = fun b => deriv (fun s => γ s b.1) t := fun t ht =>
    deriv_pi fun b => (hd b.1 b.2 t ht).differentiableAt (hI.1.mem_nhds ht)
  have hc2 : DifferentiableAt ℝ (deriv c) 0 := by
    have hb : DifferentiableAt ℝ (fun t (b : PositiveEdge L m k j) =>
        deriv (fun s => γ s b.1) t) 0 :=
      differentiableAt_pi.2 fun b => (hdd b.1 b.2 0 hI.2.2).differentiableAt hI0
    exact hb.congr_of_eventuallyEq (Filter.eventually_of_mem hI0 hcd)
  obtain ⟨hx1, hx2'⟩ := secondDeriv_comp (G := G₁) (h := c) (by rw [hc0]; exact hG₁)
    (Filter.eventually_of_mem hI0 hc1) hc2
  let x : ℝ → PositiveEdge L m k j → ComplexMatrix2.LieElement := G₁ ∘ c
  have hx2 : DifferentiableAt ℝ (deriv x) 0 := hx2'.differentiableAt
  have hx0 : x 0 = 0 := by
    show G₁ (c 0) = 0
    rw [hc0]
    exact hG₁0
  have hreading : ∀ᶠ t in 𝓝 (0 : ℝ), c t = expChartI p₀ (x t) ∧
      (∀ s, (x t s).toMatrix = logChart p₀ (c t) s) ∧ t ∈ I := by
    have hp₀Ω : p₀ ∈ Ω := (himg ▸ hp₀img : p₀ ∈ Ω ∩ _).1
    have hcΩ : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ Ω :=
      (hc1 0 hI.2.2).continuousAt.eventually (hΩ.mem_nhds (by rwa [hc0]))
    filter_upwards [hcΩ, hI0] with t ht htI
    have hcG : c t ∈ specialUnitaryPower (PositiveEdge L m k j) :=
      fun b => (hmaps htI).1 b (mem_univ _)
    have hmem : c t ∈ expChartI p₀ '' smallBall (PositiveEdge L m k j) (Real.log (19 / 10)) := by
      rw [himg]
      exact ⟨ht, hcG⟩
    obtain ⟨Y, hY, hYc⟩ := hmem
    have hxY : x t = Y := by
      funext s
      show P (logChart p₀ (c t) s) = Y s
      rw [← hYc, hleft Y hY]
      exact hP (Y s)
    refine ⟨by rw [hxY, hYc], fun s => ?_, htI⟩
    rw [hxY, ← hYc, hleft Y hY]
  have hX : ∀ᶠ t in 𝓝 (0 : ℝ), γ t =
      PeriodicLattice.expTwist (formOfLieFamily hnb (x t) : Edge L m k j → ComplexMatrix2) U := by
    filter_upwards [hreading] with t ht
    have h1 := field_of_expChart hnb U (x t)
    have h2 : fieldOfPositiveValues (expChartI p₀ (x t)) = fieldOfPositiveValues
        (fun b : PositiveEdge L m k j =>
          ComplexMatrix2.matExp (Complex.I • (x t b).toMatrix) * U b.1) := by
      rw [(hform (x t)).2.1]
      rfl
    rw [← h1, ← h2, ← ht.1]
    exact (fieldOfPositiveValues_restrict (hmaps ht.2.2)).symm
  have hdx : deriv x 0 = positiveValues L m k j B := by
    funext b
    have hxb : HasDerivAt (fun t => x t b) (deriv x 0 b) 0 :=
      (hasDerivAt_pi.1 hx1.self_of_nhds.hasDerivAt) b
    let mc : ComplexMatrix2.LieElement →L[ℝ] ComplexMatrix2 :=
      LinearMap.toContinuousLinearMap
        (ComplexMatrix2.hermitianTraceless.subtype : ComplexMatrix2.LieElement →ₗ[ℝ] ComplexMatrix2)
    have e1 : HasDerivAt (fun t => mc (x t b)) (mc (deriv x 0 b)) 0 :=
      mc.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hxb
    have hW := (hA.1 I hI).1 (fun t => γ t b.1) (fun t ht => (hmaps ht).1 b.1 (mem_univ _))
      ((hd b.1 b.2 0 hI.2.2).differentiableAt hI0)
    obtain ⟨-, hW1, hW2, -⟩ := hW
    simp only [hγ0] at hW1 hW2
    have hder : HasDerivAt
        (fun t => (1 / Complex.I) • ComplexMatrix2.logSeries (γ t b.1 * (U b.1)⁻¹))
        ((1 / Complex.I) • deriv (fun t => ComplexMatrix2.logSeries (γ t b.1 * (U b.1)⁻¹)) 0) 0 :=
      hW1.hasDerivAt.const_smul (1 / Complex.I)
    have e2 : (fun t => mc (x t b)) =ᶠ[𝓝 0]
        fun t => (1 / Complex.I) • ComplexMatrix2.logSeries (γ t b.1 * (U b.1)⁻¹) :=
      hreading.mono fun t ht => ht.2.1 b
    have e3 := e1.unique (hder.congr_of_eventuallyEq e2)
    rw [one_div, hW2] at e3
    have hval := congrFun hB b.1
    simp only [curveTangent, extendOddly, if_pos b.2, hγ0] at hval
    apply Subtype.ext
    exact e3.trans hval
  let ξ : edgeFormSpace L m k j := formOfLieFamily hnb (deriv (deriv x) 0)
  obtain ⟨hfinb, hfd, -, core, hcore⟩ := hS L m k j hL hm hj
  have hxc : Tendsto x (𝓝 0) (𝓝 0) := by
    have h : ContinuousAt x 0 := hx1.self_of_nhds.continuousAt
    have := h.tendsto
    rwa [hx0] at this
  refine ⟨fun t => formOfLieFamily hnb (x t), ξ, hX, ?_, ?_, ?_⟩
  · have hcomp : ∀ s : PositiveEdge L m k j,
        Tendsto (fun t => (x t s).toMatrix) (𝓝 0) (𝓝 0) := by
      intro s
      let mc : ComplexMatrix2.LieElement →L[ℝ] ComplexMatrix2 :=
        LinearMap.toContinuousLinearMap
          (ComplexMatrix2.hermitianTraceless.subtype : ComplexMatrix2.LieElement →ₗ[ℝ] ComplexMatrix2)
      have h1 : Tendsto (fun t => x t s) (𝓝 0) (𝓝 0) := tendsto_pi_nhds.1 hxc s
      have h2 : Tendsto (fun t => mc (x t s)) (𝓝 0) (𝓝 (mc 0)) :=
        (mc.continuous.tendsto 0).comp h1
      rw [map_zero] at h2
      exact h2
    rw [tendsto_subtype_rng]
    refine tendsto_pi_nhds.2 fun b => ?_
    show Tendsto (fun t => edgeFormOfPositiveValues (fun s => (x t s).toMatrix) b) (𝓝 0) (𝓝 0)
    rcases em b.IsPositivelyOriented with h | h
    · simp only [edgeForm_pos _ h]
      exact hcomp ⟨b, h⟩
    · have h' := (isPos_or_opposite_isPos b).resolve_left h
      simp only [edgeForm_opposite _ h h']
      simpa using (hcomp ⟨b.opposite, h'⟩).neg
  · obtain ⟨K, hK⟩ := exists_norm_bound_of_core core
      (fun A : edgeFormSpace L m k j => edgeFormNorm (A : Edge L m k j → ComplexMatrix2))
      (edgeFormNorm_eq_sqrt hcore) (formOfLieFamily hnb)
    have hr := isLittleO_taylor_two hx1 hx2 hx0
    refine (IsBigO.of_bound |K| (Filter.Eventually.of_forall fun t => ?_)).trans_isLittleO hr
    have e : formOfLieFamily hnb (x t) - t • B - (t ^ 2 / 2) • ξ =
        formOfLieFamily hnb (x t - t • deriv x 0 - (t ^ 2 / 2) • deriv (deriv x) 0) := by
      rw [map_sub, map_sub, map_smul, map_smul, hdx, formOfLieFamily_positiveValues]
    rw [e]
    have h0 : 0 ≤ edgeFormNorm ((formOfLieFamily hnb (x t - t • deriv x 0 -
        (t ^ 2 / 2) • deriv (deriv x) 0) : edgeFormSpace L m k j) : Edge L m k j → ComplexMatrix2) :=
      Real.sqrt_nonneg _
    rw [Real.norm_of_nonneg h0]
    exact (hK _).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _))
  · have hnear : (fun t => F (γ t)) =ᶠ[𝓝 0] ψ ∘ x :=
      hX.mono fun t ht => by
        show F (γ t) = ψ (x t)
        rw [hψv, ht]
    obtain ⟨-, h2⟩ := secondDeriv_comp (G := ψ) (h := x) (by rw [hx0]; exact hψ) hx1 hx2
    have hφ : ∀ (B' : edgeFormSpace L m k j) (u : ℝ), F (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ u • (B' : Edge L m k j → ComplexMatrix2)) U) =
        ψ (u • positiveValues L m k j B') := by
      intro B' u
      rw [hψv, map_smul, formOfLieFamily_positiveValues]
      congr 2
    let l : edgeFormSpace L m k j →ₗ[ℝ] ℝ :=
      (fderiv ℝ ψ 0).toLinearMap ∘ₗ positiveValues L m k j
    have hl : ∀ B' : edgeFormSpace L m k j, leftDeriv (fun V => (F V : ℂ)) U
        (B' : Edge L m k j → ComplexMatrix2) = ((l B' : ℝ) : ℂ) := by
      intro B'
      have h3 := ((line_derivs hψ (positiveValues L m k j B')).1).ofReal_comp
      show deriv (fun t : ℝ => ((F (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ t • (B' : Edge L m k j → ComplexMatrix2)) U) : ℝ) : ℂ)) 0 = _
      simp only [hφ]
      exact h3.deriv
    have hg := leftGradient_pairing hS hL hm hj l hl ξ
    have hsd : leftSecondDeriv F U (B : Edge L m k j → ComplexMatrix2) B =
        fderiv ℝ (fderiv ℝ ψ) 0 (positiveValues L m k j B) (positiveValues L m k j B) := by
      rw [leftSecondDeriv_eq_line, ← (line_derivs hψ (positiveValues L m k j B)).2]
      exact congrArg (fun g : ℝ → ℝ => deriv (deriv g) 0) (funext (hφ B))
    have hlξ : l ξ = fderiv ℝ ψ 0 (deriv (deriv x) 0) := by
      show fderiv ℝ ψ 0 (positiveValues L m k j (formOfLieFamily hnb (deriv (deriv x) 0))) = _
      rw [positiveValues_formOfLieFamily]
    rw [hnear.deriv.deriv_eq, h2.deriv, hx0, hdx, hsd, hg, Complex.ofReal_re, hlξ]
end Edges
end FibreHessian
open FibreHessian in
theorem fibreHessianViaQuadraticExpansion_holds
    (hT : LeftChartStepExpansion)
    (hForm : CriticalFibreHessianPosDef)
    (hGrad : GaugeFixedGradientOnFibre)
    (hFix : ChosenBranchIsCritical)
    (hC : ExpChartsStatement)
    (hE : BondSetFields.ProductStructureHolds)
    (hA : LeftChartFields.Claim)
    (hS : FiniteSideFormSpaces)
    (hP : diffAtZeroPathsStatement)
    (hRA : AnalyticMapsAlongCurves)
    (hPair : RealTransposeEdgeFormPairing) :
    FibreHessianViaQuadraticExpansion := by
  intro L m k hL hm i hi
  have hik : i < k := hi
  obtain ⟨hb, hUall⟩ := hFix L m k hL hm
  have hU := hUall i hik
  have hlim := tendsto_prolong hP hRA hL hm hb hik
  have htv := hT L m k i hL hm hi
  have hform := hForm L m k hL hm i hi
  have hgrad := hGrad L m k hL hm i hi
  unfold EventuallyNearIdentity at htv hform hgrad ⊢
  filter_upwards [hform, hgrad, hlim.eventually htv, self_mem_nhdsWithin] with W hF hG hV hWc
  obtain ⟨hcrit, -, hH, hcurves, -⟩ := hF
  obtain ⟨g, hg, hgt⟩ := hG
  obtain ⟨-, hD, hQ⟩ := hV
  refine ⟨hQ.1.exists, fun q hq B => ?_⟩
  have hspec : ∀ A : edgeFormSpace L m k i,
      (constraintDifferential L m k i W A : Edge L m k (i + 1) → ComplexMatrix2) =
      leftDifferential (smoothingStep L m k i) (chosenProlong L m k i W) A :=
    Classical.epsilon_spec hD.2.1
  obtain ⟨I, γ, hγ, hγN, hγ0, hγt⟩ := hcurves B
  obtain ⟨X, ξ, hX, hX0, ho, hval⟩ := second_deriv_along_curve (F := chosenGaugeFixedEnergy L m k i)
    hC hE hA hS hL hm hik.le hU.analytic_gaugeFixedEnergy hcrit.1.1 hγ hγ0 (B := B.1) hγt
  have hH' := hH I γ B hγ hγN hγ0 hγt
  have hI0 : I ∈ 𝓝 (0 : ℝ) := hγ.1.1.1.mem_nhds hγ.1.1.2.2
  obtain ⟨-, hfd, -, core, hcore⟩ := hS L m k i hL hm hik.le
  have hN := edgeFormNorm_eq_sqrt hcore
  have hlog1 : ComplexMatrix2.logSeries 1 = 0 := by simp [ComplexMatrix2.logSeries]
  have hrel : ∀ c : PositiveEdge L m k (i + 1),
      (constraintDifferential L m k i W ξ : Edge L m k (i + 1) → ComplexMatrix2) c =
        -q B.1 B.1 c := by
    intro c
    obtain ⟨Cq, hCq⟩ := hq.2 c
    have hWinv : W (c : Edge L m k (i + 1)) * (W (c : Edge L m k (i + 1)))⁻¹ = 1 := by
      have hu : W (c : Edge L m k (i + 1)) ∈ PeriodicLattice.compactGaugeGroup :=
        hWc.1 _ (Set.mem_univ _)
      have : IsUnit (W (c : Edge L m k (i + 1))).det := by
        have := hu.2
        simp_all
      exact Matrix.mul_nonsing_inv _ this
    have hvanish : ∀ᶠ t in 𝓝 (0 : ℝ), stepLog (chosenProlong L m k i W) c
        (X t : Edge L m k i → ComplexMatrix2) = 0 := by
      filter_upwards [hX, hI0] with t e ht
      unfold stepLog
      rw [← e, (hγN ht).2, hcrit.1.2, hWinv, hlog1, smul_zero]
    let l : edgeFormSpace L m k i →ₗ[ℝ] ComplexMatrix2 :=
      (LinearMap.proj (c : Edge L m k (i + 1))) ∘ₗ
        (edgeFormSpace L m k (i + 1)).subtype ∘ₗ constraintDifferential L m k i W
    let β : edgeFormSpace L m k i →ₗ[ℝ] edgeFormSpace L m k i →ₗ[ℝ] ComplexMatrix2 :=
      q.compr₂ (LinearMap.proj c)
    have hl : ∀ A : edgeFormSpace L m k i, l A =
        leftDifferential (smoothingStep L m k i) (chosenProlong L m k i W)
          (A : Edge L m k i → ComplexMatrix2) c := fun A => congrFun (hspec A) c
    have hr := linear_add_quadratic_eq_zero_of_core core
      (fun A : edgeFormSpace L m k i => edgeFormNorm (A : Edge L m k i → ComplexMatrix2)) hN l β
      (X := X) (B := B.1) (ξ := ξ) (C := Cq)
      (by
        show (constraintDifferential L m k i W B.1 : Edge L m k (i + 1) → ComplexMatrix2) c = 0
        rw [LinearMap.mem_ker.1 B.2]
        rfl) ho (by
        filter_upwards [hX0.eventually hCq, hvanish] with t ht hv
        rw [hv] at ht
        refine le_trans (le_of_eq ?_) ht
        rw [hl]
        rw [← norm_neg]
        congr 1
        show _ = _
        simp only [β, LinearMap.compr₂_apply, LinearMap.proj_apply]
        abel)
    exact eq_neg_of_add_eq_zero_left hr
  have hpos : restrictToPositiveEdges
      (constraintDifferential L m k i W ξ : Edge L m k (i + 1) → ComplexMatrix2) =
      -q B.1 B.1 := funext hrel
  have e := hPair L m k i (i + 1) hL hm hik.le hi (constraintDifferential L m k i W) g ξ
  rw [hgt] at e
  have e' : edgeFormPairing (leftGradient (fieldSpace L m k i)
      (fun V => (chosenGaugeFixedEnergy L m k i V : ℂ)) (chosenProlong L m k i W))
      (ξ : Edge L m k i → ComplexMatrix2) =
      -traceFinsumPairing
        (restrictToPositiveEdges ((chosenCriticalBranch L m k).energyGradient (i + 1) W))
        (q B.1 B.1) := by
    rw [e, ← hg]
    show traceFinsumPairing _ (restrictToPositiveEdges
      (constraintDifferential L m k i W ξ : Edge L m k (i + 1) → ComplexMatrix2)) = _
    rw [hpos, traceFinsumPairing_neg_right]
  rw [hH', hval, e', Complex.neg_re, sub_eq_add_neg]
end YangMills.Construction.Tower
end

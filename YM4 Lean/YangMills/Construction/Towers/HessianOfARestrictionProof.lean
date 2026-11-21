import YangMills.Construction.Towers.AveragingIsAnalyticAndCovariantOnTheSidesProof
import YangMills.Construction.Towers.HessianOfARestriction
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace YangMills.Construction
namespace Tower.RestrictionHessian
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
theorem deriv_comp_curve {f : P → ℝ} {c : ℝ → P} (hf : DifferentiableAt ℝ f (c 0))
    (hc : DifferentiableAt ℝ c 0) : deriv (f ∘ c) 0 = fderiv ℝ f (c 0) (deriv c 0) :=
  fderiv_comp_deriv 0 hf hc
theorem deriv_deriv_comp_curve {f : P → ℝ} {x : P} (hf : ContDiffAt ℝ 2 f x)
    (hx : fderiv ℝ f x = 0) {c : ℝ → P} (hc0 : c 0 = x)
    (hc : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ c t)
    (hc2 : DifferentiableAt ℝ (deriv c) 0) :
    deriv (deriv (f ∘ c)) 0 = fderiv ℝ (fderiv ℝ f) x (deriv c 0) (deriv c 0) := by
  have hcd : DifferentiableAt ℝ c 0 := hc.self_of_nhds
  have hlim : Tendsto c (𝓝 0) (𝓝 x) := by
    have := hcd.continuousAt.tendsto
    rwa [hc0] at this
  have hfd : ∀ᶠ p in 𝓝 x, DifferentiableAt ℝ f p := by
    have := hf.eventually (by simp)
    exact this.mono fun p hp => hp.differentiableAt (by norm_num)
  have hev : deriv (f ∘ c) =ᶠ[𝓝 0] fun t => fderiv ℝ f (c t) (deriv c t) := by
    filter_upwards [hc, hlim.eventually hfd] with t ht hft
    exact fderiv_comp_deriv t hft ht
  rw [hev.deriv_eq]
  have hf2 : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : HasDerivAt (fun t => fderiv ℝ f (c t))
      (fderiv ℝ (fderiv ℝ f) x (deriv c 0)) 0 := by
    have h := hf2.hasFDerivAt
    rw [← hc0] at h
    have h' := h.comp_hasDerivAt (0 : ℝ) hcd.hasDerivAt
    rw [hc0] at h'
    exact h'
  have h2 := h1.clm_apply hc2.hasDerivAt
  rw [h2.deriv, hc0, hx]
  simp
end Tower.RestrictionHessian
namespace Geometry.CurveData
variable {X T : Type} [AddCommGroup T] [Module ℝ T] (R : CurveData X T)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
structure ParametrizationData (N : Set X) (F : X → ℝ) (φ : P → X) (z : P) (D : P →ₗ[ℝ] T) :
    Prop where
  injective : Function.Injective D
  mem : φ z ∈ N
  contDiffAt : ContDiffAt ℝ 2 (F ∘ φ) z
  liftCurve : ∀ (I : Set ℝ) (γ : ℝ → X), R.IsCurve I γ → MapsTo γ I N → γ 0 = φ z →
    ∃ c : ℝ → P, c 0 = z ∧ DifferentiableAt ℝ c 0 ∧ (∀ᶠ t in 𝓝 (0 : ℝ), F (γ t) = F (φ (c t))) ∧
      R.tangent γ = D (deriv c 0)
  liftCurve₂ : ∀ (I : Set ℝ) (γ : ℝ → X), R.IsTwiceDiffCurve I γ → MapsTo γ I N →
    γ 0 = φ z → ∃ c : ℝ → P, c 0 = z ∧ (∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ c t) ∧
      DifferentiableAt ℝ (deriv c) 0 ∧ (∀ᶠ t in 𝓝 (0 : ℝ), F (γ t) = F (φ (c t))) ∧
      R.tangent γ = D (deriv c 0)
  line : ∀ h : P, ∃ I : Set ℝ, R.IsCurve I (fun t : ℝ => φ (z + t • h)) ∧
    R.IsTwiceDiffCurve I (fun t : ℝ => φ (z + t • h)) ∧
    MapsTo (fun t : ℝ => φ (z + t • h)) I N ∧ R.tangent (fun t : ℝ => φ (z + t • h)) = D h
variable {R} {N : Set X} {F : X → ℝ} {φ : P → X} {z : P} {D : P →ₗ[ℝ] T}
theorem ParametrizationData.differentiableAt (H : R.ParametrizationData N F φ z D) :
    DifferentiableAt ℝ (F ∘ φ) z :=
  H.contDiffAt.differentiableAt (by norm_num)
theorem ParametrizationData.range_eq (H : R.ParametrizationData N F φ z D) :
    LinearMap.range D = R.tangentSpan N (φ z) := by
  apply le_antisymm
  · rintro _ ⟨h, rfl⟩
    obtain ⟨I, hI, -, hm, ht⟩ := H.line h
    exact Submodule.subset_span ⟨I, _, hI, hm, by simp, ht⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨I, γ, hγ, hm, h0, rfl⟩
    obtain ⟨c, -, -, -, ht⟩ := H.liftCurve I γ hγ hm h0
    exact ⟨deriv c 0, ht.symm⟩
theorem ParametrizationData.isCriticalOn_iff (H : R.ParametrizationData N F φ z D) :
    R.IsCriticalOn N F (φ z) ↔ fderiv ℝ (F ∘ φ) z = 0 := by
  constructor
  · rintro ⟨-, hc⟩
    ext h
    obtain ⟨I, hI, -, hm, -⟩ := H.line h
    have h1 := hc I _ hI hm (by simp)
    have hl : HasDerivAt (fun t : ℝ => z + t • h) h 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add z
    have h2 : HasDerivAt (fun t : ℝ => (F ∘ φ) (z + t • h)) (fderiv ℝ (F ∘ φ) z h) 0 := by
      have hd := H.differentiableAt.hasFDerivAt
      have hd' : HasFDerivAt (F ∘ φ) (fderiv ℝ (F ∘ φ) z) (z + (0 : ℝ) • h) := by simpa using hd
      exact hd'.comp_hasDerivAt (0 : ℝ) hl
    have h3 : deriv (fun t : ℝ => F (φ (z + t • h))) 0 = fderiv ℝ (F ∘ φ) z h := h2.deriv
    simpa [h3] using h1
  · intro h0
    refine ⟨H.mem, fun I γ hγ hm hz => ?_⟩
    obtain ⟨c, c0, hc, hev, -⟩ := H.liftCurve I γ hγ hm hz
    have h1 : (fun t => F (γ t)) =ᶠ[𝓝 0] (F ∘ φ) ∘ c := hev
    rw [h1.deriv_eq,
      Tower.RestrictionHessian.deriv_comp_curve (by rw [c0]; exact H.differentiableAt) hc,
      c0, h0]
    simp
theorem ParametrizationData.secondDeriv_eq (H : R.ParametrizationData N F φ z D)
    (hcr : R.IsCriticalOn N F (φ z)) (I : Set ℝ) (γ : ℝ → X) (h : P)
    (hγ : R.IsTwiceDiffCurve I γ) (hm : MapsTo γ I N) (h0 : γ 0 = φ z)
    (ht : R.tangent γ = D h) :
    deriv (deriv fun t => F (γ t)) 0 = fderiv ℝ (fderiv ℝ (F ∘ φ)) z h h := by
  obtain ⟨c, c0, hc, hc2, hev, htc⟩ := H.liftCurve₂ I γ hγ hm h0
  have hh : deriv c 0 = h := H.injective (htc.symm.trans ht)
  have h1 : (fun t => F (γ t)) =ᶠ[𝓝 0] (F ∘ φ) ∘ c := hev
  rw [h1.deriv.deriv_eq,
    Tower.RestrictionHessian.deriv_deriv_comp_curve H.contDiffAt (H.isCriticalOn_iff.1 hcr) c0
      hc hc2,
    hh]
theorem ParametrizationData.exists_curve (H : R.ParametrizationData N F φ z D)
    (v : T) (hv : v ∈ R.tangentSpan N (φ z)) :
    ∃ (I : Set ℝ) (γ : ℝ → X), R.IsTwiceDiffCurve I γ ∧ MapsTo γ I N ∧ γ 0 = φ z ∧
      R.tangent γ = v := by
  rw [← H.range_eq] at hv
  obtain ⟨h, rfl⟩ := hv
  obtain ⟨I, -, hI, hm, ht⟩ := H.line h
  exact ⟨I, _, hI, hm, by simp, ht⟩
theorem ParametrizationData.exists_quadraticForm (H : R.ParametrizationData N F φ z D) :
    ∃ Q : QuadraticForm ℝ (R.tangentSpan N (φ z)), ∀ (h : P) (v : R.tangentSpan N (φ z)),
      (v : T) = D h → Q v = fderiv ℝ (fderiv ℝ (F ∘ φ)) z h h := by
  have hr := H.range_eq
  let e : R.tangentSpan N (φ z) →ₗ[ℝ] P :=
    (LinearEquiv.ofInjective D H.injective).symm.toLinearMap ∘ₗ
      (LinearEquiv.ofEq _ _ hr.symm).toLinearMap
  have he : ∀ v : R.tangentSpan N (φ z), D (e v) = v := by
    intro v
    have := (LinearEquiv.ofInjective D H.injective).apply_symm_apply
      (LinearEquiv.ofEq _ _ hr.symm v)
    simp [e]
  let A := fderiv ℝ (fderiv ℝ (F ∘ φ)) z
  let B : P →ₗ[ℝ] P →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun a b => A a b) (by simp) (by simp) (by simp)
    (by simp)
  refine ⟨LinearMap.BilinMap.toQuadraticMap (B.compl₁₂ e e), fun h v hv => ?_⟩
  have : e v = h := H.injective ((he v).trans hv)
  simp [B, this, A]
theorem ParametrizationData.isHessianFormAt_of (H : R.ParametrizationData N F φ z D)
    (hcr : R.IsCriticalOn N F (φ z)) (Q : R.tangentSpan N (φ z) → ℝ)
    (hQ : ∀ (h : P) (v : R.tangentSpan N (φ z)), (v : T) = D h →
      Q v = fderiv ℝ (fderiv ℝ (F ∘ φ)) z h h) :
    R.IsHessianFormAt Subtype.val N F (φ z) Q := by
  intro I γ v hγ hm h0 ht
  have hv : (v : T) ∈ LinearMap.range D := by
    rw [H.range_eq]
    exact v.2
  obtain ⟨h, hh⟩ := hv
  rw [hQ h v hh.symm, H.secondDeriv_eq hcr I γ h hγ hm h0 (ht.trans hh.symm)]
theorem ParametrizationData.eq_of_isHessianFormAt (H : R.ParametrizationData N F φ z D)
    (Q Q' : R.tangentSpan N (φ z) → ℝ)
    (hQ : R.IsHessianFormAt Subtype.val N F (φ z) Q)
    (hQ' : R.IsHessianFormAt Subtype.val N F (φ z) Q') :
    Q = Q' := by
  funext v
  obtain ⟨I, γ, hγ, hm, h0, ht⟩ := H.exists_curve v v.2
  rw [hQ I γ v hγ hm h0 ht, hQ' I γ v hγ hm h0 ht]
theorem ParametrizationData.hessianForm_isHessianFormAt (H : R.ParametrizationData N F φ z D)
    (hcr : R.IsCriticalOn N F (φ z)) :
    R.IsHessianFormAt Subtype.val N F (φ z)
      (R.hessianForm (S := R.tangentSpan N (φ z)) Subtype.val N F (φ z)) := by
  obtain ⟨Q, hQ⟩ := H.exists_quadraticForm
  exact Classical.epsilon_spec (p := fun Q : QuadraticForm ℝ (R.tangentSpan N (φ z)) =>
    R.IsHessianFormAt Subtype.val N F (φ z) Q) ⟨Q, H.isHessianFormAt_of hcr Q hQ⟩
theorem ParametrizationData.hessianForm_apply (H : R.ParametrizationData N F φ z D)
    (hcr : R.IsCriticalOn N F (φ z)) (h : P) (v : R.tangentSpan N (φ z))
    (hv : (v : T) = D h) :
    R.hessianForm (S := R.tangentSpan N (φ z)) Subtype.val N F (φ z) v =
      fderiv ℝ (fderiv ℝ (F ∘ φ)) z h h := by
  obtain ⟨Q, hQ⟩ := H.exists_quadraticForm
  have h1 := H.eq_of_isHessianFormAt _ _ (H.hessianForm_isHessianFormAt hcr)
    (H.isHessianFormAt_of hcr Q hQ)
  rw [congrFun h1 v, hQ h v hv]
theorem ParametrizationData.hessianViaParametrization (H : R.ParametrizationData N F φ z D) :
    R.HessianViaParametrization N F φ z D where
  injective := H.injective
  range_eq := H.range_eq
  isCriticalOn_iff := H.isCriticalOn_iff
  secondDeriv_eq := fun hcr I γ h => H.secondDeriv_eq hcr I γ h
  exists_curve := fun _ v hv => H.exists_curve v hv
  existsUnique_isHessianFormAt := fun hcr =>
    ⟨_, H.hessianForm_isHessianFormAt hcr,
      fun _ hQ => H.eq_of_isHessianFormAt _ _ hQ (H.hessianForm_isHessianFormAt hcr)⟩
  hessianForm_isHessianFormAt := H.hessianForm_isHessianFormAt
  hessianForm_apply := H.hessianForm_apply
  posDef_hessianForm_iff := fun hcr => by
    have hr := H.range_eq
    constructor
    · intro hp h hh
      have hm : D h ∈ R.tangentSpan N (φ z) := hr ▸ LinearMap.mem_range_self D h
      have hne : (⟨D h, hm⟩ : R.tangentSpan N (φ z)) ≠ 0 := by
        intro h0
        apply hh
        apply H.injective
        simpa using congrArg Subtype.val h0
      rw [← H.hessianForm_apply hcr h ⟨D h, hm⟩ rfl]
      exact hp _ hne
    · intro hp v hv
      have hm : (v : T) ∈ LinearMap.range D := by
        rw [hr]
        exact v.2
      obtain ⟨h, hh⟩ := hm
      rw [H.hessianForm_apply hcr h v hh.symm]
      refine hp h ?_
      rintro rfl
      apply hv
      apply Subtype.ext
      simpa using hh.symm
theorem ParametrizationData.hasUniqueHessianAt (H : R.ParametrizationData N F φ z D)
    (hcr : R.IsCriticalOn N F (φ z)) : R.HasUniqueHessianAt N F (φ z) := by
  refine ⟨R.hessianForm (S := R.tangentSpan N (φ z)) Subtype.val N F (φ z),
    H.hessianForm_isHessianFormAt hcr, fun Q hQ => ?_⟩
  apply DFunLike.coe_injective
  exact H.eq_of_isHessianFormAt _ _ hQ (H.hessianForm_isHessianFormAt hcr)
end Geometry.CurveData
namespace Tower.RestrictionHessian
def coordinateSubspace {d : ℕ} (s : Set (Fin d)) : Submodule ℝ (Fin d → ℝ) where
  carrier := {w | ∀ i, i ∉ s → w i = 0}
  add_mem' := by
    intro a b ha hb i hi
    simp [ha i hi, hb i hi]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c a ha i hi
    simp [ha i hi]
theorem fderiv_fderiv_comp_add_subspace {d : ℕ} {V : Submodule ℝ (Fin d → ℝ)}
    {G : (Fin d → ℝ) → ℝ} {u₀ : Fin d → ℝ} (hG : ContDiffAt ℝ 2 G u₀) (w w' : V) :
    fderiv ℝ (fderiv ℝ fun p : V => G (u₀ + p)) 0 w w' = fderiv ℝ (fderiv ℝ G) u₀ w w' := by
  let ι : V →L[ℝ] (Fin d → ℝ) := V.subtypeL
  have hA : ∀ p : V, HasFDerivAt (fun p : V => u₀ + (p : Fin d → ℝ)) ι p :=
    fun p => ι.hasFDerivAt.const_add u₀
  have hlim : Tendsto (fun p : V => u₀ + (p : Fin d → ℝ)) (𝓝 0) (𝓝 u₀) := by
    have := (hA 0).continuousAt.tendsto
    simpa using this
  have hd : ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℝ G u :=
    (hG.eventually (by simp)).mono fun p hp => hp.differentiableAt (by norm_num)
  have h1 : fderiv ℝ (fun p : V => G (u₀ + p)) =ᶠ[𝓝 0]
      fun p => (fderiv ℝ G (u₀ + p)).comp ι := by
    filter_upwards [hlim.eventually hd] with p hp
    exact (hp.hasFDerivAt.comp p (hA p)).fderiv
  rw [h1.fderiv_eq]
  have hG2 : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) u₀)
      (u₀ + ((0 : V) : Fin d → ℝ)) := by
    have : DifferentiableAt ℝ (fderiv ℝ G) u₀ :=
      (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    simpa using this.hasFDerivAt
  have h2 := (hG2.comp (0 : V) (hA 0)).clm_comp (hasFDerivAt_const ι (0 : V))
  have h3 : (fun p : V => (fderiv ℝ G (u₀ + p)).comp ι) =
      fun p => ((fderiv ℝ G ∘ fun p : V => u₀ + (p : Fin d → ℝ)) p).comp ι := rfl
  rw [h3, h2.fderiv]
  simp [ι]
end Tower.RestrictionHessian
namespace Geometry.CurveData
open YangMills.Construction.Tower.RestrictionHessian
variable {X T : Type} [AddCommGroup T] [Module ℝ T] {R : CurveData X T}
  {N : Set X} {F : X → ℝ}
theorem ParametrizationData.hessianEqPartialsMatrix {d : ℕ} {ψ : (Fin d → ℝ) → X}
    {u₀ : Fin d → ℝ} {s : Set (Fin d)} {D : coordinateSubspace s →ₗ[ℝ] T}
    (H : R.ParametrizationData N F (fun p : coordinateSubspace s => ψ (u₀ + p)) 0 D)
    (hcr : R.IsCriticalOn N F (ψ u₀)) (hG : ContDiffAt ℝ 2 (F ∘ ψ) u₀) :
    R.HessianEqPartialsMatrix N F ψ u₀ s := by
  have key : ∀ x, (fun p : coordinateSubspace s => ψ (u₀ + p)) 0 = x →
      LinearMap.range D = R.tangentSpan N x ∧ (R.IsCriticalOn N F x →
      ∀ (h : coordinateSubspace s) (v : R.tangentSpan N x), (v : T) = D h →
        R.hessianForm (S := R.tangentSpan N x) Subtype.val N F x v =
          fderiv ℝ (fderiv ℝ (F ∘ fun p : coordinateSubspace s => ψ (u₀ + p))) 0 h h) := by
    rintro _ rfl
    exact ⟨H.range_eq, H.hessianForm_apply⟩
  obtain ⟨hr, hh⟩ := key (ψ u₀) (by simp)
  replace hh := hh hcr
  have htan : ∀ (w : Fin d → ℝ) (hw : w ∈ coordinateSubspace s),
      R.tangent (fun t : ℝ => ψ (u₀ + t • w)) = D ⟨w, hw⟩ := by
    intro w hw
    obtain ⟨I, -, -, -, ht⟩ := H.line ⟨w, hw⟩
    simpa using ht
  have hsec : ∀ (h : coordinateSubspace s) (v : R.tangentSpan N (ψ u₀)), (v : T) = D h →
      R.hessianForm (S := R.tangentSpan N (ψ u₀)) Subtype.val N F (ψ u₀) v =
        fderiv ℝ (fderiv ℝ (F ∘ ψ)) u₀ h h := by
    intro h v hv
    rw [hh h v hv]
    exact fderiv_fderiv_comp_add_subspace hG h h
  refine ⟨fun w hw => ?_, fun w w' v v' hw hw' hv hv' => ?_⟩
  · rw [htan w hw, ← hr]
    exact LinearMap.mem_range_self D _
  · rw [htan w hw] at hv
    rw [htan w' hw'] at hv'
    have hsum : ((v + v' : R.tangentSpan N (ψ u₀)) : T) =
        D (⟨w, hw⟩ + ⟨w', hw'⟩) := by
      simp [hv, hv']
    have hsym : fderiv ℝ (fderiv ℝ (F ∘ ψ)) u₀ w' w = fderiv ℝ (fderiv ℝ (F ∘ ψ)) u₀ w w' :=
      (hG.isSymmSndFDerivAt (by simp)).eq w' w
    have hexp : ∀ a : Fin d → ℝ, a = ∑ i, a i • (Pi.single i 1 : Fin d → ℝ) := by
      intro a
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    have hmat : fderiv ℝ (fderiv ℝ (F ∘ ψ)) u₀ w w' =
        ∑ i, ∑ j, w i * w' j *
          fderiv ℝ (fderiv ℝ (F ∘ ψ)) u₀ (Pi.single i 1) (Pi.single j 1) := by
      conv_lhs => rw [hexp w, hexp w']
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [QuadraticMap.polar, hsec _ _ hsum, hsec _ _ hv, hsec _ _ hv', ← hmat]
    simp only [Submodule.coe_add, map_add, ContinuousLinearMap.add_apply, hsym]
    ring
end Geometry.CurveData
namespace Matrices.EmbeddedSubmanifold
open YangMills.Construction.Tower.RestrictionHessian
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
theorem exists_contDiffAt_leftInverse {φ : P → E} {z : P} (hφ : ContDiffAt ℝ 2 φ z)
    (hinj : Function.Injective (fderiv ℝ φ z)) :
    ∃ r : E → P, ContDiffAt ℝ 2 r (φ z) ∧ r (φ z) = z ∧ ∀ᶠ p in 𝓝 z, r (φ p) = p := by
  have : CompleteSpace P := FiniteDimensional.complete ℝ P
  let A : P →ₗ[ℝ] E := fderiv ℝ φ z
  have hAi : Function.Injective A := hinj
  let e := LinearEquiv.ofInjective A hAi
  have : FiniteDimensional ℝ (LinearMap.range A) := LinearMap.finiteDimensional_range A
  let g : LinearMap.range A →L[ℝ] P := e.symm.toLinearMap.toContinuousLinearMap
  obtain ⟨L, hL⟩ := g.exist_extension_of_finiteDimensional_range
  have hLA : ∀ h : P, L (fderiv ℝ φ z h) = h := by
    intro h
    have h1 : g (e h) = h := e.symm_apply_apply h
    have h2 := congrArg (fun m => m (e h)) hL
    simp only [ContinuousLinearMap.comp_apply] at h2
    rw [h1] at h2
    simpa [e, A] using h2.symm
  have hd : HasFDerivAt φ (fderiv ℝ φ z) z := (hφ.differentiableAt (by norm_num)).hasFDerivAt
  have hgz : HasFDerivAt (L ∘ φ)
      (((ContinuousLinearEquiv.refl ℝ P : P ≃L[ℝ] P)) : P →L[ℝ] P) z := by
    have := L.hasFDerivAt.comp z hd
    convert this using 1
    ext h
    simp [hLA]
  have hc : ContDiffAt ℝ 2 (L ∘ φ) z := L.contDiff.contDiffAt.comp z hφ
  have h2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  refine ⟨hc.localInverse hgz h2 ∘ L, ?_, ?_, ?_⟩
  · exact ContDiffAt.comp (φ z) (hc.to_localInverse hgz h2) L.contDiff.contDiffAt
  · exact hc.localInverse_apply_image hgz h2
  · exact (hc.hasStrictFDerivAt' hgz h2).eventually_left_inverse
variable {N : Set E} {O : Set P} {φ : P → E} {z : P}
theorem IsC2Parametrization.contDiffAt (hφ : IsC2Parametrization N O φ) (hz : z ∈ O) :
    ContDiffAt ℝ 2 φ z :=
  hφ.2.1.contDiffAt (hφ.1.mem_nhds hz)
theorem IsC2Parametrization.exists_local_retraction (hφ : IsC2Parametrization N O φ)
    (hz : z ∈ O) :
    ∃ r : E → P, ContDiffAt ℝ 2 r (φ z) ∧ r (φ z) = z ∧
      ∀ᶠ y in 𝓝[N] (φ z), r y ∈ O ∧ φ (r y) = y := by
  have hO := hφ.1
  have hW := hφ.2.2.2.2.2
  obtain ⟨r, hr, r0, hev⟩ :=
    exists_contDiffAt_leftInverse (hφ.contDiffAt hz) (hφ.2.2.2.2.1 z hz)
  refine ⟨r, hr, r0, ?_⟩
  have hWo : IsOpen (interior {p | r (φ p) = p} ∩ O) := isOpen_interior.inter hO
  have hzW : z ∈ interior {p | r (φ p) = p} ∩ O := ⟨mem_interior_iff_mem_nhds.2 hev, hz⟩
  obtain ⟨Y, hY, hE⟩ := hW _ inter_subset_right hWo
  have hzY : φ z ∈ Y ∩ N := hE ▸ mem_image_of_mem φ hzW
  refine mem_nhdsWithin.2 ⟨Y, hY, hzY.1, fun y hy => ?_⟩
  have hy' : y ∈ φ '' (interior {p | r (φ p) = p} ∩ O) := by
    rw [hE]
    exact ⟨hy.1, hy.2⟩
  obtain ⟨p, hp, rfl⟩ := hy'
  have hrp : p ∈ {p | r (φ p) = p} := interior_subset hp.1
  replace hrp : r (φ p) = p := hrp
  exact ⟨by rw [hrp]; exact hp.2, by rw [hrp]⟩
theorem Chart.isC2Parametrization {M : Set E} (c : Chart M) :
    IsC2Parametrization M c.source c.param := by
  refine ⟨c.isOpen_source, c.contDiffOn_param.of_le ENat.LEInfty.out,
    c.injOn_param, fun u hu => ?_, c.injective_fderiv_param, c.isRelativelyOpen_image⟩
  obtain ⟨Y, -, hE⟩ := c.isRelativelyOpen_image c.source subset_rfl c.isOpen_source
  have : c.param u ∈ Y ∩ M := hE ▸ mem_image_of_mem _ hu
  exact this.2
theorem IsC2Parametrization.contDiffAt_comp_of_isC2OnCharted {𝒳 : Set E} {F : E → ℝ}
    (h𝒳 : IsChartedSubset 𝒳) (hN : N ⊆ 𝒳) (hF : IsC2OnCharted 𝒳 F)
    (hφ : IsC2Parametrization N O φ) (hz : z ∈ O) : ContDiffAt ℝ 2 (F ∘ φ) z := by
  have hzN : φ z ∈ 𝒳 := hN (hφ.2.2.2.1 hz)
  obtain ⟨c, u, hu, hcu⟩ := h𝒳 _ hzN
  obtain ⟨r, hr, r0, hev⟩ := c.isC2Parametrization.exists_local_retraction hu
  have hφz := hφ.contDiffAt hz
  rw [hcu] at hr hev
  have hpull : ContDiffAt ℝ 2 (c.pullback F) (r (φ z)) := by
    rw [hcu] at r0
    rw [r0]
    exact (hF c).contDiffAt (c.isOpen_source.mem_nhds hu)
  have hG : ContDiffAt ℝ 2 (c.pullback F ∘ r ∘ φ) z :=
    ContDiffAt.comp z hpull (ContDiffAt.comp z hr hφz)
  refine hG.congr_of_eventuallyEq ?_
  have ht : Tendsto φ (𝓝 z) (𝓝[𝒳] (φ z)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hφz.continuousAt.tendsto, ?_⟩
    filter_upwards [hφ.1.mem_nhds hz] with p hp
    exact hN (hφ.2.2.2.1 hp)
  filter_upwards [ht.eventually hev] with p hp
  simp [Chart.pullback, hp.2]
theorem IsC2Parametrization.exists_line (hφ : IsC2Parametrization N O φ) (hz : z ∈ O) (h : P) :
    ∃ I : Set ℝ, Tower.IsOpenIntervalAroundZero I ∧ MapsTo (fun t : ℝ => z + t • h) I O ∧
      DifferentiableOn ℝ (fun t : ℝ => φ (z + t • h)) I ∧
      DifferentiableOn ℝ (deriv fun t : ℝ => φ (z + t • h)) I ∧
      deriv (fun t : ℝ => φ (z + t • h)) 0 = fderiv ℝ φ z h := by
  have hℓ : ContDiff ℝ 2 (fun t : ℝ => z + t • h) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hop : IsOpen ((fun t : ℝ => z + t • h) ⁻¹' O) := hφ.1.preimage hℓ.continuous
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 hop 0 (by simpa using hz)
  have hI : IsOpen (Metric.ball (0 : ℝ) ε) := Metric.isOpen_ball
  have hm : MapsTo (fun t : ℝ => z + t • h) (Metric.ball (0 : ℝ) ε) O := fun t ht => hb ht
  have hc : ContDiffOn ℝ (1 + 1) (fun t : ℝ => φ (z + t • h)) (Metric.ball (0 : ℝ) ε) := by
    have := hφ.2.1.comp hℓ.contDiffOn hm
    rw [one_add_one_eq_two]
    exact this
  obtain ⟨h1, -, h2⟩ := (contDiffOn_succ_iff_deriv_of_isOpen hI).1 hc
  refine ⟨Metric.ball 0 ε, ⟨hI, (convex_ball (0 : ℝ) ε).ordConnected, Metric.mem_ball_self hε⟩,
    hm, h1, h2.differentiableOn (by norm_num), ?_⟩
  have hl : HasDerivAt (fun t : ℝ => z + t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add z
  have hd : HasFDerivAt φ (fderiv ℝ φ z) (z + (0 : ℝ) • h) := by
    simpa using ((hφ.contDiffAt hz).differentiableAt (by norm_num)).hasFDerivAt
  exact (hd.comp_hasDerivAt (0 : ℝ) hl).deriv
end Matrices.EmbeddedSubmanifold
namespace Matrices.EmbeddedSubmanifold
open YangMills.Construction.Tower.RestrictionHessian
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {N : Set E} {O : Set P} {φ : P → E} {z : P}
theorem paramEvaluationData {𝒳 : Set E} {F : E → ℝ} (h𝒳 : IsChartedSubset 𝒳) (hN : N ⊆ 𝒳)
    (hF : IsC2OnCharted 𝒳 F) (hφ : IsC2Parametrization N O φ) (hz : z ∈ O) :
    (vectorCurveData E).ParametrizationData N F φ z (fderiv ℝ φ z : P →ₗ[ℝ] E) := by
  obtain ⟨r, hr, r0, hev⟩ := hφ.exists_local_retraction hz
  have hφd : DifferentiableAt ℝ φ z := (hφ.contDiffAt hz).differentiableAt (by norm_num)
  have hlift : ∀ γ : ℝ → E, ContinuousAt γ 0 → γ 0 = φ z → (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ N) →
      ∀ᶠ t in 𝓝 (0 : ℝ), φ (r (γ t)) = γ t := by
    intro γ hc h0 hm
    have ht : Tendsto γ (𝓝 0) (𝓝[N] (φ z)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, hm⟩
      have := hc.tendsto
      rwa [h0] at this
    exact (ht.eventually hev).mono fun t h => h.2
  have htan : ∀ γ : ℝ → E, γ 0 = φ z → DifferentiableAt ℝ (r ∘ γ) 0 →
      (∀ᶠ t in 𝓝 (0 : ℝ), φ (r (γ t)) = γ t) →
      deriv γ 0 = fderiv ℝ φ z (deriv (r ∘ γ) 0) := by
    intro γ h0 hd hl
    have h1 : γ =ᶠ[𝓝 0] φ ∘ (r ∘ γ) := hl.mono fun t ht => ht.symm
    have hc0 : (r ∘ γ) 0 = z := by simp [h0, r0]
    rw [h1.deriv_eq, fderiv_comp_deriv 0 (by rw [hc0]; exact hφd) hd, hc0]
  refine ⟨fun a b h => hφ.2.2.2.2.1 z hz h, hφ.2.2.2.1 hz,
    hφ.contDiffAt_comp_of_isC2OnCharted h𝒳 hN hF hz, ?_, ?_, ?_⟩
  · rintro I γ ⟨hI, hd⟩ hm h0
    have hI0 : I ∈ 𝓝 (0 : ℝ) := hI.1.mem_nhds hI.2.2
    have hγ0 : DifferentiableAt ℝ γ 0 := hd.differentiableAt hI0
    have hl := hlift γ hγ0.continuousAt h0 (by filter_upwards [hI0] with t ht using hm ht)
    have hr0 : DifferentiableAt ℝ r (γ 0) := by
      rw [h0]
      exact hr.differentiableAt (by norm_num)
    have hcd : DifferentiableAt ℝ (r ∘ γ) 0 := hr0.comp 0 hγ0
    refine ⟨r ∘ γ, by simp [h0, r0], hcd, ?_, htan γ h0 hcd hl⟩
    filter_upwards [hl] with t ht
    simp [ht]
  · rintro I γ ⟨hI, hd, hd2⟩ hm h0
    have hI0 : I ∈ 𝓝 (0 : ℝ) := hI.1.mem_nhds hI.2.2
    have hγ0 : DifferentiableAt ℝ γ 0 := hd.differentiableAt hI0
    have hl := hlift γ hγ0.continuousAt h0 (by filter_upwards [hI0] with t ht using hm ht)
    have hγt : Tendsto γ (𝓝 0) (𝓝 (φ z)) := by
      have := hγ0.continuousAt.tendsto
      rwa [h0] at this
    have hrd : ∀ᶠ y in 𝓝 (φ z), DifferentiableAt ℝ r y :=
      (hr.eventually (by simp)).mono fun p hp => hp.differentiableAt (by norm_num)
    have hγd : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ γ t := by
      filter_upwards [hI0] with t ht
      exact hd.differentiableAt (hI.1.mem_nhds ht)
    have hcd : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ (r ∘ γ) t := by
      filter_upwards [hγt.eventually hrd, hγd] with t h1 h2
      exact h1.comp t h2
    have hev2 : deriv (r ∘ γ) =ᶠ[𝓝 0] fun t => fderiv ℝ r (γ t) (deriv γ t) := by
      filter_upwards [hγt.eventually hrd, hγd] with t h1 h2
      exact fderiv_comp_deriv t h1 h2
    have hr2 : DifferentiableAt ℝ (fderiv ℝ r) (γ 0) := by
      rw [h0]
      exact (hr.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have h3 : DifferentiableAt ℝ (fun t => fderiv ℝ r (γ t) (deriv γ t)) 0 :=
      DifferentiableAt.clm_apply (hr2.comp 0 hγ0) (hd2.differentiableAt hI0)
    refine ⟨r ∘ γ, by simp [h0, r0], hcd, h3.congr_of_eventuallyEq hev2, ?_,
      htan γ h0 hcd.self_of_nhds hl⟩
    filter_upwards [hl] with t ht
    simp [ht]
  · intro h
    obtain ⟨I, hI, hm, h1, h2, h3⟩ := hφ.exists_line hz h
    exact ⟨I, ⟨hI, h1⟩, ⟨hI, h1, h2⟩, fun t ht => hφ.2.2.2.1 (hm ht), h3⟩
theorem Chart.exists_coordinatePlane_parametrization {𝒳 : Set E} (hN : N ⊆ 𝒳) (c : Chart 𝒳)
    {u₀ : Fin c.dim → ℝ} {s : Set (Fin c.dim)} (h : c.IsLocallyCoordinatePlane N u₀ s) :
    ∃ O : Set (coordinateSubspace s), (0 : coordinateSubspace s) ∈ O ∧
      IsC2Parametrization N O fun p : coordinateSubspace s => c.param (u₀ + p) := by
  obtain ⟨W, hWo, hu, hWd, hW⟩ := h
  let ι : coordinateSubspace s →L[ℝ] (Fin c.dim → ℝ) := (coordinateSubspace s).subtypeL
  have hAc : ContDiff ℝ 2 (fun p : coordinateSubspace s => u₀ + (p : Fin c.dim → ℝ)) :=
    contDiff_const.add ι.contDiff
  have hA : ∀ p : coordinateSubspace s,
      HasFDerivAt (fun p : coordinateSubspace s => u₀ + (p : Fin c.dim → ℝ)) ι p :=
    fun p => ι.hasFDerivAt.const_add u₀
  have hcp := c.isC2Parametrization
  refine ⟨{p | u₀ + (p : Fin c.dim → ℝ) ∈ W}, by simpa using hu,
    hWo.preimage hAc.continuous, ?_, ?_, ?_, ?_, ?_⟩
  · exact hcp.2.1.comp hAc.contDiffOn fun p hp => hWd hp
  · intro p hp q hq e
    have := c.injOn_param (hWd hp) (hWd hq) e
    exact Subtype.ext (add_left_cancel this)
  · intro p hp
    refine (hW _ hp).2 fun i hi => ?_
    simp [p.2 i hi]
  · intro p hp
    have hd : HasFDerivAt c.param (fderiv ℝ c.param (u₀ + p))
        (u₀ + (p : Fin c.dim → ℝ)) :=
      ((hcp.contDiffAt (hWd hp)).differentiableAt (by norm_num)).hasFDerivAt
    have h1 := (hd.comp p (hA p)).fderiv
    have h2 : fderiv ℝ (fun p : coordinateSubspace s => c.param (u₀ + p)) p =
        (fderiv ℝ c.param (u₀ + p)).comp ι := h1
    rw [h2]
    intro a b e
    exact Subtype.ext (c.injective_fderiv_param _ (hWd hp) e)
  · intro W' hW' hW'o
    obtain ⟨t, ht, rfl⟩ := isOpen_induced_iff.1 hW'o
    have hA'o : IsOpen ({u | u - u₀ ∈ t} ∩ W) :=
      (ht.preimage (continuous_id.sub continuous_const)).inter hWo
    obtain ⟨Y, hY, hE⟩ := c.isRelativelyOpen_image _ (inter_subset_right.trans hWd) hA'o
    refine ⟨Y, hY, ?_⟩
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      have h1 : c.param (u₀ + p) ∈ Y ∩ 𝒳 := by
        rw [← hE]
        exact ⟨u₀ + p, ⟨by simpa using hp, hW' hp⟩, rfl⟩
      exact ⟨h1.1, (hW _ (hW' hp)).2 fun i hi => by simp [p.2 i hi]⟩
    · rintro ⟨hy, hyN⟩
      have h1 : y ∈ c.param '' ({u | u - u₀ ∈ t} ∩ W) := by
        rw [hE]
        exact ⟨hy, hN hyN⟩
      obtain ⟨u, ⟨hut, huW⟩, rfl⟩ := h1
      have h2 := (hW u huW).1 hyN
      have hmem : u - u₀ ∈ coordinateSubspace s := by
        intro i hi
        simp [h2 i hi]
      exact ⟨⟨u - u₀, hmem⟩, hut, by simp⟩
end Matrices.EmbeddedSubmanifold
namespace Tower
open YangMills.Construction.Tower.RestrictionHessian
variable {L n k j : ℕ}
theorem restrictToPositiveEdges_fieldOfPositiveValues
    (w : PositiveEdge L n k j → Matrices.ComplexMatrix2) :
    restrictToPositiveEdges (fieldOfPositiveValues w) = w := by apply _root_.YangMills.SharedProofs.p777 <;> assumption
theorem fieldOfPositiveValues_restrictToPositiveEdges
    {V : Edge L n k j → Matrices.ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
def tangentMapOfValues (x : Edge L n k j → Matrices.ComplexMatrix2) :
    (PositiveEdge L n k j → Matrices.ComplexMatrix2) →ₗ[ℝ]
      Edge L n k j → Matrices.ComplexMatrix2 where
  toFun v := extendOddly fun b => open Classical in
    if h : b.IsPositivelyOriented then Complex.I⁻¹ • (v ⟨b, h⟩ * (x b)⁻¹) else 0
  map_add' v w := by
    funext b
    have hadd : ∀ (c : Edge L n k j) (h : c.IsPositivelyOriented),
        Complex.I⁻¹ • ((v ⟨c, h⟩ + w ⟨c, h⟩) * (x c)⁻¹) =
          Complex.I⁻¹ • (v ⟨c, h⟩ * (x c)⁻¹) + Complex.I⁻¹ • (w ⟨c, h⟩ * (x c)⁻¹) := by
      intro c h
      rw [add_mul, smul_add]
    by_cases hb : b.IsPositivelyOriented
    · simp only [extendOddly, Pi.add_apply, if_pos hb, dif_pos hb, hadd]
    · by_cases hb' : b.opposite.IsPositivelyOriented
      · simp only [extendOddly, Pi.add_apply, if_neg hb, dif_pos hb', hadd, neg_add]
      · simp only [extendOddly, Pi.add_apply, if_neg hb, dif_neg hb', neg_zero, add_zero]
  map_smul' r v := by
    funext b
    have hsm : ∀ (c : Edge L n k j) (h : c.IsPositivelyOriented),
        Complex.I⁻¹ • (r • v ⟨c, h⟩ * (x c)⁻¹) = r • Complex.I⁻¹ • (v ⟨c, h⟩ * (x c)⁻¹) := by
      intro c h
      rw [smul_mul_assoc, smul_comm]
    by_cases hb : b.IsPositivelyOriented
    · simp only [extendOddly, RingHom.id_apply, Pi.smul_apply, if_pos hb, dif_pos hb, hsm]
    · by_cases hb' : b.opposite.IsPositivelyOriented
      · simp only [extendOddly, RingHom.id_apply, Pi.smul_apply, if_neg hb, dif_pos hb', hsm,
          smul_neg]
      · simp only [extendOddly, RingHom.id_apply, Pi.smul_apply, if_neg hb, dif_neg hb',
          neg_zero, smul_zero]
theorem tangentMapOfValues_apply (x : Edge L n k j → Matrices.ComplexMatrix2)
    (v : PositiveEdge L n k j → Matrices.ComplexMatrix2) (b : PositiveEdge L n k j) :
    tangentMapOfValues x v b = Complex.I⁻¹ • (v b * (x b)⁻¹) := by
  have hb : (b : Edge L n k j).IsPositivelyOriented := b.2
  simp [tangentMapOfValues, extendOddly, hb]
theorem tangentMapOfValues_injective {x : Edge L n k j → Matrices.ComplexMatrix2}
    (hx : x ∈ fieldSpace L n k j) : Function.Injective (tangentMapOfValues x) := by
  have hx' : PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ x := hx
  rw [injective_iff_map_eq_zero]
  intro v hv
  funext b
  have h1 : Complex.I⁻¹ • (v b * (x b)⁻¹) = 0 := by
    rw [← tangentMapOfValues_apply, hv]
    rfl
  have h2 : v b * (x b)⁻¹ = 0 :=
    (smul_eq_zero.1 h1).resolve_left (inv_ne_zero Complex.I_ne_zero)
  have hdet : IsUnit (x b).det := by
    have := (Matrix.mem_specialUnitaryGroup_iff.1 (hx'.1 b.1 (mem_univ _))).2
    rw [this]
    exact isUnit_one
  calc v b = v b * ((x b)⁻¹ * x b) := by rw [Matrix.nonsing_inv_mul _ hdet, mul_one]
    _ = 0 := by rw [← mul_assoc, h2, zero_mul]
theorem curveTangent_eq [Fintype (PositiveEdge L n k j)]
    {γ : ℝ → Edge L n k j → Matrices.ComplexMatrix2}
    (hd : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      DifferentiableAt ℝ (fun t => γ t b) 0) :
    curveTangent γ =
      tangentMapOfValues (γ 0) (deriv (fun t => restrictToPositiveEdges (γ t)) 0) := by
  have hp : deriv (fun t => restrictToPositiveEdges (γ t)) 0 =
      fun b : PositiveEdge L n k j => deriv (fun t => γ t b) 0 :=
    deriv_pi fun b => hd b.1 b.2
  rw [hp]
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp [curveTangent, tangentMapOfValues, extendOddly, hb]
  · have hb' := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
    simp [curveTangent, tangentMapOfValues, extendOddly, hb, hb']
theorem IsFieldSubmanifold.isChartedSubset [i : Fintype (PositiveEdge L n k j)]
    {N : Set (Edge L n k j → Matrices.ComplexMatrix2)} (h : IsFieldSubmanifold N) :
    Matrices.EmbeddedSubmanifold.IsChartedSubset (restrictToPositiveEdges '' N) := by
  obtain ⟨-, i', hm⟩ := h
  obtain rfl := Subsingleton.elim i i'
  exact hm
variable [Fintype (PositiveEdge L n k j)]
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {N : Set (Edge L n k j → Matrices.ComplexMatrix2)}
  {F : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ} {O : Set P}
  {φ : P → Edge L n k j → Matrices.ComplexMatrix2} {z : P}
theorem paramEvaluationData_of_values (hNc : N ⊆ fieldSpace L n k j)
    (hφ : IsFieldParametrization N O φ) (hz : z ∈ O)
    {D₀ : P →ₗ[ℝ] PositiveEdge L n k j → Matrices.ComplexMatrix2}
    (H : (Matrices.EmbeddedSubmanifold.vectorCurveData
      (PositiveEdge L n k j → Matrices.ComplexMatrix2)).ParametrizationData
      (restrictToPositiveEdges '' N) (fun w => F (fieldOfPositiveValues w))
      (fun p => restrictToPositiveEdges (φ p)) z D₀) :
    (fieldCurveData L n k j).ParametrizationData N F φ z (tangentMapOfValues (φ z) ∘ₗ D₀) := by
  have hval : ∀ V ∈ N, F (fieldOfPositiveValues (restrictToPositiveEdges V)) = F V :=
    fun V hV => by rw [fieldOfPositiveValues_restrictToPositiveEdges (hNc hV)]
  have hφ' := hφ.2
  have hO := hφ'.1
  have hnear : ∀ c : ℝ → P, c 0 = z → ContinuousAt c 0 → ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ O := by
    intro c c0 hc
    apply hc.eventually_mem
    rw [c0]
    exact hO.mem_nhds hz
  refine ⟨?_, hφ.1 hz, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.coe_comp]
    exact (tangentMapOfValues_injective (hNc (hφ.1 hz))).comp H.injective
  · refine H.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hz] with p hp
    exact (hval _ (hφ.1 hp)).symm
  · rintro I γ ⟨hI, hconf, hd⟩ hm h0
    have hI0 : I ∈ 𝓝 (0 : ℝ) := hI.1.mem_nhds hI.2.2
    have hcur : (Matrices.EmbeddedSubmanifold.vectorCurveData
        (PositiveEdge L n k j → Matrices.ComplexMatrix2)).IsCurve I
        (fun t => restrictToPositiveEdges (γ t)) :=
      ⟨hI, differentiableOn_pi.2 fun b => hd b.1 b.2⟩
    obtain ⟨c, c0, hc, hev, ht⟩ :=
      H.liftCurve I _ hcur (fun t ht => mem_image_of_mem _ (hm ht)) (by simp [h0])
    refine ⟨c, c0, hc, ?_, ?_⟩
    · filter_upwards [hev, hI0, hnear c c0 hc.continuousAt] with t h1 h2 h3
      rw [← hval _ (hm h2), ← hval _ (hφ.1 h3)]
      exact h1
    · have h1 : curveTangent γ = _ :=
        curveTangent_eq fun b hb => (hd b hb).differentiableAt hI0
      rw [h0] at h1
      exact h1.trans (congrArg _ ht)
  · rintro I γ ⟨⟨hI, hconf, hd⟩, hd2⟩ hm h0
    have hI0 : I ∈ 𝓝 (0 : ℝ) := hI.1.mem_nhds hI.2.2
    have hdat : ∀ t ∈ I, deriv (fun t => restrictToPositiveEdges (γ t)) t =
        fun b : PositiveEdge L n k j => deriv (fun t => γ t b) t := fun t ht =>
      deriv_pi fun b => (hd b.1 b.2).differentiableAt (hI.1.mem_nhds ht)
    have hcur : (Matrices.EmbeddedSubmanifold.vectorCurveData
        (PositiveEdge L n k j → Matrices.ComplexMatrix2)).IsTwiceDiffCurve
        I (fun t => restrictToPositiveEdges (γ t)) :=
      ⟨hI, differentiableOn_pi.2 fun b => hd b.1 b.2,
        (differentiableOn_pi.2 fun b => hd2 b.1 b.2 :
          DifferentiableOn ℝ (fun t => fun b : PositiveEdge L n k j =>
            deriv (fun t => γ t b) t) I).congr hdat⟩
    obtain ⟨c, c0, hc, hc2, hev, ht⟩ :=
      H.liftCurve₂ I _ hcur (fun t ht => mem_image_of_mem _ (hm ht)) (by simp [h0])
    refine ⟨c, c0, hc, hc2, ?_, ?_⟩
    · filter_upwards [hev, hI0, hnear c c0 hc.self_of_nhds.continuousAt] with t h1 h2 h3
      rw [← hval _ (hm h2), ← hval _ (hφ.1 h3)]
      exact h1
    · have h1 : curveTangent γ = _ :=
        curveTangent_eq fun b hb => (hd b hb).differentiableAt hI0
      rw [h0] at h1
      exact h1.trans (congrArg _ ht)
  · intro h
    obtain ⟨I, hI, hm, h1, h2, h3⟩ := hφ'.exists_line hz h
    have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
        DifferentiableOn ℝ (fun t : ℝ => φ (z + t • h) b) I :=
      fun b hb => differentiableOn_pi.1 h1 ⟨b, hb⟩
    have hcv : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I
        fun t : ℝ => φ (z + t • h) :=
      ⟨hI, fun t ht => hNc (hφ.1 (hm ht)), hpos⟩
    have hI0 : I ∈ 𝓝 (0 : ℝ) := hI.1.mem_nhds hI.2.2
    refine ⟨I, hcv, ⟨hcv, fun b hb => ?_⟩, fun t ht => hφ.1 (hm ht), ?_⟩
    · refine (differentiableOn_pi.1 h2 ⟨b, hb⟩).congr fun t ht => ?_
      have h4 : deriv (fun t : ℝ => restrictToPositiveEdges (φ (z + t • h))) t =
          fun b : PositiveEdge L n k j => deriv (fun t : ℝ => φ (z + t • h) b) t :=
        deriv_pi fun b => (hpos b.1 b.2).differentiableAt (hI.1.mem_nhds ht)
      exact (congrFun h4 ⟨b, hb⟩).symm
    · have h5 : curveTangent (fun t : ℝ => φ (z + t • h)) = _ :=
        curveTangent_eq fun b hb => (hpos b hb).differentiableAt hI0
      have h6 : φ (z + (0 : ℝ) • h) = φ z := by simp
      rw [h6, h3] at h5
      obtain ⟨J, -, -, -, hJ⟩ := H.line h
      have hJ' : fderiv ℝ (fun p => restrictToPositiveEdges (φ p)) z h = D₀ h := by
        rw [← h3]
        exact hJ
      rw [hJ'] at h5
      exact h5
theorem isFieldParametrization_of_values (hNc : N ⊆ fieldSpace L n k j)
    {ψ : P → PositiveEdge L n k j → Matrices.ComplexMatrix2}
    (h : Matrices.EmbeddedSubmanifold.IsC2Parametrization (restrictToPositiveEdges '' N) O ψ) :
    IsFieldParametrization N O fun p => fieldOfPositiveValues (ψ p) := by
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨V, hV, e⟩ := h.2.2.2.1 hp
    show fieldOfPositiveValues (ψ p) ∈ N
    rw [← e, fieldOfPositiveValues_restrictToPositiveEdges (hNc hV)]
    exact hV
  · simpa only [restrictToPositiveEdges_fieldOfPositiveValues] using h
theorem paramEvaluationData_field {𝒳 : Set (Edge L n k j → Matrices.ComplexMatrix2)}
    (h𝒳 : IsFieldSubmanifold 𝒳) (hN : IsFieldSubmanifold N) (hsub : N ⊆ 𝒳)
    (hF : Matrices.EmbeddedSubmanifold.IsC2OnCharted (restrictToPositiveEdges '' 𝒳)
      fun w => F (fieldOfPositiveValues w))
    (hφ : IsFieldParametrization N O φ) (hz : z ∈ O) :
    (fieldCurveData L n k j).ParametrizationData N F φ z (tangentMapOfValues (φ z) ∘ₗ
      (fderiv ℝ (fun p => restrictToPositiveEdges (φ p)) z :
        P →ₗ[ℝ] PositiveEdge L n k j → Matrices.ComplexMatrix2)) :=
  paramEvaluationData_of_values hN.1 hφ hz
    (Matrices.EmbeddedSubmanifold.paramEvaluationData (IsFieldSubmanifold.isChartedSubset h𝒳)
      (image_mono hsub) hF hφ.2 hz)
end Tower
namespace Tower
theorem RestrictionHessian.proof : RestrictionHessian.Statement := by
  refine ⟨?_, ?_⟩
  · intro E _ _ 𝒳 N F h𝒳 hN hF
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro P _ _ _ O φ z hφ hz
      exact (Matrices.EmbeddedSubmanifold.paramEvaluationData h𝒳 hN.1 hF hφ hz).hessianViaParametrization
    · intro x hx
      obtain ⟨c, u, hu, e⟩ := hN.2 x hx
      exact ⟨c.dim, c.source, c.param, u, c.isC2Parametrization, hu, e⟩
    · intro x hcr
      obtain ⟨c, u, hu, rfl⟩ := hN.2 x hcr.1
      exact (Matrices.EmbeddedSubmanifold.paramEvaluationData h𝒳 hN.1 hF c.isC2Parametrization
        hu).hasUniqueHessianAt hcr
    · intro c u₀ s hp hcr
      obtain ⟨O, hO0, hpar⟩ := c.exists_coordinatePlane_parametrization hN.1 hp
      have hu : u₀ ∈ c.source := by
        obtain ⟨W, -, h, hs, -⟩ := hp
        exact hs h
      exact (Matrices.EmbeddedSubmanifold.paramEvaluationData h𝒳 hN.1 hF hpar
        hO0).hessianEqPartialsMatrix
        (ψ := c.param) hcr ((hF c).contDiffAt (c.isOpen_source.mem_nhds hu))
  · intro L n k j _ 𝒳 N F h𝒳 hN hsub hF
    have mN := IsFieldSubmanifold.isChartedSubset hN
    have hNc := hN.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro P _ _ _ O φ z hφ hz
      have H := paramEvaluationData_field h𝒳 hN hsub hF hφ hz
      refine ⟨_, fun h => ?_, H.hessianViaParametrization⟩
      obtain ⟨I, -, -, -, ht⟩ := H.line h
      exact ht.symm
    · intro x hx
      obtain ⟨c, u, hu, e⟩ := mN _ (mem_image_of_mem restrictToPositiveEdges hx)
      refine ⟨c.dim, c.source, fun u => fieldOfPositiveValues (c.param u), u,
        isFieldParametrization_of_values hNc c.isC2Parametrization, hu, ?_⟩
      show fieldOfPositiveValues (c.param u) = x
      rw [e, fieldOfPositiveValues_restrictToPositiveEdges (hNc hx)]
    · intro x hcr
      obtain ⟨c, u, hu, e⟩ := mN _ (mem_image_of_mem restrictToPositiveEdges hcr.1)
      have e' : fieldOfPositiveValues (c.param u) = x := by
        rw [e, fieldOfPositiveValues_restrictToPositiveEdges (hNc hcr.1)]
      subst e'
      exact (paramEvaluationData_field (φ := fun u => fieldOfPositiveValues (c.param u))
        h𝒳 hN hsub hF (isFieldParametrization_of_values hNc c.isC2Parametrization)
        hu).hasUniqueHessianAt hcr
    · intro c u₀ s hp hcr
      obtain ⟨O, hO0, hpar⟩ := c.exists_coordinatePlane_parametrization (image_mono hsub) hp
      have hu : u₀ ∈ c.source := by
        obtain ⟨W, -, h, hs, -⟩ := hp
        exact hs h
      exact (paramEvaluationData_field (φ := fun p : RestrictionHessian.coordinateSubspace s =>
          fieldOfPositiveValues (c.param (u₀ + p)))
        h𝒳 hN hsub hF (isFieldParametrization_of_values hNc hpar) hO0).hessianEqPartialsMatrix
        (ψ := fun u => fieldOfPositiveValues (c.param u)) hcr
        ((hF c).contDiffAt (c.isOpen_source.mem_nhds hu))
end Tower
end YangMills.Construction
end

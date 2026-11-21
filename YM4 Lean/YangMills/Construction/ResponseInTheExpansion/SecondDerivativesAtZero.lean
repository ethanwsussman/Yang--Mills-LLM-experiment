import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
namespace SecondOrder
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
def hessianAtZero (f : E → ℝ) (p q : E) : ℝ := fderiv ℝ (fderiv ℝ f) 0 p q
theorem eventually_differentiableAt_of_contDiffAt {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℝ f y :=
  (hf.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
theorem differentiableAt_fderiv_of_contDiffAt {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    DifferentiableAt ℝ (fderiv ℝ f) 0 :=
  (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
theorem hessianAtZero_add_left {f : E → ℝ} (p p' q : E) :
    hessianAtZero f (p + p') q = hessianAtZero f p q + hessianAtZero f p' q := by
  simp [hessianAtZero]
theorem hessianAtZero_add_right {f : E → ℝ} (p q q' : E) :
    hessianAtZero f p (q + q') = hessianAtZero f p q + hessianAtZero f p q' := by
  simp [hessianAtZero]
theorem hessianAtZero_smul_left {f : E → ℝ} (r : ℝ) (p q : E) :
    hessianAtZero f (r • p) q = r * hessianAtZero f p q := by
  simp [hessianAtZero]
theorem hessianAtZero_smul_right {f : E → ℝ} (r : ℝ) (p q : E) :
    hessianAtZero f p (r • q) = r * hessianAtZero f p q := by
  simp [hessianAtZero]
theorem hessianAtZero_sum_left {ι : Type*} {f : E → ℝ} (s : Finset ι) (p : ι → E) (q : E) :
    hessianAtZero f (∑ i ∈ s, p i) q = ∑ i ∈ s, hessianAtZero f (p i) q := by
  simp [hessianAtZero, map_sum]
theorem hessianAtZero_sum_right {ι : Type*} {f : E → ℝ} (s : Finset ι) (p : E) (q : ι → E) :
    hessianAtZero f p (∑ i ∈ s, q i) = ∑ i ∈ s, hessianAtZero f p (q i) := by
  simp [hessianAtZero, map_sum]
theorem hessianAtZero_comm {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) (p q : E) :
    hessianAtZero f p q = hessianAtZero f q p :=
  (hf.isSymmSndFDerivAt (by simp)).eq p q
theorem hessianAtZero_comp_clm {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) (ι : E' →L[ℝ] E) (u v : E') :
    hessianAtZero (fun x => f (ι x)) u v = hessianAtZero f (ι u) (ι v) := by
  have hev : fderiv ℝ (fun x => f (ι x)) =ᶠ[𝓝 0] fun x => (fderiv ℝ f (ι x)).comp ι := by
    have h1 : ∀ᶠ x in 𝓝 (0 : E'), DifferentiableAt ℝ f (ι x) :=
      ι.continuous.continuousAt.eventually (by simpa using eventually_differentiableAt_of_contDiffAt hf)
    filter_upwards [h1] with x hx
    exact (hx.hasFDerivAt.comp x ι.hasFDerivAt).fderiv
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) (ι 0) := by
    simpa using (differentiableAt_fderiv_of_contDiffAt hf).hasFDerivAt
  have h2 : HasFDerivAt (fun x => fderiv ℝ f (ι x)) ((fderiv ℝ (fderiv ℝ f) 0).comp ι) (0 : E') :=
    hD.comp (0 : E') ι.hasFDerivAt
  set P : (E →L[ℝ] ℝ) →L[ℝ] (E' →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ E' E ℝ).flip ι with hP
  have h3 : HasFDerivAt (fun x => P (fderiv ℝ f (ι x))) (P.comp ((fderiv ℝ (fderiv ℝ f) 0).comp ι)) (0 : E') :=
    P.hasFDerivAt.comp (0 : E') h2
  unfold hessianAtZero
  rw [hev.fderiv_eq]
  have h4 : (fun x => (fderiv ℝ f (ι x)).comp ι) = fun x => P (fderiv ℝ f (ι x)) := by
    funext x
    simp [hP]
  rw [h4, h3.fderiv]
  simp [hP]
theorem deriv_deriv_eq_hessianAtZero {g : ℝ → ℝ} (hg : ContDiffAt ℝ 2 g 0) :
    deriv (deriv g) 0 = hessianAtZero g 1 1 := by
  have e : deriv g = fun x => fderiv ℝ g x 1 := by
    funext x
    rfl
  have h := (differentiableAt_fderiv_of_contDiffAt hg).hasFDerivAt.hasDerivAt
  have h2 := h.clm_apply (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  rw [e]
  have := h2.deriv
  simpa [hessianAtZero] using this
theorem contDiffAt_along_line {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) (p : E) :
    ContDiffAt ℝ 2 (fun τ : ℝ => f (τ • p)) 0 := by
  have h : ContDiffAt ℝ 2 (fun τ : ℝ => τ • p) 0 := contDiffAt_id.smul contDiffAt_const
  have h0 : ContDiffAt ℝ 2 f ((0 : ℝ) • p) := by simpa using hf
  exact h0.comp (0 : ℝ) h
theorem deriv_deriv_along_line {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) (p : E) :
    deriv (deriv fun τ : ℝ => f (τ • p)) 0 = hessianAtZero f p p := by
  rw [deriv_deriv_eq_hessianAtZero (contDiffAt_along_line hf p)]
  have := hessianAtZero_comp_clm hf ((ContinuousLinearMap.id ℝ ℝ).smulRight p) (1 : ℝ) (1 : ℝ)
  simpa using this
theorem differentiableAt_deriv_of_contDiffAt {γ : ℝ → E} (hγ : ContDiffAt ℝ 2 γ 0) :
    DifferentiableAt ℝ (deriv γ) 0 := by
  have e : deriv γ = fun x => fderiv ℝ γ x 1 := by
    funext x
    rfl
  rw [e]
  exact ((hγ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
    (differentiableAt_const _)
theorem deriv_deriv_along_curve {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) (hz : fderiv ℝ f 0 = 0) {γ : ℝ → E}
    (hγ : ContDiffAt ℝ 2 γ 0) (h0 : γ 0 = 0) :
    deriv (deriv fun τ => f (γ τ)) 0 = hessianAtZero f (deriv γ 0) (deriv γ 0) := by
  have hγc : ContinuousAt γ 0 := hγ.continuousAt
  have h1 : ∀ᶠ τ in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (γ τ) :=
    hγc.eventually (by simpa [h0] using eventually_differentiableAt_of_contDiffAt hf)
  have h2 : ∀ᶠ τ in 𝓝 (0 : ℝ), DifferentiableAt ℝ γ τ :=
    (hγ.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have hev : deriv (fun τ => f (γ τ)) =ᶠ[𝓝 0] fun τ => fderiv ℝ f (γ τ) (deriv γ τ) := by
    filter_upwards [h1, h2] with τ a b
    exact (a.hasFDerivAt.comp_hasDerivAt τ b.hasDerivAt).deriv
  rw [hev.deriv_eq]
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) (γ 0) := by
    simpa [h0] using (differentiableAt_fderiv_of_contDiffAt hf).hasFDerivAt
  have hg : HasDerivAt γ (deriv γ 0) 0 := (hγ.differentiableAt (by norm_num)).hasDerivAt
  have hc : HasDerivAt (fun τ => fderiv ℝ f (γ τ)) ((fderiv ℝ (fderiv ℝ f) 0) (deriv γ 0)) 0 :=
    hD.comp_hasDerivAt 0 hg
  have h3 := hc.clm_apply (differentiableAt_deriv_of_contDiffAt hγ).hasDerivAt
  rw [h3.deriv]
  simp [hessianAtZero, h0, hz]
theorem mixed_deriv_eq_hessianAtZero {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) (p q : E) :
    deriv (fun s : ℝ => deriv (fun s' : ℝ => f (s • p + s' • q)) 0) 0 = hessianAtZero f p q := by
  have hl : ContinuousAt (fun s : ℝ => s • p) 0 := (continuous_id.smul continuous_const).continuousAt
  have hl0 : (fun s : ℝ => s • p) 0 = 0 := zero_smul ℝ p
  have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (s • p) := by
    have := eventually_differentiableAt_of_contDiffAt hf
    rw [← hl0] at this
    exact hl.eventually this
  have hev : (fun s : ℝ => deriv (fun s' : ℝ => f (s • p + s' • q)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℝ f (s • p) q := by
    filter_upwards [h1] with s hs
    have hq : HasDerivAt (fun s' : ℝ => s • p + s' • q) q 0 := by
      have h3 : HasDerivAt (fun s' : ℝ => s' • q) ((1 : ℝ) • q) 0 := (hasDerivAt_id' (0 : ℝ)).smul_const q
      rw [one_smul] at h3
      exact h3.const_add (s • p)
    have h2 : HasFDerivAt f (fderiv ℝ f (s • p)) (s • p + (0 : ℝ) • q) := by
      rw [zero_smul, add_zero]
      exact hs.hasFDerivAt
    exact (HasFDerivAt.comp_hasDerivAt (f := fun s' : ℝ => s • p + s' • q) (0 : ℝ) h2 hq).deriv
  rw [hev.deriv_eq]
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) ((0 : ℝ) • p) := by
    rw [zero_smul]
    exact (differentiableAt_fderiv_of_contDiffAt hf).hasFDerivAt
  have hp : HasDerivAt (fun s : ℝ => s • p) p 0 := by
    have h3 : HasDerivAt (fun s : ℝ => s • p) ((1 : ℝ) • p) 0 := (hasDerivAt_id' (0 : ℝ)).smul_const p
    rwa [one_smul] at h3
  have hc0 : HasDerivAt (fun s : ℝ => fderiv ℝ f (s • p)) (fderiv ℝ (fderiv ℝ f) 0 p) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => s • p) (0 : ℝ) hD hp
  have hc := hc0.clm_apply (hasDerivAt_const (0 : ℝ) q)
  rw [hc.deriv]
  simp [hessianAtZero]
structure SecondJet (g : ℝ → ℝ) (v0 v1 v2 : ℝ) : Prop where
  contDiffAt : ContDiffAt ℝ 2 g 0
  value : g 0 = v0
  firstDeriv : deriv g 0 = v1
  secondDeriv : deriv (deriv g) 0 = v2
theorem eventually_differentiableAt_real {g : ℝ → ℝ} (hg : ContDiffAt ℝ 2 g 0) :
    ∀ᶠ y in 𝓝 (0 : ℝ), DifferentiableAt ℝ g y :=
  eventually_differentiableAt_of_contDiffAt hg
theorem SecondJet.of_contDiffAt {g : ℝ → ℝ} (hg : ContDiffAt ℝ 2 g 0) :
    SecondJet g (g 0) (deriv g 0) (deriv (deriv g) 0) :=
  ⟨hg, rfl, rfl, rfl⟩
theorem SecondJet.add {g h : ℝ → ℝ} {a0 a1 a2 b0 b1 b2 : ℝ} (G : SecondJet g a0 a1 a2)
    (H : SecondJet h b0 b1 b2) :
    SecondJet (fun τ => g τ + h τ) (a0 + b0) (a1 + b1) (a2 + b2) := by
  have hev : deriv (fun τ => g τ + h τ) =ᶠ[𝓝 0] fun τ => deriv g τ + deriv h τ := by
    filter_upwards [eventually_differentiableAt_real G.contDiffAt,
      eventually_differentiableAt_real H.contDiffAt] with τ a b
    exact deriv_fun_add a b
  refine ⟨G.contDiffAt.add H.contDiffAt, by simp [G.value, H.value], ?_, ?_⟩
  · rw [hev.eq_of_nhds, G.firstDeriv, H.firstDeriv]
  · rw [hev.deriv_eq, deriv_fun_add (differentiableAt_deriv_of_contDiffAt G.contDiffAt)
      (differentiableAt_deriv_of_contDiffAt H.contDiffAt), G.secondDeriv, H.secondDeriv]
theorem SecondJet.mul {g h : ℝ → ℝ} {a0 a1 a2 b0 b1 b2 : ℝ} (G : SecondJet g a0 a1 a2)
    (H : SecondJet h b0 b1 b2) :
    SecondJet (fun τ => g τ * h τ) (a0 * b0) (a1 * b0 + a0 * b1) (a2 * b0 + 2 * a1 * b1 + a0 * b2) := by
  have hev : deriv (fun τ => g τ * h τ) =ᶠ[𝓝 0] fun τ => deriv g τ * h τ + g τ * deriv h τ := by
    filter_upwards [eventually_differentiableAt_real G.contDiffAt,
      eventually_differentiableAt_real H.contDiffAt] with τ a b
    exact deriv_fun_mul a b
  have dg : DifferentiableAt ℝ g 0 := G.contDiffAt.differentiableAt (by norm_num)
  have dh : DifferentiableAt ℝ h 0 := H.contDiffAt.differentiableAt (by norm_num)
  have dg' := differentiableAt_deriv_of_contDiffAt G.contDiffAt
  have dh' := differentiableAt_deriv_of_contDiffAt H.contDiffAt
  refine ⟨G.contDiffAt.mul H.contDiffAt, by simp [G.value, H.value], ?_, ?_⟩
  · rw [hev.eq_of_nhds, G.firstDeriv, H.firstDeriv, G.value, H.value]
  · have h3 := (dg'.hasDerivAt.fun_mul dh.hasDerivAt).fun_add (dg.hasDerivAt.fun_mul dh'.hasDerivAt)
    rw [hev.deriv_eq, h3.deriv, G.firstDeriv, H.firstDeriv, G.secondDeriv, H.secondDeriv, G.value, H.value]
    ring
theorem SecondJet.const (c : ℝ) : SecondJet (fun _ => c) c 0 0 := by
  refine ⟨contDiffAt_const, rfl, by simp, ?_⟩
  have : deriv (fun _ : ℝ => c) = fun _ => 0 := by
    funext x
    simp
  rw [this]
  simp
theorem SecondJet.const_mul {g : ℝ → ℝ} {a0 a1 a2 : ℝ} (c : ℝ) (G : SecondJet g a0 a1 a2) :
    SecondJet (fun τ => c * g τ) (c * a0) (c * a1) (c * a2) := by
  have := (SecondJet.const c).mul G
  convert this using 1 <;> ring
theorem SecondJet.sub {g h : ℝ → ℝ} {a0 a1 a2 b0 b1 b2 : ℝ} (G : SecondJet g a0 a1 a2)
    (H : SecondJet h b0 b1 b2) :
    SecondJet (fun τ => g τ - h τ) (a0 - b0) (a1 - b1) (a2 - b2) := by
  have := G.add (H.const_mul (-1))
  convert this using 1
  · funext τ
    ring
  · ring
  · ring
  · ring
theorem SecondJet.sum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℝ} {a0 a1 a2 : ι → ℝ}
    (G : ∀ i ∈ s, SecondJet (g i) (a0 i) (a1 i) (a2 i)) :
    SecondJet (fun τ => ∑ i ∈ s, g i τ) (∑ i ∈ s, a0 i) (∑ i ∈ s, a1 i) (∑ i ∈ s, a2 i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SecondJet.const 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (G i (Finset.mem_insert_self i s)).add (ih fun j hj => G j (Finset.mem_insert_of_mem hj))
theorem SecondJet.cos_mul (p : ℝ) : SecondJet (fun τ => Real.cos (τ * p)) 1 0 (-p ^ 2) := by
  have h1 : ∀ τ : ℝ, HasDerivAt (fun τ => Real.cos (τ * p)) (-Real.sin (τ * p) * p) τ := fun τ => by
    simpa using ((hasDerivAt_id' τ).mul_const p).cos
  have e1 : deriv (fun τ => Real.cos (τ * p)) = fun τ => -Real.sin (τ * p) * p :=
    funext fun τ => (h1 τ).deriv
  have h2 : HasDerivAt (fun τ => -Real.sin (τ * p) * p) (-(Real.cos ((0 : ℝ) * p) * p) * p) 0 := by
    simpa using (((hasDerivAt_id' (0 : ℝ)).mul_const p).sin.fun_neg).mul_const p
  refine ⟨by fun_prop, by simp, ?_, ?_⟩
  · rw [e1]
    simp
  · rw [e1, h2.deriv]
    simp
    ring
theorem SecondJet.sin_mul (p : ℝ) : SecondJet (fun τ => Real.sin (τ * p)) 0 p 0 := by
  have h1 : ∀ τ : ℝ, HasDerivAt (fun τ => Real.sin (τ * p)) (Real.cos (τ * p) * p) τ := fun τ => by
    simpa using ((hasDerivAt_id' τ).mul_const p).sin
  have e1 : deriv (fun τ => Real.sin (τ * p)) = fun τ => Real.cos (τ * p) * p :=
    funext fun τ => (h1 τ).deriv
  have h2 : HasDerivAt (fun τ => Real.cos (τ * p) * p) (-(Real.sin ((0 : ℝ) * p) * p) * p) 0 := by
    simpa using (((hasDerivAt_id' (0 : ℝ)).mul_const p).cos).mul_const p
  refine ⟨by fun_prop, by simp, ?_, ?_⟩
  · rw [e1]
    simp
  · rw [e1, h2.deriv]
    simp
theorem SecondJet.sqrt {N : ℝ → ℝ} {n2 : ℝ} (G : SecondJet N 1 0 n2) (hN : ∀ τ, 0 ≤ N τ) :
    SecondJet (fun τ => Real.sqrt (N τ)) 1 0 (n2 / 2) := by
  have hr : ContDiffAt ℝ 2 (fun τ => Real.sqrt (N τ)) 0 := by
    refine G.contDiffAt.sqrt ?_
    rw [G.value]
    norm_num
  have h0 : Real.sqrt (N 0) = 1 := by rw [G.value, Real.sqrt_one]
  have J := SecondJet.of_contDiffAt hr
  have M := J.mul J
  have e : (fun τ => Real.sqrt (N τ) * Real.sqrt (N τ)) = N := funext fun τ => Real.mul_self_sqrt (hN τ)
  rw [e] at M
  have a1 := M.firstDeriv
  have a2 := M.secondDeriv
  rw [G.firstDeriv] at a1
  rw [G.secondDeriv] at a2
  simp only [h0] at a1 a2
  have b1 : deriv (fun τ => Real.sqrt (N τ)) 0 = 0 := by linarith
  refine ⟨hr, h0, b1, ?_⟩
  rw [b1] at a2
  linarith
theorem SecondJet.rotationFit {ι : Type*} (s : Finset ι) (w p : ι → ℝ) (b : ℝ) (hw : ∑ k ∈ s, w k = 1) :
    SecondJet (fun τ => Real.sqrt ((∑ k ∈ s, w k * Real.cos (τ * p k)) ^ 2 +
        (∑ k ∈ s, w k * Real.sin (τ * p k)) ^ 2) -
      ((∑ k ∈ s, w k * Real.cos (τ * p k)) * Real.cos (τ * b) +
        (∑ k ∈ s, w k * Real.sin (τ * p k)) * Real.sin (τ * b))) 0 0
      ((∑ k ∈ s, w k * p k - b) ^ 2) := by
  set m2 := ∑ k ∈ s, w k * p k ^ 2 with hm2
  set m1 := ∑ k ∈ s, w k * p k with hm1
  have C : SecondJet (fun τ => ∑ k ∈ s, w k * Real.cos (τ * p k)) 1 0 (-m2) := by
    have := SecondJet.sum s (g := fun k τ => w k * Real.cos (τ * p k)) (a0 := fun k => w k * 1)
      (a1 := fun k => w k * 0) (a2 := fun k => w k * (-p k ^ 2))
      fun k _ => (SecondJet.cos_mul (p k)).const_mul (w k)
    convert this using 1
    · simp [hw]
    · simp
    · simp [hm2, Finset.sum_neg_distrib]
  have S : SecondJet (fun τ => ∑ k ∈ s, w k * Real.sin (τ * p k)) 0 m1 0 := by
    have := SecondJet.sum s (g := fun k τ => w k * Real.sin (τ * p k)) (a0 := fun k => w k * 0)
      (a1 := fun k => w k * p k) (a2 := fun k => w k * 0)
      fun k _ => (SecondJet.sin_mul (p k)).const_mul (w k)
    convert this using 1
    · simp
    · simp
  have N0 := (C.mul C).add (S.mul S)
  have N : SecondJet (fun τ => (∑ k ∈ s, w k * Real.cos (τ * p k)) ^ 2 +
      (∑ k ∈ s, w k * Real.sin (τ * p k)) ^ 2) 1 0 (-2 * m2 + 2 * m1 ^ 2) := by
    convert N0 using 1
    · funext τ
      ring
    · ring
    · ring
    · ring
  have R := N.sqrt fun τ => by positivity
  have P := (C.mul (SecondJet.cos_mul b)).add (S.mul (SecondJet.sin_mul b))
  have := R.sub P
  convert this using 1
  · ring
  · ring
  · ring
theorem deriv_deriv_nonneg_of_nonneg {h : ℝ → ℝ} (hh : ContDiffAt ℝ 2 h 0) (h0 : h 0 = 0)
    (hpos : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 ≤ h τ) :
    0 ≤ deriv (deriv h) 0 := by
  by_contra hneg
  rw [not_le] at hneg
  have hmin : IsLocalMin h 0 := by
    filter_upwards [hpos] with τ hτ
    rw [h0]
    exact hτ
  have hd : deriv h 0 = 0 := hmin.deriv_eq_zero
  set ε := -(deriv (deriv h) 0) / 4 with hε
  have hεp : 0 < ε := by rw [hε]; linarith
  have Q : SecondJet (fun τ : ℝ => τ * τ) 0 0 2 := by
    have hid : SecondJet (fun τ : ℝ => τ) 0 1 0 := by
      refine ⟨contDiffAt_id, rfl, by simp, ?_⟩
      have : deriv (fun τ : ℝ => τ) = fun _ => 1 := by
        funext x
        simp
      rw [this]
      simp
    have := hid.mul hid
    convert this using 1 <;> norm_num
  have G := (SecondJet.of_contDiffAt hh).add (Q.const_mul ε)
  have hmax : IsLocalMax (fun τ => h τ + ε * (τ * τ)) 0 := by
    refine isLocalMax_of_deriv_deriv_neg ?_ ?_ G.contDiffAt.continuousAt
    · rw [G.secondDeriv]
      rw [hε]
      linarith
    · rw [G.firstDeriv, hd]
      ring
  have hcl : ∀ᶠ τ in 𝓝 (0 : ℝ), ε * (τ * τ) ≤ 0 := by
    filter_upwards [hmax, hpos] with τ a b
    have : h 0 + ε * (0 * 0) = 0 := by rw [h0]; ring
    simp only [this] at a
    linarith
  have hne : ∀ᶠ τ in 𝓝[≠] (0 : ℝ), τ ≠ 0 := self_mem_nhdsWithin
  obtain ⟨τ, a, b⟩ := ((hcl.filter_mono nhdsWithin_le_nhds).and hne).exists
  have : 0 < ε * (τ * τ) := mul_pos hεp (mul_self_pos.mpr b)
  linarith
end SecondOrder
end YangMills.Construction
end

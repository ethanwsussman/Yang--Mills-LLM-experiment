import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenAtATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.IntegralOfASmoothFamilyProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open Set
set_option linter.unusedSectionVars false
namespace YangMills.Construction.IteratedDerivative
namespace RayGradient
section General
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem fderiv_clm_apply_const {G : E → E →L[ℝ] ℝ} {q y : E} (x : E) (hG : DifferentiableAt ℝ G q) :
    fderiv ℝ (fun p => G p x) q y = fderiv ℝ G q y x := by
  have := (hG.hasFDerivAt.clm_apply (hasFDerivAt_const x q)).fderiv
  rw [this]
  simp
theorem natCast_le_natCast_withTop {n m : ℕ} (hnm : n ≤ m) :
    ((n : ℕ) : WithTop ℕ∞) ≤ ((m : ℕ) : WithTop ℕ∞) := by
  exact_mod_cast hnm
theorem eventually_contDiffAt {f : E → ℝ} {x : E} (n : ℕ) (hf : ContDiffAt ℝ (n : WithTop ℕ∞) f x) :
    ∀ᶠ q in 𝓝 x, ContDiffAt ℝ (n : WithTop ℕ∞) f q :=
  hf.eventually (by simp)
theorem derivAlong_fderiv_apply_eventuallyEq (R : DerivAlongRules E (E →L[ℝ] ℝ)) (f : E → ℝ) (y : E)
    (l : List E) (x : E) (hf : ContDiffAt ℝ ((l.length + 1 : ℕ) : WithTop ℕ∞) f x) :
    derivAlong (fun z => fderiv ℝ f z y) l =ᶠ[𝓝 x] fun x' => derivAlong (fderiv ℝ f) l x' y := by
  induction l generalizing x with
  | nil => exact Filter.Eventually.of_forall fun _ => rfl
  | cons u l ih =>
    filter_upwards [(eventually_contDiffAt _ hf).eventually_nhds] with q hq
    have hq0 := hq.self_of_nhds
    have heq := ih q (hq0.of_le (natCast_le_natCast_withTop (by simp)))
    have hg : ContDiffAt ℝ ((1 + l.length : ℕ) : WithTop ℕ∞) (fderiv ℝ f) q :=
      hq0.fderiv_right (by norm_cast; simp; omega)
    have hd : DifferentiableAt ℝ (derivAlong (fderiv ℝ f) l) q :=
      (R.contDiffAt _ q 1 l hg).differentiableAt (by simp)
    simp only [derivAlong]
    rw [heq.fderiv_eq]
    exact fderiv_clm_apply_const y hd
def gradPairing (f : E → ℝ) (S ℓ : E →L[ℝ] E) (l : List E) (q : E) : ℝ :=
  derivAlong (fderiv ℝ f) l (S q) (ℓ q)
theorem gradPairing_eq_derivAlong_append (R : DerivAlongRules E (E →L[ℝ] ℝ)) (R' : DerivAlongRules E ℝ)
    (f : E → ℝ) (S ℓ : E →L[ℝ] E) (l : List E) (q : E)
    (hf : ContDiffAt ℝ ((l.length + 1 : ℕ) : WithTop ℕ∞) f (S q)) :
    gradPairing f S ℓ l q = derivAlong f (l ++ [ℓ q]) (S q) := by
  rw [R'.append]
  exact ((derivAlong_fderiv_apply_eventuallyEq R f (ℓ q) l (S q) hf).self_of_nhds).symm
theorem contDiffAt_gradPairing (R : DerivAlongRules E (E →L[ℝ] ℝ)) (f : E → ℝ) (S ℓ : E →L[ℝ] E)
    (l : List E) (q : E) (n : ℕ) (hf : ContDiffAt ℝ ((n + l.length + 1 : ℕ) : WithTop ℕ∞) f (S q)) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (gradPairing f S ℓ l) q := by
  have hg : ContDiffAt ℝ ((n + l.length : ℕ) : WithTop ℕ∞) (fderiv ℝ f) (S q) :=
    hf.fderiv_right (by norm_cast)
  have h1 := R.contDiffAt _ _ n l hg
  have h2 : ContDiffAt ℝ (n : WithTop ℕ∞) (fun q => derivAlong (fderiv ℝ f) l (S q)) q :=
    ContDiffAt.comp q h1 S.contDiff.contDiffAt
  exact h2.clm_apply ℓ.contDiff.contDiffAt
theorem fderiv_gradPairing (R : DerivAlongRules E (E →L[ℝ] ℝ)) (f : E → ℝ) (S ℓ : E →L[ℝ] E)
    (l : List E) (q u : E) (hf : ContDiffAt ℝ ((l.length + 2 : ℕ) : WithTop ℕ∞) f (S q)) :
    fderiv ℝ (gradPairing f S ℓ l) q u =
      gradPairing f S ℓ (S u :: l) q + derivAlong (fderiv ℝ f) l (S q) (ℓ u) := by
  have hg : ContDiffAt ℝ ((1 + l.length : ℕ) : WithTop ℕ∞) (fderiv ℝ f) (S q) :=
    hf.fderiv_right (by norm_cast; omega)
  have hd : DifferentiableAt ℝ (derivAlong (fderiv ℝ f) l) (S q) :=
    (R.contDiffAt _ _ 1 l hg).differentiableAt (by simp)
  have h1 : HasFDerivAt (fun q => derivAlong (fderiv ℝ f) l (S q))
      ((fderiv ℝ (derivAlong (fderiv ℝ f) l) (S q)).comp S) q :=
    hd.hasFDerivAt.comp q S.hasFDerivAt
  have h2 := h1.clm_apply ℓ.hasFDerivAt
  have heq : gradPairing f S ℓ l = fun q => derivAlong (fderiv ℝ f) l (S q) (ℓ q) := rfl
  rw [heq, h2.fderiv]
  simp [gradPairing, derivAlong]
  ring
theorem derivAlong_gradPairing_eventuallyEq (R : DerivAlongRules E (E →L[ℝ] ℝ))
    (R' : DerivAlongRules E ℝ) (f : E → ℝ) (S ℓ : E →L[ℝ] E)
    (m : List E) : ∀ (l : List E) (p : E), (∀ u ∈ m, S u = u ∧ ℓ u = 0) →
    ContDiffAt ℝ ((m.length + l.length + 2 : ℕ) : WithTop ℕ∞) f (S p) →
    derivAlong (gradPairing f S ℓ l) m =ᶠ[𝓝 p] gradPairing f S ℓ (m ++ l) := by
  induction m using List.reverseRecOn with
  | nil => intro l p _ _; exact Filter.EventuallyEq.rfl
  | append_singleton m u ih =>
    intro l p hm hf
    have hu := hm u (by simp)
    have hm' : ∀ u ∈ m, S u = u ∧ ℓ u = 0 := fun u' hu' => hm u' (by simp [hu'])
    have hlen : (m ++ [u]).length = m.length + 1 := by simp
    rw [hlen] at hf
    have hcS : ContinuousAt S p := S.continuous.continuousAt
    have hev := hcS.eventually (eventually_contDiffAt _ hf)
    have e1 : derivAlong (gradPairing f S ℓ l) [u] =ᶠ[𝓝 p] gradPairing f S ℓ (u :: l) := by
      filter_upwards [hev] with q hq
      have hq' : ContDiffAt ℝ ((l.length + 2 : ℕ) : WithTop ℕ∞) f (S q) :=
        hq.of_le (natCast_le_natCast_withTop (by omega))
      simp only [derivAlong]
      rw [fderiv_gradPairing R f S ℓ l q u hq', hu.1, hu.2]
      simp
    rw [R'.append]
    have e2 := R'.congr _ _ p m e1
    have e3 := ih (u :: l) p hm' (by
      have : m.length + (u :: l).length + 2 = m.length + 1 + l.length + 2 := by simp; ring
      rw [this]; exact hf)
    have e4 : (m ++ [u]) ++ l = m ++ u :: l := by simp
    rw [e4]
    exact e2.trans e3
theorem derivAlong_gradPairing_singleton_eventuallyEq (R : DerivAlongRules E (E →L[ℝ] ℝ)) (f : E → ℝ)
    (S ℓ : E →L[ℝ] E) (p u : E) (hf : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) f (S p)) :
    derivAlong (gradPairing f S ℓ []) [u] =ᶠ[𝓝 p]
      fun q => gradPairing f S ℓ [S u] q + fderiv ℝ f (S q) (ℓ u) := by
  have hcS : ContinuousAt S p := S.continuous.continuousAt
  filter_upwards [hcS.eventually (eventually_contDiffAt _ hf)] with q hq
  simp only [derivAlong]
  exact fderiv_gradPairing R f S ℓ [] q u hq
theorem contDiffAt_fderiv_comp_apply (f : E → ℝ) (S : E →L[ℝ] E) (y p : E) (n : ℕ)
    (hf : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f (S p)) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (fun q => fderiv ℝ f (S q) y) p := by
  have hg : ContDiffAt ℝ (n : WithTop ℕ∞) (fderiv ℝ f) (S p) := hf.fderiv_right (by norm_cast)
  have h2 : ContDiffAt ℝ (n : WithTop ℕ∞) (fun q => fderiv ℝ f (S q)) p :=
    ContDiffAt.comp p hg S.contDiff.contDiffAt
  exact h2.clm_apply contDiffAt_const
theorem derivAlong_fderiv_comp_apply (R' : DerivAlongRules E ℝ)
    (hA : ∀ (f : E → ℝ) (A : E →L[ℝ] E) (p₀ t : E) (l : List E),
      ContDiffAt ℝ (l.length : WithTop ℕ∞) f (p₀ + A t) →
      derivAlong (fun t' => f (p₀ + A t')) l t = derivAlong f (l.map A) (p₀ + A t))
    (f : E → ℝ) (S : E →L[ℝ] E) (y p : E) (l : List E) (hl : ∀ u ∈ l, S u = u)
    (hf : ContDiffAt ℝ ((l.length + 1 : ℕ) : WithTop ℕ∞) f (S p)) :
    derivAlong (fun q => fderiv ℝ f (S q) y) l p = derivAlong f (l ++ [y]) (S p) := by
  have hs : ContDiffAt ℝ (l.length : WithTop ℕ∞) (fun x => fderiv ℝ f x y) (0 + S p) := by
    rw [zero_add]
    exact (hf.fderiv_right (m := l.length) (by norm_cast)).clm_apply contDiffAt_const
  have := hA (fun x => fderiv ℝ f x y) S 0 p l hs
  simp only [zero_add] at this
  rw [this, R'.append]
  have hm : l.map S = l := by
    conv_rhs => rw [← List.map_id l]
    exact List.map_congr_left hl
  rw [hm]
  rfl
end General
section Ray
variable {ι B T : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
def scaleVariables (ι B T : Type) [Fintype ι] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup T] [NormedSpace ℝ T] (v : ℝ) : ((ι → B) × T) →L[ℝ] ((ι → B) × T) :=
  (v • ContinuousLinearMap.fst ℝ (ι → B) T).prod (ContinuousLinearMap.snd ℝ (ι → B) T)
def projectVariable (T : Type) [NormedAddCommGroup T] [NormedSpace ℝ T] (b : ι) :
    ((ι → B) × T) →L[ℝ] ((ι → B) × T) :=
  (ContinuousLinearMap.inl ℝ (ι → B) T).comp ((ContinuousLinearMap.single ℝ (fun _ : ι => B) b).comp
    ((ContinuousLinearMap.proj b).comp (ContinuousLinearMap.fst ℝ (ι → B) T)))
theorem scaleVariables_apply (v : ℝ) (p : (ι → B) × T) : scaleVariables ι B T v p = (v • p.1, p.2) := rfl
theorem projectVariable_apply (b : ι) (p : (ι → B) × T) :
    projectVariable T b p = (Pi.single b (p.1 b), 0) := rfl
def rayIntegrand (f : (ι → B) × T → ℝ) (b : ι) (z : ℝ × ((ι → B) × T)) : ℝ :=
  gradPairing f (scaleVariables ι B T z.1) (projectVariable T b) [] z.2
theorem contDiffAt_rayIntegrand (f : (ι → B) × T → ℝ) (b : ι) (v : ℝ) (p : (ι → B) × T) (n : ℕ)
    (hf : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f (v • p.1, p.2)) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (rayIntegrand f b) (v, p) := by
  have hg : ContDiffAt ℝ (n : WithTop ℕ∞) (fderiv ℝ f) (v • p.1, p.2) := hf.fderiv_right (by norm_cast)
  have hσ : ContDiffAt ℝ (n : WithTop ℕ∞) (fun z : ℝ × ((ι → B) × T) => (z.1 • z.2.1, z.2.2)) (v, p) :=
    ContDiff.contDiffAt (by fun_prop)
  have h2 : ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun z : ℝ × ((ι → B) × T) => fderiv ℝ f (z.1 • z.2.1, z.2.2)) (v, p) :=
    ContDiffAt.comp (v, p) hg hσ
  have h3 : ContDiffAt ℝ (n : WithTop ℕ∞) (fun z : ℝ × ((ι → B) × T) => projectVariable T b z.2) (v, p) :=
    ContDiff.contDiffAt (((projectVariable (ι := ι) (B := B) T b).contDiff (n := n)).comp contDiff_snd)
  exact h2.clm_apply h3
theorem rayGradientSum_eq_sum_integral (f : (ι → B) × T → ℝ) (Q : Finset ι) :
    rayGradientSum f Q = fun p => ∑ b ∈ Q, ∫ v in (0 : ℝ)..1, rayIntegrand f b (v, p) := rfl
theorem derivAlong_finset_sum {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R' : DerivAlongRules E ℝ) (Q : Finset κ) (g : κ → E → ℝ) (p : E) (l : List E)
    (hg : ∀ b ∈ Q, ContDiffAt ℝ (l.length : WithTop ℕ∞) (g b) p) :
    derivAlong (fun q => ∑ b ∈ Q, g b q) l p = ∑ b ∈ Q, derivAlong (g b) l p := by apply _root_.YangMills.Construction.Interpolation.AtTop.derivAlong_sum <;> assumption
theorem abs_derivAlong_segment_le (R' : DerivAlongRules ((ι → B) × T) ℝ) (f : (ι → B) × T → ℝ)
    (η : ι → B) (l : List ((ι → B) × T)) (C₀ : ℝ) (G : ι → ℝ) (hG : ∀ b', 0 ≤ G b')
    (hs : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ((l.length + 1 : ℕ) : WithTop ℕ∞) f (v • η, 0))
    (h0 : |derivAlong f l (0, 0)| ≤ C₀)
    (h1 : ∀ v ∈ Icc (0 : ℝ) 1, ∀ b',
      |derivAlong f (variableDirection T (Pi.single b' (η b')) :: l) (v • η, 0)| ≤ G b')
    (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
    |derivAlong f l (v • η, 0)| ≤ C₀ + ∑ b', G b' := by
  set g : ℝ → ℝ := fun u => derivAlong f l (u • η, 0) with hgdef
  set g' : ℝ → ℝ := fun u =>
    ∑ b', derivAlong f (variableDirection T (Pi.single b' (η b')) :: l) (u • η, 0) with hg'
  have hline : ∀ u : ℝ, HasDerivAt (fun u : ℝ => ((u • η, 0) : (ι → B) × T)) (η, 0) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => u • η) η u := by
      simpa using (hasDerivAt_id u).smul_const η
    exact h1.prodMk (hasDerivAt_const u (0 : T))
  have hsum : ((η, 0) : (ι → B) × T) = ∑ b', variableDirection T (Pi.single b' (η b')) := by
    have e1 : (∑ b', variableDirection T (Pi.single b' (η b') : ι → B)).1 = η := by
      simp only [variableDirection, Prod.fst_sum]
      exact Finset.univ_sum_single η
    have e2 : (∑ b', variableDirection T (Pi.single b' (η b') : ι → B)).2 = 0 := by
      simp [variableDirection, Prod.snd_sum]
    exact Prod.ext e1.symm e2.symm
  have hder : ∀ u ∈ Icc (0 : ℝ) v, HasDerivWithinAt g (g' u) (Icc 0 v) u := by
    intro u hu
    have hu1 : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans hv.2⟩
    have hd : DifferentiableAt ℝ (derivAlong f l) (u • η, 0) :=
      (R'.contDiffAt _ _ 1 l (by rw [add_comm]; exact hs u hu1)).differentiableAt (by simp)
    have h2 := hd.hasFDerivAt.comp_hasDerivAt u (hline u)
    have e : fderiv ℝ (derivAlong f l) (u • η, 0) (η, 0) = g' u := by
      rw [hsum, map_sum]
      rfl
    rw [e] at h2
    exact h2.hasDerivWithinAt
  have hb : ∀ u ∈ Ico (0 : ℝ) v, ‖g' u‖ ≤ ∑ b', G b' := by
    intro u hu
    have hu1 : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.le.trans hv.2⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
    rw [Real.norm_eq_abs]
    exact h1 u hu1 b'
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hder hb v (right_mem_Icc.2 hv.1)
  have hpos : 0 ≤ ∑ b', G b' := Finset.sum_nonneg fun b' _ => hG b'
  have hg0 : g 0 = derivAlong f l (0, 0) := by simp [hgdef]
  rw [Real.norm_eq_abs, sub_zero] at hmv
  have h3 : (∑ b', G b') * v ≤ ∑ b', G b' := by nlinarith [hv.1, hv.2]
  have h4 : |g v| ≤ |g v - g 0| + |g 0| := by
    have := abs_add_le (g v - g 0) (g 0)
    simpa using this
  rw [hg0] at h4 hmv
  change |g v| ≤ _
  linarith
theorem derivAlong_rayGradientSum (R' : DerivAlongRules ((ι → B) × T) ℝ)
    (hI : IntervalIntegralSmoothFamily)
    (f : (ι → B) × T → ℝ) (Q : Finset ι) (η : ι → B) (n : ℕ)
    (hs : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f (v • η, 0))
    (l : List ((ι → B) × T)) (hl : l.length ≤ n) :
    derivAlong (rayGradientSum f Q) l (η, 0) =
      ∑ b ∈ Q, ∫ v in (0 : ℝ)..1,
        derivAlong (gradPairing f (scaleVariables ι B T v) (projectVariable T b) []) l (η, 0) := by
  have hb := fun b => hI _ (rayIntegrand f b) (η, 0) n fun v hv =>
    contDiffAt_rayIntegrand f b v (η, 0) n (hs v hv)
  rw [rayGradientSum_eq_sum_integral,
    derivAlong_finset_sum R' Q _ _ _ fun b _ => (hb b).1.of_le (natCast_le_natCast_withTop hl)]
  exact Finset.sum_congr rfl fun b _ => (hb b).2 l hl
theorem contDiffAt_rayGradientSum (hI : IntervalIntegralSmoothFamily)
    (f : (ι → B) × T → ℝ) (Q : Finset ι) (η : ι → B) (n : ℕ)
    (hs : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f (v • η, 0)) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (rayGradientSum f Q) (η, 0) := by
  rw [rayGradientSum_eq_sum_integral]
  exact ContDiffAt.sum fun b _ =>
    (hI _ (rayIntegrand f b) (η, 0) n fun v hv => contDiffAt_rayIntegrand f b v (η, 0) n (hs v hv)).1
theorem parameterDirections_fixed (tl : List T) (v : ℝ) (b : ι) :
    ∀ u ∈ parameterDirections ι B tl, scaleVariables ι B T v u = u ∧ projectVariable T b u = 0 := by
  intro u hu
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hu
  refine ⟨?_, ?_⟩
  · rw [scaleVariables_apply]
    simp
  · rw [projectVariable_apply]
    simp
theorem length_parameterDirections (tl : List T) : (parameterDirections ι B tl).length = tl.length := by
  simp [parameterDirections]
variable (Rg : DerivAlongRules ((ι → B) × T) (((ι → B) × T) →L[ℝ] ℝ))
  (R' : DerivAlongRules ((ι → B) × T) ℝ)
  (hA : ∀ (f : (ι → B) × T → ℝ) (A : ((ι → B) × T) →L[ℝ] ((ι → B) × T)) (p₀ t : (ι → B) × T)
    (l : List ((ι → B) × T)), ContDiffAt ℝ (l.length : WithTop ℕ∞) f (p₀ + A t) →
    derivAlong (fun t' => f (p₀ + A t')) l t = derivAlong f (l.map A) (p₀ + A t))
include Rg R' in
theorem derivAlong_rayIntegrand_parameters (f : (ι → B) × T → ℝ) (η : ι → B) (tl : List T) (v : ℝ)
    (b : ι) (hf : ContDiffAt ℝ ((tl.length + 3 : ℕ) : WithTop ℕ∞) f (v • η, 0)) :
    derivAlong (gradPairing f (scaleVariables ι B T v) (projectVariable T b) [])
        (parameterDirections ι B tl) (η, 0) =
      derivAlong f (parameterDirections ι B tl ++ [variableDirection T (Pi.single b (η b))])
        (v • η, 0) := by
  have e := (derivAlong_gradPairing_eventuallyEq Rg R' f (scaleVariables ι B T v) (projectVariable T b)
    (parameterDirections ι B tl) [] (η, 0) (parameterDirections_fixed tl v b)
    (hf.of_le (natCast_le_natCast_withTop (by simp [length_parameterDirections])))).self_of_nhds
  rw [e, List.append_nil, gradPairing_eq_derivAlong_append Rg R' f _ _ _ _
    (hf.of_le (natCast_le_natCast_withTop (by simp [length_parameterDirections])))]
  rfl
include Rg R' hA in
theorem derivAlong_rayIntegrand_parameters_append (f : (ι → B) × T → ℝ) (η : ι → B) (tl : List T)
    (v : ℝ) (b : ι) (u : (ι → B) × T)
    (hf : ContDiffAt ℝ ((tl.length + 3 : ℕ) : WithTop ℕ∞) f (v • η, 0)) :
    derivAlong (gradPairing f (scaleVariables ι B T v) (projectVariable T b) [])
        (parameterDirections ι B tl ++ [u]) (η, 0) =
      derivAlong f (scaleVariables ι B T v u ::
          (parameterDirections ι B tl ++ [variableDirection T (Pi.single b (η b))])) (v • η, 0) +
      derivAlong f (parameterDirections ι B tl ++ [projectVariable T b u]) (v • η, 0) := by
  set S := scaleVariables ι B T v with hS
  set ℓ : ((ι → B) × T) →L[ℝ] ((ι → B) × T) := projectVariable T b with hℓ
  set Lt := parameterDirections ι B tl with hL
  have hlen : Lt.length = tl.length := length_parameterDirections tl
  have hSp : S (η, 0) = (v • η, 0) := rfl
  have hf' : ContDiffAt ℝ ((tl.length + 3 : ℕ) : WithTop ℕ∞) f (S (η, 0)) := hf
  rw [R'.append, (R'.congr _ _ (η, 0) Lt (derivAlong_gradPairing_singleton_eventuallyEq Rg f S ℓ (η, 0) u
    (hf'.of_le (natCast_le_natCast_withTop (by omega))))).self_of_nhds, R'.add _ _ (η, 0) Lt
    (contDiffAt_gradPairing Rg f S ℓ [S u] (η, 0) Lt.length
      (hf'.of_le (natCast_le_natCast_withTop (by simp [hlen]))))
    (contDiffAt_fderiv_comp_apply f S (ℓ u) (η, 0) Lt.length
      (hf'.of_le (natCast_le_natCast_withTop (by simp [hlen]))))]
  congr 1
  · have e := (derivAlong_gradPairing_eventuallyEq Rg R' f S ℓ Lt [S u] (η, 0)
      (parameterDirections_fixed tl v b)
      (hf'.of_le (natCast_le_natCast_withTop (by simp [hlen])))).self_of_nhds
    rw [e, gradPairing_eq_derivAlong_append Rg R' f S ℓ _ (η, 0)
      (hf'.of_le (natCast_le_natCast_withTop (by simp [hlen])))]
    have hp : ((Lt ++ [S u]) ++ [ℓ (η, 0)]).Perm (S u :: (Lt ++ [ℓ (η, 0)])) := by
      simpa using List.perm_middle (a := S u) (l₁ := Lt) (l₂ := [ℓ (η, 0)])
    exact R'.perm f _ _ _ hp (hf'.of_le (natCast_le_natCast_withTop (by simp [hlen])))
  · exact derivAlong_fderiv_comp_apply R' hA f S (ℓ u) (η, 0) Lt
      (fun x hx => (parameterDirections_fixed tl v b x hx).1)
      (hf'.of_le (natCast_le_natCast_withTop (by simp [hlen])))
include Rg R' in
theorem derivAlong_rayIntegrand_pair (f : (ι → B) × T → ℝ) (η : ι → B) (v : ℝ) (b : ι)
    (u u' : (ι → B) × T) (hf : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) f (v • η, 0)) :
    derivAlong (gradPairing f (scaleVariables ι B T v) (projectVariable T b) []) [u', u] (η, 0) =
      derivAlong f [scaleVariables ι B T v u', scaleVariables ι B T v u,
        variableDirection T (Pi.single b (η b))] (v • η, 0) +
      derivAlong f [scaleVariables ι B T v u, projectVariable T b u'] (v • η, 0) +
      derivAlong f [scaleVariables ι B T v u', projectVariable T b u] (v • η, 0) := by
  set S := scaleVariables ι B T v with hS
  set ℓ : ((ι → B) × T) →L[ℝ] ((ι → B) × T) := projectVariable T b with hℓ
  have hf' : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) f (S (η, 0)) := hf
  have d1 : DifferentiableAt ℝ (gradPairing f S ℓ [S u]) (η, 0) :=
    (contDiffAt_gradPairing Rg f S ℓ [S u] (η, 0) 1 (by simpa using hf')).differentiableAt (by simp)
  have d2 : DifferentiableAt ℝ (fun q => fderiv ℝ f (S q) (ℓ u)) (η, 0) :=
    (contDiffAt_fderiv_comp_apply f S (ℓ u) (η, 0) 1
      (hf'.of_le (natCast_le_natCast_withTop (by omega)))).differentiableAt (by simp)
  have e1 : derivAlong (gradPairing f S ℓ []) [u', u] (η, 0) =
      fderiv ℝ (derivAlong (gradPairing f S ℓ []) [u]) (η, 0) u' := rfl
  rw [e1, (derivAlong_gradPairing_singleton_eventuallyEq Rg f S ℓ (η, 0) u
      (hf'.of_le (natCast_le_natCast_withTop (by omega)))).fderiv_eq, fderiv_fun_add d1 d2,
    add_apply, fderiv_gradPairing Rg f S ℓ [S u] (η, 0) u' (by simpa using hf'),
    gradPairing_eq_derivAlong_append Rg R' f S ℓ [S u', S u] (η, 0) (by simpa using hf')]
  have e2 : derivAlong (fderiv ℝ f) [S u] (S (η, 0)) (ℓ u') = derivAlong f [S u, ℓ u'] (S (η, 0)) := by
    exact ((derivAlong_fderiv_apply_eventuallyEq Rg f (ℓ u') [S u] (S (η, 0))
      (hf'.of_le (natCast_le_natCast_withTop (by simp)))).self_of_nhds).symm
  have e3 : fderiv ℝ (fun q => fderiv ℝ f (S q) (ℓ u)) (η, 0) u' =
      derivAlong f [S u', ℓ u] (S (η, 0)) := by
    have dF : DifferentiableAt ℝ (fun x => fderiv ℝ f x (ℓ u)) (S (η, 0)) :=
      (((hf'.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)).differentiableAt (by simp)
    have := (dF.hasFDerivAt.comp (η, 0) S.hasFDerivAt).fderiv
    change fderiv ℝ ((fun x => fderiv ℝ f x (ℓ u)) ∘ S) (η, 0) u' = _
    rw [this]
    rfl
  rw [e2, e3]
  rfl
theorem sum_norm_single_mul (Q : Finset ι) (b₀ : ι) (e : B) (X : ι → ℝ) :
    ∑ b ∈ Q, ‖(Pi.single b₀ e : ι → B) b‖ * X b = if b₀ ∈ Q then ‖e‖ * X b₀ else 0 := by
  have h : ∀ b, ‖(Pi.single b₀ e : ι → B) b‖ * X b = if b = b₀ then ‖e‖ * X b₀ else 0 := by
    intro b
    by_cases hb : b = b₀
    · subst hb
      simp
    · simp [hb]
  simp only [h]
  simp
theorem scaleVariables_variableDirection_single (T : Type) [NormedAddCommGroup T] [NormedSpace ℝ T]
    (v : ℝ) (b : ι) (e : B) :
    scaleVariables ι B T v (variableDirection T (Pi.single b e)) =
      variableDirection T (Pi.single b (v • e)) := by
  rw [scaleVariables_apply]
  simp [variableDirection, Pi.single_smul]
theorem projectVariable_variableDirection_single (T : Type) [NormedAddCommGroup T] [NormedSpace ℝ T]
    (b b₀ : ι) (e : B) :
    projectVariable T b (variableDirection T (Pi.single b₀ e) : (ι → B) × T) =
      variableDirection T (Pi.single b ((Pi.single b₀ e : ι → B) b)) := rfl
theorem norm_smul_le_of_mem_unitInterval {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (e : B) : ‖v • e‖ ≤ ‖e‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hv.1]
  nlinarith [norm_nonneg e, hv.2]
theorem mem_Icc_of_mem_uIoc {t : ℝ} (ht : t ∈ Set.uIoc (0 : ℝ) 1) : t ∈ Icc (0 : ℝ) 1 := by apply _root_.YangMills.Construction.IteratedDerivative.ParametricIntegral.mem_Icc_of_mem_uIoc <;> assumption
theorem abs_intervalIntegral_le_of_abs_le {g : ℝ → ℝ} {C : ℝ} (hg : ∀ v ∈ Icc (0 : ℝ) 1, |g v| ≤ C) :
    |∫ v in (0 : ℝ)..1, g v| ≤ C := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (f := g) (C := C)
    fun x hx => by rw [Real.norm_eq_abs]; exact hg x (mem_Icc_of_mem_uIoc hx)
  simpa using this
include R' in
theorem abs_derivAlong_parameters_variable_le (f : (ι → B) × T → ℝ) (η : ι → B) (tl : List T)
    (A : ι → ℝ) (D : ι → ι → ℝ) (hD : ∀ b b', 0 ≤ D b b')
    (hs : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ((tl.length + 3 : ℕ) : WithTop ℕ∞) f (v • η, 0))
    (h0 : ∀ (b : ι) (e : B),
      |derivAlong f (parameterDirections ι B tl ++ [variableDirection T (Pi.single b e)]) (0, 0)| ≤
        ‖e‖ * A b)
    (h1 : ∀ v ∈ Icc (0 : ℝ) 1, ∀ (b b' : ι) (e e' : B),
      |derivAlong f (variableDirection T (Pi.single b' e') :: (parameterDirections ι B tl ++
        [variableDirection T (Pi.single b e)])) (v • η, 0)| ≤ ‖e‖ * ‖e'‖ * D b b')
    (b : ι) (e : B) (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
    |derivAlong f (parameterDirections ι B tl ++ [variableDirection T (Pi.single b e)]) (v • η, 0)| ≤
      ‖e‖ * (A b + ∑ b', ‖η b'‖ * D b b') := by
  have := abs_derivAlong_segment_le R' f η
    (parameterDirections ι B tl ++ [variableDirection T (Pi.single b e)]) (‖e‖ * A b)
    (fun b' => ‖e‖ * ‖η b'‖ * D b b') (fun b' => by have := hD b b'; positivity)
    (fun v hv => (hs v hv).of_le (natCast_le_natCast_withTop (by simp [length_parameterDirections])))
    (h0 b e) (fun v hv b' => h1 v hv b b' e (η b')) v hv
  refine this.trans (le_of_eq ?_)
  rw [mul_add, Finset.mul_sum]
  simp only [mul_assoc]
include Rg R' hA in
theorem rayGradientBounds_holds (hI : IntervalIntegralSmoothFamily) (f : (ι → B) × T → ℝ)
    (Q : Finset ι) (η : ι → B)
    (tl : List T) (A : ι → ℝ) (D : ι → ι → ℝ) (hD : ∀ b b', 0 ≤ D b b')
    (hs : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ((tl.length + 3 : ℕ) : WithTop ℕ∞) f (v • η, 0))
    (h0 : ∀ (b : ι) (e : B),
      |derivAlong f (parameterDirections ι B tl ++ [variableDirection T (Pi.single b e)]) (0, 0)| ≤
        ‖e‖ * A b)
    (h1 : ∀ v ∈ Icc (0 : ℝ) 1, ∀ (b b' : ι) (e e' : B),
      |derivAlong f (variableDirection T (Pi.single b' e') :: (parameterDirections ι B tl ++
        [variableDirection T (Pi.single b e)])) (v • η, 0)| ≤ ‖e‖ * ‖e'‖ * D b b') :
    RayGradientBounds f Q η tl A D := by
  have hs' : ∀ v ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ (((tl.length + 2) + 1 : ℕ) : WithTop ℕ∞) f (v • η, 0) := hs
  have hsg := abs_derivAlong_parameters_variable_le R' f η tl A D hD hs h0 h1
  refine ⟨?_, ?_⟩
  · rw [derivAlong_rayGradientSum R' hI f Q η (tl.length + 2) hs' _
      (by simp [length_parameterDirections])]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    refine abs_intervalIntegral_le_of_abs_le fun v hv => ?_
    rw [derivAlong_rayIntegrand_parameters Rg R' f η tl v b (hs v hv)]
    exact hsg b (η b) v hv
  · intro b₀ e
    rw [derivAlong_rayGradientSum R' hI f Q η (tl.length + 2) hs' _
      (by simp [length_parameterDirections])]
    have key : ∀ b ∈ Q, |∫ v in (0 : ℝ)..1,
        derivAlong (gradPairing f (scaleVariables ι B T v) (projectVariable T b) [])
        (parameterDirections ι B tl ++ [variableDirection T (Pi.single b₀ e)]) (η, 0)| ≤
        ‖e‖ * (‖η b‖ * D b b₀) + ‖(Pi.single b₀ e : ι → B) b‖ * (A b + ∑ b', ‖η b'‖ * D b b') := by
      intro b _
      refine abs_intervalIntegral_le_of_abs_le fun v hv => ?_
      rw [derivAlong_rayIntegrand_parameters_append Rg R' hA f η tl v b _ (hs v hv),
        scaleVariables_variableDirection_single, projectVariable_variableDirection_single]
      refine (abs_add_le _ _).trans (add_le_add ?_ (hsg b _ v hv))
      have h2 := h1 v hv b b₀ (η b) (v • e)
      have h3 : ‖η b‖ * ‖v • e‖ * D b b₀ ≤ ‖e‖ * (‖η b‖ * D b b₀) := by
        have := mul_le_mul_of_nonneg_left (norm_smul_le_of_mem_unitInterval hv e)
          (mul_nonneg (norm_nonneg (η b)) (hD b b₀))
        nlinarith
      exact h2.trans h3
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum key).trans (le_of_eq ?_))
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_norm_single_mul, mul_add]
    split_ifs <;> ring
include Rg R' in
theorem abs_derivAlong_rayGradientSum_pair_le (hI : IntervalIntegralSmoothFamily)
    (f : (ι → B) × T → ℝ) (Q : Finset ι) (η : ι → B)
    (D : ι → ι → ℝ) (H : ι → ι → ι → ℝ) (hD : ∀ b b', 0 ≤ D b b') (hH : ∀ b b' b'', 0 ≤ H b b' b'')
    (hs : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) f (v • η, 0))
    (h2 : ∀ v ∈ Icc (0 : ℝ) 1, ∀ (b b' : ι) (e e' : B),
      |derivAlong f [variableDirection T (Pi.single b' e'), variableDirection T (Pi.single b e)]
        (v • η, 0)| ≤ ‖e‖ * ‖e'‖ * D b b')
    (h3 : ∀ v ∈ Icc (0 : ℝ) 1, ∀ (b b' b'' : ι) (e e' e'' : B),
      |derivAlong f [variableDirection T (Pi.single b'' e''), variableDirection T (Pi.single b' e'),
        variableDirection T (Pi.single b e)] (v • η, 0)| ≤ ‖e‖ * ‖e'‖ * ‖e''‖ * H b b' b'')
    (b₁ b₂ : ι) (e₁ e₂ : B) :
    |derivAlong (rayGradientSum f Q)
      [variableDirection T (Pi.single b₂ e₂), variableDirection T (Pi.single b₁ e₁)] (η, 0)| ≤
      ‖e₁‖ * ‖e₂‖ * (∑ b ∈ Q, ‖η b‖ * H b b₁ b₂ +
        (if b₁ ∈ Q then D b₁ b₂ else 0) + if b₂ ∈ Q then D b₂ b₁ else 0) := by
  have hs' : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) f (v • η, 0) := hs
  rw [derivAlong_rayGradientSum R' hI f Q η 2 hs' _ (by simp)]
  have key : ∀ b ∈ Q, |∫ v in (0 : ℝ)..1,
      derivAlong (gradPairing f (scaleVariables ι B T v) (projectVariable T b) [])
      [variableDirection T (Pi.single b₂ e₂), variableDirection T (Pi.single b₁ e₁)] (η, 0)| ≤
      ‖e₁‖ * ‖e₂‖ * (‖η b‖ * H b b₁ b₂) + ‖(Pi.single b₂ e₂ : ι → B) b‖ * (‖e₁‖ * D b b₁) +
        ‖(Pi.single b₁ e₁ : ι → B) b‖ * (‖e₂‖ * D b b₂) := by
    intro b _
    refine abs_intervalIntegral_le_of_abs_le fun v hv => ?_
    rw [derivAlong_rayIntegrand_pair Rg R' f η v b _ _ (hs v hv), scaleVariables_variableDirection_single,
      scaleVariables_variableDirection_single, projectVariable_variableDirection_single,
      projectVariable_variableDirection_single]
    have t1 := h3 v hv b b₁ b₂ (η b) (v • e₁) (v • e₂)
    have t2 := h2 v hv b b₁ ((Pi.single b₂ e₂ : ι → B) b) (v • e₁)
    have t3 := h2 v hv b b₂ ((Pi.single b₁ e₁ : ι → B) b) (v • e₂)
    have n1 := norm_smul_le_of_mem_unitInterval hv e₁
    have n2 := norm_smul_le_of_mem_unitInterval hv e₂
    have hHb := hH b b₁ b₂
    have u1 : ‖η b‖ * ‖v • e₁‖ * ‖v • e₂‖ * H b b₁ b₂ ≤ ‖e₁‖ * ‖e₂‖ * (‖η b‖ * H b b₁ b₂) := by
      have a1 : ‖v • e₁‖ * ‖v • e₂‖ ≤ ‖e₁‖ * ‖e₂‖ :=
        mul_le_mul n1 n2 (norm_nonneg _) (norm_nonneg _)
      have := mul_le_mul_of_nonneg_right a1 (mul_nonneg (norm_nonneg (η b)) hHb)
      nlinarith
    have u2 : ‖(Pi.single b₂ e₂ : ι → B) b‖ * ‖v • e₁‖ * D b b₁ ≤
        ‖(Pi.single b₂ e₂ : ι → B) b‖ * (‖e₁‖ * D b b₁) := by
      have := mul_le_mul_of_nonneg_right n1
        (mul_nonneg (norm_nonneg ((Pi.single b₂ e₂ : ι → B) b)) (hD b b₁))
      nlinarith
    have u3 : ‖(Pi.single b₁ e₁ : ι → B) b‖ * ‖v • e₂‖ * D b b₂ ≤
        ‖(Pi.single b₁ e₁ : ι → B) b‖ * (‖e₂‖ * D b b₂) := by
      have := mul_le_mul_of_nonneg_right n2
        (mul_nonneg (norm_nonneg ((Pi.single b₁ e₁ : ι → B) b)) (hD b b₂))
      nlinarith
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · exact t1.trans u1
    · exact t2.trans u2
    · exact t3.trans u3
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum key).trans (le_of_eq ?_))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_norm_single_mul,
    sum_norm_single_mul]
  split_ifs <;> ring
end Ray
end RayGradient
open RayGradient in
theorem rayGradientSumSmoothAndBounded_holds (h : DerivAlongRulesHold)
    (hI : IntervalIntegralSmoothFamily) : RayGradientSumSmoothAndBounded := by
  intro ι B T _ _ _ _ _ _ f Q η tl hs
  have Rg := h.1 ((ι → B) × T) (((ι → B) × T) →L[ℝ] ℝ)
  have R' := h.1 ((ι → B) × T) ℝ
  have hA : ∀ (f : (ι → B) × T → ℝ) (A : ((ι → B) × T) →L[ℝ] ((ι → B) × T)) (p₀ t : (ι → B) × T)
      (l : List ((ι → B) × T)), ContDiffAt ℝ (l.length : WithTop ℕ∞) f (p₀ + A t) →
      derivAlong (fun t' => f (p₀ + A t')) l t = derivAlong f (l.map A) (p₀ + A t) :=
    fun f A p₀ t l => h.2 _ _ ℝ f A p₀ t l
  refine ⟨contDiffAt_rayGradientSum hI f Q η _ hs,
    fun A D hD h0 h1 => rayGradientBounds_holds Rg R' hA hI f Q η tl A D hD hs h0 h1, ?_⟩
  intro htl D H hD hH h2 h3 b₁ b₂ e₁ e₂
  subst htl
  exact abs_derivAlong_rayGradientSum_pair_le Rg R' hI f Q η D H hD hH (fun v hv => by simpa using hs v hv)
    h2 h3 b₁ b₂ e₁ e₂
end YangMills.Construction.IteratedDerivative
end

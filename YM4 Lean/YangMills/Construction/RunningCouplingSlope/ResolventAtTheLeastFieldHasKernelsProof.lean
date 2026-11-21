import YangMills.Construction.ColdStepAtMirrorFrames.SitesOfABlock
import YangMills.Construction.RunningCouplingSlope.EnergyAtTheLeastFieldHasKernels
import YangMills.Construction.RunningCouplingSlope.HessianAtTheLeastFieldHasKernels
import YangMills.Construction.RunningCouplingSlope.LeastFieldAtAColdnessTheChainReaches
import YangMills.Construction.RunningCouplingSlope.ResolventAtTheLeastFieldHasKernels
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open Filter Topology
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames Interpolation ReferenceDensity
namespace ResolventKernels
section Partials
variable {α : Type} {E E' W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup W] [NormedSpace ℝ W]
private def iterPartial (e : α → E) : List α → (E → W) → E → W
  | [], f => f
  | v :: vs, f => fun x => fderiv ℝ (iterPartial e vs f) x (e v)
private theorem iterPartial_contDiffAt (e : α → E) (vs : List α) {f : E → W} {x : E} {n : ℕ}
    (h : ContDiffAt ℝ ((n + vs.length : ℕ) : WithTop ℕ∞) f x) : ContDiffAt ℝ n (iterPartial e vs f) x := by
  induction vs generalizing n with
  | nil => simpa [iterPartial] using h
  | cons v vs ih =>
    have h1 : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (iterPartial e vs f) x :=
      ih (n := n + 1) (by simpa [add_assoc, add_comm 1] using h)
    have h2 : ContDiffAt ℝ n (fderiv ℝ (iterPartial e vs f)) x := h1.fderiv_right (by norm_cast)
    exact h2.clm_apply contDiffAt_const
private theorem iterPartial_differentiableAt (e : α → E) (vs : List α) {f : E → W} {x : E} {N : ℕ}
    (hl : vs.length + 1 ≤ N) (h : ContDiffAt ℝ N f x) : DifferentiableAt ℝ (iterPartial e vs f) x := by
  have : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (iterPartial e vs f) x :=
    iterPartial_contDiffAt e vs (h.of_le (by norm_cast; omega))
  exact this.differentiableAt (by simp)
private theorem iterPartial_congr (e : α → E) (vs : List α) {f g : E → W} {x : E} (h : f =ᶠ[𝓝 x] g) :
    iterPartial e vs f =ᶠ[𝓝 x] iterPartial e vs g := by
  induction vs with
  | nil => simpa [iterPartial] using h
  | cons v vs ih => exact ih.fderiv.mono fun y hy => by simp only [iterPartial]; rw [hy]
private theorem iterPartial_const (e : α → E) (v : α) (vs : List α) (c : W) :
    iterPartial e (v :: vs) (fun _ : E => c) = fun _ => 0 := by
  induction vs generalizing v with
  | nil => funext x; simp [iterPartial]
  | cons u vs ih =>
    funext x
    change fderiv ℝ (iterPartial e (u :: vs) fun _ : E => c) x (e v) = 0
    rw [ih]
    simp
private theorem iteratedFDeriv_eq_iterPartial (e : α → E) {f : E → W} : ∀ (n : ℕ) (m : Fin n → α) (x : E),
    ContDiffAt ℝ n f x → iteratedFDeriv ℝ n f x (fun i => e (m i)) = iterPartial e (List.ofFn m) f x := by
  intro n
  induction n with
  | zero => intro m x _; simp [iterPartial]
  | succ n ih =>
    intro m x h
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ]
    have hn : ContDiffAt ℝ n f x := h.of_le (by norm_cast; omega)
    have hev : iterPartial e (List.ofFn fun i : Fin n => m i.succ) f =ᶠ[𝓝 x]
        fun y => iteratedFDeriv ℝ n f y (fun i => e (m i.succ)) :=
      (hn.eventually (by simp)).mono fun y hy => (ih (fun i => m i.succ) y hy).symm
    simp only [iterPartial]
    rw [hev.fderiv_eq]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x :=
      (h.iteratedFDeriv_right (m := 1) (i := n) (by norm_cast; omega)).differentiableAt (by simp)
    have := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) W
      (fun i => e (m i.succ))).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
    have h2 : fderiv ℝ (fun y => iteratedFDeriv ℝ n f y (fun i => e (m i.succ))) x (e (m 0)) =
        (fderiv ℝ (iteratedFDeriv ℝ n f) x (e (m 0))) (fun i => e (m i.succ)) := by
      have h3 := congrArg (fun L => L (e (m 0))) this
      simpa [Function.comp_def] using h3
    rw [h2]
    rfl
private theorem iterPartial_comp_affine (L : E →L[ℝ] E') (y₀ : E') (e : α → E) (l : List α) {f : E' → W}
    {N : ℕ} (hl : l.length ≤ N) {x : E} (hf : ContDiffAt ℝ N f (L x + y₀)) :
    iterPartial e l (fun z => f (L z + y₀)) =ᶠ[𝓝 x] fun z => iterPartial (fun a => L (e a)) l f (L z + y₀) := by
  induction l generalizing x with
  | nil => exact EventuallyEq.rfl
  | cons v l ih =>
    have hc : Continuous fun z => L z + y₀ := by fun_prop
    have hev : ∀ᶠ z in 𝓝 x, ContDiffAt ℝ N f (L z + y₀) :=
      hc.continuousAt.eventually (hf.eventually (by simp))
    have hl' : l.length + 1 ≤ N := by simpa using hl
    refine ((Filter.EventuallyEq.fderiv (𝕜 := ℝ) (ih (Nat.le_of_succ_le hl') hf)).and hev).mono fun z hz => ?_
    obtain ⟨h1, h2⟩ := hz
    simp only [iterPartial]
    rw [h1]
    have hd := iterPartial_differentiableAt (fun a => L (e a)) l hl' h2
    have hA : HasFDerivAt (fun z => L z + y₀) L z := L.hasFDerivAt.add_const y₀
    have := (hd.hasFDerivAt.comp z hA).fderiv
    have h3 := congrArg (fun Q => Q (e v)) this
    simpa [Function.comp_def] using h3
end Partials
section Leibniz
variable {α : Type} {E A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]
private def twoSplits : List α → List (List α × List α)
  | [] => [([], [])]
  | v :: vs => (twoSplits vs).map (fun p => (v :: p.1, p.2)) ++ (twoSplits vs).map (fun p => (p.1, v :: p.2))
private theorem twoSplits_spec (l : List α) : ∀ p ∈ twoSplits l, p.1.length + p.2.length = l.length ∧
    ∀ x ∈ l, x ∈ p.1 ∨ x ∈ p.2 := by
  induction l with
  | nil => simp [twoSplits]
  | cons v l ih =>
    intro p hp
    simp only [twoSplits, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · obtain ⟨h1, h2⟩ := ih q hq
      refine ⟨by simp; omega, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · rcases h2 x hx with h | h <;> simp [h]
    · obtain ⟨h1, h2⟩ := ih q hq
      refine ⟨by simp; omega, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · rcases h2 x hx with h | h <;> simp [h]
private theorem twoSplits_head (l : List α) : ∃ rest, twoSplits l = (l, []) :: rest ∧ (∀ p ∈ rest, p.2 ≠ []) ∧
    rest.length + 1 = 2 ^ l.length := by
  induction l with
  | nil => exact ⟨[], by simp [twoSplits], by simp, by simp⟩
  | cons v l ih =>
    obtain ⟨rest, h1, h2, h3⟩ := ih
    refine ⟨rest.map (fun p => (v :: p.1, p.2)) ++
      ((l, []) :: rest).map (fun p => (p.1, v :: p.2)), ?_, ?_, ?_⟩
    · simp only [twoSplits, h1, List.map_cons, List.cons_append]
    · intro p hp
      simp only [List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · exact h2 q hq
      · simp
    · simp only [List.length_append, List.length_map, List.length_cons, pow_succ]
      omega
private theorem fderiv_listSum_apply {β : Type} (P : List β) (h : β → E → A) (y w : E)
    (hd : ∀ p ∈ P, DifferentiableAt ℝ (h p) y) :
    DifferentiableAt ℝ (fun z => (P.map fun p => h p z).sum) y ∧
    fderiv ℝ (fun z => (P.map fun p => h p z).sum) y w = (P.map fun p => fderiv ℝ (h p) y w).sum := by
  induction P with
  | nil => simp
  | cons q P ih =>
    obtain ⟨i1, i2⟩ := ih fun p hp => hd p (List.mem_cons_of_mem _ hp)
    have hq := hd q List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    refine ⟨hq.add i1, ?_⟩
    rw [fderiv_fun_add hq i1]
    simp [i2]
private theorem iterPartial_mul (e : α → E) (l : List α) {f g : E → A} {N : ℕ} (hl : l.length ≤ N) {x : E}
    (hf : ContDiffAt ℝ N f x) (hg : ContDiffAt ℝ N g x) :
    iterPartial e l (fun y => f y * g y) =ᶠ[𝓝 x]
      fun y => ((twoSplits l).map fun p => iterPartial e p.1 f y * iterPartial e p.2 g y).sum := by
  induction l generalizing x with
  | nil => simp [iterPartial, twoSplits]
  | cons v l ih =>
    have hl' : l.length + 1 ≤ N := by simpa using hl
    have hev := (hf.eventually (by simp)).and (hg.eventually (by simp))
    have hev2 : ∀ᶠ y in 𝓝 x, iterPartial e l (fun y => f y * g y) =ᶠ[𝓝 y]
        fun y => ((twoSplits l).map fun p => iterPartial e p.1 f y * iterPartial e p.2 g y).sum := by
      filter_upwards [hev] with y hy using ih (Nat.le_of_succ_le hl') hy.1 hy.2
    filter_upwards [hev, hev2] with y hy h2
    obtain ⟨hfy, hgy⟩ := hy
    simp only [iterPartial]
    rw [h2.fderiv_eq]
    have hdf : ∀ p ∈ twoSplits l, DifferentiableAt ℝ (iterPartial e p.1 f) y ∧
        DifferentiableAt ℝ (iterPartial e p.2 g) y := by
      intro p hp
      have := (twoSplits_spec l p hp).1
      exact ⟨iterPartial_differentiableAt e _ (by omega) hfy, iterPartial_differentiableAt e _ (by omega) hgy⟩
    have hprod : ∀ p ∈ twoSplits l, DifferentiableAt ℝ (fun z => iterPartial e p.1 f z * iterPartial e p.2 g z) y :=
      fun p hp => (hdf p hp).1.mul (hdf p hp).2
    rw [(fderiv_listSum_apply (twoSplits l) (fun p z => iterPartial e p.1 f z * iterPartial e p.2 g z) y (e v)
      hprod).2]
    simp only [twoSplits, List.map_append, List.map_map, List.sum_append, Function.comp_def, iterPartial]
    rw [← List.sum_map_add]
    refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
    obtain ⟨h1, h2⟩ := hdf p hp
    rw [fderiv_fun_mul' h1 h2]
    simp [add_comm]
end Leibniz
section Kernels
variable {ι β : Type} [Fintype ι] [DecidableEq ι]
private structure IsSpan (sp : ι → ι → List β → ℝ) (S : ℝ → ℝ) : Prop where
  nonneg : ∀ a b A, 0 ≤ sp a b A
  triangle : ∀ a e b (A B A' : List β), (∀ x ∈ A', x ∈ A ∨ x ∈ B) → sp a b A' ≤ sp a e A + sp e b B
  base_le : ∀ a e A, sp a e [] ≤ sp a e A
  sum_le : ∀ ε, 0 < ε → ∀ a, ∑ e, Real.exp (-(ε * sp a e [])) ≤ S ε
  bound_nonneg : ∀ ε, 0 ≤ S ε
private def HasKernel (sp : ι → ι → List β → ℝ) (r C : ℝ) (A : List β) (m : Matrix ι ι ℝ) : Prop :=
  ∀ a b, |m a b| ≤ C * Real.exp (-(r * sp a b A))
variable {sp : ι → ι → List β → ℝ} {S : ℝ → ℝ}
private theorem HasKernel.mul (h : IsSpan sp S) {r C₁ C₂ : ℝ} (hr : 0 < r) (h1 : 0 ≤ C₁) (h2 : 0 ≤ C₂)
    {A B A' : List β} (hc : ∀ x ∈ A', x ∈ A ∨ x ∈ B) {m₁ m₂ : Matrix ι ι ℝ}
    (k₁ : HasKernel sp r C₁ A m₁) (k₂ : HasKernel sp r C₂ B m₂) :
    HasKernel sp (r / 2) (C₁ * C₂ * S (r / 2)) A' (m₁ * m₂) := by
  intro a b
  rw [Matrix.mul_apply]
  calc |∑ e, m₁ a e * m₂ e b| ≤ ∑ e, |m₁ a e * m₂ e b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, C₁ * C₂ * Real.exp (-(r / 2 * sp a b A')) * Real.exp (-(r / 2 * sp a e [])) := by
        apply Finset.sum_le_sum
        intro e _
        rw [abs_mul]
        have h3 := mul_le_mul (k₁ a e) (k₂ e b) (abs_nonneg _) (by positivity)
        refine h3.trans ?_
        have hx := h.base_le a e A
        have hy := h.nonneg e b B
        have ht := h.triangle a e b A B A' hc
        have h4 : Real.exp (-(r * sp a e A)) * Real.exp (-(r * sp e b B)) ≤
            Real.exp (-(r / 2 * sp a b A')) * Real.exp (-(r / 2 * sp a e [])) := by
          rw [← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.2
          nlinarith
        calc C₁ * Real.exp (-(r * sp a e A)) * (C₂ * Real.exp (-(r * sp e b B)))
            = C₁ * C₂ * (Real.exp (-(r * sp a e A)) * Real.exp (-(r * sp e b B))) := by ring
          _ ≤ C₁ * C₂ * (Real.exp (-(r / 2 * sp a b A')) * Real.exp (-(r / 2 * sp a e []))) :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
          _ = _ := by ring
    _ = C₁ * C₂ * Real.exp (-(r / 2 * sp a b A')) * ∑ e, Real.exp (-(r / 2 * sp a e [])) := by
        rw [Finset.mul_sum]
    _ ≤ C₁ * C₂ * Real.exp (-(r / 2 * sp a b A')) * S (r / 2) :=
        mul_le_mul_of_nonneg_left (h.sum_le _ (by positivity) a) (by positivity)
    _ = _ := by ring
private theorem HasKernel.mono (h : IsSpan sp S) {r r' C C' : ℝ} (hr : r' ≤ r) (hC : 0 ≤ C) (hC' : C ≤ C')
    {A : List β} {m : Matrix ι ι ℝ} (k : HasKernel sp r C A m) : HasKernel sp r' C' A m := by
  intro a b
  refine (k a b).trans ?_
  have h1 : Real.exp (-(r * sp a b A)) ≤ Real.exp (-(r' * sp a b A)) := by
    apply Real.exp_le_exp.2
    have := h.nonneg a b A
    nlinarith
  calc C * Real.exp (-(r * sp a b A)) ≤ C * Real.exp (-(r' * sp a b A)) :=
        mul_le_mul_of_nonneg_left h1 hC
    _ ≤ C' * Real.exp (-(r' * sp a b A)) := mul_le_mul_of_nonneg_right hC' (Real.exp_pos _).le
private theorem HasKernel.listSum {r C : ℝ} {A : List β} (hC : 0 ≤ C) (P : List (Matrix ι ι ℝ))
    (hP : ∀ m ∈ P, HasKernel sp r C A m) : HasKernel sp r (P.length * C) A P.sum := by
  induction P with
  | nil =>
    intro a b
    simp
  | cons q P ih =>
    intro a b
    have h1 := hP q List.mem_cons_self a b
    have h2 := ih (fun m hm => hP m (List.mem_cons_of_mem _ hm)) a b
    simp only [List.sum_cons, Matrix.add_apply, List.length_cons]
    refine (abs_add_le _ _).trans ?_
    push_cast
    linarith
private def inverseConst (S : ℝ → ℝ) (r₀ C₀ D : ℝ) : ℕ → ℝ
  | 0 => C₀
  | m + 1 => inverseConst S r₀ C₀ D m +
      2 ^ (m + 1) * (inverseConst S r₀ C₀ D m * D * S (r₀ / 4 ^ m / 2) * C₀ * S (r₀ / 4 ^ m / 2 / 2))
private theorem inverseConst_nonneg (h : IsSpan sp S) {r₀ C₀ D : ℝ} (h0 : 0 ≤ C₀) (hD : 0 ≤ D) (m : ℕ) :
    0 ≤ inverseConst S r₀ C₀ D m := by
  induction m with
  | zero => exact h0
  | succ m ih =>
    have := h.bound_nonneg (r₀ / 4 ^ m / 2)
    have := h.bound_nonneg (r₀ / 4 ^ m / 2 / 2)
    simp only [inverseConst]
    positivity
private theorem hasKernel_of_inverse (h : IsSpan sp S) {r₀ C₀ D : ℝ} (hr : 0 < r₀) (h0 : 0 ≤ C₀) (hD : 0 ≤ D)
    (P Q : List β → Matrix ι ι ℝ) (n : ℕ) (hone : Q [] * P [] = 1)
    (hid : ∀ A : List β, A ≠ [] → A.length ≤ n →
      ((twoSplits A).map fun p => P p.1 * Q p.2).sum = 0)
    (hP : HasKernel sp r₀ C₀ [] (P []))
    (hQ : ∀ B : List β, B ≠ [] → B.length ≤ n → HasKernel sp r₀ D B (Q B)) :
    ∀ m, m ≤ n → ∀ A : List β, A.length ≤ m →
      HasKernel sp (r₀ / 4 ^ m) (inverseConst S r₀ C₀ D m) A (P A) := by
  intro m
  induction m with
  | zero =>
    intro _ A hA
    have : A = [] := List.length_eq_zero_iff.1 (by omega)
    subst this
    simpa [inverseConst] using hP
  | succ m ih =>
    intro hm A hA
    have hCm : 0 ≤ inverseConst S r₀ C₀ D m := inverseConst_nonneg h h0 hD m
    have hS1 := h.bound_nonneg (r₀ / 4 ^ m / 2)
    have hS2 := h.bound_nonneg (r₀ / 4 ^ m / 2 / 2)
    have hrm : 0 < r₀ / 4 ^ m := by positivity
    have hrate : r₀ / 4 ^ (m + 1) = r₀ / 4 ^ m / 2 / 2 := by rw [pow_succ]; field_simp; norm_num
    have hle : r₀ / 4 ^ m ≤ r₀ := div_le_self hr.le (one_le_pow₀ (by norm_num))
    by_cases hAm : A.length ≤ m
    · refine HasKernel.mono h ?_ hCm ?_ (ih (by omega) A hAm)
      · rw [hrate]
        have : 0 < r₀ / 4 ^ m := hrm
        linarith
      · simp only [inverseConst]
        have : 0 ≤ 2 ^ (m + 1) * (inverseConst S r₀ C₀ D m * D * S (r₀ / 4 ^ m / 2) * C₀ *
            S (r₀ / 4 ^ m / 2 / 2)) := by positivity
        linarith
    · have hlen : A.length = m + 1 := by omega
      have hne : A ≠ [] := by
        intro hh
        simp [hh] at hlen
      obtain ⟨rest, h1, h2, h3⟩ := twoSplits_head A
      have hsum := hid A hne (by omega)
      rw [h1] at hsum
      simp only [List.map_cons, List.sum_cons] at hsum
      have hPA : P A = -(((rest.map fun p => P p.1 * Q p.2).sum) * P []) := by
        have : P A * (Q [] * P []) = -(((rest.map fun p => P p.1 * Q p.2).sum) * P []) := by
          rw [← mul_assoc, eq_neg_iff_add_eq_zero, ← add_mul, hsum, zero_mul]
        rwa [hone, mul_one] at this
      set K : ℝ := inverseConst S r₀ C₀ D m * D * S (r₀ / 4 ^ m / 2) * C₀ * S (r₀ / 4 ^ m / 2 / 2) with hK
      have hK0 : 0 ≤ K := by positivity
      have hterm : ∀ p ∈ rest, HasKernel sp (r₀ / 4 ^ m / 2)
          (inverseConst S r₀ C₀ D m * D * S (r₀ / 4 ^ m / 2)) A (P p.1 * Q p.2) := by
        intro p hp
        have hpm : p ∈ twoSplits A := by rw [h1]; exact List.mem_cons_of_mem _ hp
        obtain ⟨s1, s2⟩ := twoSplits_spec A p hpm
        have hp2 : p.2 ≠ [] := h2 p hp
        have hl2 : 0 < p.2.length := List.length_pos_iff.2 hp2
        exact HasKernel.mul h hrm hCm hD s2 (ih (by omega) p.1 (by omega))
          (HasKernel.mono h hle hD le_rfl (hQ p.2 hp2 (by omega)))
      have hsumK := HasKernel.listSum (sp := sp) (A := A) (r := r₀ / 4 ^ m / 2)
        (C := inverseConst S r₀ C₀ D m * D * S (r₀ / 4 ^ m / 2)) (by positivity)
        (rest.map fun p => P p.1 * Q p.2) (by
          intro m' hm'
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm'
          exact hterm p hp)
      have hR : HasKernel sp (r₀ / 4 ^ m / 2) C₀ [] (P []) :=
        HasKernel.mono h (by have := hrm; linarith) h0 le_rfl hP
      have hprod := HasKernel.mul h (r := r₀ / 4 ^ m / 2) (by positivity) (by positivity) h0
        (A := A) (B := []) (A' := A) (fun x hx => Or.inl hx) hsumK hR
      have hbound : ((rest.map fun p => P p.1 * Q p.2).length : ℝ) ≤ 2 ^ (m + 1) := by
        rw [List.length_map]
        have : (rest.length : ℝ) + 1 = 2 ^ (m + 1) := by
          rw [← hlen]; exact_mod_cast h3
        linarith
      rw [hPA, hrate]
      intro a b
      have h5 := hprod a b
      rw [Matrix.neg_apply, abs_neg]
      refine h5.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      simp only [inverseConst]
      have h6 : ((rest.map fun p => P p.1 * Q p.2).length : ℝ) *
          (inverseConst S r₀ C₀ D m * D * S (r₀ / 4 ^ m / 2)) * C₀ * S (r₀ / 4 ^ m / 2 / 2) =
          ((rest.map fun p => P p.1 * Q p.2).length : ℝ) * K := by rw [hK]; ring
      rw [h6]
      have := mul_le_mul_of_nonneg_right hbound hK0
      linarith
private theorem abs_inv_entry_le_of_schur {lam r : ℝ} (hlam : 0 < lam) (d : ι → ι → ℝ) (A : Matrix ι ι ℝ)
    (hsymm : ∀ a b, A a b = A b a) (hd0 : ∀ a, d a a = 0)
    (hds : ∀ a b, d a b = d b a) (hdt : ∀ a b c, d a c ≤ d a b + d b c) (hr : 0 ≤ r)
    (hfloor : ∀ v : ι → ℝ, lam * ∑ a, v a ^ 2 ≤ ∑ a, ∑ b, v a * A a b * v b)
    (hrow : ∀ a, ∑ b, |A a b| * (Real.exp (r * d a b) - 1) ≤ lam / 2)
    (hinv : IsUnit A) (i j : ι) :
    |A⁻¹ i j| ≤ 2 / lam * Real.exp (-(r * d i j)) := by
  set φ : ι → ℝ := fun x => r * d x j with hφ
  set g : ι → ℝ := fun x => A⁻¹ x j with hg
  have hAg : ∀ x, ∑ y, A x y * g y = if x = j then 1 else 0 := by
    intro x
    have hh : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hinv)
    have := congrFun (congrFun hh x) j
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  set v : ι → ℝ := fun x => Real.exp (φ x) * g x with hv
  have hlip : ∀ x y, |φ x - φ y| ≤ r * d x y := by
    intro x y
    have h1 := hdt x y j
    have h2 := hdt y x j
    rw [hds y x] at h2
    simp only [hφ]
    rw [abs_le]
    constructor <;> nlinarith
  have hE : ∀ x y, |Real.exp (φ x - φ y) - 1| ≤ Real.exp (r * d x y) - 1 := by
    intro x y
    have h1 := hlip x y
    have hmono := abs_le.1 h1
    rw [abs_le]
    have h2 : Real.exp (φ x - φ y) ≤ Real.exp (r * d x y) := Real.exp_le_exp.2 hmono.2
    have h3 : Real.exp (-(r * d x y)) ≤ Real.exp (φ x - φ y) := Real.exp_le_exp.2 hmono.1
    have h4 : 2 ≤ Real.exp (r * d x y) + Real.exp (-(r * d x y)) := by
      have := Real.add_one_le_exp (r * d x y)
      have h5 := Real.add_one_le_exp (-(r * d x y))
      linarith
    constructor <;> linarith
  have hform : ∑ a, ∑ b, v a * (A a b * Real.exp (φ a - φ b)) * v b = v j * Real.exp (φ j) := by
    have h1 : ∀ a, ∑ b, v a * (A a b * Real.exp (φ a - φ b)) * v b =
        v a * Real.exp (φ a) * ∑ b, A a b * g b := by
      intro a
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have : Real.exp (φ a - φ b) * Real.exp (φ b) = Real.exp (φ a) := by
        rw [← Real.exp_add, sub_add_cancel]
      simp only [hv]
      calc v a * (A a b * Real.exp (φ a - φ b)) * (Real.exp (φ b) * g b)
          = v a * (Real.exp (φ a - φ b) * Real.exp (φ b)) * (A a b * g b) := by
            simp only [hv]; ring
        _ = _ := by rw [this]
    simp only [h1, hAg]
    simp
  have hφj : φ j = 0 := by simp [hφ, hd0]
  have hsplit : ∑ a, ∑ b, v a * (A a b * Real.exp (φ a - φ b)) * v b =
      ∑ a, ∑ b, v a * A a b * v b +
        ∑ a, ∑ b, v a * (A a b * (Real.exp (φ a - φ b) - 1)) * v b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have herr : |∑ a, ∑ b, v a * (A a b * (Real.exp (φ a - φ b) - 1)) * v b| ≤
      lam / 2 * ∑ a, v a ^ 2 := by
    have hterm : ∀ a b, |v a * (A a b * (Real.exp (φ a - φ b) - 1)) * v b| ≤
        (v a ^ 2 + v b ^ 2) / 2 * (|A a b| * (Real.exp (r * d a b) - 1)) := by
      intro a b
      have h1 : |v a * v b| ≤ (v a ^ 2 + v b ^ 2) / 2 := by
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (v a - v b), sq_nonneg (v a + v b)]
      have h2 : |A a b * (Real.exp (φ a - φ b) - 1)| ≤
          |A a b| * (Real.exp (r * d a b) - 1) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hE a b) (abs_nonneg _)
      calc |v a * (A a b * (Real.exp (φ a - φ b) - 1)) * v b|
          = |v a * v b| * |A a b * (Real.exp (φ a - φ b) - 1)| := by
            rw [← abs_mul]; congr 1; ring
        _ ≤ _ := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    set w : ι → ι → ℝ := fun a b => |A a b| * (Real.exp (r * d a b) - 1) with hw
    have hws : ∀ a b, w a b = w b a := by
      intro a b
      simp only [hw]
      rw [hsymm a b, hds a b]
    have hwrow : ∀ a, ∑ b, w a b ≤ lam / 2 := hrow
    calc |∑ a, ∑ b, v a * (A a b * (Real.exp (φ a - φ b) - 1)) * v b|
        ≤ ∑ a, ∑ b, |v a * (A a b * (Real.exp (φ a - φ b) - 1)) * v b| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          exact Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ∑ b, (v a ^ 2 + v b ^ 2) / 2 * w a b :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
      _ = ∑ a, ∑ b, v a ^ 2 * w a b := by
          have h1 : ∑ a, ∑ b, v b ^ 2 * w a b = ∑ a, ∑ b, v a ^ 2 * w a b := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            rw [hws]
          have h2 : ∑ a, ∑ b, (v a ^ 2 + v b ^ 2) / 2 * w a b =
              (∑ a, ∑ b, v a ^ 2 * w a b + ∑ a, ∑ b, v b ^ 2 * w a b) / 2 := by
            rw [← Finset.sum_add_distrib, Finset.sum_div]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Finset.sum_add_distrib, Finset.sum_div]
            refine Finset.sum_congr rfl fun b _ => ?_
            ring
          rw [h2, h1]
          ring
      _ = ∑ a, v a ^ 2 * ∑ b, w a b := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ a, v a ^ 2 * (lam / 2) :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hwrow a) (sq_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hlow : lam / 2 * ∑ a, v a ^ 2 ≤ v j := by
    have h1 := hfloor v
    have h2 := (abs_le.1 herr).1
    have h3 := hform
    rw [hsplit, hφj, Real.exp_zero, mul_one] at h3
    linarith
  have hvv : v i ^ 2 ≤ ∑ a, v a ^ 2 :=
    Finset.single_le_sum (f := fun a => v a ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hvj2 : v j ^ 2 ≤ ∑ a, v a ^ 2 :=
    Finset.single_le_sum (f := fun a => v a ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  set s := ∑ a, v a ^ 2 with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs1 : lam / 2 * s ≤ Real.sqrt s := by
    refine hlow.trans ?_
    exact (le_abs_self _).trans (Real.abs_le_sqrt hvj2)
  have hs2 : Real.sqrt s ≤ 2 / lam := by
    by_cases hz : Real.sqrt s = 0
    · rw [hz]; positivity
    · have hpos : 0 < Real.sqrt s := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
      have h1 : lam / 2 * (Real.sqrt s * Real.sqrt s) ≤ Real.sqrt s := by
        rw [Real.mul_self_sqrt hs0]; exact hs1
      rw [le_div_iff₀ hlam]
      have h2 : lam / 2 * Real.sqrt s ≤ 1 := by
        by_contra hc
        rw [not_le] at hc
        nlinarith
      linarith
  have hvi : |v i| ≤ 2 / lam := (Real.abs_le_sqrt hvv).trans hs2
  have hgi : |g i| = Real.exp (-(φ i)) * |v i| := by
    simp only [hv]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), ← mul_assoc, ← Real.exp_add]
    simp
  have : A⁻¹ i j = g i := rfl
  rw [this, hgi, mul_comm]
  exact mul_le_mul_of_nonneg_right hvi (Real.exp_pos _).le
end Kernels
section Cells
variable {F : BlockFrame}
private theorem cellSupDist_self_zero (y : F.Cell) : cellSupDist y y = 0 := by
  simp [cellSupDist]
private theorem cellSupDist_symm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by
  unfold cellSupDist
  congr 1
  funext i
  rw [show z i - y i = -(y i - z i) by ring, ZMod.natAbs_valMinAbs_neg]
private theorem cellSupDist_le_add (x y z : F.Cell) :
    cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by
  unfold cellSupDist
  refine Finset.sup_le fun i _ => ?_
  have h1 : x i - z i = (x i - y i) + (y i - z i) := by ring
  rw [h1]
  refine ((ZMod.natAbs_valMinAbs_add_le _ _).trans (Int.natAbs_add_le _ _)).trans ?_
  exact add_le_add
    (Finset.le_sup (f := fun i => ((x i - y i).valMinAbs).natAbs) (Finset.mem_univ i))
    (Finset.le_sup (f := fun i => ((y i - z i).valMinAbs).natAbs) (Finset.mem_univ i))
private theorem le_cellSetDiameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by
  unfold cellSetDiameter
  exact (Finset.le_sup (f := fun v => cellSupDist u v) hv).trans
    (Finset.le_sup (f := fun u => P.sup fun v => cellSupDist u v) hu)
private theorem cellSetDiameter_le {P : Finset F.Cell} {n : ℕ} (h : ∀ u ∈ P, ∀ v ∈ P, cellSupDist u v ≤ n) :
    cellSetDiameter P ≤ n :=
  Finset.sup_le fun u hu => Finset.sup_le fun v hv => h u hu v hv
private theorem cellSetDiameter_mono {P Q : Finset F.Cell} (h : P ⊆ Q) :
    cellSetDiameter P ≤ cellSetDiameter Q :=
  cellSetDiameter_le fun _ hu _ hv => le_cellSetDiameter (h hu) (h hv)
private theorem cellSetDiameter_pair (y z : F.Cell) :
    cellSetDiameter ({y, z} : Finset F.Cell) = cellSupDist y z := by
  apply le_antisymm
  · refine cellSetDiameter_le fun u hu v hv => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
      simp [cellSupDist_self_zero, cellSupDist_symm]
  · exact le_cellSetDiameter (by simp) (by simp)
private theorem cellSetDiameter_union_le {P Q R : Finset F.Cell} {e : F.Cell} (he : e ∈ P) (he' : e ∈ Q)
    (h : R ⊆ P ∪ Q) : cellSetDiameter R ≤ cellSetDiameter P + cellSetDiameter Q := by
  refine cellSetDiameter_le fun u hu v hv => ?_
  rcases Finset.mem_union.1 (h hu) with h1 | h1 <;> rcases Finset.mem_union.1 (h hv) with h2 | h2
  · exact (le_cellSetDiameter h1 h2).trans (Nat.le_add_right _ _)
  · exact (cellSupDist_le_add u e v).trans
      (add_le_add (le_cellSetDiameter h1 he) (le_cellSetDiameter he' h2))
  · refine (cellSupDist_le_add u e v).trans ?_
    rw [add_comm]
    exact add_le_add (by rw [cellSupDist_symm]; exact le_cellSetDiameter h2 he)
      (by rw [cellSupDist_symm]; exact le_cellSetDiameter he' h1)
  · exact (le_cellSetDiameter h1 h2).trans (Nat.le_add_left _ _)
private def expLineSum (δ : ℝ) : ℝ := ∑' t : ℤ, Real.exp (-(δ * |(t : ℝ)|))
private theorem expLineSum_nonneg (δ : ℝ) : 0 ≤ expLineSum δ := tsum_nonneg fun _ => (Real.exp_pos _).le
private theorem expLineSum_summable {δ : ℝ} (hδ : 0 < δ) :
    Summable fun t : ℤ => Real.exp (-(δ * |(t : ℝ)|)) := by
  have hg : Summable fun n : ℕ => Real.exp (-δ) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simpa using hδ)
  have h1 : Summable fun n : ℕ => Real.exp (-(δ * |((n : ℤ) : ℝ)|)) := by
    refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]
    simp
    ring_nf
  have h2 : Summable fun n : ℕ => Real.exp (-(δ * |((-(n : ℤ) : ℤ) : ℝ)|)) := by
    refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]
    simp
    ring_nf
  exact Summable.of_nat_of_neg h1 h2
private theorem sum_zmod_exp_le {m : ℕ} [NeZero m] {δ : ℝ} (hδ : 0 < δ) (y₀ : ZMod m) :
    ∑ y : ZMod m, Real.exp (-(δ * |(((y₀ - y).valMinAbs : ℤ) : ℝ)|)) ≤ expLineSum δ := by
  have hinj : Function.Injective fun y : ZMod m => (y₀ - y).valMinAbs := by
    intro u v h
    have h' : (((y₀ - u).valMinAbs : ℤ) : ZMod m) = (((y₀ - v).valMinAbs : ℤ) : ZMod m) := by
      simpa using congrArg (fun t : ℤ => (t : ZMod m)) h
    rw [ZMod.coe_valMinAbs, ZMod.coe_valMinAbs] at h'
    exact sub_right_injective h'
  have := (expLineSum_summable hδ).sum_le_tsum (Finset.univ.image fun y : ZMod m => (y₀ - y).valMinAbs)
    (fun _ _ => (Real.exp_pos _).le)
  rw [Finset.sum_image (fun u _ v _ h => hinj h)] at this
  exact this
private theorem mem_finiteCells_of (hF : ∀ i, F.period F.top i ≠ 0) (z : F.Cell) : z ∈ finiteCells F := by
  have : ∀ i, NeZero (F.period F.top i) := fun i => ⟨hF i⟩
  have : Finite F.Cell := inferInstance
  simp [finiteCells, this]
private theorem sum_finiteCells_exp_le (hF : ∀ i, F.period F.top i ≠ 0) {δ : ℝ} (hδ : 0 < δ) (y₀ : F.Cell) :
    ∑ z ∈ finiteCells F, Real.exp (-(4 * δ * (cellSupDist y₀ z : ℝ))) ≤ expLineSum δ ^ 4 := by
  have : ∀ i, NeZero (F.period F.top i) := fun i => ⟨hF i⟩
  have hS : finiteCells F = Finset.univ := by
    ext z
    simp [mem_finiteCells_of hF z]
  rw [hS]
  have hterm : ∀ z : F.Cell, Real.exp (-(4 * δ * (cellSupDist y₀ z : ℝ))) ≤
      ∏ i, Real.exp (-(δ * |(((y₀ i - z i).valMinAbs : ℤ) : ℝ)|)) := by
    intro z
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, neg_le_neg_iff,
      show 4 * δ * (cellSupDist y₀ z : ℝ) = δ * (4 * (cellSupDist y₀ z : ℝ)) by ring]
    refine mul_le_mul_of_nonneg_left ?_ hδ.le
    have h1 : ∀ i, |(((y₀ i - z i).valMinAbs : ℤ) : ℝ)| ≤ (cellSupDist y₀ z : ℝ) := by
      intro i
      have : ((y₀ i - z i).valMinAbs).natAbs ≤ cellSupDist y₀ z :=
        Finset.le_sup (f := fun i => ((y₀ i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      exact_mod_cast this
    calc ∑ i, |(((y₀ i - z i).valMinAbs : ℤ) : ℝ)| ≤ ∑ _i : Fin 4, (cellSupDist y₀ z : ℝ) :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = 4 * (cellSupDist y₀ z : ℝ) := by simp
  refine (Finset.sum_le_sum fun z _ => hterm z).trans ?_
  have hprod := Finset.prod_univ_sum
    (fun i : Fin 4 => (Finset.univ : Finset (ZMod (F.period F.top i))))
    (fun i y => Real.exp (-(δ * |(((y₀ i - y).valMinAbs : ℤ) : ℝ)|)))
  rw [Fintype.piFinset_univ] at hprod
  rw [← hprod]
  calc ∏ i : Fin 4, ∑ y : ZMod (F.period F.top i), Real.exp (-(δ * |(((y₀ i - y).valMinAbs : ℤ) : ℝ)|))
      ≤ ∏ _i : Fin 4, expLineSum δ :=
        Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
          fun i _ => sum_zmod_exp_le hδ (y₀ i)
    _ = expLineSum δ ^ 4 := by simp
private def chartSumBound (L : ℕ) (ε : ℝ) : ℝ := 12 * ((centredCube L).card : ℝ) * expLineSum (ε / 4) ^ 4
private theorem chartSumBound_nonneg (L : ℕ) (ε : ℝ) : 0 ≤ chartSumBound L ε := by
  have := expLineSum_nonneg (ε / 4)
  unfold chartSumBound
  positivity
private theorem sum_chartCoord_le (hS : SiteDecomposition) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (hF : ∀ i, F.period F.top i ≠ 0) (f : F.Cell → ℝ) (hf : ∀ z, 0 ≤ f z) :
    ∑ e : ChartCoord F, f (enclosingCell e.1.1.1) ≤
      12 * ((centredCube F.blockSide).card : ℝ) * ∑ z ∈ finiteCells F, f z := by
  obtain ⟨-, h2, -, -⟩ := hS F hL hs
  have hsum3 : ∑ e : ChartCoord F, f (enclosingCell e.1.1.1) =
      3 * ∑ b ∈ chordBonds (finiteCells F), f (enclosingCell b.1) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum,
      Finset.sum_coe_sort (chordBonds (finiteCells F)) (fun b => f (enclosingCell b.1))]
    norm_num
  rw [hsum3]
  set ψ : F.Site F.depth × Fin 4 → F.Cell × (Fin 4 → ℤ) × Fin 4 :=
    fun b => (enclosingCell b.1, cellOffset b.1, b.2) with hψ
  have hinj : Function.Injective ψ := by
    intro b b' h
    simp only [hψ, Prod.mk.injEq] at h
    obtain ⟨h₁, h₂, h₃⟩ := h
    refine Prod.ext ?_ h₃
    rw [← (h2 b.1).1, ← (h2 b'.1).1, h₁, h₂]
  set g : F.Cell × (Fin 4 → ℤ) × Fin 4 → ℝ := fun p => f p.1 with hg
  have h1 : ∑ b ∈ chordBonds (finiteCells F), f (enclosingCell b.1) =
      ∑ p ∈ (chordBonds (finiteCells F)).image ψ, g p := by
    rw [Finset.sum_image (fun u _ v _ h => hinj h)]
  have hsub : (chordBonds (finiteCells F)).image ψ ⊆
      finiteCells F ×ˢ (centredCube F.blockSide ×ˢ (Finset.univ : Finset (Fin 4))) := by
    intro p hp
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hp
    simp only [hψ, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨mem_finiteCells_of hF _, (h2 b.1).2⟩
  have h3 : ∑ p ∈ (chordBonds (finiteCells F)).image ψ, g p ≤
      ∑ p ∈ finiteCells F ×ˢ (centredCube F.blockSide ×ˢ (Finset.univ : Finset (Fin 4))), g p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hf _
  have h4 : ∑ p ∈ finiteCells F ×ˢ (centredCube F.blockSide ×ˢ (Finset.univ : Finset (Fin 4))), g p =
      4 * ((centredCube F.blockSide).card : ℝ) * ∑ z ∈ finiteCells F, f z := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp [hg, Finset.sum_const, Finset.card_product, mul_comm]
  rw [h1]
  calc 3 * ∑ p ∈ (chordBonds (finiteCells F)).image ψ, g p
      ≤ 3 * (4 * ((centredCube F.blockSide).card : ℝ) * ∑ z ∈ finiteCells F, f z) := by
        rw [← h4]; linarith
    _ = _ := by ring
private def chartSpan {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (a b : ChartCoord F)
    (A : List (Fin k)) : ℝ :=
  (cellSetDiameter ({enclosingCell a.1.1.1, enclosingCell b.1.1.1} ∪
    (A.map fun l => (c l).1).toFinset) : ℝ)
private theorem chartSpan_nil {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (a b : ChartCoord F) :
    chartSpan c a b [] = (cellSupDist (enclosingCell a.1.1.1) (enclosingCell b.1.1.1) : ℝ) := by
  simp only [chartSpan, List.map_nil, List.toFinset_nil, Finset.union_empty, cellSetDiameter_pair]
private theorem isSpan_chartSpan (hS : SiteDecomposition) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (hF : ∀ i, F.period F.top i ≠ 0)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) : IsSpan (chartSpan c) (chartSumBound F.blockSide) where
  nonneg _ _ _ := by simp [chartSpan]
  triangle a e b A B A' hc := by
    simp only [chartSpan]
    have := cellSetDiameter_union_le (R := {enclosingCell a.1.1.1, enclosingCell b.1.1.1} ∪
        (A'.map fun l => (c l).1).toFinset)
      (P := {enclosingCell a.1.1.1, enclosingCell e.1.1.1} ∪ (A.map fun l => (c l).1).toFinset)
      (Q := {enclosingCell e.1.1.1, enclosingCell b.1.1.1} ∪ (B.map fun l => (c l).1).toFinset)
      (e := enclosingCell e.1.1.1) (by simp) (by simp) (by
        intro u hu
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, List.mem_toFinset,
          List.mem_map] at hu ⊢
        rcases hu with (rfl | rfl) | ⟨l, hl, rfl⟩
        · simp
        · simp
        · rcases hc l hl with h | h
          · exact Or.inl (Or.inr ⟨l, h, rfl⟩)
          · exact Or.inr (Or.inr ⟨l, h, rfl⟩))
    exact_mod_cast this
  base_le a e A := by
    simp only [chartSpan, List.map_nil, List.toFinset_nil, Finset.union_empty]
    exact_mod_cast cellSetDiameter_mono Finset.subset_union_left
  sum_le ε hε a := by
    have h1 := sum_chartCoord_le hS hL hs hF
      (fun z => Real.exp (-(ε * (cellSupDist (enclosingCell a.1.1.1) z : ℝ))))
      (fun _ => (Real.exp_pos _).le)
    have h2 := sum_finiteCells_exp_le hF (δ := ε / 4) (by positivity) (enclosingCell a.1.1.1)
    have h3 : ∀ z, 4 * (ε / 4) * (cellSupDist (enclosingCell a.1.1.1) z : ℝ) =
        ε * (cellSupDist (enclosingCell a.1.1.1) z : ℝ) := fun z => by ring
    simp only [h3] at h2
    simp only [chartSpan_nil]
    refine h1.trans ?_
    unfold chartSumBound
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  bound_nonneg ε := chartSumBound_nonneg _ _
end Cells
section Floor
variable {F : BlockFrame}
private def unitVariation (a : ChartCoord F) : StepVariable (finiteCells F) :=
  bondVariation a.1 (EuclideanSpace.single a.2 1)
private def variationOf (x : ChartCoord F → ℝ) : StepVariable (finiteCells F) := ∑ a, x a • unitVariation a
private theorem variationOf_apply (x : ChartCoord F → ℝ) (b : ↥(chordBonds (finiteCells F))) (α : Fin 3) :
    variationOf x b α = x (b, α) := by
  let Lc : StepVariable (finiteCells F) →L[ℝ] ℝ :=
    (EuclideanSpace.proj α).comp (ContinuousLinearMap.proj b)
  have h1 : Lc (variationOf x) = ∑ a, x a * Lc (unitVariation a) := by
    simp [variationOf, map_sum, map_smul]
  have hL : ∀ a, Lc (unitVariation a) = if a = (b, α) then 1 else 0 := by
    rintro ⟨b', α'⟩
    by_cases hb : b' = b
    · subst hb
      by_cases hα : α' = α
      · subst hα
        simp [Lc, unitVariation, bondVariation]
      · have h2 : α ≠ α' := Ne.symm hα
        simp [Lc, unitVariation, bondVariation, hα, h2]
    · have h2 : b ≠ b' := Ne.symm hb
      simp [Lc, unitVariation, bondVariation, hb]
  change Lc (variationOf x) = _
  rw [h1]
  simp [hL]
private theorem norm_sq_variationOf (x : ChartCoord F → ℝ) (b : ↥(chordBonds (finiteCells F))) :
    ‖variationOf x b‖ ^ 2 = ∑ α, x (b, α) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [variationOf_apply]
private theorem expUnit_zero_eq_one : expUnit (0 : imaginaryQuaternions) = 1 := by
  apply Subtype.ext
  simp [expUnit]
private theorem displacedPoint_coords {n : ℕ} (eqv : ChartCoord F ≃ Fin n)
    (ζ : StepVariable (finiteCells F)) :
    displacedPoint 0 (fun p => (eqv.symm p).1) (fun p => EuclideanSpace.single (eqv.symm p).2 (1 : ℝ))
      (fun p => ζ (eqv.symm p).1 (eqv.symm p).2) = ζ := by
  unfold displacedPoint
  rw [zero_add]
  have := Equiv.sum_comp eqv.symm (fun a : ChartCoord F =>
    (Pi.single a.1 (ζ a.1 a.2 • EuclideanSpace.single a.2 (1 : ℝ)) : StepVariable (finiteCells F)))
  rw [this]
  have h1 : ∀ a : ChartCoord F,
      (Pi.single a.1 (ζ a.1 a.2 • EuclideanSpace.single a.2 (1 : ℝ)) : StepVariable (finiteCells F)) =
        ζ a.1 a.2 • unitVariation a := fun a => by
    simp [unitVariation, bondVariation, Pi.single_smul]
  simp only [h1]
  change variationOf (fun a : ChartCoord F => ζ a.1 a.2) = ζ
  funext b
  ext α
  rw [variationOf_apply]
private theorem contDiffAt_chartedEnergyAtMinimizer {a ρ : ℝ} {V : F.GaugeField F.top}
    (h : ∀ (l : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3)),
      2 ≤ l → (∀ i, ‖u i‖ = 1) → ContDiffAt ℝ ((l + 0 : ℕ) : WithTop ℕ∞)
        (jointDisplacement (fun ζ V' => chartedEnergyAtMinimizer a ρ V' ζ) 0 V b u
          (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)) 0)
    (i₀ : ChartCoord F) : ContDiffAt ℝ 2 (chartedEnergyAtMinimizer a ρ V) 0 := by
  set n := Fintype.card (ChartCoord F) with hn
  have hn2 : 2 ≤ n := by
    have h1 : 0 < Fintype.card ↥(chordBonds (finiteCells F)) := Fintype.card_pos_iff.2 ⟨i₀.1⟩
    simp only [hn, Fintype.card_prod, Fintype.card_fin]
    omega
  let eqv : ChartCoord F ≃ Fin n := Fintype.equivFin _
  have hs := h n (fun p => (eqv.symm p).1) (fun p => EuclideanSpace.single (eqv.symm p).2 (1 : ℝ)) hn2
    (fun i => by simp)
  let Co : StepVariable (finiteCells F) →L[ℝ] (Fin (n + 0) → ℝ) :=
    ContinuousLinearMap.pi fun p => (EuclideanSpace.proj (eqv.symm p).2).comp
      (ContinuousLinearMap.proj (eqv.symm p).1)
  have hkey : chartedEnergyAtMinimizer a ρ V =
      (jointDisplacement (fun ζ V' => chartedEnergyAtMinimizer a ρ V' ζ)
      0 V (fun p => (eqv.symm p).1) (fun p => EuclideanSpace.single (eqv.symm p).2 (1 : ℝ))
      (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)) ∘ Co := by
    funext ζ
    have hV : leftTranslate (bondSpread (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)
        (fun i => Co ζ (Fin.natAdd n i))) V = V := by
      funext y i
      simp [leftTranslate, bondSpread, expUnit_zero_eq_one]
    simp only [Function.comp, jointDisplacement, hV, chartedEnergyAtMinimizer]
    congr 2
    exact (displacedPoint_coords eqv ζ).symm
  rw [hkey]
  have hc0 : Co 0 = 0 := map_zero _
  have h2 : ContDiffAt ℝ ((n + 0 : ℕ) : WithTop ℕ∞)
      (jointDisplacement (fun ζ V' => chartedEnergyAtMinimizer a ρ V' ζ)
      0 V (fun p => (eqv.symm p).1) (fun p => EuclideanSpace.single (eqv.symm p).2 (1 : ℝ))
      (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)) (Co 0) := by
    rw [hc0]; exact hs
  have h3 := h2.comp (0 : StepVariable (finiteCells F)) Co.contDiff.contDiffAt
  exact h3.of_le (by norm_cast)
private theorem chartedHessian_eq_fderiv {a ρ : ℝ} {V : F.GaugeField F.top} (i j : ChartCoord F)
    (h : ContDiffAt ℝ 2 (chartedEnergyAtMinimizer a ρ V) 0) :
    chartedHessian a ρ V 0 i j =
      fderiv ℝ (fderiv ℝ (chartedEnergyAtMinimizer a ρ V)) 0 (unitVariation j) (unitVariation i) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (chartedEnergyAtMinimizer a ρ V)) 0 :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have := (hd.hasFDerivAt.clm_apply
    (hasFDerivAt_const (unitVariation i) (0 : StepVariable (finiteCells F)))).fderiv
  simp only [chartedHessian, secondDerivAlong]
  have h2 := congrArg (fun Q => Q (unitVariation j)) this
  simpa [unitVariation] using h2
private theorem chartedHessian_symm {a ρ : ℝ} {V : F.GaugeField F.top} (i j : ChartCoord F)
    (h : ContDiffAt ℝ 2 (chartedEnergyAtMinimizer a ρ V) 0) :
    chartedHessian a ρ V 0 i j = chartedHessian a ρ V 0 j i := by
  rw [chartedHessian_eq_fderiv i j h, chartedHessian_eq_fderiv j i h]
  exact (h.isSymmSndFDerivAt (by simp)) _ _
private theorem chartedHessian_form {a ρ : ℝ} {V : F.GaugeField F.top} (x : ChartCoord F → ℝ)
    (h : ContDiffAt ℝ 2 (chartedEnergyAtMinimizer a ρ V) 0) :
    ∑ i, ∑ j, x i * chartedHessian a ρ V 0 i j * x j =
      deriv (deriv fun u : ℝ => chartedEnergyAtMinimizer a ρ V (u • variationOf x)) 0 := by
  set Ψ := chartedEnergyAtMinimizer a ρ V with hΨ
  set v := variationOf x with hv
  have hd : DifferentiableAt ℝ (fderiv ℝ Ψ) 0 :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hQ : ∑ i, ∑ j, x i * chartedHessian a ρ V 0 i j * x j =
      fderiv ℝ (fderiv ℝ Ψ) 0 v v := by
    simp only [chartedHessian_eq_fderiv _ _ h]
    rw [hv]
    unfold variationOf
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hQ]
  have hγ : ∀ u : ℝ, HasDerivAt (fun u : ℝ => u • v) v u := fun u => by
    simpa using (hasDerivAt_id u).smul_const v
  have hc : Continuous fun u : ℝ => u • v := by fun_prop
  have hev : ∀ᶠ u in 𝓝 (0 : ℝ), DifferentiableAt ℝ Ψ (u • v) := by
    have h1 : ∀ᶠ ζ in 𝓝 (0 : StepVariable (finiteCells F)), ContDiffAt ℝ 2 Ψ ζ := h.eventually (by simp)
    have h2 : Tendsto (fun u : ℝ => u • v) (𝓝 0) (𝓝 0) := by
      have := hc.tendsto 0
      simpa using this
    exact (h2.eventually h1).mono fun u hu => hu.differentiableAt (by simp)
  have hfirst : deriv (fun u : ℝ => Ψ (u • v)) =ᶠ[𝓝 0] fun u => fderiv ℝ Ψ (u • v) v := by
    refine hev.mono fun u hu => ?_
    exact (hu.hasFDerivAt.comp_hasDerivAt u (hγ u)).deriv
  rw [hfirst.deriv_eq]
  have h0 : HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) 0) ((0 : ℝ) • v) := by
    simpa using hd.hasFDerivAt
  have h1 := h0.comp_hasDerivAt (0 : ℝ) (hγ 0)
  have h2 := h1.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have h3 := h2.deriv
  simpa [Function.comp_def] using h3.symm
private theorem toImaginary_smul_eq (c : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (c • v) = c • toImaginary v := by
  apply Subtype.ext
  ext
  · exact (mul_zero c).symm
  · rfl
  · rfl
  · rfl
private theorem norm_toImaginary_eq (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by
  have h1 : ‖toImaginary v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    have h2 : ‖toImaginary v‖ = ‖((toImaginary v : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
    rw [h2, sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    simp [toImaginary]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
private theorem chartedHessian_floor {a lam ρ σ : ℝ}
    {V : F.GaugeField F.top} (hfl : HasCoerciveHessian a lam ρ σ (finiteCells F) V)
    (hleast : IsMinimizingChart a (finiteCells F) V ρ (minimizingCoordinates a (finiteCells F) V ρ))
    (hcold : IsCold (finiteCells F) F.depth σ (chartedField (minimizingCoordinates a (finiteCells F) V ρ) V))
    (h : ContDiffAt ℝ 2 (chartedEnergyAtMinimizer a ρ V) 0) (x : ChartCoord F → ℝ) :
    lam * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, x i * chartedHessian a ρ V 0 i j * x j := by
  rw [chartedHessian_form x h]
  have hdw : ∀ b, b ∉ chordBonds (finiteCells F) → stepCoordinates (variationOf x) b.1 b.2 = 0 := by
    intro b hb
    simp [stepCoordinates, hb]
  have h1 := hfl _ (stepCoordinates (variationOf x)) hleast.1 hdw hleast.2.1 hcold
  have hE : (fun τ : ℝ => blockEnergy a (finiteCells F) F.depth (chartedField (fun z i =>
        minimizingCoordinates a (finiteCells F) V ρ z i + τ • stepCoordinates (variationOf x) z i) V) V) =
      fun u : ℝ => chartedEnergyAtMinimizer a ρ V (u • variationOf x) := by
    funext u
    have : coordsAboveFrame true a ρ 0 V (u • variationOf x) = fun z i =>
        minimizingCoordinates a (finiteCells F) V ρ z i + u • stepCoordinates (variationOf x) z i := by
      funext z i
      simp only [coordsAboveFrame, stepFrame, if_true, minimizingBondCoordinate]
      congr 1
      simp only [stepCoordinates]
      split_ifs with hz
      · exact toImaginary_smul_eq u _
      · simp
    simp only [chartedEnergyAtMinimizer, this, chartedEnergy]
  rw [hE] at h1
  refine le_trans (le_of_eq ?_) h1
  congr 1
  rw [← Finset.sum_coe_sort (chordBonds (finiteCells F)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : stepCoordinates (variationOf x) b.1.1 b.1.2 = toImaginary (variationOf x b) := by
    simp [stepCoordinates]
  rw [this, norm_toImaginary_eq, norm_sq_variationOf]
end Floor
section Maps
variable {α : Type} {E W W' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W'] [NormedSpace ℝ W']
private theorem iterPartial_clm (Lc : W →L[ℝ] W') (e : α → E) (l : List α) {f : E → W} {N : ℕ}
    (hl : l.length ≤ N) {x : E} (hf : ContDiffAt ℝ N f x) :
    iterPartial e l (fun y => Lc (f y)) =ᶠ[𝓝 x] fun y => Lc (iterPartial e l f y) := by
  induction l generalizing x with
  | nil => exact EventuallyEq.rfl
  | cons v l ih =>
    have hl' : l.length + 1 ≤ N := by simpa using hl
    refine ((Filter.EventuallyEq.fderiv (𝕜 := ℝ) (ih (Nat.le_of_succ_le hl') hf)).and
      (hf.eventually (by simp))).mono fun z hz => ?_
    obtain ⟨h1, h2⟩ := hz
    simp only [iterPartial]
    rw [h1]
    have hd := iterPartial_differentiableAt e l hl' h2
    have := (Lc.hasFDerivAt.comp z hd.hasFDerivAt).fderiv
    have h3 := congrArg (fun Q => Q (e v)) this
    simpa [Function.comp_def] using h3
private theorem iterPartial_add_const (e : α → E) (v : α) (vs : List α) (f : E → W) (c : W) :
    iterPartial e (v :: vs) (fun y => f y + c) = iterPartial e (v :: vs) f := by
  induction vs generalizing v with
  | nil =>
    funext x
    simp only [iterPartial]
    rw [fderiv_add_const]
  | cons u vs ih =>
    funext x
    change fderiv ℝ (iterPartial e (u :: vs) fun y => f y + c) x (e v) =
      fderiv ℝ (iterPartial e (u :: vs) f) x (e v)
    rw [ih]
private theorem iterPartial_reindex {γ : Type} (e : α → E) (g : γ → α) (l : List γ) (f : E → W) :
    iterPartial (fun q => e (g q)) l f = iterPartial e (l.map g) f := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext x
    simp only [iterPartial, List.map_cons]
    rw [ih]
end Maps
section Inverse
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
private def paramDir (l : Fin k) : Fin k → ℝ := Pi.single l 1
private def entryCLM (a b : ι) : Matrix ι ι ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ a b)
private theorem contDiffAt_matrix_of_entries {M : (Fin k → ℝ) → Matrix ι ι ℝ} {m : ℕ}
    (hM : ∀ a b, ContDiffAt ℝ m (fun σ => M σ a b) 0) : ContDiffAt ℝ m M 0 := by
  have h1 : M = fun σ => ∑ a, ∑ b, M σ a b • Matrix.single a b (1 : ℝ) := by
    funext σ
    conv_lhs => rw [Matrix.matrix_eq_sum_single (M σ)]
    simp [Matrix.smul_single]
  rw [h1]
  refine ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => ?_
  exact (hM a b).smul contDiffAt_const
private theorem kernels_iterPartial_inv {β : Type} {sp : ι → ι → List (Fin k) → ℝ} {S : ℝ → ℝ}
    (hS : IsSpan sp S)
    (M : (Fin k → ℝ) → Matrix ι ι ℝ) (hM : ∀ a b, ∀ m : ℕ, ContDiffAt ℝ m (fun σ => M σ a b) 0)
    (hunit : IsUnit (M 0)) {r₀ C₀ D : ℝ} (hr : 0 < r₀) (h0 : 0 ≤ C₀) (hD : 0 ≤ D) (n : ℕ)
    (hR : HasKernel sp r₀ C₀ [] (M 0)⁻¹)
    (hQ : ∀ B : List (Fin k), B ≠ [] → B.length ≤ n → ∀ a b,
      |iterPartial paramDir B (fun σ => M σ a b) 0| ≤ D * Real.exp (-(r₀ * sp a b B))) :
    (∀ (m : ℕ) a b, ContDiffAt ℝ m (fun σ => (M σ)⁻¹ a b) 0) ∧
    ∀ A : List (Fin k), A.length ≤ n → ∀ a b, |iterPartial paramDir A (fun σ => (M σ)⁻¹ a b) 0| ≤
      inverseConst S r₀ C₀ D n * Real.exp (-(r₀ / 4 ^ n * sp a b A)) := by
  have : CompleteSpace (Matrix ι ι ℝ) := FiniteDimensional.complete ℝ _
  have hMs : ∀ m : ℕ, ContDiffAt ℝ m M 0 := fun m => contDiffAt_matrix_of_entries fun a b => hM a b m
  have hRs : ∀ m : ℕ, ContDiffAt ℝ m (fun σ => (M σ)⁻¹) 0 := by
    intro m
    have h1 : ContDiffAt ℝ m (Ring.inverse : Matrix ι ι ℝ → Matrix ι ι ℝ) (M 0) := by
      obtain ⟨u, hu⟩ := hunit
      rw [← hu]
      exact contDiffAt_ringInverse ℝ u
    have h2 := h1.comp (0 : Fin k → ℝ) (hMs m)
    have h3 : (fun σ => (M σ)⁻¹) = Ring.inverse ∘ M := by
      funext σ
      exact Matrix.nonsing_inv_eq_ringInverse _
    rw [h3]
    exact h2
  refine ⟨fun m a b => ((entryCLM a b).contDiff.contDiffAt).comp (0 : Fin k → ℝ) (hRs m), ?_⟩
  have hev : ∀ᶠ σ in 𝓝 (0 : Fin k → ℝ), (M σ)⁻¹ * M σ = 1 := by
    have h1 : ∀ᶠ σ in 𝓝 (0 : Fin k → ℝ), IsUnit (M σ) :=
      (hMs 0).continuousAt.eventually (Units.isOpen.mem_nhds hunit)
    refine h1.mono fun σ hσ => ?_
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hσ)
  have hid : ∀ A : List (Fin k), A ≠ [] → A.length ≤ n →
      ((twoSplits A).map fun p =>
        iterPartial paramDir p.1 (fun σ => (M σ)⁻¹) 0 * iterPartial paramDir p.2 M 0).sum = 0 := by
    intro A hA hl
    have h1 := iterPartial_mul paramDir A (N := A.length) le_rfl (hRs _) (hMs _)
    have h2 := iterPartial_congr paramDir A
      (show (fun σ => (M σ)⁻¹ * M σ) =ᶠ[𝓝 0] fun _ => (1 : Matrix ι ι ℝ) from hev)
    have h3 : iterPartial paramDir A (fun _ : Fin k → ℝ => (1 : Matrix ι ι ℝ)) = fun _ => 0 := by
      obtain ⟨v, vs, rfl⟩ := List.exists_cons_of_ne_nil hA
      exact iterPartial_const paramDir v vs 1
    have h4 := (h1.symm.trans h2).self_of_nhds
    rw [h3] at h4
    exact h4
  have hent : ∀ (f : (Fin k → ℝ) → Matrix ι ι ℝ), (∀ m : ℕ, ContDiffAt ℝ m f 0) →
      ∀ (A : List (Fin k)) a b, iterPartial paramDir A f 0 a b = iterPartial paramDir A (fun σ => f σ a b) 0 := by
    intro f hf A a b
    exact (iterPartial_clm (entryCLM a b) paramDir A (N := A.length) le_rfl (hf _)).self_of_nhds.symm
  have hone : iterPartial paramDir [] M 0 * iterPartial paramDir [] (fun σ => (M σ)⁻¹) 0 = 1 := by
    simp only [iterPartial]
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit)
  have hK := hasKernel_of_inverse hS hr h0 hD (fun A => iterPartial paramDir A (fun σ => (M σ)⁻¹) 0)
    (fun B => iterPartial paramDir B M 0) n hone hid hR
    (fun B hB hl a b => by
      rw [hent M hMs]
      exact hQ B hB hl a b)
  intro A hA a b
  rw [← hent _ hRs]
  exact hK n le_rfl A hA a b
end Inverse
section Assembly
variable {F : BlockFrame}
private theorem bondSpread_reindex {k j : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (g : Fin j → Fin k) (τ' : Fin j → ℝ) :
    bondSpread (fun q => c (g q)) (fun q => X (g q)) τ' =
      bondSpread c X (fun l => ∑ q, if g q = l then τ' q else 0) := by
  funext y i
  simp only [bondSpread]
  have h1 : ∀ l, (if c l = (y, i) then (∑ q, if g q = l then τ' q else 0) • X l else 0) =
      ∑ q, if g q = l then (if c l = (y, i) then τ' q • X l else 0) else 0 := by
    intro l
    split_ifs with h
    · rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun q _ => ?_
      split_ifs <;> simp
    · simp
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_ite_eq]
  simp
private theorem leftTranslate_bondSpread_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top) :
    leftTranslate (bondSpread c X 0) V = V := by
  funext y i
  simp [leftTranslate, bondSpread, expUnit_zero_eq_one]
private theorem bondDeriv_sublist {k : ℕ} (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hs : ∀ m : ℕ, ContDiffAt ℝ m (fun σ => G (leftTranslate (bondSpread c X σ) V)) 0)
    (B : List (Fin k)) :
    bondDeriv G V (fun q : Fin B.length => c (B.get q)) (fun q => X (B.get q)) =
      iterPartial paramDir B (fun σ => G (leftTranslate (bondSpread c X σ) V)) 0 := by
  set h := fun σ => G (leftTranslate (bondSpread c X σ) V) with hh
  let Lb : (Fin B.length → ℝ) →L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearMap.pi fun l => ∑ q, if B.get q = l then ContinuousLinearMap.proj q else 0
  have hLb : ∀ τ' l, Lb τ' l = ∑ q, if B.get q = l then τ' q else 0 := by
    intro τ' l
    simp only [Lb, ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp
  have hfun : (fun τ' => G (leftTranslate (bondSpread (fun q : Fin B.length => c (B.get q))
      (fun q => X (B.get q)) τ') V)) = fun τ' => h (Lb τ' + 0) := by
    funext τ'
    simp only [hh, add_zero]
    rw [bondSpread_reindex]
    congr 3
    funext l
    exact (hLb τ' l).symm
  have hL0 : Lb 0 + 0 = 0 := by simp
  have hsL : ContDiffAt ℝ (B.length : ℕ) h (Lb 0 + 0) := by
    rw [hL0]; exact hs _
  have hc : ContDiffAt ℝ (B.length : ℕ) (fun τ' => h (Lb τ' + 0)) 0 := by
    have h1 : ContDiffAt ℝ (B.length : ℕ) (fun τ' : Fin B.length → ℝ => Lb τ' + 0) 0 :=
      (Lb.contDiff.add contDiff_const).contDiffAt
    exact ContDiffAt.comp (g := h) (0 : Fin B.length → ℝ) hsL h1
  unfold bondDeriv
  rw [hfun]
  have h1 := iteratedFDeriv_eq_iterPartial (paramDir (k := B.length)) B.length id 0 hc
  have h2 := (iterPartial_comp_affine Lb 0 (paramDir (k := B.length)) (List.ofFn id) (N := B.length)
    (by simp) (x := 0) hsL).self_of_nhds
  have h3 : (fun a : Fin B.length => Lb (paramDir a)) = fun a => paramDir (B.get a) := by
    funext a l
    rw [hLb]
    simp only [paramDir, Pi.single_apply]
    rw [Finset.sum_eq_single a]
    · simp [eq_comm]
    · intro q _ hq
      simp [hq]
    · simp
  change iteratedFDeriv ℝ B.length (fun τ' => h (Lb τ' + 0)) 0 (fun i => paramDir (id i)) = _
  have h2' : iterPartial paramDir (List.ofFn id) (fun z => h (Lb z + 0)) 0 =
      iterPartial (fun a => Lb (paramDir a)) (List.ofFn id) h (Lb 0 + 0) := h2
  rw [h1, h2', h3, hL0, iterPartial_reindex paramDir B.get]
  have h4 : (List.ofFn (id : Fin B.length → Fin B.length)).map B.get = B := by
    rw [List.map_ofFn]
    exact List.ofFn_get B
  rw [h4]
private theorem topBondCells_sublist {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (B : List (Fin k)) :
    topBondCells (fun q : Fin B.length => c (B.get q)) = (B.map fun l => (c l).1).toFinset := by
  ext y
  simp only [topBondCells, Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset,
    List.mem_map]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨B.get q, List.get_mem _ _, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨q, rfl⟩ := List.get_of_mem hl
    exact ⟨q, rfl⟩
private theorem exp_mul_tail_le {δ r d : ℝ} (hδ : 0 < δ) (hr0 : 0 ≤ r) (hr : r ≤ δ / 2) (hd : 0 ≤ d) :
    Real.exp (-(δ * d)) * (Real.exp (r * d) - 1) ≤ r * (4 / δ) * Real.exp (-(δ / 4 * d)) := by
  have h1 : Real.exp (r * d) - 1 ≤ r * d * Real.exp (r * d) := by
    have h2 := Real.add_one_le_exp (-(r * d))
    have h3 : Real.exp (-(r * d)) * Real.exp (r * d) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (r * d)).le
    rw [h3] at h4
    nlinarith
  have h5 : d ≤ 4 / δ * Real.exp (δ / 4 * d) := by
    have h6 := Real.add_one_le_exp (δ / 4 * d)
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    nlinarith
  have h7 : Real.exp (-(δ * d)) * (Real.exp (δ / 4 * d) * Real.exp (r * d)) ≤
      Real.exp (-(δ / 4 * d)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  calc Real.exp (-(δ * d)) * (Real.exp (r * d) - 1)
      ≤ Real.exp (-(δ * d)) * (r * d * Real.exp (r * d)) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ ≤ Real.exp (-(δ * d)) * (r * (4 / δ * Real.exp (δ / 4 * d)) * Real.exp (r * d)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left h5 hr0
    _ = r * (4 / δ) * (Real.exp (-(δ * d)) * (Real.exp (δ / 4 * d) * Real.exp (r * d))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h7 (by positivity)
private theorem resolvent_kernels_abstract {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    {sp : ι → ι → List (Fin k) → ℝ} {S : ℝ → ℝ} (hS : IsSpan sp S)
    (H : (Fin k → ℝ) → Matrix ι ι ℝ) {lam τ δ₂ r₀ D D0 : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hlam : 0 < lam) (hδ : 0 < δ₂) (hr : 0 < r₀) (hrδ : r₀ ≤ δ₂ / 2)
    (hD00 : 0 < D0) (hD0 : 0 ≤ D)
    (hrow : D0 * (r₀ * (4 / δ₂)) * S (δ₂ / 4) ≤ lam / 2)
    (hs : ∀ p q, ∀ m : ℕ, ContDiffAt ℝ m (fun σ => H σ p q) 0)
    (hfloor : ∀ x : ι → ℝ, lam * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, x i * H 0 i j * x j)
    (hsym : ∀ i j, H 0 i j = H 0 j i)
    (hself : ∀ p, sp p p [] = 0) (hcomm : ∀ p q, sp p q [] = sp q p [])
    (hH0 : ∀ p q, |H 0 p q| ≤ D0 * Real.exp (-(δ₂ * sp p q [])))
    (hB : ∀ B : List (Fin k), B ≠ [] → B.length ≤ 6 → ∀ p q,
      |iterPartial paramDir B (fun σ => H σ p q) 0| ≤ D * Real.exp (-(r₀ * sp p q B))) :
    (∀ (m : ℕ) a b, ContDiffAt ℝ m (fun σ => (τ • H σ + (1 - τ) • lam • (1 : Matrix ι ι ℝ))⁻¹ a b) 0) ∧
    ∀ A : List (Fin k), A.length ≤ 6 → ∀ a b,
      |iterPartial paramDir A (fun σ => (τ • H σ + (1 - τ) • lam • (1 : Matrix ι ι ℝ))⁻¹ a b) 0| ≤
        inverseConst S r₀ (2 / lam) D 6 * Real.exp (-(r₀ / 4 ^ 6 * sp a b A)) := by
  set M : (Fin k → ℝ) → Matrix ι ι ℝ := fun σ => τ • H σ + (1 - τ) • lam • (1 : Matrix ι ι ℝ) with hM
  have hent : ∀ σ p q, M σ p q = τ * H σ p q + (1 - τ) * (lam * (1 : Matrix ι ι ℝ) p q) := by
    intro σ p q
    simp [hM, Matrix.add_apply, Matrix.smul_apply]
  have hMs : ∀ p q, ∀ m : ℕ, ContDiffAt ℝ m (fun σ => M σ p q) 0 := by
    intro p q m
    simp only [hent]
    exact (contDiffAt_const.mul (hs p q m)).add contDiffAt_const
  have hform : ∀ v : ι → ℝ, lam * ∑ p, v p ^ 2 ≤ ∑ p, ∑ q, v p * M 0 p q * v q := by
    intro v
    have h1 : ∑ p, ∑ q, v p * M 0 p q * v q =
        τ * ∑ p, ∑ q, v p * H 0 p q * v q + (1 - τ) * (lam * ∑ p, v p ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [hent, Matrix.one_apply, mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun q _ => ?_
        ring
      · rw [Finset.sum_eq_single p]
        · simp
          ring
        · intro q _ hq
          simp [Ne.symm hq]
        · simp
    rw [h1]
    have h2 := hfloor v
    have h3 : 0 ≤ ∑ p, v p ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h2 hτ0]
  have hunit : IsUnit (M 0) := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro u w huw
    have hz : (M 0).mulVec (u - w) = 0 := by
      rw [Matrix.mulVec_sub]
      exact sub_eq_zero.2 huw
    have h1 := hform (u - w)
    have h2 : ∑ p, ∑ q, (u - w) p * M 0 p q * (u - w) q = 0 := by
      have h3 : ∀ p, ∑ q, (u - w) p * M 0 p q * (u - w) q = (u - w) p * (M 0).mulVec (u - w) p := by
        intro p
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
      rw [Finset.sum_congr rfl fun p _ => h3 p]
      simp only [hz, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    rw [h2] at h1
    have h3 : ∑ p, (u - w) p ^ 2 ≤ 0 := by
      by_contra hc
      rw [not_le] at hc
      nlinarith [mul_pos hlam hc]
    have h4 : ∀ p, (u - w) p ^ 2 = 0 := by
      intro p
      have h5 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1
        (le_antisymm h3 (Finset.sum_nonneg fun _ _ => sq_nonneg _)) p (Finset.mem_univ p)
      exact h5
    funext p
    have h6 := pow_eq_zero_iff (two_ne_zero) |>.1 (h4 p)
    exact sub_eq_zero.1 h6
  have hsymM : ∀ p q, M 0 p q = M 0 q p := by
    intro p q
    rw [hent, hent, hsym p q, Matrix.one_apply, Matrix.one_apply]
    simp only [eq_comm]
  have hrowM : ∀ p, ∑ q, |M 0 p q| * (Real.exp (r₀ * sp p q []) - 1) ≤ lam / 2 := by
    intro p
    have hterm : ∀ q, |M 0 p q| * (Real.exp (r₀ * sp p q []) - 1) ≤
        D0 * (r₀ * (4 / δ₂)) * Real.exp (-(δ₂ / 4 * sp p q [])) := by
      intro q
      set dd : ℝ := sp p q [] with hdd
      have hdd0 : 0 ≤ dd := hS.nonneg _ _ _
      by_cases hpq : p = q
      · subst hpq
        have : dd = 0 := hself p
        rw [this]
        simp only [mul_zero, Real.exp_zero, sub_self, neg_zero]
        positivity
      · have h4 : |M 0 p q| ≤ D0 * Real.exp (-(δ₂ * dd)) := by
          rw [hent, Matrix.one_apply_ne hpq]
          simp only [mul_zero, add_zero, abs_mul]
          have : |τ| ≤ 1 := by rw [abs_of_nonneg hτ0]; exact hτ1
          calc |τ| * |H 0 p q| ≤ 1 * |H 0 p q| :=
                mul_le_mul_of_nonneg_right this (abs_nonneg _)
            _ ≤ _ := by rw [one_mul]; exact hH0 p q
        have h5 : 0 ≤ Real.exp (r₀ * dd) - 1 := by
          have := Real.add_one_le_exp (r₀ * dd)
          have h6 : 0 ≤ r₀ * dd := mul_nonneg hr.le hdd0
          linarith
        calc |M 0 p q| * (Real.exp (r₀ * dd) - 1)
            ≤ D0 * Real.exp (-(δ₂ * dd)) * (Real.exp (r₀ * dd) - 1) :=
              mul_le_mul_of_nonneg_right h4 h5
          _ = D0 * (Real.exp (-(δ₂ * dd)) * (Real.exp (r₀ * dd) - 1)) := by ring
          _ ≤ D0 * (r₀ * (4 / δ₂) * Real.exp (-(δ₂ / 4 * dd))) :=
              mul_le_mul_of_nonneg_left (exp_mul_tail_le hδ hr.le hrδ hdd0) hD00.le
          _ = _ := by ring
    have h0 : 0 ≤ D0 * (r₀ * (4 / δ₂)) := by positivity
    calc _ ≤ ∑ q, D0 * (r₀ * (4 / δ₂)) * Real.exp (-(δ₂ / 4 * sp p q [])) :=
          Finset.sum_le_sum fun q _ => hterm q
      _ = D0 * (r₀ * (4 / δ₂)) * ∑ q, Real.exp (-(δ₂ / 4 * sp p q [])) := by
          rw [Finset.mul_sum]
      _ ≤ D0 * (r₀ * (4 / δ₂)) * S (δ₂ / 4) :=
          mul_le_mul_of_nonneg_left (hS.sum_le _ (by positivity) p) h0
      _ ≤ _ := hrow
  have hR : HasKernel sp r₀ (2 / lam) [] (M 0)⁻¹ := by
    intro p q
    exact abs_inv_entry_le_of_schur hlam (fun p q => sp p q []) (M 0) hsymM hself hcomm
      (fun p q s => by
        simpa using hS.triangle p q s [] [] [] (by simp)) hr.le hform hrowM hunit p q
  have hQ : ∀ B : List (Fin k), B ≠ [] → B.length ≤ 6 → ∀ p q,
      |iterPartial paramDir B (fun σ => M σ p q) 0| ≤ D * Real.exp (-(r₀ * sp p q B)) := by
    intro B hB' hl p q
    obtain ⟨v, vs, hvs⟩ := List.exists_cons_of_ne_nil hB'
    have h1 : iterPartial paramDir B (fun σ => M σ p q) 0 =
        τ * iterPartial paramDir B (fun σ => H σ p q) 0 := by
      have h2 : (fun σ => M σ p q) = fun σ =>
          (τ • ContinuousLinearMap.id ℝ ℝ) (H σ p q) + (1 - τ) * (lam * (1 : Matrix ι ι ℝ) p q) := by
        funext σ
        rw [hent]
        simp
      rw [h2, hvs, iterPartial_add_const, ← hvs]
      have h3 := (iterPartial_clm (τ • ContinuousLinearMap.id ℝ ℝ) paramDir B (N := B.length) le_rfl
        (hs p q _)).self_of_nhds
      rw [h3]
      simp
    rw [h1, abs_mul]
    have h3 : |τ| ≤ 1 := by rw [abs_of_nonneg hτ0]; exact hτ1
    calc |τ| * |iterPartial paramDir B (fun σ => H σ p q) 0| ≤
          1 * |iterPartial paramDir B (fun σ => H σ p q) 0| :=
          mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hB B hB' hl p q
  exact kernels_iterPartial_inv (β := Unit) hS M hMs hunit hr (by positivity) hD0 6 hR hQ
private theorem resolvent_kernels_at {a ρ lam τ δ₂ r₀ D : ℝ} {S : ℝ → ℝ} {Dk : ℕ → ℝ}
    {V : F.GaugeField F.top} {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hlam : 0 < lam) (hδ : 0 < δ₂) (hr : 0 < r₀) (hrδ : r₀ ≤ δ₂ / 2)
    (hDk : ∀ j, 0 < Dk j) (hD0 : 0 ≤ D) (hD : ∀ j, j ≤ 6 → Dk j ≤ D)
    (hS : IsSpan (chartSpan c) S)
    (hrow : Dk 0 * (r₀ * (4 / δ₂)) * S (δ₂ / 4) ≤ lam / 2)
    (hH : ∀ (i j : ChartCoord F) (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4)
      (X' : Fin k' → imaginaryQuaternions),
      AreUnitVectors X' →
      (∀ m : ℕ, ContDiffAt ℝ m (fun σ' : Fin k' → ℝ =>
        chartedHessian a ρ (leftTranslate (bondSpread c' X' σ') V) 0 i j) 0) ∧
      |bondDeriv (fun V' => chartedHessian a ρ V' 0 i j) V c' X'| ≤
        Dk k' * Real.exp (-(δ₂ * cellSetDiameter ({enclosingCell i.1.1.1, enclosingCell j.1.1.1} ∪
          topBondCells c'))))
    (hfloor : ∀ x : ChartCoord F → ℝ,
      lam * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, x i * chartedHessian a ρ V 0 i j * x j)
    (hsym : ∀ i j, chartedHessian a ρ V 0 i j = chartedHessian a ρ V 0 j i)
    (hX : AreUnitVectors X) (hk : k ≤ 6) (i j : ChartCoord F) :
    ContDiffAt ℝ ((6 : ℕ) : WithTop ℕ∞) (fun σ' : Fin k → ℝ =>
      hessianResolvent a ρ lam τ (leftTranslate (bondSpread c X σ') V) i j) 0 ∧
    |bondDeriv (fun V' => hessianResolvent a ρ lam τ V' i j) V c X| ≤
      inverseConst S r₀ (2 / lam) D 6 * Real.exp (-(r₀ / 4 ^ 6 *
        cellSetDiameter ({enclosingCell i.1.1.1, enclosingCell j.1.1.1} ∪ topBondCells c))) := by
  have hV0 := leftTranslate_bondSpread_zero c X V
  have hH0 : ∀ p q, |chartedHessian a ρ (leftTranslate (bondSpread c X 0) V) 0 p q| ≤
      Dk 0 * Real.exp (-(δ₂ * chartSpan c p q [])) := by
    intro p q
    have h1 := (hH p q 0 (fun l => l.elim0) (fun l => l.elim0) (fun l => l.elim0)).2
    have h2 : bondDeriv (fun V' => chartedHessian a ρ V' 0 p q) V
        (fun l : Fin 0 => l.elim0) (fun l : Fin 0 => l.elim0) = chartedHessian a ρ V 0 p q := by
      simp only [bondDeriv, iteratedFDeriv_zero_apply]
      have : leftTranslate (bondSpread (fun l : Fin 0 => l.elim0) (fun l : Fin 0 => l.elim0) 0) V = V :=
        leftTranslate_bondSpread_zero _ _ V
      rw [this]
    have h3 : topBondCells (fun l : Fin 0 => (l.elim0 : F.Site F.top × Fin 4)) = ∅ := by
      simp [topBondCells]
    rw [h2, h3, Finset.union_empty, cellSetDiameter_pair] at h1
    rw [chartSpan_nil, hV0]
    exact h1
  have hB : ∀ B : List (Fin k), B ≠ [] → B.length ≤ 6 → ∀ p q,
      |iterPartial paramDir B (fun σ => chartedHessian a ρ (leftTranslate (bondSpread c X σ) V) 0 p q) 0| ≤
        D * Real.exp (-(r₀ * chartSpan c p q B)) := by
    intro B hB' hl p q
    have hs := (hH p q k c X hX).1
    have h2 := (hH p q B.length (fun q' => c (B.get q')) (fun q' => X (B.get q'))
      (fun l => hX _)).2
    rw [bondDeriv_sublist (fun V' => chartedHessian a ρ V' 0 p q) V c X hs B, topBondCells_sublist] at h2
    have h4 : Real.exp (-(δ₂ * (cellSetDiameter ({enclosingCell p.1.1.1, enclosingCell q.1.1.1} ∪
        (B.map fun l => (c l).1).toFinset) : ℕ))) ≤ Real.exp (-(r₀ * chartSpan c p q B)) := by
      apply Real.exp_le_exp.2
      have h5 : 0 ≤ chartSpan c p q B := hS.nonneg p q B
      have h6 : r₀ ≤ δ₂ := by linarith
      simp only [chartSpan] at h5 ⊢
      nlinarith
    calc _ ≤ Dk B.length * Real.exp (-(r₀ * chartSpan c p q B)) :=
          h2.trans (mul_le_mul_of_nonneg_left h4 (hDk _).le)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hD _ hl) (Real.exp_pos _).le
  obtain ⟨hsm, hb⟩ := resolvent_kernels_abstract hS
    (fun σ => chartedHessian a ρ (leftTranslate (bondSpread c X σ) V) 0) hτ0 hτ1 hlam hδ hr hrδ (hDk 0)
    hD0 hrow
    (fun p q m => (hH p q k c X hX).1 m)
    (by simpa only [hV0] using hfloor) (by simpa only [hV0] using hsym)
    (fun p => by simp [chartSpan_nil, cellSupDist_self_zero])
    (fun p q => by simp [chartSpan_nil, cellSupDist_symm])
    hH0 hB
  refine ⟨hsm 6 i j, ?_⟩
  have hspan : chartSpan c i j (List.ofFn id) =
      (cellSetDiameter ({enclosingCell i.1.1.1, enclosingCell j.1.1.1} ∪ topBondCells c) : ℕ) := by
    simp only [chartSpan]
    congr 3
  have hfin := hb (List.ofFn id) (by simpa using hk) i j
  rw [hspan] at hfin
  have hpd := iteratedFDeriv_eq_iterPartial (paramDir (k := k)) k id 0 ((hsm k i j))
  have : bondDeriv (fun V' => hessianResolvent a ρ lam τ V' i j) V c X =
      iterPartial paramDir (List.ofFn id)
        (fun σ => (τ • chartedHessian a ρ (leftTranslate (bondSpread c X σ) V) 0 +
        (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ))⁻¹ i j) 0 := hpd
  rw [this]
  exact hfin
end Assembly
section Table
private def decayRate (δ₂ lam D0 Sv : ℝ) : ℝ := min (δ₂ / 2) (lam * δ₂ / (8 * D0 * (Sv + 1)))
private theorem decayRate_spec {δ₂ lam D0 Sv : ℝ} (hδ : 0 < δ₂) (hlam : 0 < lam) (hD : 0 < D0) (hS : 0 ≤ Sv) :
    0 < decayRate δ₂ lam D0 Sv ∧ decayRate δ₂ lam D0 Sv ≤ δ₂ / 2 ∧
      D0 * (decayRate δ₂ lam D0 Sv * (4 / δ₂)) * Sv ≤ lam / 2 := by
  have hden : 0 < 8 * D0 * (Sv + 1) := by positivity
  have hpos : 0 < decayRate δ₂ lam D0 Sv := lt_min (by positivity) (by positivity)
  refine ⟨hpos, min_le_left _ _, ?_⟩
  set r := decayRate δ₂ lam D0 Sv with hr
  have h1 : r * (8 * D0 * (Sv + 1)) ≤ lam * δ₂ := by
    have : r ≤ lam * δ₂ / (8 * D0 * (Sv + 1)) := min_le_right _ _
    rwa [le_div_iff₀ hden] at this
  have h2 : D0 * (r * (4 / δ₂)) * Sv = 4 * D0 * r * Sv / δ₂ := by
    field_simp
  rw [h2, div_le_iff₀ hδ]
  have h3 : 0 ≤ r * D0 := by positivity
  nlinarith
variable {F : BlockFrame}
private theorem mix_det_ne_zero {lam τ : ℝ} (M : Matrix (ChartCoord F) (ChartCoord F) ℝ)
    (hlam : 0 < lam) (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (hfl : ∀ x : ChartCoord F → ℝ, lam * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, x i * M i j * x j) :
    (τ • M + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hN⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hform := hfl v
  have e1 : ∑ i, v i * ((τ • M + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)).mulVec v) i
      = 0 := by
    simp [hN]
  have e2 : ∑ i, v i * ((τ • M + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)).mulVec v) i =
      τ * ∑ i, ∑ j, v i * M i j * v j + (1 - τ) * lam * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ((τ • M + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)).mulVec v) i =
        τ * ∑ j, M i j * v j + (1 - τ) * lam * v i := by
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
      ring
    rw [this, Finset.mul_sum]
    simp only [mul_add, Finset.mul_sum]
    have hs : ∑ j, v i * (τ * (M i j * v j)) = ∑ j, τ * (v i * M i j * v j) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [hs]
    ring
  have hpos : 0 < ∑ i, v i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    refine Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩
    have : v i ≠ 0 := hi
    positivity
  rw [e1] at e2
  nlinarith [mul_le_mul_of_nonneg_left hform h0, mul_pos hlam hpos]
end Table
end ResolventKernels
namespace RunningCouplingSlope
open ResolventKernels
theorem minimizerResolventDecay_holds (h₁ : hessianDerivBoundStatement)
    (h₂ : energyAtMinimizerDerivBoundStatement) (h₃ : MinimizerAtReachableColdness)
    (h₄ : SiteDecomposition) : MinimizerResolventDecay := by
  intro a L cn ha hL hL40 hcn
  obtain ⟨Dk, hDk, g₁⟩ := h₁ a L cn ha hL hL40 hcn
  obtain ⟨DK, hDK, g₂⟩ := h₂ a L cn ha hL hL40 hcn
  have hδ₁ : 0 < cn.δ₁ := hcn.positivity.1
  have hδ : 0 < cn.δ₁ / 4 := by positivity
  have hlam : 0 < cn.lam := hcn.positivity.2.2.1
  obtain ⟨hr0, hr1, hrow⟩ := decayRate_spec (Sv := chartSumBound L (cn.δ₁ / 4 / 4)) hδ hlam (hDk 0)
    (chartSumBound_nonneg _ _)
  set r₀ := decayRate (cn.δ₁ / 4) cn.lam (Dk 0) (chartSumBound L (cn.δ₁ / 4 / 4)) with hr₀
  have hD0 : 0 ≤ ∑ j ∈ Finset.range 7, Dk j := Finset.sum_nonneg fun j _ => (hDk j).le
  have hD : ∀ j, j ≤ 6 → Dk j ≤ ∑ j ∈ Finset.range 7, Dk j := fun j hj =>
    Finset.single_le_sum (f := Dk) (fun j _ => (hDk j).le) (Finset.mem_range.2 (by omega))
  have floor_at : ∀ (F : BlockFrame) (s : ℝ) (V : F.GaugeField F.top), IsBlockTorus L F →
      ColdChain.IsReachableColdness cn L s →
      IsSmallCurvature s V → ∀ i₀ : ChartCoord F, ContDiffAt ℝ 2 (chartedEnergyAtMinimizer a cn.ρA V) 0 ∧
        ∀ x : ChartCoord F → ℝ,
          cn.lam * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, x i * chartedHessian a cn.ρA V 0 i j * x j := by
    intro F s V hF hs hV i₀
    obtain ⟨hleast, -, hcold2, -, -⟩ := h₃ a L cn ha hL hL40 hcn F s V hF hs hV
    have hcl := hcn.estimates F s V hF hs.pos hs.le_bound hV
    have hcoldA : IsCold (finiteCells F) F.depth cn.σA
        (chartedField (minimizingCoordinates a (finiteCells F) V cn.ρA) V) := by
      intro p hp
      simp only [innerPlaquettes, Finset.mem_filter] at hp
      refine lt_of_lt_of_le (hcold2 p hp.2.1) ?_
      have h1 := hs.pos
      have h2 := hs.le_bound
      linarith
    have hC2 := contDiffAt_chartedEnergyAtMinimizer (fun l b u hl hu =>
      (g₂ F s V hF hs hV l 0 b u (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0) hl hu
        (fun i => i.elim0)).1) i₀
    exact ⟨hC2, chartedHessian_floor hcl.hessian hleast hcoldA hC2⟩
  refine ⟨r₀ / 4 ^ 6, fun _ => |inverseConst (chartSumBound L) r₀ (2 / cn.lam)
    (∑ j ∈ Finset.range 7, Dk j) 6| + 1, by positivity, fun _ => by positivity, ?_, ?_⟩
  · intro F s V τ hF hs hV hτ0 hτ1
    by_cases hE : Nonempty (ChartCoord F)
    · exact mix_det_ne_zero _ hlam hτ0 hτ1 (floor_at F s V hF hs hV hE.some).2
    · have : IsEmpty (ChartCoord F) := not_nonempty_iff.1 hE
      simp
  intro F s V τ i j k c X hF hs hV hτ0 hτ1 hk hX
  obtain ⟨hC2, hfl⟩ := floor_at F s V hF hs hV i
  have hFL := hF.1
  obtain ⟨n, hn64, hside⟩ := hF.2
  have hodd : Odd F.blockSide := hFL ▸ hL
  have hside2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside]; omega
  have hper : ∀ i, F.period F.top i ≠ 0 := by
    intro i
    have hL0 : F.blockSide ≠ 0 := fun h => by simp [h] at hodd
    simp only [BlockFrame.period, hside]
    simp
    omega
  have hS := isSpan_chartSpan h₄ hodd hside2 hper c
  rw [hFL] at hS
  have res := resolvent_kernels_at (a := a) (ρ := cn.ρA) (lam := cn.lam) (τ := τ) (δ₂ := cn.δ₁ / 4) c X
    hτ0 hτ1 hlam hδ hr0 hr1 hDk hD0 hD hS hrow
    (fun i j k' c' X' hX' => g₁ F s V i j k' c' X' hF hs hV hX') hfl
    (fun i j => chartedHessian_symm i j hC2) hX hk i j
  refine ⟨by exact_mod_cast res.1, res.2.trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have := le_abs_self (inverseConst (chartSumBound L) r₀ (2 / cn.lam) (∑ j ∈ Finset.range 7, Dk j) 6)
  linarith
end RunningCouplingSlope
end YangMills.Construction
end

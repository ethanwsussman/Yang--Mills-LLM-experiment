import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongParametersOfAFamilyProofForm
import Mathlib
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
namespace YangMills.Construction.Dilation
theorem coe_nat_ne_infty (n : ℕ) : ((n : ℕ) : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
section Iterated
variable {E G H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
theorem iteratedFDeriv_comp_linear_add_eval {n : ℕ} {f : E → H} (L : G →L[ℝ] E) (a : E) {x : G}
    (hf : ContDiffAt ℝ n f (L x + a)) {i : ℕ} (hi : i ≤ n) (v : Fin i → G) :
    iteratedFDeriv ℝ i (fun z => f (L z + a)) x v = iteratedFDeriv ℝ i f (L x + a) fun j => L (v j) := by apply _root_.YangMills.SharedProofs.p13665 <;> assumption
theorem iteratedFDeriv_succ_cons_eval {n : ℕ} {f : E → H} {x : E} (hf : ContDiffAt ℝ (n + 1 : ℕ) f x)
    (a : E) (u : Fin n → E) :
    iteratedFDeriv ℝ (n + 1) f x (Fin.cons a u) =
      fderiv ℝ (fun y => iteratedFDeriv ℝ n f y u) x a := by apply _root_.YangMills.Construction.ParameterListDerivatives.iteratedFDeriv_succ_cons_eq_fderiv <;> assumption
theorem fderiv_clm_eval {Ψ : E → G →L[ℝ] H} {x : E} (h : DifferentiableAt ℝ Ψ x) (a : E) (b : G) :
    (fderiv ℝ Ψ x a) b = fderiv ℝ (fun y => Ψ y b) x a := by
  have h1 := ((ContinuousLinearMap.apply ℝ H b).hasFDerivAt.comp x h.hasFDerivAt).fderiv
  have h2 : (fun y => Ψ y b) = (ContinuousLinearMap.apply ℝ H b) ∘ Ψ := rfl
  rw [h2, h1]
  rfl
theorem contDiffAt_iteratedFDeriv_eval {n m i : ℕ} {f : E → H} {x : E} (hf : ContDiffAt ℝ n f x)
    (hmn : m + i ≤ n) (u : Fin i → E) :
    ContDiffAt ℝ m (fun y => iteratedFDeriv ℝ i f y u) x := by apply _root_.YangMills.Construction.ParameterListDerivatives.contDiffAt_iteratedFDeriv_eval <;> assumption
theorem contDiffAt_fderiv_eval {n : ℕ} {f : E → H} {x : E} (hf : ContDiffAt ℝ (n + 1 : ℕ) f x) (e : E) :
    ContDiffAt ℝ n (fun y => fderiv ℝ f y e) x := by
  have h1 : ContDiffAt ℝ n (fderiv ℝ f) x := hf.fderiv_right (by norm_cast)
  exact ((ContinuousLinearMap.apply ℝ H e).contDiff.contDiffAt).comp x h1
theorem iteratedFDeriv_fderiv_eval_comm : ∀ (j : ℕ) (f : E → H) (x : E), ContDiffAt ℝ (j + 2 : ℕ) f x →
    ∀ (w : Fin j → E) (e : E), iteratedFDeriv ℝ j (fun y => fderiv ℝ f y e) x w =
      fderiv ℝ (fun y => iteratedFDeriv ℝ j f y w) x e := by
  intro j
  induction j with
  | zero =>
    intro f x _ w e
    simp only [iteratedFDeriv_zero_apply]
  | succ j ih =>
    intro f x hf w e
    set r : Fin j → E := Fin.tail w with hr
    set a : E := w 0 with ha
    have hw : w = Fin.cons a r := (Fin.cons_self_tail w).symm
    set A : E → H := fun y => iteratedFDeriv ℝ j f y r with hA
    have hA2 : ContDiffAt ℝ 2 A x := by
      exact_mod_cast contDiffAt_iteratedFDeriv_eval (m := 2) hf (by omega) r
    have hg : ContDiffAt ℝ (j + 1 : ℕ) (fun y => fderiv ℝ f y e) x :=
      contDiffAt_fderiv_eval (hf.of_le (by norm_cast; omega)) e
    have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ (j + 2 : ℕ) f y :=
      (hf.of_le (by norm_cast; omega)).eventually (coe_nat_ne_infty _)
    have hd : DifferentiableAt ℝ (fderiv ℝ A) x :=
      (hA2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    rw [hw, iteratedFDeriv_succ_cons_eval hg a r]
    have e1 : (fun y => iteratedFDeriv ℝ j (fun y' => fderiv ℝ f y' e) y r) =ᶠ[𝓝 x]
        fun y => fderiv ℝ A y e := by
      filter_upwards [hev] with y hy
      exact ih f y hy r e
    rw [e1.fderiv_eq, ← fderiv_clm_eval hd a e, hA2.isSymmSndFDerivAt (by simp) a e,
      fderiv_clm_eval hd e a]
    have e2 : (fun y => fderiv ℝ A y a) =ᶠ[𝓝 x] fun y => iteratedFDeriv ℝ (j + 1) f y (Fin.cons a r) := by
      filter_upwards [hev] with y hy
      exact (iteratedFDeriv_succ_cons_eval (hy.of_le (by norm_cast; omega)) a r).symm
    rw [e2.fderiv_eq]
end Iterated
section Second
variable {E₁ E₂ H : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂] [NormedAddCommGroup H] [NormedSpace ℝ H]
def secondJet (f : E₁ × E₂ → H) (y : E₂) {k : ℕ} (w : Fin k → E₂) (x : E₁) : H :=
  iteratedFDeriv ℝ k (fun y' => f (x, y')) y w
theorem secondJet_eq {n k : ℕ} {f : E₁ × E₂ → H} {x : E₁} {y : E₂} (hf : ContDiffAt ℝ n f (x, y))
    (hk : k ≤ n) (w : Fin k → E₂) :
    secondJet f y w x = iteratedFDeriv ℝ k f (x, y) fun j => (0, w j) := by
  have h := iteratedFDeriv_comp_linear_add_eval (ContinuousLinearMap.inr ℝ E₁ E₂) (x, 0) (x := y) (f := f)
    (by simpa using hf) hk w
  have e1 : (fun z => f ((ContinuousLinearMap.inr ℝ E₁ E₂) z + (x, 0))) = fun y' => f (x, y') := by
    funext z; simp
  rw [e1] at h
  simp only [secondJet]
  rw [h]
  simp
theorem eventually_contDiffAt_fst {n : ℕ} {f : E₁ × E₂ → H} {x : E₁} {y : E₂} (hf : ContDiffAt ℝ n f (x, y)) :
    ∀ᶠ x' in 𝓝 x, ContDiffAt ℝ n f (x', y) := by apply _root_.YangMills.Construction.ParameterListDerivatives.eventually_contDiffAt_left <;> assumption
theorem contDiffAt_secondJet {n m k : ℕ} {f : E₁ × E₂ → H} {x : E₁} {y : E₂}
    (hf : ContDiffAt ℝ n f (x, y)) (hmn : m + k ≤ n) (w : Fin k → E₂) :
    ContDiffAt ℝ m (secondJet f y w) x := by
  have h1 : ContDiffAt ℝ m (fun z => iteratedFDeriv ℝ k f z fun j => (0, w j)) (x, y) :=
    contDiffAt_iteratedFDeriv_eval hf hmn _
  have h2 : ContDiffAt ℝ m (fun x' : E₁ => (x', y)) x := by fun_prop
  have h3 : ContDiffAt ℝ m (fun x' => iteratedFDeriv ℝ k f (x', y) fun j => (0, w j)) x :=
    ContDiffAt.comp x (g := fun z => iteratedFDeriv ℝ k f z fun j => (0, w j)) h1 h2
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [eventually_contDiffAt_fst hf] with x' hx'
  exact secondJet_eq hx' (by omega) w
def IsSplitTuple {m p k : ℕ} (v : Fin p → E₁) (w : Fin k → E₂) (u : Fin m → E₁ × E₂) : Prop :=
  m = p + k ∧ (∀ (i : Fin m) (hi : i.val < p), u i = (v ⟨i.val, hi⟩, 0)) ∧
    ∀ (i : Fin m) (hi : p ≤ i.val) (hk : i.val - p < k), u i = (0, w ⟨i.val - p, hk⟩)
theorem iteratedFDeriv_secondJet {k : ℕ} (w : Fin k → E₂) {n : ℕ} {f : E₁ × E₂ → H} {y : E₂} :
    ∀ (p m : ℕ) (v : Fin p → E₁) (u : Fin m → E₁ × E₂) (x : E₁), IsSplitTuple v w u →
      ContDiffAt ℝ n f (x, y) → m ≤ n →
      iteratedFDeriv ℝ p (secondJet f y w) x v = iteratedFDeriv ℝ m f (x, y) u := by
  intro p
  induction p with
  | zero =>
    intro m v u x hu hf hm
    obtain ⟨h0, -, h2⟩ := hu
    have : m = k := by omega
    subst this
    have hu' : u = fun j => (0, w j) := by
      funext j
      have := h2 j (Nat.zero_le _) (by simpa using j.2)
      simpa using this
    rw [hu', ← secondJet_eq hf hm w]
    simp
  | succ p ih =>
    intro m v u x hu hf hm
    obtain ⟨h0, h1, h2⟩ := hu
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hR : ContDiffAt ℝ (p + 1 : ℕ) (secondJet f y w) x :=
      contDiffAt_secondJet hf (by omega) w
    have hf' : ContDiffAt ℝ (m' + 1 : ℕ) f (x, y) := hf.of_le (by exact_mod_cast hm)
    have hu0 : u 0 = (v 0, 0) := h1 0 (by simp)
    have ht : IsSplitTuple (Fin.tail v) w (Fin.tail u) := by
      refine ⟨by omega, fun i hi => ?_, fun i hi hk => ?_⟩
      · have := h1 i.succ (by simpa using hi)
        simpa [Fin.tail_def] using this
      · have := h2 i.succ (by simp; omega) (by simp; omega)
        simp only [Fin.tail_def]
        rw [this]
        congr 2
        apply Fin.ext
        simp
    have e1 := iteratedFDeriv_succ_cons_eval hR (v 0) (Fin.tail v)
    have e2 := iteratedFDeriv_succ_cons_eval hf' (u 0) (Fin.tail u)
    rw [Fin.cons_self_tail] at e1 e2
    rw [e1, e2]
    have hev : (fun x' => iteratedFDeriv ℝ p (secondJet f y w) x' (Fin.tail v)) =ᶠ[𝓝 x]
        fun x' => iteratedFDeriv ℝ m' f (x', y) (Fin.tail u) := by
      filter_upwards [eventually_contDiffAt_fst hf] with x' hx'
      exact ih m' _ _ x' ht hx' (by omega)
    rw [hev.fderiv_eq, hu0]
    have hd : DifferentiableAt ℝ (fun z => iteratedFDeriv ℝ m' f z (Fin.tail u)) (x, y) :=
      (contDiffAt_iteratedFDeriv_eval (m := 1) hf (by omega) _).differentiableAt (by norm_num)
    have hc : HasFDerivAt (fun x' : E₁ => (x', y)) (ContinuousLinearMap.inl ℝ E₁ E₂) x :=
      hasFDerivAt_prodMk_left x y
    have := (hd.hasFDerivAt.comp x hc).fderiv
    have e3 : (fun x' => iteratedFDeriv ℝ m' f (x', y) (Fin.tail u)) =
      (fun z => iteratedFDeriv ℝ m' f z (Fin.tail u)) ∘ fun x' : E₁ => (x', y) := rfl
    rw [e3, this]
    simp
theorem secondJet_fderiv_eval {k : ℕ} {f : E₁ × E₂ → H} {x : E₁} {y : E₂} (hf : ContDiffAt ℝ (k + 2 : ℕ) f (x, y))
    (w : Fin k → E₂) (e : E₁) :
    secondJet (fun z => fderiv ℝ f z (e, 0)) y w x = fderiv ℝ (secondJet f y w) x e := by
  have hs : ContDiffAt ℝ (k + 1 : ℕ) (fun z => fderiv ℝ f z (e, 0)) (x, y) := contDiffAt_fderiv_eval hf _
  rw [secondJet_eq hs (by omega) w, iteratedFDeriv_fderiv_eval_comm k f (x, y) hf]
  have hev : secondJet f y w =ᶠ[𝓝 x] fun x' => iteratedFDeriv ℝ k f (x', y) fun j => (0, w j) := by
    filter_upwards [eventually_contDiffAt_fst hf] with x' hx'
    exact secondJet_eq hx' (by omega) w
  rw [hev.fderiv_eq]
  have hd : DifferentiableAt ℝ (fun z => iteratedFDeriv ℝ k f z fun j => (0, w j)) (x, y) :=
    (contDiffAt_iteratedFDeriv_eval (m := 1) hf (by omega) _).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun x' : E₁ => (x', y)) (ContinuousLinearMap.inl ℝ E₁ E₂) x :=
    hasFDerivAt_prodMk_left x y
  have := (hd.hasFDerivAt.comp x hc).fderiv
  have e3 : (fun x' => iteratedFDeriv ℝ k f (x', y) fun j => (0, w j)) =
    (fun z => iteratedFDeriv ℝ k f z fun j => (0, w j)) ∘ fun x' : E₁ => (x', y) := rfl
  rw [e3, this]
  simp
end Second
section Integral
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem eventually_contDiffAt_tube {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ} {Φ : E × ℝ → F} {z : E}
    (hΦ : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ m Φ (z, v)) :
    ∀ᶠ y in 𝓝 z, ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ m Φ (y, v) := by
  have hW : IsOpen {p : E × ℝ | ContDiffAt ℝ m Φ p} := isOpen_iff_mem_nhds.2 fun p hp =>
    (show ContDiffAt ℝ m Φ p from hp).eventually (coe_nat_ne_infty _)
  have hsub : ({z} : Set E) ×ˢ Icc (0 : ℝ) 1 ⊆ {p : E × ℝ | ContDiffAt ℝ m Φ p} := by
    rintro ⟨y, v⟩ ⟨hy, hv⟩
    obtain rfl : y = z := hy
    exact hΦ v hv
  obtain ⟨u, w, hu, -, hzu, hIw, huw⟩ := generalized_tube_lemma isCompact_singleton isCompact_Icc hW hsub
  filter_upwards [hu.mem_nhds (hzu rfl)] with y hy v hv
  exact huw ⟨hy, hIw hv⟩
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
theorem intervalIntegrable_unit_slice {Φ : E × ℝ → F} {z : E} (hΦ : ∀ v ∈ Icc (0 : ℝ) 1, ContinuousAt Φ (z, v)) :
    IntervalIntegrable (fun v => Φ (z, v)) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le zero_le_one]
  intro v hv
  exact ((hΦ v hv).comp (f := fun v : ℝ => (z, v)) (by fun_prop)).continuousWithinAt
def partialFst (Φ : E × ℝ → F) (p : E × ℝ) : E →L[ℝ] F := (fderiv ℝ Φ p).comp (ContinuousLinearMap.inl ℝ E ℝ)
theorem contDiffAt_partialFst {n : ℕ} {Φ : E × ℝ → F} {p : E × ℝ} (h : ContDiffAt ℝ (n + 1 : ℕ) Φ p) :
    ContDiffAt ℝ n (partialFst Φ) p :=
  (h.fderiv_right (m := n) (by norm_cast)).clm_comp contDiffAt_const
theorem eventually_hasFDerivAt_intervalIntegral_unit {Φ : E × ℝ → F} {z : E}
    (hΦ : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (1 : ℕ) Φ (z, v)) :
    ∀ᶠ y in 𝓝 z, HasFDerivAt (fun y => ∫ v in (0 : ℝ)..1, Φ (y, v))
      (∫ v in (0 : ℝ)..1, partialFst Φ (y, v)) y := by
  set W : Set (E × ℝ) := {p | ContDiffAt ℝ (1 : ℕ) Φ p} with hWdef
  have hW : IsOpen W := isOpen_iff_mem_nhds.2 fun p hp =>
    (show ContDiffAt ℝ (1 : ℕ) Φ p from hp).eventually (coe_nat_ne_infty _)
  have hDc : ContinuousOn (partialFst Φ) W := fun p hp =>
    (contDiffAt_partialFst (n := 0) (by simpa using (show ContDiffAt ℝ (1 : ℕ) Φ p from hp))).continuousAt.continuousWithinAt
  have hC : IsCompact (({z} : Set E) ×ˢ Icc (0 : ℝ) 1) := isCompact_singleton.prod isCompact_Icc
  have hCW : ({z} : Set E) ×ˢ Icc (0 : ℝ) 1 ⊆ W := by
    rintro ⟨y, v⟩ ⟨hy, hv⟩
    obtain rfl : y = z := hy
    exact hΦ v hv
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn (hDc.mono hCW)
  have hn : IsOpen (W ∩ partialFst Φ ⁻¹' Metric.ball 0 (B + 1)) :=
    hDc.isOpen_inter_preimage hW Metric.isOpen_ball
  have hsub : ({z} : Set E) ×ˢ Icc (0 : ℝ) 1 ⊆ W ∩ partialFst Φ ⁻¹' Metric.ball 0 (B + 1) := by
    intro p hp
    refine ⟨hCW hp, ?_⟩
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right]
    linarith [hB p hp]
  obtain ⟨u, w, hu, -, hzu, hIw, huw⟩ := generalized_tube_lemma isCompact_singleton isCompact_Icc hn hsub
  have hmem : ∀ y ∈ u, ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (1 : ℕ) Φ (y, v) ∧ ‖partialFst Φ (y, v)‖ < B + 1 := by
    intro y hy v hv
    have h := huw (show (y, v) ∈ u ×ˢ w from ⟨hy, hIw hv⟩)
    refine ⟨h.1, ?_⟩
    simpa using h.2
  filter_upwards [hu.mem_nhds (hzu rfl)] with y hy
  have hIoc : ∀ t ∈ Set.uIoc (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := fun t ht => by
    rw [uIoc_of_le zero_le_one] at ht
    exact ⟨ht.1.le, ht.2⟩
  have hcs : ∀ x ∈ u, ContinuousOn (fun v => Φ (x, v)) (Set.uIoc (0 : ℝ) 1) := fun x hx v hv =>
    (((hmem x hx v (hIoc v hv)).1.continuousAt).comp (f := fun v : ℝ => (x, v)) (by fun_prop)).continuousWithinAt
  have hcd : ContinuousOn (fun v => partialFst Φ (y, v)) (Set.uIoc (0 : ℝ) 1) := fun v hv =>
    ((contDiffAt_partialFst (n := 0) (by simpa using (hmem y hy v (hIoc v hv)).1)).continuousAt.comp
      (f := fun v : ℝ => (y, v)) (by fun_prop)).continuousWithinAt
  exact (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun x v => Φ (x, v)) (F' := fun x v => partialFst Φ (x, v)) (bound := fun _ => B + 1) (s := u)
    (hu.mem_nhds hy)
    (by
      filter_upwards [hu.mem_nhds hy] with x hx
      exact (hcs x hx).aestronglyMeasurable measurableSet_uIoc)
    (intervalIntegrable_unit_slice fun v hv => (hmem y hy v hv).1.continuousAt)
    (hcd.aestronglyMeasurable measurableSet_uIoc)
    (Eventually.of_forall fun t ht x hx => (hmem x hx t (hIoc t ht)).2.le)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht x hx => by
      have h1 := ((hmem x hx t (hIoc t ht)).1.differentiableAt (by norm_num)).hasFDerivAt
      exact h1.comp x (hasFDerivAt_prodMk_left x t)))
theorem contDiffAt_intervalIntegral_unit (n : ℕ) : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Φ : E × ℝ → F) (z : E), (∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1 : ℕ) Φ (z, v)) →
    ContDiffAt ℝ n (fun y => ∫ v in (0 : ℝ)..1, Φ (y, v)) z := by
  induction n with
  | zero =>
    intro F _ _ _ Φ z hΦ
    have h := eventually_hasFDerivAt_intervalIntegral_unit (Φ := Φ) (z := z) (by simpa using hΦ)
    obtain ⟨u, hu, huh⟩ := h.exists_mem
    have : ContDiffAt ℝ 0 (fun y => ∫ v in (0 : ℝ)..1, Φ (y, v)) z :=
      contDiffAt_zero.2 ⟨u, hu, fun y hy => (huh y hy).continuousAt.continuousWithinAt⟩
    simpa using this
  | succ n ih =>
    intro F _ _ _ Φ z hΦ
    have hD : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1 : ℕ) (partialFst Φ) (z, v) := fun v hv =>
      contDiffAt_partialFst (hΦ v hv)
    have h1 := ih (E →L[ℝ] F) (partialFst Φ) z hD
    have h := eventually_hasFDerivAt_intervalIntegral_unit (Φ := Φ) (z := z) fun v hv => (hΦ v hv).of_le (by norm_cast; omega)
    obtain ⟨u, hu, huh⟩ := h.exists_mem
    have : ContDiffAt ℝ ((n : WithTop ℕ∞) + 1) (fun y => ∫ v in (0 : ℝ)..1, Φ (y, v)) z :=
      contDiffAt_succ_iff_hasFDerivAt.2 ⟨fun y => ∫ v in (0 : ℝ)..1, partialFst Φ (y, v), ⟨u, hu, huh⟩, h1⟩
    exact_mod_cast this
theorem iteratedFDeriv_slice_eval {n : ℕ} {Φ : E × ℝ → F} {z : E} {v : ℝ} (h : ContDiffAt ℝ n Φ (z, v)) (w : Fin n → E) :
    iteratedFDeriv ℝ n Φ (z, v) (fun i => (w i, 0)) = iteratedFDeriv ℝ n (fun y => Φ (y, v)) z w := by
  have h1 := iteratedFDeriv_comp_linear_add_eval (ContinuousLinearMap.inl ℝ E ℝ) ((0 : E), v) (x := z) (f := Φ)
    (by simpa using h) le_rfl w
  have e1 : (fun y => Φ ((ContinuousLinearMap.inl ℝ E ℝ) y + ((0 : E), v))) = fun y => Φ (y, v) := by
    funext y; simp
  rw [e1] at h1
  rw [h1]
  simp
theorem iteratedFDeriv_intervalIntegral_eval (n : ℕ) : ∀ (Φ : E × ℝ → F) (z : E), (∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1 : ℕ) Φ (z, v)) →
    ∀ w : Fin n → E, iteratedFDeriv ℝ n (fun y => ∫ v in (0 : ℝ)..1, Φ (y, v)) z w =
      ∫ v in (0 : ℝ)..1, iteratedFDeriv ℝ n Φ (z, v) (fun i => (w i, 0)) := by
  induction n with
  | zero =>
    intro Φ z _ w
    simp only [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro Φ z hΦ w
    set r : Fin n → E := Fin.tail w with hr
    set a : E := w 0 with ha
    have hw : w = Fin.cons a r := (Fin.cons_self_tail w).symm
    have hI : ContDiffAt ℝ (n + 1 : ℕ) (fun y => ∫ v in (0 : ℝ)..1, Φ (y, v)) z :=
      contDiffAt_intervalIntegral_unit (n + 1) F Φ z hΦ
    rw [hw, iteratedFDeriv_succ_cons_eval hI a r]
    have ht : ∀ᶠ y in 𝓝 z, ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1 : ℕ) Φ (y, v) :=
      eventually_contDiffAt_tube fun v hv => (hΦ v hv).of_le (by norm_cast; omega)
    set r' : Fin n → E × ℝ := fun i => (r i, 0) with hr'
    have e1 : (fun y => iteratedFDeriv ℝ n (fun y' => ∫ v in (0 : ℝ)..1, Φ (y', v)) y r) =ᶠ[𝓝 z]
        fun y => ∫ v in (0 : ℝ)..1, iteratedFDeriv ℝ n Φ (y, v) r' := by
      filter_upwards [ht] with y hy
      exact ih Φ y hy r
    rw [e1.fderiv_eq]
    set Φ₂ : E × ℝ → F := fun p => iteratedFDeriv ℝ n Φ p r' with hΦ₂
    have h2 : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (1 : ℕ) Φ₂ (z, v) := fun v hv =>
      contDiffAt_iteratedFDeriv_eval (hΦ v hv) (by omega) r'
    have hk := (eventually_hasFDerivAt_intervalIntegral_unit (Φ := Φ₂) (z := z) h2).self_of_nhds
    rw [hk.fderiv, ContinuousLinearMap.intervalIntegral_apply (intervalIntegrable_unit_slice fun v hv =>
      (contDiffAt_partialFst (n := 0) (by simpa using h2 v hv)).continuousAt)]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le zero_le_one] at hv
    show (fderiv ℝ Φ₂ (z, v)) ((ContinuousLinearMap.inl ℝ E ℝ) a) = _
    have e2 : (fun i => ((Fin.cons a r : Fin (n + 1) → E) i, (0 : ℝ))) = Fin.cons (a, (0 : ℝ)) r' := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [hr']
    rw [e2, iteratedFDeriv_succ_cons_eval ((hΦ v hv).of_le (by norm_cast; omega))]
    rfl
end Integral
section Line
theorem abs_trapezoid_le {g g' g'' : ℝ → ℝ} {M : ℝ} (h1 : ∀ v ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' v) v)
    (h2 : ∀ v ∈ Icc (0 : ℝ) 1, HasDerivAt g' (g'' v) v) (hM : ∀ v ∈ Icc (0 : ℝ) 1, |g'' v| ≤ M) :
    |g 1 - 2 * (∫ v in (0 : ℝ)..1, g v) + g 0| ≤ 3 * M := by
  have mem0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have mem1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 mem0)
  have hg1 : ∀ v ∈ Icc (0 : ℝ) 1, ‖g' v - g' 0‖ ≤ M := by
    intro v hv
    have h3 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Icc (0 : ℝ) 1) (f := g') (f' := g'')
      (C := M) (fun y hy => (h2 y hy).hasDerivWithinAt) (fun y hy => hM y hy) (convex_Icc _ _) mem0 hv
    rw [Real.norm_eq_abs (v - 0), sub_zero, abs_of_nonneg hv.1] at h3
    calc _ ≤ M * v := h3
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left hv.2 hM0
      _ = M := mul_one _
  set h : ℝ → ℝ := fun v => g v - g 0 - v * g' 0 with hh
  have hd : ∀ v ∈ Icc (0 : ℝ) 1, HasDerivAt h (g' v - g' 0) v := by
    intro v hv
    have h3 : HasDerivAt h (g' v - 1 * g' 0) v :=
      ((h1 v hv).sub_const (g 0)).fun_sub ((hasDerivAt_id' v).mul_const (g' 0))
    simpa using h3
  have hb : ∀ v ∈ Icc (0 : ℝ) 1, ‖h v‖ ≤ M := by
    intro v hv
    have h3 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Icc (0 : ℝ) 1) (f := h)
      (f' := fun v => g' v - g' 0) (C := M) (fun y hy => (hd y hy).hasDerivWithinAt)
      (fun y hy => hg1 y hy) (convex_Icc _ _) mem0 hv
    have h0 : h 0 = 0 := by simp [hh]
    rw [h0, sub_zero, Real.norm_eq_abs (v - 0), sub_zero, abs_of_nonneg hv.1] at h3
    calc _ ≤ M * v := h3
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left hv.2 hM0
      _ = M := mul_one _
  have hgi : IntervalIntegrable g volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact fun v hv => (h1 v hv).continuousAt.continuousWithinAt
  have hli : IntervalIntegrable (fun v : ℝ => v * g' 0) volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hint : ∫ v in (0 : ℝ)..1, h v = (∫ v in (0 : ℝ)..1, g v) - g 0 - g' 0 / 2 := by
    simp only [hh]
    rw [intervalIntegral.integral_sub (hgi.sub intervalIntegrable_const) hli,
      intervalIntegral.integral_sub hgi intervalIntegrable_const, intervalIntegral.integral_mul_const,
      integral_id, intervalIntegral.integral_const]
    simp
    ring
  have hbi : ‖∫ v in (0 : ℝ)..1, h v‖ ≤ M := by
    have h3 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (f := h) (C := M)
      (fun v hv => by
        rw [uIoc_of_le zero_le_one] at hv
        exact hb v ⟨hv.1.le, hv.2⟩)
    simpa using h3
  have key : g 1 - 2 * (∫ v in (0 : ℝ)..1, g v) + g 0 = h 1 - 2 * ∫ v in (0 : ℝ)..1, h v := by
    rw [hint]
    simp only [hh]
    ring
  rw [key]
  have a1 := hb 1 mem1
  rw [Real.norm_eq_abs] at a1 hbi
  have a2 := abs_le.1 a1
  have a3 := abs_le.1 hbi
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [a2.1, a2.2, a3.1, a3.2]
theorem abs_weighted_mean_le {p p' : ℝ → ℝ} {M : ℝ} (h1 : ∀ v ∈ Icc (0 : ℝ) 1, HasDerivAt p (p' v) v)
    (hM : ∀ v ∈ Icc (0 : ℝ) 1, |p' v| ≤ M) : |p 1 - 2 * ∫ v in (0 : ℝ)..1, v * p v| ≤ 2 * M := by
  have mem1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 1 mem1)
  have hb : ∀ v ∈ Icc (0 : ℝ) 1, ‖p 1 - p v‖ ≤ M := by
    intro v hv
    have h3 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Icc (0 : ℝ) 1) (f := p) (f' := p')
      (C := M) (fun y hy => (h1 y hy).hasDerivWithinAt) (fun y hy => hM y hy) (convex_Icc _ _) hv mem1
    have h4 : ‖(1 : ℝ) - v‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hv.2])]
      linarith [hv.1]
    calc _ ≤ M * ‖(1 : ℝ) - v‖ := h3
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left h4 hM0
      _ = M := mul_one _
  have hci : ContinuousOn p (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact fun v hv => (h1 v hv).continuousAt.continuousWithinAt
  have hwi : IntervalIntegrable (fun v : ℝ => v * p v) volume 0 1 :=
    (continuousOn_id.mul hci).intervalIntegrable
  have hli : IntervalIntegrable (fun v : ℝ => v * p 1) volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hint : ∫ v in (0 : ℝ)..1, v * (p 1 - p v) = p 1 / 2 - ∫ v in (0 : ℝ)..1, v * p v := by
    have e : (fun v : ℝ => v * (p 1 - p v)) = fun v => v * p 1 - v * p v := by
      funext v; ring
    rw [e, intervalIntegral.integral_sub hli hwi, intervalIntegral.integral_mul_const, integral_id]
    simp
    ring
  have hbi : ‖∫ v in (0 : ℝ)..1, v * (p 1 - p v)‖ ≤ M := by
    have h3 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun v => v * (p 1 - p v)) (C := M) (fun v hv => by
        rw [uIoc_of_le zero_le_one] at hv
        have h4 := hb v ⟨hv.1.le, hv.2⟩
        rw [norm_mul, Real.norm_eq_abs, abs_of_pos hv.1]
        calc v * ‖p 1 - p v‖ ≤ 1 * ‖p 1 - p v‖ := mul_le_mul_of_nonneg_right hv.2 (norm_nonneg _)
          _ ≤ M := by simpa using h4)
    simpa using h3
  have key : p 1 - 2 * (∫ v in (0 : ℝ)..1, v * p v) = 2 * ∫ v in (0 : ℝ)..1, v * (p 1 - p v) := by
    rw [hint]
    ring
  rw [key, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [Real.norm_eq_abs] at hbi
  linarith
end Line
section Ray
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem iteratedFDeriv_two_eval_fderiv {A : E → ℝ} {y : E} (h : ContDiffAt ℝ (2 : ℕ) A y) (b c : E) :
    iteratedFDeriv ℝ 2 A y ![b, c] = fderiv ℝ (fun y' => fderiv ℝ A y' c) y b := by
  have h1 : iteratedFDeriv ℝ 2 A y ![b, c] = fderiv ℝ (fun y' => iteratedFDeriv ℝ 1 A y' ![c]) y b :=
    iteratedFDeriv_succ_cons_eval h b ![c]
  have e : (fun y' => iteratedFDeriv ℝ 1 A y' ![c]) = fun y' => fderiv ℝ A y' c := by
    funext y'
    simp [iteratedFDeriv_one_apply]
  rw [h1, e]
theorem iteratedFDeriv_two_eval_fderiv_fderiv {A : E → ℝ} {y : E} (h : ContDiffAt ℝ (2 : ℕ) A y) (b c : E) :
    iteratedFDeriv ℝ 2 A y ![b, c] = fderiv ℝ (fderiv ℝ A) y b c := by
  rw [iteratedFDeriv_two_eval_fderiv h]
  have hd : DifferentiableAt ℝ (fderiv ℝ A) y :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (fderiv_clm_eval hd b c).symm
theorem iteratedFDeriv_three_eval_fderiv {A : E → ℝ} {y : E} (h : ContDiffAt ℝ (3 : ℕ) A y) (a b c : E) :
    iteratedFDeriv ℝ 3 A y ![a, b, c] = fderiv ℝ (fun y' => iteratedFDeriv ℝ 2 A y' ![b, c]) y a :=
  iteratedFDeriv_succ_cons_eval h a ![b, c]
theorem hasDerivAt_ray {f : E → ℝ} {f' : E →L[ℝ] ℝ} {η : E} {v : ℝ} (h : HasFDerivAt f f' (v • η)) :
    HasDerivAt (fun v : ℝ => f (v • η)) (f' η) v := by
  have h1 : HasDerivAt (fun v : ℝ => v • η) η v := by simpa using (hasDerivAt_id v).smul_const η
  exact h.comp_hasDerivAt v h1
theorem abs_ray_slope_le {A : E → ℝ} {η e : E} {M : ℝ} (hA : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (3 : ℕ) A (v • η))
    (hM : ∀ v ∈ Icc (0 : ℝ) 1, |iteratedFDeriv ℝ 3 A (v • η) ![η, η, e]| ≤ M) :
    |fderiv ℝ A η e - 2 * (∫ v in (0 : ℝ)..1, fderiv ℝ A (v • η) e) + fderiv ℝ A 0 e| ≤ 3 * M := by
  have h := abs_trapezoid_le (g := fun v => fderiv ℝ A (v • η) e) (g' := fun v => iteratedFDeriv ℝ 2 A (v • η) ![η, e])
    (g'' := fun v => iteratedFDeriv ℝ 3 A (v • η) ![η, η, e]) ?_ ?_ hM
  · simpa using h
  · intro v hv
    have h3 := hA v hv
    have hs : ContDiffAt ℝ (1 : ℕ) (fun y => fderiv ℝ A y e) (v • η) :=
      contDiffAt_fderiv_eval (h3.of_le (by norm_num)) e
    have h4 := hasDerivAt_ray (hs.differentiableAt (by norm_num)).hasFDerivAt
    rw [← iteratedFDeriv_two_eval_fderiv (h3.of_le (by norm_num))] at h4
    exact h4
  · intro v hv
    have h3 := hA v hv
    have hs : ContDiffAt ℝ (1 : ℕ) (fun y => iteratedFDeriv ℝ 2 A y ![η, e]) (v • η) :=
      contDiffAt_iteratedFDeriv_eval h3 (by norm_num) _
    have h4 := hasDerivAt_ray (hs.differentiableAt (by norm_num)).hasFDerivAt
    rw [← iteratedFDeriv_three_eval_fderiv h3] at h4
    exact h4
theorem abs_ray_weighted_le {A : E → ℝ} {η u e : E} {M : ℝ} (hA : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (3 : ℕ) A (v • η))
    (hM : ∀ v ∈ Icc (0 : ℝ) 1, |iteratedFDeriv ℝ 3 A (v • η) ![η, u, e]| ≤ M) :
    |iteratedFDeriv ℝ 2 A η ![u, e] - 2 * ∫ v in (0 : ℝ)..1, v * iteratedFDeriv ℝ 2 A (v • η) ![u, e]| ≤ 2 * M := by
  have h := abs_weighted_mean_le (p := fun v => iteratedFDeriv ℝ 2 A (v • η) ![u, e])
    (p' := fun v => iteratedFDeriv ℝ 3 A (v • η) ![η, u, e]) ?_ hM
  · simpa using h
  · intro v hv
    have h3 := hA v hv
    have hs : ContDiffAt ℝ (1 : ℕ) (fun y => iteratedFDeriv ℝ 2 A y ![u, e]) (v • η) :=
      contDiffAt_iteratedFDeriv_eval h3 (by norm_num) _
    have h4 := hasDerivAt_ray (hs.differentiableAt (by norm_num)).hasFDerivAt
    rw [← iteratedFDeriv_three_eval_fderiv h3] at h4
    exact h4
variable {β : Type}
def remainder (S : E × ℝ → E) (B : Finset β) (P : β → E →L[ℝ] E) (f : E → ℝ) (z : E) : ℝ :=
  ∑ b ∈ B, (fderiv ℝ f z (P b z) - 2 * ∫ v in (0 : ℝ)..1, fderiv ℝ f (S (z, v)) (P b z))
def meanFDeriv (S : E × ℝ → E) (f : E → ℝ) (z : E) : E →L[ℝ] ℝ := ∫ v in (0 : ℝ)..1, fderiv ℝ f (S (z, v))
def dilate (p : E × ℝ) : E := p.2 • p.1
theorem contDiff_dilate {n : WithTop ℕ∞} : ContDiff ℝ n (dilate (E := E)) := by
  unfold dilate
  exact contDiff_snd.smul contDiff_fst
theorem eventually_contDiffAt_comp_tube {m : ℕ} {S : E × ℝ → E} (hS : Continuous S) {f : E → ℝ} {z : E}
    (hv : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ m f (S (z, v))) :
    ∀ᶠ y in 𝓝 z, ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ m f (S (y, v)) := by
  have hW : IsOpen {q : E | ContDiffAt ℝ m f q} := isOpen_iff_mem_nhds.2 fun p hp =>
    (show ContDiffAt ℝ m f p from hp).eventually (coe_nat_ne_infty _)
  have hsub : ({z} : Set E) ×ˢ Icc (0 : ℝ) 1 ⊆ S ⁻¹' {q : E | ContDiffAt ℝ m f q} := by
    rintro ⟨y, v⟩ ⟨hy, hv'⟩
    obtain rfl : y = z := hy
    exact hv v hv'
  obtain ⟨u, w, hu, -, hzu, hIw, huw⟩ := generalized_tube_lemma isCompact_singleton isCompact_Icc
    (hW.preimage hS) hsub
  filter_upwards [hu.mem_nhds (hzu rfl)] with y hy v hv'
  exact huw (show (y, v) ∈ u ×ˢ w from ⟨hy, hIw hv'⟩)
theorem intervalIntegrable_fderiv_comp {S : E × ℝ → E} (hS : Continuous S) {f : E → ℝ} {z : E}
    (hv : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (1 : ℕ) f (S (z, v))) :
    IntervalIntegrable (fun v => fderiv ℝ f (S (z, v))) volume 0 1 := by
  refine intervalIntegrable_unit_slice (Φ := fun p => fderiv ℝ f (S p)) fun v hv' => ?_
  have h1 : ContinuousAt (fderiv ℝ f) (S (z, v)) :=
    ((hv v hv').fderiv_right (m := 0) (by norm_num)).continuousAt
  exact ContinuousAt.comp (f := S) h1 hS.continuousAt
theorem remainder_eq_sum_mean {S : E × ℝ → E} (hS : Continuous S) (B : Finset β) (P : β → E →L[ℝ] E) {f : E → ℝ} {z : E}
    (hv : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (1 : ℕ) f (S (z, v))) :
    remainder S B P f z = ∑ b ∈ B, (fderiv ℝ f z - (2 : ℝ) • meanFDeriv S f z) (P b z) := by
  unfold remainder
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 := ContinuousLinearMap.intervalIntegral_apply (intervalIntegrable_fderiv_comp hS hv) (P b z)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, meanFDeriv]
  rw [h1]
theorem contDiffAt_remainder {S : E × ℝ → E} (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S) (B : Finset β)
    (P : β → E →L[ℝ] E) {f : E → ℝ} {z : E} (n : ℕ) (hz : ContDiffAt ℝ (n + 2 : ℕ) f z)
    (hv : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 2 : ℕ) f (S (z, v))) :
    ContDiffAt ℝ n (remainder S B P f) z := by
  have hSc : Continuous S := hS.continuous
  have hΦ : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1 : ℕ) (fun p => fderiv ℝ f (S p)) (z, v) := fun v hv' => by
    have h1 : ContDiffAt ℝ (n + 1 : ℕ) (fderiv ℝ f) (S (z, v)) :=
      (hv v hv').fderiv_right (by norm_cast)
    have h2 : ContDiffAt ℝ (n + 1 : ℕ) S (z, v) := (hS.of_le (by exact_mod_cast le_top)).contDiffAt
    exact ContDiffAt.comp (z, v) h1 h2
  have hm : ContDiffAt ℝ n (meanFDeriv S f) z :=
    contDiffAt_intervalIntegral_unit n _ (fun p => fderiv ℝ f (S p)) z hΦ
  have hfd : ContDiffAt ℝ n (fderiv ℝ f) z := hz.fderiv_right (by norm_cast; omega)
  have hM : ContDiffAt ℝ n (fun y => fderiv ℝ f y - (2 : ℝ) • meanFDeriv S f y) z :=
    hfd.sub (hm.const_smul (2 : ℝ))
  have hsum : ContDiffAt ℝ n (fun y => ∑ b ∈ B, (fderiv ℝ f y - (2 : ℝ) • meanFDeriv S f y) (P b y)) z :=
    ContDiffAt.sum fun b _ => hM.clm_apply (P b).contDiff.contDiffAt
  refine hsum.congr_of_eventuallyEq ?_
  have ht := eventually_contDiffAt_comp_tube hSc (m := 1) (fun v hv' => (hv v hv').of_le (by norm_cast; omega))
  filter_upwards [ht] with y hy
  exact remainder_eq_sum_mean hSc B P hy
theorem partialFst_dilate {A : E → ℝ} {η : E} {v : ℝ} (h : ContDiffAt ℝ (2 : ℕ) A (v • η)) :
    partialFst (fun p => fderiv ℝ A (dilate p)) (η, v) =
      (fderiv ℝ (fderiv ℝ A) (v • η)).comp (v • ContinuousLinearMap.id ℝ E) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ A) (v • η) :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : ContDiffAt ℝ (2 : ℕ) (dilate (E := E)) (η, v) := contDiff_dilate.contDiffAt
  have hΦ : DifferentiableAt ℝ (fun p : E × ℝ => fderiv ℝ A (dilate p)) (η, v) :=
    DifferentiableAt.comp (η, v) (g := fderiv ℝ A) (f := dilate) hd (h2.differentiableAt (by norm_num))
  have h3 : HasFDerivAt (fun y => fderiv ℝ A (dilate (y, v)))
      (partialFst (fun p => fderiv ℝ A (dilate p)) (η, v)) η :=
    HasFDerivAt.comp η (g := fun p : E × ℝ => fderiv ℝ A (dilate p)) (f := fun y : E => (y, v))
      hΦ.hasFDerivAt (hasFDerivAt_prodMk_left η v)
  have h4 : HasFDerivAt (fun y : E => v • y) (v • ContinuousLinearMap.id ℝ E) η :=
    (ContinuousLinearMap.id ℝ E).hasFDerivAt.const_smul v
  have h5 : HasFDerivAt (fun y => fderiv ℝ A (dilate (y, v)))
      ((fderiv ℝ (fderiv ℝ A) (v • η)).comp (v • ContinuousLinearMap.id ℝ E)) η :=
    HasFDerivAt.comp η (g := fderiv ℝ A) (f := fun y : E => v • y) hd.hasFDerivAt h4
  exact h3.unique h5
theorem hasFDerivAt_remainder_dilate (B : Finset β) (P : β → E →L[ℝ] E) {A : E → ℝ} {η : E}
    (hA : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (3 : ℕ) A (v • η)) :
    ∃ L : E →L[ℝ] ℝ, HasFDerivAt (remainder dilate B P A) L η ∧ ∀ u, L u = ∑ b ∈ B,
      ((fderiv ℝ A η (P b u) - 2 * ∫ v in (0 : ℝ)..1, fderiv ℝ A (v • η) (P b u)) +
        (iteratedFDeriv ℝ 2 A η ![u, P b η] -
          2 * ∫ v in (0 : ℝ)..1, v * iteratedFDeriv ℝ 2 A (v • η) ![u, P b η])) := by
  have hSc : Continuous (dilate (E := E)) := (contDiff_dilate (n := 0)).continuous
  have h1η : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hAη : ContDiffAt ℝ (3 : ℕ) A η := by simpa using hA 1 h1η
  set Φ : E × ℝ → E →L[ℝ] ℝ := fun p => fderiv ℝ A (dilate p) with hΦdef
  have hΦ : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (1 : ℕ) Φ (η, v) := fun v hv => by
    have h1 : ContDiffAt ℝ (1 : ℕ) (fderiv ℝ A) (v • η) := (hA v hv).fderiv_right (by norm_num)
    have h2 : ContDiffAt ℝ (1 : ℕ) (dilate (E := E)) (η, v) := contDiff_dilate.contDiffAt
    exact ContDiffAt.comp (η, v) (g := fderiv ℝ A) (f := dilate) h1 h2
  set D : E →L[ℝ] E →L[ℝ] ℝ := ∫ v in (0 : ℝ)..1, partialFst Φ (η, v) with hD
  have hmean : HasFDerivAt (meanFDeriv dilate A) D η :=
    (eventually_hasFDerivAt_intervalIntegral_unit (Φ := Φ) (z := η) hΦ).self_of_nhds
  have hfd : HasFDerivAt (fderiv ℝ A) (fderiv ℝ (fderiv ℝ A) η) η :=
    ((hAη.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hM : HasFDerivAt (fun y => fderiv ℝ A y - (2 : ℝ) • meanFDeriv dilate A y)
      (fderiv ℝ (fderiv ℝ A) η - (2 : ℝ) • D) η := hfd.sub (hmean.const_smul (2 : ℝ))
  set M₀ : E →L[ℝ] ℝ := fderiv ℝ A η - (2 : ℝ) • meanFDeriv dilate A η with hM₀
  set M₁ : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ A) η - (2 : ℝ) • D with hM₁
  have hterm : ∀ b ∈ B, HasFDerivAt (fun y => (fderiv ℝ A y - (2 : ℝ) • meanFDeriv dilate A y) (P b y))
      (M₀.comp (P b) + M₁.flip (P b η)) η := fun b _ => hM.clm_apply (P b).hasFDerivAt
  have hsum := HasFDerivAt.fun_sum hterm
  have hev : remainder dilate B P A =ᶠ[𝓝 η]
      fun y => ∑ b ∈ B, (fderiv ℝ A y - (2 : ℝ) • meanFDeriv dilate A y) (P b y) := by
    have ht := eventually_contDiffAt_comp_tube hSc (f := A) (z := η) (m := 1) (fun v hv => (hA v hv).of_le (by norm_num))
    filter_upwards [ht] with y hy
    exact remainder_eq_sum_mean hSc B P hy
  refine ⟨_, hsum.congr_of_eventuallyEq hev, fun u => ?_⟩
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hI1 := intervalIntegrable_fderiv_comp hSc (f := A) (z := η) fun v hv => (hA v hv).of_le (by norm_num)
  have e1 : M₀ (P b u) = fderiv ℝ A η (P b u) - 2 * ∫ v in (0 : ℝ)..1, fderiv ℝ A (v • η) (P b u) := by
    have h1 := ContinuousLinearMap.intervalIntegral_apply hI1 (P b u)
    simp only [hM₀, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, meanFDeriv]
    rw [h1]
    rfl
  have hφ : ∀ v ∈ Icc (0 : ℝ) 1, partialFst Φ (η, v) =
      (fderiv ℝ (fderiv ℝ A) (v • η)).comp (v • ContinuousLinearMap.id ℝ E) := fun v hv =>
    partialFst_dilate ((hA v hv).of_le (by norm_num))
  have hcφ : ∀ v ∈ Icc (0 : ℝ) 1, ContinuousAt (partialFst Φ) (η, v) := fun v hv =>
    (contDiffAt_partialFst (n := 0) (by simpa using hΦ v hv)).continuousAt
  have hI2 : IntervalIntegrable (fun v => partialFst Φ (η, v)) volume 0 1 := intervalIntegrable_unit_slice hcφ
  have hI3 : IntervalIntegrable (fun v => partialFst Φ (η, v) u) volume 0 1 := by
    refine intervalIntegrable_unit_slice (Φ := fun p => partialFst Φ p u) fun v hv => ?_
    exact ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) u).continuous.continuousAt).comp (hcφ v hv)
  have e2 : D u (P b η) = ∫ v in (0 : ℝ)..1, v * iteratedFDeriv ℝ 2 A (v • η) ![u, P b η] := by
    have h1 := ContinuousLinearMap.intervalIntegral_apply hI2 u
    have h2 := ContinuousLinearMap.intervalIntegral_apply hI3 (P b η)
    rw [hD, h1, h2]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le zero_le_one] at hv
    simp only [hφ v hv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
    rw [iteratedFDeriv_two_eval_fderiv_fderiv ((hA v hv).of_le (by norm_num))]
  have e3 : M₁ u (P b η) = iteratedFDeriv ℝ 2 A η ![u, P b η] -
      2 * ∫ v in (0 : ℝ)..1, v * iteratedFDeriv ℝ 2 A (v • η) ![u, P b η] := by
    simp only [hM₁, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [e2, iteratedFDeriv_two_eval_fderiv_fderiv (hAη.of_le (by norm_num))]
  rw [e1, e3]
theorem abs_remainder_dilate_le (B : Finset β) (P : β → E →L[ℝ] E) {A : E → ℝ} {η : E} {M : β → ℝ}
    (hA : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (3 : ℕ) A (v • η))
    (hM : ∀ b ∈ B, ∀ v ∈ Icc (0 : ℝ) 1, |iteratedFDeriv ℝ 3 A (v • η) ![η, η, P b η]| ≤ M b) :
    |remainder dilate B P A η| ≤ ∑ b ∈ B, (|fderiv ℝ A 0 (P b η)| + 3 * M b) := by
  unfold remainder
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b hb => ?_)
  have h1 := abs_ray_slope_le hA (hM b hb)
  have h2 := abs_le.1 h1
  have h3 := neg_abs_le (fderiv ℝ A 0 (P b η))
  have h4 := le_abs_self (fderiv ℝ A 0 (P b η))
  simp only [dilate]
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [h2.1, h2.2]
theorem abs_fderiv_remainder_dilate_le (B : Finset β) (P : β → E →L[ℝ] E) {A : E → ℝ} {η u : E} {M₁ M₂ : β → ℝ}
    (hA : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (3 : ℕ) A (v • η))
    (h1 : ∀ b ∈ B, ∀ v ∈ Icc (0 : ℝ) 1, |iteratedFDeriv ℝ 3 A (v • η) ![η, η, P b u]| ≤ M₁ b)
    (h2 : ∀ b ∈ B, ∀ v ∈ Icc (0 : ℝ) 1, |iteratedFDeriv ℝ 3 A (v • η) ![η, u, P b η]| ≤ M₂ b) :
    |fderiv ℝ (remainder dilate B P A) η u| ≤ ∑ b ∈ B, (|fderiv ℝ A 0 (P b u)| + 3 * M₁ b + 2 * M₂ b) := by
  obtain ⟨L, hL, hLu⟩ := hasFDerivAt_remainder_dilate B P hA
  rw [hL.fderiv, hLu]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b hb => ?_)
  have a1 := abs_le.1 (abs_ray_slope_le hA (h1 b hb))
  have a2 := abs_le.1 (abs_ray_weighted_le hA (h2 b hb))
  have h3 := neg_abs_le (fderiv ℝ A 0 (P b u))
  have h4 := le_abs_self (fderiv ℝ A 0 (P b u))
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [a1.1, a1.2, a2.1, a2.2]
end Ray
section Jet
variable {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  {β : Type}
def dilateFst (p : (E₁ × E₂) × ℝ) : E₁ × E₂ := (p.2 • p.1.1, p.1.2)
theorem contDiff_dilateFst {n : WithTop ℕ∞} : ContDiff ℝ n (dilateFst (E₁ := E₁) (E₂ := E₂)) := by
  unfold dilateFst
  exact (contDiff_snd.smul (contDiff_fst.comp contDiff_fst)).prodMk (contDiff_snd.comp contDiff_fst)
def liftFst (P : E₁ →L[ℝ] E₁) : (E₁ × E₂) →L[ℝ] E₁ × E₂ :=
  (ContinuousLinearMap.inl ℝ E₁ E₂).comp (P.comp (ContinuousLinearMap.fst ℝ E₁ E₂))
theorem liftFst_apply (P : E₁ →L[ℝ] E₁) (z : E₁ × E₂) : liftFst P z = (P z.1, 0) := rfl
theorem iteratedFDeriv_finsetSum_eval {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {J : Type} (S : Finset J) (k : ℕ)
    (g : J → E → ℝ) (x : E) (hs : ∀ j ∈ S, ContDiffAt ℝ k (g j) x) (v : Fin k → E) :
    iteratedFDeriv ℝ k (fun τ => ∑ j ∈ S, g j τ) x v = ∑ j ∈ S, iteratedFDeriv ℝ k (g j) x v := by apply _root_.YangMills.Construction.ResponseInTheExpansion.iteratedFDeriv_finsetSum_apply <;> assumption
theorem iteratedFDeriv_const_mul_eval {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {g : E → ℝ} {x : E}
    (h : ContDiffAt ℝ k g x) (a : ℝ) (v : Fin k → E) :
    iteratedFDeriv ℝ k (fun τ => a * g τ) x v = a * iteratedFDeriv ℝ k g x v := by
  have h1 := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := k) (a := a) (f := g) (x := x) h
  have e2 : (fun τ => a * g τ) = a • g := by
    funext τ; simp
  rw [e2, h1]
  simp
theorem iteratedFDeriv_fun_sub_eval {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {g₁ g₂ : E → ℝ} {x : E}
    (h₁ : ContDiffAt ℝ k g₁ x) (h₂ : ContDiffAt ℝ k g₂ x) (v : Fin k → E) :
    iteratedFDeriv ℝ k (fun τ => g₁ τ - g₂ τ) x v = iteratedFDeriv ℝ k g₁ x v - iteratedFDeriv ℝ k g₂ x v := by
  have h3 := iteratedFDeriv_const_mul_eval h₂ (-1) v
  have h4 : ContDiffAt ℝ k (fun τ => -1 * g₂ τ) x := contDiffAt_const.mul h₂
  have h5 := iteratedFDeriv_add_apply (i := k) h₁ h4
  have e : (fun τ => g₁ τ - g₂ τ) = g₁ + fun τ => -1 * g₂ τ := by
    funext τ
    simp only [Pi.add_apply]
    ring
  rw [e, h5]
  simp only [ContinuousMultilinearMap.add_apply]
  rw [h3]
  ring
theorem iteratedFDeriv_remainder_dilateFst {k : ℕ} (B : Finset β) (P : β → E₁ →L[ℝ] E₁) {f : E₁ × E₂ → ℝ} {η : E₁} (w : Fin k → E₂)
    [CompleteSpace E₂] (hf : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (k + 3 : ℕ) f (v • η, (0 : E₂))) :
    iteratedFDeriv ℝ k (fun τ => remainder dilateFst B (fun b => liftFst (P b)) f (η, τ)) 0 w =
      remainder dilate B P (secondJet f 0 w) η := by
  have h1η : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hfη : ContDiffAt ℝ (k + 3 : ℕ) f (η, (0 : E₂)) := by simpa using hf 1 h1η
  unfold remainder
  simp only [liftFst_apply, dilateFst, smul_eq_mul]
  have hpart : ∀ b ∈ B, ∀ e : E₁, ContDiffAt ℝ k (fun τ => fderiv ℝ f (η, τ) (e, 0)) (0 : E₂) ∧
      ContDiffAt ℝ k (fun τ => ∫ v in (0 : ℝ)..1, fderiv ℝ f (v • η, τ) (e, 0)) (0 : E₂) ∧
      iteratedFDeriv ℝ k (fun τ => ∫ v in (0 : ℝ)..1, fderiv ℝ f (v • η, τ) (e, 0)) 0 w =
        ∫ v in (0 : ℝ)..1, fderiv ℝ (secondJet f 0 w) (v • η) e := by
    intro b _ e
    set g : E₁ × E₂ → ℝ := fun z => fderiv ℝ f z (e, 0) with hg
    have hgs : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (k + 2 : ℕ) g (v • η, (0 : E₂)) := fun v hv =>
      contDiffAt_fderiv_eval ((hf v hv).of_le (by norm_cast)) _
    have hline : ∀ v : ℝ, ContDiffAt ℝ (k + 1 : ℕ) (fun p : E₂ × ℝ => ((p.2 • η, p.1) : E₁ × E₂)) (0, v) := fun v => by
      have : ContDiff ℝ (k + 1 : ℕ) (fun p : E₂ × ℝ => ((p.2 • η, p.1) : E₁ × E₂)) :=
        (contDiff_snd.smul contDiff_const).prodMk contDiff_fst
      exact this.contDiffAt
    have hΦ : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (k + 1 : ℕ) (fun p : E₂ × ℝ => g (p.2 • η, p.1)) (0, v) := fun v hv =>
      ContDiffAt.comp (0, v) (g := g) (f := fun p : E₂ × ℝ => ((p.2 • η, p.1) : E₁ × E₂))
        ((hgs v hv).of_le (by norm_cast; omega)) (hline v)
    refine ⟨?_, contDiffAt_intervalIntegral_unit k ℝ _ 0 hΦ, ?_⟩
    · have h2 : ContDiffAt ℝ k (fun τ : E₂ => ((η, τ) : E₁ × E₂)) (0 : E₂) := by fun_prop
      exact ContDiffAt.comp (0 : E₂) (g := g) (f := fun τ : E₂ => ((η, τ) : E₁ × E₂))
        ((contDiffAt_fderiv_eval (hfη.of_le (by norm_cast; omega)) _)) h2
    · rw [iteratedFDeriv_intervalIntegral_eval k _ 0 hΦ w]
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [uIcc_of_le zero_le_one] at hv
      have h3 : ContDiffAt ℝ k (fun p : E₂ × ℝ => g (p.2 • η, p.1)) (0, v) := (hΦ v hv).of_le (by norm_cast; omega)
      have h4 := iteratedFDeriv_slice_eval h3 w
      simp only at h4 ⊢
      rw [h4]
      exact secondJet_fderiv_eval ((hf v hv).of_le (by norm_cast; omega)) w e
  rw [iteratedFDeriv_finsetSum_eval B k _ 0 (fun b hb => ?_) w]
  · refine Finset.sum_congr rfl fun b hb => ?_
    obtain ⟨p1, p2, p3⟩ := hpart b hb (P b η)
    rw [iteratedFDeriv_fun_sub_eval p1 (contDiffAt_const.mul p2), iteratedFDeriv_const_mul_eval p2, p3]
    congr 1
    exact secondJet_fderiv_eval (hfη.of_le (by norm_cast; omega)) w (P b η)
  · obtain ⟨p1, p2, -⟩ := hpart b hb (P b η)
    exact p1.sub (contDiffAt_const.mul p2)
end Jet
end YangMills.Construction.Dilation
end

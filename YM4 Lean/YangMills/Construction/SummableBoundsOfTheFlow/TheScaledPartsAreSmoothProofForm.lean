import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenAtATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.BondsAtACell
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongParametersOfAFamilyProofForm
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheGapAboveTheFramesProof
import YangMills.Construction.SummableBoundsOfTheFlow.LeastChartEnergyIsSmoothProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceGoesUpALevelProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledPartsAreSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.TheTailOfTheGapIsSmoothProof
import YangMills.Construction.SummableBoundsOfTheFlow.ValuesAboveTheLeastField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RescaledParts
section
open Set Filter Topology
section
variable {E G H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
theorem iteratedFDeriv_succ_cons_eq_fderiv {n : ℕ} {f : E → H} {x : E} (hf : ContDiffAt ℝ (n + 1 : ℕ) f x)
    (a : E) (u : Fin n → E) :
    iteratedFDeriv ℝ (n + 1) f x (Fin.cons a u) =
      fderiv ℝ (fun y => iteratedFDeriv ℝ n f y u) x a := by apply _root_.YangMills.Construction.ParameterListDerivatives.iteratedFDeriv_succ_cons_eq_fderiv <;> assumption
theorem fderiv_clm_apply_eq {Ψ : E → G →L[ℝ] H} {x : E} (h : DifferentiableAt ℝ Ψ x) (a : E) (b : G) :
    (fderiv ℝ Ψ x a) b = fderiv ℝ (fun y => Ψ y b) x a := by
  have h1 := ((ContinuousLinearMap.apply ℝ H b).hasFDerivAt.comp x h.hasFDerivAt).fderiv
  have h2 : (fun y => Ψ y b) = (ContinuousLinearMap.apply ℝ H b) ∘ Ψ := rfl
  rw [h2, h1]
  rfl
theorem contDiffAt_iteratedFDeriv_apply {n m i : ℕ} {f : E → H} {x : E} (hf : ContDiffAt ℝ n f x)
    (hmn : m + i ≤ n) (u : Fin i → E) :
    ContDiffAt ℝ m (fun y => iteratedFDeriv ℝ i f y u) x := by apply _root_.YangMills.Construction.ParameterListDerivatives.contDiffAt_iteratedFDeriv_eval <;> assumption
theorem iteratedFDeriv_cons_cons_eq {n : ℕ} {f : E → H} {x : E} (hf : ContDiffAt ℝ (n + 1 + 1 : ℕ) f x)
    (a b : E) (w : Fin n → E) :
    iteratedFDeriv ℝ (n + 1 + 1) f x (Fin.cons a (Fin.cons b w)) =
      fderiv ℝ (fderiv ℝ fun y => iteratedFDeriv ℝ n f y w) x a b := by
  set τ : E → H := fun y => iteratedFDeriv ℝ n f y w with hτ
  have hτ2 : ContDiffAt ℝ 2 τ x := by exact_mod_cast contDiffAt_iteratedFDeriv_apply (m := 2) hf (by omega) w
  rw [iteratedFDeriv_succ_cons_eq_fderiv hf a]
  have he : (fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.cons b w)) =ᶠ[𝓝 x] fun y => fderiv ℝ τ y b := by
    have : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ (n + 1 : ℕ) f y :=
      (hf.of_le (by norm_cast; omega)).eventually (by simp)
    filter_upwards [this] with y hy
    exact iteratedFDeriv_succ_cons_eq_fderiv hy b w
  rw [he.fderiv_eq]
  have hd : DifferentiableAt ℝ (fderiv ℝ τ) x :=
    (hτ2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (fderiv_clm_apply_eq hd a b).symm
theorem iteratedFDeriv_swap_adjacent : ∀ (n : ℕ) (f : E → H) (x : E), ContDiffAt ℝ (n + 1 : ℕ) f x →
    ∀ (v : Fin (n + 1) → E) (i : Fin n),
      iteratedFDeriv ℝ (n + 1) f x (v ∘ Equiv.swap i.castSucc i.succ) = iteratedFDeriv ℝ (n + 1) f x v := by
  intro n
  induction n with
  | zero => intro f x _ v i; exact i.elim0
  | succ n ih =>
    intro f x hf v i
    refine Fin.cases ?_ (fun j => ?_) i
    · set w : Fin n → E := Fin.tail (Fin.tail v) with hw
      have hv : v = Fin.cons (v 0) (Fin.cons (v 1) w) := by
        funext k
        refine Fin.cases ?_ (fun k => ?_) k
        · simp
        · refine Fin.cases ?_ (fun k => ?_) k
          · simp
          · simp [hw, Fin.tail_def]
      have hs : v ∘ Equiv.swap (Fin.castSucc (0 : Fin (n + 1))) (Fin.succ (0 : Fin (n + 1))) =
          Fin.cons (v 1) (Fin.cons (v 0) w) := by
        funext k
        refine Fin.cases ?_ (fun k => ?_) k
        · simp
        · refine Fin.cases ?_ (fun k => ?_) k
          · simp
          · have h0 : (k.succ.succ : Fin (n + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
            have h1 : (k.succ.succ : Fin (n + 1 + 1)) ≠ 1 := by
              intro h
              have := congrArg Fin.val h
              simp at this
            simp [Equiv.swap_apply_of_ne_of_ne, h0, h1, hw, Fin.tail_def]
      rw [hs]
      conv_rhs => rw [hv]
      rw [iteratedFDeriv_cons_cons_eq hf, iteratedFDeriv_cons_cons_eq hf]
      have hτ2 : ContDiffAt ℝ 2 (fun y => iteratedFDeriv ℝ n f y w) x := by
        exact_mod_cast contDiffAt_iteratedFDeriv_apply (m := 2) hf (by omega) w
      exact hτ2.isSymmSndFDerivAt (by simp) _ _
    · have hc : v ∘ Equiv.swap (j.succ.castSucc) (j.succ.succ) =
          Fin.cons (v 0) ((Fin.tail v) ∘ Equiv.swap j.castSucc j.succ) := by
        have e : j.succ.castSucc = j.castSucc.succ := Fin.ext (by simp)
        rw [e]
        funext k
        refine Fin.cases ?_ (fun k => ?_) k
        · simp only [Function.comp, Fin.cons_zero]
          rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm]
        · simp only [Function.comp, Fin.cons_succ, Fin.tail_def]
          rw [← Function.Injective.map_swap (Fin.succ_injective _)]
      rw [hc, iteratedFDeriv_succ_cons_eq_fderiv hf]
      have he : (fun y => iteratedFDeriv ℝ (n + 1) f y ((Fin.tail v) ∘ Equiv.swap j.castSucc j.succ)) =ᶠ[𝓝 x]
          fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.tail v) := by
        have : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ (n + 1 : ℕ) f y :=
          (hf.of_le (by norm_cast; omega)).eventually (by simp)
        filter_upwards [this] with y hy
        exact ih f y hy _ j
      rw [he.fderiv_eq, ← iteratedFDeriv_succ_cons_eq_fderiv hf, Fin.cons_self_tail]
theorem iteratedFDeriv_comp_perm {n : ℕ} {f : E → H} {x : E} (hf : ContDiffAt ℝ n f x) (v : Fin n → E)
    (σ : Equiv.Perm (Fin n)) : iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
  cases n with
  | zero => congr 1; funext i; exact i.elim0
  | succ n =>
    have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
    induction hσ using Submonoid.closure_induction generalizing v with
    | mem τ hτ => obtain ⟨i, rfl⟩ := hτ; exact iteratedFDeriv_swap_adjacent n f x hf v i
    | one => rfl
    | mul σ τ _ _ h1 h2 =>
      have : v ∘ (σ * τ) = (v ∘ σ) ∘ τ := by funext k; simp
      rw [this, h2, h1]
theorem iteratedFDeriv_comp_add_const {n : ℕ} {f : E → H} (L : G →L[ℝ] E) (a : E) {x : G}
    (hf : ContDiffAt ℝ n f (L x + a)) {i : ℕ} (hi : i ≤ n) (v : Fin i → G) :
    iteratedFDeriv ℝ i (fun z => f (L z + a)) x v = iteratedFDeriv ℝ i f (L x + a) fun j => L (v j) := by apply _root_.YangMills.SharedProofs.p13665 <;> assumption
end
section
variable {E₁ E₂ H : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂] [NormedAddCommGroup H] [NormedSpace ℝ H]
def partialJetRight (f : E₁ × E₂ → H) (y : E₂) {k : ℕ} (w : Fin k → E₂) (x : E₁) : H :=
  iteratedFDeriv ℝ k (fun y' => f (x, y')) y w
theorem partialJetRight_eq {n k : ℕ} {f : E₁ × E₂ → H} {x : E₁} {y : E₂} (hf : ContDiffAt ℝ n f (x, y))
    (hk : k ≤ n) (w : Fin k → E₂) :
    partialJetRight f y w x = iteratedFDeriv ℝ k f (x, y) fun j => (0, w j) := by
  have h := iteratedFDeriv_comp_add_const (ContinuousLinearMap.inr ℝ E₁ E₂) (x, 0) (x := y) (f := f)
    (by simpa using hf) hk w
  have e1 : (fun z => f ((ContinuousLinearMap.inr ℝ E₁ E₂) z + (x, 0))) = fun y' => f (x, y') := by
    funext z; simp
  rw [e1] at h
  simp only [partialJetRight]
  rw [h]
  simp
theorem eventually_contDiffAt_left {n : ℕ} {f : E₁ × E₂ → H} {x : E₁} {y : E₂} (hf : ContDiffAt ℝ n f (x, y)) :
    ∀ᶠ x' in 𝓝 x, ContDiffAt ℝ n f (x', y) := by apply _root_.YangMills.Construction.ParameterListDerivatives.eventually_contDiffAt_left <;> assumption
theorem contDiffAt_partialJetRight {n m k : ℕ} {f : E₁ × E₂ → H} {x : E₁} {y : E₂}
    (hf : ContDiffAt ℝ n f (x, y)) (hmn : m + k ≤ n) (w : Fin k → E₂) :
    ContDiffAt ℝ m (partialJetRight f y w) x := by
  have h1 : ContDiffAt ℝ m (fun z => iteratedFDeriv ℝ k f z fun j => (0, w j)) (x, y) :=
    contDiffAt_iteratedFDeriv_apply hf hmn _
  have h2 : ContDiffAt ℝ m (fun x' : E₁ => (x', y)) x := by fun_prop
  have h3 : ContDiffAt ℝ m (fun x' => iteratedFDeriv ℝ k f (x', y) fun j => (0, w j)) x :=
    ContDiffAt.comp x (g := fun z => iteratedFDeriv ℝ k f z fun j => (0, w j)) h1 h2
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [eventually_contDiffAt_left hf] with x' hx'
  exact partialJetRight_eq hx' (by omega) w
def IsSplitList {m p k : ℕ} (v : Fin p → E₁) (w : Fin k → E₂) (u : Fin m → E₁ × E₂) : Prop :=
  m = p + k ∧ (∀ (i : Fin m) (hi : i.val < p), u i = (v ⟨i.val, hi⟩, 0)) ∧
    ∀ (i : Fin m) (hi : p ≤ i.val) (hk : i.val - p < k), u i = (0, w ⟨i.val - p, hk⟩)
theorem iteratedFDeriv_partialJetRight {k : ℕ} (w : Fin k → E₂) {n : ℕ} {f : E₁ × E₂ → H} {y : E₂} :
    ∀ (p m : ℕ) (v : Fin p → E₁) (u : Fin m → E₁ × E₂) (x : E₁), IsSplitList v w u →
      ContDiffAt ℝ n f (x, y) → m ≤ n →
      iteratedFDeriv ℝ p (partialJetRight f y w) x v = iteratedFDeriv ℝ m f (x, y) u := by
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
    rw [hu', ← partialJetRight_eq hf hm w]
    simp
  | succ p ih =>
    intro m v u x hu hf hm
    obtain ⟨h0, h1, h2⟩ := hu
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hR : ContDiffAt ℝ (p + 1 : ℕ) (partialJetRight f y w) x :=
      contDiffAt_partialJetRight hf (by omega) w
    have hf' : ContDiffAt ℝ (m' + 1 : ℕ) f (x, y) := hf.of_le (by exact_mod_cast hm)
    have hu0 : u 0 = (v 0, 0) := h1 0 (by simp)
    have ht : IsSplitList (Fin.tail v) w (Fin.tail u) := by
      refine ⟨by omega, fun i hi => ?_, fun i hi hk => ?_⟩
      · have := h1 i.succ (by simpa using hi)
        simpa [Fin.tail_def] using this
      · have := h2 i.succ (by simp; omega) (by simp; omega)
        simp only [Fin.tail_def]
        rw [this]
        congr 2
        apply Fin.ext
        simp
    have e1 := iteratedFDeriv_succ_cons_eq_fderiv hR (v 0) (Fin.tail v)
    have e2 := iteratedFDeriv_succ_cons_eq_fderiv hf' (u 0) (Fin.tail u)
    rw [Fin.cons_self_tail] at e1 e2
    rw [e1, e2]
    have hev : (fun x' => iteratedFDeriv ℝ p (partialJetRight f y w) x' (Fin.tail v)) =ᶠ[𝓝 x]
        fun x' => iteratedFDeriv ℝ m' f (x', y) (Fin.tail u) := by
      filter_upwards [eventually_contDiffAt_left hf] with x' hx'
      exact ih m' _ _ x' ht hx' (by omega)
    rw [hev.fderiv_eq, hu0]
    have hd : DifferentiableAt ℝ (fun z => iteratedFDeriv ℝ m' f z (Fin.tail u)) (x, y) :=
      (contDiffAt_iteratedFDeriv_apply (m := 1) hf (by omega) _).differentiableAt (by norm_num)
    have hc : HasFDerivAt (fun x' : E₁ => (x', y)) (ContinuousLinearMap.inl ℝ E₁ E₂) x :=
      hasFDerivAt_prodMk_left x y
    have := (hd.hasFDerivAt.comp x hc).fderiv
    have e3 : (fun x' => iteratedFDeriv ℝ m' f (x', y) (Fin.tail u)) =
      (fun z => iteratedFDeriv ℝ m' f z (Fin.tail u)) ∘ fun x' : E₁ => (x', y) := rfl
    rw [e3, this]
    simp
end
end
section
open Set Filter Topology
section
variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
theorem iteratedDeriv_along_ray {n : ℕ} {R : Z → ℝ} (ξ : Z) (l : ℝ) {i : ℕ}
    (hf : ContDiffAt ℝ n R (l • ξ)) (hi : i ≤ n) :
    iteratedDeriv i (fun l' : ℝ => R (l' • ξ)) l = iteratedFDeriv ℝ i R (l • ξ) fun _ => ξ := by
  have h := iteratedFDeriv_comp_add_const (ContinuousLinearMap.toSpanSingleton ℝ ξ) 0 (x := l) (f := R)
    (by simpa using hf) hi (fun _ => (1 : ℝ))
  simp only [ContinuousLinearMap.toSpanSingleton_apply, add_zero, one_smul] at h
  rw [iteratedDeriv_eq_iteratedFDeriv]
  exact h
variable {Idx : Type} [Fintype Idx] [DecidableEq Idx]
theorem sum_prod_eq_prod_sum {i : ℕ} (f : Fin i → Idx → ℝ) :
    ∑ σ : Fin i → Idx, ∏ j, f j (σ j) = ∏ j, ∑ α, f j α := by
  have := Finset.prod_univ_sum (fun _ : Fin i => (Finset.univ : Finset Idx)) f
  rw [this, Fintype.piFinset_univ]
theorem multilinear_basis_expand {i : ℕ} (D : ContinuousMultilinearMap ℝ (fun _ : Fin i => Z) ℝ)
    (φ : Idx → Z → ℝ) (ε : Idx → Z) (ξ : Fin i → Z) (hξ : ∀ j, ξ j = ∑ α, φ α (ξ j) • ε α) :
    D ξ = ∑ σ : Fin i → Idx, (∏ j, φ (σ j) (ξ j)) * D fun j => ε (σ j) := by
  have h1 : ξ = fun j => ∑ α, φ α (ξ j) • ε α := funext hξ
  conv_lhs => rw [h1]
  rw [ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ]
  rfl
theorem multilinear_diag_bound {i : ℕ} (D : ContinuousMultilinearMap ℝ (fun _ : Fin i => Z) ℝ)
    (φ : Idx → Z → ℝ) (ε : Idx → Z) (ξ : Z) (hξ : ξ = ∑ α, φ α ξ • ε α) (w : Idx → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hT : ∀ σ : Fin i → Idx, |D fun j => ε (σ j)| ≤ B * ∏ j, w (σ j)) :
    |D fun _ => ξ| ≤ B * (∑ α, |φ α ξ| * w α) ^ i := by
  rw [multilinear_basis_expand D φ ε (fun _ => ξ) (fun _ => hξ)]
  calc |∑ σ : Fin i → Idx, (∏ j, φ (σ j) ξ) * D fun j => ε (σ j)|
      ≤ ∑ σ : Fin i → Idx, |(∏ j, φ (σ j) ξ) * D fun j => ε (σ j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : Fin i → Idx, B * ∏ j, (|φ (σ j) ξ| * w (σ j)) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [abs_mul, Finset.abs_prod, Finset.prod_mul_distrib]
        calc (∏ j, |φ (σ j) ξ|) * |D fun j => ε (σ j)|
            ≤ (∏ j, |φ (σ j) ξ|) * (B * ∏ j, w (σ j)) :=
              mul_le_mul_of_nonneg_left (hT σ) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
          _ = _ := by ring
    _ = B * (∑ α, |φ α ξ| * w α) ^ i := by
        rw [← Finset.mul_sum, sum_prod_eq_prod_sum (fun _ α => |φ α ξ| * w α)]
        simp
theorem hasDerivAt_diag_line {i : ℕ} {R : Z → ℝ} (φ : Idx → Z →L[ℝ] ℝ) (ε : Idx → Z)
    (hφ : ∀ z, z = ∑ α, φ α z • ε α) (l : ℝ) (ξ δ : Z)
    (hR : ContDiffAt ℝ (i + 1 : ℕ) R (l • ξ)) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ i R (l • (ξ + s • δ)) fun _ => ξ + s • δ)
      (∑ σ : Fin i → Idx,
        ((∑ j, (∏ j' ∈ Finset.univ.erase j, φ (σ j') ξ) * φ (σ j) δ) *
            iteratedFDeriv ℝ i R (l • ξ) (fun j => ε (σ j)) +
          (∏ j, φ (σ j) ξ) * (l * iteratedFDeriv ℝ (i + 1) R (l • ξ)
            (Fin.cons δ fun j => ε (σ j))))) 0 := by
  have hexp : ∀ s : ℝ, (iteratedFDeriv ℝ i R (l • (ξ + s • δ)) fun _ => ξ + s • δ) =
      ∑ σ : Fin i → Idx, (∏ j, (φ (σ j) ξ + s * φ (σ j) δ)) *
        iteratedFDeriv ℝ i R (l • (ξ + s • δ)) fun j => ε (σ j) := by
    intro s
    rw [multilinear_basis_expand (iteratedFDeriv ℝ i R (l • (ξ + s • δ))) (fun α z => φ α z) ε
      (fun _ => ξ + s • δ) (fun _ => hφ _)]
    simp
  simp_rw [hexp]
  refine HasDerivAt.fun_sum fun σ _ => ?_
  have h1 : HasDerivAt (fun s : ℝ => ∏ j, (φ (σ j) ξ + s * φ (σ j) δ))
      (∑ j, (∏ j' ∈ Finset.univ.erase j, φ (σ j') ξ) * φ (σ j) δ) 0 := by
    have := HasDerivAt.fun_finsetProd (u := Finset.univ)
      (f := fun j s => φ (σ j) ξ + s * φ (σ j) δ) (f' := fun j => φ (σ j) δ) (x := (0 : ℝ))
      (fun j _ => by simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (φ (σ j) δ)).const_add (φ (σ j) ξ))
    simpa using this
  have hT : DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ i R y fun j => ε (σ j)) (l • ξ) :=
    (contDiffAt_iteratedFDeriv_apply (m := 1) hR (by omega) _).differentiableAt (by norm_num)
  have hline : HasDerivAt (fun s : ℝ => l • (ξ + s • δ)) (l • δ) 0 := by
    have : HasDerivAt (fun s : ℝ => ξ + s • δ) δ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add ξ
    exact this.const_smul l
  have hx : l • (ξ + (0 : ℝ) • δ) = l • ξ := by simp
  have h2 : HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ i R (l • (ξ + s • δ)) fun j => ε (σ j))
      (l * iteratedFDeriv ℝ (i + 1) R (l • ξ) (Fin.cons δ fun j => ε (σ j))) 0 := by
    have hT' : DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ i R y fun j => ε (σ j))
        (l • (ξ + (0 : ℝ) • δ)) := by rw [hx]; exact hT
    have hc := hT'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
    have e : (fderiv ℝ (fun y => iteratedFDeriv ℝ i R y fun j => ε (σ j)) (l • (ξ + (0 : ℝ) • δ))) (l • δ) =
        l * iteratedFDeriv ℝ (i + 1) R (l • ξ) (Fin.cons δ fun j => ε (σ j)) := by
      rw [hx, map_smul, iteratedFDeriv_succ_cons_eq_fderiv hR]
      simp [smul_eq_mul]
    rw [e] at hc
    exact hc
  have h3 := h1.mul h2
  refine h3.congr_deriv ?_
  simp [hx]
theorem diag_line_deriv_bound {i : ℕ} {R : Z → ℝ} (φ : Idx → Z →L[ℝ] ℝ) (ε : Idx → Z)
    (hφ : ∀ z, z = ∑ α, φ α z • ε α) (l : ℝ) (ξ δ : Z)
    (hR : ContDiffAt ℝ (i + 1 : ℕ) R (l • ξ)) (w : Idx → ℝ) (hw : ∀ α, 0 ≤ w α) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ (σ : Fin i → Idx) (j : Fin i), φ (σ j) δ ≠ 0 →
      |iteratedFDeriv ℝ i R (l • ξ) fun j => ε (σ j)| ≤ B * ∏ j' ∈ Finset.univ.erase j, w (σ j'))
    (hc : ∀ σ : Fin i → Idx, |iteratedFDeriv ℝ (i + 1) R (l • ξ) (Fin.cons δ fun j => ε (σ j))| ≤
      B * ∏ j, w (σ j))
    (d : ℝ)
    (hd : HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ i R (l • (ξ + s • δ)) fun _ => ξ + s • δ) d 0) :
    |d| ≤ B * ((i : ℝ) * ((∑ α, |φ α δ|) * (∑ α, |φ α ξ| * w α) ^ (i - 1)) +
      |l| * (∑ α, |φ α ξ| * w α) ^ i) := by
  rw [hd.unique (hasDerivAt_diag_line φ ε hφ l ξ δ hR)]
  set A := ∑ α, |φ α ξ| * w α with hA
  set Ad := ∑ α, |φ α δ| with hAd
  have hterm1 : ∀ (σ : Fin i → Idx) (j : Fin i),
      |(∏ j' ∈ Finset.univ.erase j, φ (σ j') ξ) * φ (σ j) δ *
        iteratedFDeriv ℝ i R (l • ξ) fun j => ε (σ j)| ≤
      B * ∏ j', (if j' = j then |φ (σ j') δ| else |φ (σ j') ξ| * w (σ j')) := by
    intro σ j
    by_cases h0 : φ (σ j) δ = 0
    · have : 0 ≤ ∏ j', (if j' = j then |φ (σ j') δ| else |φ (σ j') ξ| * w (σ j')) := by
        refine Finset.prod_nonneg fun j' _ => ?_
        split_ifs
        · exact abs_nonneg _
        · exact mul_nonneg (abs_nonneg _) (hw _)
      simp only [h0, mul_zero, zero_mul, abs_zero]
      exact mul_nonneg hB this
    · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
      have e1 : ∏ x ∈ Finset.univ.erase j, (if x = j then |φ (σ x) δ| else |φ (σ x) ξ| * w (σ x)) =
          (∏ x ∈ Finset.univ.erase j, |φ (σ x) ξ|) * ∏ x ∈ Finset.univ.erase j, w (σ x) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun x hx => ?_
        simp [Finset.ne_of_mem_erase hx]
      rw [e1]
      simp only [if_true]
      rw [abs_mul, abs_mul, Finset.abs_prod]
      calc (∏ x ∈ Finset.univ.erase j, |φ (σ x) ξ|) * |φ (σ j) δ| *
            |iteratedFDeriv ℝ i R (l • ξ) fun j => ε (σ j)|
          ≤ (∏ x ∈ Finset.univ.erase j, |φ (σ x) ξ|) * |φ (σ j) δ| *
            (B * ∏ j' ∈ Finset.univ.erase j, w (σ j')) :=
            mul_le_mul_of_nonneg_left (hb σ j h0)
              (mul_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _))
        _ = _ := by ring
  have hsum1 : ∀ j : Fin i, ∑ σ : Fin i → Idx,
      ∏ j', (if j' = j then |φ (σ j') δ| else |φ (σ j') ξ| * w (σ j')) = Ad * A ^ (i - 1) := by
    intro j
    have h1 := sum_prod_eq_prod_sum (fun (j' : Fin i) α => if j' = j then |φ α δ| else |φ α ξ| * w α)
    have e0 : ∀ σ : Fin i → Idx, ∏ j', (if j' = j then |φ (σ j') δ| else |φ (σ j') ξ| * w (σ j')) =
        ∏ j', (fun (j' : Fin i) α => if j' = j then |φ α δ| else |φ α ξ| * w α) j' (σ j') := fun _ => rfl
    simp only [e0]
    rw [h1, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    have e2 : ∏ x ∈ Finset.univ.erase j, ∑ α, (if x = j then |φ α δ| else |φ α ξ| * w α) =
        A ^ (i - 1) := by
      rw [Finset.prod_congr rfl (g := fun _ => A) (fun x hx => by
        simp [Finset.ne_of_mem_erase hx, hA])]
      simp
    rw [e2]
    simp [hAd]
  calc |∑ σ : Fin i → Idx,
        ((∑ j, (∏ j' ∈ Finset.univ.erase j, φ (σ j') ξ) * φ (σ j) δ) *
            iteratedFDeriv ℝ i R (l • ξ) (fun j => ε (σ j)) +
          (∏ j, φ (σ j) ξ) * (l * iteratedFDeriv ℝ (i + 1) R (l • ξ)
            (Fin.cons δ fun j => ε (σ j))))|
      ≤ ∑ σ : Fin i → Idx, ((∑ j, B * ∏ j', (if j' = j then |φ (σ j') δ| else |φ (σ j') ξ| * w (σ j'))) +
          |l| * (B * ∏ j, (|φ (σ j) ξ| * w (σ j)))) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [Finset.sum_mul]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hterm1 σ j)
        · rw [abs_mul, abs_mul, Finset.abs_prod, Finset.prod_mul_distrib]
          calc (∏ j, |φ (σ j) ξ|) * (|l| * |iteratedFDeriv ℝ (i + 1) R (l • ξ) (Fin.cons δ fun j => ε (σ j))|)
              ≤ (∏ j, |φ (σ j) ξ|) * (|l| * (B * ∏ j, w (σ j))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hc σ) (abs_nonneg _))
                  (Finset.prod_nonneg fun _ _ => abs_nonneg _)
            _ = _ := by ring
    _ = B * ((i : ℝ) * (Ad * A ^ (i - 1)) + |l| * A ^ i) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        simp only [← Finset.mul_sum, hsum1]
        rw [sum_prod_eq_prod_sum (fun _ α => |φ α ξ| * w α)]
        simp
        ring
end
end
section
open Set Filter Topology MeasureTheory
open scoped Interval
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
theorem continuousOn_unitSlice {H : Type} [TopologicalSpace H] {I : Set ℝ} {U : Set E}
    (hIc : Icc (0 : ℝ) 1 ⊆ I) {Φ : ℝ × E → H} {x : E} (hx : x ∈ U)
    (hΦ : ContinuousOn Φ (I ×ˢ U)) : ContinuousOn (fun v => Φ (v, x)) (Icc (0 : ℝ) 1) :=
  hΦ.comp (by fun_prop) fun _ hv => ⟨hIc hv, hx⟩
theorem aestronglyMeasurable_unitSlice {H : Type} [NormedAddCommGroup H] {I : Set ℝ} {U : Set E}
    (hIc : Icc (0 : ℝ) 1 ⊆ I) {Φ : ℝ × E → H} {x : E} (hx : x ∈ U)
    (hΦ : ContinuousOn Φ (I ×ˢ U)) :
    AEStronglyMeasurable (fun v => Φ (v, x)) (volume.restrict (Ι (0 : ℝ) 1)) := by apply _root_.YangMills.Construction.HaarGapTailRegularity.aestronglyMeasurable_slice <;> assumption
theorem exists_closedBall_bound {H : Type} [NormedAddCommGroup H] {I : Set ℝ} {U : Set E}
    (hIc : Icc (0 : ℝ) 1 ⊆ I) (hU : IsOpen U) {Φ : ℝ × E → H} {x : E} (hx : x ∈ U)
    (hΦ : ContinuousOn Φ (I ×ˢ U)) :
    ∃ r C : ℝ, 0 < r ∧ Metric.closedBall x r ⊆ U ∧
      ∀ v ∈ Icc (0 : ℝ) 1, ∀ y ∈ Metric.closedBall x r, ‖Φ (v, y)‖ ≤ C := by apply _root_.YangMills.Construction.HaarGapTailRegularity.exists_closedBall_bound <;> assumption
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
def partialRight (Φ : ℝ × E → H) (p : ℝ × E) : E →L[ℝ] H :=
  (fderiv ℝ Φ p).comp (ContinuousLinearMap.inr ℝ ℝ E)
theorem continuousOn_partialRight {I : Set ℝ} {U : Set E} (hI : IsOpen I) (hU : IsOpen U)
    {Φ : ℝ × E → H} (hΦ : ContDiffOn ℝ 1 Φ (I ×ˢ U)) :
    ContinuousOn (partialRight Φ) (I ×ˢ U) :=
  (hΦ.continuousOn_fderiv_of_isOpen (hI.prod hU) le_rfl).clm_comp continuousOn_const
theorem hasFDerivAt_paramIntegral {M : ℝ → ℝ} (hM : Continuous M) {I : Set ℝ} {U : Set E} (hI : IsOpen I)
    (hIc : Icc (0 : ℝ) 1 ⊆ I) (hU : IsOpen U) {Φ : ℝ × E → H} (hΦ : ContDiffOn ℝ 1 Φ (I ×ˢ U)) {x : E}
    (hx : x ∈ U) :
    HasFDerivAt (fun x => ∫ v in (0 : ℝ)..1, M v • Φ (v, x))
      (∫ v in (0 : ℝ)..1, M v • partialRight Φ (v, x)) x := by
  have hc : ContinuousOn (fun p : ℝ × E => M p.1 • partialRight Φ p) (I ×ˢ U) :=
    (hM.comp continuous_fst).continuousOn.smul (continuousOn_partialRight hI hU hΦ)
  have hΦc : ContinuousOn (fun p : ℝ × E => M p.1 • Φ p) (I ×ˢ U) :=
    (hM.comp continuous_fst).continuousOn.smul hΦ.continuousOn
  obtain ⟨r, C, hr, hrU, hC⟩ := exists_closedBall_bound (Φ := fun p : ℝ × E => M p.1 • partialRight Φ p) hIc hU hx hc
  have hb : Metric.closedBall x r ∈ 𝓝 x := Metric.closedBall_mem_nhds x hr
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x t => M t • Φ (t, x)) (F' := fun x t => M t • partialRight Φ (t, x)) (bound := fun _ => C)
    hb ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [hb] with y hy
    exact aestronglyMeasurable_unitSlice (Φ := fun p : ℝ × E => M p.1 • Φ p) hIc (hrU hy) hΦc
  · exact ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le zero_le_one]
      exact continuousOn_unitSlice (Φ := fun p : ℝ × E => M p.1 • Φ p) hIc hx hΦc)
  · exact aestronglyMeasurable_unitSlice (Φ := fun p : ℝ × E => M p.1 • partialRight Φ p) hIc hx hc
  · refine Eventually.of_forall fun t ht y hy => hC t ?_ y hy
    rw [uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  · refine Eventually.of_forall fun t ht y hy => ?_
    rw [uIoc_of_le zero_le_one] at ht
    have hp : (t, y) ∈ I ×ˢ U := ⟨hIc (Ioc_subset_Icc_self ht), hrU hy⟩
    have hd : DifferentiableAt ℝ Φ (t, y) :=
      ((hΦ (t, y) hp).contDiffAt ((hI.prod hU).mem_nhds hp)).differentiableAt (by norm_num)
    exact (hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)).const_smul (M t)
end
theorem contDiffOn_paramIntegral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] {M : ℝ → ℝ},
      Continuous M → ∀ {I : Set ℝ} {U : Set E}, IsOpen I → Icc (0 : ℝ) 1 ⊆ I → IsOpen U →
      ∀ {Φ : ℝ × E → H}, ContDiffOn ℝ n Φ (I ×ˢ U) →
        ContDiffOn ℝ n (fun x => ∫ v in (0 : ℝ)..1, M v • Φ (v, x)) U := by apply _root_.YangMills.Construction.HaarGapTailRegularity.contDiffOn_intervalIntegral_param <;> assumption
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
theorem exists_tube_contDiffOn {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ} {Φ : ℝ × E → H} {x₀ : E}
    (h : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ n Φ (v, x₀)) :
    ∃ (I : Set ℝ) (U : Set E), IsOpen I ∧ Icc (0 : ℝ) 1 ⊆ I ∧ IsOpen U ∧ x₀ ∈ U ∧
      ContDiffOn ℝ n Φ (I ×ˢ U) := by
  have hS : IsOpen {p | ContDiffAt ℝ n Φ p} :=
    isOpen_iff_mem_nhds.2 fun p hp => (show ContDiffAt ℝ n Φ p from hp).eventually (by simp)
  obtain ⟨I, U, hI, hU, hIc, hxU, hsub⟩ := generalized_tube_lemma isCompact_Icc
    (isCompact_singleton (x := x₀)) hS (fun p hp => by
      obtain ⟨hp1, hp2⟩ := hp
      have : p = (p.1, x₀) := Prod.ext rfl hp2
      rw [this]
      exact h _ hp1)
  exact ⟨I, U, hI, hIc, hU, hxU rfl, fun p hp => (show ContDiffAt ℝ n Φ p from hsub hp).contDiffWithinAt⟩
theorem paramIntegral_jets {n : ℕ} {M : ℝ → ℝ} (hM : Continuous M) {Φ : ℝ × E → ℝ} {x₀ : E}
    (h : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ n Φ (v, x₀)) :
    ContDiffAt ℝ n (fun x => ∫ v in (0 : ℝ)..1, M v • Φ (v, x)) x₀ ∧
      ∀ m, m ≤ n → ∀ u : Fin m → E,
        iteratedFDeriv ℝ m (fun x => ∫ v in (0 : ℝ)..1, M v • Φ (v, x)) x₀ u =
          ∫ v in (0 : ℝ)..1, M v • iteratedFDeriv ℝ m Φ (v, x₀) fun j => (0, u j) := by
  obtain ⟨I, U, hI, hIc, hU, hx, hΦ⟩ := exists_tube_contDiffOn h
  have hW : ContDiffOn ℝ n (fun x => ∫ v in (0 : ℝ)..1, M v • Φ (v, x)) U :=
    contDiffOn_paramIntegral n ℝ hM hI hIc hU hΦ
  refine ⟨hW.contDiffAt (hU.mem_nhds hx), ?_⟩
  have key : ∀ m, m ≤ n → ∀ (u : Fin m → E), ∀ x ∈ U,
      iteratedFDeriv ℝ m (fun x => ∫ v in (0 : ℝ)..1, M v • Φ (v, x)) x u =
        ∫ v in (0 : ℝ)..1, M v • iteratedFDeriv ℝ m Φ (v, x) fun j => (0, u j) := by
    intro m
    induction m with
    | zero =>
      intro _ u x _
      simp
    | succ m ih =>
      intro hm u x hxU
      have hWx : ContDiffAt ℝ (m + 1 : ℕ) (fun x => ∫ v in (0 : ℝ)..1, M v • Φ (v, x)) x :=
        (hW.contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast hm)
      have e1 := iteratedFDeriv_succ_cons_eq_fderiv hWx (u 0) (Fin.tail u)
      rw [Fin.cons_self_tail] at e1
      rw [e1]
      set Ψ : ℝ × E → ℝ := fun p => iteratedFDeriv ℝ m Φ p fun j => (0, Fin.tail u j) with hΨ
      have hΨc : ContDiffOn ℝ 1 Ψ (I ×ˢ U) := by
        intro p hp
        have hp' : ContDiffAt ℝ n Φ p := (hΦ p hp).contDiffAt ((hI.prod hU).mem_nhds hp)
        exact (contDiffAt_iteratedFDeriv_apply (m := 1) hp' (by omega) _).contDiffWithinAt
      have hev : (fun y => iteratedFDeriv ℝ m (fun x => ∫ v in (0 : ℝ)..1, M v • Φ (v, x)) y (Fin.tail u)) =ᶠ[𝓝 x]
          fun y => ∫ v in (0 : ℝ)..1, M v • Ψ (v, y) := by
        filter_upwards [hU.mem_nhds hxU] with y hy
        exact ih (by omega) _ y hy
      rw [hev.fderiv_eq, (hasFDerivAt_paramIntegral hM hI hIc hU hΨc hxU).fderiv]
      have hint : IntervalIntegrable (fun v => M v • partialRight Ψ (v, x)) volume 0 1 :=
        ContinuousOn.intervalIntegrable (by
          rw [uIcc_of_le zero_le_one]
          exact continuousOn_unitSlice (Φ := fun p : ℝ × E => M p.1 • partialRight Ψ p) hIc hxU
            ((hM.comp continuous_fst).continuousOn.smul (continuousOn_partialRight hI hU hΨc)))
      rw [ContinuousLinearMap.intervalIntegral_apply hint]
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [uIcc_of_le zero_le_one] at hv
      have hp : (v, x) ∈ I ×ˢ U := ⟨hIc hv, hxU⟩
      have hp' : ContDiffAt ℝ (m + 1 : ℕ) Φ (v, x) :=
        ((hΦ _ hp).contDiffAt ((hI.prod hU).mem_nhds hp)).of_le (by exact_mod_cast hm)
      have e2 := iteratedFDeriv_succ_cons_eq_fderiv hp' (0, u 0) (fun j => (0, Fin.tail u j))
      have e3 : (Fin.cons ((0 : ℝ), u 0) (fun j => ((0 : ℝ), Fin.tail u j)) : Fin (m + 1) → ℝ × E) =
          fun j => (0, u j) := by
        funext k
        refine Fin.cases ?_ (fun k => ?_) k
        · simp
        · simp [Fin.tail_def]
      rw [e3] at e2
      simp only [partialRight, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inr_apply]
      rw [e2]
  intro m hm u
  exact key m hm u x₀ hx
end
end
section
open Set Filter Topology
section
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem iteratedFDeriv_comp_eq_sum {m : ℕ} {f : E → F} {g : F → ℝ} {x : E}
    (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g (f x)) (v : Fin m → E) :
    iteratedFDeriv ℝ m (g ∘ f) x v =
      ∑ c : OrderedFinpartition m, iteratedFDeriv ℝ c.length g (f x) fun i =>
        iteratedFDeriv ℝ (c.partSize i) f x (v ∘ c.emb i) := by
  obtain ⟨u, hu, hcf⟩ := hf.contDiffOn (m := m) le_rfl (by simp)
  obtain ⟨w, hw, hcg⟩ := hg.contDiffOn (m := m) le_rfl (by simp)
  obtain ⟨U₀, hU₀u, hU₀o, hxU₀⟩ := mem_nhds_iff.1 hu
  obtain ⟨W, hWw, hWo, hxW⟩ := mem_nhds_iff.1 hw
  have hcf' : ContDiffOn ℝ m f U₀ := hcf.mono hU₀u
  have hcg' : ContDiffOn ℝ m g W := hcg.mono hWw
  have hUo : IsOpen (U₀ ∩ f ⁻¹' W) := hcf'.continuousOn.isOpen_inter_preimage hU₀o hWo
  have hxU : x ∈ U₀ ∩ f ⁻¹' W := ⟨hxU₀, hxW⟩
  have hf' : ContDiffOn ℝ m f (U₀ ∩ f ⁻¹' W) := hcf'.mono inter_subset_left
  have tg := hcg'.ftaylorSeriesWithin hWo.uniqueDiffOn
  have tf := hf'.ftaylorSeriesWithin hUo.uniqueDiffOn
  have tc := tg.comp tf (fun y hy => hy.2)
  have h1 := tc.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := m) le_rfl hUo.uniqueDiffOn hxU
  rw [iteratedFDerivWithin_of_isOpen m hUo hxU] at h1
  rw [← h1]
  simp only [FormalMultilinearSeries.taylorComp, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply, ftaylorSeriesWithin]
  rw [iteratedFDerivWithin_of_isOpen _ hWo hxW]
  congr 1
  funext i
  rw [iteratedFDerivWithin_of_isOpen _ hUo hxU]
theorem iteratedFDeriv_comp_bound {m : ℕ} {f : E → F} {g : F → ℝ} {x : E}
    (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g (f x)) (v : Fin m → E) (M Θ : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ p, p ≤ m → ‖iteratedFDeriv ℝ p g (f x)‖ ≤ M)
    (hΘ : ∀ c : OrderedFinpartition m, ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) f x (v ∘ c.emb i)‖ ≤ Θ) :
    |iteratedFDeriv ℝ m (g ∘ f) x v| ≤ (Fintype.card (OrderedFinpartition m) : ℝ) * (M * Θ) := by
  rw [iteratedFDeriv_comp_eq_sum hf hg v]
  calc |∑ c : OrderedFinpartition m, iteratedFDeriv ℝ c.length g (f x) fun i =>
          iteratedFDeriv ℝ (c.partSize i) f x (v ∘ c.emb i)|
      ≤ ∑ c : OrderedFinpartition m, |iteratedFDeriv ℝ c.length g (f x) fun i =>
          iteratedFDeriv ℝ (c.partSize i) f x (v ∘ c.emb i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c : OrderedFinpartition m, M * Θ := by
        refine Finset.sum_le_sum fun c _ => ?_
        have h1 := (iteratedFDeriv ℝ c.length g (f x)).le_opNorm fun i =>
          iteratedFDeriv ℝ (c.partSize i) f x (v ∘ c.emb i)
        rw [Real.norm_eq_abs] at h1
        refine h1.trans ?_
        exact mul_le_mul (hM _ c.length_le) (hΘ c)
          (Finset.prod_nonneg fun _ _ => norm_nonneg _) hM0
    _ = _ := by simp
end
section
variable {A P : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup P] [NormedSpace ℝ P]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
def scaleJet (f : (ℝ × Z) × P → ℝ) {k : ℕ} (w : Fin k → P) (i : ℕ) (p : ℝ × Z) : ℝ :=
  iteratedDeriv i (fun l' => partialJetRight f 0 w (l', p.2)) p.1
theorem scaleJet_succ {f : (ℝ × Z) × P → ℝ} {k : ℕ} (w : Fin k → P) (i : ℕ) (p : ℝ × Z)
    (hd : DifferentiableAt ℝ (scaleJet f w i) p) :
    scaleJet f w (i + 1) p = fderiv ℝ (scaleJet f w i) p (1, 0) := by
  have h1 : scaleJet f w (i + 1) p = deriv (fun l' => scaleJet f w i (l', p.2)) p.1 := by
    simp only [scaleJet, iteratedDeriv_succ]
  rw [h1]
  have h2 : HasFDerivAt (fun l' : ℝ => (l', p.2)) (ContinuousLinearMap.inl ℝ ℝ Z) p.1 :=
    hasFDerivAt_prodMk_left p.1 p.2
  have hd' : HasFDerivAt (scaleJet f w i) (fderiv ℝ (scaleJet f w i) p) (p.1, p.2) := hd.hasFDerivAt
  have h3 := (hd'.comp p.1 h2).hasDerivAt.deriv
  have e : (scaleJet f w i ∘ fun l' : ℝ => (l', p.2)) = fun l' => scaleJet f w i (l', p.2) := rfl
  rw [e] at h3
  rw [h3]
  simp
theorem contDiffAt_scaleJet {n k : ℕ} {f : (ℝ × Z) × P → ℝ} (w : Fin k → P) {O : Set (ℝ × Z)}
    (hO : IsOpen O) (hf : ∀ p ∈ O, ContDiffAt ℝ n f (p, 0)) :
    ∀ (i m : ℕ), m + i + k ≤ n → ∀ p ∈ O, ContDiffAt ℝ m (scaleJet f w i) p := by
  intro i
  induction i with
  | zero =>
    intro m hm p hp
    have h1 : scaleJet f w 0 = partialJetRight f 0 w := by
      funext p
      simp [scaleJet]
    rw [h1]
    exact contDiffAt_partialJetRight (hf p hp) (by omega) w
  | succ i ih =>
    intro m hm p hp
    have h1 : ContDiffAt ℝ (m + 1 : ℕ) (scaleJet f w i) p := ih (m + 1) (by omega) p hp
    have h2 : ContDiffAt ℝ m (fun q => fderiv ℝ (scaleJet f w i) q (1, 0)) p := by
      have h3 : ContDiffAt ℝ m (fderiv ℝ (scaleJet f w i)) p := h1.fderiv_right (by norm_cast)
      exact h3.clm_apply contDiffAt_const
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hp] with q hq
    refine scaleJet_succ w i q ?_
    exact (ih 1 (by omega) q hq).differentiableAt (by norm_num)
theorem contDiffAt_slice_right {n : WithTop ℕ∞} {f : A × P → ℝ} {x : A} {y : P} (hf : ContDiffAt ℝ n f (x, y)) :
    ContDiffAt ℝ n (fun y' => f (x, y')) y :=
  ContDiffAt.comp y (g := f) hf (by fun_prop)
theorem scaleJet_add {n k : ℕ} {f₁ f₂ : (ℝ × Z) × P → ℝ} (w : Fin k → P) {O : Set (ℝ × Z)}
    (hO : IsOpen O) (h₁ : ∀ p ∈ O, ContDiffAt ℝ n f₁ (p, 0)) (h₂ : ∀ p ∈ O, ContDiffAt ℝ n f₂ (p, 0)) :
    ∀ i, i + k ≤ n → ∀ p ∈ O, scaleJet (fun q => f₁ q + f₂ q) w i p =
      scaleJet f₁ w i p + scaleJet f₂ w i p := by
  have h₃ : ∀ p ∈ O, ContDiffAt ℝ n (fun q => f₁ q + f₂ q) (p, 0) := fun p hp => (h₁ p hp).add (h₂ p hp)
  have hz : ∀ (g : (ℝ × Z) × P → ℝ) (p : ℝ × Z), scaleJet g w 0 p = partialJetRight g 0 w p := by
    intro g p; simp [scaleJet]
  intro i
  induction i with
  | zero =>
    intro hk p hp
    rw [hz, hz, hz]
    have s₁ : ContDiffAt ℝ k (fun y' => f₁ (p, y')) 0 :=
      (contDiffAt_slice_right (h₁ p hp)).of_le (by exact_mod_cast (by omega : k ≤ n))
    have s₂ : ContDiffAt ℝ k (fun y' => f₂ (p, y')) 0 :=
      (contDiffAt_slice_right (h₂ p hp)).of_le (by exact_mod_cast (by omega : k ≤ n))
    simp only [partialJetRight]
    have e := iteratedFDeriv_add_apply s₁ s₂
    exact congrArg (fun T => T w) e
  | succ i ih =>
    intro hk p hp
    have d₁ : DifferentiableAt ℝ (scaleJet f₁ w i) p :=
      (contDiffAt_scaleJet w hO h₁ i 1 (by omega) p hp).differentiableAt (by norm_num)
    have d₂ : DifferentiableAt ℝ (scaleJet f₂ w i) p :=
      (contDiffAt_scaleJet w hO h₂ i 1 (by omega) p hp).differentiableAt (by norm_num)
    have d₃ : DifferentiableAt ℝ (scaleJet (fun q => f₁ q + f₂ q) w i) p :=
      (contDiffAt_scaleJet w hO h₃ i 1 (by omega) p hp).differentiableAt (by norm_num)
    rw [scaleJet_succ w i p d₁, scaleJet_succ w i p d₂, scaleJet_succ w i p d₃]
    have he : scaleJet (fun q => f₁ q + f₂ q) w i =ᶠ[𝓝 p]
        fun q => scaleJet f₁ w i q + scaleJet f₂ w i q := by
      filter_upwards [hO.mem_nhds hp] with q hq
      exact ih (by omega) q hq
    rw [he.fderiv_eq, fderiv_fun_add d₁ d₂]
    rfl
theorem scaleJet_const_mul {n k : ℕ} {f : (ℝ × Z) × P → ℝ} (a : ℝ) (w : Fin k → P) {O : Set (ℝ × Z)}
    (hO : IsOpen O) (h : ∀ p ∈ O, ContDiffAt ℝ n f (p, 0)) :
    ∀ i, i + k ≤ n → ∀ p ∈ O, scaleJet (fun q => a * f q) w i p = a * scaleJet f w i p := by
  have h₃ : ∀ p ∈ O, ContDiffAt ℝ n (fun q => a * f q) (p, 0) := fun p hp => contDiffAt_const.mul (h p hp)
  have hz : ∀ (g : (ℝ × Z) × P → ℝ) (p : ℝ × Z), scaleJet g w 0 p = partialJetRight g 0 w p := by
    intro g p; simp [scaleJet]
  intro i
  induction i with
  | zero =>
    intro hk p hp
    rw [hz, hz]
    have s₁ : ContDiffAt ℝ k (fun y' => f (p, y')) 0 :=
      (contDiffAt_slice_right (h p hp)).of_le (by exact_mod_cast (by omega : k ≤ n))
    simp only [partialJetRight, ← smul_eq_mul]
    rw [iteratedFDeriv_const_smul_apply' s₁]
    rfl
  | succ i ih =>
    intro hk p hp
    have d₁ : DifferentiableAt ℝ (scaleJet f w i) p :=
      (contDiffAt_scaleJet w hO h i 1 (by omega) p hp).differentiableAt (by norm_num)
    have d₃ : DifferentiableAt ℝ (scaleJet (fun q => a * f q) w i) p :=
      (contDiffAt_scaleJet w hO h₃ i 1 (by omega) p hp).differentiableAt (by norm_num)
    rw [scaleJet_succ w i p d₁, scaleJet_succ w i p d₃]
    have he : scaleJet (fun q => a * f q) w i =ᶠ[𝓝 p] fun q => a * scaleJet f w i q := by
      filter_upwards [hO.mem_nhds hp] with q hq
      exact ih (by omega) q hq
    rw [he.fderiv_eq, fderiv_const_mul d₁]
    rfl
end
end
section
open Set Filter Topology
section
variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
theorem iteratedFDeriv_eq_of_eventuallyEq {f g : E → H} {x : E} (h : f =ᶠ[𝓝 x] g) (n : ℕ) :
    iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x :=
  (h.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
theorem iteratedFDeriv_reindex {M M' : ℕ} (h : M = M') {f : E → H} {x : E} (hf : ContDiffAt ℝ M f x)
    (t : Fin M → E) (u : Fin M' → E) (σ : Fin M' ≃ Fin M) (hu : ∀ i, u i = t (σ i)) :
    iteratedFDeriv ℝ M f x t = iteratedFDeriv ℝ M' f x u := by
  subst h
  have : u = t ∘ σ := funext hu
  rw [this]
  exact (iteratedFDeriv_comp_perm hf t σ).symm
theorem iteratedFDeriv_iteratedFDeriv_apply {p : ℕ} (u : Fin p → E) {N : ℕ} {f : E → H} :
    ∀ (m M : ℕ) (w : Fin m → E) (t : Fin M → E) (x : E), M = m + p →
      (∀ (i : Fin M) (hi : i.val < m), t i = w ⟨i.val, hi⟩) →
      (∀ (i : Fin M) (hi : m ≤ i.val) (hk : i.val - m < p), t i = u ⟨i.val - m, hk⟩) →
      ContDiffAt ℝ N f x → M ≤ N →
      iteratedFDeriv ℝ m (fun y => iteratedFDeriv ℝ p f y u) x w = iteratedFDeriv ℝ M f x t := by
  intro m
  induction m with
  | zero =>
    intro M w t x h0 h1 h2 hf hM
    have : M = p := by omega
    subst this
    have hu : t = u := by
      funext j
      have := h2 j (Nat.zero_le _) (by simp)
      simpa using this
    rw [hu]
    simp
  | succ m ih =>
    intro M w t x h0 h1 h2 hf hM
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    have hg : ContDiffAt ℝ (m + 1 : ℕ) (fun y => iteratedFDeriv ℝ p f y u) x :=
      contDiffAt_iteratedFDeriv_apply hf (by omega) u
    have hf' : ContDiffAt ℝ (M' + 1 : ℕ) f x := hf.of_le (by exact_mod_cast hM)
    have e1 := iteratedFDeriv_succ_cons_eq_fderiv hg (w 0) (Fin.tail w)
    have e2 := iteratedFDeriv_succ_cons_eq_fderiv hf' (t 0) (Fin.tail t)
    rw [Fin.cons_self_tail] at e1 e2
    rw [e1, e2, h1 0 (by simp)]
    have hev : (fun y => iteratedFDeriv ℝ m (fun y => iteratedFDeriv ℝ p f y u) y (Fin.tail w)) =ᶠ[𝓝 x]
        fun y => iteratedFDeriv ℝ M' f y (Fin.tail t) := by
      have hnear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ N f y := hf.eventually (by simp)
      filter_upwards [hnear] with y hy
      refine ih M' _ _ y (by omega) (fun i hi => ?_) (fun i hi hk => ?_) hy (by omega)
      · have := h1 i.succ (by simpa using hi)
        simpa [Fin.tail_def] using this
      · have := h2 i.succ (by simp; omega) (by simp; omega)
        simp only [Fin.tail_def]
        rw [this]
        congr 1
        apply Fin.ext
        simp
    rw [hev.fderiv_eq]
    rfl
end
section
variable {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
def secondPartialLeft (f : E₁ × E₂ → ℝ) (a b : E₁) (p : E₁ × E₂) : ℝ :=
  fderiv ℝ (fun x' => fderiv ℝ (fun x'' => f (x'', p.2)) x' a) p.1 b
def pairList {E : Type} (a b : E) : Fin 2 → E := Fin.cons a (Fin.cons b Fin.elim0)
def secondJetLeft (f : E₁ × E₂ → ℝ) (a b : E₁) (z : E₁ × E₂) : ℝ :=
  iteratedFDeriv ℝ 2 f z (pairList (b, 0) (a, 0))
theorem secondPartialLeft_eq {N : ℕ} (hN : 2 ≤ N) {f : E₁ × E₂ → ℝ} (a b : E₁) {z : E₁ × E₂}
    (hf : ContDiffAt ℝ N f z) : secondPartialLeft f a b z = secondJetLeft f a b z := by
  obtain ⟨x, y⟩ := z
  have hf2 : ContDiffAt ℝ (1 + 1 : ℕ) f (x, y) := hf.of_le (by exact_mod_cast hN)
  have h1 : secondJetLeft f a b (x, y) =
      fderiv ℝ (fun z' => fderiv ℝ f z' (a, 0)) (x, y) (b, 0) := by
    simp only [secondJetLeft, pairList]
    rw [iteratedFDeriv_succ_cons_eq_fderiv hf2]
    have : (fun y' => iteratedFDeriv ℝ 1 f y' (Fin.cons (a, 0) Fin.elim0)) =
        fun z' => fderiv ℝ f z' (a, 0) := by
      funext z'
      simp [iteratedFDeriv_one_apply]
    rw [this]
  rw [h1]
  have hnear : ∀ᶠ x' in 𝓝 x, ContDiffAt ℝ N f (x', y) := eventually_contDiffAt_left hf
  have hev : (fun x' => fderiv ℝ (fun x'' => f (x'', y)) x' a) =ᶠ[𝓝 x]
      fun x' => fderiv ℝ f (x', y) (a, 0) := by
    filter_upwards [hnear] with x' hx'
    have hd : DifferentiableAt ℝ f (x', y) := hx'.differentiableAt (by exact_mod_cast (by omega : N ≠ 0))
    have := (hd.hasFDerivAt.comp x' (hasFDerivAt_prodMk_left (𝕜 := ℝ) x' y)).fderiv
    have e : (fun x'' => f (x'', y)) = f ∘ fun x'' => (x'', y) := rfl
    rw [e, this]
    simp
  simp only [secondPartialLeft]
  rw [hev.fderiv_eq]
  have hd2 : DifferentiableAt ℝ (fun z' => fderiv ℝ f z' (a, 0)) (x, y) := by
    have h3 : ContDiffAt ℝ 1 (fderiv ℝ f) (x, y) := hf2.fderiv_right (by norm_num)
    exact (h3.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have := (hd2.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)).fderiv
  have e : (fun x' => fderiv ℝ f (x', y) (a, 0)) = (fun z' => fderiv ℝ f z' (a, 0)) ∘ fun x' => (x', y) := rfl
  rw [e, this]
  simp
theorem secondPartialLeft_eventuallyEq {N : ℕ} (hN : 2 ≤ N) {f : E₁ × E₂ → ℝ} (a b : E₁) {z : E₁ × E₂}
    (hf : ContDiffAt ℝ N f z) : secondPartialLeft f a b =ᶠ[𝓝 z] secondJetLeft f a b := by
  have hnear : ∀ᶠ z' in 𝓝 z, ContDiffAt ℝ N f z' := hf.eventually (by simp)
  filter_upwards [hnear] with z' hz'
  exact secondPartialLeft_eq hN a b hz'
theorem contDiffAt_secondPartialLeft {N M : ℕ} (hM : M + 2 ≤ N) {f : E₁ × E₂ → ℝ} (a b : E₁) {z : E₁ × E₂}
    (hf : ContDiffAt ℝ N f z) : ContDiffAt ℝ M (secondPartialLeft f a b) z := by
  have h1 : ContDiffAt ℝ M (secondJetLeft f a b) z := contDiffAt_iteratedFDeriv_apply hf hM _
  exact h1.congr_of_eventuallyEq (secondPartialLeft_eventuallyEq (by omega) a b hf)
theorem partialJetRight_secondPartialLeft {k N : ℕ} (hN : k + 2 ≤ N) {f : E₁ × E₂ → ℝ} (a b : E₁) {x : E₁} {y : E₂}
    (w : Fin k → E₂) (hf : ContDiffAt ℝ N f (x, y)) :
    partialJetRight (secondPartialLeft f a b) y w x =
      iteratedFDeriv ℝ 2 (partialJetRight f y w) x (pairList b a) := by
  have hN2 : 2 ≤ N := by omega
  have hT : ContDiffAt ℝ k (secondJetLeft f a b) (x, y) := contDiffAt_iteratedFDeriv_apply hf (by omega) _
  have hslice : (fun y' => secondPartialLeft f a b (x, y')) =ᶠ[𝓝 y] fun y' => secondJetLeft f a b (x, y') := by
    have h2 : Tendsto (fun y' : E₂ => (x, y')) (𝓝 y) (𝓝 (x, y)) := (Continuous.prodMk_right x).tendsto y
    exact h2.eventually (secondPartialLeft_eventuallyEq hN2 a b hf)
  have h1 : partialJetRight (secondPartialLeft f a b) y w x = partialJetRight (secondJetLeft f a b) y w x := by
    simp only [partialJetRight]
    rw [iteratedFDeriv_eq_of_eventuallyEq hslice k]
  rw [h1, partialJetRight_eq hT le_rfl w]
  set t : Fin (k + 2) → E₁ × E₂ := Fin.append (fun j => ((0 : E₁), w j)) (pairList (b, 0) (a, 0)) with ht
  have h3 : iteratedFDeriv ℝ k (secondJetLeft f a b) (x, y) (fun j => (0, w j)) =
      iteratedFDeriv ℝ (k + 2) f (x, y) t := by
    refine iteratedFDeriv_iteratedFDeriv_apply (pairList (b, (0 : E₂)) (a, 0)) (N := N) (f := f) k (k + 2)
      (fun j => ((0 : E₁), w j)) t (x, y) rfl (fun i hi => ?_) (fun i hi hk => ?_) hf hN
    · have : i = Fin.castAdd 2 ⟨i.val, hi⟩ := Fin.ext rfl
      rw [ht]
      conv_lhs => rw [this]
      rw [Fin.append_left]
    · have : i = Fin.natAdd k ⟨i.val - k, hk⟩ := Fin.ext (by simp; omega)
      rw [ht]
      conv_lhs => rw [this]
      rw [Fin.append_right]
  rw [h3]
  set u : Fin (2 + k) → E₁ × E₂ := Fin.append (pairList (b, 0) (a, 0)) (fun j => ((0 : E₁), w j)) with hu
  have hfM : ContDiffAt ℝ (k + 2 : ℕ) f (x, y) := hf.of_le (by exact_mod_cast hN)
  have h5 : iteratedFDeriv ℝ (k + 2) f (x, y) t = iteratedFDeriv ℝ (2 + k) f (x, y) u := by
    refine iteratedFDeriv_reindex (by omega) hfM t u finAddFlip fun i => ?_
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
    · rw [finAddFlip_apply_castAdd, hu, ht, Fin.append_left, Fin.append_right]
    · rw [finAddFlip_apply_natAdd, hu, ht, Fin.append_left, Fin.append_right]
  rw [h5]
  have hpair : ∀ j : Fin 2, pairList ((b, 0) : E₁ × E₂) (a, 0) j = (pairList b a j, 0) := by
    intro j
    refine Fin.cases ?_ (fun j' => ?_) j
    · simp [pairList]
    · have : j' = 0 := Subsingleton.elim _ _
      subst this
      simp [pairList]
  refine (iteratedFDeriv_partialJetRight w 2 (2 + k) (pairList b a) u x ⟨rfl, fun i hi => ?_, fun i hi hk => ?_⟩ hf
    (by omega)).symm
  · have : i = Fin.castAdd k ⟨i.val, hi⟩ := Fin.ext rfl
    rw [hu]
    conv_lhs => rw [this]
    rw [Fin.append_left, hpair]
  · have : i = Fin.natAdd 2 ⟨i.val - 2, hk⟩ := Fin.ext (by simp; omega)
    rw [hu]
    conv_lhs => rw [this]
    rw [Fin.append_right]
end
section
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
theorem scaleJet_congr {f₁ f₂ : (ℝ × Z) × P → ℝ} {k : ℕ} (w : Fin k → P) {O : Set (ℝ × Z)} (hO : IsOpen O)
    (h : ∀ p ∈ O, f₁ =ᶠ[𝓝 (p, 0)] f₂) (i : ℕ) {p : ℝ × Z} (hp : p ∈ O) :
    scaleJet f₁ w i p = scaleJet f₂ w i p := by
  have hnear : ∀ᶠ l' in 𝓝 p.1, (l', p.2) ∈ O := by
    have h2 : Tendsto (fun l' : ℝ => (l', p.2)) (𝓝 p.1) (𝓝 (p.1, p.2)) :=
      (Continuous.prodMk_left p.2).tendsto p.1
    exact h2.eventually (hO.mem_nhds hp)
  have hev : (fun l' => partialJetRight f₁ 0 w (l', p.2)) =ᶠ[𝓝 p.1] fun l' => partialJetRight f₂ 0 w (l', p.2) := by
    filter_upwards [hnear] with l' hl'
    simp only [partialJetRight]
    have h2 : Tendsto (fun y' : P => ((l', p.2), y')) (𝓝 0) (𝓝 ((l', p.2), 0)) :=
      (Continuous.prodMk_right (l', p.2)).tendsto 0
    have h3 : (fun y' => f₁ ((l', p.2), y')) =ᶠ[𝓝 0] fun y' => f₂ ((l', p.2), y') := h2.eventually (h _ hl')
    rw [iteratedFDeriv_eq_of_eventuallyEq h3 k]
  simp only [scaleJet]
  exact hev.iteratedDeriv_eq i
end
end
section
open Set Filter Topology
open YangMills.Construction.BlockAverages
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.ScaledVariables
variable {F : BlockFrame}
def translatedObservable {Zp : Type} (G : Zp → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (p : Zp × (Fin k → ℝ)) : ℝ :=
  G p.1 (leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X p.2) V)
abbrev unitParams (k : ℕ) : Fin k → Fin k → ℝ := fun l => Pi.single l 1
def displacementMap {l : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (e : Fin l → EuclideanSpace ℝ (Fin 3))
    (k : ℕ) : (Fin (l + k) → ℝ) →L[ℝ] StepVariable (finiteCells F) × (Fin k → ℝ) :=
  ContinuousLinearMap.prod
    (∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (l + k) => ℝ) (Fin.castAdd k i)).smulRight
      (bondVariation (b i) (e i)))
    (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.natAdd l j))
theorem jointDisplacement_eq {l k : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (e : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    jointDisplacement G η V b e c X = fun τ => translatedObservable G V c X (displacementMap b e k τ + (η, 0)) := by
  funext τ
  simp only [jointDisplacement, translatedObservable, displacementMap, displacedPoint]
  congr 1
  · simp only [ContinuousLinearMap.prod_apply, Prod.fst_add, sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [bondVariation]
    rw [Pi.single_smul]
  · congr 2
    funext j
    simp
theorem displacementMap_castAdd {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (e : Fin l → EuclideanSpace ℝ (Fin 3)) (i : Fin l) :
    displacementMap b e k (Pi.single (Fin.castAdd k i) 1) = (bondVariation (b i) (e i), 0) := by
  simp only [displacementMap, ContinuousLinearMap.prod_apply, sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  refine Prod.ext ?_ ?_
  · simp only
    rw [Finset.sum_eq_single i]
    · simp
    · intro i' _ hne
      have : Fin.castAdd k i' ≠ Fin.castAdd k i := fun h => hne (Fin.castAdd_injective _ _ h)
      simp [Pi.single_apply, this]
    · simp
  · funext j
    have : Fin.natAdd l j ≠ Fin.castAdd k i := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [Pi.single_apply, this]
theorem displacementMap_natAdd {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (e : Fin l → EuclideanSpace ℝ (Fin 3)) (j : Fin k) :
    displacementMap b e k (Pi.single (Fin.natAdd l j) 1) = (0, Pi.single j 1) := by
  simp only [displacementMap, ContinuousLinearMap.prod_apply, sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  refine Prod.ext ?_ ?_
  · simp only
    refine Finset.sum_eq_zero fun i _ => ?_
    have : Fin.castAdd k i ≠ Fin.natAdd l j := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [Pi.single_apply, this]
  · funext j'
    by_cases h : j' = j
    · subst h; simp
    · have : Fin.natAdd l j' ≠ Fin.natAdd l j := fun h' => h (Fin.natAdd_injective _ _ h')
      simp [Pi.single_apply, this, h]
theorem jointMixedDeriv_eq_jet {l k : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (e : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hf : ContDiffAt ℝ (l + k : ℕ) (translatedObservable G V c X) (η, 0)) :
    jointMixedDeriv G η V b e c X =
      iteratedFDeriv ℝ l (partialJetRight (translatedObservable G V c X) 0 (unitParams k)) η
        fun i => bondVariation (b i) (e i) := by
  have h := iteratedFDeriv_comp_add_const (displacementMap b e k) (η, 0) (x := 0) (f := translatedObservable G V c X)
    (by simpa using hf) le_rfl (fun i => Pi.single i 1)
  simp only [jointMixedDeriv]
  rw [jointDisplacement_eq, h]
  simp only [map_zero, zero_add]
  refine (iteratedFDeriv_partialJetRight (unitParams k) l (l + k) _ _ η ⟨rfl, fun i hi => ?_, fun i hi hk => ?_⟩ hf le_rfl).symm
  · have this : i = Fin.castAdd k ⟨i.val, hi⟩ := Fin.ext rfl
    have h2 := displacementMap_castAdd (k := k) b e ⟨i.val, hi⟩
    rwa [← this] at h2
  · have this : i = Fin.natAdd l ⟨i.val - l, hk⟩ := Fin.ext (by simp; omega)
    have h2 := displacementMap_natAdd (l := l) b e ⟨i.val - l, hk⟩
    rwa [← this] at h2
abbrev ChordCoord (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F)) × Fin 3
def chordBasis (α : ChordCoord F) : StepVariable (finiteCells F) :=
  bondVariation α.1 (EuclideanSpace.single α.2 1)
def chordCoord (α : ChordCoord F) : StepVariable (finiteCells F) →L[ℝ] ℝ :=
  (EuclideanSpace.proj α.2).comp (ContinuousLinearMap.proj α.1)
theorem chordCoord_apply (α : ChordCoord F) (ζ : StepVariable (finiteCells F)) :
    chordCoord α ζ = ζ α.1 α.2 := rfl
theorem chordBasis_expand (ζ : StepVariable (finiteCells F)) :
    ζ = ∑ α : ChordCoord F, chordCoord α ζ • chordBasis α := by
  funext b
  ext a
  have h1 : ∀ (b' : ↥(chordBonds (finiteCells F))) (a' : Fin 3),
      ((chordCoord (b', a') ζ • chordBasis (b', a') : StepVariable (finiteCells F)) b) a =
        if b' = b then (if a' = a then ζ b' a' else 0) else 0 := by
    intro b' a'
    simp only [chordCoord_apply, chordBasis, bondVariation, Pi.smul_apply, Pi.single_apply]
    by_cases hb : b = b'
    · subst hb
      by_cases ha : a' = a
      · subst ha; simp
      · simp [ha, EuclideanSpace.single_apply, Ne.symm ha]
    · simp [hb, Ne.symm hb]
  have h2 : (∑ α : ChordCoord F, chordCoord α ζ • chordBasis α) b a =
      ∑ α : ChordCoord F, ((chordCoord α ζ • chordBasis α : StepVariable (finiteCells F)) b) a := by
    simp [Finset.sum_apply]
  rw [h2, Fintype.sum_prod_type]
  simp only [h1]
  simp
def unitImaginary : imaginaryQuaternions := ⟨⟨0, 1, 0, 0⟩, rfl⟩
theorem norm_coe_unitImaginary : ‖(unitImaginary : Quaternion ℝ)‖ = 1 := by apply _root_.YangMills.Construction.ChartedEnergyRegularity.norm_coe_imaginaryUnit <;> assumption
theorem norm_unitImaginary : ‖unitImaginary‖ = 1 := norm_coe_unitImaginary
def doubledIndex (F : BlockFrame) (i : Fin (Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F))) : ChordCoord F :=
  (Fintype.equivFin (ChordCoord F)).symm
    (Fin.addCases (motive := fun _ => Fin (Fintype.card (ChordCoord F))) (fun j => j) (fun j => j) i)
def doubledBond (F : BlockFrame) (i : Fin (Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F))) :
    ↥(chordBonds (finiteCells F)) := (doubledIndex F i).1
def doubledUnit (F : BlockFrame) (i : Fin (Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F))) :
    EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (doubledIndex F i).2 1
theorem norm_doubledUnit (F : BlockFrame) (i) : ‖doubledUnit F i‖ = 1 := by
  simp [doubledUnit]
def doubledParams (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) :
    Fin ((Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F)) + (k + n)) → ℝ :=
  Fin.addCases
    (fun a => Fin.addCases (motive := fun _ => ℝ)
      (fun a₁ => chordCoord ((Fintype.equivFin (ChordCoord F)).symm a₁) (p.1 - η)) (fun _ => 0) a)
    (fun d => Fin.addCases (motive := fun _ => ℝ) (fun j => s j * p.2 j) (fun _ => 0) d)
theorem doubledParams_left (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (a : Fin (Fintype.card (ChordCoord F))) :
    doubledParams F η s n p (Fin.castAdd (k + n) (Fin.castAdd _ a)) =
      chordCoord ((Fintype.equivFin (ChordCoord F)).symm a) (p.1 - η) := by
  simp only [doubledParams, Fin.addCases_left]
theorem doubledParams_mid (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (a : Fin (Fintype.card (ChordCoord F))) :
    doubledParams F η s n p (Fin.castAdd (k + n) (Fin.natAdd _ a)) = 0 := by
  simp only [doubledParams, Fin.addCases_left, Fin.addCases_right]
theorem doubledParams_top (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (j : Fin k) :
    doubledParams F η s n p (Fin.natAdd _ (Fin.castAdd n j)) = s j * p.2 j := by
  simp only [doubledParams, Fin.addCases_left, Fin.addCases_right]
theorem doubledParams_pad (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (j : Fin n) :
    doubledParams F η s n p (Fin.natAdd _ (Fin.natAdd k j)) = 0 := by
  simp only [doubledParams, Fin.addCases_right]
theorem doubledParams_contDiff (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (doubledParams F η s n) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.addCases (fun a => ?_) (fun d => ?_) i
  · refine Fin.addCases (fun a₁ => ?_) (fun a₂ => ?_) a
    · simp only [doubledParams_left]
      exact (chordCoord _).contDiff.comp (contDiff_fst.sub contDiff_const)
    · simp only [doubledParams_mid]
      exact contDiff_const
  · refine Fin.addCases (fun j => ?_) (fun a₂ => ?_) d
    · simp only [doubledParams_top]
      exact contDiff_const.mul ((contDiff_apply ℝ ℝ j).comp contDiff_snd)
    · simp only [doubledParams_pad]
      exact contDiff_const
theorem doubledParams_base (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ) :
    doubledParams F η s n (η, 0) = 0 := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun d => ?_) i
  · refine Fin.addCases (fun a₁ => ?_) (fun a₂ => ?_) a
    · rw [doubledParams_left]; simp
    · rw [doubledParams_mid]; rfl
  · refine Fin.addCases (fun j => ?_) (fun a₂ => ?_) d
    · rw [doubledParams_top]; simp
    · rw [doubledParams_pad]; rfl
theorem displacedPoint_doubledParams (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) :
    displacedPoint η (doubledBond F) (doubledUnit F)
      (fun i => doubledParams F η s n p (Fin.castAdd (k + n) i)) = p.1 := by
  simp only [displacedPoint]
  rw [Fin.sum_univ_add]
  have h2 : ∑ i, (Pi.single (doubledBond F (Fin.natAdd _ i))
      (doubledParams F η s n p (Fin.castAdd (k + n) (Fin.natAdd _ i)) • doubledUnit F (Fin.natAdd _ i)) :
        StepVariable (finiteCells F)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [doubledParams_mid]
    simp
  rw [h2, add_zero]
  have h1 : ∀ a : Fin (Fintype.card (ChordCoord F)),
      (Pi.single (doubledBond F (Fin.castAdd _ a))
        (doubledParams F η s n p (Fin.castAdd (k + n) (Fin.castAdd _ a)) • doubledUnit F (Fin.castAdd _ a)) :
          StepVariable (finiteCells F)) =
      chordCoord ((Fintype.equivFin (ChordCoord F)).symm a) (p.1 - η) •
        chordBasis ((Fintype.equivFin (ChordCoord F)).symm a) := by
    intro a
    rw [doubledParams_left]
    simp only [doubledBond, doubledUnit, doubledIndex, Fin.addCases_left, chordBasis, bondVariation]
    rw [Pi.single_smul]
  simp only [h1]
  rw [Equiv.sum_comp (Fintype.equivFin (ChordCoord F)).symm
    (fun α => chordCoord α (p.1 - η) • chordBasis α), ← chordBasis_expand]
  abel
theorem bondSpread_doubledParams (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (c : Fin k → F.Site F.top × Fin 4)
    (X X' : Fin k → imaginaryQuaternions)
    (hX : ∀ j, s j • X' j = X j) (c₀ : F.Site F.top × Fin 4) (X₀ : imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread (Fin.addCases (motive := fun _ => F.Site F.top × Fin 4) c fun _ : Fin n => c₀)
      (Fin.addCases (motive := fun _ => imaginaryQuaternions) X' fun _ : Fin n => X₀)
      (fun i => doubledParams F η s n p (Fin.natAdd _ i)) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X p.2 := by
  funext y i
  simp only [_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_right, doubledParams_pad, zero_smul, ite_self, Finset.sum_const_zero, add_zero,
    Fin.addCases_left, doubledParams_top]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hX j, smul_smul, mul_comm]
theorem contDiffAt_translatedObservable {n : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (hG : ∀ (p : ℕ) (c' : Fin p → F.Site F.top × Fin 4) (X' : Fin p → imaginaryQuaternions), AreUnitVectors X' →
      n ≤ p → ContDiffAt ℝ n (jointDisplacement G η V (doubledBond F) (doubledUnit F) c' X') 0) :
    ContDiffAt ℝ n (translatedObservable G V c X) (η, 0) := by
  classical
  set X' : Fin k → imaginaryQuaternions := fun j => if X j = 0 then unitImaginary else (‖X j‖⁻¹ : ℝ) • X j with hX'
  set s : Fin k → ℝ := fun j => ‖X j‖ with hs
  have hsX : ∀ j, s j • X' j = X j := by
    intro j
    by_cases h : X j = 0
    · simp [hs, hX', h]
    · have h0 : ‖X j‖ ≠ 0 := norm_ne_zero_iff.2 h
      simp only [hs, hX', h, if_false, smul_smul, mul_inv_cancel₀ h0, one_smul]
  have hunit : ∀ j, ‖X' j‖ = 1 := by
    intro j
    by_cases h : X j = 0
    · simp only [hX', h, if_true, norm_unitImaginary]
    · have h0 : ‖X j‖ ≠ 0 := norm_ne_zero_iff.2 h
      simp only [hX', h, if_false, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h0]
  set c₀ : F.Site F.top × Fin 4 := (0, 0)
  set cc := Fin.addCases (motive := fun _ => F.Site F.top × Fin 4) c fun _ : Fin n => c₀ with hcc
  set XX := Fin.addCases (motive := fun _ => imaginaryQuaternions) X' fun _ : Fin n => unitImaginary with hXX
  have hu : AreUnitVectors XX := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [hXX, Fin.addCases_left, hunit]
    · simp only [hXX, Fin.addCases_right, norm_unitImaginary]
  have h1 := hG (k + n) cc XX hu (by omega)
  have h2 : ContDiffAt ℝ n (doubledParams F η s n) (η, 0) :=
    ((doubledParams_contDiff F η s n).of_le (by exact_mod_cast le_top)).contDiffAt
  have h3 : ContDiffAt ℝ n (jointDisplacement G η V (doubledBond F) (doubledUnit F) cc XX)
      (doubledParams F η s n (η, 0)) := by
    rw [doubledParams_base]; exact h1
  have h4 := ContDiffAt.comp (η, (0 : Fin k → ℝ)) h3 h2
  refine h4.congr_of_eventuallyEq (Eventually.of_forall fun p => ?_)
  simp only [Function.comp, jointDisplacement, translatedObservable]
  rw [displacedPoint_doubledParams, bondSpread_doubledParams F η s n p c X X' hsX c₀ unitImaginary]
end
section
open Set Filter Topology
open YangMills.Construction.BlockAverages
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.ScaledVariables
variable {F : BlockFrame}
def scaledObservable (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (p : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)) : ℝ :=
  Ob p.1.1 p.1.2 (leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X p.2) V)
theorem scaleDeriv_eq_scaleJet (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (i : ℕ)
    (ζ : StepVariable (finiteCells F)) (l : ℝ) :
    scaleDeriv Ob V c X i ζ l = scaleJet (scaledObservable Ob V c X) (unitParams k) i (l, ζ) := rfl
def scaleBallSet (F : BlockFrame) (ρ : ℝ) : Set (ℝ × StepVariable (finiteCells F)) :=
  {p | ∀ b, |p.1| * ‖p.2 b‖ < ρ}
theorem isOpen_scaleBallSet (ρ : ℝ) : IsOpen (scaleBallSet F ρ) := by
  have h : scaleBallSet F ρ = ⋂ b, {p | |p.1| * ‖p.2 b‖ < ρ} := by
    ext p; simp [scaleBallSet]
  rw [h]
  exact isOpen_iInter_of_finite fun b => isOpen_lt (by fun_prop) continuous_const
theorem mem_scaleBallSet {ρ l : ℝ} {ζ : StepVariable (finiteCells F)} (hl : 0 < l)
    (h : MemScaledBalls ρ l ζ) : (l, ζ) ∈ scaleBallSet F ρ := by
  intro b
  simpa [abs_of_pos hl] using h b
theorem controlledOrder_le {k i : ℕ} (h : IsControlledOrder k i) : 1 + i + k ≤ 6 := by
  rcases h with h | h <;> omega
structure IsDecayingPart (κ ρ l₁ : ℝ) (Y : F.Cell) (V : F.GaugeField F.top)
    (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (Bd : StepVariable (finiteCells F) → ℝ)
    (Sd : ↥(chordBonds (finiteCells F)) → StepVariable (finiteCells F) → ℝ) : Prop where
  smooth : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), ∀ p ∈ scaleBallSet F ρ,
    ContDiffAt ℝ (6 : ℕ) (scaledObservable Ob V c X) (p, 0)
  deriv_le : ∀ (k i : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (l : ℝ)
    (ζ : StepVariable (finiteCells F)), IsControlledOrder k i → AreUnitVectors X → 0 < l → l ≤ l₁ →
    MemScaledBalls ρ l ζ →
    |scaleDeriv Ob V c X i ζ l| ≤ Bd ζ * Real.exp (-(2 ^ 4 * κ * bondSpan Y c))
  partial_le : ∀ (k i : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (l : ℝ)
    (ζ : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) (e : BondVector), IsControlledOrder k i →
    AreUnitVectors X → 0 < l → l ≤ l₁ → MemScaledBalls ρ l ζ → ‖e‖ = 1 →
    |bondPartialDeriv (fun ζ' => scaleDeriv Ob V c X i ζ' l) b ζ e| ≤
      Sd b ζ * Real.exp (-(2 ^ 4 * κ * bondSpan Y (Fin.cons (enclosingCell b.1.1, 0) c :
        Fin (k + 1) → F.Site F.top × Fin 4)))
variable {κ ρ l₁ : ℝ} {Y : F.Cell} {V : F.GaugeField F.top}
theorem eventually_mem_scaleBallSet {l : ℝ} {ζ : StepVariable (finiteCells F)} (hp : (l, ζ) ∈ scaleBallSet F ρ) :
    ∀ᶠ ζ' in 𝓝 ζ, (l, ζ') ∈ scaleBallSet F ρ := by
  have h2 : Tendsto (fun ζ' : StepVariable (finiteCells F) => (l, ζ')) (𝓝 ζ) (𝓝 (l, ζ)) :=
    (Continuous.prodMk_right l).tendsto ζ
  exact h2.eventually ((isOpen_scaleBallSet ρ).mem_nhds hp)
theorem differentiableAt_scaleDeriv {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {k i : ℕ}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    (hj : ∀ p ∈ scaleBallSet F ρ, ContDiffAt ℝ (6 : ℕ) (scaledObservable Ob V c X) (p, 0))
    (hik : 1 + i + k ≤ 6) {l : ℝ} {ζ : StepVariable (finiteCells F)} (hp : (l, ζ) ∈ scaleBallSet F ρ) :
    DifferentiableAt ℝ (fun ζ' => scaleDeriv Ob V c X i ζ' l) ζ := by
  have h1 : DifferentiableAt ℝ (scaleJet (scaledObservable Ob V c X) (unitParams k) i) (l, ζ) :=
    (contDiffAt_scaleJet (unitParams k) (isOpen_scaleBallSet ρ) hj i 1 hik (l, ζ) hp).differentiableAt
      (by norm_num)
  have h2 : DifferentiableAt ℝ (fun ζ' : StepVariable (finiteCells F) => (l, ζ')) ζ := by fun_prop
  exact DifferentiableAt.comp ζ (g := scaleJet (scaledObservable Ob V c X) (unitParams k) i) h1 h2
theorem IsDecayingPart.add {Ob₁ Ob₂ : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {Bd₁ Bd₂ : StepVariable (finiteCells F) → ℝ}
    {Sd₁ Sd₂ : ↥(chordBonds (finiteCells F)) → StepVariable (finiteCells F) → ℝ}
    (h₁ : IsDecayingPart κ ρ l₁ Y V Ob₁ Bd₁ Sd₁) (h₂ : IsDecayingPart κ ρ l₁ Y V Ob₂ Bd₂ Sd₂) :
    IsDecayingPart κ ρ l₁ Y V (fun l ζ V' => Ob₁ l ζ V' + Ob₂ l ζ V') (fun ζ => Bd₁ ζ + Bd₂ ζ)
      (fun b ζ => Sd₁ b ζ + Sd₂ b ζ) := by
  have hadd : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (i : ℕ), i + k ≤ 6 →
      ∀ p ∈ scaleBallSet F ρ,
      scaleJet (scaledObservable (fun l ζ V' => Ob₁ l ζ V' + Ob₂ l ζ V') V c X) (unitParams k) i p =
        scaleJet (scaledObservable Ob₁ V c X) (unitParams k) i p + scaleJet (scaledObservable Ob₂ V c X) (unitParams k) i p :=
    fun c X i hik p hp => scaleJet_add (unitParams _) (isOpen_scaleBallSet ρ) (h₁.smooth _ c X)
      (h₂.smooth _ c X) i hik p hp
  refine ⟨fun k c X p hp => (h₁.smooth k c X p hp).add (h₂.smooth k c X p hp), ?_, ?_⟩
  · intro k i c X l ζ hki hX hl hl₁ hb
    have hp := mem_scaleBallSet hl hb
    rw [scaleDeriv_eq_scaleJet, hadd c X i (by have := controlledOrder_le hki; omega) _ hp, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (h₁.deriv_le k i c X l ζ hki hX hl hl₁ hb)
      (h₂.deriv_le k i c X l ζ hki hX hl hl₁ hb))
  · intro k i c X l ζ b e hki hX hl hl₁ hb he
    have hp := mem_scaleBallSet hl hb
    have hik := controlledOrder_le hki
    have hev : (fun ζ' => scaleDeriv (fun l ζ V' => Ob₁ l ζ V' + Ob₂ l ζ V') V c X i ζ' l) =ᶠ[𝓝 ζ]
        fun ζ' => scaleDeriv Ob₁ V c X i ζ' l + scaleDeriv Ob₂ V c X i ζ' l := by
      filter_upwards [eventually_mem_scaleBallSet hp] with ζ' hζ'
      exact hadd c X i (by omega) _ hζ'
    have d₁ := differentiableAt_scaleDeriv (h₁.smooth k c X) hik hp
    have d₂ := differentiableAt_scaleDeriv (h₂.smooth k c X) hik hp
    have e1 : bondPartialDeriv (fun ζ' => scaleDeriv (fun l ζ V' => Ob₁ l ζ V' + Ob₂ l ζ V') V c X i ζ' l) b ζ e =
        bondPartialDeriv (fun ζ' => scaleDeriv Ob₁ V c X i ζ' l) b ζ e +
          bondPartialDeriv (fun ζ' => scaleDeriv Ob₂ V c X i ζ' l) b ζ e := by
      simp only [bondPartialDeriv]
      rw [hev.fderiv_eq, fderiv_fun_add d₁ d₂]
      rfl
    rw [e1, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (h₁.partial_le k i c X l ζ b e hki hX hl hl₁ hb he)
      (h₂.partial_le k i c X l ζ b e hki hX hl hl₁ hb he))
theorem IsDecayingPart.const_mul {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {Bd : StepVariable (finiteCells F) → ℝ}
    {Sd : ↥(chordBonds (finiteCells F)) → StepVariable (finiteCells F) → ℝ}
    (h : IsDecayingPart κ ρ l₁ Y V Ob Bd Sd) (a : ℝ) :
    IsDecayingPart κ ρ l₁ Y V (fun l ζ V' => a * Ob l ζ V') (fun ζ => |a| * Bd ζ)
      (fun b ζ => |a| * Sd b ζ) := by
  have hmul : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (i : ℕ), i + k ≤ 6 →
      ∀ p ∈ scaleBallSet F ρ,
      scaleJet (scaledObservable (fun l ζ V' => a * Ob l ζ V') V c X) (unitParams k) i p =
        a * scaleJet (scaledObservable Ob V c X) (unitParams k) i p :=
    fun c X i hik p hp => scaleJet_const_mul a (unitParams _) (isOpen_scaleBallSet ρ) (h.smooth _ c X) i hik p hp
  refine ⟨fun k c X p hp => contDiffAt_const.mul (h.smooth k c X p hp), ?_, ?_⟩
  · intro k i c X l ζ hki hX hl hl₁ hb
    have hp := mem_scaleBallSet hl hb
    rw [scaleDeriv_eq_scaleJet, hmul c X i (by have := controlledOrder_le hki; omega) _ hp, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.deriv_le k i c X l ζ hki hX hl hl₁ hb) (abs_nonneg _)
  · intro k i c X l ζ b e hki hX hl hl₁ hb he
    have hp := mem_scaleBallSet hl hb
    have hik := controlledOrder_le hki
    have hev : (fun ζ' => scaleDeriv (fun l ζ V' => a * Ob l ζ V') V c X i ζ' l) =ᶠ[𝓝 ζ]
        fun ζ' => a * scaleDeriv Ob V c X i ζ' l := by
      filter_upwards [eventually_mem_scaleBallSet hp] with ζ' hζ'
      exact hmul c X i (by omega) _ hζ'
    have d₁ := differentiableAt_scaleDeriv (h.smooth k c X) hik hp
    have e1 : bondPartialDeriv (fun ζ' => scaleDeriv (fun l ζ V' => a * Ob l ζ V') V c X i ζ' l) b ζ e =
        a * bondPartialDeriv (fun ζ' => scaleDeriv Ob V c X i ζ' l) b ζ e := by
      simp only [bondPartialDeriv]
      rw [hev.fderiv_eq, fderiv_const_mul d₁]
      rfl
    rw [e1, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.partial_le k i c X l ζ b e hki hX hl hl₁ hb he) (abs_nonneg _)
theorem isDecayingPart_zero : IsDecayingPart κ ρ l₁ Y V (fun _ _ _ => 0) (fun _ => 0) (fun _ _ => 0) := by
  have hj : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), ∀ p ∈ scaleBallSet F ρ,
      ContDiffAt ℝ (6 : ℕ) (scaledObservable (fun (_ : ℝ) (_ : StepVariable (finiteCells F)) (_ : F.GaugeField F.top) =>
        (0 : ℝ)) V c X) (p, 0) := fun k c X p _ => contDiffAt_const
  have hz : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (i : ℕ), i + k ≤ 6 →
      ∀ p ∈ scaleBallSet F ρ,
      scaleJet (scaledObservable (fun (_ : ℝ) (_ : StepVariable (finiteCells F)) (_ : F.GaugeField F.top) => (0 : ℝ))
        V c X) (unitParams k) i p = 0 := by
    intro k c X i hik p hp
    have h1 := scaleJet_const_mul 0 (unitParams k) (isOpen_scaleBallSet ρ) (hj k c X) i hik p hp
    rw [zero_mul] at h1
    have e : (fun q => (0 : ℝ) * scaledObservable (fun (_ : ℝ) (_ : StepVariable (finiteCells F))
        (_ : F.GaugeField F.top) => (0 : ℝ)) V c X q) =
        scaledObservable (fun (_ : ℝ) (_ : StepVariable (finiteCells F)) (_ : F.GaugeField F.top) => (0 : ℝ)) V c X := by
      funext q; simp [scaledObservable]
    rwa [e] at h1
  refine ⟨hj, ?_, ?_⟩
  · intro k i c X l ζ hki hX hl hl₁ hb
    rw [scaleDeriv_eq_scaleJet, hz c X i (by have := controlledOrder_le hki; omega) _ (mem_scaleBallSet hl hb)]
    simp
  · intro k i c X l ζ b e hki hX hl hl₁ hb he
    have hp := mem_scaleBallSet hl hb
    have hik := controlledOrder_le hki
    have hev : (fun ζ' => scaleDeriv (fun (_ : ℝ) (_ : StepVariable (finiteCells F)) (_ : F.GaugeField F.top) => (0 : ℝ))
        V c X i ζ' l) =ᶠ[𝓝 ζ] fun _ => 0 := by
      filter_upwards [eventually_mem_scaleBallSet hp] with ζ' hζ'
      exact hz c X i (by omega) _ hζ'
    simp only [bondPartialDeriv]
    rw [hev.fderiv_eq]
    simp
theorem IsDecayingPart.sum {ι : Type} (s : Finset ι) {Ob : ι → ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {Bd : ι → StepVariable (finiteCells F) → ℝ}
    {Sd : ι → ↥(chordBonds (finiteCells F)) → StepVariable (finiteCells F) → ℝ}
    (h : ∀ i ∈ s, IsDecayingPart κ ρ l₁ Y V (Ob i) (Bd i) (Sd i)) :
    IsDecayingPart κ ρ l₁ Y V (fun l ζ V' => ∑ i ∈ s, Ob i l ζ V') (fun ζ => ∑ i ∈ s, Bd i ζ)
      (fun b ζ => ∑ i ∈ s, Sd i b ζ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isDecayingPart_zero
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have h3 := h1.add h2
    simpa only [Finset.sum_insert ha] using h3
def ExtendsToClosedBalls (ρ l₁ : ℝ) (V : F.GaugeField F.top) (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) : Prop :=
  ∃ G : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) → ℝ,
    (∀ᶠ τ : Fin k → ℝ in 𝓝 0, ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l → l ≤ l₁ → MemScaledBalls ρ l ζ →
      G ((l, ζ), τ) = Ob l ζ (leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X τ) V)) ∧
    ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l → l ≤ l₁ → (∀ b, l * ‖ζ b‖ ≤ ρ) →
      ContDiffAt ℝ (6 : ℕ) G ((l, ζ), 0)
theorem ExtendsToClosedBalls.of_contDiffAt {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {k : ℕ}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    (h : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l → l ≤ l₁ → (∀ b, l * ‖ζ b‖ ≤ ρ) →
      ContDiffAt ℝ (6 : ℕ) (scaledObservable Ob V c X) ((l, ζ), 0)) : ExtendsToClosedBalls ρ l₁ V Ob c X :=
  ⟨scaledObservable Ob V c X, Eventually.of_forall fun _ _ _ _ _ _ => rfl, h⟩
theorem ExtendsToClosedBalls.add {Ob₁ Ob₂ : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {k : ℕ}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} (h₁ : ExtendsToClosedBalls ρ l₁ V Ob₁ c X)
    (h₂ : ExtendsToClosedBalls ρ l₁ V Ob₂ c X) :
    ExtendsToClosedBalls ρ l₁ V (fun l ζ V' => Ob₁ l ζ V' + Ob₂ l ζ V') c X := by
  obtain ⟨G₁, a₁, b₁⟩ := h₁
  obtain ⟨G₂, a₂, b₂⟩ := h₂
  refine ⟨fun q => G₁ q + G₂ q, ?_, fun l ζ hl hl₁ hb => (b₁ l ζ hl hl₁ hb).add (b₂ l ζ hl hl₁ hb)⟩
  filter_upwards [a₁, a₂] with τ e₁ e₂ l ζ hl hl₁ hb
  rw [e₁ l ζ hl hl₁ hb, e₂ l ζ hl hl₁ hb]
theorem ExtendsToClosedBalls.const_mul {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {k : ℕ}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} (h : ExtendsToClosedBalls ρ l₁ V Ob c X)
    (a : ℝ) : ExtendsToClosedBalls ρ l₁ V (fun l ζ V' => a * Ob l ζ V') c X := by
  obtain ⟨G, e, b⟩ := h
  refine ⟨fun q => a * G q, ?_, fun l ζ hl hl₁ hb => contDiffAt_const.mul (b l ζ hl hl₁ hb)⟩
  filter_upwards [e] with τ e₁ l ζ hl hl₁ hb
  rw [e₁ l ζ hl hl₁ hb]
theorem ExtendsToClosedBalls.sum {ι : Type} (s : Finset ι)
    {Ob : ι → ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {k : ℕ}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    (h : ∀ i ∈ s, ExtendsToClosedBalls ρ l₁ V (Ob i) c X) :
    ExtendsToClosedBalls ρ l₁ V (fun l ζ V' => ∑ i ∈ s, Ob i l ζ V') c X := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ExtendsToClosedBalls.of_contDiffAt fun _ _ _ _ _ => contDiffAt_const
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have h3 := h1.add h2
    simpa only [Finset.sum_insert ha] using h3
theorem isSmoothObservable_of_decayingPart {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {Bd : StepVariable (finiteCells F) → ℝ}
    {Sd : ↥(chordBonds (finiteCells F)) → StepVariable (finiteCells F) → ℝ} {K : ℝ}
    (h : IsDecayingPart κ ρ l₁ Y V Ob Bd Sd)
    (heven : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)) (V' : F.GaugeField F.top), Ob (-l) (-ζ) V' = Ob l ζ V')
    (hB : ∀ ζ, Bd ζ ≤ K * (1 + localWeight κ Y ζ) ^ 7)
    (hcl : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      ExtendsToClosedBalls ρ l₁ V Ob c X)
    (hS : ∀ b ζ, Sd b ζ ≤ K * (1 + localWeight κ Y ζ) ^ 7) :
    IsSmoothObservable κ ρ l₁ K Y V Ob := by
  refine ⟨heven, ?_, hcl, ?_, ?_, ?_⟩
  · intro l ζ k c X hb
    have hp : (l, ζ) ∈ scaleBallSet F ρ := fun b => hb b
    exact h.smooth k c X (l, ζ) hp
  · intro k i c X l ζ hki hX hl hl₁ hb
    exact (h.deriv_le k i c X l ζ hki hX hl hl₁ hb).trans
      (mul_le_mul_of_nonneg_right (hB ζ) (Real.exp_pos _).le)
  · intro k i c X l ζ b e hki hX hl hl₁ hb he
    exact (h.partial_le k i c X l ζ b e hki hX hl hl₁ hb he).trans
      (mul_le_mul_of_nonneg_right (hS b ζ) (Real.exp_pos _).le)
  · intro k i c X R hki
    have hik := controlledOrder_le hki
    intro q hq
    obtain ⟨h0, -, hb, -⟩ := hq
    have hp : q ∈ scaleBallSet F ρ := fun b => by
      have := hb b
      simpa [abs_of_nonneg h0] using this
    have h1 := (contDiffAt_scaleJet (unitParams k) (isOpen_scaleBallSet ρ) (h.smooth k c X) i 1 hik q hp)
    exact h1.continuousAt.continuousWithinAt
end
section
open Set Filter Topology
open YangMills.Construction.BlockAverages
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.ScaledVariables
variable {F : BlockFrame}
variable {Zp : Type} [NormedAddCommGroup Zp] [NormedSpace ℝ Zp]
def rayObservable (G : Zp → F.GaugeField F.top → ℝ) (ray : StepVariable (finiteCells F) → Zp)
    (m : StepVariable (finiteCells F) → ℝ) : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  fun l ζ V' => m ζ * G (l • ray ζ) V'
abbrev translatedJet (G : Zp → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) : Zp → ℝ :=
  partialJetRight (translatedObservable G V c X) 0 (unitParams k)
variable {κ ρ l₁ : ℝ} {Y : F.Cell} {V : F.GaugeField F.top}
theorem contDiffAt_rayObservable {G : Zp → F.GaugeField F.top → ℝ} {ray : StepVariable (finiteCells F) → Zp}
    {m : StepVariable (finiteCells F) → ℝ} (hray : ContDiff ℝ (6 : ℕ) ray) (hm : ContDiff ℝ (6 : ℕ) m)
    {S : Set Zp} (hS : ∀ p ∈ scaleBallSet F ρ, p.1 • ray p.2 ∈ S)
    (hG : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), ∀ x ∈ S,
      ContDiffAt ℝ (6 : ℕ) (translatedObservable G V c X) (x, 0))
    (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (p : ℝ × StepVariable (finiteCells F))
    (hp : p ∈ scaleBallSet F ρ) : ContDiffAt ℝ (6 : ℕ) (scaledObservable (rayObservable G ray m) V c X) (p, 0) := by
  have h1 : ContDiffAt ℝ (6 : ℕ)
      (fun q : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) => m q.1.2) (p, 0) :=
    (hm.comp (contDiff_snd.comp contDiff_fst)).contDiffAt
  have h2 : ContDiff ℝ (6 : ℕ) (fun q : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) =>
      (q.1.1 • ray q.1.2, q.2)) :=
    ((contDiff_fst.comp contDiff_fst).smul (hray.comp (contDiff_snd.comp contDiff_fst))).prodMk contDiff_snd
  have h3 := ContDiffAt.comp (p, (0 : Fin k → ℝ)) (g := translatedObservable G V c X) (hG k c X _ (hS p hp))
    h2.contDiffAt
  exact h1.mul h3
theorem contDiffAt_rayObservable_of_mem {G : Zp → F.GaugeField F.top → ℝ} {ray : StepVariable (finiteCells F) → Zp}
    {m : StepVariable (finiteCells F) → ℝ} (hray : ContDiff ℝ (6 : ℕ) ray) (hm : ContDiff ℝ (6 : ℕ) m)
    {S : Set Zp} (hG : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), ∀ x ∈ S,
      ContDiffAt ℝ (6 : ℕ) (translatedObservable G V c X) (x, 0))
    (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (p : ℝ × StepVariable (finiteCells F))
    (hp : p.1 • ray p.2 ∈ S) : ContDiffAt ℝ (6 : ℕ) (scaledObservable (rayObservable G ray m) V c X) (p, 0) := by
  have h1 : ContDiffAt ℝ (6 : ℕ)
      (fun q : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) => m q.1.2) (p, 0) :=
    (hm.comp (contDiff_snd.comp contDiff_fst)).contDiffAt
  have h2 : ContDiff ℝ (6 : ℕ) (fun q : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) =>
      (q.1.1 • ray q.1.2, q.2)) :=
    ((contDiff_fst.comp contDiff_fst).smul (hray.comp (contDiff_snd.comp contDiff_fst))).prodMk contDiff_snd
  have h3 := ContDiffAt.comp (p, (0 : Fin k → ℝ)) (g := translatedObservable G V c X) (hG k c X _ hp) h2.contDiffAt
  exact h1.mul h3
theorem scaleDeriv_rayObservable {G : Zp → F.GaugeField F.top → ℝ} {ray : StepVariable (finiteCells F) → Zp}
    {m : StepVariable (finiteCells F) → ℝ} {S : Set Zp} (hS : ∀ p ∈ scaleBallSet F ρ, p.1 • ray p.2 ∈ S)
    (hG : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), ∀ x ∈ S,
      ContDiffAt ℝ (6 : ℕ) (translatedObservable G V c X) (x, 0))
    {k i : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hik : i + k ≤ 6) {l : ℝ}
    {ζ : StepVariable (finiteCells F)} (hp : (l, ζ) ∈ scaleBallSet F ρ) :
    scaleDeriv (rayObservable G ray m) V c X i ζ l =
      m ζ * iteratedFDeriv ℝ i (translatedJet G V c X) (l • ray ζ) fun _ => ray ζ := by
  have hnear : ∀ᶠ l' in 𝓝 l, (l', ζ) ∈ scaleBallSet F ρ := by
    have h2 : Tendsto (fun l' : ℝ => (l', ζ)) (𝓝 l) (𝓝 (l, ζ)) := (Continuous.prodMk_left ζ).tendsto l
    exact h2.eventually ((isOpen_scaleBallSet ρ).mem_nhds hp)
  have hev : (fun l' => bondDeriv (rayObservable G ray m l' ζ) V c X) =ᶠ[𝓝 l]
      fun l' => m ζ * translatedJet G V c X (l' • ray ζ) := by
    filter_upwards [hnear] with l' hl'
    have hs : ContDiffAt ℝ k (fun q => translatedObservable G V c X (l' • ray ζ, q)) 0 :=
      (contDiffAt_slice_right (hG k c X _ (hS _ hl'))).of_le (by exact_mod_cast (by omega : k ≤ 6))
    have := iteratedFDeriv_const_smul_apply' (a := m ζ) hs
    exact congrArg (fun T => T (unitParams k)) this
  simp only [scaleDeriv]
  rw [hev.iteratedDeriv_eq, iteratedDeriv_const_mul_field]
  congr 1
  exact iteratedDeriv_along_ray (n := i) (ray ζ) l (contDiffAt_partialJetRight (hG k c X _ (hS _ hp)) (by omega) _) le_rfl
theorem partial_scaleDeriv_rayObservable_le {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {G : Zp → F.GaugeField F.top → ℝ} {ray : StepVariable (finiteCells F) → Zp}
    {m : StepVariable (finiteCells F) → ℝ} (hray : ContDiff ℝ (6 : ℕ) ray) (hm : ContDiff ℝ (6 : ℕ) m)
    {S : Set Zp} (hS : ∀ p ∈ scaleBallSet F ρ, p.1 • ray p.2 ∈ S)
    (hG : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), ∀ x ∈ S,
      ContDiffAt ℝ (6 : ℕ) (translatedObservable G V c X) (x, 0))
    (Lr : StepVariable (finiteCells F) →L[ℝ] Zp)
    (hline : ∀ (ζ δ : StepVariable (finiteCells F)) (s : ℝ), ray (ζ + s • δ) = ray ζ + s • Lr δ)
    (φ : Idx → Zp →L[ℝ] ℝ) (ε : Idx → Zp) (hφ : ∀ z, z = ∑ α, φ α z • ε α)
    (w : Idx → ℝ) (hw : ∀ α, 0 ≤ w α)
    {k i : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hik : 1 + i + k ≤ 6) {l : ℝ}
    {ζ : StepVariable (finiteCells F)} (hp : (l, ζ) ∈ scaleBallSet F ρ)
    (δ : StepVariable (finiteCells F)) (B : ℝ) (hB : 0 ≤ B)
    (h0 : fderiv ℝ m ζ δ ≠ 0 → ∀ σ : Fin i → Idx,
      |iteratedFDeriv ℝ i (translatedJet G V c X) (l • ray ζ) fun j => ε (σ j)| ≤ B * ∏ j, w (σ j))
    (hb : ∀ (σ : Fin i → Idx) (j : Fin i), φ (σ j) (Lr δ) ≠ 0 →
      |iteratedFDeriv ℝ i (translatedJet G V c X) (l • ray ζ) fun j => ε (σ j)| ≤
        B * ∏ j' ∈ Finset.univ.erase j, w (σ j'))
    (hc : ∀ σ : Fin i → Idx,
      |iteratedFDeriv ℝ (i + 1) (translatedJet G V c X) (l • ray ζ) (Fin.cons (Lr δ) fun j => ε (σ j))| ≤
        B * ∏ j, w (σ j)) :
    |fderiv ℝ (fun ζ' => scaleDeriv (rayObservable G ray m) V c X i ζ' l) ζ δ| ≤
      |fderiv ℝ m ζ δ| * (B * (∑ α, |φ α (ray ζ)| * w α) ^ i) +
        |m ζ| * (B * ((i : ℝ) * ((∑ α, |φ α (Lr δ)|) * (∑ α, |φ α (ray ζ)| * w α) ^ (i - 1)) +
          |l| * (∑ α, |φ α (ray ζ)| * w α) ^ i)) := by
  set R := translatedJet G V c X with hRdef
  have hR : ContDiffAt ℝ (i + 1 : ℕ) R (l • ray ζ) :=
    contDiffAt_partialJetRight (hG k c X _ (hS _ hp)) (by omega) _
  set D : ℝ → ℝ := fun s => iteratedFDeriv ℝ i R (l • (ray ζ + s • Lr δ)) fun _ => ray ζ + s • Lr δ with hD
  have hD0 : D 0 = iteratedFDeriv ℝ i R (l • ray ζ) fun _ => ray ζ := by simp [hD]
  obtain ⟨d₀, hd₀⟩ : ∃ d, HasDerivAt D d 0 := ⟨_, hasDerivAt_diag_line φ ε hφ l (ray ζ) (Lr δ) hR⟩
  have hev : (fun ζ' => scaleDeriv (rayObservable G ray m) V c X i ζ' l) =ᶠ[𝓝 ζ]
      fun ζ' => m ζ' * iteratedFDeriv ℝ i R (l • ray ζ') fun _ => ray ζ' := by
    filter_upwards [eventually_mem_scaleBallSet hp] with ζ' h
    exact scaleDeriv_rayObservable hS hG c X (by omega) h
  have hd := differentiableAt_scaleDeriv (contDiffAt_rayObservable hray hm hS hG k c X) hik hp
  have hline₀ : HasDerivAt (fun s : ℝ => ζ + s • δ) δ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add ζ
  have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline₀ (by simp)
  have htend : Tendsto (fun s : ℝ => ζ + s • δ) (𝓝 0) (𝓝 ζ) := by
    have := hline₀.continuousAt.tendsto
    simpa using this
  have hm1 : HasDerivAt (fun s : ℝ => m (ζ + s • δ)) (fderiv ℝ m ζ δ) 0 :=
    ((hm.differentiable (by norm_num)) ζ).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline₀ (by simp)
  have h3 : HasDerivAt (fun s : ℝ => m (ζ + s • δ) * D s)
      (fderiv ℝ m ζ δ * D 0 + m (ζ + (0 : ℝ) • δ) * d₀) 0 := hm1.mul hd₀
  have h4 : (fun s : ℝ => (fun ζ' => scaleDeriv (rayObservable G ray m) V c X i ζ' l) (ζ + s • δ)) =ᶠ[𝓝 0]
      fun s : ℝ => m (ζ + s • δ) * D s := by
    filter_upwards [htend.eventually hev] with s hs
    rw [hs]
    simp only [hD, hline]
  have h5 := (h3.congr_of_eventuallyEq h4).unique h1
  have h6 := diag_line_deriv_bound φ ε hφ l (ray ζ) (Lr δ) hR w hw B hB hb hc d₀ hd₀
  rw [← h5]
  simp only [zero_smul, add_zero]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    by_cases hz : fderiv ℝ m ζ δ = 0
    · simp [hz]
    · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [hD0]
      exact multilinear_diag_bound _ (fun α z => φ α z) ε (ray ζ) (hφ _) w B hB (h0 hz)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h6 (abs_nonneg _)
theorem decayingPart_of_ray {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {G : Zp → F.GaugeField F.top → ℝ} {ray : StepVariable (finiteCells F) → Zp}
    {m : StepVariable (finiteCells F) → ℝ} (hray : ContDiff ℝ (6 : ℕ) ray) (hm : ContDiff ℝ (6 : ℕ) m)
    {S : Set Zp} (hS : ∀ p ∈ scaleBallSet F ρ, p.1 • ray p.2 ∈ S)
    (hG : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), ∀ x ∈ S,
      ContDiffAt ℝ (6 : ℕ) (translatedObservable G V c X) (x, 0))
    (Lr : StepVariable (finiteCells F) →L[ℝ] Zp)
    (hline : ∀ (ζ δ : StepVariable (finiteCells F)) (s : ℝ), ray (ζ + s • δ) = ray ζ + s • Lr δ)
    (φ : Idx → Zp →L[ℝ] ℝ) (ε : Idx → Zp) (hφ : ∀ z, z = ∑ α, φ α z • ε α)
    (w : Idx → ℝ) (hw : ∀ α, 0 ≤ w α) (B Ad : ℝ) (hB : 0 ≤ B) (hl₁ : l₁ ≤ 1)
    (hAd : ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector), ‖e‖ = 1 →
      ∑ α, |φ α (Lr (bondVariation b e))| ≤ Ad)
    (Md : ↥(chordBonds (finiteCells F)) → StepVariable (finiteCells F) → ℝ)
    (hMd : ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector) (ζ : StepVariable (finiteCells F)),
      ‖e‖ = 1 → |fderiv ℝ m ζ (bondVariation b e)| ≤ Md b ζ)
    (K0 : ∀ (k i : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (l : ℝ)
      (ζ : StepVariable (finiteCells F)) (σ : Fin i → Idx), IsControlledOrder k i → AreUnitVectors X → 0 < l →
      l ≤ l₁ → MemScaledBalls ρ l ζ →
      |iteratedFDeriv ℝ i (translatedJet G V c X) (l • ray ζ) fun j => ε (σ j)| ≤
        B * (∏ j, w (σ j)) * Real.exp (-(2 ^ 4 * κ * bondSpan Y c)))
    (K1 : ∀ (k i : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (l : ℝ)
      (ζ : StepVariable (finiteCells F)) (σ : Fin i → Idx) (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
      IsControlledOrder k i → AreUnitVectors X → 0 < l → l ≤ l₁ → MemScaledBalls ρ l ζ → ‖e‖ = 1 →
      fderiv ℝ m ζ (bondVariation b e) ≠ 0 →
      |iteratedFDeriv ℝ i (translatedJet G V c X) (l • ray ζ) fun j => ε (σ j)| ≤
        B * (∏ j, w (σ j)) * Real.exp (-(2 ^ 4 * κ * bondSpan Y (Fin.cons (enclosingCell b.1.1, 0) c :
          Fin (k + 1) → F.Site F.top × Fin 4))))
    (K2 : ∀ (k i : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (l : ℝ)
      (ζ : StepVariable (finiteCells F)) (σ : Fin i → Idx) (b : ↥(chordBonds (finiteCells F))) (e : BondVector)
      (j : Fin i), IsControlledOrder k i → AreUnitVectors X → 0 < l → l ≤ l₁ → MemScaledBalls ρ l ζ → ‖e‖ = 1 →
      φ (σ j) (Lr (bondVariation b e)) ≠ 0 →
      |iteratedFDeriv ℝ i (translatedJet G V c X) (l • ray ζ) fun j => ε (σ j)| ≤
        B * (∏ j' ∈ Finset.univ.erase j, w (σ j')) *
          Real.exp (-(2 ^ 4 * κ * bondSpan Y (Fin.cons (enclosingCell b.1.1, 0) c :
            Fin (k + 1) → F.Site F.top × Fin 4))))
    (K3 : ∀ (k i : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (l : ℝ)
      (ζ : StepVariable (finiteCells F)) (σ : Fin i → Idx) (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
      IsControlledOrder k i → AreUnitVectors X → 0 < l → l ≤ l₁ → MemScaledBalls ρ l ζ → ‖e‖ = 1 →
      |iteratedFDeriv ℝ (i + 1) (translatedJet G V c X) (l • ray ζ)
          (Fin.cons (Lr (bondVariation b e)) fun j => ε (σ j))| ≤
        B * (∏ j, w (σ j)) * Real.exp (-(2 ^ 4 * κ * bondSpan Y (Fin.cons (enclosingCell b.1.1, 0) c :
          Fin (k + 1) → F.Site F.top × Fin 4)))) :
    IsDecayingPart κ ρ l₁ Y V (rayObservable G ray m)
      (fun ζ => |m ζ| * B * (1 + ∑ α, |φ α (ray ζ)| * w α) ^ 3)
      (fun b ζ => (Md b ζ + |m ζ| * (3 * Ad + 1)) * B * (1 + ∑ α, |φ α (ray ζ)| * w α) ^ 3) := by
  have hA0 : ∀ ζ, 0 ≤ ∑ α, |φ α (ray ζ)| * w α := fun ζ =>
    Finset.sum_nonneg fun α _ => mul_nonneg (abs_nonneg _) (hw α)
  have hpow : ∀ (ζ : StepVariable (finiteCells F)) (i : ℕ), i ≤ 3 →
      (∑ α, |φ α (ray ζ)| * w α) ^ i ≤ (1 + ∑ α, |φ α (ray ζ)| * w α) ^ 3 := by
    intro ζ i hi
    calc (∑ α, |φ α (ray ζ)| * w α) ^ i ≤ (1 + ∑ α, |φ α (ray ζ)| * w α) ^ i :=
          pow_le_pow_left₀ (hA0 ζ) (by linarith) i
      _ ≤ _ := pow_le_pow_right₀ (by linarith [hA0 ζ]) hi
  have hi3 : ∀ {k i : ℕ}, IsControlledOrder k i → i ≤ 3 := by
    intro k i h
    rcases h with h | h <;> omega
  refine ⟨contDiffAt_rayObservable hray hm hS hG, ?_, ?_⟩
  · intro k i c X l ζ hki hX hl hl' hb
    have hp := mem_scaleBallSet hl hb
    have hik := controlledOrder_le hki
    rw [scaleDeriv_rayObservable hS hG c X (by omega) hp, abs_mul]
    set E := Real.exp (-(2 ^ 4 * κ * bondSpan Y c)) with hE
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have h1 := multilinear_diag_bound (iteratedFDeriv ℝ i (translatedJet G V c X) (l • ray ζ)) (fun α z => φ α z) ε
      (ray ζ) (hφ _) w (B * E) (mul_nonneg hB hE0) (fun σ => by
        refine (K0 k i c X l ζ σ hki hX hl hl' hb).trans (le_of_eq ?_)
        ring)
    calc |m ζ| * |iteratedFDeriv ℝ i (translatedJet G V c X) (l • ray ζ) fun _ => ray ζ|
        ≤ |m ζ| * (B * E * (∑ α, |φ α (ray ζ)| * w α) ^ i) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ |m ζ| * (B * E * (1 + ∑ α, |φ α (ray ζ)| * w α) ^ 3) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hpow ζ i (hi3 hki)) (mul_nonneg hB hE0)) (abs_nonneg _)
      _ = _ := by ring
  · intro k i c X l ζ b e hki hX hl hl' hb he
    have hp := mem_scaleBallSet hl hb
    have hik := controlledOrder_le hki
    set E := Real.exp (-(2 ^ 4 * κ * bondSpan Y (Fin.cons (enclosingCell b.1.1, 0) c :
      Fin (k + 1) → F.Site F.top × Fin 4))) with hE
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have h1 := partial_scaleDeriv_rayObservable_le hray hm hS hG Lr hline φ ε hφ w hw c X hik hp
      (bondVariation b e) (B * E) (mul_nonneg hB hE0)
      (fun hz σ => (K1 k i c X l ζ σ b e hki hX hl hl' hb he hz).trans (le_of_eq (by ring)))
      (fun σ j hz => (K2 k i c X l ζ σ b e j hki hX hl hl' hb he hz).trans (le_of_eq (by ring)))
      (fun σ => (K3 k i c X l ζ σ b e hki hX hl hl' hb he).trans (le_of_eq (by ring)))
    simp only [bondPartialDeriv]
    refine h1.trans ?_
    set A := ∑ α, |φ α (ray ζ)| * w α with hA
    set P3 := (1 + A) ^ 3 with hP3
    have hP0 : 0 ≤ P3 := by have := hA0 ζ; positivity
    have hAi : A ^ i ≤ P3 := hpow ζ i (hi3 hki)
    have hAi1 : A ^ (i - 1) ≤ P3 := hpow ζ (i - 1) (by have := hi3 hki; omega)
    have hAi0 : 0 ≤ A ^ i := pow_nonneg (hA0 ζ) _
    have hAi10 : 0 ≤ A ^ (i - 1) := pow_nonneg (hA0 ζ) _
    have hAd' := hAd b e he
    have hAd0 : 0 ≤ ∑ α, |φ α (Lr (bondVariation b e))| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hAdd : 0 ≤ Ad := hAd0.trans hAd'
    have hlabs : |l| ≤ 1 := by rw [abs_of_pos hl]; linarith
    have hi : (i : ℝ) ≤ 3 := by exact_mod_cast hi3 hki
    have hBE : 0 ≤ B * E := mul_nonneg hB hE0
    have hM := hMd b e ζ he
    have hM0 : 0 ≤ Md b ζ := (abs_nonneg _).trans hM
    have t1 : |fderiv ℝ m ζ (bondVariation b e)| * (B * E * A ^ i) ≤ Md b ζ * (B * E * P3) :=
      mul_le_mul hM (mul_le_mul_of_nonneg_left hAi hBE) (mul_nonneg hBE hAi0) hM0
    have t2 : (i : ℝ) * ((∑ α, |φ α (Lr (bondVariation b e))|) * A ^ (i - 1)) + |l| * A ^ i ≤
        (3 * Ad + 1) * P3 := by
      have u1 : (i : ℝ) * ((∑ α, |φ α (Lr (bondVariation b e))|) * A ^ (i - 1)) ≤ 3 * (Ad * P3) :=
        mul_le_mul hi (mul_le_mul hAd' hAi1 hAi10 hAdd) (mul_nonneg hAd0 hAi10) (by norm_num)
      have u2 : |l| * A ^ i ≤ 1 * P3 := mul_le_mul hlabs hAi hAi0 (by norm_num)
      nlinarith
    have t3 : |m ζ| * (B * E * ((i : ℝ) * ((∑ α, |φ α (Lr (bondVariation b e))|) * A ^ (i - 1)) + |l| * A ^ i)) ≤
        |m ζ| * (B * E * ((3 * Ad + 1) * P3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left t2 hBE) (abs_nonneg _)
    calc _ ≤ Md b ζ * (B * E * P3) + |m ζ| * (B * E * ((3 * Ad + 1) * P3)) := add_le_add t1 t3
      _ = _ := by ring
end
section
open Set Filter Topology
open YangMills.Construction.BlockAverages
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.ScaledVariables
variable {F : BlockFrame}
theorem cellSupDist_le_diameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
theorem cellSetDiameter_mono {P Q : Finset F.Cell} (h : P ⊆ Q) : cellSetDiameter P ≤ cellSetDiameter Q := by apply _root_.YangMills.SharedProofs.p30422 <;> assumption
theorem bondSpan_le_diameter {Y : F.Cell} {k : ℕ} {c : Fin k → F.Site F.top × Fin 4} {P : Finset F.Cell}
    (hY : Y ∈ P) (hc : ∀ l, (c l).1 ∈ P) : bondSpan Y c ≤ cellSetDiameter P :=
  max_le (Finset.sup_le fun l _ => cellSupDist_le_diameter hY (hc l))
    (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => cellSupDist_le_diameter (hc l) (hc l'))
theorem exp_diameter_le {ι : Type} {κ r : ℝ} {S d₀ s₀ : ℕ} (hκ : 0 < κ) (I : Finset ι) (d : ι → ℕ)
    (hd : ∀ i ∈ I, d i ≤ S) (hd₀ : d₀ ≤ S) (hs₀ : s₀ ≤ S) (hr : ((I.card : ℝ) + 2) * (2 ^ 4 * κ) ≤ r) :
    Real.exp (-(r * S)) ≤ Real.exp (-(2 ^ 4 * κ * d₀)) * (∏ i ∈ I, Real.exp (-(2 ^ 4 * κ * d i))) *
      Real.exp (-(2 ^ 4 * κ * s₀)) := by
  rw [← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hc : 0 < 2 ^ 4 * κ := by positivity
  have h1 : ∑ i ∈ I, (d i : ℝ) ≤ (I.card : ℝ) * S := by
    calc ∑ i ∈ I, (d i : ℝ) ≤ ∑ _i ∈ I, (S : ℝ) :=
          Finset.sum_le_sum fun i hi => by exact_mod_cast hd i hi
      _ = _ := by simp
  have h2 : (d₀ : ℝ) ≤ S := by exact_mod_cast hd₀
  have h3 : (s₀ : ℝ) ≤ S := by exact_mod_cast hs₀
  have h4 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have h5 : 2 ^ 4 * κ * ((d₀ : ℝ) + (∑ i ∈ I, (d i : ℝ)) + s₀) ≤ r * S := by
    calc 2 ^ 4 * κ * ((d₀ : ℝ) + (∑ i ∈ I, (d i : ℝ)) + s₀)
        ≤ 2 ^ 4 * κ * (((I.card : ℝ) + 2) * S) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hc.le
      _ = (((I.card : ℝ) + 2) * (2 ^ 4 * κ)) * S := by ring
      _ ≤ r * S := mul_le_mul_of_nonneg_right hr h4
  have h6 : ∑ i ∈ I, -(2 ^ 4 * κ * (d i : ℝ)) = -(2 ^ 4 * κ * ∑ i ∈ I, (d i : ℝ)) := by
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  rw [h6]
  nlinarith
structure IsDecayingKernel (V : F.GaugeField F.top) (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (B r : ℝ) (P : Finset F.Cell) (S : Set (StepVariable (finiteCells F))) (n : ℕ) : Prop where
  smooth : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), ∀ η ∈ S,
    ContDiffAt ℝ (n : ℕ) (translatedObservable G V c X) (η, 0)
  deriv_le : ∀ η ∈ S, ∀ (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions),
    l + j ≤ n → (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
    |jointMixedDeriv G η V b u c X| ≤
      B * Real.exp (-(r * cellSetDiameter (P ∪ chordBondCells b ∪ topBondCells c)))
def coordDecay (κ : ℝ) (Y : F.Cell) (α : ChordCoord F) : ℝ :=
  Real.exp (-(2 ^ 4 * κ * cellSupDist (enclosingCell α.1.1.1) Y))
variable {κ ρ l₁ : ℝ} {Y : F.Cell} {V : F.GaugeField F.top}
theorem IsDecayingKernel.deriv_le_prod {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {B r : ℝ}
    {P : Finset F.Cell} {S : Set (StepVariable (finiteCells F))} {n : ℕ}
    (hk : IsDecayingKernel V G B r P S n) (hB : 0 ≤ B) (hκ : 0 < κ) {ι : Type} {η : StepVariable (finiteCells F)}
    (hη : η ∈ S) {l j : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions)
    (hlj : l + j ≤ n) (hu : ∀ i, ‖u i‖ = 1) (hX : AreUnitVectors X) (I : Finset ι) (d : ι → ℕ) {d₀ s₀ : ℕ}
    (hd : ∀ i ∈ I, d i ≤ cellSetDiameter (P ∪ chordBondCells b ∪ topBondCells c))
    (hd₀ : d₀ ≤ cellSetDiameter P)
    (hs₀ : s₀ ≤ cellSetDiameter (P ∪ chordBondCells b ∪ topBondCells c))
    (hr : ((I.card : ℝ) + 2) * (2 ^ 4 * κ) ≤ r) :
    |jointMixedDeriv G η V b u c X| ≤ B * Real.exp (-(2 ^ 4 * κ * d₀)) *
      (∏ i ∈ I, Real.exp (-(2 ^ 4 * κ * d i))) * Real.exp (-(2 ^ 4 * κ * s₀)) := by
  refine (hk.deriv_le η hη l j b u c X hlj hu hX).trans ?_
  have h1 := exp_diameter_le (S := cellSetDiameter (P ∪ chordBondCells b ∪ topBondCells c)) hκ I d hd
    (hd₀.trans (cellSetDiameter_mono (fun x hx => by simp [hx]))) hs₀ hr
  calc _ ≤ B * _ := mul_le_mul_of_nonneg_left h1 hB
    _ = _ := by ring
theorem mem_chordBondCells {l : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (i : Fin l) :
    enclosingCell (b i).1.1 ∈ chordBondCells b := by
  simp only [chordBondCells, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨i, rfl⟩
theorem mem_topBondCells {j : ℕ} (c : Fin j → F.Site F.top × Fin 4) (i : Fin j) :
    (c i).1 ∈ topBondCells c := by
  simp only [topBondCells, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨i, rfl⟩
theorem sum_abs_chordCoord_le_three (b : ↥(chordBonds (finiteCells F))) (e : BondVector) (he : ‖e‖ = 1) :
    ∑ α : ChordCoord F, |chordCoord α (bondVariation b e)| ≤ 3 := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · calc ∑ a : Fin 3, |chordCoord (b, a) (bondVariation b e)| ≤ ∑ _a : Fin 3, (1 : ℝ) := by
          refine Finset.sum_le_sum fun a _ => ?_
          have h1 : chordCoord (b, a) (bondVariation b e) = e a := by simp [chordCoord_apply, bondVariation]
          rw [h1, ← he]
          exact (PiLp.norm_apply_le e a)
      _ = 3 := by simp
  · intro b' _ hne
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [chordCoord_apply, bondVariation, Pi.single_apply, hne]
  · simp
theorem chordCoord_ne_zero_bond {b : ↥(chordBonds (finiteCells F))} {e : BondVector} {α : ChordCoord F}
    (h : chordCoord α (bondVariation b e) ≠ 0) : α.1 = b := by
  by_contra hne
  exact h (by simp [chordCoord_apply, bondVariation, Pi.single_apply, hne])
theorem decayingPart_of_kernel {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {B r : ℝ}
    {P : Finset F.Cell} {S : Set (StepVariable (finiteCells F))}
    (hk : IsDecayingKernel V G B r P S 6) (hB : 0 ≤ B) (hκ : 0 < κ) (hr : 2 ^ 7 * κ ≤ r) (hl₁ : l₁ ≤ 1)
    (hY : Y ∈ P) {d₀ : ℕ} (hd₀ : d₀ ≤ cellSetDiameter P) {m : StepVariable (finiteCells F) → ℝ}
    (hm : ContDiff ℝ (6 : ℕ) m)
    (Md : ↥(chordBonds (finiteCells F)) → StepVariable (finiteCells F) → ℝ)
    (hMd : ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector) (ζ : StepVariable (finiteCells F)),
      ‖e‖ = 1 → |fderiv ℝ m ζ (bondVariation b e)| ≤ Md b ζ)
    (hmP : ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector) (ζ : StepVariable (finiteCells F)),
      ‖e‖ = 1 → fderiv ℝ m ζ (bondVariation b e) ≠ 0 → enclosingCell b.1.1 ∈ P)
    (hS : ∀ p ∈ scaleBallSet F ρ, p.1 • p.2 ∈ S) :
    IsDecayingPart κ ρ l₁ Y V (rayObservable G id m)
      (fun ζ => |m ζ| * (B * Real.exp (-(2 ^ 4 * κ * d₀))) *
        (1 + ∑ α, |chordCoord α (id ζ)| * coordDecay κ Y α) ^ 3)
      (fun b ζ => (Md b ζ + |m ζ| * (3 * 3 + 1)) * (B * Real.exp (-(2 ^ 4 * κ * d₀))) *
        (1 + ∑ α, |chordCoord α (id ζ)| * coordDecay κ Y α) ^ 3) := by
  have hG6 : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), ∀ x ∈ S,
      ContDiffAt ℝ (6 : ℕ) (translatedObservable G V c X) (x, 0) := hk.smooth
  have hc2 : ∀ {i : ℕ}, i ≤ 3 → ((i : ℝ) + 2) * (2 ^ 4 * κ) ≤ r := by
    intro i hi
    have : (i : ℝ) ≤ 3 := by exact_mod_cast hi
    nlinarith
  have hi3 : ∀ {k i : ℕ}, IsControlledOrder k i → i ≤ 3 := by
    intro k i h
    rcases h with h | h <;> omega
  have hxS : ∀ {l : ℝ} {ζ : StepVariable (finiteCells F)}, 0 < l → MemScaledBalls ρ l ζ → l • id ζ ∈ S :=
    fun hl hb => hS _ (mem_scaleBallSet hl hb)
  have hjet : ∀ {k i : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (η : StepVariable (finiteCells F)) (σ : Fin i → ChordCoord F), η ∈ S → i + k ≤ 6 →
      iteratedFDeriv ℝ i (translatedJet G V c X) η (fun j => chordBasis (σ j)) =
        jointMixedDeriv G η V (fun j => (σ j).1) (fun j => EuclideanSpace.single (σ j).2 (1 : ℝ)) c X := by
    intro k i c X η σ hη hik
    rw [jointMixedDeriv_eq_jet G η V _ _ c X ((hk.smooth k c X η hη).of_le (by exact_mod_cast hik))]
    rfl
  refine decayingPart_of_ray (contDiff_id) hm (ray := id) hS hG6 (ContinuousLinearMap.id ℝ _)
    (fun _ _ _ => rfl) chordCoord chordBasis chordBasis_expand (coordDecay κ Y)
    (fun _ => (Real.exp_pos _).le) _ 3 (mul_nonneg hB (Real.exp_pos _).le) hl₁
    (fun b e he => sum_abs_chordCoord_le_three b e he) Md hMd ?_ ?_ ?_ ?_
  · intro k i c X l ζ σ hki hX hl hl' hb
    have hik := controlledOrder_le hki
    rw [hjet c X _ σ (hxS hl hb) (by omega)]
    exact hk.deriv_le_prod hB hκ (hxS hl hb) (fun j => (σ j).1) (fun j => EuclideanSpace.single (σ j).2 (1 : ℝ)) c X
      (by omega) (fun _ => by simp) hX Finset.univ (fun j => cellSupDist (enclosingCell (σ j).1.1.1) Y) (d₀ := d₀)
      (s₀ := bondSpan Y c)
      (fun j _ => cellSupDist_le_diameter
        (Finset.mem_union_left _ (Finset.mem_union_right _ (mem_chordBondCells (fun j => (σ j).1) j)))
        (Finset.mem_union_left _ (Finset.mem_union_left _ hY))) hd₀
      (bondSpan_le_diameter (Finset.mem_union_left _ (Finset.mem_union_left _ hY))
        fun l' => Finset.mem_union_right _ (mem_topBondCells c l'))
      (by simpa using hc2 (hi3 hki))
  · intro k i c X l ζ σ b e hki hX hl hl' hb he hz
    have hik := controlledOrder_le hki
    rw [hjet c X _ σ (hxS hl hb) (by omega)]
    have hbP := hmP b e ζ he hz
    exact hk.deriv_le_prod hB hκ (hxS hl hb) (fun j => (σ j).1) (fun j => EuclideanSpace.single (σ j).2 (1 : ℝ)) c X
      (by omega) (fun _ => by simp) hX Finset.univ (fun j => cellSupDist (enclosingCell (σ j).1.1.1) Y) (d₀ := d₀)
      (s₀ := bondSpan Y (Fin.cons (enclosingCell b.1.1, 0) c : Fin (k + 1) → F.Site F.top × Fin 4))
      (fun j _ => cellSupDist_le_diameter
        (Finset.mem_union_left _ (Finset.mem_union_right _ (mem_chordBondCells (fun j => (σ j).1) j)))
        (Finset.mem_union_left _ (Finset.mem_union_left _ hY))) hd₀
      (bondSpan_le_diameter (Finset.mem_union_left _ (Finset.mem_union_left _ hY)) fun l' => by
        refine Fin.cases ?_ (fun l'' => ?_) l'
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hbP)
        · exact Finset.mem_union_right _ (mem_topBondCells c l''))
      (by simpa using hc2 (hi3 hki))
  · intro k i c X l ζ σ b e j hki hX hl hl' hb he hz
    have hik := controlledOrder_le hki
    rw [hjet c X _ σ (hxS hl hb) (by omega)]
    have hbj : (σ j).1 = b := chordCoord_ne_zero_bond (e := e) (by simpa using hz)
    have hbP : enclosingCell b.1.1 ∈ chordBondCells (fun j => (σ j).1) := by
      rw [← hbj]
      exact mem_chordBondCells (fun j => (σ j).1) j
    exact hk.deriv_le_prod hB hκ (hxS hl hb) (fun j => (σ j).1) (fun j => EuclideanSpace.single (σ j).2 (1 : ℝ)) c X
      (by omega) (fun _ => by simp) hX (Finset.univ.erase j) (fun j => cellSupDist (enclosingCell (σ j).1.1.1) Y)
      (d₀ := d₀)
      (s₀ := bondSpan Y (Fin.cons (enclosingCell b.1.1, 0) c : Fin (k + 1) → F.Site F.top × Fin 4))
      (fun j _ => cellSupDist_le_diameter
        (Finset.mem_union_left _ (Finset.mem_union_right _ (mem_chordBondCells (fun j => (σ j).1) j)))
        (Finset.mem_union_left _ (Finset.mem_union_left _ hY))) hd₀
      (bondSpan_le_diameter (Finset.mem_union_left _ (Finset.mem_union_left _ hY)) fun l' => by
        refine Fin.cases ?_ (fun l'' => ?_) l'
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hbP)
        · exact Finset.mem_union_right _ (mem_topBondCells c l''))
      (by
        have h1 : ((Finset.univ.erase j).card : ℝ) = ((i - 1 : ℕ) : ℝ) := by simp
        rw [h1]
        exact hc2 (by have := hi3 hki; omega))
  · intro k i c X l ζ σ b e hki hX hl hl' hb he
    have hik := controlledOrder_le hki
    set bl : Fin (i + 1) → ↥(chordBonds (finiteCells F)) := Fin.cons b fun j => (σ j).1 with hbl
    set ul : Fin (i + 1) → EuclideanSpace ℝ (Fin 3) :=
      Fin.cons e fun j => EuclideanSpace.single (σ j).2 (1 : ℝ) with hul
    have he1 : (Fin.cons (ContinuousLinearMap.id ℝ _ (bondVariation b e)) fun j => chordBasis (σ j) :
        Fin (i + 1) → StepVariable (finiteCells F)) = fun j => bondVariation (bl j) (ul j) := by
      funext j
      refine Fin.cases ?_ (fun j' => ?_) j
      · simp [hbl, hul]
      · simp [hbl, hul, chordBasis]
    rw [he1, ← jointMixedDeriv_eq_jet G _ V bl ul c X
      ((hk.smooth k c X _ (hxS hl hb)).of_le (by exact_mod_cast (by omega : i + 1 + k ≤ 6)))]
    have hmem : ∀ j : Fin i, enclosingCell (σ j).1.1.1 ∈ chordBondCells bl := fun j => by
      simpa [hbl] using mem_chordBondCells bl j.succ
    have hb0 : enclosingCell b.1.1 ∈ chordBondCells bl := by
      simpa [hbl] using mem_chordBondCells bl 0
    exact hk.deriv_le_prod hB hκ (hxS hl hb) bl ul c X (by omega)
      (fun j => by
        refine Fin.cases ?_ (fun j' => ?_) j
        · simpa [hul] using he
        · simp [hul]) hX Finset.univ (fun j => cellSupDist (enclosingCell (σ j).1.1.1) Y) (d₀ := d₀)
      (s₀ := bondSpan Y (Fin.cons (enclosingCell b.1.1, 0) c : Fin (k + 1) → F.Site F.top × Fin 4))
      (fun j _ => cellSupDist_le_diameter (Finset.mem_union_left _ (Finset.mem_union_right _ (hmem j)))
        (Finset.mem_union_left _ (Finset.mem_union_left _ hY))) hd₀
      (bondSpan_le_diameter (Finset.mem_union_left _ (Finset.mem_union_left _ hY)) fun l' => by
        refine Fin.cases ?_ (fun l'' => ?_) l'
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hb0)
        · exact Finset.mem_union_right _ (mem_topBondCells c l''))
      (by simpa using hc2 (hi3 hki))
end
section
open Set Filter Topology MeasureTheory
open scoped Interval
open YangMills.Construction.BlockAverages
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.ScaledVariables
variable {F : BlockFrame}
theorem jointMixedDeriv_eq_iteratedFDeriv {l k : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (e : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hf : ContDiffAt ℝ (l + k : ℕ) (translatedObservable G V c X) (η, 0)) :
    jointMixedDeriv G η V b e c X =
      iteratedFDeriv ℝ (l + k) (translatedObservable G V c X) (η, 0) fun i => displacementMap b e k (Pi.single i 1) := by
  have h := iteratedFDeriv_comp_add_const (displacementMap b e k) (η, 0) (x := 0) (f := translatedObservable G V c X)
    (by simpa using hf) le_rfl (fun i => Pi.single i 1)
  simp only [jointMixedDeriv]
  rw [jointDisplacement_eq, h]
  simp
def taylorRemainderMean (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) :
    StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  fun η V' => ∫ v in (0 : ℝ)..1, (1 - v) * G (v • η) V'
variable {V : F.GaugeField F.top}
def segmentObservable (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (p : ℝ × (StepVariable (finiteCells F) × (Fin k → ℝ))) : ℝ :=
  translatedObservable G V c X (p.1 • p.2.1, p.2.2)
theorem translatedObservable_taylorRemainderMean (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    translatedObservable (taylorRemainderMean G) V c X =
      fun x => ∫ v in (0 : ℝ)..1, (1 - v) • segmentObservable G V c X (v, x) := rfl
theorem contDiffAt_segmentObservable {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {n k : ℕ}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {η : StepVariable (finiteCells F)} {v : ℝ}
    (h : ContDiffAt ℝ n (translatedObservable G V c X) (v • η, 0)) :
    ContDiffAt ℝ n (segmentObservable G V c X) (v, (η, 0)) := by
  have h2 : ContDiff ℝ n (fun p : ℝ × (StepVariable (finiteCells F) × (Fin k → ℝ)) =>
      (p.1 • p.2.1, p.2.2)) :=
    (contDiff_fst.smul (contDiff_fst.comp contDiff_snd)).prodMk (contDiff_snd.comp contDiff_snd)
  exact ContDiffAt.comp (v, (η, (0 : Fin k → ℝ))) (g := translatedObservable G V c X) h h2.contDiffAt
theorem isDecayingKernel_taylorRemainderMean {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {B r : ℝ}
    {P : Finset F.Cell} {S : Set (StepVariable (finiteCells F))} {n : ℕ}
    (hk : IsDecayingKernel V G B r P S n) (hstar : ∀ η ∈ S, ∀ v ∈ Icc (0 : ℝ) 1, v • η ∈ S) (hB : 0 ≤ B) :
    IsDecayingKernel V (taylorRemainderMean G) B r P S n := by
  have hM : Continuous fun v : ℝ => 1 - v := by fun_prop
  have hseg : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (η), η ∈ S →
      ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ n (segmentObservable G V c X) (v, (η, 0)) :=
    fun k c X η hη v hv => contDiffAt_segmentObservable (hk.smooth k c X _ (hstar η hη v hv))
  refine ⟨fun k c X η hη => ?_, fun η hη l j b u c X hlj hu hX => ?_⟩
  · rw [translatedObservable_taylorRemainderMean]
    exact (paramIntegral_jets hM (hseg k c X η hη)).1
  · obtain ⟨h1, h2⟩ := paramIntegral_jets hM (hseg j c X η hη)
    have hW : ContDiffAt ℝ (l + j : ℕ) (translatedObservable (taylorRemainderMean G) V c X) (η, 0) := by
      rw [translatedObservable_taylorRemainderMean]
      exact h1.of_le (by exact_mod_cast hlj)
    rw [jointMixedDeriv_eq_iteratedFDeriv _ η V b u c X hW, translatedObservable_taylorRemainderMean, h2 _ hlj]
    set E := Real.exp (-(r * cellSetDiameter (P ∪ chordBondCells b ∪ topBondCells c))) with hE
    have hconst : ∀ v ∈ Ι (0 : ℝ) 1, ‖(1 - v) • iteratedFDeriv ℝ (l + j) (segmentObservable G V c X) (v, (η, 0))
        (fun i => ((0 : ℝ), displacementMap b u j (Pi.single i 1)))‖ ≤ B * E := by
      intro v hv
      rw [uIoc_of_le zero_le_one] at hv
      have hv' : v ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hv
      have hvS := hstar η hη v hv'
      have hG : ContDiffAt ℝ (l + j : ℕ) (translatedObservable G V c X) (v • η, 0) :=
        (hk.smooth j c X _ hvS).of_le (by exact_mod_cast hlj)
      have hΦ : ContDiffAt ℝ (l + j : ℕ) (segmentObservable G V c X) (v, (η, 0)) := contDiffAt_segmentObservable hG
      have e1 := partialJetRight_eq hΦ le_rfl (fun i => displacementMap b u j (Pi.single i 1))
      rw [← e1]
      let A : StepVariable (finiteCells F) × (Fin j → ℝ) →L[ℝ] StepVariable (finiteCells F) × (Fin j → ℝ) :=
        (v • ContinuousLinearMap.fst ℝ _ _).prod (ContinuousLinearMap.snd ℝ _ _)
      have e2 := iteratedFDeriv_comp_add_const A 0 (x := (η, 0)) (f := translatedObservable G V c X)
        (by simpa [A] using hG) le_rfl (fun i => displacementMap b u j (Pi.single i 1))
      have e3 : partialJetRight (segmentObservable G V c X) (η, 0)
          (fun i => displacementMap b u j (Pi.single i 1)) v =
          iteratedFDeriv ℝ (l + j) (fun z => translatedObservable G V c X (A z + 0)) (η, 0)
            (fun i => displacementMap b u j (Pi.single i 1)) := by
        simp only [partialJetRight]
        congr 2
        funext z
        simp [segmentObservable, A]
      let cs : Fin (l + j) → ℝ := Fin.addCases (fun _ => v) (fun _ => 1)
      have e4 : (fun i => A (displacementMap b u j (Pi.single i 1))) =
          fun i => cs i • displacementMap b u j (Pi.single i 1) := by
        funext i
        refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
        · simp [cs, displacementMap_castAdd, A]
        · simp [cs, displacementMap_natAdd, A]
      have e5 : ∏ i, cs i = v ^ l := by
        rw [Fin.prod_univ_add]
        simp [cs]
      have e6 : A (η, 0) + 0 = (v • η, 0) := by simp [A]
      rw [e3, e2, e4, ContinuousMultilinearMap.map_smul_univ, e6, e5,
        ← jointMixedDeriv_eq_iteratedFDeriv G (v • η) V b u c X hG]
      have hd := hk.deriv_le _ hvS l j b u c X hlj hu hX
      have h1v : ‖(1 - v)‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hv.1, hv.2]
      have hvl : ‖v ^ l‖ ≤ 1 := by
        rw [norm_pow, Real.norm_eq_abs, abs_of_pos hv.1]
        exact pow_le_one₀ hv.1.le hv.2
      rw [norm_smul, norm_smul]
      calc ‖1 - v‖ * (‖v ^ l‖ * ‖jointMixedDeriv G (v • η) V b u c X‖)
          ≤ 1 * (1 * ‖jointMixedDeriv G (v • η) V b u c X‖) := by gcongr
        _ ≤ B * E := by
            rw [one_mul, one_mul, Real.norm_eq_abs]
            exact hd
    have := intervalIntegral.norm_integral_le_of_norm_le_const hconst
    simpa using this
theorem IsDecayingPart.congr {κ ρ l₁ : ℝ} {Y : F.Cell}
    {Ob Ob' : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {Bd : StepVariable (finiteCells F) → ℝ}
    {Sd : ↥(chordBonds (finiteCells F)) → StepVariable (finiteCells F) → ℝ}
    (h : IsDecayingPart κ ρ l₁ Y V Ob' Bd Sd)
    (he : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), ∀ p ∈ scaleBallSet F ρ,
      scaledObservable Ob V c X =ᶠ[𝓝 (p, 0)] scaledObservable Ob' V c X) :
    IsDecayingPart κ ρ l₁ Y V Ob Bd Sd := by
  have hs : ∀ (k i : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (p : ℝ × StepVariable (finiteCells F)),
      p ∈ scaleBallSet F ρ → scaleJet (scaledObservable Ob V c X) (unitParams k) i p =
        scaleJet (scaledObservable Ob' V c X) (unitParams k) i p :=
    fun k i c X p hp => scaleJet_congr (unitParams k) (isOpen_scaleBallSet ρ) (he k c X) i hp
  refine ⟨fun k c X p hp => (h.smooth k c X p hp).congr_of_eventuallyEq (he k c X p hp), ?_, ?_⟩
  · intro k i c X l ζ hki hX hl hl₁ hb
    rw [scaleDeriv_eq_scaleJet, hs k i c X _ (mem_scaleBallSet hl hb)]
    exact h.deriv_le k i c X l ζ hki hX hl hl₁ hb
  · intro k i c X l ζ b e hki hX hl hl₁ hb he'
    have hp := mem_scaleBallSet hl hb
    have hev : (fun ζ' => scaleDeriv Ob V c X i ζ' l) =ᶠ[𝓝 ζ]
        fun ζ' => scaleDeriv Ob' V c X i ζ' l := by
      filter_upwards [eventually_mem_scaleBallSet hp] with ζ' hζ'
      exact hs k i c X _ hζ'
    simp only [bondPartialDeriv]
    rw [hev.fderiv_eq]
    exact h.partial_le k i c X l ζ b e hki hX hl hl₁ hb he'
structure IsDecayingEnergy (V : F.GaugeField F.top) (E : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (B r : ℝ) (S : Set (StepVariable (finiteCells F))) : Prop where
  smooth : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), ∀ η ∈ S,
    ContDiffAt ℝ (8 : ℕ) (translatedObservable E V c X) (η, 0)
  deriv_le : ∀ η ∈ S, ∀ (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions),
    2 ≤ l → l + j ≤ 8 → (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
    |jointMixedDeriv E η V b u c X| ≤
      B * Real.exp (-(r * cellSetDiameter (∅ ∪ chordBondCells b ∪ topBondCells c)))
def secondDerivKernel (E : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (α β : ChordCoord F) :
    StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  fun η V' => secondDerivAlong (fun η' => E η' V') η (chordBasis α) (chordBasis β)
theorem translatedObservable_secondDerivKernel (E : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (α β : ChordCoord F) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    translatedObservable (secondDerivKernel E α β) V c X =
      secondPartialLeft (translatedObservable E V c X) (chordBasis α) (chordBasis β) := rfl
theorem isDecayingKernel_secondDerivKernel {E : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {B r : ℝ}
    {S : Set (StepVariable (finiteCells F))} (h : IsDecayingEnergy V E B r S) (hr : 0 ≤ r) (hB : 0 ≤ B)
    (α β : ChordCoord F) :
    IsDecayingKernel V (secondDerivKernel E α β) B r {enclosingCell α.1.1.1, enclosingCell β.1.1.1} S 6 := by
  refine ⟨fun k c X η hη => ?_, fun η hη l j b u c X hlj hu hX => ?_⟩
  · rw [translatedObservable_secondDerivKernel]
    exact contDiffAt_secondPartialLeft (M := 6) (N := 8) (by norm_num) _ _ (h.smooth k c X η hη)
  · have hf := h.smooth j c X η hη
    have hG2 : ContDiffAt ℝ (l + j : ℕ) (translatedObservable (secondDerivKernel E α β) V c X) (η, 0) := by
      rw [translatedObservable_secondDerivKernel]
      exact contDiffAt_secondPartialLeft (M := l + j) (N := 8) (by omega) _ _ hf
    rw [jointMixedDeriv_eq_jet _ η V b u c X hG2]
    have hnear : ∀ᶠ η' in 𝓝 η, ContDiffAt ℝ (8 : ℕ) (translatedObservable E V c X) (η', 0) :=
      eventually_contDiffAt_left hf
    have hev : partialJetRight (translatedObservable (secondDerivKernel E α β) V c X) 0 (unitParams j) =ᶠ[𝓝 η]
        fun y => iteratedFDeriv ℝ 2 (translatedJet E V c X) y (pairList (chordBasis β) (chordBasis α)) := by
      filter_upwards [hnear] with η' h'
      rw [translatedObservable_secondDerivKernel]
      exact partialJetRight_secondPartialLeft (k := j) (N := 8) (by omega) _ _ (unitParams j) h'
    rw [iteratedFDeriv_eq_of_eventuallyEq hev l]
    have hRc : ContDiffAt ℝ (8 - j : ℕ) (translatedJet E V c X) η :=
      contDiffAt_partialJetRight hf (by omega) (unitParams j)
    set b' : Fin (l + 2) → ↥(chordBonds (finiteCells F)) := Fin.append b (pairList β.1 α.1) with hb'
    set u' : Fin (l + 2) → EuclideanSpace ℝ (Fin 3) :=
      Fin.append u (pairList (EuclideanSpace.single β.2 (1 : ℝ)) (EuclideanSpace.single α.2 (1 : ℝ))) with hu'
    have hA := iteratedFDeriv_iteratedFDeriv_apply (pairList (chordBasis β) (chordBasis α)) (N := 8 - j)
      (f := translatedJet E V c X) l (l + 2)
      (fun i => bondVariation (b i) (u i)) (fun i => bondVariation (b' i) (u' i)) η rfl (fun i hi => ?_)
      (fun i hi hk => ?_) hRc (by omega)
    · rw [hA, ← jointMixedDeriv_eq_jet E η V b' u' c X (hf.of_le (by exact_mod_cast (by omega : l + 2 + j ≤ 8)))]
      have hu'1 : ∀ i, ‖u' i‖ = 1 := by
        intro i
        refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
        · simp [hu', hu]
        · refine Fin.cases ?_ (fun i'' => ?_) i'
          · simp [hu', pairList]
          · have : i'' = 0 := Subsingleton.elim _ _
            subst this
            simp [hu', pairList]
      refine (h.deriv_le η hη (l + 2) j b' u' c X (by omega) (by omega) hu'1 hX).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg ?_)) hB
      refine mul_le_mul_of_nonneg_left ?_ hr
      have hsub : {enclosingCell α.1.1.1, enclosingCell β.1.1.1} ∪ chordBondCells b ∪ topBondCells c ⊆
          ∅ ∪ chordBondCells b' ∪ topBondCells c := by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.empty_union, Finset.mem_union]
        rcases hx with (hx | hx) | hx
        · left
          rcases hx with rfl | rfl
          · simpa [hb', pairList] using mem_chordBondCells b' (Fin.natAdd l 1)
          · simpa [hb', pairList] using mem_chordBondCells b' (Fin.natAdd l 0)
        · left
          simp only [chordBondCells, Finset.mem_image, Finset.mem_univ, true_and] at hx
          obtain ⟨i, rfl⟩ := hx
          simpa [hb'] using mem_chordBondCells b' (Fin.castAdd 2 i)
        · exact Or.inr hx
      exact_mod_cast cellSetDiameter_mono hsub
    · have this : i = Fin.castAdd 2 ⟨i.val, hi⟩ := Fin.ext rfl
      simp only [hb', hu']
      conv_lhs => rw [this]
      rw [Fin.append_left, Fin.append_left]
    · have this : i = Fin.natAdd l ⟨i.val - l, hk⟩ := Fin.ext (by simp; omega)
      simp only [hb', hu']
      conv_lhs => rw [this]
      rw [Fin.append_right, Fin.append_right]
      generalize (⟨i.val - l, hk⟩ : Fin 2) = j'
      refine Fin.cases ?_ (fun j'' => ?_) j'
      · simp [pairList, chordBasis]
      · have : j'' = 0 := Subsingleton.elim _ _
        subst this
        simp [pairList, chordBasis]
end
section
open Set Filter Topology
open YangMills.Construction.BlockAverages
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.ScaledVariables
variable {F : BlockFrame}
theorem cellSupDist_self (x : F.Cell) : cellSupDist x x = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem cellSupDist_triangle (x y z : F.Cell) : cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem cellSetDiameter_union_le {A B : Finset F.Cell} {z : F.Cell} (hA : z ∈ A) (hB : z ∈ B) :
    cellSetDiameter (A ∪ B) ≤ cellSetDiameter A + cellSetDiameter B := by
  refine Finset.sup_le fun u hu => Finset.sup_le fun v hv => ?_
  rcases Finset.mem_union.1 hu with hu | hu <;> rcases Finset.mem_union.1 hv with hv | hv
  · exact (cellSupDist_le_diameter hu hv).trans (Nat.le_add_right _ _)
  · exact (cellSupDist_triangle u z v).trans
      (add_le_add (cellSupDist_le_diameter hu hA) (cellSupDist_le_diameter hB hv))
  · have h1 := cellSupDist_triangle v z u
    have h2 : cellSupDist u v ≤ cellSupDist u z + cellSupDist z v := cellSupDist_triangle u z v
    exact h2.trans (by
      have e1 := cellSupDist_le_diameter hu hB
      have e2 := cellSupDist_le_diameter hA hv
      omega)
  · exact (cellSupDist_le_diameter hu hv).trans (Nat.le_add_left _ _)
theorem cellSetDiameter_singleton (z : F.Cell) : cellSetDiameter ({z} : Finset F.Cell) = 0 := by
  simp [cellSetDiameter, cellSupDist_self]
theorem cellSetDiameter_biUnion_le {ι : Type} (s : Finset ι) (Q : ι → Finset F.Cell) {z : F.Cell}
    (hz : ∀ i ∈ s, z ∈ Q i) :
    cellSetDiameter ({z} ∪ s.biUnion Q) ≤ ∑ i ∈ s, cellSetDiameter (Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cellSetDiameter_singleton]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.biUnion_insert]
    have h1 := ih fun i hi => hz i (Finset.mem_insert_of_mem hi)
    have h2 : ({z} ∪ (Q a ∪ s.biUnion Q) : Finset F.Cell) = Q a ∪ ({z} ∪ s.biUnion Q) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_singleton]
      tauto
    rw [h2]
    have h3 := cellSetDiameter_union_le (z := z) (A := Q a) (B := {z} ∪ s.biUnion Q)
      (hz a (Finset.mem_insert_self a s)) (by simp)
    omega
abbrev ListSlot (F : BlockFrame) (k : ℕ) : Type :=
  (↥(chordBonds (finiteCells F)) × EuclideanSpace ℝ (Fin 3)) ⊕ Fin k
def slotVector {k : ℕ} : ListSlot F k → StepVariable (finiteCells F) × (Fin k → ℝ)
  | Sum.inl p => (bondVariation p.1 p.2, 0)
  | Sum.inr j => (0, Pi.single j 1)
def slotCell {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) : ListSlot F k → F.Cell
  | Sum.inl p => enclosingCell p.1.1.1
  | Sum.inr j => (c j).1
def IsNormalizedSlot {k : ℕ} : ListSlot F k → Prop
  | Sum.inl p => ‖p.2‖ = 1
  | Sum.inr _ => True
variable {V : F.GaugeField F.top}
theorem IsDecayingKernel.iteratedFDeriv_slots_le {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {B r : ℝ} {P : Finset F.Cell} {S : Set (StepVariable (finiteCells F))} {n : ℕ}
    (hk : IsDecayingKernel V G B r P S n) (hB : 0 ≤ B) (hr : 0 ≤ r) {η : StepVariable (finiteCells F)} (hη : η ∈ S)
    {k p : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X)
    (t : Fin p → ListSlot F k) (ht : ∀ i, IsNormalizedSlot (t i)) (hp : p ≤ n) :
    |iteratedFDeriv ℝ p (translatedObservable G V c X) (η, 0) fun i => slotVector (t i)| ≤
      B * Real.exp (-(r * cellSetDiameter (P ∪ Finset.univ.image fun i => slotCell c (t i)))) := by
  classical
  let L := {i : Fin p // (t i).isLeft = true}
  let Rr := {i : Fin p // ¬ (t i).isLeft = true}
  let l := Fintype.card L
  let j := Fintype.card Rr
  let eL : Fin l ≃ L := (Fintype.equivFin L).symm
  let eR : Fin j ≃ Rr := (Fintype.equivFin Rr).symm
  let σ : Fin (l + j) ≃ Fin p :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr eL eR).trans (Equiv.sumCompl _))
  have hlj : p = l + j := by
    have := Fintype.card_congr σ
    simpa using this.symm
  have hσL : ∀ a : Fin l, σ (Fin.castAdd j a) = (eL a).1 := by
    intro a
    simp [σ]
    rfl
  have hσR : ∀ d : Fin j, σ (Fin.natAdd l d) = (eR d).1 := by
    intro d
    simp [σ]
    rfl
  have hleft : ∀ a : Fin l, ∃ q, t (eL a).1 = Sum.inl q := by
    intro a
    have := (eL a).2
    exact Sum.isLeft_iff.1 this
  have hright : ∀ d : Fin j, ∃ q, t (eR d).1 = Sum.inr q := by
    intro d
    have := (eR d).2
    rw [Bool.not_eq_true, Sum.isLeft_eq_false] at this
    exact Sum.isRight_iff.1 this
  choose qL hqL using hleft
  choose qR hqR using hright
  let bl : Fin l → ↥(chordBonds (finiteCells F)) := fun a => (qL a).1
  let ul : Fin l → EuclideanSpace ℝ (Fin 3) := fun a => (qL a).2
  let cl : Fin j → F.Site F.top × Fin 4 := fun d => c (qR d)
  let Xl : Fin j → imaginaryQuaternions := fun d => X (qR d)
  let ι : (Fin j → ℝ) →L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearMap.pi fun i => ∑ d, if qR d = i then ContinuousLinearMap.proj d else 0
  have hι : ∀ (q : Fin j → ℝ) (i : Fin k), ι q i = ∑ d, if qR d = i then q d else 0 := by
    intro q i
    simp only [ι, ContinuousLinearMap.coe_pi', sum_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  have hsp : ∀ q : Fin j → ℝ, _root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread cl Xl q = _root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X (ι q) := by
    intro q
    funext y i'
    simp only [_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread]
    have h1 : ∀ i, (if c i = (y, i') then ι q i • X i else 0) =
        ∑ d, if qR d = i then (if c i = (y, i') then q d • X i else 0) else 0 := by
      intro i
      rw [hι]
      by_cases h : c i = (y, i')
      · simp only [h, if_true, Finset.sum_smul]
        refine Finset.sum_congr rfl fun d _ => ?_
        split_ifs <;> simp
      · simp [h]
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [cl, Xl]
  let A : StepVariable (finiteCells F) × (Fin j → ℝ) →L[ℝ] StepVariable (finiteCells F) × (Fin k → ℝ) :=
    (ContinuousLinearMap.id ℝ _).prodMap ι
  have hmoved : translatedObservable G V cl Xl = fun z => translatedObservable G V c X (A z + 0) := by
    funext z
    show G z.1 (leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread cl Xl z.2) V) = G (z.1 + 0) (leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X (ι z.2 + 0)) V)
    rw [hsp, add_zero, add_zero]
  have hA0 : A (η, 0) + 0 = (η, 0) := by simp [A]
  have hfc : ContDiffAt ℝ (l + j : ℕ) (translatedObservable G V c X) (η, 0) :=
    (hk.smooth k c X η hη).of_le (by exact_mod_cast (by omega : l + j ≤ n))
  have hsm : ContDiffAt ℝ (l + j : ℕ) (translatedObservable G V cl Xl) (η, 0) :=
    (hk.smooth j cl Xl η hη).of_le (by exact_mod_cast (by omega : l + j ≤ n))
  have hder := jointMixedDeriv_eq_iteratedFDeriv G η V bl ul cl Xl hsm
  have e1 := iteratedFDeriv_comp_add_const A 0 (x := (η, 0)) (f := translatedObservable G V c X)
    (by rwa [hA0]) le_rfl (fun i => displacementMap bl ul j (Pi.single i 1))
  rw [← hmoved, hA0] at e1
  have e2 : (fun i => A (displacementMap bl ul j (Pi.single i 1))) = fun i => slotVector (t (σ i)) := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun d => ?_) i
    · rw [displacementMap_castAdd, hσL, hqL]
      simp [A, slotVector, bl, ul]
    · rw [displacementMap_natAdd, hσR, hqR]
      have hs : ι (Pi.single d 1) = Pi.single (qR d) 1 := by
        funext i
        rw [hι, Finset.sum_eq_single d]
        · by_cases h : qR d = i
          · subst h; simp
          · have : i ≠ qR d := fun h' => h h'.symm
            simp [h, this]
        · intro d' _ hne
          simp [hne]
        · simp
      simp [A, slotVector, hs]
  rw [e2] at e1
  have hfp : ContDiffAt ℝ p (translatedObservable G V c X) (η, 0) :=
    (hk.smooth k c X η hη).of_le (by exact_mod_cast hp)
  have e3 := iteratedFDeriv_reindex hlj hfp (fun i => slotVector (t i)) (fun i => slotVector (t (σ i))) σ
    (fun _ => rfl)
  rw [e3, ← e1, ← hder]
  have hul : ∀ a, ‖ul a‖ = 1 := by
    intro a
    have := ht (eL a).1
    rw [hqL] at this
    exact this
  have hXl : AreUnitVectors Xl := fun d => hX _
  refine (hk.deriv_le η hη l j bl ul cl Xl (by omega) hul hXl).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg ?_)) hB
  refine mul_le_mul_of_nonneg_left ?_ hr
  have hsub : P ∪ (Finset.univ.image fun i => slotCell c (t i)) ⊆
      P ∪ chordBondCells bl ∪ topBondCells cl := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    · simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      have hi : i = σ (σ.symm i) := (σ.apply_symm_apply i).symm
      generalize σ.symm i = i' at hi
      subst hi
      refine Fin.addCases (fun a => ?_) (fun d => ?_) i'
      · rw [hσL, hqL]
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (mem_chordBondCells bl a))
      · rw [hσR, hqR]
        exact Finset.mem_union_right _ (mem_topBondCells cl d)
  exact_mod_cast cellSetDiameter_mono hsub
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem iteratedFDeriv_clm_of_two_le (π : E →L[ℝ] ℝ) : ∀ (p : ℕ) (x : E) (v : Fin (p + 2) → E),
    iteratedFDeriv ℝ (p + 2) π x v = 0 := by
  have hs : ∀ (n : ℕ) (x : E), ContDiffAt ℝ (n : ℕ) π x := fun n x => π.contDiff.contDiffAt
  intro p
  induction p with
  | zero =>
    intro x v
    have e := iteratedFDeriv_succ_cons_eq_fderiv (hs 2 x) (v 0) (Fin.tail v)
    rw [Fin.cons_self_tail] at e
    rw [e]
    have : (fun y => iteratedFDeriv ℝ 1 π y (Fin.tail v)) = fun _ => π (Fin.tail v 0) := by
      funext y
      simp [iteratedFDeriv_one_apply]
    rw [this]
    simp
  | succ p ih =>
    intro x v
    have e := iteratedFDeriv_succ_cons_eq_fderiv (hs (p + 3) x) (v 0) (Fin.tail v)
    rw [Fin.cons_self_tail] at e
    rw [e]
    have : (fun y => iteratedFDeriv ℝ (p + 2) π y (Fin.tail v)) = fun _ => 0 :=
      funext fun y => ih y _
    rw [this]
    simp
end
abbrev ScaledPoint (F : BlockFrame) : Type := ℝ × StepVariable (finiteCells F)
def embedMap (F : BlockFrame) (k : ℕ) :
    StepVariable (finiteCells F) × (Fin k → ℝ) →L[ℝ] ScaledPoint F × (Fin k → ℝ) :=
  (ContinuousLinearMap.inr ℝ ℝ (StepVariable (finiteCells F))).prodMap (ContinuousLinearMap.id ℝ _)
def forgetScaleMap (F : BlockFrame) (k : ℕ) :
    ScaledPoint F × (Fin k → ℝ) →L[ℝ] StepVariable (finiteCells F) × (Fin k → ℝ) :=
  (ContinuousLinearMap.snd ℝ ℝ (StepVariable (finiteCells F))).prodMap (ContinuousLinearMap.id ℝ _)
def scaleCoordMap (F : BlockFrame) (k : ℕ) : ScaledPoint F × (Fin k → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (StepVariable (finiteCells F))).comp
    (ContinuousLinearMap.fst ℝ (ScaledPoint F) (Fin k → ℝ))
def scaledSlotVector {k : ℕ} : Option (ListSlot F k) → ScaledPoint F × (Fin k → ℝ)
  | none => ((1, 0), 0)
  | some s => embedMap F k (slotVector s)
def scaledSlotCells {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) : Option (ListSlot F k) → Finset F.Cell
  | none => ∅
  | some s => {slotCell c s}
def IsNormalizedScaledSlot {k : ℕ} : Option (ListSlot F k) → Prop
  | none => True
  | some s => IsNormalizedSlot s
theorem forgetScale_some {k : ℕ} (s : ListSlot F k) :
    forgetScaleMap F k (scaledSlotVector (some s)) = slotVector s := by
  simp only [scaledSlotVector]
  generalize slotVector s = y
  obtain ⟨a, b⟩ := y
  simp [forgetScaleMap, embedMap]
theorem forgetScale_none {k : ℕ} : forgetScaleMap F k (scaledSlotVector (none : Option (ListSlot F k))) = 0 := by
  simp [scaledSlotVector, forgetScaleMap]
theorem scaleCoord_some {k : ℕ} (s : ListSlot F k) : scaleCoordMap F k (scaledSlotVector (some s)) = 0 := by
  simp only [scaledSlotVector]
  generalize slotVector s = y
  obtain ⟨a, b⟩ := y
  simp [scaleCoordMap, embedMap]
theorem scaleCoord_none {k : ℕ} : scaleCoordMap F k (scaledSlotVector (none : Option (ListSlot F k))) = 1 := by
  simp [scaledSlotVector, scaleCoordMap]
def scaleAndValue {k : ℕ} (R : StepVariable (finiteCells F) × (Fin k → ℝ) → ℝ) (p : ScaledPoint F × (Fin k → ℝ)) :
    ℝ × ℝ :=
  (scaleCoordMap F k p, R (forgetScaleMap F k p))
variable {V : F.GaugeField F.top}
theorem iteratedFDeriv_scaleAndValue_le {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {B r : ℝ}
    {S : Set (StepVariable (finiteCells F))} {z : F.Cell}
    (hk : IsDecayingKernel V G B r {z} S 6) (hB : 1 ≤ B) (hr : 0 ≤ r) {x : ScaledPoint F} (hx : x.2 ∈ S) {k p : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X)
    (t : Fin p → Option (ListSlot F k)) (ht : ∀ i, IsNormalizedScaledSlot (t i)) (hp0 : 0 < p) (hp : p ≤ 6) :
    ‖iteratedFDeriv ℝ p (scaleAndValue (translatedObservable G V c X)) (x, 0) fun i => scaledSlotVector (t i)‖ ≤
      B * Real.exp (-(r * cellSetDiameter ({z} ∪ Finset.univ.biUnion fun i => scaledSlotCells c (t i)))) := by
  classical
  have hR6 : ContDiffAt ℝ (6 : ℕ) (translatedObservable G V c X) (forgetScaleMap F k (x, 0)) := by
    have : forgetScaleMap F k (x, 0) = (x.2, 0) := by simp [forgetScaleMap]
    rw [this]
    exact hk.smooth k c X _ hx
  have hRp : ContDiffAt ℝ (p : ℕ) (translatedObservable G V c X) (forgetScaleMap F k (x, 0) + 0) := by
    simpa using hR6.of_le (by exact_mod_cast hp)
  have hsecond : ContDiffAt ℝ (p : ℕ) (fun q => translatedObservable G V c X (forgetScaleMap F k q)) (x, 0) :=
    ContDiffAt.comp (x, (0 : Fin k → ℝ)) (g := translatedObservable G V c X) (by simpa using hRp)
      (forgetScaleMap F k).contDiff.contDiffAt
  have hf : ContDiffAt ℝ (p : ℕ) (scaleAndValue (translatedObservable G V c X)) (x, 0) :=
    (scaleCoordMap F k).contDiff.contDiffAt.prodMk hsecond
  have e1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).iteratedFDeriv_comp_left hf (le_refl _)
  have e2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).iteratedFDeriv_comp_left hf (le_refl _)
  set v : Fin p → ScaledPoint F × (Fin k → ℝ) := fun i => scaledSlotVector (t i) with hv
  have f1 : (iteratedFDeriv ℝ p (scaleAndValue (translatedObservable G V c X)) (x, 0) v).1 =
      iteratedFDeriv ℝ p (scaleCoordMap F k) (x, 0) v := by
    have := congrArg (fun T => T v) e1
    exact this.symm
  have f2 : (iteratedFDeriv ℝ p (scaleAndValue (translatedObservable G V c X)) (x, 0) v).2 =
      iteratedFDeriv ℝ p (translatedObservable G V c X) (forgetScaleMap F k (x, 0) + 0)
        fun i => forgetScaleMap F k (v i) := by
    have h3 := congrArg (fun T => T v) e2
    have h4 := iteratedFDeriv_comp_add_const (forgetScaleMap F k) 0 (x := (x, 0)) (f := translatedObservable G V c X)
      hRp le_rfl v
    simp only [add_zero] at h4 ⊢
    exact h3.symm.trans h4
  have hE0 : 0 < Real.exp (-(r * cellSetDiameter ({z} ∪ Finset.univ.biUnion fun i => scaledSlotCells c (t i)))) :=
    Real.exp_pos _
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, f1, f2]
  by_cases hall : ∀ i, (t i).isSome = true
  · let t' : Fin p → ListSlot F k := fun i => (t i).get (hall i)
    have ht' : ∀ i, t i = some (t' i) := fun i => by simp [t']
    have hdrop : (fun i => forgetScaleMap F k (v i)) = fun i => slotVector (t' i) := by
      funext i
      simp only [hv]
      rw [ht', forgetScale_some]
    have hun : ∀ i, IsNormalizedSlot (t' i) := fun i => by
      have := ht i
      rw [ht'] at this
      exact this
    have h2 := hk.iteratedFDeriv_slots_le (by linarith) hr hx c X hX t' hun hp
    have hd0 : forgetScaleMap F k (x, 0) + 0 = (x.2, 0) := by simp [forgetScaleMap]
    have hset : ({z} ∪ Finset.univ.image fun i => slotCell c (t' i)) =
        ({z} ∪ Finset.univ.biUnion fun i => scaledSlotCells c (t i) : Finset F.Cell) := by
      ext y
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_biUnion]
      refine or_congr Iff.rfl ⟨fun ⟨i, hi⟩ => ⟨i, ?_⟩, fun ⟨i, hi⟩ => ⟨i, ?_⟩⟩
      · rw [ht']; simp [scaledSlotCells, hi]
      · rw [ht'] at hi; simpa [scaledSlotCells, eq_comm] using hi
    rw [hset] at h2
    have h1 : iteratedFDeriv ℝ p (scaleCoordMap F k) (x, 0) v = 0 := by
      obtain ⟨p', rfl⟩ | rfl : (∃ p', p = p' + 2) ∨ p = 1 := by
        rcases p with _ | _ | p'
        · omega
        · right; rfl
        · left; exact ⟨p', rfl⟩
      · exact iteratedFDeriv_clm_of_two_le _ p' _ v
      · rw [iteratedFDeriv_one_apply]
        simp only [ContinuousLinearMap.fderiv, hv]
        rw [ht', scaleCoord_some]
    rw [h1, hdrop, hd0, abs_zero]
    exact max_le (by positivity) h2
  · push_neg at hall
    obtain ⟨i₀, hi₀⟩ := hall
    have hnone : t i₀ = none := by simpa using hi₀
    have h2 : (iteratedFDeriv ℝ p (translatedObservable G V c X) (forgetScaleMap F k (x, 0) + 0)
        fun i => forgetScaleMap F k (v i)) = 0 := by
      refine ContinuousMultilinearMap.map_coord_zero _ i₀ ?_
      simp only [hv]
      rw [hnone, forgetScale_none]
    rw [h2, abs_zero]
    refine max_le ?_ (by positivity)
    obtain ⟨p', rfl⟩ | rfl : (∃ p', p = p' + 2) ∨ p = 1 := by
      rcases p with _ | _ | p'
      · omega
      · right; rfl
      · left; exact ⟨p', rfl⟩
    · rw [iteratedFDeriv_clm_of_two_le _ p' _ v]
      simp only [abs_zero]
      positivity
    · have hi0 : i₀ = 0 := Subsingleton.elim _ _
      subst hi0
      have hset : ({z} ∪ Finset.univ.biUnion fun i => scaledSlotCells c (t i) : Finset F.Cell) = {z} := by
        ext y
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro (h | ⟨i, hi⟩)
          · exact h
          · have : i = 0 := Subsingleton.elim _ _
            subst this
            rw [hnone] at hi
            simp [scaledSlotCells] at hi
        · exact Or.inl
      rw [hset, cellSetDiameter_singleton]
      rw [iteratedFDeriv_one_apply]
      simp only [ContinuousLinearMap.fderiv, hv]
      rw [hnone, scaleCoord_none]
      simpa using hB
theorem iteratedFDeriv_comp_scaleAndValue_le {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {B r M : ℝ}
    {S : Set (StepVariable (finiteCells F))} {z : F.Cell}
    (hk : IsDecayingKernel V G B r {z} S 6) (hB : 1 ≤ B) (hr : 0 ≤ r) {x : ScaledPoint F} (hx : x.2 ∈ S) {k m : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X)
    (t : Fin m → Option (ListSlot F k)) (ht : ∀ i, IsNormalizedScaledSlot (t i)) (hm : m ≤ 6) (g : ℝ × ℝ → ℝ)
    (hg : ContDiff ℝ (6 : ℕ) g) (hM0 : 0 ≤ M)
    (hM : ∀ p, p ≤ 6 → ‖iteratedFDeriv ℝ p g (scaleAndValue (translatedObservable G V c X) (x, 0))‖ ≤ M) :
    |iteratedFDeriv ℝ m (g ∘ scaleAndValue (translatedObservable G V c X)) (x, 0) fun i => scaledSlotVector (t i)| ≤
      (Fintype.card (OrderedFinpartition m) : ℝ) * (M * (B ^ m *
        Real.exp (-(r * cellSetDiameter ({z} ∪ Finset.univ.biUnion fun i => scaledSlotCells c (t i)))))) := by
  classical
  have hR6 : ContDiffAt ℝ (6 : ℕ) (translatedObservable G V c X) (forgetScaleMap F k (x, 0)) := by
    have : forgetScaleMap F k (x, 0) = (x.2, 0) := by simp [forgetScaleMap]
    rw [this]
    exact hk.smooth k c X _ hx
  have hf : ContDiffAt ℝ (m : ℕ) (scaleAndValue (translatedObservable G V c X)) (x, 0) :=
    (scaleCoordMap F k).contDiff.contDiffAt.prodMk
      ((ContDiffAt.comp (x, (0 : Fin k → ℝ)) (g := translatedObservable G V c X) hR6
        (forgetScaleMap F k).contDiff.contDiffAt).of_le (by exact_mod_cast hm))
  refine iteratedFDeriv_comp_bound hf ((hg.of_le (by exact_mod_cast hm)).contDiffAt) _ M _ hM0
    (fun p hp => hM p (by omega)) fun cc => ?_
  set Q : Fin cc.length → Finset F.Cell :=
    fun i => {z} ∪ Finset.univ.biUnion fun a => scaledSlotCells c (t (cc.emb i a)) with hQ
  have hb : ∀ i, ‖iteratedFDeriv ℝ (cc.partSize i) (scaleAndValue (translatedObservable G V c X)) (x, 0)
      ((fun i => scaledSlotVector (t i)) ∘ cc.emb i)‖ ≤ B * Real.exp (-(r * cellSetDiameter (Q i))) := fun i =>
    iteratedFDeriv_scaleAndValue_le hk hB hr hx c X hX (fun a => t (cc.emb i a)) (fun a => ht _)
      (cc.partSize_pos i) ((cc.partSize_le i).trans hm)
  refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hb i).trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum]
  have hlen : (Finset.univ : Finset (Fin cc.length)).card ≤ m := by simpa using cc.length_le
  refine mul_le_mul (pow_le_pow_right₀ hB hlen) ?_ (Real.exp_pos _).le (by positivity)
  refine Real.exp_le_exp.2 ?_
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  refine neg_le_neg (mul_le_mul_of_nonneg_left ?_ hr)
  have h1 := cellSetDiameter_biUnion_le (Finset.univ : Finset (Fin cc.length)) Q (z := z)
    (fun i _ => by simp [hQ])
  have h2 : ({z} ∪ Finset.univ.biUnion fun i => scaledSlotCells c (t i) : Finset F.Cell) ⊆
      {z} ∪ Finset.univ.biUnion Q := by
    intro y hy
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_singleton] at hy
    rcases hy with hy | ⟨j, hj⟩
    · simp [hy]
    · obtain ⟨mi, a, rfl⟩ := cc.cover j
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_singleton]
      right
      exact ⟨mi, by
        simp only [hQ, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact Or.inr ⟨a, hj⟩⟩
  have h3 := (cellSetDiameter_mono h2).trans h1
  exact_mod_cast h3
end
section
open Set Filter Topology
open YangMills.Construction.BlockAverages
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.ScaledVariables
variable {F : BlockFrame}
def scaledCoord : Option (ChordCoord F) → ScaledPoint F →L[ℝ] ℝ
  | none => ContinuousLinearMap.fst ℝ ℝ _
  | some α => (chordCoord α).comp (ContinuousLinearMap.snd ℝ ℝ _)
def scaledBasis : Option (ChordCoord F) → ScaledPoint F
  | none => (1, 0)
  | some α => (0, chordBasis α)
theorem scaledBasis_expand (z : ScaledPoint F) : z = ∑ α, scaledCoord α z • scaledBasis α := by
  rw [Fintype.sum_option]
  refine Prod.ext ?_ ?_
  · simp [scaledCoord, scaledBasis, Prod.fst_sum]
  · simp only [scaledCoord, scaledBasis, Prod.snd_add, Prod.smul_snd, smul_zero, zero_add, Prod.snd_sum,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd']
    exact chordBasis_expand z.2
def scaledCoordDist (Y : F.Cell) : Option (ChordCoord F) → ℕ
  | none => 0
  | some α => cellSupDist (enclosingCell α.1.1.1) Y
def scaledCoordDecay (κ : ℝ) (Y : F.Cell) (α : Option (ChordCoord F)) : ℝ :=
  Real.exp (-(2 ^ 4 * κ * scaledCoordDist Y α))
def scaledCoordSlot {k : ℕ} : Option (ChordCoord F) → Option (ListSlot F k)
  | none => none
  | some α => some (Sum.inl (α.1, EuclideanSpace.single α.2 1))
theorem scaledBasis_eq_slotVector {k : ℕ} (α : Option (ChordCoord F)) :
    (scaledBasis α, (0 : Fin k → ℝ)) = scaledSlotVector (scaledCoordSlot α) := by
  cases α with
  | none => rfl
  | some α => simp [scaledBasis, scaledCoordSlot, scaledSlotVector, embedMap, slotVector, chordBasis]
theorem scaledCoordSlot_normalized {k : ℕ} (α : Option (ChordCoord F)) :
    IsNormalizedScaledSlot (scaledCoordSlot α : Option (ListSlot F k)) := by
  cases α with
  | none => trivial
  | some α => simp [scaledCoordSlot, IsNormalizedScaledSlot, IsNormalizedSlot]
variable {V : F.GaugeField F.top}
theorem bondSpread_zero {k j : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X 0 = 0 := by apply _root_.YangMills.Construction.ChartedEnergyRegularity.bondSpread_zero <;> assumption
theorem leftTranslate_zero {j : ℕ} (W : F.GaugeField j) :
    leftTranslate (0 : F.Site j → Fin 4 → imaginaryQuaternions) W = W := by apply _root_.YangMills.Construction.ChartedEnergyRegularity.leftTranslate_zero <;> assumption
theorem translatedObservable_zero {Zp : Type} (G : Zp → F.GaugeField F.top → ℝ) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (x : Zp) :
    translatedObservable G V c X (x, 0) = G x V := by
  simp [translatedObservable, bondSpread_zero, leftTranslate_zero]
def appendTopSlots {i k : ℕ} (tl : Fin i → Option (ListSlot F k)) : Fin (i + k) → Option (ListSlot F k) :=
  Fin.addCases tl fun j => some (Sum.inr j)
theorem iteratedFDeriv_gapJet_le {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {B r M : ℝ}
    {S : Set (StepVariable (finiteCells F))} {z : F.Cell}
    (hk : IsDecayingKernel V G B r {z} S 6) (hB : 1 ≤ B) (hr : 0 ≤ r) {x : ScaledPoint F} (hx : x.2 ∈ S) {k i : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) (hik : i + k ≤ 6)
    (vl : Fin i → ScaledPoint F) (tl : Fin i → Option (ListSlot F k))
    (hv : ∀ j, (vl j, (0 : Fin k → ℝ)) = scaledSlotVector (tl j))
    (ht : ∀ j, IsNormalizedScaledSlot (tl j)) (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ (6 : ℕ) g) (hM0 : 0 ≤ M)
    (hM : ∀ p, p ≤ 6 → ‖iteratedFDeriv ℝ p g (scaleAndValue (translatedObservable G V c X) (x, 0))‖ ≤ M) :
    |iteratedFDeriv ℝ i (partialJetRight (g ∘ scaleAndValue (translatedObservable G V c X)) 0 (unitParams k)) x vl| ≤
      (Fintype.card (OrderedFinpartition (i + k)) : ℝ) * (M * (B ^ (i + k) *
        Real.exp (-(r * cellSetDiameter ({z} ∪ Finset.univ.biUnion fun a =>
          scaledSlotCells c (appendTopSlots tl a)))))) := by
  have hR6 : ContDiffAt ℝ (6 : ℕ) (translatedObservable G V c X) (forgetScaleMap F k (x, 0)) := by
    have : forgetScaleMap F k (x, 0) = (x.2, 0) := by simp [forgetScaleMap]
    rw [this]
    exact hk.smooth k c X _ hx
  have hf6 : ContDiffAt ℝ (6 : ℕ) (scaleAndValue (translatedObservable G V c X)) (x, 0) :=
    (scaleCoordMap F k).contDiff.contDiffAt.prodMk
      (ContDiffAt.comp (x, (0 : Fin k → ℝ)) (g := translatedObservable G V c X) hR6
        (forgetScaleMap F k).contDiff.contDiffAt)
  have hc : ContDiffAt ℝ (6 : ℕ) (g ∘ scaleAndValue (translatedObservable G V c X)) (x, 0) :=
    hg.contDiffAt.comp _ hf6
  have hlist := iteratedFDeriv_partialJetRight (unitParams k) i (i + k) vl
    (fun a => scaledSlotVector (appendTopSlots tl a)) x
    ⟨rfl, fun a ha => ?_, fun a ha hk' => ?_⟩ hc hik
  · rw [hlist]
    exact iteratedFDeriv_comp_scaleAndValue_le hk hB hr hx c X hX (appendTopSlots tl) (fun a => by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) a
      · simpa [appendTopSlots] using ht j
      · simp [appendTopSlots, IsNormalizedScaledSlot, IsNormalizedSlot]) hik g hg hM0 hM
  · have this : a = Fin.castAdd k ⟨a.val, ha⟩ := Fin.ext rfl
    conv_lhs => rw [this]
    simp only [appendTopSlots, Fin.addCases_left]
    exact (hv _).symm
  · have this : a = Fin.natAdd i ⟨a.val - i, hk'⟩ := Fin.ext (by simp; omega)
    conv_lhs => rw [this]
    simp only [appendTopSlots, Fin.addCases_right]
    simp [scaledSlotVector, embedMap, slotVector]
variable {κ ρ l₁ : ℝ} {Y : F.Cell}
def gapJetConstant (M B : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 7, (Fintype.card (OrderedFinpartition m) : ℝ) * (M * B ^ m)
theorem iteratedFDeriv_gapJet_le_prod {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {B r M : ℝ}
    {S : Set (StepVariable (finiteCells F))} (hk : IsDecayingKernel V G B r {Y} S 6) (hB : 1 ≤ B) (hκ : 0 < κ)
    (hr : 0 ≤ r) (hM0 : 0 ≤ M) {x : ScaledPoint F} (hx : x.2 ∈ S) {k i : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) (hik : i + k ≤ 6)
    (vl : Fin i → ScaledPoint F) (tl : Fin i → Option (ListSlot F k))
    (hv : ∀ j, (vl j, (0 : Fin k → ℝ)) = scaledSlotVector (tl j))
    (ht : ∀ j, IsNormalizedScaledSlot (tl j)) (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ (6 : ℕ) g)
    (hM : ∀ p, p ≤ 6 → ‖iteratedFDeriv ℝ p g (scaleAndValue (translatedObservable G V c X) (x, 0))‖ ≤ M)
    {ι : Type} (I : Finset ι) (d : ι → ℕ) {s₀ : ℕ}
    (hd : ∀ a ∈ I, d a ≤ cellSetDiameter ({Y} ∪ Finset.univ.biUnion fun a => scaledSlotCells c (appendTopSlots tl a)))
    (hs₀ : s₀ ≤ cellSetDiameter ({Y} ∪ Finset.univ.biUnion fun a => scaledSlotCells c (appendTopSlots tl a)))
    (hc : ((I.card : ℝ) + 2) * (2 ^ 4 * κ) ≤ r) :
    |iteratedFDeriv ℝ i (partialJetRight (g ∘ scaleAndValue (translatedObservable G V c X)) 0 (unitParams k)) x vl| ≤
      gapJetConstant M B * (∏ a ∈ I, Real.exp (-(2 ^ 4 * κ * d a))) * Real.exp (-(2 ^ 4 * κ * s₀)) := by
  have h1 := iteratedFDeriv_gapJet_le hk hB hr hx c X hX hik vl tl hv ht g hg hM0 hM
  have h2 := exp_diameter_le (d₀ := 0) (s₀ := s₀) hκ I d hd (Nat.zero_le _) hs₀ hc
  simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, one_mul] at h2
  have hterm : (Fintype.card (OrderedFinpartition (i + k)) : ℝ) * (M * B ^ (i + k)) ≤ gapJetConstant M B :=
    Finset.single_le_sum (f := fun m => (Fintype.card (OrderedFinpartition m) : ℝ) * (M * B ^ m))
      (fun m _ => by positivity) (Finset.mem_range.2 (by omega))
  refine h1.trans ?_
  have hG0 : 0 ≤ gapJetConstant M B := le_trans (by positivity) hterm
  calc (Fintype.card (OrderedFinpartition (i + k)) : ℝ) * (M * (B ^ (i + k) *
        Real.exp (-(r * cellSetDiameter ({Y} ∪ Finset.univ.biUnion fun a =>
          scaledSlotCells c (appendTopSlots tl a))))))
      = ((Fintype.card (OrderedFinpartition (i + k)) : ℝ) * (M * B ^ (i + k))) *
        Real.exp (-(r * cellSetDiameter ({Y} ∪ Finset.univ.biUnion fun a =>
          scaledSlotCells c (appendTopSlots tl a)))) := by ring
    _ ≤ gapJetConstant M B * ((∏ a ∈ I, Real.exp (-(2 ^ 4 * κ * d a))) * Real.exp (-(2 ^ 4 * κ * s₀))) :=
        mul_le_mul hterm h2 (Real.exp_pos _).le hG0
    _ = _ := by ring
theorem mem_appendTopSlots_cells {k i : ℕ} (c : Fin k → F.Site F.top × Fin 4) (tl : Fin i → Option (ListSlot F k))
    (a : Fin i) {u : F.Cell} (hu : u ∈ scaledSlotCells c (tl a)) :
    u ∈ ({Y} ∪ Finset.univ.biUnion fun a => scaledSlotCells c (appendTopSlots tl a) : Finset F.Cell) := by
  refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨Fin.castAdd k a, Finset.mem_univ _, ?_⟩)
  simpa [appendTopSlots] using hu
theorem mem_appendTopSlots_top {k i : ℕ} (c : Fin k → F.Site F.top × Fin 4) (tl : Fin i → Option (ListSlot F k))
    (l : Fin k) :
    (c l).1 ∈ ({Y} ∪ Finset.univ.biUnion fun a => scaledSlotCells c (appendTopSlots tl a) : Finset F.Cell) := by
  refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨Fin.natAdd i l, Finset.mem_univ _, ?_⟩)
  simp [appendTopSlots, scaledSlotCells, slotCell]
theorem scaledCoordDist_le_diameter {k i : ℕ} (c : Fin k → F.Site F.top × Fin 4) (σ : Fin i → Option (ChordCoord F))
    (tl : Fin i → Option (ListSlot F k)) (htl : ∀ j, tl j = scaledCoordSlot (σ j)) (a : Fin i) :
    scaledCoordDist Y (σ a) ≤
      cellSetDiameter ({Y} ∪ Finset.univ.biUnion fun a => scaledSlotCells c (appendTopSlots tl a)) := by
  have hY : Y ∈ ({Y} ∪ Finset.univ.biUnion fun a => scaledSlotCells c (appendTopSlots tl a) : Finset F.Cell) := by
    simp
  cases h : σ a with
  | none => simp [scaledCoordDist]
  | some α =>
    refine cellSupDist_le_diameter (mem_appendTopSlots_cells c tl a ?_) hY
    rw [htl, h]
    simp [scaledCoordSlot, scaledSlotCells, slotCell]
theorem scaledCoord_ne_zero {b : ↥(chordBonds (finiteCells F))} {e : BondVector} {α : Option (ChordCoord F)}
    (h : scaledCoord α (ContinuousLinearMap.inr ℝ ℝ _ (bondVariation b e)) ≠ 0) :
    ∃ α', α = some α' ∧ α'.1 = b := by
  cases α with
  | none => exact absurd (by simp [scaledCoord]) h
  | some α' => exact ⟨α', rfl, chordCoord_ne_zero_bond (e := e) (by simpa [scaledCoord] using h)⟩
theorem decayingPart_gap {Lg : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {B r M : ℝ}
    {S : Set (StepVariable (finiteCells F))} (hk : IsDecayingKernel V Lg B r {Y} S 6) (hB : 1 ≤ B) (hκ : 0 < κ)
    (hr : 2 ^ 7 * κ ≤ r) (hl₁ : l₁ ≤ 1) (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ (6 : ℕ) g) (hM0 : 0 ≤ M)
    (hM : ∀ η ∈ S, ∀ s : ℝ, |s| ≤ 1 → ∀ p, p ≤ 6 → ‖iteratedFDeriv ℝ p g (s, Lg η V)‖ ≤ M)
    (hS : ∀ p ∈ scaleBallSet F ρ, p.1 • p.2 ∈ S) :
    IsDecayingPart κ ρ l₁ Y V
      (rayObservable (fun (x : ScaledPoint F) V' => g (x.1, Lg x.2 V')) (fun ζ => ((1 : ℝ), ζ)) (fun _ => 1))
      (fun ζ => |(1 : ℝ)| * gapJetConstant M B *
        (1 + ∑ α, |scaledCoord α ((1 : ℝ), ζ)| * scaledCoordDecay κ Y α) ^ 3)
      (fun _ ζ => (0 + |(1 : ℝ)| * (3 * 3 + 1)) * gapJetConstant M B *
        (1 + ∑ α, |scaledCoord α ((1 : ℝ), ζ)| * scaledCoordDecay κ Y α) ^ 3) := by
  have hr0 : 0 ≤ r := le_trans (by positivity) hr
  have htop : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      translatedObservable (fun (x : ScaledPoint F) V' => g (x.1, Lg x.2 V')) V c X =
        g ∘ scaleAndValue (translatedObservable Lg V c X) :=
    fun c X => funext fun p => by simp [translatedObservable, scaleAndValue, scaleCoordMap, forgetScaleMap]
  have hS' : ∀ p ∈ scaleBallSet F ρ, p.1 • ((1 : ℝ), p.2) ∈ {x : ScaledPoint F | x.2 ∈ S} := by
    intro p hp
    simpa using hS p hp
  have hG : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      ∀ x ∈ {x : ScaledPoint F | x.2 ∈ S},
      ContDiffAt ℝ (6 : ℕ) (translatedObservable (fun (x : ScaledPoint F) V' => g (x.1, Lg x.2 V')) V c X)
        (x, 0) := by
    intro k c X x hx
    rw [htop]
    have hR6 : ContDiffAt ℝ (6 : ℕ) (translatedObservable Lg V c X) (forgetScaleMap F k (x, 0)) := by
      have : forgetScaleMap F k (x, 0) = (x.2, 0) := by simp [forgetScaleMap]
      rw [this]
      exact hk.smooth k c X _ hx
    have hf6 : ContDiffAt ℝ (6 : ℕ) (scaleAndValue (translatedObservable Lg V c X)) (x, 0) :=
      (scaleCoordMap F k).contDiff.contDiffAt.prodMk
        (ContDiffAt.comp (x, (0 : Fin k → ℝ)) (g := translatedObservable Lg V c X) hR6
          (forgetScaleMap F k).contDiff.contDiffAt)
    exact hg.contDiffAt.comp _ hf6
  have hterm : 0 ≤ gapJetConstant M B := by
    refine Finset.sum_nonneg fun m _ => ?_
    have : 0 ≤ B := by linarith
    positivity
  have hxS : ∀ {l : ℝ} {ζ : StepVariable (finiteCells F)}, 0 < l → MemScaledBalls ρ l ζ →
      (l • ((1 : ℝ), ζ) : ScaledPoint F).2 ∈ S := fun hl hb => by
    simpa using hS _ (mem_scaleBallSet hl hb)
  have hMx : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {l : ℝ}
      {ζ : StepVariable (finiteCells F)}, 0 < l → l ≤ l₁ → MemScaledBalls ρ l ζ → ∀ p, p ≤ 6 →
      ‖iteratedFDeriv ℝ p g (scaleAndValue (translatedObservable Lg V c X) ((l • ((1 : ℝ), ζ) : ScaledPoint F), 0))‖
        ≤ M := by
    intro k c X l ζ hl hl' hb p hp
    have e : scaleAndValue (translatedObservable Lg V c X) ((l • ((1 : ℝ), ζ) : ScaledPoint F), 0) =
        (l, Lg (l • ζ) V) := by
      simp [scaleAndValue, scaleCoordMap, forgetScaleMap, translatedObservable_zero]
    rw [e]
    refine hM _ (by simpa using hxS hl hb) l ?_ p hp
    rw [abs_of_pos hl]
    linarith
  have hc2 : ∀ {i : ℕ}, i ≤ 3 → ((i : ℝ) + 2) * (2 ^ 4 * κ) ≤ r := by
    intro i hi
    have : (i : ℝ) ≤ 3 := by exact_mod_cast hi
    nlinarith
  have hi3 : ∀ {k i : ℕ}, IsControlledOrder k i → i ≤ 3 := by
    intro k i h
    rcases h with h | h <;> omega
  have hYmem : ∀ {k i : ℕ} (c : Fin k → F.Site F.top × Fin 4) (tl : Fin i → Option (ListSlot F k)),
      Y ∈ ({Y} ∪ Finset.univ.biUnion fun a => scaledSlotCells c (appendTopSlots tl a) : Finset F.Cell) :=
    fun _ _ => by simp
  refine decayingPart_of_ray (ray := fun ζ => ((1 : ℝ), ζ)) (contDiff_const.prodMk contDiff_id) contDiff_const hS' hG
    (ContinuousLinearMap.inr ℝ ℝ _) (fun ζ δ s => by simp [Prod.ext_iff]) scaledCoord scaledBasis
    scaledBasis_expand (scaledCoordDecay κ Y)
    (fun _ => (Real.exp_pos _).le) _ 3 hterm hl₁ ?_ (fun _ _ => 0) (fun b e ζ _ => by simp) ?_ ?_ ?_ ?_
  · intro b e he
    rw [Fintype.sum_option]
    have := sum_abs_chordCoord_le_three b e he
    simpa [scaledCoord] using this
  · intro k i c X l ζ σ hki hX hl hl' hb
    have hik := controlledOrder_le hki
    simp only [translatedJet]
    rw [htop]
    exact iteratedFDeriv_gapJet_le_prod hk hB hκ hr0 hM0 (hxS hl hb) c X hX (by omega) (fun j => scaledBasis (σ j))
      (fun j => scaledCoordSlot (σ j)) (fun j => scaledBasis_eq_slotVector _) (fun j => scaledCoordSlot_normalized _)
      g hg (hMx c X hl hl' hb)
      Finset.univ (fun a => scaledCoordDist Y (σ a)) (s₀ := bondSpan Y c)
      (fun a _ => scaledCoordDist_le_diameter c σ _ (fun _ => rfl) a)
      (bondSpan_le_diameter (hYmem c _) fun l' => mem_appendTopSlots_top c _ l') (by simpa using hc2 (hi3 hki))
  · intro k i c X l ζ σ b e hki hX hl hl' hb he hz
    exact absurd (by simp) hz
  · intro k i c X l ζ σ b e j hki hX hl hl' hb he hz
    have hik := controlledOrder_le hki
    obtain ⟨α', hα, hαb⟩ := scaledCoord_ne_zero hz
    simp only [translatedJet]
    rw [htop]
    have hbmem : enclosingCell b.1.1 ∈ ({Y} ∪ Finset.univ.biUnion fun a => scaledSlotCells c (appendTopSlots
        (fun j => (scaledCoordSlot (σ j) : Option (ListSlot F k))) a) : Finset F.Cell) := by
      refine mem_appendTopSlots_cells c _ j ?_
      simp [hα, scaledCoordSlot, scaledSlotCells, slotCell, hαb]
    exact iteratedFDeriv_gapJet_le_prod hk hB hκ hr0 hM0 (hxS hl hb) c X hX (by omega) (fun j => scaledBasis (σ j))
      (fun j => scaledCoordSlot (σ j)) (fun j => scaledBasis_eq_slotVector _) (fun j => scaledCoordSlot_normalized _)
      g hg (hMx c X hl hl' hb)
      (Finset.univ.erase j) (fun a => scaledCoordDist Y (σ a))
      (s₀ := bondSpan Y (Fin.cons (enclosingCell b.1.1, 0) c : Fin (k + 1) → F.Site F.top × Fin 4))
      (fun a _ => scaledCoordDist_le_diameter c σ _ (fun _ => rfl) a)
      (bondSpan_le_diameter (hYmem c _) fun l' => by
        refine Fin.cases ?_ (fun l'' => ?_) l'
        · exact hbmem
        · exact mem_appendTopSlots_top c _ l'')
      (by
        have h1 : ((Finset.univ.erase j).card : ℝ) = ((i - 1 : ℕ) : ℝ) := by simp
        rw [h1]
        exact hc2 (by have := hi3 hki; omega))
  · intro k i c X l ζ σ b e hki hX hl hl' hb he
    have hik := controlledOrder_le hki
    simp only [translatedJet]
    rw [htop]
    set tl : Fin (i + 1) → Option (ListSlot F k) :=
      Fin.cons (some (Sum.inl (b, e))) fun j => scaledCoordSlot (σ j) with htl
    have hbmem : enclosingCell b.1.1 ∈
        ({Y} ∪ Finset.univ.biUnion fun a => scaledSlotCells c (appendTopSlots tl a) : Finset F.Cell) := by
      refine mem_appendTopSlots_cells c tl 0 ?_
      simp [htl, scaledSlotCells, slotCell]
    refine iteratedFDeriv_gapJet_le_prod hk hB hκ hr0 hM0 (hxS hl hb) c X hX (by omega) _ tl (fun j => ?_)
      (fun j => ?_) g hg (hMx c X hl hl' hb) Finset.univ (fun a => scaledCoordDist Y (σ a))
      (s₀ := bondSpan Y (Fin.cons (enclosingCell b.1.1, 0) c : Fin (k + 1) → F.Site F.top × Fin 4))
      (fun a _ => ?_)
      (bondSpan_le_diameter (hYmem c _) fun l' => by
        refine Fin.cases ?_ (fun l'' => ?_) l'
        · exact hbmem
        · exact mem_appendTopSlots_top c _ l'')
      (by simpa using hc2 (hi3 hki))
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [htl, scaledSlotVector, embedMap, slotVector]
      · simpa [htl] using scaledBasis_eq_slotVector (k := k) (σ j')
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simpa [htl, IsNormalizedScaledSlot, IsNormalizedSlot] using he
      · simpa [htl] using scaledCoordSlot_normalized (k := k) (σ j')
    · have hY' : Y ∈ ({Y} ∪ Finset.univ.biUnion fun a => scaledSlotCells c (appendTopSlots tl a) : Finset F.Cell) := by
        simp
      cases h : σ a with
      | none => simp [scaledCoordDist]
      | some α =>
        refine cellSupDist_le_diameter (mem_appendTopSlots_cells c tl a.succ ?_) hY'
        simp [htl, h, scaledCoordSlot, scaledSlotCells, slotCell]
end
section
open Set Filter Topology MeasureTheory
open scoped Interval
open YangMills.Construction.BlockAverages
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.ScaledVariables
variable {F : BlockFrame}
theorem secondDerivAlong_eq {Ψ : StepVariable (finiteCells F) → ℝ} {η : StepVariable (finiteCells F)}
    (h : ContDiffAt ℝ 2 Ψ η) (u w : StepVariable (finiteCells F)) :
    secondDerivAlong Ψ η u w = fderiv ℝ (fderiv ℝ Ψ) η w u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ Ψ) η :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply_eq hd]
  rfl
theorem bondVariation_expand (b : ↥(chordBonds (finiteCells F))) (e : BondVector) :
    (bondVariation b e : StepVariable (finiteCells F)) = ∑ a : Fin 3, e a • chordBasis (b, a) := by
  funext b'
  ext a'
  have h2 : (∑ a : Fin 3, e a • chordBasis (b, a) : StepVariable (finiteCells F)) b' a' =
      ∑ a : Fin 3, ((e a • chordBasis (b, a) : StepVariable (finiteCells F)) b') a' := by
    simp [Finset.sum_apply]
  rw [h2]
  by_cases hb : b' = b
  · subst hb
    simp [bondVariation, chordBasis, Finset.sum_ite_eq]
  · simp [bondVariation, chordBasis, Pi.single_apply, hb]
theorem secondDerivAlong_expand {Ψ : StepVariable (finiteCells F) → ℝ} {η : StepVariable (finiteCells F)}
    (h : ContDiffAt ℝ 2 Ψ η) (b : ↥(chordBonds (finiteCells F))) (ζ : StepVariable (finiteCells F)) :
    secondDerivAlong Ψ η (bondVariation b (ζ b)) ζ =
      ∑ a : Fin 3, ∑ β : ChordCoord F, (ζ b a * chordCoord β ζ) *
        secondDerivAlong Ψ η (chordBasis (b, a)) (chordBasis β) := by
  set T := fderiv ℝ (fderiv ℝ Ψ) η with hT
  have h1 : T ζ = (∑ β : ChordCoord F, chordCoord β ζ • T (chordBasis β) :
      StepVariable (finiteCells F) →L[ℝ] ℝ) := by
    conv_lhs => rw [chordBasis_expand ζ]
    simp [map_sum, map_smul]
  rw [secondDerivAlong_eq h, ← hT, h1, bondVariation_expand]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    map_sum, map_smul, smul_eq_mul, secondDerivAlong_eq h, ← hT]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring
variable {V : F.GaugeField F.top} {κ ρ l₁ : ℝ} {Y : F.Cell}
def chordCoordProduct (α β : ChordCoord F) (ζ : StepVariable (finiteCells F)) : ℝ :=
  chordCoord α ζ * chordCoord β ζ
theorem chordCoordProduct_contDiff (α β : ChordCoord F) : ContDiff ℝ (6 : ℕ) (chordCoordProduct α β) :=
  (chordCoord α).contDiff.mul (chordCoord β).contDiff
theorem abs_chordCoord_bondVariation_le (α : ChordCoord F) (b : ↥(chordBonds (finiteCells F))) (e : BondVector)
    (he : ‖e‖ = 1) : |chordCoord α (bondVariation b e)| ≤ if α.1 = b then 1 else 0 := by
  by_cases h : α.1 = b
  · subst h
    rw [if_pos rfl]
    have h1 : chordCoord α (bondVariation α.1 e) = e α.2 := by simp [chordCoord_apply, bondVariation]
    rw [h1, ← he]
    exact PiLp.norm_apply_le e α.2
  · rw [if_neg h]
    have h1 : chordCoord α (bondVariation b e) = 0 := by
      simp [chordCoord_apply, bondVariation, Pi.single_apply, h]
    simp [h1]
theorem chordCoordProduct_fderiv (α β : ChordCoord F) (ζ δ : StepVariable (finiteCells F)) :
    fderiv ℝ (chordCoordProduct α β) ζ δ = chordCoord α δ * chordCoord β ζ + chordCoord α ζ * chordCoord β δ := by
  have h := ((chordCoord α).hasFDerivAt (x := ζ)).mul ((chordCoord β).hasFDerivAt (x := ζ))
  have h2 : HasFDerivAt (fun x => chordCoord α x * chordCoord β x)
      (chordCoord α ζ • chordCoord β + chordCoord β ζ • chordCoord α) ζ := h
  have e : chordCoordProduct α β = (fun x => chordCoord α x * chordCoord β x) := rfl
  rw [e, h2.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  ring
def productSlopeBound (α β : ChordCoord F) (b : ↥(chordBonds (finiteCells F))) (ζ : StepVariable (finiteCells F)) :
    ℝ :=
  (if α.1 = b then |chordCoord β ζ| else 0) + (if β.1 = b then |chordCoord α ζ| else 0)
theorem abs_fderiv_chordCoordProduct_le (α β : ChordCoord F) (b : ↥(chordBonds (finiteCells F))) (e : BondVector)
    (ζ : StepVariable (finiteCells F)) (he : ‖e‖ = 1) :
    |fderiv ℝ (chordCoordProduct α β) ζ (bondVariation b e)| ≤ productSlopeBound α β b ζ := by
  rw [chordCoordProduct_fderiv]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    have h1 := abs_chordCoord_bondVariation_le α b e he
    by_cases h : α.1 = b
    · rw [if_pos h] at h1 ⊢
      calc _ ≤ 1 * |chordCoord β ζ| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = _ := one_mul _
    · rw [if_neg h] at h1 ⊢
      have : |chordCoord α (bondVariation b e)| = 0 := le_antisymm h1 (abs_nonneg _)
      simp [this]
  · rw [abs_mul, mul_comm]
    have h1 := abs_chordCoord_bondVariation_le β b e he
    by_cases h : β.1 = b
    · rw [if_pos h] at h1 ⊢
      calc _ ≤ 1 * |chordCoord α ζ| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = _ := one_mul _
    · rw [if_neg h] at h1 ⊢
      have : |chordCoord β (bondVariation b e)| = 0 := le_antisymm h1 (abs_nonneg _)
      simp [this]
theorem cellSupDist_self_eq_zero (x : F.Cell) : cellSupDist x x = 0 := cellSupDist_self x
theorem decayingPart_quadTerm {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {B r : ℝ}
    {S : Set (StepVariable (finiteCells F))} {α β : ChordCoord F}
    (hk : IsDecayingKernel V G B r {enclosingCell α.1.1.1, enclosingCell β.1.1.1} S 6) (hB : 0 ≤ B) (hκ : 0 < κ)
    (hr : 2 ^ 7 * κ ≤ r) (hl₁ : l₁ ≤ 1)
    (hS : ∀ p ∈ scaleBallSet F ρ, p.1 • p.2 ∈ S) (hα : enclosingCell α.1.1.1 = Y) :
    IsDecayingPart κ ρ l₁ Y V (rayObservable G id (chordCoordProduct α β))
      (fun ζ => |chordCoordProduct α β ζ| * (B * coordDecay κ Y β) *
        (1 + ∑ γ, |chordCoord γ (id ζ)| * coordDecay κ Y γ) ^ 3)
      (fun b ζ => (productSlopeBound α β b ζ + |chordCoordProduct α β ζ| * (3 * 3 + 1)) * (B * coordDecay κ Y β) *
        (1 + ∑ γ, |chordCoord γ (id ζ)| * coordDecay κ Y γ) ^ 3) := by
  have hd₀ : cellSupDist (enclosingCell β.1.1.1) Y ≤
      cellSetDiameter {enclosingCell α.1.1.1, enclosingCell β.1.1.1} :=
    cellSupDist_le_diameter (by simp) (by simp [hα])
  refine decayingPart_of_kernel hk hB hκ hr hl₁ (by simp [hα]) hd₀ (chordCoordProduct_contDiff α β) _
    (fun b e ζ he => abs_fderiv_chordCoordProduct_le α β b e ζ he) (fun b e ζ he hz => ?_) hS
  have h1 : chordCoord α (bondVariation b e) ≠ 0 ∨ chordCoord β (bondVariation b e) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hz (by rw [chordCoordProduct_fderiv, hcon.1, hcon.2]; ring)
  rcases h1 with h1 | h1
  · have := chordCoord_ne_zero_bond h1
    simp [← this]
  · have := chordCoord_ne_zero_bond h1
    simp [← this]
def quadraticPart (E : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (Y : F.Cell) :
    ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  fun l ζ V' => ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
    ∫ v in (0 : ℝ)..1, (1 - v) * secondDerivAlong (fun η' => E η' V') ((v * l) • ζ) (bondVariation b (ζ b)) ζ else 0
def quadraticIndex (F : BlockFrame) (Y : F.Cell) : Finset (ChordCoord F × ChordCoord F) :=
  (Finset.univ.filter fun α : ChordCoord F => enclosingCell α.1.1.1 = Y) ×ˢ Finset.univ
theorem quadraticPart_eventuallyEq {E : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {B r : ℝ}
    {S : Set (StepVariable (finiteCells F))} (h : IsDecayingEnergy V E B r S)
    (hstar : ∀ η ∈ S, ∀ v ∈ Icc (0 : ℝ) 1, v • η ∈ S)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (p : ℝ × StepVariable (finiteCells F)) (hp : p.1 • p.2 ∈ S) :
    scaledObservable (quadraticPart E Y) V c X =ᶠ[𝓝 (p, 0)] scaledObservable (fun l ζ V' => ∑ q ∈ quadraticIndex F Y,
      rayObservable (taylorRemainderMean (secondDerivKernel E q.1 q.2)) id (chordCoordProduct q.1 q.2) l ζ V') V c X := by
  classical
  set Sh := translatedObservable E V c X with hSh
  have h8 : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (8 : ℕ) Sh (v • (p.1 • p.2), 0) :=
    fun v hv => h.smooth k c X _ (hstar _ hp v hv)
  have hev : ∀ᶠ y in 𝓝 ((p, 0) : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)), ∀ v ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ (8 : ℕ) Sh (v • (y.1.1 • y.1.2), y.2) := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually
      (P := fun (y : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)) (v : ℝ) =>
        ContDiffAt ℝ (8 : ℕ) Sh (v • (y.1.1 • y.1.2), y.2)) fun v hv => ?_
    have h1 : ∀ᶠ w in 𝓝 ((v • (p.1 • p.2), 0) : StepVariable (finiteCells F) × (Fin k → ℝ)),
        ContDiffAt ℝ (8 : ℕ) Sh w := (h8 v hv).eventually (by simp)
    have h2 : Continuous fun z : ((ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)) × ℝ =>
        ((z.2 • (z.1.1.1 • z.1.1.2), z.1.2) : StepVariable (finiteCells F) × (Fin k → ℝ)) := by fun_prop
    exact (h2.tendsto (((p, 0), v) : ((ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)) × ℝ)).eventually h1
  filter_upwards [hev] with y hy
  obtain ⟨⟨l, ζ⟩, q⟩ := y
  simp only at hy
  simp only [scaledObservable, quadraticPart, rayObservable, id]
  set V' := leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X q) V with hV'
  have hΨ : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 (fun η' => E η' V') (v • (l • ζ)) := by
    intro v hv
    have h2 : ContDiffAt ℝ (8 : ℕ) (fun η' => Sh (η', q)) (v • (l • ζ)) :=
      ContDiffAt.comp (v • (l • ζ)) (g := Sh) (hy v hv) (by fun_prop)
    exact h2.of_le (by norm_num)
  have hcontOn : ∀ α β : ChordCoord F, ContinuousOn
      (fun v : ℝ => (1 - v) * secondDerivKernel E α β (v • (l • ζ)) V') (Icc 0 1) := by
    intro α β v hv
    have h3 : ContDiffAt ℝ (0 : ℕ) (translatedObservable (secondDerivKernel E α β) V c X) (v • (l • ζ), q) := by
      rw [translatedObservable_secondDerivKernel]
      exact contDiffAt_secondPartialLeft (M := 0) (N := 8) (by norm_num) _ _ (hy v hv)
    have h4 : ContinuousAt (fun v' : ℝ => secondDerivKernel E α β (v' • (l • ζ)) V') v := by
      have h5 := h3.continuousAt
      exact ContinuousAt.comp (f := fun v' : ℝ => (v' • (l • ζ), q))
        (g := translatedObservable (secondDerivKernel E α β) V c X) h5 (by fun_prop)
    exact (ContinuousAt.mul (by fun_prop) h4).continuousWithinAt
  have hcont : ∀ α β : ChordCoord F, IntervalIntegrable
      (fun v : ℝ => (1 - v) * secondDerivKernel E α β (v • (l • ζ)) V') volume 0 1 := by
    intro α β
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact hcontOn α β
  have hb : ∀ b : ↥(chordBonds (finiteCells F)),
      ∫ v in (0 : ℝ)..1, (1 - v) * secondDerivAlong (fun η' => E η' V') ((v * l) • ζ) (bondVariation b (ζ b)) ζ =
        ∑ a : Fin 3, ∑ β : ChordCoord F, chordCoordProduct (b, a) β ζ *
          taylorRemainderMean (secondDerivKernel E (b, a) β) (l • ζ) V' := by
    intro b
    have e1 : ∫ v in (0 : ℝ)..1, (1 - v) * secondDerivAlong (fun η' => E η' V') ((v * l) • ζ)
          (bondVariation b (ζ b)) ζ =
        ∫ v in (0 : ℝ)..1, ∑ a : Fin 3, ∑ β : ChordCoord F, chordCoordProduct (b, a) β ζ *
          ((1 - v) * secondDerivKernel E (b, a) β (v • (l • ζ)) V') := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [uIcc_of_le zero_le_one] at hv
      have e2 : (v * l) • ζ = v • (l • ζ) := by rw [smul_smul]
      simp only [e2]
      rw [secondDerivAlong_expand (hΨ v hv), Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      simp only [chordCoordProduct, secondDerivKernel, chordCoord_apply]
      ring
    rw [e1, intervalIntegral.integral_finsetSum (fun a _ => ?_)]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [intervalIntegral.integral_finsetSum (fun β _ => (hcont (b, a) β).const_mul _)]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [intervalIntegral.integral_const_mul]
      rfl
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le zero_le_one]
      exact continuousOn_finset_sum _ fun β _ => continuousOn_const.mul (hcontOn (b, a) β)
  simp only [hb, quadraticIndex]
  rw [Finset.sum_product, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with hbY
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [hbY]
  · symm
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [hbY]
def quadraticBound (κ : ℝ) (Y : F.Cell) (B : ℝ) (ζ : StepVariable (finiteCells F)) : ℝ :=
  ∑ q ∈ quadraticIndex F Y, |chordCoordProduct q.1 q.2 ζ| * (B * coordDecay κ Y q.2) *
    (1 + ∑ γ, |chordCoord γ (id ζ)| * coordDecay κ Y γ) ^ 3
def quadraticSlopeBound (κ : ℝ) (Y : F.Cell) (B : ℝ) (b : ↥(chordBonds (finiteCells F)))
    (ζ : StepVariable (finiteCells F)) : ℝ :=
  ∑ q ∈ quadraticIndex F Y, (productSlopeBound q.1 q.2 b ζ + |chordCoordProduct q.1 q.2 ζ| * (3 * 3 + 1)) *
    (B * coordDecay κ Y q.2) * (1 + ∑ γ, |chordCoord γ (id ζ)| * coordDecay κ Y γ) ^ 3
theorem decayingPart_quadSum {G : ChordCoord F × ChordCoord F → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {B r : ℝ} {S : Set (StepVariable (finiteCells F))}
    (hk : ∀ q ∈ quadraticIndex F Y,
      IsDecayingKernel V (G q) B r {enclosingCell q.1.1.1.1, enclosingCell q.2.1.1.1} S 6)
    (hB : 0 ≤ B) (hκ : 0 < κ) (hr : 2 ^ 7 * κ ≤ r) (hl₁ : l₁ ≤ 1)
    (hS : ∀ p ∈ scaleBallSet F ρ, p.1 • p.2 ∈ S) :
    IsDecayingPart κ ρ l₁ Y V
      (fun l ζ V' => ∑ q ∈ quadraticIndex F Y, rayObservable (G q) id (chordCoordProduct q.1 q.2) l ζ V')
      (quadraticBound κ Y B) (quadraticSlopeBound κ Y B) := by
  refine IsDecayingPart.sum (quadraticIndex F Y) fun q hq => ?_
  have hα : enclosingCell q.1.1.1.1 = Y := by
    have := (Finset.mem_product.1 hq).1
    simpa using this
  exact decayingPart_quadTerm (hk q hq) hB hκ hr hl₁ hS hα
theorem coordDecay_nonneg (κ : ℝ) (Y : F.Cell) (γ : ChordCoord F) : 0 ≤ coordDecay κ Y γ := (Real.exp_pos _).le
theorem coordDecay_le_one (hκ : 0 < κ) (Y : F.Cell) (γ : ChordCoord F) : coordDecay κ Y γ ≤ 1 := by
  refine Real.exp_le_one_iff.2 ?_
  have : (0 : ℝ) ≤ 2 ^ 4 * κ * cellSupDist (enclosingCell γ.1.1.1) Y := by positivity
  linarith
theorem coordDecay_of_cell (κ : ℝ) {γ : ChordCoord F} (h : enclosingCell γ.1.1.1 = Y) : coordDecay κ Y γ = 1 := by
  simp [coordDecay, h, cellSupDist_self_eq_zero]
theorem sum_ite_chordCoord_bond (b : ↥(chordBonds (finiteCells F))) :
    ∑ γ : ChordCoord F, (if γ.1 = b then (1 : ℝ) else 0) = 3 := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp
  · intro b' _ hne
    simp [hne]
  · simp
theorem sum_abs_chordCoord_cell_le (hκ : 0 < κ) (ζ : StepVariable (finiteCells F)) :
    ∑ α ∈ Finset.univ.filter (fun α : ChordCoord F => enclosingCell α.1.1.1 = Y), |chordCoord α ζ| ≤
      ∑ γ, |chordCoord γ (id ζ)| * coordDecay κ Y γ := by
  calc ∑ α ∈ Finset.univ.filter (fun α : ChordCoord F => enclosingCell α.1.1.1 = Y), |chordCoord α ζ|
      = ∑ α ∈ Finset.univ.filter (fun α : ChordCoord F => enclosingCell α.1.1.1 = Y),
          |chordCoord α (id ζ)| * coordDecay κ Y α := by
        refine Finset.sum_congr rfl fun α hα => ?_
        rw [coordDecay_of_cell κ (Finset.mem_filter.1 hα).2]
        simp
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun γ _ _ => mul_nonneg (abs_nonneg _) (coordDecay_nonneg κ Y γ)
theorem quadraticBound_le (hκ : 0 < κ) {B : ℝ} (hB : 0 ≤ B) (ζ : StepVariable (finiteCells F)) :
    quadraticBound κ Y B ζ ≤ B * (∑ γ, |chordCoord γ (id ζ)| * coordDecay κ Y γ) ^ 2 *
      (1 + ∑ γ, |chordCoord γ (id ζ)| * coordDecay κ Y γ) ^ 3 := by
  set A := ∑ γ, |chordCoord γ (id ζ)| * coordDecay κ Y γ with hA
  set P := (1 + A) ^ 3 with hP
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun γ _ => mul_nonneg (abs_nonneg _) (coordDecay_nonneg κ Y γ)
  set S₁ := ∑ α ∈ Finset.univ.filter (fun α : ChordCoord F => enclosingCell α.1.1.1 = Y), |chordCoord α ζ| with hS₁
  have hS₁A : S₁ ≤ A := sum_abs_chordCoord_cell_le hκ ζ
  have e : quadraticBound κ Y B ζ = B * P * (S₁ * A) := by
    have hq : ∀ α β : ChordCoord F, |chordCoordProduct α β ζ| * (B * coordDecay κ Y β) * P =
        (B * P) * (|chordCoord α ζ| * (|chordCoord β (id ζ)| * coordDecay κ Y β)) := by
      intro α β
      simp only [chordCoordProduct, abs_mul, id]
      ring
    simp only [quadraticBound, quadraticIndex, ← hA, ← hP]
    rw [Finset.sum_product]
    simp only [hq, ← Finset.mul_sum, ← Finset.sum_mul, ← hA, ← hS₁]
  rw [e]
  calc B * P * (S₁ * A) ≤ B * P * (A * A) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS₁A hA0) (by positivity)
    _ = _ := by ring
theorem quadraticSlopeBound_le (hκ : 0 < κ) {B : ℝ} (hB : 0 ≤ B) (b : ↥(chordBonds (finiteCells F)))
    (ζ : StepVariable (finiteCells F)) :
    quadraticSlopeBound κ Y B b ζ ≤ B * (6 * (∑ γ, |chordCoord γ (id ζ)| * coordDecay κ Y γ) +
      10 * (∑ γ, |chordCoord γ (id ζ)| * coordDecay κ Y γ) ^ 2) *
      (1 + ∑ γ, |chordCoord γ (id ζ)| * coordDecay κ Y γ) ^ 3 := by
  set A := ∑ γ, |chordCoord γ (id ζ)| * coordDecay κ Y γ with hA
  set P := (1 + A) ^ 3 with hP
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun γ _ => mul_nonneg (abs_nonneg _) (coordDecay_nonneg κ Y γ)
  set AY := Finset.univ.filter (fun α : ChordCoord F => enclosingCell α.1.1.1 = Y) with hAY
  set S₁ := ∑ α ∈ AY, |chordCoord α ζ| with hS₁
  have hS₁A : S₁ ≤ A := sum_abs_chordCoord_cell_le hκ ζ
  have hw1 := coordDecay_le_one hκ Y (F := F)
  have t1 : ∑ α ∈ AY, ∑ β : ChordCoord F, (if α.1 = b then |chordCoord β ζ| else 0) * coordDecay κ Y β ≤
      3 * A := by
    have h1 : ∀ α : ChordCoord F, ∑ β : ChordCoord F, (if α.1 = b then |chordCoord β ζ| else 0) * coordDecay κ Y β =
        (if α.1 = b then (1 : ℝ) else 0) * A := by
      intro α
      by_cases h : α.1 = b
      · simp [h, hA]
      · simp [h]
    simp only [h1]
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ hA0
    rw [← sum_ite_chordCoord_bond b]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun γ _ _ => by split_ifs <;> norm_num
  have t2 : ∑ α ∈ AY, ∑ β : ChordCoord F, (if β.1 = b then |chordCoord α ζ| else 0) * coordDecay κ Y β ≤
      S₁ * 3 := by
    have h1 : ∀ α : ChordCoord F, ∑ β : ChordCoord F, (if β.1 = b then |chordCoord α ζ| else 0) * coordDecay κ Y β ≤
        |chordCoord α ζ| * 3 := by
      intro α
      rw [← sum_ite_chordCoord_bond b, Finset.mul_sum]
      refine Finset.sum_le_sum fun β _ => ?_
      by_cases h : β.1 = b
      · simp only [h, if_true, mul_one]
        calc |chordCoord α ζ| * coordDecay κ Y β ≤ |chordCoord α ζ| * 1 :=
              mul_le_mul_of_nonneg_left (hw1 β) (abs_nonneg _)
          _ = _ := mul_one _
      · simp [h]
    rw [hS₁, Finset.sum_mul]
    exact Finset.sum_le_sum fun α _ => h1 α
  have t3 : ∑ q ∈ quadraticIndex F Y, |chordCoordProduct q.1 q.2 ζ| * coordDecay κ Y q.2 = S₁ * A := by
    have hq : ∀ α β : ChordCoord F, |chordCoordProduct α β ζ| * coordDecay κ Y β =
        |chordCoord α ζ| * (|chordCoord β (id ζ)| * coordDecay κ Y β) := by
      intro α β
      simp only [chordCoordProduct, abs_mul, id]
      ring
    simp only [quadraticIndex]
    rw [Finset.sum_product]
    simp only [hq, ← Finset.mul_sum, ← Finset.sum_mul, ← hA, ← hS₁]
    rfl
  have t4 : ∑ q ∈ quadraticIndex F Y, productSlopeBound q.1 q.2 b ζ * coordDecay κ Y q.2 ≤ 3 * A + S₁ * 3 := by
    simp only [quadraticIndex]
    rw [Finset.sum_product]
    simp only [productSlopeBound, add_mul, Finset.sum_add_distrib]
    exact add_le_add t1 t2
  have e : quadraticSlopeBound κ Y B b ζ = B * P * (∑ q ∈ quadraticIndex F Y,
      productSlopeBound q.1 q.2 b ζ * coordDecay κ Y q.2 +
      10 * ∑ q ∈ quadraticIndex F Y, |chordCoordProduct q.1 q.2 ζ| * coordDecay κ Y q.2) := by
    simp only [quadraticSlopeBound, ← hA, ← hP]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [e, t3]
  have h5 : S₁ * A ≤ A ^ 2 := by nlinarith
  calc B * P * (∑ q ∈ quadraticIndex F Y, productSlopeBound q.1 q.2 b ζ * coordDecay κ Y q.2 + 10 * (S₁ * A))
      ≤ B * P * (6 * A + 10 * A ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith [t4]) (by positivity)
    _ = _ := by ring
end
section
open Set Filter Topology MeasureTheory
open scoped Interval Quaternion
open YangMills.Construction.BlockAverages
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.ScaledVariables
variable {F : BlockFrame}
theorem continuous_pathHolonomy {j k : ℕ} {W : (Fin k → ℝ) → F.GaugeField j}
    (hW : ∀ y i, Continuous fun q => ((W q y i : UnitQuaternion) : ℍ[ℝ])) :
    ∀ (l : List PathStep) (x : F.Site j), Continuous fun q => ((pathHolonomy (W q) x l : UnitQuaternion) : ℍ[ℝ]) := by
  intro l
  induction l with
  | nil =>
    intro x
    simp only [pathHolonomy]
    exact continuous_const
  | cons st r ih =>
    intro x
    simp only [pathHolonomy, linkValue, Submonoid.coe_mul]
    refine Continuous.mul ?_ (ih _)
    by_cases h : st.2 = true
    · simp only [h, if_true]
      exact hW _ _
    · simp only [h]
      have e : ∀ q, (((W q (x - unitStep j st.1) st.1)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
          star ((W q (x - unitStep j st.1) st.1 : UnitQuaternion) : ℍ[ℝ]) := by
        intro q
        rw [← Unitary.star_eq_inv, Unitary.coe_star]
      simp only [Bool.false_eq_true, if_false, e]
      exact continuous_star.comp (hW _ _)
theorem continuous_leftTranslate_bondSpread {j k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (W : F.GaugeField j) (y : F.Site j) (i : Fin 4) :
    Continuous fun q => ((leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X q) W y i : UnitQuaternion) : ℍ[ℝ]) := by
  simp only [leftTranslate, Submonoid.coe_mul]
  refine Continuous.mul ?_ continuous_const
  have h1 : Continuous fun q : Fin k → ℝ => ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X q y i : imaginaryQuaternions) : ℍ[ℝ]) := by
    have e : ∀ q : Fin k → ℝ, ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X q y i : imaginaryQuaternions) : ℍ[ℝ]) =
        ∑ l, if c l = (y, i) then q l • (X l : ℍ[ℝ]) else 0 := by
      intro q
      simp only [_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread]
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs <;> simp
    simp only [e]
    refine continuous_finset_sum _ fun l _ => ?_
    split_ifs
    · exact (continuous_apply l).smul continuous_const
    · exact continuous_const
  let +nondep : NormedAlgebra ℚ ℍ[ℝ] := .restrictScalars ℚ ℝ ℍ[ℝ]
  show Continuous fun q => NormedSpace.exp ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X q y i : imaginaryQuaternions) : ℍ[ℝ])
  exact NormedSpace.exp_continuous.comp h1
theorem eventually_smallCurvature {k : ℕ} [Finite (F.Site F.top)] (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) {s : ℝ} {V : F.GaugeField F.top} (hV : IsSmallCurvature s V) :
    ∀ᶠ q in 𝓝 (0 : Fin k → ℝ), IsSmallCurvature s (leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X q) V) := by
  have hcont : ∀ p : F.Site F.top × Fin 4 × Fin 4,
      Continuous fun q => plaquetteDefect (leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X q) V) p := by
    intro p
    have h1 := continuous_pathHolonomy (W := fun q => leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X q) V)
      (fun y i => continuous_leftTranslate_bondSpread c X V y i)
      [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] p.1
    exact (h1.sub continuous_const).norm
  have h0 : leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X (0 : Fin k → ℝ)) V = V := by
    rw [bondSpread_zero, leftTranslate_zero]
  have : ∀ p : F.Site F.top × Fin 4 × Fin 4, ∀ᶠ q in 𝓝 (0 : Fin k → ℝ), p.2.1 < p.2.2 →
      plaquetteDefect (leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X q) V) p < s := by
    intro p
    by_cases hp : p.2.1 < p.2.2
    · have h1 := hV p hp
      rw [← h0] at h1
      filter_upwards [(hcont p).continuousAt.eventually (Iio_mem_nhds h1)] with q hq _
      exact hq
    · exact Eventually.of_forall fun q h => absurd h hp
  exact (eventually_all.2 this)
def gapProfile (h : ℝ → ℝ) (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  3 / 2 * p.2 - Real.log (h (p.1 ^ 2 * Real.exp (-p.2) / a)) + Real.log (h (p.1 ^ 2 / a))
theorem contDiff_gapProfile {h : ℝ → ℝ} (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hp : ∀ u, 0 ≤ u → 0 < h u) {a : ℝ} (ha : 0 < a) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gapProfile h a) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Real.log (h (p.1 ^ 2 * Real.exp (-p.2) / a))) p := by
    refine ContDiffAt.log (hs.contDiffAt.comp _ ?_) (hp _ (by positivity)).ne'
    exact ((contDiff_fst.pow 2).mul (Real.contDiff_exp.comp contDiff_snd.neg)).contDiffAt.div_const a
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => Real.log (h (p.1 ^ 2 / a))) p := by
    refine ContDiffAt.log (hs.contDiffAt.comp _ ?_) (hp _ (by positivity)).ne'
    exact (contDiff_fst.pow 2).contDiffAt.div_const a
  have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => 3 / 2 * p.2) p :=
    contDiffAt_const.mul contDiffAt_snd
  exact (h3.sub h1).add h2
theorem haarGapShift_eq_gapProfile {h : ℝ → ℝ} (hg : ∀ u, 0 ≤ u → haarGapTail u = -Real.log (h u)) {a l r : ℝ}
    (ha : 0 < a) (hr : 0 < r) : haarGapShift a l r = gapProfile h a (l, Real.log r) := by
  simp only [haarGapShift, gapProfile]
  rw [hg _ (by positivity), hg _ (by positivity), Real.exp_neg, Real.exp_log hr]
  have : l ^ 2 / (a * r) = l ^ 2 * r⁻¹ / a := by
    field_simp
  rw [this]
  ring
variable {V : F.GaugeField F.top}
theorem jointMixedDeriv_zero (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F))
    (b : Fin 0 → ↥(chordBonds (finiteCells F))) (u : Fin 0 → EuclideanSpace ℝ (Fin 3))
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) : jointMixedDeriv G η V b u c X = G η V := by
  simp only [jointMixedDeriv]
  have h : iteratedFDeriv ℝ (0 + 0) (jointDisplacement G η V b u c X) 0 =
      iteratedFDeriv ℝ 0 (jointDisplacement G η V b u c X) 0 := rfl
  rw [h, iteratedFDeriv_zero_apply]
  simp [jointDisplacement, displacedPoint]
  have : _root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X (fun _ => (0 : ℝ)) = 0 := by
    funext y i
    simp [_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread]
  rw [this, leftTranslate_zero]
theorem cellSetDiameter_singleton_empty {z : F.Cell} (b : Fin 0 → ↥(chordBonds (finiteCells F)))
    (c : Fin 0 → F.Site F.top × Fin 4) :
    cellSetDiameter ({z} ∪ chordBondCells b ∪ topBondCells c) = 0 := by
  have h1 : chordBondCells b = ∅ := by simp [chordBondCells]
  have h2 : topBondCells c = ∅ := by simp [topBondCells]
  rw [h1, h2]
  simp [cellSetDiameter_singleton]
theorem isDecayingKernel_of_bounds {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {B r : ℝ}
    {z : F.Cell} {S : Set (StepVariable (finiteCells F))} {n : ℕ}
    (hsm : ∀ η ∈ S, ∀ (p : ℕ) (c' : Fin p → F.Site F.top × Fin 4) (X' : Fin p → imaginaryQuaternions),
      AreUnitVectors X' → n ≤ p →
      ContDiffAt ℝ n (jointDisplacement G η V (doubledBond F) (doubledUnit F) c' X') 0)
    (hval : ∀ η ∈ S, |G η V| ≤ B)
    (hb : ∀ η ∈ S, ∀ (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
      (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions),
      1 ≤ l + j → l + j ≤ n → (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
      |jointMixedDeriv G η V b u c X| ≤
        B * Real.exp (-(r * cellSetDiameter ({z} ∪ chordBondCells b ∪ topBondCells c)))) :
    IsDecayingKernel V G B r {z} S n := by
  refine ⟨fun k c X η hη => contDiffAt_translatedObservable G η V c X (hsm η hη),
    fun η hη l j b u c X hlj hu hX => ?_⟩
  by_cases h0 : 1 ≤ l + j
  · exact hb η hη l j b u c X h0 hlj hu hX
  · have hl : l = 0 := by omega
    have hj : j = 0 := by omega
    subst hl hj
    rw [jointMixedDeriv_zero, cellSetDiameter_singleton_empty]
    simpa using hval η hη
theorem smallCurvature_uniformField {j : ℕ} {s : ℝ} (hs : 0 < s) :
    IsSmallCurvature s (ColdStepAtMirrorFrames.uniformField F j) := by apply _root_.YangMills.SharedProofs.p8038 <;> assumption
theorem torusDecayFactor_zero (L : ℕ) (δ : ℝ) : torusDecayFactor L δ 0 = 1 := by
  simp [torusDecayFactor]
theorem runningMax_mono (e : ℕ → ℝ) (he : ∀ j, 0 ≤ e j) {j k : ℕ} (h : j ≤ k) : runningMax e j ≤ runningMax e k := by
  induction k, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (le_max_left _ _)
theorem runningMax_nonneg (e : ℕ → ℝ) (j : ℕ) : 0 ≤ runningMax e j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact ih.trans (le_max_left _ _)
def closedBondBalls (F : BlockFrame) (ρ : ℝ) : Set (StepVariable (finiteCells F)) := {η | ∀ b, ‖η b‖ ≤ ρ}
theorem smul_mem_closedBondBalls {ρ : ℝ} :
    ∀ η ∈ closedBondBalls F ρ, ∀ v ∈ Icc (0 : ℝ) 1, v • η ∈ closedBondBalls F ρ := by
  intro η hη v hv b
  have h1 : ‖(v • η) b‖ = |v| * ‖η b‖ := by
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  rw [h1, abs_of_nonneg hv.1]
  calc v * ‖η b‖ ≤ 1 * ‖η b‖ := mul_le_mul_of_nonneg_right hv.2 (norm_nonneg _)
    _ ≤ ρ := by simpa using hη b
theorem mem_closedBondBalls_of_scale {ρ : ℝ} : ∀ p ∈ scaleBallSet F ρ, p.1 • p.2 ∈ closedBondBalls F ρ := by
  intro p hp b
  have h1 : ‖(p.1 • p.2) b‖ = |p.1| * ‖p.2 b‖ := by
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  rw [h1]
  exact (hp b).le
def minimizerEnergy (a ρ : ℝ) : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  fun η V' => ReferenceDensity.chartedEnergyAtMinimizer a ρ V' η
def logContourAverage (a ρ : ℝ) (c₀ : F.Site F.top × Fin 4) :
    StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  fun η V' => Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true a ρ 0 V' η) c₀‖
def minimizerHaarLogRatio (a ρ : ℝ) (b₀ : ↥(chordBonds (finiteCells F))) :
    StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  fun η V' => haarLogRatio (coordsAboveFrame true a ρ 0 V' η b₀.1.1 b₀.1.2)
theorem interpolatedCoords_zero (a ρ : ℝ) (m : ℕ) (V' : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    interpolatedCoords 0 a ρ m V' η = coordsAboveFrame true a ρ 0 V' η := by apply _root_.YangMills.SharedProofs.p718 <;> assumption
theorem interpolatedEnergy_zero (a ρ : ℝ) (m : ℕ) :
    (interpolatedEnergy 0 a ρ m : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) = minimizerEnergy a ρ := by apply _root_.YangMills.Construction.ChartedEnergyRegularity.interpolatedEnergy_zero <;> assumption
theorem logContourNorm_zero (a ρ : ℝ) (m : ℕ) (c₀ : F.Site F.top × Fin 4) :
    (logContourNorm 0 a ρ m c₀ : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) =
      logContourAverage a ρ c₀ := by apply _root_.YangMills.Construction.ChartedEnergyRegularity.logContourNorm_zero <;> assumption
theorem interpolatedHaarLogRatio_zero (a ρ : ℝ) (m : ℕ) (b₀ : ↥(chordBonds (finiteCells F))) :
    (interpolatedHaarLogRatio 0 a ρ m b₀ : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) =
      minimizerHaarLogRatio a ρ b₀ := by
  funext η V'
  simp only [interpolatedHaarLogRatio, minimizerHaarLogRatio, interpolatedCoords_zero]
theorem interpolatedExpansion_zero (a ρ : ℝ) (m : ℕ) (f : LocalFamily) (y : F.Site F.depth) :
    (interpolatedExpansion 0 a ρ m f y : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) =
      centredExpansion true a ρ 0 f y := by
  funext η V'
  simp only [interpolatedExpansion, centredExpansion, interpolatedField, fieldAboveFrame, interpolatedCoords_zero]
def doubleSumRangeNine (D : ℕ → ℕ → ℝ) : ℝ := ∑ l ∈ Finset.range 9, ∑ j ∈ Finset.range 9, D l j
theorem doubleSumRangeNine_nonneg {D : ℕ → ℕ → ℝ} (hD : ∀ l j, 0 < D l j) : 0 ≤ doubleSumRangeNine D :=
  Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun j _ => (hD l j).le
theorem le_doubleSum {D : ℕ → ℕ → ℝ} (hD : ∀ l j, 0 < D l j) {l j : ℕ} (h : l + j ≤ 8) : D l j ≤ doubleSumRangeNine D := by
  have h1 : D l j ≤ ∑ j ∈ Finset.range 9, D l j :=
    Finset.single_le_sum (f := fun j => D l j) (fun j _ => (hD l j).le) (Finset.mem_range.2 (by omega))
  exact h1.trans (Finset.single_le_sum (f := fun l => ∑ j ∈ Finset.range 9, D l j)
    (fun l _ => Finset.sum_nonneg fun j _ => (hD l j).le) (Finset.mem_range.2 (by omega)))
theorem isDecayingEnergy_minimizerEnergy {a ρA κ κ₂ δ₂ x ρ : ℝ} {m : ℕ} {K : ℕ → ℝ} {D : ℕ → ℕ → ℝ}
    (hD : ∀ l j, 0 < D l j) (hne : Nonempty (ChordCoord F))
    (hK : ∀ η ∈ closedBondBalls F ρ, HasInterpolationKernels 0 a ρA κ κ₂ δ₂ x m K D V η) :
    IsDecayingEnergy V (minimizerEnergy a ρA) (doubleSumRangeNine D) δ₂ (closedBondBalls F ρ) := by
  have hc : 0 < Fintype.card (ChordCoord F) := Fintype.card_pos
  refine ⟨fun k c X η hη => contDiffAt_translatedObservable _ η V c X fun p c' X' hX' hp => ?_,
    fun η hη l j b u c X hl hlj hu hX => ?_⟩
  · have h1 := ((hK η hη).energy _ p (doubledBond F) (doubledUnit F) c' X' (by omega) (norm_doubledUnit F) hX').1
    rw [interpolatedEnergy_zero] at h1
    exact h1.of_le (by exact_mod_cast
      (by omega : 8 ≤ Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F) + p))
  · have h1 := ((hK η hη).energy l j b u c X hl hu hX).2
    rw [interpolatedEnergy_zero] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_doubleSum hD hlj) (Real.exp_pos _).le)
theorem isDecayingKernel_logContourAverage {a ρA κ κ₂ δ₂ x ρ R₀ : ℝ} {m : ℕ} {K : ℕ → ℝ} {D : ℕ → ℕ → ℝ}
    (hD : ∀ l j, 0 < D l j) (hR : 0 ≤ R₀)
    (hK : ∀ η ∈ closedBondBalls F ρ, HasInterpolationKernels 0 a ρA κ κ₂ δ₂ x m K D V η)
    (c₀ : F.Site F.top × Fin 4) (hval : ∀ η ∈ closedBondBalls F ρ, |logContourAverage a ρA c₀ η V| ≤ R₀) :
    IsDecayingKernel V (logContourAverage a ρA c₀) (doubleSumRangeNine D + R₀ + 1) (2 ^ 8 * κ) {c₀.1}
      (closedBondBalls F ρ) 6 := by
  have hT := doubleSumRangeNine_nonneg hD
  refine isDecayingKernel_of_bounds (fun η hη p c' X' hX' hp => ?_) (fun η hη => ?_)
    (fun η hη l j b u c X h1 hlj hu hX => ?_)
  · have h1 := ((hK η hη).logContour c₀ _ p (doubledBond F) (doubledUnit F) c' X' (by omega)
      (norm_doubledUnit F) hX').1
    rw [logContourNorm_zero] at h1
    exact h1.of_le (by exact_mod_cast
      (by omega : 6 ≤ Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F) + p))
  · exact (hval η hη).trans (by linarith)
  · have h2 := ((hK η hη).logContour c₀ l j b u c X h1 hu hX).2
    rw [logContourNorm_zero] at h2
    refine h2.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    have := le_doubleSum hD (by omega : l + j ≤ 8)
    linarith
theorem isDecayingKernel_minimizerHaarLogRatio {a ρA κ κ₂ δ₂ x ρ R₀ : ℝ} {m : ℕ} {K : ℕ → ℝ}
    {D : ℕ → ℕ → ℝ} (hD : ∀ l j, 0 < D l j) (hR : 0 ≤ R₀)
    (hK : ∀ η ∈ closedBondBalls F ρ, HasInterpolationKernels 0 a ρA κ κ₂ δ₂ x m K D V η)
    (b₀ : ↥(chordBonds (finiteCells F))) (hval : ∀ η ∈ closedBondBalls F ρ, |minimizerHaarLogRatio a ρA b₀ η V| ≤ R₀) :
    IsDecayingKernel V (minimizerHaarLogRatio a ρA b₀) (doubleSumRangeNine D + R₀ + 1) (2 ^ 8 * κ) {enclosingCell b₀.1.1}
      (closedBondBalls F ρ) 6 := by
  have hT := doubleSumRangeNine_nonneg hD
  refine isDecayingKernel_of_bounds (fun η hη p c' X' hX' hp => ?_) (fun η hη => ?_)
    (fun η hη l j b u c X h1 hlj hu hX => ?_)
  · have h1 := ((hK η hη).haar b₀ _ p (doubledBond F) (doubledUnit F) c' X' (by omega) (norm_doubledUnit F) hX').1
    rw [interpolatedHaarLogRatio_zero] at h1
    exact h1.of_le (by exact_mod_cast
      (by omega : 6 ≤ Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F) + p))
  · exact (hval η hη).trans (by linarith)
  · have h2 := ((hK η hη).haar b₀ l j b u c X h1 hu hX).2
    rw [interpolatedHaarLogRatio_zero] at h2
    refine h2.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    have := le_doubleSum hD (by omega : l + j ≤ 8)
    linarith
end
section
open Set Filter Topology MeasureTheory
open scoped Interval Quaternion
open YangMills.Construction.BlockAverages
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.ScaledVariables
variable {F : BlockFrame} {V : F.GaugeField F.top} {κ ρ l₁ : ℝ} {Y : F.Cell}
abbrev chordNear (κ : ℝ) (Y : F.Cell) (ζ : StepVariable (finiteCells F)) : ℝ :=
  ∑ γ, |chordCoord γ (id ζ)| * coordDecay κ Y γ
theorem chordNear_nonneg (κ : ℝ) (Y : F.Cell) (ζ : StepVariable (finiteCells F)) : 0 ≤ chordNear κ Y ζ :=
  Finset.sum_nonneg fun γ _ => mul_nonneg (abs_nonneg _) (coordDecay_nonneg κ Y γ)
theorem chordNear_le (ζ : StepVariable (finiteCells F)) : chordNear κ Y ζ ≤ 3 * localWeight κ Y ζ := by
  simp only [chordNear, localWeight]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  have h1 : ∀ a : Fin 3, |chordCoord (b, a) (id ζ)| * coordDecay κ Y (b, a) ≤
      Real.exp (-(2 ^ 4 * κ * cellSupDist (enclosingCell b.1.1) Y)) * ‖ζ b‖ := by
    intro a
    have h2 : |chordCoord (b, a) (id ζ)| ≤ ‖ζ b‖ := PiLp.norm_apply_le (ζ b) a
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  calc ∑ a : Fin 3, |chordCoord (b, a) (id ζ)| * coordDecay κ Y (b, a)
      ≤ ∑ _a : Fin 3, Real.exp (-(2 ^ 4 * κ * cellSupDist (enclosingCell b.1.1) Y)) * ‖ζ b‖ :=
        Finset.sum_le_sum fun a _ => h1 a
    _ = _ := by simp
theorem localWeight_nonneg (κ : ℝ) (Y : F.Cell) (ζ : StepVariable (finiteCells F)) : 0 ≤ localWeight κ Y ζ :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
theorem scaledNear_eq (ζ : StepVariable (finiteCells F)) :
    ∑ α, |scaledCoord α ((1 : ℝ), ζ)| * scaledCoordDecay κ Y α = 1 + chordNear κ Y ζ := by
  rw [Fintype.sum_option]
  simp [scaledCoord, scaledCoordDecay, scaledCoordDist, chordNear, coordDecay]
theorem contDiffAt_translated_gapProfile {Lg : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {B r : ℝ}
    {P : Finset F.Cell} {S : Set (StepVariable (finiteCells F))} (hk : IsDecayingKernel V Lg B r P S 6)
    {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ (6 : ℕ) g) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ∀ x ∈ {x : ScaledPoint F | x.2 ∈ S},
      ContDiffAt ℝ (6 : ℕ) (translatedObservable (fun (x : ScaledPoint F) V' => g (x.1, Lg x.2 V')) V c X) (x, 0) := by
  intro x hx
  have htop : translatedObservable (fun (x : ScaledPoint F) V' => g (x.1, Lg x.2 V')) V c X =
      g ∘ scaleAndValue (translatedObservable Lg V c X) :=
    funext fun p => by simp [translatedObservable, scaleAndValue, scaleCoordMap, forgetScaleMap]
  rw [htop]
  have hR6 : ContDiffAt ℝ (6 : ℕ) (translatedObservable Lg V c X) (forgetScaleMap F k (x, 0)) := by
    have : forgetScaleMap F k (x, 0) = (x.2, 0) := by simp [forgetScaleMap]
    rw [this]
    exact hk.smooth k c X _ hx
  have hf6 : ContDiffAt ℝ (6 : ℕ) (scaleAndValue (translatedObservable Lg V c X)) (x, 0) :=
    (scaleCoordMap F k).contDiff.contDiffAt.prodMk
      (ContDiffAt.comp (x, (0 : Fin k → ℝ)) (g := translatedObservable Lg V c X) hR6
        (forgetScaleMap F k).contDiff.contDiffAt)
  exact hg.contDiffAt.comp _ hf6
def gapTerm (a ρA : ℝ) (c₀ : F.Site F.top × Fin 4) : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  fun l ζ V' => haarGapShift a l ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true a ρA 0 V' (l • ζ)) c₀‖
theorem decayingPart_gapTerm [Finite (F.Site F.top)] {a ρA B r M s : ℝ} {c₀ : F.Site F.top × Fin 4} {h : ℝ → ℝ}
    (hk : IsDecayingKernel V (logContourAverage a ρA c₀) B r {Y} (closedBondBalls F ρ) 6) (hB : 1 ≤ B)
    (hκ : 0 < κ) (hr : 2 ^ 7 * κ ≤ r) (hl₁ : l₁ ≤ 1) (ha : 0 < a)
    (hg : ContDiff ℝ (6 : ℕ) (gapProfile h a)) (htail : ∀ u, 0 ≤ u → haarGapTail u = -Real.log (h u))
    (hM0 : 0 ≤ M)
    (hM : ∀ η ∈ closedBondBalls F ρ, ∀ s : ℝ, |s| ≤ 1 → ∀ p, p ≤ 6 →
      ‖iteratedFDeriv ℝ p (gapProfile h a) (s, logContourAverage a ρA c₀ η V)‖ ≤ M)
    (hV : IsSmallCurvature s V)
    (hpos : ∀ V' : F.GaugeField F.top, IsSmallCurvature s V' → ∀ η : StepVariable (finiteCells F),
      (∀ b, ‖η b‖ < ρ) → 0 < ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true a ρA 0 V' η) c₀‖) :
    IsDecayingPart κ ρ l₁ Y V (gapTerm a ρA c₀)
      (fun ζ => |(1 : ℝ)| * gapJetConstant M B * (1 + ∑ α, |scaledCoord α ((1 : ℝ), ζ)| * scaledCoordDecay κ Y α) ^ 3)
      (fun _ ζ => (0 + |(1 : ℝ)| * (3 * 3 + 1)) * gapJetConstant M B *
        (1 + ∑ α, |scaledCoord α ((1 : ℝ), ζ)| * scaledCoordDecay κ Y α) ^ 3) := by
  refine (decayingPart_gap hk hB hκ hr hl₁ (gapProfile h a) hg hM0 hM mem_closedBondBalls_of_scale).congr
    fun k c X p hp => ?_
  have h1 : ∀ᶠ y : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) in 𝓝 (p, 0),
      IsSmallCurvature s (leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.bondSpread c X y.2) V) :=
    (continuous_snd.tendsto (p, (0 : Fin k → ℝ))).eventually (eventually_smallCurvature c X hV)
  have h2 : ∀ᶠ y : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) in 𝓝 (p, 0), y.1 ∈ scaleBallSet F ρ :=
    (continuous_fst.tendsto (p, (0 : Fin k → ℝ))).eventually ((isOpen_scaleBallSet ρ).mem_nhds hp)
  filter_upwards [h1, h2] with y hy1 hy2
  obtain ⟨⟨l, ζ⟩, q⟩ := y
  have hb : ∀ b, ‖(l • ζ) b‖ < ρ := fun b => by
    have h3 : ‖(l • ζ) b‖ = |l| * ‖ζ b‖ := by rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    rw [h3]
    exact hy2 b
  have hr' := hpos _ hy1 _ hb
  simp only [scaledObservable, gapTerm, rayObservable]
  rw [haarGapShift_eq_gapProfile htail ha hr']
  simp [logContourAverage]
theorem isDecayingKernel_const {c B r : ℝ} {P : Finset F.Cell} {S : Set (StepVariable (finiteCells F))} {n : ℕ}
    (hB : 0 ≤ B) (hc : |c| ≤ B) (hP : c ≠ 0 → cellSetDiameter P = 0) :
    IsDecayingKernel V (fun _ _ => c) B r P S n := by
  refine ⟨fun k c' X η _ => contDiffAt_const, fun η _ l j b u c' X _ _ _ => ?_⟩
  by_cases h0 : l + j = 0
  · have hl : l = 0 := by omega
    have hj : j = 0 := by omega
    subst hl hj
    rw [jointMixedDeriv_zero]
    by_cases hc0 : c = 0
    · simp only [hc0, abs_zero]
      positivity
    · have h1 : chordBondCells b = ∅ := by simp [chordBondCells]
      have h2 : topBondCells c' = ∅ := by simp [topBondCells]
      rw [h1, h2]
      simpa [hP hc0] using hc
  · have : jointMixedDeriv (fun (_ : StepVariable (finiteCells F)) (_ : F.GaugeField F.top) => c) η V b u c' X = 0 := by
      simp only [jointMixedDeriv]
      have e : jointDisplacement (fun (_ : StepVariable (finiteCells F)) (_ : F.GaugeField F.top) => c) η V b u c' X =
          fun _ => c := rfl
      rw [e, iteratedFDeriv_const_of_ne h0]
      rfl
    rw [this, abs_zero]
    positivity
theorem final_power_bounds {A u : ℝ} (hA0 : 0 ≤ A) (hu : 1 ≤ u) (hA : A ≤ 3 * u) :
    A ^ 2 * (1 + A) ^ 3 ≤ 576 * u ^ 7 ∧ (6 * A + 10 * A ^ 2) * (1 + A) ^ 3 ≤ 6912 * u ^ 7 ∧
      (1 + A) ^ 3 ≤ 64 * u ^ 7 ∧ (1 + (1 + A)) ^ 3 ≤ 125 * u ^ 7 := by
  have h4 : 1 + A ≤ 4 * u := by linarith
  have h5 : 1 + (1 + A) ≤ 5 * u := by linarith
  have p3 : (1 + A) ^ 3 ≤ (4 * u) ^ 3 := pow_le_pow_left₀ (by linarith) h4 3
  have p5 : (1 + (1 + A)) ^ 3 ≤ (5 * u) ^ 3 := pow_le_pow_left₀ (by linarith) h5 3
  have pA : A ^ 2 ≤ (3 * u) ^ 2 := pow_le_pow_left₀ hA0 hA 2
  have u37 : u ^ 3 ≤ u ^ 7 := pow_le_pow_right₀ hu (by norm_num)
  have u57 : u ^ 5 ≤ u ^ 7 := pow_le_pow_right₀ hu (by norm_num)
  have q0 : 0 ≤ (1 + A) ^ 3 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc A ^ 2 * (1 + A) ^ 3 ≤ (3 * u) ^ 2 * (4 * u) ^ 3 :=
          mul_le_mul pA p3 q0 (by positivity)
      _ = 576 * u ^ 5 := by ring
      _ ≤ 576 * u ^ 7 := by linarith
  · have h6 : 6 * A + 10 * A ^ 2 ≤ 108 * u ^ 2 := by
      have : u ≤ u ^ 2 := by nlinarith
      nlinarith
    calc (6 * A + 10 * A ^ 2) * (1 + A) ^ 3 ≤ (108 * u ^ 2) * (4 * u) ^ 3 :=
          mul_le_mul h6 p3 q0 (by positivity)
      _ = 6912 * u ^ 5 := by ring
      _ ≤ 6912 * u ^ 7 := by linarith
  · calc (1 + A) ^ 3 ≤ (4 * u) ^ 3 := p3
      _ = 64 * u ^ 3 := by ring
      _ ≤ 64 * u ^ 7 := by linarith
  · calc (1 + (1 + A)) ^ 3 ≤ (5 * u) ^ 3 := p5
      _ = 125 * u ^ 3 := by ring
      _ ≤ 125 * u ^ 7 := by linarith
theorem torusDecayFactor_pos (L : ℕ) (δ x : ℝ) : 0 < torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
theorem hasBoundedDerivatives_abs {L t n₀ : ℕ} {σ δ : ℝ} {k : ℕ} {e : ℕ → ℝ} {f : LocalFamily}
    (h : Interpolation.HasBoundedDerivatives L t n₀ σ δ k e f) :
    Interpolation.HasBoundedDerivatives L t n₀ σ δ k (fun j => |e j|) f :=
  ⟨h.smooth, h.gauge_invariant, fun F hF y W j c X hW h1 hk hX => (h.decay F hF y W j c X hW h1 hk hX).trans
    (div_le_div_of_nonneg_right (le_abs_self _) (torusDecayFactor_pos _ _ _).le)⟩
theorem bondDeriv_nil {j : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : Fin 0 → F.Site j × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) : bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
theorem abs_subtractTrivial_le {L t n₀ : ℕ} {σ δ ε ε₃ : ℝ} {f : LocalFamily}
    (hf : FamilyNorms.IsNormBoundedLocalFamily L t n₀ σ δ ε ε₃ f)
    (hL : 3 ≤ L) (hσ : 0 < σ) (hF : IsCubicTorusAbove L t n₀ F) (hside : ∀ i, 1 ≤ F.extent i)
    (y : F.Site F.depth) (W : F.GaugeField F.depth) (hW : IsSmallCurvature σ W) :
    |ColdStepAtMirrorFrames.subtractTrivial f F y W| ≤ ε := by
  have hper : ∀ i, 2 * 0 + 2 < F.period F.depth i := by
    intro i
    have h1 : F.top - F.depth = 1 := by simp [BlockFrame.top]
    simp only [BlockFrame.period, h1, pow_one]
    have hFL : F.blockSide = L := hF.1
    rw [hFL]
    nlinarith [hside i]
  have hagree : AgreeOnBox W (ColdStepAtMirrorFrames.uniformField F F.depth) y y 0 := by
    refine ⟨hper, hper, fun b hb => ?_⟩
    exfalso
    have h1 := hb.1 b.2
    have h2 := hb.2 b.2
    simp only [Pi.add_apply, Pi.single_eq_same, Nat.cast_zero] at h1 h2
    have e1 : b.1 b.2 = 0 := abs_nonpos_iff.1 h1
    rw [e1] at h2
    simp at h2
  have h := hf.locality F F hF hF y y W (ColdStepAtMirrorFrames.uniformField F F.depth) 0 0 (fun l => l.elim0)
    (fun l => l.elim0) hW (smallCurvature_uniformField hσ)
    hagree (by omega) (fun l => l.elim0) (fun l => l.elim0)
  rw [bondDeriv_nil, bondDeriv_nil] at h
  have hc0 : ColdStepAtMirrorFrames.subtractTrivial f F y (ColdStepAtMirrorFrames.uniformField F F.depth) = 0 :=
    sub_self _
  rw [hc0, sub_zero] at h
  simpa [torusDecayFactor_zero] using h
theorem isDecayingKernel_centredExpansion {a ρA κ δ C : ℝ} {Ck : ℕ → ℝ} {L m : ℕ} {e : ℕ → ℝ} {f : LocalFamily}
    {B₀ B : ℝ} (he : ∀ j, 0 ≤ e j) (hC : 0 ≤ C) (hB₀ : B₀ ≤ B) (hBC : C * runningMax e 6 ≤ B)
    (hT : ∀ η ∈ closedBondBalls F ρ, IsTransportBounded 0 a ρA κ δ C Ck L m 6 e f V η) (y : F.Site F.depth)
    (hval : ∀ η ∈ closedBondBalls F ρ, |centredExpansion true a ρA 0 f y η V| ≤ B₀) :
    IsDecayingKernel V (centredExpansion true a ρA 0 f y) B (2 ^ 7 * κ) {enclosingCell y} (closedBondBalls F ρ) 6 := by
  refine isDecayingKernel_of_bounds (fun η hη p c' X' hX' hp => ?_) (fun η hη => (hval η hη).trans hB₀)
    (fun η hη l j b u c X h1 hlj hu hX => ?_)
  · have h1 := (hT η hη).smooth y _ p (doubledBond F) (doubledUnit F) c' X' (norm_doubledUnit F) hX'
    rwa [interpolatedExpansion_zero] at h1
  · have h2 := (hT η hη).jointDeriv_le y l j b u c X h1 hlj hu hX
    rw [interpolatedExpansion_zero] at h2
    have hset : insert (enclosingCell y) (chordBondCells b ∪ topBondCells c) =
        ({enclosingCell y} ∪ chordBondCells b ∪ topBondCells c : Finset F.Cell) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      tauto
    rw [hset] at h2
    refine h2.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    refine le_trans (mul_le_mul_of_nonneg_left (runningMax_mono e he hlj) hC) hBC
def plainBound (κ : ℝ) (Y : F.Cell) (B : ℝ) (ζ : StepVariable (finiteCells F)) : ℝ :=
  |(1 : ℝ)| * (B * Real.exp (-(2 ^ 4 * κ * ((0 : ℕ) : ℝ)))) * (1 + chordNear κ Y ζ) ^ 3
def plainSlopeBound (κ : ℝ) (Y : F.Cell) (B : ℝ) (_b : ↥(chordBonds (finiteCells F)))
    (ζ : StepVariable (finiteCells F)) : ℝ :=
  (0 + |(1 : ℝ)| * (3 * 3 + 1)) * (B * Real.exp (-(2 ^ 4 * κ * ((0 : ℕ) : ℝ)))) * (1 + chordNear κ Y ζ) ^ 3
theorem plainBound_eq (B : ℝ) (ζ : StepVariable (finiteCells F)) :
    plainBound κ Y B ζ = B * (1 + chordNear κ Y ζ) ^ 3 := by
  simp [plainBound]
theorem plainSlopeBound_eq (B : ℝ) (b : ↥(chordBonds (finiteCells F))) (ζ : StepVariable (finiteCells F)) :
    plainSlopeBound κ Y B b ζ = 10 * (B * (1 + chordNear κ Y ζ) ^ 3) := by
  simp only [plainSlopeBound, abs_one]
  norm_num
  ring
theorem decayingPart_plain {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {B r : ℝ}
    {S : Set (StepVariable (finiteCells F))} (hk : IsDecayingKernel V G B r {Y} S 6) (hB : 0 ≤ B) (hκ : 0 < κ)
    (hr : 2 ^ 7 * κ ≤ r) (hl₁ : l₁ ≤ 1) (hS : ∀ p ∈ scaleBallSet F ρ, p.1 • p.2 ∈ S) :
    IsDecayingPart κ ρ l₁ Y V (rayObservable G id (fun _ => 1)) (plainBound κ Y B) (plainSlopeBound κ Y B) :=
  decayingPart_of_kernel hk hB hκ hr hl₁ (by simp) (Nat.zero_le _) contDiff_const (fun _ _ => 0)
    (fun b e ζ _ => by simp) (fun b e ζ _ hz => absurd (by simp) hz) hS
open Classical in
def cellLayerSites (F : BlockFrame) (Y : F.Cell) : Finset (F.Site F.depth) :=
  (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y)
def cellTopBonds (F : BlockFrame) (Y : F.Cell) : Finset (F.Site F.top × Fin 4) :=
  (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y)
def cellChordBonds (F : BlockFrame) (Y : F.Cell) : Finset ↥(chordBonds (finiteCells F)) :=
  Finset.univ.filter (fun b => enclosingCell b.1.1 = Y)
theorem cellTopBonds_card_le : (cellTopBonds F Y).card ≤ 4 := by apply _root_.YangMills.Construction.Interpolation.AtTop.card_innerBonds_at_cell_le <;> assumption
def diagonalKernel (lam : ℝ) (q : ChordCoord F × ChordCoord F) :
    StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  fun _ _ => if q.1 = q.2 then lam / 2 else 0
theorem secondDerivAlong_neg (Ψ : StepVariable (finiteCells F) → ℝ) (η u w : StepVariable (finiteCells F)) :
    secondDerivAlong Ψ η (-u) (-w) = secondDerivAlong Ψ η u w := by
  simp only [secondDerivAlong, map_neg]
  have : (fun ζ => -(fderiv ℝ Ψ ζ u)) = -(fun ζ => fderiv ℝ Ψ ζ u) := rfl
  rw [this, fderiv_neg]
  simp
theorem rescaledCellRemainder_neg (a ρA lam l : ℝ) (Y : F.Cell) (V' : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) :
    rescaledCellRemainder a ρA lam (-l) Y V' (-ζ) = rescaledCellRemainder a ρA lam l Y V' ζ := by
  have e1 : (-l) • (-ζ) = l • ζ := by simp
  have e2 : ∀ v : ℝ, (v * -l) • (-ζ) = (v * l) • ζ := fun v => by simp
  have e3 : ∀ b : ↥(chordBonds (finiteCells F)), (bondVariation b (-(ζ b)) : StepVariable (finiteCells F)) =
      -bondVariation b (ζ b) := fun b => by
    simp [bondVariation, Pi.single_neg]
  have e4 : ∀ (r : ℝ), haarGapShift a (-l) r = haarGapShift a l r := fun r => by simp [haarGapShift]
  simp only [rescaledCellRemainder, rescaledCellTerm, e1, e2, e4, Pi.neg_apply, e3, secondDerivAlong_neg, norm_neg]
theorem diagonal_sum_eq (lam : ℝ) (l : ℝ) (Y : F.Cell) (V' : F.GaugeField F.top) (ζ : StepVariable (finiteCells F)) :
    lam / 2 * (∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then ‖ζ b‖ ^ 2 else 0) =
      ∑ q ∈ quadraticIndex F Y, rayObservable (diagonalKernel lam q) id (chordCoordProduct q.1 q.2) l ζ V' := by
  simp only [quadraticIndex]
  rw [Finset.sum_product, Finset.sum_filter, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : enclosingCell b.1.1 = Y
  · simp only [hb, if_true]
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (b, a)]
    · simp [rayObservable, diagonalKernel, chordCoordProduct, chordCoord_apply]
      ring
    · intro β _ hne
      have : ((b, a) : ChordCoord F) ≠ β := fun h => hne h.symm
      simp [rayObservable, diagonalKernel, this]
    · simp
  · simp [hb]
theorem rescaledCellRemainder_eq (a ρA lam l : ℝ) (Y : F.Cell) (V' : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) :
    rescaledCellRemainder a ρA lam l Y V' ζ =
      quadraticPart (minimizerEnergy a ρA) Y l ζ V' + -1 * ∑ c ∈ cellTopBonds F Y, gapTerm a ρA c l ζ V' +
        -1 * ∑ b ∈ cellChordBonds F Y, rayObservable (minimizerHaarLogRatio a ρA b) id (fun _ => 1) l ζ V' +
        -1 * ∑ q ∈ quadraticIndex F Y, rayObservable (diagonalKernel lam q) id (chordCoordProduct q.1 q.2) l ζ V' := by
  rw [← diagonal_sum_eq]
  have h3 : ∑ b ∈ cellChordBonds F Y, rayObservable (minimizerHaarLogRatio a ρA b) id (fun _ => 1) l ζ V' =
      ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
        haarLogRatio (coordsAboveFrame true a ρA 0 V' (l • ζ) b.1.1 b.1.2) else 0 := by
    simp only [cellChordBonds]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [rayObservable, minimizerHaarLogRatio]
  rw [h3]
  simp only [rescaledCellRemainder, rescaledCellTerm, quadraticPart, minimizerEnergy, cellTopBonds, gapTerm]
  ring
theorem exists_gapProfile_bound {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (R₀ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s R : ℝ, |s| ≤ 1 → |R| ≤ R₀ → ∀ p, p ≤ 6 → ‖iteratedFDeriv ℝ p g (s, R)‖ ≤ M := by
  have hK : IsCompact (Icc (-1 : ℝ) 1 ×ˢ Icc (-R₀) R₀) := isCompact_Icc.prod isCompact_Icc
  have h1 : ∀ p : ℕ, ∃ C : ℝ, ∀ w ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-R₀) R₀, ‖iteratedFDeriv ℝ p g w‖ ≤ C := fun p =>
    hK.exists_bound_of_continuousOn
      ((hg.continuous_iteratedFDeriv (m := p) (by exact_mod_cast le_top)).continuousOn)
  choose C hC using h1
  refine ⟨∑ p ∈ Finset.range 7, |C p|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun s R hs hR p hp => ?_⟩
  have hw : (s, R) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-R₀) R₀ := ⟨abs_le.1 hs, abs_le.1 hR⟩
  refine (hC p _ hw).trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun p => |C p|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (by omega))
set_option maxHeartbeats 4000000 in
theorem rescaledParts_of_parameters (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hT : T.IsOrdered) (hn : 1 ≤ T.n₀)
    (hκr : 2 ^ 7 * T.κ ≤ T.chainParams.δ₂)
    (hL : 3 ≤ T.L) {C : ℝ} {Ck : ℕ → ℝ} (hC : 0 < C) (hTr : TransportBoundsAt T C Ck)
    {Kf : ℕ → ℝ} {D : ℕ → ℕ → ℝ} (hD : ∀ l j, 0 < D l j) (hKe : interpolationKernelBoundsAt T Kf D)
    (hLE : ∀ (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V →
      ContDiffOn ℝ 2 (ReferenceDensity.chartedEnergyAtMinimizer T.a T.ρA V) {η | ∀ b, ‖η b‖ < T.ballRadius} ∧
      fderiv ℝ (ReferenceDensity.chartedEnergyAtMinimizer T.a T.ρA V) 0 = 0 ∧
      (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) → ∀ c ∈ innerBonds (finiteCells F) F.top,
        0 < ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true T.a T.ρA 0 V η) c‖) ∧
      0 < T.lam ∧ ∀ η u : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        T.lam * ∑ b, ‖u b‖ ^ 2 ≤ secondDerivAlong (ReferenceDensity.chartedEnergyAtMinimizer T.a T.ρA V) η u u)
    (hVal : ∃ R₀ : ℝ, 0 ≤ R₀ ∧
      ∀ (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)),
        IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → (∀ b, ‖η b‖ ≤ T.ballRadius) →
        IsSmallCurvature T.σ (fieldAboveFrame true T.a T.ρA 0 V η) ∧
        (∀ c ∈ innerBonds (finiteCells F) F.top,
          |Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true T.a T.ρA 0 V η) c‖| ≤ R₀) ∧
        ∀ b : ↥(chordBonds (finiteCells F)),
          |haarLogRatio (coordsAboveFrame true T.a T.ρA 0 V η b.1.1 b.1.2)| ≤ R₀)
    {h : ℝ → ℝ} (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) (hp : ∀ u, 0 ≤ u → 0 < h u)
    (htail : ∀ u, 0 ≤ u → haarGapTail u = -Real.log (h u)) (N : ℕ)
    (hN : ∀ F : BlockFrame, F.blockSide = T.L → ∀ (ι : Type) [Fintype ι] (j : ι → F.Site F.depth × Fin 4),
      Function.Injective j → ∀ z : F.Cell, (Finset.univ.filter fun b => enclosingCell (j b).1 = z).card ≤ N)
    (e : ℕ → ℝ) :
    ∃ l₀ K : ℝ, 0 < l₀ ∧ 0 ≤ K ∧ ∀ l₁ : ℝ, 0 < l₁ → l₁ ≤ l₀ →
      ∀ (t : ℕ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell),
      T.IsBoundedFamilyOrderSix e t f →
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
      IsSmoothObservable T.κ T.ballRadius l₁ K Y V
        (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) ∧
      IsSmoothObservable T.κ T.ballRadius l₁ K Y V (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) := by
  obtain ⟨R₀, hR₀, hVb⟩ := hVal
  have ha : 0 < T.a := lt_of_lt_of_le one_pos hT.one_le_a
  have hκ : 0 < T.κ := hT.κ_pos
  have hσ : 0 < T.σ := hT.σ_pos
  have hg6 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gapProfile h T.a) := contDiff_gapProfile hs hp ha
  obtain ⟨M, hM0, hM⟩ := exists_gapProfile_bound hg6 R₀
  set e' : ℕ → ℝ := fun j => |e j| with he'
  have he0 : ∀ j, 0 ≤ e' j := fun j => abs_nonneg _
  set BE := doubleSumRangeNine D with hBE
  have hBE0 : 0 ≤ BE := doubleSumRangeNine_nonneg hD
  set B₁ := BE + R₀ + 1 with hB₁
  have hB₁1 : 1 ≤ B₁ := by linarith
  have hB₁0 : 0 ≤ B₁ := by linarith
  set Cg := gapJetConstant M B₁ with hCg
  have hCg0 : 0 ≤ Cg := Finset.sum_nonneg fun m _ => by positivity
  have hE1 : 1 ≤ T.E := hT.one_le_E
  have hlarge := runningMax_nonneg e' 6
  set B₂ := C * runningMax e' 6 + T.E + 1 with hB₂
  have hCl : 0 ≤ C * runningMax e' 6 := mul_nonneg hC.le hlarge
  have hB₂0 : 0 ≤ B₂ := by linarith
  set B₄ := |T.lam / 2| with hB₄
  have hB₄0 : 0 ≤ B₄ := abs_nonneg _
  set K₁ := 6912 * BE + 6912 * B₄ + 5000 * Cg + 640 * (N : ℝ) * B₁ with hK₁
  set K₂ := 640 * (N : ℝ) * B₂ with hK₂
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  refine ⟨1, K₁ + K₂, one_pos, by positivity, fun l₁ hl0 hl₁ t f F V Y hfam hF hV => ?_⟩
  obtain ⟨hFL, hFt, n, hside, hnn⟩ := id hF
  have hs1 : ∀ i, 1 ≤ F.extent i := fun i => by rw [hside i]; omega
  haveI hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
    have h1 : F.top - F.top = 0 := Nat.sub_self _
    simp only [BlockFrame.period, h1, pow_zero, mul_one]
    have := hs1 i
    omega⟩
  haveI hfin : Finite (F.Site F.top) := inferInstance
  have hKst : ∀ η ∈ closedBondBalls F T.ballRadius, HasInterpolationKernels 0 T.a T.ρA T.κ T.chainParams.κ₂
      T.chainParams.δ₂ T.coupling (frameRadius T.coupling) Kf D V η :=
    fun η hη => hKe T.coupling t F V 0 η le_rfl hF hV le_rfl zero_le_one hη
  have hval := fun η (hη : η ∈ closedBondBalls F T.ballRadius) => hVb t F V η hF hV hη
  have hr8 : 2 ^ 7 * T.κ ≤ 2 ^ 8 * T.κ := by nlinarith
  have hr0 : 0 ≤ T.chainParams.δ₂ := le_trans (by positivity) hκr
  have hGp : ∀ c ∈ cellTopBonds F Y, IsDecayingPart T.κ T.ballRadius l₁ Y V (gapTerm T.a T.ρA c)
      (fun ζ => |(1 : ℝ)| * Cg * (1 + ∑ α, |scaledCoord α ((1 : ℝ), ζ)| * scaledCoordDecay T.κ Y α) ^ 3)
      (fun _ ζ => (0 + |(1 : ℝ)| * (3 * 3 + 1)) * Cg *
        (1 + ∑ α, |scaledCoord α ((1 : ℝ), ζ)| * scaledCoordDecay T.κ Y α) ^ 3) := by
    intro c hc
    have hcb : c ∈ innerBonds (finiteCells F) F.top := (Finset.mem_filter.1 hc).1
    have hcY : c.1 = Y := (Finset.mem_filter.1 hc).2
    have hk := isDecayingKernel_logContourAverage hD hR₀ hKst c (fun η hη => (hval η hη).2.1 c hcb)
    rw [hcY] at hk
    exact decayingPart_gapTerm hk hB₁1 hκ hr8 (by linarith) ha (contDiff_infty.1 hg6 6) htail hM0
      (fun η hη s hs' p hp' => hM s _ hs' ((hval η hη).2.1 c hcb) p hp') hV
      (fun V' hV' η hη => (hLE t F V' hF hV').2.2.1 η hη c hcb)
  have hHr : ∀ b ∈ cellChordBonds F Y, IsDecayingPart T.κ T.ballRadius l₁ Y V
      (rayObservable (minimizerHaarLogRatio T.a T.ρA b) id (fun _ => 1))
      (plainBound T.κ Y B₁) (plainSlopeBound T.κ Y B₁) := by
    intro b hb
    have hbY : enclosingCell b.1.1 = Y := (Finset.mem_filter.1 hb).2
    have hk := isDecayingKernel_minimizerHaarLogRatio hD hR₀ hKst b (fun η hη => (hval η hη).2.2 b)
    rw [hbY] at hk
    exact decayingPart_plain hk hB₁0 hκ hr8 (by linarith) mem_closedBondBalls_of_scale
  have hSq : IsDecayingPart T.κ T.ballRadius l₁ Y V
      (fun l ζ V' => ∑ q ∈ quadraticIndex F Y,
        rayObservable (diagonalKernel T.lam q) id (chordCoordProduct q.1 q.2) l ζ V')
      (quadraticBound T.κ Y B₄) (quadraticSlopeBound T.κ Y B₄) := by
    refine decayingPart_quadSum (r := 2 ^ 7 * T.κ) (S := closedBondBalls F T.ballRadius) (fun q _ => ?_) hB₄0 hκ
      le_rfl (by linarith) mem_closedBondBalls_of_scale
    show IsDecayingKernel V (fun _ _ => if q.1 = q.2 then T.lam / 2 else 0) _ _ _ _ _
    refine isDecayingKernel_const hB₄0 ?_ fun hc => ?_
    · split_ifs
      · exact le_rfl
      · simpa using hB₄0
    · have hq : q.1 = q.2 := by
        by_contra hne
        exact hc (if_neg hne)
      rw [hq]
      simp [cellSetDiameter_singleton]
  have hQ : IsDecayingPart T.κ T.ballRadius l₁ Y V (quadraticPart (minimizerEnergy T.a T.ρA) Y)
      (quadraticBound T.κ Y BE) (quadraticSlopeBound T.κ Y BE) := by
    by_cases hne' : Nonempty (ChordCoord F)
    · have hE := isDecayingEnergy_minimizerEnergy hD hne' hKst
      have hk : ∀ q ∈ quadraticIndex F Y,
          IsDecayingKernel V (taylorRemainderMean (secondDerivKernel (minimizerEnergy T.a T.ρA) q.1 q.2)) BE
            T.chainParams.δ₂ {enclosingCell q.1.1.1.1, enclosingCell q.2.1.1.1} (closedBondBalls F T.ballRadius) 6 :=
        fun q _ => isDecayingKernel_taylorRemainderMean (isDecayingKernel_secondDerivKernel hE hr0 hBE0 q.1 q.2)
          smul_mem_closedBondBalls hBE0
      exact (decayingPart_quadSum hk hBE0 hκ hκr (by linarith) mem_closedBondBalls_of_scale).congr
        fun k c X p hp' => quadraticPart_eventuallyEq hE smul_mem_closedBondBalls c X p
          (mem_closedBondBalls_of_scale p hp')
    · have hem : IsEmpty ↥(chordBonds (finiteCells F)) := ⟨fun b => hne' ⟨(b, 0)⟩⟩
      have hq : IsEmpty (ChordCoord F) := not_nonempty_iff.1 hne'
      have e1 : quadraticPart (minimizerEnergy T.a T.ρA) Y = fun _ _ _ => (0 : ℝ) := by
        funext l ζ V'
        simp [quadraticPart]
      have e2 : quadraticBound T.κ Y BE = fun _ => (0 : ℝ) := by
        funext ζ
        simp [quadraticBound, quadraticIndex]
      have e3 : quadraticSlopeBound T.κ Y BE = fun _ _ => (0 : ℝ) := by
        funext b ζ
        simp [quadraticSlopeBound, quadraticIndex]
      rw [e1, e2, e3]
      exact isDecayingPart_zero
  have hLow : IsCubicTorusAbove T.L t T.n₀ F := ⟨hFL, hFt, n, hside, by nlinarith⟩
  have hTst : ∀ η ∈ closedBondBalls F T.ballRadius,
      IsTransportBounded 0 T.a T.ρA T.κ T.decayRate C Ck T.L (frameRadius T.coupling) 6 e' f V η :=
    fun η hη => hTr T.coupling t 6 e' f F V 0 η le_rfl (by norm_num) le_rfl he0 (hasBoundedDerivatives_abs hfam.2)
      hF hV le_rfl zero_le_one hη
  have hR : ∀ y ∈ cellLayerSites F Y, IsDecayingPart T.κ T.ballRadius l₁ Y V
      (rayObservable (centredExpansion true T.a T.ρA 0 f y) id (fun _ => 1))
      (plainBound T.κ Y B₂) (plainSlopeBound T.κ Y B₂) := by
    intro y hy
    have hyY : enclosingCell y = Y := (Finset.mem_filter.1 hy).2
    have hk := isDecayingKernel_centredExpansion (B₀ := T.E) (B := B₂) he0 hC.le (by linarith) (by linarith) hTst y
      (fun η hη => abs_subtractTrivial_le hfam.1 hL hσ hLow hs1 y _ (hval η hη).1)
    rw [hyY] at hk
    exact decayingPart_plain hk hB₂0 hκ le_rfl (by linarith) mem_closedBondBalls_of_scale
  have hcardB : ((cellChordBonds F Y).card : ℝ) ≤ N := by
    exact_mod_cast hN F hFL ↥(chordBonds (finiteCells F)) (fun b => b.1) Subtype.val_injective Y
  have hcardS : ((cellLayerSites F Y).card : ℝ) ≤ N := by
    have h1 := hN F hFL ↥(cellLayerSites F Y) (fun y => (y.1, 0))
      (fun y y' hyy => Subtype.ext (congrArg Prod.fst hyy)) Y
    have h2 : (Finset.univ.filter fun b : ↥(cellLayerSites F Y) => enclosingCell (b.1, (0 : Fin 4)).1 = Y) =
        Finset.univ := by
      ext b
      simpa using (Finset.mem_filter.1 b.2).2
    rw [h2] at h1
    simp only [Finset.card_univ, Fintype.card_coe] at h1
    exact_mod_cast h1
  have hcardG : ((cellTopBonds F Y).card : ℝ) ≤ 4 := by exact_mod_cast cellTopBonds_card_le
  have hnum : ∀ ζ : StepVariable (finiteCells F), ∃ w : ℝ, w = (1 + localWeight T.κ Y ζ) ^ 7 ∧ 0 ≤ w ∧
      (chordNear T.κ Y ζ) ^ 2 * (1 + chordNear T.κ Y ζ) ^ 3 ≤ 576 * w ∧
      (6 * chordNear T.κ Y ζ + 10 * chordNear T.κ Y ζ ^ 2) * (1 + chordNear T.κ Y ζ) ^ 3 ≤ 6912 * w ∧
      (1 + chordNear T.κ Y ζ) ^ 3 ≤ 64 * w ∧ (1 + (1 + chordNear T.κ Y ζ)) ^ 3 ≤ 125 * w := by
    intro ζ
    have hn0 := localWeight_nonneg T.κ Y ζ
    obtain ⟨p1, p2, p3, p4⟩ := final_power_bounds (chordNear_nonneg T.κ Y ζ)
      (by linarith : 1 ≤ 1 + localWeight T.κ Y ζ)
      (by have := chordNear_le (κ := T.κ) (Y := Y) ζ; linarith)
    exact ⟨_, rfl, by positivity, p1, p2, p3, p4⟩
  have hclS : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l → (∀ b, l * ‖ζ b‖ ≤ T.ballRadius) →
      l • ζ ∈ closedBondBalls F T.ballRadius :=
    fun l ζ hl hb b => by
      have h3 : ‖(l • ζ) b‖ = l * ‖ζ b‖ := by
        rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hl.le]
      rw [h3]
      exact hb b
  have hclKer : ∀ {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {B r : ℝ} {P : Finset F.Cell}
      {m : StepVariable (finiteCells F) → ℝ} {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions),
      IsDecayingKernel V G B r P (closedBondBalls F T.ballRadius) 6 → ContDiff ℝ (6 : ℕ) m →
      ExtendsToClosedBalls T.ballRadius l₁ V (rayObservable G id m) c X := fun c X hk hm =>
    ExtendsToClosedBalls.of_contDiffAt fun l ζ hl _ hb =>
      contDiffAt_rayObservable_of_mem contDiff_id hm hk.smooth _ c X (l, ζ) (hclS l ζ hl hb)
  have hclGap : ∀ c₀ ∈ cellTopBonds F Y, ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions),
      ExtendsToClosedBalls T.ballRadius l₁ V (gapTerm T.a T.ρA c₀) c X := by
    intro c₀ hc k c X
    have hcb : c₀ ∈ innerBonds (finiteCells F) F.top := (Finset.mem_filter.1 hc).1
    have hk := isDecayingKernel_logContourAverage hD hR₀ hKst c₀ (fun η hη => (hval η hη).2.1 c₀ hcb)
    refine ⟨scaledObservable (rayObservable (fun (x : ScaledPoint F) V' =>
      gapProfile h T.a (x.1, logContourAverage T.a T.ρA c₀ x.2 V'))
      (fun ζ => ((1 : ℝ), ζ)) (fun _ => 1)) V c X, ?_, fun l ζ hl _ hb => ?_⟩
    · filter_upwards [eventually_smallCurvature c X hV] with τ hτ l ζ hl _ hb
      have hb' : ∀ b, ‖(l • ζ) b‖ < T.ballRadius := fun b => by
        have h3 : ‖(l • ζ) b‖ = l * ‖ζ b‖ := by
          rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hl.le]
        rw [h3]
        exact hb b
      have hr' := (hLE t F _ hF hτ).2.2.1 _ hb' c₀ hcb
      simp only [scaledObservable, gapTerm, rayObservable]
      rw [haarGapShift_eq_gapProfile htail ha hr']
      simp [logContourAverage]
    · refine contDiffAt_rayObservable_of_mem (S := {x : ScaledPoint F | x.2 ∈ closedBondBalls F T.ballRadius})
        (contDiff_const.prodMk contDiff_id) contDiff_const
        (fun k' c' X' => contDiffAt_translated_gapProfile hk (contDiff_infty.1 hg6 6) k' c' X') k c X (l, ζ) ?_
      simpa using hclS l ζ hl hb
  have hclQ : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      ExtendsToClosedBalls T.ballRadius l₁ V (quadraticPart (minimizerEnergy T.a T.ρA) Y) c X := by
    intro k c X
    by_cases hne' : Nonempty (ChordCoord F)
    · have hE := isDecayingEnergy_minimizerEnergy hD hne' hKst
      have hk : ∀ q ∈ quadraticIndex F Y,
          IsDecayingKernel V (taylorRemainderMean (secondDerivKernel (minimizerEnergy T.a T.ρA) q.1 q.2)) BE
            T.chainParams.δ₂ {enclosingCell q.1.1.1.1, enclosingCell q.2.1.1.1} (closedBondBalls F T.ballRadius) 6 :=
        fun q _ => isDecayingKernel_taylorRemainderMean (isDecayingKernel_secondDerivKernel hE hr0 hBE0 q.1 q.2)
          smul_mem_closedBondBalls hBE0
      refine ExtendsToClosedBalls.of_contDiffAt fun l ζ hl _ hb => ?_
      have hform : ContDiffAt ℝ (6 : ℕ) (scaledObservable (fun l ζ V' => ∑ q ∈ quadraticIndex F Y,
          rayObservable (taylorRemainderMean (secondDerivKernel (minimizerEnergy T.a T.ρA) q.1 q.2)) id
            (chordCoordProduct q.1 q.2) l ζ V') V c X) ((l, ζ), 0) :=
        ContDiffAt.sum fun q hq => contDiffAt_rayObservable_of_mem contDiff_id (chordCoordProduct_contDiff q.1 q.2)
          (hk q hq).smooth k c X (l, ζ) (hclS l ζ hl hb)
      exact hform.congr_of_eventuallyEq
        (quadraticPart_eventuallyEq hE smul_mem_closedBondBalls c X (l, ζ) (hclS l ζ hl hb))
    · have hem : IsEmpty ↥(chordBonds (finiteCells F)) := ⟨fun b => hne' ⟨(b, 0)⟩⟩
      have e1 : quadraticPart (minimizerEnergy T.a T.ρA) Y = fun _ _ _ => (0 : ℝ) := by
        funext l ζ V'
        simp [quadraticPart]
      rw [e1]
      exact ExtendsToClosedBalls.of_contDiffAt fun _ _ _ _ _ => contDiffAt_const
  have hclSq : ∀ q ∈ quadraticIndex F Y, ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions),
      ExtendsToClosedBalls T.ballRadius l₁ V (rayObservable (diagonalKernel T.lam q) id (chordCoordProduct q.1 q.2))
        c X := by
    intro q _ k c X
    refine hclKer (B := B₄) (r := 2 ^ 7 * T.κ) (P := {enclosingCell q.1.1.1.1, enclosingCell q.2.1.1.1}) c X ?_
      (chordCoordProduct_contDiff q.1 q.2)
    show IsDecayingKernel V (fun _ _ => if q.1 = q.2 then T.lam / 2 else 0) _ _ _ _ _
    refine isDecayingKernel_const hB₄0 ?_ fun hc => ?_
    · split_ifs
      · exact le_rfl
      · simpa using hB₄0
    · have hq : q.1 = q.2 := by
        by_contra hne
        exact hc (if_neg hne)
      rw [hq]
      simp [cellSetDiameter_singleton]
  constructor
  · have hgood := ((hQ.add ((IsDecayingPart.sum (cellTopBonds F Y) hGp).const_mul (-1))).add
      ((IsDecayingPart.sum (cellChordBonds F Y) hHr).const_mul (-1))).add (hSq.const_mul (-1))
    have hfun : (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) = fun l ζ V' =>
        quadraticPart (minimizerEnergy T.a T.ρA) Y l ζ V' + -1 * ∑ c ∈ cellTopBonds F Y, gapTerm T.a T.ρA c l ζ V' +
          -1 * ∑ b ∈ cellChordBonds F Y, rayObservable (minimizerHaarLogRatio T.a T.ρA b) id (fun _ => 1) l ζ V' +
          -1 * ∑ q ∈ quadraticIndex F Y,
            rayObservable (diagonalKernel T.lam q) id (chordCoordProduct q.1 q.2) l ζ V' := by
      funext l ζ V'
      exact rescaledCellRemainder_eq _ _ _ _ _ _ _
    have hcl : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
        ExtendsToClosedBalls T.ballRadius l₁ V (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) c X := by
      intro k c X
      rw [hfun]
      exact (((hclQ c X).add ((ExtendsToClosedBalls.sum (cellTopBonds F Y) fun c₀ hc =>
          hclGap c₀ hc c X).const_mul (-1))).add
        ((ExtendsToClosedBalls.sum (cellChordBonds F Y) fun b hb =>
          hclKer c X (isDecayingKernel_minimizerHaarLogRatio hD hR₀ hKst b (fun η hη => (hval η hη).2.2 b))
            contDiff_const).const_mul (-1))).add
        ((ExtendsToClosedBalls.sum (quadraticIndex F Y) fun q hq => hclSq q hq c X).const_mul (-1))
    refine isSmoothObservable_of_decayingPart (K := K₁ + K₂) (hfun ▸ hgood)
      (fun l ζ V' => rescaledCellRemainder_neg _ _ _ _ _ _ _) ?_ hcl ?_
    · intro ζ
      obtain ⟨w, hw, hw0, p1, p2, p3, p4⟩ := hnum ζ
      rw [← hw]
      have t1 := quadraticBound_le (Y := Y) hκ hBE0 ζ
      have t4 := quadraticBound_le (Y := Y) hκ hB₄0 ζ
      simp only [Finset.sum_const, nsmul_eq_mul, abs_neg, abs_one, one_mul, scaledNear_eq, plainBound_eq]
      have a1 : ((cellTopBonds F Y).card : ℝ) * (Cg * (1 + (1 + chordNear T.κ Y ζ)) ^ 3) ≤ 4 * (Cg * (125 * w)) :=
        mul_le_mul hcardG (mul_le_mul_of_nonneg_left p4 hCg0)
          (mul_nonneg hCg0 (pow_nonneg (by have := chordNear_nonneg T.κ Y ζ; linarith) _)) (by norm_num)
      have a2 : ((cellChordBonds F Y).card : ℝ) * (B₁ * (1 + chordNear T.κ Y ζ) ^ 3) ≤ (N : ℝ) * (B₁ * (64 * w)) :=
        mul_le_mul hcardB (mul_le_mul_of_nonneg_left p3 hB₁0)
          (mul_nonneg hB₁0 (pow_nonneg (by have := chordNear_nonneg T.κ Y ζ; linarith) _)) hNn
      have a3 : BE * chordNear T.κ Y ζ ^ 2 * (1 + chordNear T.κ Y ζ) ^ 3 ≤ BE * (576 * w) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left p1 hBE0
      have a4 : B₄ * chordNear T.κ Y ζ ^ 2 * (1 + chordNear T.κ Y ζ) ^ 3 ≤ B₄ * (576 * w) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left p1 hB₄0
      have b1 : 0 ≤ BE * w := mul_nonneg hBE0 hw0
      have b2 : 0 ≤ B₄ * w := mul_nonneg hB₄0 hw0
      have b3 : 0 ≤ Cg * w := mul_nonneg hCg0 hw0
      have b4 : 0 ≤ (N : ℝ) * B₁ * w := mul_nonneg (mul_nonneg hNn hB₁0) hw0
      have b5 : 0 ≤ (N : ℝ) * B₂ * w := mul_nonneg (mul_nonneg hNn hB₂0) hw0
      rw [hK₁, hK₂]
      have t1' := t1.trans a3
      have t4' := t4.trans a4
      linarith
    · intro b ζ
      obtain ⟨w, hw, hw0, p1, p2, p3, p4⟩ := hnum ζ
      rw [← hw]
      have t1 := quadraticSlopeBound_le (Y := Y) hκ hBE0 b ζ
      have t4 := quadraticSlopeBound_le (Y := Y) hκ hB₄0 b ζ
      simp only [Finset.sum_const, nsmul_eq_mul, abs_neg, abs_one, one_mul, scaledNear_eq, plainSlopeBound_eq]
      have e10 : (0 + (3 * 3 + 1) : ℝ) = 10 := by norm_num
      rw [e10]
      have a1 : ((cellTopBonds F Y).card : ℝ) * (10 * Cg * (1 + (1 + chordNear T.κ Y ζ)) ^ 3) ≤
          4 * (10 * Cg * (125 * w)) :=
        mul_le_mul hcardG (mul_le_mul_of_nonneg_left p4 (mul_nonneg (by norm_num) hCg0))
          (mul_nonneg (mul_nonneg (by norm_num) hCg0)
            (pow_nonneg (by have := chordNear_nonneg T.κ Y ζ; linarith) _))
          (by norm_num)
      have a2 : ((cellChordBonds F Y).card : ℝ) * (10 * (B₁ * (1 + chordNear T.κ Y ζ) ^ 3)) ≤
          (N : ℝ) * (10 * (B₁ * (64 * w))) :=
        mul_le_mul hcardB (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left p3 hB₁0) (by norm_num))
          (mul_nonneg (by norm_num) (mul_nonneg hB₁0
            (pow_nonneg (by have := chordNear_nonneg T.κ Y ζ; linarith) _))) hNn
      have a3 : BE * (6 * chordNear T.κ Y ζ + 10 * chordNear T.κ Y ζ ^ 2) * (1 + chordNear T.κ Y ζ) ^ 3 ≤
          BE * (6912 * w) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left p2 hBE0
      have a4 : B₄ * (6 * chordNear T.κ Y ζ + 10 * chordNear T.κ Y ζ ^ 2) * (1 + chordNear T.κ Y ζ) ^ 3 ≤
          B₄ * (6912 * w) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left p2 hB₄0
      have b1 : 0 ≤ BE * w := mul_nonneg hBE0 hw0
      have b2 : 0 ≤ B₄ * w := mul_nonneg hB₄0 hw0
      have b3 : 0 ≤ Cg * w := mul_nonneg hCg0 hw0
      have b4 : 0 ≤ (N : ℝ) * B₁ * w := mul_nonneg (mul_nonneg hNn hB₁0) hw0
      have b5 : 0 ≤ (N : ℝ) * B₂ * w := mul_nonneg (mul_nonneg hNn hB₂0) hw0
      rw [hK₁, hK₂]
      have t1' := t1.trans a3
      have t4' := t4.trans a4
      linarith
  · have hgood := IsDecayingPart.sum (cellLayerSites F Y) hR
    have hfun : (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) = fun l ζ V' =>
        ∑ y ∈ cellLayerSites F Y, rayObservable (centredExpansion true T.a T.ρA 0 f y) id (fun _ => 1) l ζ V' := by
      funext l ζ V'
      simp [rescaledCellExpansion, cellCentredExpansion, rayObservable, cellLayerSites]
    have hcl : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
        ExtendsToClosedBalls T.ballRadius l₁ V (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) c X := by
      intro k c X
      rw [hfun]
      exact ExtendsToClosedBalls.sum (cellLayerSites F Y) fun y hy =>
        hclKer c X (isDecayingKernel_centredExpansion (B₀ := T.E) (B := B₂) he0 hC.le (by linarith) (by linarith) hTst y
          (fun η hη => abs_subtractTrivial_le hfam.1 hL hσ hLow hs1 y _ (hval η hη).1)) contDiff_const
    refine isSmoothObservable_of_decayingPart (K := K₁ + K₂) (hfun ▸ hgood) (fun l ζ V' => ?_) ?_ hcl ?_
    · simp [rescaledCellExpansion]
    · intro ζ
      obtain ⟨w, hw, hw0, p1, p2, p3, p4⟩ := hnum ζ
      rw [← hw]
      simp only [Finset.sum_const, nsmul_eq_mul, plainBound_eq]
      have a2 : ((cellLayerSites F Y).card : ℝ) * (B₂ * (1 + chordNear T.κ Y ζ) ^ 3) ≤ (N : ℝ) * (B₂ * (64 * w)) :=
        mul_le_mul hcardS (mul_le_mul_of_nonneg_left p3 hB₂0)
          (mul_nonneg hB₂0 (pow_nonneg (by have := chordNear_nonneg T.κ Y ζ; linarith) _)) hNn
      have b5 : 0 ≤ (N : ℝ) * B₂ * w := mul_nonneg (mul_nonneg hNn hB₂0) hw0
      have b6 : 0 ≤ K₁ * w := mul_nonneg hK₁0 hw0
      rw [add_mul, hK₂]
      linarith
    · intro b ζ
      obtain ⟨w, hw, hw0, p1, p2, p3, p4⟩ := hnum ζ
      rw [← hw]
      simp only [Finset.sum_const, nsmul_eq_mul, plainSlopeBound_eq]
      have a2 : ((cellLayerSites F Y).card : ℝ) * (10 * (B₂ * (1 + chordNear T.κ Y ζ) ^ 3)) ≤
          (N : ℝ) * (10 * (B₂ * (64 * w))) :=
        mul_le_mul hcardS (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left p3 hB₂0) (by norm_num))
          (mul_nonneg (by norm_num) (mul_nonneg hB₂0
            (pow_nonneg (by have := chordNear_nonneg T.κ Y ζ; linarith) _))) hNn
      have b5 : 0 ≤ (N : ℝ) * B₂ * w := mul_nonneg (mul_nonneg hNn hB₂0) hw0
      have b6 : 0 ≤ K₁ * w := mul_nonneg hK₁0 hw0
      rw [add_mul, hK₂]
      linarith
theorem eventually_rate_below_chain :
    EventuallyInParameters fun T => 2 ^ 7 * T.κ ≤ T.chainParams.δ₂ ∧ 3 ≤ T.L := by
  intro a _
  refine ⟨3, fun L _ hL c hc => ⟨0, fun Ct _ => ?_⟩⟩
  have hδ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  refine ⟨c.δ₂ / 2 ^ 7, by positivity, fun κ _ hκ => ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun nss _ =>
    ⟨1, one_pos, fun σ _ _ p _ => ⟨0, fun Cs _ E _ => ⟨0, fun n₀ _ => ⟨0, fun CE _ => ⟨0, fun y₁ _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩
  refine ⟨?_, hL⟩
  show 2 ^ 7 * κ ≤ c.δ₂
  rw [le_div_iff₀ (by positivity)] at hκ
  linarith
theorem rescaledPartsSmooth_proof (hTr : Interpolation.transportBoundsStatement)
    (hKe : Interpolation.interpolationKernelBoundsStatement)
    (hLE : ReferenceDensity.chartedEnergyAtMinimizerRegular) (hVal : StepDensities.valuesAboveFrameBoundedStatement)
    (hTail : ScaledVariables.HaarGapTailSmooth) (hBonds : CellCounting.BondsPerCellBounded) :
    StepDensities.rescaledPartsSmoothStatement := by
  obtain ⟨C, Ck, hC, -, h1⟩ := hTr
  obtain ⟨Kf, D, -, hD, h2⟩ := hKe
  obtain ⟨h, hs, hp, htail⟩ := hTail
  have A := EventuallyInParameters.and (EventuallyInParameters.and h1 h2) eventually_rate_below_chain
  have B : EventuallyOrdered _ := EventuallyInParameters.mono A fun T g _ _ => g
  have Cc := EventuallyOrdered.and (EventuallyOrdered.and B hLE) hVal
  refine EventuallyOrdered.mono Cc fun T hT hn g => ?_
  obtain ⟨⟨⟨⟨g1, g2⟩, g3, g4⟩, g5⟩, g6⟩ := g
  have hL0 : 0 < T.L := by omega
  obtain ⟨N, hN⟩ := hBonds T.L hL0
  intro e
  exact rescaledParts_of_parameters T hT hn g3 g4 (hC _) g1 (hD _) g2 g5 g6 hs hp htail N hN e
end
end YangMills.Construction.RescaledParts
end

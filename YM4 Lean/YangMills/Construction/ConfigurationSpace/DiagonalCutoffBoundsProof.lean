import YangMills.Construction.BumpFunctions.SmoothBumpsGevreyBounds
import YangMills.Construction.ConfigurationSpace.DiagonalCutoffBounds
import YangMills.Construction.ConfigurationSpace.MinSeparationProperties
import YangMills.Construction.ConfigurationSpace.ShellCenterCountProof
import YangMills.Construction.Continuum.NormFactorialInequalities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace.DiagonalCutoff
open YangMills.Construction.BumpFunctions YangMills.Construction.WhitneyScales
open YangMills.Construction.TestFunctions
open scoped ContDiff
section Derivatives
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {I : Type*}
def listDeriv (e : I → V) (L : List I) (f : V → ℂ) : V → ℂ :=
  L.foldl (fun g ι => dirDeriv (e ι) g) f
theorem listDeriv_cons (e : I → V) (ι : I) (L : List I) (f : V → ℂ) :
    listDeriv e (ι :: L) f = listDeriv e L (dirDeriv (e ι) f) := rfl
theorem listDeriv_append (e : I → V) (L M : List I) (f : V → ℂ) :
    listDeriv e (L ++ M) f = listDeriv e M (listDeriv e L f) := by
  simp [listDeriv, List.foldl_append]
theorem iterate_dirDeriv_eq_listDeriv (e : I → V) (ι : I) (k : ℕ) (f : V → ℂ) :
    (dirDeriv (e ι))^[k] f = listDeriv e (List.replicate k ι) f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih]; rfl
theorem exists_listDeriv_eq_foldr (e : I → V) (α : I → ℕ) (l : List I) :
    ∃ L : List I, L.length = (l.map α).sum ∧ ∀ f : V → ℂ,
      l.foldr (fun ι g => (dirDeriv (e ι))^[α ι] g) f = listDeriv e L f := by
  induction l with
  | nil => exact ⟨[], rfl, fun _ => rfl⟩
  | cons a l ih =>
    obtain ⟨L, hl, h⟩ := ih
    refine ⟨L ++ List.replicate (α a) a, ?_, fun f => ?_⟩
    · simp [hl, add_comm]
    · rw [List.foldr_cons, h, iterate_dirDeriv_eq_listDeriv, listDeriv_append]
theorem exists_listDeriv_eq_iterDirDeriv [Fintype I] [LinearOrder I] (e : I → V)
    (α : MultiIdx I) :
    ∃ L : List I, L.length = MultiIdx.order α ∧ ∀ f : V → ℂ,
      iterDirDeriv e α f = listDeriv e L f := by
  obtain ⟨L, hl, h⟩ := exists_listDeriv_eq_foldr (V := V) e α ((Finset.univ : Finset I).sort (· ≤ ·))
  refine ⟨L, hl.trans ?_, h⟩
  have := List.sum_toFinset α (Finset.sort_nodup (Finset.univ : Finset I) (· ≤ ·))
  rw [Finset.sort_toFinset] at this
  exact this.symm
theorem dirDeriv_eq_fderiv (v : V) {f : V → ℂ} (hf : ContDiff ℝ ∞ f) :
    dirDeriv v f = fun x => fderiv ℝ f x v := by
  funext x
  exact (hf.differentiable (by simp) x).lineDeriv_eq_fderiv
theorem contDiff_dirDeriv (v : V) {f : V → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dirDeriv v f) := by
  rw [dirDeriv_eq_fderiv v hf]
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
theorem dirDeriv_add_const_mul (v : V) {f g : V → ℂ} (c : ℂ) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) :
    dirDeriv v (fun x => f x + c * g x) =
      fun x => dirDeriv v f x + c * dirDeriv v g x := by
  have hfg : ContDiff ℝ ∞ (fun x => f x + c * g x) := hf.add (contDiff_const.mul hg)
  rw [dirDeriv_eq_fderiv v hf, dirDeriv_eq_fderiv v hg, dirDeriv_eq_fderiv v hfg]
  funext x
  have h1 := (hf.differentiable (by simp) x).hasFDerivAt
  have h2 := (hg.differentiable (by simp) x).hasFDerivAt
  have h3 : HasFDerivAt (fun x => f x + c * g x) _ x := h1.add (h2.const_mul c)
  rw [h3.fderiv]
  simp
theorem listDeriv_add_const_mul (e : I → V) (L : List I) {f g : V → ℂ} (c : ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    listDeriv e L (fun x => f x + c * g x) =
      fun x => listDeriv e L f x + c * listDeriv e L g x := by
  induction L generalizing f g with
  | nil => rfl
  | cons a L ih =>
    rw [listDeriv_cons, dirDeriv_add_const_mul _ c hf hg,
      ih (contDiff_dirDeriv _ hf) (contDiff_dirDeriv _ hg)]
    rfl
theorem dirDeriv_mul (v : V) {f g : V → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    dirDeriv v (fun x => f x * g x) =
      fun x => dirDeriv v f x * g x + 1 * (f x * dirDeriv v g x) := by
  have hfg : ContDiff ℝ ∞ (fun x => f x * g x) := hf.mul hg
  rw [dirDeriv_eq_fderiv v hf, dirDeriv_eq_fderiv v hg, dirDeriv_eq_fderiv v hfg]
  funext x
  have h1 := (hf.differentiable (by simp) x).hasFDerivAt
  have h2 := (hg.differentiable (by simp) x).hasFDerivAt
  have h3 : HasFDerivAt (fun x => f x * g x) _ x := h1.mul h2
  rw [h3.fderiv]
  simp
  ring
def shuffleSum : List I → (List I → List I → ℂ) → ℂ
  | [], G => G [] []
  | ι :: L, G => shuffleSum L (fun s t => G (ι :: s) t) + shuffleSum L (fun s t => G s (ι :: t))
theorem listDeriv_mul (e : I → V) (L : List I) {f g : V → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (x : V) :
    listDeriv e L (fun y => f y * g y) x =
      shuffleSum L (fun s t => listDeriv e s f x * listDeriv e t g x) := by
  induction L generalizing f g with
  | nil => rfl
  | cons a L ih =>
    have hf' := contDiff_dirDeriv (e a) hf
    have hg' := contDiff_dirDeriv (e a) hg
    rw [listDeriv_cons, dirDeriv_mul _ hf hg,
      listDeriv_add_const_mul e L 1 (hf'.mul hg) (hf.mul hg')]
    simp only [one_mul]
    rw [ih hf' hg, ih hf hg']
    rfl
theorem norm_shuffleSum_le (w₁ w₂ : I → ℝ) (L : List I) (G : List I → List I → ℂ) (c : ℝ)
    (h : ∀ s t : List I, s.length + t.length = L.length →
      ‖G s t‖ ≤ c * ((s.map w₁).prod * (t.map w₂).prod)) :
    ‖shuffleSum L G‖ ≤ c * (L.map fun ι => w₁ ι + w₂ ι).prod := by
  induction L generalizing G c with
  | nil => simpa [shuffleSum] using h [] [] rfl
  | cons a L ih =>
    have h1 := ih (fun s t => G (a :: s) t) (c * w₁ a) (fun s t hst => by
      have := h (a :: s) t (by simp only [List.length_cons]; omega)
      simp only [List.map_cons, List.prod_cons] at this
      calc ‖G (a :: s) t‖ ≤ _ := this
        _ = _ := by ring)
    have h2 := ih (fun s t => G s (a :: t)) (c * w₂ a) (fun s t hst => by
      have := h s (a :: t) (by simp only [List.length_cons]; omega)
      simp only [List.map_cons, List.prod_cons] at this
      calc ‖G s (a :: t)‖ ≤ _ := this
        _ = _ := by ring)
    calc ‖shuffleSum (a :: L) G‖ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by simp only [List.map_cons, List.prod_cons]; ring
def ListGevreyBound (e : I → V) (f : V → ℂ) (w : I → ℝ) : Prop :=
  ∀ (L : List I) (x : V),
    ‖listDeriv e L f x‖ ≤ (L.map w).prod * (L.length.factorial : ℝ) ^ 2
theorem prod_map_weights_nonneg {w : I → ℝ} (hw : ∀ ι, 0 ≤ w ι) (L : List I) :
    0 ≤ (L.map w).prod :=
  List.prod_nonneg (by simp only [List.mem_map]; rintro _ ⟨ι, _, rfl⟩; exact hw ι)
theorem prod_map_weights_le {w w' : I → ℝ} (hw : ∀ ι, 0 ≤ w ι) (hww : ∀ ι, w ι ≤ w' ι)
    (L : List I) : (L.map w).prod ≤ (L.map w').prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_le_mul (hww a) ih (prod_map_weights_nonneg hw L) ((hw a).trans (hww a))
theorem ListGevreyBound.mono {e : I → V} {f : V → ℂ} {w w' : I → ℝ} (h : ListGevreyBound e f w)
    (hw : ∀ ι, 0 ≤ w ι) (hww : ∀ ι, w ι ≤ w' ι) : ListGevreyBound e f w' := fun L x =>
  (h L x).trans (mul_le_mul_of_nonneg_right (prod_map_weights_le hw hww L) (by positivity))
theorem ListGevreyBound.mul {e : I → V} {f g : V → ℂ} {w₁ w₂ : I → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hw₁ : ∀ ι, 0 ≤ w₁ ι) (hw₂ : ∀ ι, 0 ≤ w₂ ι)
    (b₁ : ListGevreyBound e f w₁) (b₂ : ListGevreyBound e g w₂) :
    ListGevreyBound e (fun x => f x * g x) (fun ι => w₁ ι + w₂ ι) := by
  intro L x
  rw [listDeriv_mul e L hf hg x, mul_comm]
  refine norm_shuffleSum_le w₁ w₂ L _ _ fun s t hst => ?_
  have hfac : (s.length.factorial : ℝ) * t.length.factorial ≤ L.length.factorial := by
    rw [← hst]
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  have hs := prod_map_weights_nonneg hw₁ s
  have ht := prod_map_weights_nonneg hw₂ t
  rw [norm_mul]
  calc ‖listDeriv e s f x‖ * ‖listDeriv e t g x‖
      ≤ ((s.map w₁).prod * (s.length.factorial : ℝ) ^ 2) *
          ((t.map w₂).prod * (t.length.factorial : ℝ) ^ 2) :=
        mul_le_mul (b₁ s x) (b₂ t x) (norm_nonneg _) (by positivity)
    _ = ((s.length.factorial : ℝ) * t.length.factorial) ^ 2 *
          ((s.map w₁).prod * (t.map w₂).prod) := by ring
    _ ≤ (L.length.factorial : ℝ) ^ 2 * ((s.map w₁).prod * (t.map w₂).prod) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hfac 2) (by positivity)
theorem dirDeriv_const (v : V) (c : ℂ) : dirDeriv v (fun _ : V => c) = fun _ => 0 := by
  rw [dirDeriv_eq_fderiv v contDiff_const]
  simp
theorem listDeriv_zero (e : I → V) (L : List I) :
    listDeriv e L (fun _ : V => (0 : ℂ)) = fun _ => 0 := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [listDeriv_cons, dirDeriv_const, ih]
theorem listGevreyBound_one (e : I → V) : ListGevreyBound e (fun _ => 1) (fun _ => 0) := by
  intro L x
  cases L with
  | nil => simp [listDeriv]
  | cons a L =>
    rw [listDeriv_cons, dirDeriv_const, listDeriv_zero]
    simp
theorem ListGevreyBound.prod {J : Type*} {e : I → V} (S : Finset J) {f : J → V → ℂ}
    {w : J → I → ℝ} (hf : ∀ q, ContDiff ℝ ∞ (f q)) (hw : ∀ q ι, 0 ≤ w q ι)
    (hb : ∀ q ∈ S, ListGevreyBound e (f q) (w q)) :
    ListGevreyBound e (fun x => ∏ q ∈ S, f q x) (fun ι => ∑ q ∈ S, w q ι) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using listGevreyBound_one e
  | insert a S ha ih =>
    have hS : ContDiff ℝ ∞ (fun x => ∏ q ∈ S, f q x) :=
      contDiff_prod fun q _ => hf q
    have h := ListGevreyBound.mul (hf a) hS (hw a) (fun ι => Finset.sum_nonneg fun q _ => hw q ι)
      (hb a (Finset.mem_insert_self a S))
      (ih fun q hq => hb q (Finset.mem_insert_of_mem hq))
    simpa only [Finset.prod_insert ha, Finset.sum_insert ha] using h
end Derivatives
section Factors
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {I : Type*}
def linearFormProd (U : ℕ → ℝ → ℝ) (ℓ : Fin 4 → V →L[ℝ] ℝ) (r : Fin 4 → ℕ) (x : V) : ℝ :=
  ∏ c, U (r c) (ℓ c x)
theorem hasDerivAt_linearFormProd {U : ℕ → ℝ → ℝ} {ℓ : Fin 4 → V →L[ℝ] ℝ}
    (hU : ∀ r t, HasDerivAt (U r) (U (r + 1) t) t) (r : Fin 4 → ℕ) (x v : V) (c₀ : Fin 4) (s : ℝ)
    (hv : ∀ c, ℓ c v = if c = c₀ then s else 0) :
    HasDerivAt (fun t : ℝ => linearFormProd U ℓ r (x + t • v))
      (s * linearFormProd U ℓ (r + Pi.single c₀ 1) x) 0 := by
  set P : ℝ := ∏ c ∈ Finset.univ.erase c₀, U (r c) (ℓ c x) with hP
  have hfun : (fun t : ℝ => linearFormProd U ℓ r (x + t • v)) =
      fun t => U (r c₀) (ℓ c₀ x + t * s) * P := by
    funext t
    unfold linearFormProd
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c₀), hP]
    congr 1
    · simp [hv]
    · refine Finset.prod_congr rfl fun c hc => ?_
      have hne : c ≠ c₀ := Finset.ne_of_mem_erase hc
      simp [hv, hne]
  have hval : linearFormProd U ℓ (r + Pi.single c₀ 1) x = U (r c₀ + 1) (ℓ c₀ x) * P := by
    unfold linearFormProd
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c₀), hP]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun c hc => ?_
      have hne : c ≠ c₀ := Finset.ne_of_mem_erase hc
      simp [hne]
  have hin : HasDerivAt (fun t : ℝ => ℓ c₀ x + t * s) s 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const s).const_add (ℓ c₀ x)
  have h0 : HasDerivAt (U (r c₀)) (U (r c₀ + 1) (ℓ c₀ x)) ((fun t : ℝ => ℓ c₀ x + t * s) 0) := by
    simpa using hU (r c₀) (ℓ c₀ x)
  have hc : HasDerivAt (fun t : ℝ => U (r c₀) (ℓ c₀ x + t * s))
      (U (r c₀ + 1) (ℓ c₀ x) * s) 0 := HasDerivAt.comp (0 : ℝ) h0 hin
  rw [hfun, hval]
  have e : s * (U (r c₀ + 1) (ℓ c₀ x) * P) = U (r c₀ + 1) (ℓ c₀ x) * s * P := by ring
  rw [e]
  exact hc.mul_const P
def affineProd (U : ℕ → ℝ → ℝ) (ℓ : Fin 4 → V →L[ℝ] ℝ) (b a : ℂ) (r : Fin 4 → ℕ) : V → ℂ :=
  fun x => b + a * (linearFormProd U ℓ r x : ℂ)
theorem dirDeriv_affineProd {U : ℕ → ℝ → ℝ} {ℓ : Fin 4 → V →L[ℝ] ℝ}
    (hU : ∀ r t, HasDerivAt (U r) (U (r + 1) t) t) (r : Fin 4 → ℕ) (v : V) (b a : ℂ) (c₀ : Fin 4)
    (s : ℝ) (hv : ∀ c, ℓ c v = if c = c₀ then s else 0) :
    dirDeriv v (affineProd U ℓ b a r) = affineProd U ℓ 0 (a * s) (r + Pi.single c₀ 1) := by
  funext x
  have h := hasDerivAt_linearFormProd hU r x v c₀ s hv
  have h2 : HasLineDerivAt ℝ (affineProd U ℓ b a r)
      (a * ((s * linearFormProd U ℓ (r + Pi.single c₀ 1) x : ℝ) : ℂ)) x v :=
    (h.ofReal_comp.const_mul a).const_add b
  unfold dirDeriv
  rw [h2.lineDeriv]
  simp only [affineProd]
  push_cast
  ring
theorem listDeriv_affineProd {U : ℕ → ℝ → ℝ} {ℓ : Fin 4 → V →L[ℝ] ℝ}
    (hU : ∀ r t, HasDerivAt (U r) (U (r + 1) t) t) (e : I → V) (dead : I → Prop)
    (hdir : ∀ ι, ∃ (c₀ : Fin 4) (s : ℝ), |s| ≤ 1 ∧ (dead ι → s = 0) ∧
      ∀ c, ℓ c (e ι) = if c = c₀ then s else 0)
    (L : List I) (b a : ℂ) (r : Fin 4 → ℕ) :
    ∃ (b' a' : ℂ) (r' : Fin 4 → ℕ),
      listDeriv e L (affineProd U ℓ b a r) = affineProd U ℓ b' a' r' ∧
      (L ≠ [] → b' = 0) ∧ (b = 0 → b' = 0) ∧ ‖a'‖ ≤ ‖a‖ ∧
      ∑ c, r' c = ∑ c, r c + L.length ∧ ((∃ ι ∈ L, dead ι) → a' = 0) := by
  induction L generalizing b a r with
  | nil => exact ⟨b, a, r, rfl, fun h => absurd rfl h, id, le_rfl, by simp, by simp⟩
  | cons ι L ih =>
    obtain ⟨c₀, s, hs, hd, hv⟩ := hdir ι
    obtain ⟨b', a', r', h, -, hb, ha, hr, hz⟩ := ih 0 (a * s) (r + Pi.single c₀ 1)
    refine ⟨b', a', r', ?_, fun _ => hb rfl, fun _ => hb rfl, ?_, ?_, ?_⟩
    · rw [listDeriv_cons, dirDeriv_affineProd hU r _ b a c₀ s hv, h]
    · refine ha.trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) hs
    · rw [hr]
      simp only [Pi.add_apply, Finset.sum_add_distrib, List.length_cons]
      simp
      omega
    · rintro ⟨ι', hι', hdead⟩
      rcases List.mem_cons.1 hι' with rfl | hL
      · have h0 : a * (s : ℂ) = 0 := by simp [hd hdead]
        rw [h0, norm_zero] at ha
        exact norm_le_zero_iff.1 ha
      · exact hz ⟨ι', hL, hdead⟩
theorem abs_linearFormProd_le {U : ℕ → ℝ → ℝ} (ℓ : Fin 4 → V →L[ℝ] ℝ) {A K : ℝ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : ∀ r t, |U r t| ≤ A * K ^ r * (r.factorial : ℝ) ^ 2)
    (hfac : ∀ k : Fin 4 → ℕ, ∏ a, (k a).factorial ≤ (∑ a, k a).factorial)
    (r : Fin 4 → ℕ) (x : V) :
    |linearFormProd U ℓ r x| ≤
      A ^ 4 * K ^ (∑ c, r c) * ((∑ c, r c).factorial : ℝ) ^ 2 := by
  unfold linearFormProd
  rw [Finset.abs_prod]
  calc ∏ c, |U (r c) (ℓ c x)|
      ≤ ∏ c, (A * K ^ (r c) * ((r c).factorial : ℝ) ^ 2) :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun c _ => hB _ _)
    _ = A ^ 4 * K ^ (∑ c, r c) * ((∏ c, (r c).factorial : ℕ) : ℝ) ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
          Finset.prod_pow, Nat.cast_prod]
        simp
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hfac r) 2
theorem listDeriv_one_sub_affineProd {U : ℕ → ℝ → ℝ} {ℓ : Fin 4 → V →L[ℝ] ℝ}
    (hU : ∀ r t, HasDerivAt (U r) (U (r + 1) t) t) (e : I → V) (dead : I → Prop)
    (hdir : ∀ ι, ∃ (c₀ : Fin 4) (s : ℝ), |s| ≤ 1 ∧ (dead ι → s = 0) ∧
      ∀ c, ℓ c (e ι) = if c = c₀ then s else 0)
    {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hB : ∀ r t, |U r t| ≤ A * K ^ r * (r.factorial : ℝ) ^ 2)
    (hfac : ∀ k : Fin 4 → ℕ, ∏ a, (k a).factorial ≤ (∑ a, k a).factorial)
    (L : List I) (hL : L ≠ []) (x : V) :
    ‖listDeriv e L (affineProd U ℓ 1 (-1) 0) x‖ ≤
        A ^ 4 * K ^ L.length * (L.length.factorial : ℝ) ^ 2 ∧
      ((∃ ι ∈ L, dead ι) → listDeriv e L (affineProd U ℓ 1 (-1) 0) x = 0) := by
  obtain ⟨b', a', r', h, hb, -, ha, hr, hz⟩ := listDeriv_affineProd hU e dead hdir L 1 (-1) 0
  have hb0 := hb hL
  have hsum : ∑ c, r' c = L.length := by simpa using hr
  rw [h, hb0]
  constructor
  · have hΦ := abs_linearFormProd_le ℓ hA hK hB hfac r' x
    rw [hsum] at hΦ
    simp only [affineProd, zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have ha1 : ‖a'‖ ≤ 1 := by simpa using ha
    calc ‖a'‖ * |linearFormProd U ℓ r' x| ≤ 1 * |linearFormProd U ℓ r' x| :=
          mul_le_mul_of_nonneg_right ha1 (abs_nonneg _)
      _ ≤ _ := by simpa using hΦ
  · intro hd
    simp [affineProd, hz hd]
theorem prod_map_weights_eq_pow {w : I → ℝ} {W : ℝ} (L : List I) (hw : ∀ ι ∈ L, w ι = W) :
    (L.map w).prod = W ^ L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [hw a (by simp), ih fun ι h => hw ι (by simp [h]), pow_succ]
    ring
end Factors
section Concrete
theorem whitneyScale_eq_inv_pow (j : ℕ) : whitneyScale j = ((2 : ℝ) ^ j)⁻¹ := by
  simp [whitneyScale, zpow_neg]
theorem whitneyScale_pos (j : ℕ) : 0 < whitneyScale j := by apply _root_.YangMills.Construction.ConfigurationSpace.ShellCount.scale_pos <;> assumption
theorem whitneyScale_anti {j j' : ℕ} (h : j ≤ j') : whitneyScale j' ≤ whitneyScale j := by
  rw [whitneyScale_eq_inv_pow, whitneyScale_eq_inv_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) h)
theorem whitneyScale_eq_two_mul_succ (j : ℕ) : whitneyScale j = 2 * whitneyScale (j + 1) := by
  rw [whitneyScale_eq_inv_pow, whitneyScale_eq_inv_pow, pow_succ, mul_inv]
  ring
theorem whitneyScale_zero_eq_one : whitneyScale 0 = 1 := by
  simp [whitneyScale]
theorem le_whitneyScale_iff (j : ℕ) (t : ℝ) : t ≤ whitneyScale j ↔ 2 ^ j * t ≤ 1 := by
  have h : (0 : ℝ) < 2 ^ j := by positivity
  rw [whitneyScale_eq_inv_pow, ← one_div, le_div_iff₀ h, mul_comm]
theorem maxNorm_le_iff {y : Fin 4 → ℝ} {s : ℝ} : maxNorm y ≤ s ↔ ∀ c, |y c| ≤ s :=
  ciSup_le_iff (Set.finite_range _).bddAbove
theorem exists_abs_eq_maxNorm (y : Fin 4 → ℝ) : ∃ c, |y c| = maxNorm y :=
  exists_eq_ciSup_of_finite
def rescaledStepDeriv (j r : ℕ) (t : ℝ) : ℝ :=
  (if r = 0 then 1 else 0) - ((2 : ℝ) ^ j) ^ r * iteratedDeriv r evenSmoothStep (2 ^ j * t)
theorem rescaledStepDeriv_zero (j : ℕ) (t : ℝ) :
    rescaledStepDeriv j 0 t = 1 - evenSmoothStep (2 ^ j * t) := by
  simp [rescaledStepDeriv]
theorem hasDerivAt_rescaledStepDeriv (hs : ContDiff ℝ ∞ evenSmoothStep) (j r : ℕ) (t : ℝ) :
    HasDerivAt (rescaledStepDeriv j r) (rescaledStepDeriv j (r + 1) t) t := by
  have hd : Differentiable ℝ (iteratedDeriv r evenSmoothStep) :=
    hs.differentiable_iteratedDeriv r (by exact_mod_cast WithTop.coe_lt_top _)
  have h1 : HasDerivAt (iteratedDeriv r evenSmoothStep)
      (iteratedDeriv (r + 1) evenSmoothStep (2 ^ j * t)) ((fun u : ℝ => 2 ^ j * u) t) := by
    rw [iteratedDeriv_succ]
    exact (hd _).hasDerivAt
  have h2 : HasDerivAt (fun u : ℝ => (2 : ℝ) ^ j * u) (2 ^ j) t := by
    simpa using (hasDerivAt_id t).const_mul ((2 : ℝ) ^ j)
  have h3 : HasDerivAt (fun u : ℝ => iteratedDeriv r evenSmoothStep (2 ^ j * u))
      (iteratedDeriv (r + 1) evenSmoothStep (2 ^ j * t) * 2 ^ j) t := HasDerivAt.comp t h1 h2
  have h4 := (h3.const_mul (((2 : ℝ) ^ j) ^ r)).const_sub (if r = 0 then (1 : ℝ) else 0)
  have e : rescaledStepDeriv j (r + 1) t =
      -(((2 : ℝ) ^ j) ^ r * (iteratedDeriv (r + 1) evenSmoothStep (2 ^ j * t) * 2 ^ j)) := by
    simp only [rescaledStepDeriv, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, pow_succ]
    ring
  rw [e]
  exact h4
theorem one_le_integralConstBound : 1 ≤ integralConstBound := le_max_left _ _
theorem blockConst_pos : 0 < blockConst := by
  norm_num [blockConst, gevreyConst]
theorem abs_rescaledStepDeriv_le (hb : SmoothBumpsGevreyBounds) (j r : ℕ) (t : ℝ) :
    |rescaledStepDeriv j r t| ≤
      integralConstBound * (blockConst * 2 ^ j) ^ r * (r.factorial : ℝ) ^ 2 := by
  have hrange := hb.2.2.1
  cases r with
  | zero =>
    rw [rescaledStepDeriv_zero]
    have h := hrange.2.2.1 (2 ^ j * t)
    have h1 := one_le_integralConstBound
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, one_pow]
    rw [abs_of_nonneg (by linarith [h.2])]
    linarith [h.1]
  | succ r =>
    have hB := (hb.2.2.2.2.2 (r + 1) (2 ^ j * t)).2.1
    have e : rescaledStepDeriv j (r + 1) t =
        -(((2 : ℝ) ^ j) ^ (r + 1) * iteratedDeriv (r + 1) evenSmoothStep (2 ^ j * t)) := by
      simp [rescaledStepDeriv]
    rw [e, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ j) ^ (r + 1))]
    calc ((2 : ℝ) ^ j) ^ (r + 1) * |iteratedDeriv (r + 1) evenSmoothStep (2 ^ j * t)|
        ≤ ((2 : ℝ) ^ j) ^ (r + 1) * (integralConstBound * blockConst ^ (r + 1) *
            ((r + 1).factorial : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by rw [mul_pow]; ring
theorem pairCutoff_eq_one_sub_prod (j : ℕ) (y : Fin 4 → ℝ) :
    pairCutoff j y = 1 - ∏ c, rescaledStepDeriv j 0 (y c) := by
  simp only [pairCutoff, rescaledStepDeriv_zero]
def coordProj (c : Fin 4) : (Fin 4 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj c
def pairDiffProj {n : ℕ} (a b : Fin n) (c : Fin 4) : Config n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj c).comp
    ((ContinuousLinearMap.proj a : Config n →L[ℝ] (Fin 4 → ℝ)) - ContinuousLinearMap.proj b)
theorem pairDiffProj_apply {n : ℕ} (a b : Fin n) (c : Fin 4) (x : Config n) :
    pairDiffProj a b c x = x a c - x b c := rfl
theorem ofRealFun_pairCutoff (j : ℕ) :
    ofRealFun (pairCutoff j) = affineProd (rescaledStepDeriv j) coordProj 1 (-1) 0 := by
  funext y
  simp only [ofRealFun, affineProd, linearFormProd, pairCutoff_eq_one_sub_prod, Pi.zero_apply]
  push_cast
  simp [coordProj]
  ring
theorem ofRealFun_pairCutoff_sub {n : ℕ} (j : ℕ) (a b : Fin n) :
    (fun x : Config n => ofRealFun (pairCutoff j) (x a - x b)) =
      affineProd (rescaledStepDeriv j) (pairDiffProj a b) 1 (-1) 0 := by
  funext x
  simp only [ofRealFun, affineProd, linearFormProd, pairCutoff_eq_one_sub_prod, Pi.zero_apply,
    pairDiffProj_apply, Pi.sub_apply]
  push_cast
  ring
theorem contDiff_pairCutoff (hs : ContDiff ℝ ∞ evenSmoothStep) (j : ℕ) :
    ContDiff ℝ ∞ (pairCutoff j) := by
  refine contDiff_const.sub (contDiff_prod fun c _ => contDiff_const.sub ?_)
  exact hs.comp (contDiff_const.mul (contDiff_apply ℝ ℝ c))
theorem contDiff_ofRealFun {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : V → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (ofRealFun f) :=
  Complex.ofRealCLM.contDiff.comp hf
theorem pairCutoffBounds_holds (hb : SmoothBumpsGevreyBounds)
    (he : ElementaryInequalities.NormPowerFactorialBounds) (j : ℕ) :
    PairCutoffBounds j := by
  obtain ⟨hsm, heven, hrange, hzero, hpos, hone, hmono⟩ := hb.2.2.1
  have hu0 : ∀ (j : ℕ) (c : Fin 4) (y : Fin 4 → ℝ),
      0 ≤ 1 - evenSmoothStep (2 ^ j * y c) := fun j c y => by
    linarith [(hrange (2 ^ j * y c)).2]
  have hu1 : ∀ (j : ℕ) (c : Fin 4) (y : Fin 4 → ℝ),
      1 - evenSmoothStep (2 ^ j * y c) ≤ 1 := fun j c y => by
    linarith [(hrange (2 ^ j * y c)).1]
  have habs : ∀ (j : ℕ) (t : ℝ), |(2 : ℝ) ^ j * t| = 2 ^ j * |t| := fun j t => by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ j)]
  refine ⟨contDiff_ofRealFun (contDiff_pairCutoff hsm j), ?_, ?_, ?_, ?_⟩
  · intro y
    refine ⟨?_, ?_, ?_⟩
    · simp only [pairCutoff]
      linarith [Finset.prod_le_one (s := Finset.univ) (fun c _ => hu0 j c y)
        (fun c _ => hu1 j c y)]
    · simp only [pairCutoff]
      have : ∏ c : Fin 4, (1 - evenSmoothStep (2 ^ (j + 1) * y c)) ≤
          ∏ c : Fin 4, (1 - evenSmoothStep (2 ^ j * y c)) := by
        refine Finset.prod_le_prod (fun c _ => hu0 (j + 1) c y) fun c _ => ?_
        have : evenSmoothStep (2 ^ j * y c) ≤ evenSmoothStep (2 ^ (j + 1) * y c) := by
          refine hmono _ _ ?_
          rw [habs, habs]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num) (Nat.le_succ j)) (abs_nonneg _)
        linarith
      linarith
    · simp only [pairCutoff]
      linarith [Finset.prod_nonneg (s := Finset.univ) fun c _ => hu0 (j + 1) c y]
  · intro y
    constructor
    · intro h
      rw [maxNorm_le_iff]
      intro c
      rw [le_whitneyScale_iff]
      by_contra hlt
      push Not at hlt
      have hp : 0 < evenSmoothStep (2 ^ j * y c) := hpos _ (by rw [habs]; exact hlt)
      have hprod : ∏ c' : Fin 4, (1 - evenSmoothStep (2 ^ j * y c')) ≤
          1 - evenSmoothStep (2 ^ j * y c) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
        exact mul_le_of_le_one_right (hu0 j c y)
          (Finset.prod_le_one (fun c' _ => hu0 j c' y) fun c' _ => hu1 j c' y)
      simp only [pairCutoff] at h
      linarith
    · intro h
      rw [maxNorm_le_iff] at h
      simp only [pairCutoff]
      have : ∀ c : Fin 4, evenSmoothStep (2 ^ j * y c) = 0 := fun c => by
        have h1 := (le_whitneyScale_iff j _).1 (h c)
        rw [← habs] at h1
        exact hzero _ (abs_le.1 h1)
      simp [this]
  · intro y h
    obtain ⟨c, hc⟩ := exists_abs_eq_maxNorm y
    rw [← hc] at h
    have h2 : (2 : ℝ) ≤ |2 ^ j * y c| := by
      rw [habs]
      have hd : 2 ^ j * whitneyScale j = 1 := by
        rw [whitneyScale_eq_inv_pow]
        exact mul_inv_cancel₀ (by positivity)
      have : 2 ^ j * (2 * whitneyScale j) ≤ 2 ^ j * |y c| :=
        mul_le_mul_of_nonneg_left h (by positivity)
      nlinarith
    have h1 : evenSmoothStep (2 ^ j * y c) = 1 := hone _ fun hm => by
      have := abs_lt.2 hm
      linarith
    simp only [pairCutoff]
    rw [Finset.prod_eq_zero (Finset.mem_univ c) (by rw [h1, sub_self]), sub_zero]
  · intro γ hγ y
    obtain ⟨L, hl, hL⟩ := exists_listDeriv_eq_iterDirDeriv
      (fun ι : Fin 4 => (Pi.single ι 1 : Fin 4 → ℝ)) γ
    have hne : L ≠ [] := by
      rintro rfl
      apply hγ
      funext c
      have h0 : MultiIdx.order γ = 0 := by simpa using hl.symm
      exact (Finset.sum_eq_zero_iff.1 h0) c (Finset.mem_univ c)
    have hK : (0 : ℝ) ≤ blockConst * 2 ^ j := by
      have := blockConst_pos
      positivity
    have h := (listDeriv_one_sub_affineProd (U := rescaledStepDeriv j) (ℓ := coordProj)
      (hasDerivAt_rescaledStepDeriv hsm j) (fun ι : Fin 4 => (Pi.single ι 1 : Fin 4 → ℝ))
      (fun _ => False)
      (fun ι => ⟨ι, 1, by simp, False.elim, fun c => by simp [coordProj, Pi.single_apply]⟩)
      (by linarith [one_le_integralConstBound]) hK (abs_rescaledStepDeriv_le hb j)
      (fun k => he.2.2 4 (by norm_num) k) L hne y).1
    rw [← ofRealFun_pairCutoff, hl] at h
    unfold multiDeriv
    rw [hL]
    exact h
def pairWeight {n : ℕ} (W : ℝ) (q : Fin n × Fin n) (ι : CoordIndex n) : ℝ :=
  if (ofLex ι).1 = q.1 ∨ (ofLex ι).1 = q.2 then W else 0
theorem pairWeight_nonneg {n : ℕ} {W : ℝ} (hW : 0 ≤ W) (q : Fin n × Fin n)
    (ι : CoordIndex n) : 0 ≤ pairWeight W q ι := by
  unfold pairWeight
  split_ifs
  · exact hW
  · exact le_rfl
theorem sum_pairWeight_le {n : ℕ} {W : ℝ} (hW : 0 ≤ W) (ι : CoordIndex n) :
    ∑ q ∈ orderedPairs n, pairWeight W q ι ≤ n * W := by
  classical
  set i := (ofLex ι).1 with hi
  have hcard : ((orderedPairs n).filter fun q => i = q.1 ∨ i = q.2).card ≤ n := by
    have := Finset.card_le_card_of_injOn
      (s := (orderedPairs n).filter fun q => i = q.1 ∨ i = q.2)
      (t := (Finset.univ : Finset (Fin n))) (fun q => if q.1 = i then q.2 else q.1)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
    · simpa using this
    · rintro ⟨a, b⟩ h ⟨a', b'⟩ h' e
      simp only [Finset.coe_filter, orderedPairs, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at h h'
      obtain ⟨hab, h⟩ := h
      obtain ⟨hab', h'⟩ := h'
      simp only at e
      rcases h with rfl | rfl <;> rcases h' with h' | h'
      · subst h'
        simp at e
        rw [e]
      · subst h'
        simp [hab'.ne] at e
        omega
      · subst h'
        simp [hab.ne] at e
        omega
      · subst h'
        simp [hab.ne, hab'.ne] at e
        rw [e]
  unfold pairWeight
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hW
theorem coordBasis_apply {n : ℕ} (ι : CoordIndex n) (a : Fin n) (c : Fin 4) :
    coordBasis ι a c =
      (if a = (ofLex ι).1 then 1 else 0) * (if c = (ofLex ι).2 then 1 else 0) := by
  unfold coordBasis
  by_cases ha : a = (ofLex ι).1
  · subst ha
    simp [Pi.single_apply]
  · rw [Pi.single_eq_of_ne ha]
    simp [if_neg ha]
theorem listGevreyBound_pairCutoff (hb : SmoothBumpsGevreyBounds)
    (he : ElementaryInequalities.NormPowerFactorialBounds) {n : ℕ} (j : ℕ)
    (a b : Fin n) (hab : a ≠ b) :
    ListGevreyBound (coordBasis (n := n))
      (fun x : Config n => ofRealFun (pairCutoff j) (x a - x b))
      (pairWeight (integralConstBound ^ 4 * (blockConst * 2 ^ j)) (a, b)) := by
  have hA := one_le_integralConstBound
  have hA0 : 0 ≤ integralConstBound := by linarith
  have hK : (0 : ℝ) ≤ blockConst * 2 ^ j := by
    have := blockConst_pos
    positivity
  have hW : 0 ≤ integralConstBound ^ 4 * (blockConst * 2 ^ j) := by positivity
  intro L x
  by_cases hL : L = []
  · subst hL
    have h := (pairCutoffBounds_holds hb he j).2.1 (x a - x b)
    have h1 : pairCutoff j (x a - x b) ≤ 1 := h.2.1.trans h.2.2
    simp only [listDeriv, List.foldl_nil, List.map_nil, List.prod_nil, List.length_nil,
      Nat.factorial_zero, Nat.cast_one, one_pow, mul_one, ofRealFun, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_nonneg h.1]
    exact h1
  have hdir : ∀ ι : CoordIndex n, ∃ (c₀ : Fin 4) (s : ℝ), |s| ≤ 1 ∧
      ((ofLex ι).1 ≠ a ∧ (ofLex ι).1 ≠ b → s = 0) ∧
      ∀ c, pairDiffProj a b c (coordBasis ι) = if c = c₀ then s else 0 := by
    intro ι
    refine ⟨(ofLex ι).2, (if a = (ofLex ι).1 then 1 else 0) - (if b = (ofLex ι).1 then 1 else 0),
      ?_, ?_, ?_⟩
    · by_cases h1 : a = (ofLex ι).1
      · have h2 : b ≠ (ofLex ι).1 := fun h => hab (h1.trans h.symm)
        simp [if_pos h1, if_neg h2]
      · by_cases h2 : b = (ofLex ι).1
        · simp [if_neg h1, if_pos h2]
        · simp [if_neg h1, if_neg h2]
    · rintro ⟨h1, h2⟩
      simp [if_neg h1.symm, if_neg h2.symm]
    · intro c
      rw [pairDiffProj_apply, coordBasis_apply, coordBasis_apply]
      by_cases hc : c = (ofLex ι).2
      · simp [if_pos hc]
      · simp [if_neg hc]
  have hmain := listDeriv_one_sub_affineProd (U := rescaledStepDeriv j) (ℓ := pairDiffProj a b)
    (hasDerivAt_rescaledStepDeriv hb.2.2.1.1 j) (coordBasis (n := n))
    (fun ι => (ofLex ι).1 ≠ a ∧ (ofLex ι).1 ≠ b) hdir hA0 hK (abs_rescaledStepDeriv_le hb j)
    (fun k => he.2.2 4 (by norm_num) k) L hL x
  rw [← ofRealFun_pairCutoff_sub] at hmain
  by_cases hd : ∃ ι ∈ L, (ofLex ι).1 ≠ a ∧ (ofLex ι).1 ≠ b
  · rw [hmain.2 hd, norm_zero]
    exact mul_nonneg (prod_map_weights_nonneg (pairWeight_nonneg hW _) L) (by positivity)
  · push Not at hd
    have hw : ∀ ι ∈ L, pairWeight (integralConstBound ^ 4 * (blockConst * 2 ^ j)) (a, b) ι =
        integralConstBound ^ 4 * (blockConst * 2 ^ j) := by
      intro ι hι
      unfold pairWeight
      rw [if_pos]
      by_cases h1 : (ofLex ι).1 = a
      · exact Or.inl h1
      · exact Or.inr (hd ι hι h1)
    rw [prod_map_weights_eq_pow L hw]
    have hfac : (0 : ℝ) ≤ (L.length.factorial : ℝ) ^ 2 := by positivity
    have hKl : (0 : ℝ) ≤ (blockConst * 2 ^ j) ^ L.length := pow_nonneg hK _
    refine hmain.1.trans (mul_le_mul_of_nonneg_right ?_ hfac)
    rw [mul_pow (integralConstBound ^ 4)]
    refine mul_le_mul_of_nonneg_right ?_ hKl
    have hlen : L.length ≠ 0 := by simpa using hL
    calc integralConstBound ^ 4 ≤ (integralConstBound ^ 4) ^ L.length :=
          le_self_pow₀ (one_le_pow₀ hA) hlen
      _ = _ := rfl
theorem ofRealFun_pairCutoffProd {n : ℕ} (j : ℕ) :
    ofRealFun (pairCutoffProd (n := n) j) =
      fun x => ∏ q ∈ orderedPairs n, ofRealFun (pairCutoff j) (x q.1 - x q.2) := by
  funext x
  simp [ofRealFun, pairCutoffProd]
theorem contDiff_pairCutoffProd (hs : ContDiff ℝ ∞ evenSmoothStep) {n : ℕ} (j : ℕ) :
    ContDiff ℝ ∞ (pairCutoffProd (n := n) j) := by
  refine contDiff_prod fun q _ => (contDiff_pairCutoff hs j).comp ?_
  exact (contDiff_apply ℝ (Fin 4 → ℝ) q.1).sub (contDiff_apply ℝ (Fin 4 → ℝ) q.2)
theorem norm_listDeriv_pairCutoffProd_le (hb : SmoothBumpsGevreyBounds)
    (he : ElementaryInequalities.NormPowerFactorialBounds) {n : ℕ} (j : ℕ)
    (L : List (CoordIndex n)) (x : Config n) :
    ‖listDeriv coordBasis L (ofRealFun (pairCutoffProd j)) x‖ ≤
      (pairCutoffConst * n * 2 ^ j) ^ L.length * (L.length.factorial : ℝ) ^ 2 := by
  have hA := one_le_integralConstBound
  have hC := blockConst_pos
  have hW : 0 ≤ integralConstBound ^ 4 * (blockConst * 2 ^ j) := by positivity
  have hsm : ContDiff ℝ ∞ (pairCutoff j) := contDiff_pairCutoff hb.2.2.1.1 j
  have hprod := ListGevreyBound.prod (e := coordBasis (n := n)) (orderedPairs n)
    (f := fun (q : Fin n × Fin n) (x : Config n) => ofRealFun (pairCutoff j) (x q.1 - x q.2))
    (w := pairWeight (integralConstBound ^ 4 * (blockConst * 2 ^ j)))
    (fun q => (contDiff_ofRealFun hsm).comp
      ((contDiff_apply ℝ (Fin 4 → ℝ) q.1).sub (contDiff_apply ℝ (Fin 4 → ℝ) q.2)))
    (fun q ι => pairWeight_nonneg hW q ι)
    (fun q hq => listGevreyBound_pairCutoff hb he j q.1 q.2 (by
      have : q.1 < q.2 := by simpa [orderedPairs] using hq
      exact this.ne))
  have hmono := hprod.mono (w' := fun _ => pairCutoffConst * n * 2 ^ j)
    (fun ι => Finset.sum_nonneg fun q _ => pairWeight_nonneg hW q ι)
    (fun ι => by
      refine (sum_pairWeight_le hW ι).trans (le_of_eq ?_)
      unfold pairCutoffConst
      ring)
  rw [ofRealFun_pairCutoffProd]
  have h := hmono L x
  rwa [prod_map_weights_eq_pow L fun _ _ => rfl] at h
theorem pairCutoffProdBounds_holds (hb : SmoothBumpsGevreyBounds)
    (he : ElementaryInequalities.NormPowerFactorialBounds) (n j : ℕ) :
    PairCutoffProdBounds n j := by
  have hF := fun j => pairCutoffBounds_holds hb he j
  have hs := hb.2.2.1.1
  refine ⟨contDiff_ofRealFun (contDiff_pairCutoffProd hs j), ?_, ?_, ?_, ?_⟩
  · intro x
    have hq : ∀ (j : ℕ) (q : Fin n × Fin n), 0 ≤ pairCutoff j (x q.1 - x q.2) ∧
        pairCutoff j (x q.1 - x q.2) ≤ pairCutoff (j + 1) (x q.1 - x q.2) ∧
        pairCutoff (j + 1) (x q.1 - x q.2) ≤ 1 := fun j q => (hF j).2.1 _
    unfold pairCutoffProd
    exact ⟨Finset.prod_nonneg fun q _ => (hq j q).1,
      Finset.prod_le_prod (fun q _ => (hq j q).1) (fun q _ => (hq j q).2.1),
      Finset.prod_le_one (fun q _ => (hq (j + 1) q).1) (fun q _ => (hq j q).2.2)⟩
  · intro x hx
    by_contra hne
    have hall : ∀ q ∈ orderedPairs n, whitneyScale j < maxNorm (x q.1 - x q.2) := by
      intro q hq
      by_contra hle
      push Not at hle
      exact hne (Finset.prod_eq_zero hq (((hF j).2.2.1 _).2 hle))
    have hlt : ENNReal.ofReal (whitneyScale j) < minSeparation x := by
      unfold minSeparation
      rw [← Finset.inf_eq_iInf, Finset.lt_inf_iff ENNReal.ofReal_lt_top]
      intro q hq
      exact (ENNReal.ofReal_lt_ofReal_iff ((whitneyScale_pos j).trans (hall q hq))).2 (hall q hq)
    exact absurd hx (not_le.2 hlt)
  · intro x hx
    refine Finset.prod_eq_one fun q hq => ?_
    apply (hF j).2.2.2.1
    have h1 := le_iInf₂_iff.1 hx q hq
    rcases ENNReal.ofReal_le_ofReal_iff'.1 h1 with h | h
    · exact h
    · linarith [whitneyScale_pos j]
  · intro α x
    obtain ⟨L, hl, hL⟩ := exists_listDeriv_eq_iterDirDeriv (coordBasis (n := n)) α
    unfold configMultiDeriv
    rw [hL, ← hl]
    exact norm_listDeriv_pairCutoffProd_le hb he j L x
end Concrete
section Shells
theorem shellDiff_zero_eq {n : ℕ} (x : Config n) : shellDiff 0 x = pairCutoffProd 0 x := rfl
theorem shellDiff_succ_eq {n : ℕ} (j : ℕ) (x : Config n) :
    shellDiff (j + 1) x = pairCutoffProd (j + 1) x - pairCutoffProd j x := rfl
theorem continuous_minSeparation (hm : MinSeparationProperties) {n : ℕ}
    (hn : 1 ≤ n) : Continuous (minSeparation (n := n)) := by
  rcases hn.eq_or_lt with rfl | h2
  · have : minSeparation (n := 1) = fun _ => ⊤ := funext minSeparation_one
    rw [this]
    exact continuous_const
  · obtain ⟨hfin, -, hcont⟩ := (hm.1 n h2).1
    have : minSeparation (n := n) = fun x => ENNReal.ofReal (minSeparation x).toReal :=
      funext fun x => (ENNReal.ofReal_toReal (hfin x)).symm
    rw [this]
    exact ENNReal.continuous_ofReal.comp hcont
theorem minSeparation_ne_zero (hm : MinSeparationProperties) {n : ℕ} (hn : 1 ≤ n)
    {x : Config n} (hx : x ∈ injectiveTuples (Fin 4 → ℝ) n) :
    minSeparation x ≠ 0 := by
  have key : FatDiagonalEqZeros n ∧ FatDiagonalComplEqInjective n := by
    rcases hn.eq_or_lt with rfl | h2
    · exact hm.2
    · exact (hm.1 n h2).2
  intro h0
  have h1 : x ∈ fatDiagonal n := by
    rw [key.1.1]
    exact h0
  have h2 : x ∈ (fatDiagonal n)ᶜ := by
    rw [key.2.1]
    exact hx
  exact h2 h1
theorem exists_two_whitneyScale_le {m : ENNReal} (hm : m ≠ 0) :
    ∃ J : ℕ, ENNReal.ofReal (2 * whitneyScale J) ≤ m := by
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_two_pow_lt hm
  refine ⟨k + 1, le_of_eq_of_le ?_ hk.le⟩
  rw [← whitneyScale_eq_two_mul_succ, whitneyScale_eq_inv_pow, ← inv_pow,
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp
theorem shellDiffBounds_holds (hb : SmoothBumpsGevreyBounds)
    (he : ElementaryInequalities.NormPowerFactorialBounds)
    (hm : MinSeparationProperties) (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    ShellDiffBounds n j := by
  have hH := fun j => pairCutoffProdBounds_holds hb he n j
  have hnn : ∀ (j : ℕ) (x : Config n), 0 ≤ pairCutoffProd j x := fun j x => ((hH j).2.1 x).1
  have hup : ∀ (j : ℕ) (x : Config n), pairCutoffProd j x ≤ pairCutoffProd (j + 1) x :=
    fun j x => ((hH j).2.1 x).2.1
  have hle1 : ∀ (j : ℕ) (x : Config n), pairCutoffProd j x ≤ 1 :=
    fun j x => (hup j x).trans ((hH j).2.1 x).2.2
  have hvan : ∀ (j : ℕ) (x : Config n), minSeparation x ≤ ENNReal.ofReal (whitneyScale j) →
      pairCutoffProd j x = 0 := fun j => (hH j).2.2.1
  have hfull : ∀ (j : ℕ) (x : Config n), ENNReal.ofReal (2 * whitneyScale j) ≤ minSeparation x →
      pairCutoffProd j x = 1 := fun j => (hH j).2.2.2.1
  have hshell0 : ∀ (j : ℕ) (x : Config n), 0 ≤ shellDiff j x := by
    intro j x
    cases j with
    | zero => exact hnn 0 x
    | succ j => exact sub_nonneg.2 (hup j x)
  have hsum : ∀ (J : ℕ) (x : Config n),
      ∑ j' ∈ Finset.range (J + 1), shellDiff j' x = pairCutoffProd J x := by
    intro J x
    induction J with
    | zero => simp [shellDiff_zero_eq]
    | succ J ih => rw [Finset.sum_range_succ, ih, shellDiff_succ_eq]; ring
  have hlow : ∀ (j : ℕ) (x : Config n), shellDiff j x ≠ 0 →
      ENNReal.ofReal (whitneyScale j) < minSeparation x := by
    intro j x hne
    by_contra hle
    rw [not_lt] at hle
    have h0 := hvan j x hle
    apply hne
    cases j with
    | zero => exact h0
    | succ j =>
      rw [shellDiff_succ_eq, h0]
      have := hup j x
      have := hnn j x
      have h1 : pairCutoffProd j x = 0 := by linarith
      rw [h1, sub_zero]
  have hhigh : ∀ (j : ℕ) (x : Config n), shellDiff j x ≠ 0 → 1 ≤ j →
      minSeparation x < ENNReal.ofReal (4 * whitneyScale j) := by
    intro j x hne hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    by_contra hle
    rw [not_lt] at hle
    have h4 : 4 * whitneyScale (k + 1) = 2 * whitneyScale k := by
      rw [whitneyScale_eq_two_mul_succ k]
      ring
    rw [h4] at hle
    have h1 := hfull k x hle
    apply hne
    rw [shellDiff_succ_eq, h1]
    have := hup k x
    have := hle1 (k + 1) x
    linarith
  have hcont := continuous_minSeparation hm hn
  have hsupp : ∀ j : ℕ, 1 ≤ j → tsupport (shellDiff (n := n) j) ⊆
      {x | ENNReal.ofReal (whitneyScale j) ≤ minSeparation x ∧
        minSeparation x ≤ ENNReal.ofReal (4 * whitneyScale j)} := by
    intro j hj
    refine closure_minimal (fun x hx => ⟨(hlow j x hx).le, (hhigh j x hx hj).le⟩) ?_
    exact (isClosed_le continuous_const hcont).inter (isClosed_le hcont continuous_const)
  have hsupp0 : tsupport (shellDiff (n := n) 0) ⊆
      {x | ENNReal.ofReal 1 ≤ minSeparation x} := by
    refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_const hcont)
    have := (hlow 0 x hx).le
    rwa [whitneyScale_zero_eq_one] at this
  refine ⟨fun x => hshell0 j x, hsum, ?_, fun x => hlow j x, fun x => hhigh j x, hsupp j, hsupp0,
    ?_, ?_⟩
  · intro x hx
    obtain ⟨J₀, hJ₀⟩ := exists_two_whitneyScale_le (minSeparation_ne_zero hm hn hx)
    have hone : ∀ J, J₀ ≤ J → pairCutoffProd J x = 1 := fun J hJ =>
      hfull J x (le_trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (whitneyScale_anti hJ) (by norm_num))) hJ₀)
    have hzero : ∀ j', J₀ < j' → shellDiff j' x = 0 := by
      intro j' hj
      obtain ⟨k, rfl⟩ : ∃ k, j' = k + 1 := ⟨j' - 1, by omega⟩
      rw [shellDiff_succ_eq, hone (k + 1) (by omega), hone k (by omega), sub_self]
    constructor
    · refine (Set.finite_Iic J₀).subset fun j' hj' => ?_
      by_contra hlt
      exact hj' (hzero j' (not_le.1 hlt))
    · rw [tsum_eq_sum (s := Finset.range (J₀ + 1)) (fun b hb' => hzero b (by
        simp only [Finset.mem_range, not_lt] at hb'
        omega)), hsum, hone J₀ le_rfl]
  · intro x
    classical
    have hbelow : ∀ j' : ℕ, x ∈ tsupport (shellDiff (n := n) j') →
        ENNReal.ofReal (whitneyScale j') ≤ minSeparation x := by
      intro j' hj'
      cases j' with
      | zero =>
        rw [whitneyScale_zero_eq_one]
        exact hsupp0 hj'
      | succ k => exact (hsupp (k + 1) (by omega) hj').1
    have hgap : ∀ j₁ j₂ : ℕ, j₁ < j₂ → x ∈ tsupport (shellDiff (n := n) j₁) →
        x ∈ tsupport (shellDiff (n := n) j₂) → j₂ ≤ j₁ + 2 := by
      intro j₁ j₂ h12 h1 h2
      by_contra hbig
      have hle := (hbelow j₁ h1).trans (hsupp j₂ (by omega) h2).2
      have hreal : whitneyScale j₁ ≤ 4 * whitneyScale j₂ := by
        rcases ENNReal.ofReal_le_ofReal_iff'.1 hle with h | h
        · exact h
        · linarith [whitneyScale_pos j₁]
      have h3 : whitneyScale j₂ ≤ whitneyScale (j₁ + 3) := whitneyScale_anti (by omega)
      have e1 := whitneyScale_eq_two_mul_succ j₁
      have e2 := whitneyScale_eq_two_mul_succ (j₁ + 1)
      have e3 := whitneyScale_eq_two_mul_succ (j₁ + 2)
      have hp := whitneyScale_pos (j₁ + 3)
      linarith
    by_cases hem : {j' : ℕ | x ∈ tsupport (shellDiff (n := n) j')}.Nonempty
    · set S := {j' : ℕ | x ∈ tsupport (shellDiff (n := n) j')} with hS
      have hmin : sInf S ∈ S := Nat.sInf_mem hem
      have hsub : S ⊆ ((Finset.Icc (sInf S) (sInf S + 2) : Finset ℕ) : Set ℕ) := by
        intro j' hj'
        have h1 : sInf S ≤ j' := Nat.sInf_le hj'
        rw [Finset.mem_coe, Finset.mem_Icc]
        refine ⟨h1, ?_⟩
        rcases h1.eq_or_lt with h | h
        · omega
        · exact hgap _ _ h hmin hj'
      calc S.encard ≤ ((Finset.Icc (sInf S) (sInf S + 2) : Finset ℕ) : Set ℕ).encard :=
            Set.encard_le_encard hsub
        _ = ((Finset.Icc (sInf S) (sInf S + 2)).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
        _ ≤ 3 := by
            rw [Nat.card_Icc]
            have : sInf S + 2 + 1 - sInf S = 3 := by omega
            rw [this]
            rfl
    · rw [Set.not_nonempty_iff_eq_empty] at hem
      rw [hem]
      simp
  · intro α x
    obtain ⟨L, hl, hL⟩ := exists_listDeriv_eq_iterDirDeriv (coordBasis (n := n)) α
    have hC := blockConst_pos
    have hA := one_le_integralConstBound
    have hnum : 0 ≤ pairCutoffConst := by
      unfold pairCutoffConst
      positivity
    unfold configMultiDeriv
    rw [hL, ← hl]
    have hfac : (0 : ℝ) ≤ (L.length.factorial : ℝ) ^ 2 := by positivity
    cases j with
    | zero =>
      have h := norm_listDeriv_pairCutoffProd_le hb he (n := n) 0 L x
      have hpos : 0 ≤ (pairCutoffConst * n * 2 ^ 0) ^ L.length * (L.length.factorial : ℝ) ^ 2 := by
        positivity
      have e : ofRealFun (shellDiff (n := n) 0) = ofRealFun (pairCutoffProd 0) := rfl
      rw [e]
      linarith
    | succ k =>
      have h1 := norm_listDeriv_pairCutoffProd_le hb he (n := n) (k + 1) L x
      have h2 := norm_listDeriv_pairCutoffProd_le hb he (n := n) k L x
      have hs := hb.2.2.1.1
      have c1 := contDiff_ofRealFun (contDiff_pairCutoffProd (n := n) hs (k + 1))
      have c2 := contDiff_ofRealFun (contDiff_pairCutoffProd (n := n) hs k)
      have e : ofRealFun (shellDiff (n := n) (k + 1)) =
          fun y => ofRealFun (pairCutoffProd (k + 1)) y +
            (-1) * ofRealFun (pairCutoffProd k) y := by
        funext y
        simp only [ofRealFun, shellDiff_succ_eq]
        push_cast
        ring
      have hmono : (pairCutoffConst * n * 2 ^ k) ^ L.length ≤
          (pairCutoffConst * n * 2 ^ (k + 1)) ^ L.length := by
        refine pow_le_pow_left₀ (by positivity) ?_ _
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)
      rw [e, listDeriv_add_const_mul _ _ (-1) c1 c2]
      calc ‖listDeriv coordBasis L (ofRealFun (pairCutoffProd (k + 1))) x +
            (-1) * listDeriv coordBasis L (ofRealFun (pairCutoffProd k)) x‖
          ≤ ‖listDeriv coordBasis L (ofRealFun (pairCutoffProd (k + 1))) x‖ +
            ‖listDeriv coordBasis L (ofRealFun (pairCutoffProd k)) x‖ := by
            refine (norm_add_le _ _).trans (le_of_eq ?_)
            simp
        _ ≤ (pairCutoffConst * n * 2 ^ (k + 1)) ^ L.length * (L.length.factorial : ℝ) ^ 2 +
            (pairCutoffConst * n * 2 ^ k) ^ L.length * (L.length.factorial : ℝ) ^ 2 :=
            add_le_add h1 h2
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hmono hfac]
end Shells
theorem diagonalCutoffProperties_holds (hb : SmoothBumpsGevreyBounds)
    (he : ElementaryInequalities.NormPowerFactorialBounds)
    (hm : MinSeparationProperties) : DiagonalCutoffProperties :=
  fun n hn j => ⟨pairCutoffBounds_holds hb he j, pairCutoffProdBounds_holds hb he n j,
    shellDiffBounds_holds hb he hm n hn j⟩
end YangMills.Construction.ConfigurationSpace.DiagonalCutoff
end

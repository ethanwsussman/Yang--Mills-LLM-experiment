import YangMills.Construction.RunningCouplingSlope.CoordinateFamiliesAreClosedProof
import YangMills.Construction.RunningCouplingSlope.KernelsNearTheCellsAreBoundedProof
import YangMills.Construction.RunningCouplingSlope.LocalFamiliesAreClosed
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.ClosureProof
open Tower
private def ContDiff2 (F : ℝ → ℝ → ℂ) : Prop := ContDiffAt ℝ 2 (fun w : ℝ × ℝ => F w.1 w.2) 0
private def dFst (F : ℝ → ℝ → ℂ) : ℂ := deriv (fun s => F s 0) 0
private def dSnd (F : ℝ → ℝ → ℂ) : ℂ := deriv (fun t => F 0 t) 0
private def dMix (F : ℝ → ℝ → ℂ) : ℂ := deriv (fun s => deriv (fun t => F s t) 0) 0
private lemma ContDiff2.differentiableAt {F : ℝ → ℝ → ℂ} (h : ContDiff2 F) :
    DifferentiableAt ℝ (fun w : ℝ × ℝ => F w.1 w.2) ((0 : ℝ), (0 : ℝ)) :=
  ContDiffAt.differentiableAt h (by norm_num)
private lemma ContDiff2.lineFirst {F : ℝ → ℝ → ℂ} (h : ContDiff2 F) :
    DifferentiableAt ℝ (fun s => F s 0) 0 := by
  have h2 : DifferentiableAt ℝ (fun s : ℝ => ((s, 0) : ℝ × ℝ)) 0 := by fun_prop
  exact DifferentiableAt.comp (f := fun s : ℝ => ((s, 0) : ℝ × ℝ))
    (g := fun w : ℝ × ℝ => F w.1 w.2) (0 : ℝ) h.differentiableAt h2
private lemma ContDiff2.lineSecond {F : ℝ → ℝ → ℂ} (h : ContDiff2 F) :
    DifferentiableAt ℝ (fun t => F 0 t) 0 := by
  have h2 : DifferentiableAt ℝ (fun t : ℝ => ((0, t) : ℝ × ℝ)) 0 := by fun_prop
  exact DifferentiableAt.comp (f := fun t : ℝ => ((0, t) : ℝ × ℝ))
    (g := fun w : ℝ × ℝ => F w.1 w.2) (0 : ℝ) h.differentiableAt h2
private lemma ContDiff2.eventually_differentiableAt {F : ℝ → ℝ → ℂ} (h : ContDiff2 F) :
    ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun w : ℝ × ℝ => F w.1 w.2) (s, 0) := by
  have h1 : ∀ᶠ w in 𝓝 (0 : ℝ × ℝ), ContDiffAt ℝ 2 (fun w : ℝ × ℝ => F w.1 w.2) w :=
    ContDiffAt.eventually h (by simp)
  have h2 : Filter.Tendsto (fun s : ℝ => ((s, 0) : ℝ × ℝ)) (𝓝 0) (𝓝 (0 : ℝ × ℝ)) := by
    have : Continuous (fun s : ℝ => ((s, 0) : ℝ × ℝ)) := by fun_prop
    exact this.tendsto 0
  filter_upwards [h2.eventually h1] with s hs
  exact hs.differentiableAt (by norm_num)
private lemma ContDiff2.eventually_lineSecond {F : ℝ → ℝ → ℂ} (h : ContDiff2 F) :
    ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun t => F s t) 0 := by
  filter_upwards [h.eventually_differentiableAt] with s hs
  have h2 : DifferentiableAt ℝ (fun t : ℝ => ((s, t) : ℝ × ℝ)) 0 := by fun_prop
  exact DifferentiableAt.comp (f := fun t : ℝ => ((s, t) : ℝ × ℝ))
    (g := fun w : ℝ × ℝ => F w.1 w.2) (0 : ℝ) hs h2
private lemma ContDiff2.differentiableAt_derivSecond {F : ℝ → ℝ → ℂ} (h : ContDiff2 F) :
    DifferentiableAt ℝ (fun s => deriv (fun t => F s t) 0) 0 := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ (fun w : ℝ × ℝ => F w.1 w.2)) 0 :=
    ContDiffAt.fderiv_right h (by norm_num)
  have h3 : DifferentiableAt ℝ (fderiv ℝ (fun w : ℝ × ℝ => F w.1 w.2)) ((0 : ℝ), (0 : ℝ)) :=
    h1.differentiableAt (by norm_num)
  have h2 : DifferentiableAt ℝ (fun s : ℝ => ((s, 0) : ℝ × ℝ)) 0 := by fun_prop
  have h4 : DifferentiableAt ℝ
      (fun s : ℝ => fderiv ℝ (fun w : ℝ × ℝ => F w.1 w.2) (s, 0)) 0 :=
    DifferentiableAt.comp (f := fun s : ℝ => ((s, 0) : ℝ × ℝ)) (0 : ℝ) h3 h2
  have h5 : DifferentiableAt ℝ
      (fun s : ℝ => fderiv ℝ (fun w : ℝ × ℝ => F w.1 w.2) (s, 0) ((0 : ℝ), (1 : ℝ))) 0 :=
    h4.clm_apply (differentiableAt_const _)
  refine h5.congr_of_eventuallyEq ?_
  filter_upwards [h.eventually_differentiableAt] with s hs
  have hp : HasDerivAt (fun t : ℝ => ((s, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) 0 :=
    (hasDerivAt_const (0 : ℝ) s).prodMk (hasDerivAt_id (0 : ℝ))
  have := (hs.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hp)
  exact this.deriv
private lemma ContDiff2.const (x : ℂ) : ContDiff2 (fun _ _ => x) := contDiffAt_const
private lemma ContDiff2.add {F G : ℝ → ℝ → ℂ} (hF : ContDiff2 F) (hG : ContDiff2 G) :
    ContDiff2 (fun s t => F s t + G s t) := ContDiffAt.add hF hG
private lemma ContDiff2.mul {F G : ℝ → ℝ → ℂ} (hF : ContDiff2 F) (hG : ContDiff2 G) :
    ContDiff2 (fun s t => F s t * G s t) := ContDiffAt.mul hF hG
private lemma ContDiff2.sum {ι : Type} (u : Finset ι) {F : ι → ℝ → ℝ → ℂ}
    (hF : ∀ i ∈ u, ContDiff2 (F i)) :
    ContDiff2 (fun s t => ∑ i ∈ u, F i s t) := ContDiffAt.sum fun i hi => hF i hi
private lemma dFst_mul {F G : ℝ → ℝ → ℂ} (hF : ContDiff2 F) (hG : ContDiff2 G) :
    dFst (fun s t => F s t * G s t) = dFst F * G 0 0 + F 0 0 * dFst G :=
  deriv_fun_mul hF.lineFirst hG.lineFirst
private lemma dSnd_mul {F G : ℝ → ℝ → ℂ} (hF : ContDiff2 F) (hG : ContDiff2 G) :
    dSnd (fun s t => F s t * G s t) = dSnd F * G 0 0 + F 0 0 * dSnd G :=
  deriv_fun_mul hF.lineSecond hG.lineSecond
private lemma dMix_mul {F G : ℝ → ℝ → ℂ} (hF : ContDiff2 F) (hG : ContDiff2 G) :
    dMix (fun s t => F s t * G s t) =
      dMix F * G 0 0 + dSnd F * dFst G + dFst F * dSnd G + F 0 0 * dMix G := by
  have h : (fun s => deriv (fun t => F s t * G s t) 0) =ᶠ[𝓝 0]
      fun s => deriv (fun t => F s t) 0 * G s 0 + F s 0 * deriv (fun t => G s t) 0 := by
    filter_upwards [hF.eventually_lineSecond, hG.eventually_lineSecond] with s a b
    exact deriv_fun_mul a b
  unfold dMix dFst dSnd
  rw [h.deriv_eq, (HasDerivAt.fun_add
    (HasDerivAt.fun_mul hF.differentiableAt_derivSecond.hasDerivAt hG.lineFirst.hasDerivAt)
    (HasDerivAt.fun_mul hF.lineFirst.hasDerivAt hG.differentiableAt_derivSecond.hasDerivAt)).deriv]
  ring
private lemma dFst_sum {ι : Type} (u : Finset ι) {F : ι → ℝ → ℝ → ℂ}
    (hF : ∀ i ∈ u, ContDiff2 (F i)) :
    dFst (fun s t => ∑ i ∈ u, F i s t) = ∑ i ∈ u, dFst (F i) :=
  deriv_fun_sum fun i hi => (hF i hi).lineFirst
private lemma dSnd_sum {ι : Type} (u : Finset ι) {F : ι → ℝ → ℝ → ℂ}
    (hF : ∀ i ∈ u, ContDiff2 (F i)) :
    dSnd (fun s t => ∑ i ∈ u, F i s t) = ∑ i ∈ u, dSnd (F i) :=
  deriv_fun_sum fun i hi => (hF i hi).lineSecond
private lemma dMix_sum {ι : Type} (u : Finset ι) {F : ι → ℝ → ℝ → ℂ}
    (hF : ∀ i ∈ u, ContDiff2 (F i)) :
    dMix (fun s t => ∑ i ∈ u, F i s t) = ∑ i ∈ u, dMix (F i) := by
  have h : (fun s => deriv (fun t => ∑ i ∈ u, F i s t) 0) =ᶠ[𝓝 0]
      fun s => ∑ i ∈ u, deriv (fun t => F i s t) 0 := by
    have : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i ∈ u, DifferentiableAt ℝ (fun t => F i s t) 0 :=
      (Finset.eventually_all u).2 fun i hi => (hF i hi).eventually_lineSecond
    filter_upwards [this] with s hs
    exact deriv_fun_sum hs
  unfold dMix
  rw [h.deriv_eq]
  exact deriv_fun_sum fun i hi => (hF i hi).differentiableAt_derivSecond
private lemma dFst_const_mul (x : ℂ) {F : ℝ → ℝ → ℂ} (hF : ContDiff2 F) :
    dFst (fun s t => x * F s t) = x * dFst F := by
  have := dFst_mul (ContDiff2.const x) hF
  simpa [dFst] using this
private lemma dSnd_const_mul (x : ℂ) {F : ℝ → ℝ → ℂ} (hF : ContDiff2 F) :
    dSnd (fun s t => x * F s t) = x * dSnd F := by
  have := dSnd_mul (ContDiff2.const x) hF
  simpa [dSnd] using this
private lemma dMix_const_mul (x : ℂ) {F : ℝ → ℝ → ℂ} (hF : ContDiff2 F) :
    dMix (fun s t => x * F s t) = x * dMix F := by
  have := dMix_mul (ContDiff2.const x) hF
  simpa [dFst, dSnd, dMix] using this
private lemma dFst_add {F G : ℝ → ℝ → ℂ} (hF : ContDiff2 F) (hG : ContDiff2 G) :
    dFst (fun s t => F s t + G s t) = dFst F + dFst G :=
  deriv_fun_add hF.lineFirst hG.lineFirst
private lemma dSnd_add {F G : ℝ → ℝ → ℂ} (hF : ContDiff2 F) (hG : ContDiff2 G) :
    dSnd (fun s t => F s t + G s t) = dSnd F + dSnd G :=
  deriv_fun_add hF.lineSecond hG.lineSecond
private lemma dMix_add {F G : ℝ → ℝ → ℂ} (hF : ContDiff2 F) (hG : ContDiff2 G) :
    dMix (fun s t => F s t + G s t) = dMix F + dMix G := by
  have h : (fun s => deriv (fun t => F s t + G s t) 0) =ᶠ[𝓝 0]
      fun s => deriv (fun t => F s t) 0 + deriv (fun t => G s t) 0 := by
    filter_upwards [hF.eventually_lineSecond, hG.eventually_lineSecond] with s a b
    exact deriv_fun_add a b
  unfold dMix
  rw [h.deriv_eq]
  exact deriv_fun_add hF.differentiableAt_derivSecond hG.differentiableAt_derivSecond
private lemma derivs_eq_zero_of_eventually_const {F : ℝ → ℝ → ℂ} {x : ℂ}
    (h : ∀ᶠ w : ℝ × ℝ in 𝓝 (0, 0), F w.1 w.2 = x) : dFst F = 0 ∧ dSnd F = 0 ∧ dMix F = 0 := by
  have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ᶠ t in 𝓝 (0 : ℝ), F s t = x :=
    Filter.Eventually.curry_nhds h
  have h2 : (fun s => F s 0) =ᶠ[𝓝 0] fun _ => x := by
    filter_upwards [h1] with s hs
    exact hs.self_of_nhds
  have h3 : (fun t => F 0 t) =ᶠ[𝓝 0] fun _ => x := h1.self_of_nhds
  have h4 : (fun s => deriv (fun t => F s t) 0) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [h1] with s hs
    have : (fun t => F s t) =ᶠ[𝓝 0] fun _ => x := hs
    rw [this.deriv_eq]
    simp
  refine ⟨?_, ?_, ?_⟩
  · unfold dFst
    rw [h2.deriv_eq]
    simp
  · unfold dSnd
    rw [h3.deriv_eq]
    simp
  · unfold dMix
    rw [h4.deriv_eq]
    simp
section Families
variable {ι ι' ι'' : Type}
private def EntriesC2 (T : ℝ → ℝ → Matrix ι' ι ℂ) : Prop := ∀ p q, ContDiff2 fun s t => T s t p q
private lemma EntriesC2.mul [Fintype ι'] {A : ℝ → ℝ → Matrix ι'' ι' ℂ}
    {B : ℝ → ℝ → Matrix ι' ι ℂ} (hA : EntriesC2 A) (hB : EntriesC2 B) :
    EntriesC2 fun s t => A s t * B s t := by
  intro p q
  simp only [Matrix.mul_apply]
  exact ContDiff2.sum _ fun r _ => (hA p r).mul (hB r q)
private lemma derivFirst_mul [Fintype ι'] {A : ℝ → ℝ → Matrix ι'' ι' ℂ}
    {B : ℝ → ℝ → Matrix ι' ι ℂ} (hA : EntriesC2 A) (hB : EntriesC2 B) :
    derivFirst (fun s t => A s t * B s t) =
      derivFirst A * B 0 0 + A 0 0 * derivFirst B := by
  ext p q
  have h1 := dFst_sum (F := fun r s t => A s t p r * B s t r q) Finset.univ
    fun r _ => (hA p r).mul (hB r q)
  have h2 : derivFirst (fun s t => A s t * B s t) p q =
      dFst fun s t => ∑ r, A s t p r * B s t r q := by
    simp only [derivFirst, dFst, Matrix.mul_apply]
  rw [h2, h1]
  simp only [Matrix.add_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  exact dFst_mul (hA p r) (hB r q)
private lemma derivSecond_mul [Fintype ι'] {A : ℝ → ℝ → Matrix ι'' ι' ℂ}
    {B : ℝ → ℝ → Matrix ι' ι ℂ} (hA : EntriesC2 A) (hB : EntriesC2 B) :
    derivSecond (fun s t => A s t * B s t) =
      derivSecond A * B 0 0 + A 0 0 * derivSecond B := by
  ext p q
  have h1 := dSnd_sum (F := fun r s t => A s t p r * B s t r q) Finset.univ
    fun r _ => (hA p r).mul (hB r q)
  have h2 : derivSecond (fun s t => A s t * B s t) p q =
      dSnd fun s t => ∑ r, A s t p r * B s t r q := by
    simp only [derivSecond, dSnd, Matrix.mul_apply]
  rw [h2, h1]
  simp only [Matrix.add_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  exact dSnd_mul (hA p r) (hB r q)
private lemma derivMixed_mul [Fintype ι'] {A : ℝ → ℝ → Matrix ι'' ι' ℂ}
    {B : ℝ → ℝ → Matrix ι' ι ℂ} (hA : EntriesC2 A) (hB : EntriesC2 B) :
    derivMixed (fun s t => A s t * B s t) =
      derivMixed A * B 0 0 + derivSecond A * derivFirst B +
        derivFirst A * derivSecond B + A 0 0 * derivMixed B := by
  ext p q
  have h1 := dMix_sum (F := fun r s t => A s t p r * B s t r q) Finset.univ
    fun r _ => (hA p r).mul (hB r q)
  have h2 : derivMixed (fun s t => A s t * B s t) p q =
      dMix fun s t => ∑ r, A s t p r * B s t r q := by
    simp only [derivMixed, dMix, Matrix.mul_apply]
  rw [h2, h1]
  simp only [Matrix.add_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  exact dMix_mul (hA p r) (hB r q)
end Families
section Blocks
variable {Y ι ι' ι'' : Type}
private lemma blockBetween_mul [Fintype Y] [Fintype ι'] (c : ι → Y) (c' : ι' → Y)
    (c'' : ι'' → Y) (A : Matrix ι'' ι' ℂ) (B : Matrix ι' ι ℂ) (y'' y : Y) :
    blockBetween c c'' (A * B) y'' y =
      ∑ y', blockBetween c' c'' A y'' y' * blockBetween c c' B y' y := by
  classical
  ext p q
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply, blockBetween]
  rw [Finset.sum_comm]
  by_cases h : c'' p = y'' ∧ c q = y
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_eq_single (c' r)]
    · simp [h]
    · intro b _ hb
      have : ¬ (c' r = b) := fun e => hb e.symm
      simp [this]
    · simp
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun y' _ => ?_
    by_cases h1 : c'' p = y''
    · have h2 : ¬ c q = y := fun e => h ⟨h1, e⟩
      simp [h2]
    · simp [h1]
private lemma blockBetween_add (c : ι → Y) (c' : ι' → Y) (A B : Matrix ι' ι ℂ) (y' y : Y) :
    blockBetween c c' (A + B) y' y = blockBetween c c' A y' y + blockBetween c c' B y' y := by
  ext p q
  simp only [blockBetween, Matrix.add_apply]
  split_ifs <;> simp
private lemma blockBetween_smul (c : ι → Y) (c' : ι' → Y) (x : ℂ) (A : Matrix ι' ι ℂ)
    (y' y : Y) : blockBetween c c' (x • A) y' y = x • blockBetween c c' A y' y := by
  ext p q
  simp only [blockBetween, Matrix.smul_apply]
  split_ifs <;> simp
private lemma blockBetween_zero (c : ι → Y) (c' : ι' → Y) (y' y : Y) :
    blockBetween c c' (0 : Matrix ι' ι ℂ) y' y = 0 := by
  ext p q
  simp [blockBetween]
private lemma blockBetween_transpose (c : ι → Y) (c' : ι' → Y) (A : Matrix ι' ι ℂ) (y' y : Y) :
    blockBetween c' c A.transpose y y' = (blockBetween c c' A y' y).transpose := by
  ext p q
  simp only [blockBetween, Matrix.transpose_apply]
  by_cases h : c' q = y' ∧ c p = y
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun e => h e.symm]
end Blocks
section Cells
variable {L n k : ℕ}
private structure CellGeometry (L n k : ℕ) (ε S : ℝ) : Prop where
  dist_nonneg : ∀ y y' : Vertex L n k k, 0 ≤ cellDist y y'
  dist_symm : ∀ y y' : Vertex L n k k, cellDist y y' = cellDist y' y
  dist_triangle : ∀ x y z : Vertex L n k k, cellDist x z ≤ cellDist x y + cellDist y z
  sum_exp_le : ∃ _ : Fintype (Vertex L n k k), ∀ y : Vertex L n k k,
    ∑ y', Real.exp (-(ε * cellDist y y')) ≤ S
private def pairWeight (c₀ c₁ : Vertex L n k k) (r : ℝ) (a b : Bool) (y : Vertex L n k k) : ℝ :=
  (if a then cellDecayWeight r c₀ y else 1) * (if b then cellDecayWeight r c₁ y else 1)
private lemma cellDecayWeight_pos (r : ℝ) (c y : Vertex L n k k) : 0 < cellDecayWeight r c y :=
  Real.exp_pos _
private lemma pairWeight_nonneg (c₀ c₁ : Vertex L n k k) (r : ℝ) (a b : Bool)
    (y : Vertex L n k k) : 0 ≤ pairWeight c₀ c₁ r a b y := by
  unfold pairWeight
  have h0 := (cellDecayWeight_pos r c₀ y).le
  have h1 := (cellDecayWeight_pos r c₁ y).le
  cases a <;> cases b <;> simp <;> positivity
private lemma weightFactor_shift {ε S : ℝ} (G : CellGeometry L n k ε S) {r : ℝ} (hr : 0 < r)
    (c y'' y' : Vertex L n k k) (a a' : Bool) :
    (if a then cellDecayWeight r c y'' else 1) * (if a' then cellDecayWeight r c y' else 1) ≤
      (if (a || a') then cellDecayWeight (r / 4) c y'' else 1) *
        Real.exp (r / 4 * cellDist y'' y') := by
  have hD := G.dist_nonneg y'' y'
  have hu := G.dist_nonneg y'' c
  have hv := G.dist_nonneg y' c
  have ht := G.dist_triangle y'' y' c
  have h1 := mul_nonneg hr.le hD
  have h2 := mul_nonneg hr.le hu
  have h3 := mul_nonneg hr.le hv
  have h4 := mul_le_mul_of_nonneg_left ht hr.le
  cases a <;> cases a' <;> simp only [Bool.false_eq_true, if_true, if_false, Bool.or_false,
    Bool.or_true, Bool.false_or, mul_one, one_mul, cellDecayWeight, ← Real.exp_add]
  · exact Real.one_le_exp (by positivity)
  · apply Real.exp_le_exp.2
    nlinarith
  · apply Real.exp_le_exp.2
    nlinarith
  · apply Real.exp_le_exp.2
    nlinarith
private lemma pairWeight_shift {ε S : ℝ} (G : CellGeometry L n k ε S) {r : ℝ} (hr : 0 < r)
    (c₀ c₁ y'' y' : Vertex L n k k) (a b a' b' : Bool) :
    pairWeight c₀ c₁ r a b y'' * pairWeight c₀ c₁ r a' b' y' ≤
      pairWeight c₀ c₁ (r / 4) (a || a') (b || b') y'' * Real.exp (r / 2 * cellDist y'' y') := by
  have h0 := weightFactor_shift G hr c₀ y'' y' a a'
  have h1 := weightFactor_shift G hr c₁ y'' y' b b'
  have e : Real.exp (r / 2 * cellDist y'' y') =
      Real.exp (r / 4 * cellDist y'' y') * Real.exp (r / 4 * cellDist y'' y') := by
    rw [← Real.exp_add]
    ring_nf
  have p0 : 0 ≤ (if a then cellDecayWeight r c₀ y'' else 1) *
      (if a' then cellDecayWeight r c₀ y' else 1) := by
    have := (cellDecayWeight_pos r c₀ y'').le
    have := (cellDecayWeight_pos r c₀ y').le
    cases a <;> cases a' <;> simp <;> positivity
  have p1 : 0 ≤ (if b then cellDecayWeight r c₁ y'' else 1) *
      (if b' then cellDecayWeight r c₁ y' else 1) := by
    have := (cellDecayWeight_pos r c₁ y'').le
    have := (cellDecayWeight_pos r c₁ y').le
    cases b <;> cases b' <;> simp <;> positivity
  have p2 : 0 ≤ (if (a || a') then cellDecayWeight (r / 4) c₀ y'' else 1) *
      Real.exp (r / 4 * cellDist y'' y') := le_trans p0 h0
  calc pairWeight c₀ c₁ r a b y'' * pairWeight c₀ c₁ r a' b' y'
      = ((if a then cellDecayWeight r c₀ y'' else 1) *
          (if a' then cellDecayWeight r c₀ y' else 1)) *
        ((if b then cellDecayWeight r c₁ y'' else 1) *
          (if b' then cellDecayWeight r c₁ y' else 1)) := by
          unfold pairWeight; ring
    _ ≤ ((if (a || a') then cellDecayWeight (r / 4) c₀ y'' else 1) *
          Real.exp (r / 4 * cellDist y'' y')) *
        ((if (b || b') then cellDecayWeight (r / 4) c₁ y'' else 1) *
          Real.exp (r / 4 * cellDist y'' y')) :=
        mul_le_mul h0 h1 p1 p2
    _ = _ := by rw [e]; unfold pairWeight; ring
private lemma pairWeight_anti {ε S : ℝ} (G : CellGeometry L n k ε S) {r r' : ℝ} (h : r' ≤ r)
    (c₀ c₁ : Vertex L n k k) (a b : Bool) (y : Vertex L n k k) :
    pairWeight c₀ c₁ r a b y ≤ pairWeight c₀ c₁ r' a b y := by
  have h0 : cellDecayWeight r c₀ y ≤ cellDecayWeight r' c₀ y :=
    Real.exp_le_exp.2 (by nlinarith [G.dist_nonneg y c₀])
  have h1 : cellDecayWeight r c₁ y ≤ cellDecayWeight r' c₁ y :=
    Real.exp_le_exp.2 (by nlinarith [G.dist_nonneg y c₁])
  unfold pairWeight
  have p1 := (cellDecayWeight_pos r c₁ y).le
  have q0 := (cellDecayWeight_pos r' c₀ y).le
  cases a <;> cases b <;> simp [h0, h1]
  exact mul_le_mul h0 h1 p1 q0
variable {ι ι' ι'' : Type}
private def WeightedLocal [Fintype ι] [Fintype ι'] [DecidableEq ι] (c₀ c₁ : Vertex L n k k)
    (c : ι → Vertex L n k k) (c' : ι' → Vertex L n k k) (T : Matrix ι' ι ℂ) (M r : ℝ)
    (a b : Bool) : Prop :=
  IsLocalOnCells c c' T M r (pairWeight c₀ c₁ r a b)
private lemma WeightedLocal.mul {ε S : ℝ} (G : CellGeometry L n k ε S) [Fintype ι] [Fintype ι']
    [Fintype ι''] [DecidableEq ι] [DecidableEq ι'] {c₀ c₁ : Vertex L n k k}
    {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k} {c'' : ι'' → Vertex L n k k}
    {A : Matrix ι'' ι' ℂ} {B : Matrix ι' ι ℂ} {M M' r : ℝ} {a b a' b' : Bool} (hr : 0 < r)
    (hε : ε ≤ r / 4) (hM : 0 ≤ M) (hM' : 0 ≤ M') (hA : WeightedLocal c₀ c₁ c' c'' A M r a b)
    (hB : WeightedLocal c₀ c₁ c c' B M' r a' b') :
    WeightedLocal c₀ c₁ c c'' (A * B) (S * M * M') (r / 4) (a || a') (b || b') := by
  obtain ⟨_, hsum⟩ := G.sum_exp_le
  intro y'' y
  rw [blockBetween_mul c c' c'' A B y'' y]
  have hW := pairWeight_nonneg c₀ c₁ (r / 4) (a || a') (b || b') y''
  set W := pairWeight c₀ c₁ (r / 4) (a || a') (b || b') y'' with hWdef
  have hK : 0 ≤ M * M' * Real.exp (-(r / 4 * cellDist y'' y)) * W := by positivity
  have term : ∀ y', ‖blockBetween c' c'' A y'' y' * blockBetween c c' B y' y‖ ≤
      M * M' * Real.exp (-(r / 4 * cellDist y'' y)) * W *
        Real.exp (-(ε * cellDist y'' y')) := by
    intro y'
    have h1 := hA y'' y'
    have h2 := hB y' y
    have h3 := pairWeight_shift G hr c₀ c₁ y'' y' a b a' b'
    have d1 := G.dist_nonneg y'' y'
    have d2 := G.dist_nonneg y' y
    have dt := G.dist_triangle y'' y' y
    have e1 : 0 ≤ pairWeight c₀ c₁ r a b y'' := pairWeight_nonneg _ _ _ _ _ _
    have hexp : Real.exp (-(r * cellDist y'' y')) * Real.exp (-(r * cellDist y' y)) *
        Real.exp (r / 2 * cellDist y'' y') ≤
        Real.exp (-(r / 4 * cellDist y'' y)) * Real.exp (-(ε * cellDist y'' y')) := by
      simp only [← Real.exp_add]
      apply Real.exp_le_exp.2
      have k2 := mul_nonneg hr.le d2
      have k3 := mul_le_mul_of_nonneg_left dt hr.le
      have k4 := mul_le_mul_of_nonneg_right hε d1
      nlinarith
    calc ‖blockBetween c' c'' A y'' y' * blockBetween c c' B y' y‖
        ≤ ‖blockBetween c' c'' A y'' y'‖ * ‖blockBetween c c' B y' y‖ :=
          Matrix.l2_opNorm_mul _ _
      _ ≤ (M * Real.exp (-(r * cellDist y'' y')) * pairWeight c₀ c₁ r a b y'') *
          (M' * Real.exp (-(r * cellDist y' y)) * pairWeight c₀ c₁ r a' b' y') :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = M * M' * (Real.exp (-(r * cellDist y'' y')) * Real.exp (-(r * cellDist y' y))) *
          (pairWeight c₀ c₁ r a b y'' * pairWeight c₀ c₁ r a' b' y') := by ring
      _ ≤ M * M' * (Real.exp (-(r * cellDist y'' y')) * Real.exp (-(r * cellDist y' y))) *
          (W * Real.exp (r / 2 * cellDist y'' y')) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = M * M' * W * (Real.exp (-(r * cellDist y'' y')) *
            Real.exp (-(r * cellDist y' y)) * Real.exp (r / 2 * cellDist y'' y')) := by
          ring
      _ ≤ M * M' * W * (Real.exp (-(r / 4 * cellDist y'' y)) *
            Real.exp (-(ε * cellDist y'' y'))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  calc ‖∑ y', blockBetween c' c'' A y'' y' * blockBetween c c' B y' y‖
      ≤ ∑ y', ‖blockBetween c' c'' A y'' y' * blockBetween c c' B y' y‖ := norm_sum_le _ _
    _ ≤ ∑ y', M * M' * Real.exp (-(r / 4 * cellDist y'' y)) * W *
        Real.exp (-(ε * cellDist y'' y')) := Finset.sum_le_sum fun y' _ => term y'
    _ = M * M' * Real.exp (-(r / 4 * cellDist y'' y)) * W *
        ∑ y', Real.exp (-(ε * cellDist y'' y')) := (Finset.mul_sum _ _ _).symm
    _ ≤ M * M' * Real.exp (-(r / 4 * cellDist y'' y)) * W * S :=
        mul_le_mul_of_nonneg_left (hsum y'') hK
    _ = S * M * M' * Real.exp (-(r / 4 * cellDist y'' y)) * W := by ring
private lemma WeightedLocal.add [Fintype ι] [Fintype ι'] [DecidableEq ι] {c₀ c₁ : Vertex L n k k}
    {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k} {A B : Matrix ι' ι ℂ} {M M' r : ℝ}
    {a b : Bool} (hA : WeightedLocal c₀ c₁ c c' A M r a b)
    (hB : WeightedLocal c₀ c₁ c c' B M' r a b) :
    WeightedLocal c₀ c₁ c c' (A + B) (M + M') r a b := by
  intro y' y
  rw [blockBetween_add]
  refine (norm_add_le _ _).trans ?_
  have := add_le_add (hA y' y) (hB y' y)
  linarith
private lemma WeightedLocal.smul [Fintype ι] [Fintype ι'] [DecidableEq ι]
    {c₀ c₁ : Vertex L n k k} {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k}
    {A : Matrix ι' ι ℂ} {M r : ℝ} {a b : Bool} (x : ℂ)
    (hA : WeightedLocal c₀ c₁ c c' A M r a b) :
    WeightedLocal c₀ c₁ c c' (x • A) (‖x‖ * M) r a b := by
  intro y' y
  rw [blockBetween_smul, norm_smul]
  have := mul_le_mul_of_nonneg_left (hA y' y) (norm_nonneg x)
  linarith
private lemma WeightedLocal.mono {ε S : ℝ} (G : CellGeometry L n k ε S) [Fintype ι] [Fintype ι']
    [DecidableEq ι] {c₀ c₁ : Vertex L n k k} {c : ι → Vertex L n k k}
    {c' : ι' → Vertex L n k k} {A : Matrix ι' ι ℂ} {M M' r r' : ℝ} {a b : Bool} (hM : 0 ≤ M)
    (hMM : M ≤ M') (hr : r' ≤ r) (hA : WeightedLocal c₀ c₁ c c' A M r a b) :
    WeightedLocal c₀ c₁ c c' A M' r' a b := by
  intro y' y
  refine (hA y' y).trans ?_
  have h1 : Real.exp (-(r * cellDist y' y)) ≤ Real.exp (-(r' * cellDist y' y)) :=
    Real.exp_le_exp.2 (by nlinarith [G.dist_nonneg y' y])
  have h2 := pairWeight_anti G hr c₀ c₁ a b y'
  have h3 := pairWeight_nonneg c₀ c₁ r a b y'
  exact mul_le_mul (mul_le_mul hMM h1 (Real.exp_pos _).le (hM.trans hMM)) h2 h3
    (by have := hM.trans hMM; positivity)
private lemma WeightedLocal.zero [Fintype ι] [Fintype ι'] [DecidableEq ι]
    {c₀ c₁ : Vertex L n k k} {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k} {M r : ℝ}
    {a b : Bool} (hM : 0 ≤ M) : WeightedLocal c₀ c₁ c c' (0 : Matrix ι' ι ℂ) M r a b := by
  intro y' y
  rw [blockBetween_zero, norm_zero]
  have := pairWeight_nonneg c₀ c₁ r a b y'
  positivity
end Cells
section Norms
variable {a a' b b' : Type}
private lemma l2_norm_transpose_le [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (X : Matrix a b ℂ) : ‖X.transpose‖ ≤ ‖X‖ := by apply _root_.YangMills.SharedProofs.p19594 <;> assumption
private lemma l2_norm_fromBlocks_le [Fintype a] [Fintype a'] [Fintype b] [Fintype b']
    [DecidableEq a] [DecidableEq b] (A : Matrix a' a ℂ) (B : Matrix a' b ℂ)
    (C : Matrix b' a ℂ) (D : Matrix b' b ℂ) :
    ‖Matrix.fromBlocks A B C D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by apply _root_.YangMills.SharedProofs.p53664 <;> assumption
end Norms
section Closure
variable {L n k : ℕ} {ι ι' ι'' : Type}
private lemma pairWeight_ff (c₀ c₁ : Vertex L n k k) (r : ℝ) :
    pairWeight c₀ c₁ r false false = fun _ => 1 := by
  funext y
  simp [pairWeight]
private lemma pairWeight_tf (c₀ c₁ : Vertex L n k k) (r : ℝ) :
    pairWeight c₀ c₁ r true false = cellDecayWeight r c₀ := by
  funext y
  simp [pairWeight]
private lemma pairWeight_ft (c₀ c₁ : Vertex L n k k) (r : ℝ) :
    pairWeight c₀ c₁ r false true = cellDecayWeight r c₁ := by
  funext y
  simp [pairWeight]
private lemma pairWeight_tt (c₀ c₁ : Vertex L n k k) (r : ℝ) :
    pairWeight c₀ c₁ r true true = fun y => cellDecayWeight r c₀ y * cellDecayWeight r c₁ y := by
  funext y
  simp [pairWeight]
private structure LocalFourWeights [Fintype ι] [Fintype ι'] [DecidableEq ι]
    (c₀ c₁ : Vertex L n k k) (c : ι → Vertex L n k k) (c' : ι' → Vertex L n k k)
    (T : ℝ → ℝ → Matrix ι' ι ℂ) (M r : ℝ) : Prop where
  entries : EntriesC2 T
  value : WeightedLocal c₀ c₁ c c' (T 0 0) M r false false
  first : WeightedLocal c₀ c₁ c c' (derivFirst T) M r true false
  second : WeightedLocal c₀ c₁ c c' (derivSecond T) M r false true
  mixed : WeightedLocal c₀ c₁ c c' (derivMixed T) M r true true
private lemma fourWeights_of_local [Fintype ι] [Fintype ι'] [DecidableEq ι]
    {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k} {T : ℝ → ℝ → Matrix ι' ι ℂ}
    {z : Fin 4 → ℤ} {M r : ℝ} (h : IsLocalAlongBackground c c' T z M r) :
    LocalFourWeights (cellOfCoords L n k 0) (cellOfCoords L n k z) c c' T M r where
  entries := fun p q => h.contDiffAt_entry p q
  value := by unfold WeightedLocal; rw [pairWeight_ff]; exact h.value_local
  first := by unfold WeightedLocal; rw [pairWeight_tf]; exact h.derivFirst_local
  second := by unfold WeightedLocal; rw [pairWeight_ft]; exact h.derivSecond_local
  mixed := by unfold WeightedLocal; rw [pairWeight_tt]; exact h.derivMixed_local
private lemma local_of_fourWeights [Fintype ι] [Fintype ι'] [DecidableEq ι]
    {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k} {T : ℝ → ℝ → Matrix ι' ι ℂ}
    {z : Fin 4 → ℤ} {M r : ℝ}
    (h : LocalFourWeights (cellOfCoords L n k 0) (cellOfCoords L n k z) c c' T M r) :
    IsLocalAlongBackground c c' T z M r where
  contDiffAt_entry := fun p q => h.entries p q
  value_local := by have := h.value; unfold WeightedLocal at this; rwa [pairWeight_ff] at this
  derivFirst_local := by
    have := h.first; unfold WeightedLocal at this; rwa [pairWeight_tf] at this
  derivSecond_local := by
    have := h.second; unfold WeightedLocal at this; rwa [pairWeight_ft] at this
  derivMixed_local := by
    have := h.mixed; unfold WeightedLocal at this; rwa [pairWeight_tt] at this
private lemma LocalFourWeights.mono {ε S : ℝ} (G : CellGeometry L n k ε S) [Fintype ι]
    [Fintype ι'] [DecidableEq ι] {c₀ c₁ : Vertex L n k k} {c : ι → Vertex L n k k}
    {c' : ι' → Vertex L n k k} {T : ℝ → ℝ → Matrix ι' ι ℂ} {M M' r r' : ℝ} (hM : 0 ≤ M)
    (hMM : M ≤ M') (hr : r' ≤ r) (h : LocalFourWeights c₀ c₁ c c' T M r) :
    LocalFourWeights c₀ c₁ c c' T M' r' :=
  ⟨h.entries, WeightedLocal.mono G hM hMM hr h.value, WeightedLocal.mono G hM hMM hr h.first,
    WeightedLocal.mono G hM hMM hr h.second, WeightedLocal.mono G hM hMM hr h.mixed⟩
private lemma EntriesC2.add {A B : ℝ → ℝ → Matrix ι' ι ℂ} (hA : EntriesC2 A) (hB : EntriesC2 B) :
    EntriesC2 fun s t => A s t + B s t := fun p q => (hA p q).add (hB p q)
private lemma LocalFourWeights.add [Fintype ι] [Fintype ι'] [DecidableEq ι]
    {c₀ c₁ : Vertex L n k k} {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k}
    {A B : ℝ → ℝ → Matrix ι' ι ℂ} {M M' r : ℝ} (hA : LocalFourWeights c₀ c₁ c c' A M r)
    (hB : LocalFourWeights c₀ c₁ c c' B M' r) :
    LocalFourWeights c₀ c₁ c c' (fun s t => A s t + B s t) (M + M') r := by
  have e1 : derivFirst (fun s t => A s t + B s t) = derivFirst A + derivFirst B := by
    ext p q
    exact dFst_add (hA.entries p q) (hB.entries p q)
  have e2 : derivSecond (fun s t => A s t + B s t) = derivSecond A + derivSecond B := by
    ext p q
    exact dSnd_add (hA.entries p q) (hB.entries p q)
  have e3 : derivMixed (fun s t => A s t + B s t) = derivMixed A + derivMixed B := by
    ext p q
    exact dMix_add (hA.entries p q) (hB.entries p q)
  refine ⟨hA.entries.add hB.entries, hA.value.add hB.value, ?_, ?_, ?_⟩
  · rw [e1]; exact hA.first.add hB.first
  · rw [e2]; exact hA.second.add hB.second
  · rw [e3]; exact hA.mixed.add hB.mixed
private lemma LocalFourWeights.smul [Fintype ι] [Fintype ι'] [DecidableEq ι]
    {c₀ c₁ : Vertex L n k k} {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k}
    {A : ℝ → ℝ → Matrix ι' ι ℂ} {M r : ℝ} (x : ℂ) (hA : LocalFourWeights c₀ c₁ c c' A M r) :
    LocalFourWeights c₀ c₁ c c' (fun s t => x • A s t) (‖x‖ * M) r := by
  have e1 : derivFirst (fun s t => x • A s t) = x • derivFirst A := by
    ext p q
    exact dFst_const_mul x (hA.entries p q)
  have e2 : derivSecond (fun s t => x • A s t) = x • derivSecond A := by
    ext p q
    exact dSnd_const_mul x (hA.entries p q)
  have e3 : derivMixed (fun s t => x • A s t) = x • derivMixed A := by
    ext p q
    exact dMix_const_mul x (hA.entries p q)
  refine ⟨fun p q => (ContDiff2.const x).mul (hA.entries p q), hA.value.smul x, ?_, ?_, ?_⟩
  · rw [e1]; exact hA.first.smul x
  · rw [e2]; exact hA.second.smul x
  · rw [e3]; exact hA.mixed.smul x
private lemma LocalFourWeights.mul {ε S : ℝ} (G : CellGeometry L n k ε S) [Fintype ι]
    [Fintype ι'] [Fintype ι''] [DecidableEq ι] [DecidableEq ι'] {c₀ c₁ : Vertex L n k k}
    {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k} {c'' : ι'' → Vertex L n k k}
    {A : ℝ → ℝ → Matrix ι'' ι' ℂ} {B : ℝ → ℝ → Matrix ι' ι ℂ} {M M' r : ℝ} (hS : 0 ≤ S)
    (hr : 0 < r) (hε : ε ≤ r / 4) (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hA : LocalFourWeights c₀ c₁ c' c'' A M r) (hB : LocalFourWeights c₀ c₁ c c' B M' r) :
    LocalFourWeights c₀ c₁ c c'' (fun s t => A s t * B s t) (4 * S * M * M') (r / 4) := by
  have hK : 0 ≤ S * M * M' := by positivity
  refine ⟨hA.entries.mul hB.entries, ?_, ?_, ?_, ?_⟩
  · exact WeightedLocal.mono G hK (by nlinarith) le_rfl
      (WeightedLocal.mul G hr hε hM hM' hA.value hB.value)
  · rw [derivFirst_mul hA.entries hB.entries]
    exact WeightedLocal.mono G (by positivity) (by nlinarith) le_rfl
      (WeightedLocal.add (WeightedLocal.mul G hr hε hM hM' hA.first hB.value)
        (WeightedLocal.mul G hr hε hM hM' hA.value hB.first))
  · rw [derivSecond_mul hA.entries hB.entries]
    exact WeightedLocal.mono G (by positivity) (by nlinarith) le_rfl
      (WeightedLocal.add (WeightedLocal.mul G hr hε hM hM' hA.second hB.value)
        (WeightedLocal.mul G hr hε hM hM' hA.value hB.second))
  · rw [derivMixed_mul hA.entries hB.entries]
    exact WeightedLocal.mono G (by positivity) (by nlinarith) le_rfl
      (WeightedLocal.add (WeightedLocal.add (WeightedLocal.add
        (WeightedLocal.mul G hr hε hM hM' hA.mixed hB.value)
        (WeightedLocal.mul G hr hε hM hM' hA.second hB.first))
        (WeightedLocal.mul G hr hε hM hM' hA.first hB.second))
        (WeightedLocal.mul G hr hε hM hM' hA.value hB.mixed))
private lemma WeightedLocal.transpose {ε S : ℝ} (G : CellGeometry L n k ε S) [Fintype ι]
    [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] {c₀ c₁ : Vertex L n k k}
    {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k} {A : Matrix ι' ι ℂ} {M r : ℝ}
    {a b : Bool} (hr : 0 < r) (hM : 0 ≤ M) (hA : WeightedLocal c₀ c₁ c c' A M r a b) :
    WeightedLocal c₀ c₁ c' c A.transpose M (r / 4) a b := by
  intro y y'
  rw [blockBetween_transpose]
  refine (l2_norm_transpose_le _).trans ((hA y' y).trans ?_)
  have h3 := pairWeight_shift G hr c₀ c₁ y y' false false a b
  rw [pairWeight_ff] at h3
  simp only [one_mul, Bool.false_or] at h3
  have d := G.dist_nonneg y y'
  rw [G.dist_symm y' y]
  have hW := pairWeight_nonneg c₀ c₁ (r / 4) a b y
  calc M * Real.exp (-(r * cellDist y y')) * pairWeight c₀ c₁ r a b y'
      ≤ M * Real.exp (-(r * cellDist y y')) *
        (pairWeight c₀ c₁ (r / 4) a b y * Real.exp (r / 2 * cellDist y y')) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = M * (Real.exp (-(r * cellDist y y')) * Real.exp (r / 2 * cellDist y y')) *
        pairWeight c₀ c₁ (r / 4) a b y := by ring
    _ ≤ M * Real.exp (-(r / 4 * cellDist y y')) * pairWeight c₀ c₁ (r / 4) a b y := by
        have : Real.exp (-(r * cellDist y y')) * Real.exp (r / 2 * cellDist y y') ≤
            Real.exp (-(r / 4 * cellDist y y')) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          nlinarith [mul_nonneg hr.le d]
        gcongr
private lemma LocalFourWeights.transpose {ε S : ℝ} (G : CellGeometry L n k ε S) [Fintype ι]
    [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] {c₀ c₁ : Vertex L n k k}
    {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k} {T : ℝ → ℝ → Matrix ι' ι ℂ} {M r : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (h : LocalFourWeights c₀ c₁ c c' T M r) :
    LocalFourWeights c₀ c₁ c' c (fun s t => (T s t).transpose) M (r / 4) :=
  ⟨fun p q => h.entries q p, WeightedLocal.transpose G hr hM h.value,
    WeightedLocal.transpose G hr hM h.first, WeightedLocal.transpose G hr hM h.second,
    WeightedLocal.transpose G hr hM h.mixed⟩
private lemma LocalFourWeights.const [Fintype ι] [Fintype ι'] [DecidableEq ι]
    {c₀ c₁ : Vertex L n k k} {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k}
    {A : Matrix ι' ι ℂ} {M r : ℝ} (hM : 0 ≤ M) (h : WeightedLocal c₀ c₁ c c' A M r false false) :
    LocalFourWeights c₀ c₁ c c' (fun _ _ => A) M r := by
  have e1 : derivFirst (fun _ _ => A) = (0 : Matrix ι' ι ℂ) := by
    ext p q
    simp [derivFirst]
  have e2 : derivSecond (fun _ _ => A) = (0 : Matrix ι' ι ℂ) := by
    ext p q
    simp [derivSecond]
  have e3 : derivMixed (fun _ _ => A) = (0 : Matrix ι' ι ℂ) := by
    ext p q
    simp [derivMixed]
  refine ⟨fun p q => ContDiff2.const _, h, ?_, ?_, ?_⟩
  · rw [e1]; exact WeightedLocal.zero hM
  · rw [e2]; exact WeightedLocal.zero hM
  · rw [e3]; exact WeightedLocal.zero hM
private lemma WeightedLocal.blocks {ι₁ ι₂ ι₁' ι₂' : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₁']
    [Fintype ι₂'] [DecidableEq ι₁] [DecidableEq ι₂] {c₀ c₁' : Vertex L n k k}
    {d₁ : ι₁ → Vertex L n k k} {d₂ : ι₂ → Vertex L n k k} {e₁ : ι₁' → Vertex L n k k}
    {e₂ : ι₂' → Vertex L n k k} {A : Matrix ι₁' ι₁ ℂ} {B : Matrix ι₁' ι₂ ℂ}
    {C : Matrix ι₂' ι₁ ℂ} {D : Matrix ι₂' ι₂ ℂ} {M r : ℝ} {a b : Bool}
    (hA : WeightedLocal c₀ c₁' d₁ e₁ A M r a b) (hB : WeightedLocal c₀ c₁' d₂ e₁ B M r a b)
    (hC : WeightedLocal c₀ c₁' d₁ e₂ C M r a b) (hD : WeightedLocal c₀ c₁' d₂ e₂ D M r a b) :
    WeightedLocal c₀ c₁' (Sum.elim d₁ d₂) (Sum.elim e₁ e₂) (Matrix.fromBlocks A B C D)
      (4 * M) r a b := by
  intro y' y
  have e : blockBetween (Sum.elim d₁ d₂) (Sum.elim e₁ e₂) (Matrix.fromBlocks A B C D) y' y =
      Matrix.fromBlocks (blockBetween d₁ e₁ A y' y) (blockBetween d₂ e₁ B y' y)
        (blockBetween d₁ e₂ C y' y) (blockBetween d₂ e₂ D y' y) := by
    ext p q
    rcases p with p | p <;> rcases q with q | q <;> simp [blockBetween] <;> congr
  rw [e]
  refine (l2_norm_fromBlocks_le _ _ _ _).trans ?_
  have := hA y' y
  have := hB y' y
  have := hC y' y
  have := hD y' y
  linarith
private lemma LocalFourWeights.blocks {ι₁ ι₂ ι₁' ι₂' : Type} [Fintype ι₁] [Fintype ι₂]
    [Fintype ι₁'] [Fintype ι₂'] [DecidableEq ι₁] [DecidableEq ι₂] {c₀ c₁' : Vertex L n k k}
    {d₁ : ι₁ → Vertex L n k k} {d₂ : ι₂ → Vertex L n k k} {e₁ : ι₁' → Vertex L n k k}
    {e₂ : ι₂' → Vertex L n k k} {A : ℝ → ℝ → Matrix ι₁' ι₁ ℂ} {B : ℝ → ℝ → Matrix ι₁' ι₂ ℂ}
    {C : ℝ → ℝ → Matrix ι₂' ι₁ ℂ} {D : ℝ → ℝ → Matrix ι₂' ι₂ ℂ} {M r : ℝ}
    (hA : LocalFourWeights c₀ c₁' d₁ e₁ A M r) (hB : LocalFourWeights c₀ c₁' d₂ e₁ B M r)
    (hC : LocalFourWeights c₀ c₁' d₁ e₂ C M r) (hD : LocalFourWeights c₀ c₁' d₂ e₂ D M r) :
    LocalFourWeights c₀ c₁' (Sum.elim d₁ d₂) (Sum.elim e₁ e₂)
      (fun s t => Matrix.fromBlocks (A s t) (B s t) (C s t) (D s t)) (4 * M) r := by
  have e1 : derivFirst (fun s t => Matrix.fromBlocks (A s t) (B s t) (C s t) (D s t)) =
      Matrix.fromBlocks (derivFirst A) (derivFirst B) (derivFirst C) (derivFirst D) := by
    ext p q
    rcases p with p | p <;> rcases q with q | q <;> rfl
  have e2 : derivSecond (fun s t => Matrix.fromBlocks (A s t) (B s t) (C s t) (D s t)) =
      Matrix.fromBlocks (derivSecond A) (derivSecond B) (derivSecond C) (derivSecond D) := by
    ext p q
    rcases p with p | p <;> rcases q with q | q <;> rfl
  have e3 : derivMixed (fun s t => Matrix.fromBlocks (A s t) (B s t) (C s t) (D s t)) =
      Matrix.fromBlocks (derivMixed A) (derivMixed B) (derivMixed C) (derivMixed D) := by
    ext p q
    rcases p with p | p <;> rcases q with q | q <;> rfl
  refine ⟨?_, WeightedLocal.blocks hA.value hB.value hC.value hD.value, ?_, ?_, ?_⟩
  · intro p q
    rcases p with p | p <;> rcases q with q | q
    · exact hA.entries p q
    · exact hB.entries p q
    · exact hC.entries p q
    · exact hD.entries p q
  · rw [e1]; exact WeightedLocal.blocks hA.first hB.first hC.first hD.first
  · rw [e2]; exact WeightedLocal.blocks hA.second hB.second hC.second hD.second
  · rw [e3]; exact WeightedLocal.blocks hA.mixed hB.mixed hC.mixed hD.mixed
end Closure
section Inverses
variable {L n k : ℕ} {ι : Type}
private lemma ContDiff2.prod {κ : Type} (u : Finset κ) {F : κ → ℝ → ℝ → ℂ}
    (hF : ∀ i ∈ u, ContDiff2 (F i)) :
    ContDiff2 (fun s t => ∏ i ∈ u, F i s t) := contDiffAt_prod fun i hi => hF i hi
private lemma ContDiff2.det [Fintype ι] [DecidableEq ι] {A : ℝ → ℝ → Matrix ι ι ℂ}
    (hA : EntriesC2 A) : ContDiff2 fun s t => (A s t).det := by
  simp only [Matrix.det_apply']
  exact ContDiff2.sum _ fun σ _ => (ContDiff2.const _).mul (ContDiff2.prod _ fun i _ => hA _ _)
private lemma EntriesC2.inv [Fintype ι] [DecidableEq ι] {T : ℝ → ℝ → Matrix ι ι ℂ}
    (hT : EntriesC2 T) (hdet : IsUnit (T 0 0).det) : EntriesC2 fun s t => (T s t)⁻¹ := by
  intro p q
  have hne : (T 0 0).det ≠ 0 := hdet.ne_zero
  have hinv : ContDiff2 fun s t => ((T s t).det)⁻¹ := ContDiffAt.inv (ContDiff2.det hT) hne
  have hadj : ContDiff2 fun s t => (T s t).adjugate p q := by
    simp only [Matrix.adjugate_apply]
    apply ContDiff2.det
    intro a b
    by_cases h : a = q
    · subst h
      simp only [Matrix.updateRow_self]
      exact ContDiff2.const _
    · simp only [Matrix.updateRow_ne h]
      exact hT a b
  have e : (fun s t => (T s t)⁻¹ p q) =
      fun s t => ((T s t).det)⁻¹ * (T s t).adjugate p q := by
    funext s t
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  rw [e]
  exact hinv.mul hadj
private lemma WeightedLocal.neg [Fintype ι] [DecidableEq ι] {ι' : Type} [Fintype ι']
    {c₀ c₁ : Vertex L n k k} {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k}
    {A : Matrix ι' ι ℂ} {M r : ℝ} {a b : Bool} (h : WeightedLocal c₀ c₁ c c' A M r a b) :
    WeightedLocal c₀ c₁ c c' (-A) M r a b := by
  have := WeightedLocal.smul (-1 : ℂ) h
  simpa using this
private lemma LocalFourWeights.inv {ε S : ℝ} (G : CellGeometry L n k ε S) [Fintype ι]
    [DecidableEq ι] {c₀ c₁ : Vertex L n k k} {c : ι → Vertex L n k k}
    {T : ℝ → ℝ → Matrix ι ι ℂ} {M r : ℝ} (hS : 1 ≤ S) (hr : 0 < r) (hε : ε ≤ r / 1024)
    (hM : 0 ≤ M) (hT : LocalFourWeights c₀ c₁ c c T M r) (hdet : IsUnit (T 0 0).det)
    (hI : WeightedLocal c₀ c₁ c c (T 0 0)⁻¹ M r false false) :
    LocalFourWeights c₀ c₁ c c (fun s t => (T s t)⁻¹) ((4 * S) ^ 4 * (M + 1) ^ 5) (r / 256) := by
  set m : ℝ := M + 1 with hm
  have hm1 : 1 ≤ m := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hMm : M ≤ m := by linarith
  have smI : EntriesC2 fun s t => (T s t)⁻¹ := hT.entries.inv hdet
  have hne : (T 0 0).det ≠ 0 := hdet.ne_zero
  have hev : ∀ᶠ w : ℝ × ℝ in 𝓝 (0, 0), IsUnit (T w.1 w.2).det := by
    have hc : ContinuousAt (fun w : ℝ × ℝ => (T w.1 w.2).det) (0, 0) :=
      ContDiffAt.continuousAt (ContDiff2.det hT.entries)
    filter_upwards [hc.eventually_ne hne] with w hw using isUnit_iff_ne_zero.2 hw
  have hconst : ∀ p q, dFst (fun s t => (T s t * (T s t)⁻¹) p q) = 0 ∧
      dSnd (fun s t => (T s t * (T s t)⁻¹) p q) = 0 ∧
      dMix (fun s t => (T s t * (T s t)⁻¹) p q) = 0 := by
    intro p q
    refine derivs_eq_zero_of_eventually_const (x := (1 : Matrix ι ι ℂ) p q) ?_
    filter_upwards [hev] with w hw
    rw [Matrix.mul_nonsing_inv _ hw]
  have zS : derivFirst (fun s t => T s t * (T s t)⁻¹) = 0 := by
    ext p q
    exact (hconst p q).1
  have zT : derivSecond (fun s t => T s t * (T s t)⁻¹) = 0 := by
    ext p q
    exact (hconst p q).2.1
  have zM : derivMixed (fun s t => T s t * (T s t)⁻¹) = 0 := by
    ext p q
    exact (hconst p q).2.2
  rw [derivFirst_mul hT.entries smI] at zS
  rw [derivSecond_mul hT.entries smI] at zT
  rw [derivMixed_mul hT.entries smI] at zM
  set I0 : Matrix ι ι ℂ := (T 0 0)⁻¹ with hI0
  set dIs := derivFirst fun s t => (T s t)⁻¹ with hdIs
  set dIt := derivSecond fun s t => (T s t)⁻¹ with hdIt
  set dIm := derivMixed fun s t => (T s t)⁻¹ with hdIm
  have left : I0 * T 0 0 = 1 := Matrix.nonsing_inv_mul _ hdet
  have solve : ∀ X Z : Matrix ι ι ℂ, X + T 0 0 * Z = 0 → Z = -(I0 * X) := by
    intro X Z h
    have h1 : T 0 0 * Z = -X := eq_neg_of_add_eq_zero_right h
    calc Z = (I0 * T 0 0) * Z := by rw [left, Matrix.one_mul]
      _ = I0 * (T 0 0 * Z) := Matrix.mul_assoc _ _ _
      _ = -(I0 * X) := by rw [h1, Matrix.mul_neg]
  have eS : dIs = -(I0 * (derivFirst T * I0)) := solve _ _ zS
  have eT : dIt = -(I0 * (derivSecond T * I0)) := solve _ _ zT
  have eM : dIm = -(I0 * (derivMixed T * I0 + derivSecond T * dIs +
      derivFirst T * dIt)) := solve _ _ zM
  have r1 : 0 < r / 4 := by positivity
  have r2 : 0 < r / 4 / 4 := by positivity
  have r3 : 0 < r / 4 / 4 / 4 := by positivity
  have q1 : r / 4 ≤ r := by linarith
  have q2 : r / 4 / 4 ≤ r := by linarith
  have q3 : r / 4 / 4 / 4 ≤ r := by linarith
  have q4 : r / 4 / 4 / 4 ≤ r / 4 := by linarith
  have f0 : ε ≤ r / 4 := by linarith
  have f1 : ε ≤ r / 4 / 4 := by linarith
  have f2 : ε ≤ r / 4 / 4 / 4 := by linarith
  have f3 : ε ≤ r / 4 / 4 / 4 / 4 := by linarith
  have I1 : WeightedLocal c₀ c₁ c c I0 m r false false := WeightedLocal.mono G hM hMm le_rfl hI
  have Ts : WeightedLocal c₀ c₁ c c (derivFirst T) m r true false :=
    WeightedLocal.mono G hM hMm le_rfl hT.first
  have Tt : WeightedLocal c₀ c₁ c c (derivSecond T) m r false true :=
    WeightedLocal.mono G hM hMm le_rfl hT.second
  have Tm : WeightedLocal c₀ c₁ c c (derivMixed T) m r true true :=
    WeightedLocal.mono G hM hMm le_rfl hT.mixed
  set x1 : ℝ := S * m * m with hx1
  set x2 : ℝ := S * m * x1 with hx2
  set x3 : ℝ := S * m * x2 with hx3
  have p1 : 0 ≤ x1 := by positivity
  have p2 : 0 ≤ x2 := by positivity
  have Is : WeightedLocal c₀ c₁ c c dIs x2 (r / 4 / 4) true false := by
    rw [eS]
    exact WeightedLocal.neg (WeightedLocal.mul G r1 f1 hm0 p1 (WeightedLocal.mono G hm0 le_rfl q1 I1)
      (WeightedLocal.mul G hr f0 hm0 hm0 Ts I1))
  have It : WeightedLocal c₀ c₁ c c dIt x2 (r / 4 / 4) false true := by
    rw [eT]
    exact WeightedLocal.neg (WeightedLocal.mul G r1 f1 hm0 p1 (WeightedLocal.mono G hm0 le_rfl q1 I1)
      (WeightedLocal.mul G hr f0 hm0 hm0 Tt I1))
  have A1 : WeightedLocal c₀ c₁ c c (derivMixed T * I0) x1 (r / 4 / 4 / 4) true true :=
    WeightedLocal.mono G p1 le_rfl q4 (WeightedLocal.mul G hr f0 hm0 hm0 Tm I1)
  have A2 : WeightedLocal c₀ c₁ c c (derivSecond T * dIs) x3 (r / 4 / 4 / 4) true true :=
    WeightedLocal.mul G r2 f2 hm0 p2 (WeightedLocal.mono G hm0 le_rfl q2 Tt) Is
  have A3 : WeightedLocal c₀ c₁ c c (derivFirst T * dIt) x3 (r / 4 / 4 / 4) true true :=
    WeightedLocal.mul G r2 f2 hm0 p2 (WeightedLocal.mono G hm0 le_rfl q2 Ts) It
  have Im : WeightedLocal c₀ c₁ c c dIm (S * m * (x1 + x3 + x3)) (r / 4 / 4 / 4 / 4) true true := by
    rw [eM]
    exact WeightedLocal.neg (WeightedLocal.mul G r3 f3 hm0 (by positivity)
      (WeightedLocal.mono G hm0 le_rfl q3 I1) ((A1.add A2).add A3))
  have b2 : x2 ≤ S ^ 4 * m ^ 5 := by
    have e : x2 = S ^ 2 * m ^ 3 := by rw [hx2, hx1]; ring
    rw [e]
    exact mul_le_mul (pow_le_pow_right₀ hS (by norm_num)) (pow_le_pow_right₀ hm1 (by norm_num))
      (by positivity) (by positivity)
  have b3 : S * m * (x1 + x3 + x3) ≤ 3 * (S ^ 4 * m ^ 5) := by
    have e : S * m * (x1 + x3 + x3) = S ^ 2 * m ^ 3 + 2 * (S ^ 4 * m ^ 5) := by
      rw [hx3, hx2, hx1]; ring
    rw [e]
    have : S ^ 2 * m ^ 3 ≤ S ^ 4 * m ^ 5 :=
      mul_le_mul (pow_le_pow_right₀ hS (by norm_num)) (pow_le_pow_right₀ hm1 (by norm_num))
        (by positivity) (by positivity)
    linarith
  have hK : (4 * S) ^ 4 * m ^ 5 = 256 * (S ^ 4 * m ^ 5) := by ring
  have hmK : m ≤ S ^ 4 * m ^ 5 := by
    have a1 : (1 : ℝ) ≤ S ^ 4 := one_le_pow₀ hS
    have a2 : m ≤ m ^ 5 := le_self_pow₀ hm1 (by norm_num)
    calc m = 1 * m := by ring
      _ ≤ S ^ 4 * m ^ 5 := mul_le_mul a1 a2 hm0 (by positivity)
  refine ⟨smI, ?_, ?_, ?_, ?_⟩
  · exact WeightedLocal.mono G hm0 (by rw [hK]; linarith) (by linarith) I1
  · exact WeightedLocal.mono G p2 (by rw [hK]; linarith) (by linarith) Is
  · exact WeightedLocal.mono G p2 (by rw [hK]; linarith) (by linarith) It
  · exact WeightedLocal.mono G (by positivity) (by rw [hK]; linarith) (by linarith) Im
end Inverses
section Distance
open TorusMetric
private lemma supNormVec_nonneg' (v : Fin 4 → ℝ) : 0 ≤ supNormVec v :=
  (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
variable {S : ℝ}
private lemma torusEuclidNorm_nonneg' (x : Torus4 S) : 0 ≤ torusEuclidNorm x := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_nonneg <;> assumption
private lemma torusEuclidNorm_neg' (x : Torus4 S) : torusEuclidNorm (-x) = torusEuclidNorm x := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.torusEuclidNorm_neg <;> assumption
private lemma torusEuclidNorm_add_le' (x y : Torus4 S) :
    torusEuclidNorm (x + y) ≤ torusEuclidNorm x + torusEuclidNorm y := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_add_le <;> assumption
private lemma torusSupNorm_le_torusEuclidNorm' (x : Torus4 S) :
    torusSupNorm x ≤ torusEuclidNorm x := by apply _root_.YangMills.SharedProofs.p76601 <;> assumption
end Distance
private lemma exists_cellGeometry
    (hs : HessianOfTheMainTerm.SiteSums.BallDoublingAndWeightBound)
    (hl : HessianOfTheMainTerm.SiteLengthFacts) {ε : ℝ} (hε : 0 < ε) :
    ∃ S₀ : ℝ, 1 ≤ S₀ ∧ ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n →
      CellGeometry L n k ε S₀ := by
  obtain ⟨T, -, hT⟩ := hs.2 ε hε
  refine ⟨max T 1, le_max_right _ _, fun L n k hL hn => ?_⟩
  have hL1 : 1 < L := by have := hL.2; omega
  have hj : 0 ≤ (n : ℤ) + PeriodicLattice.levelDepth k k := by
    simp [PeriodicLattice.levelDepth]
  obtain ⟨hfin, -⟩ := hl L n (PeriodicLattice.levelDepth k k) hL1 hj
  have hsp : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) = 1 := by
    rw [meshSize_levelDepth]
    simp [meshAt]
  refine ⟨fun y y' => torusEuclidNorm_nonneg' _, fun y y' => ?_, fun x y z => ?_, ?_⟩
  · unfold cellDist
    rw [← neg_sub, torusEuclidNorm_neg']
  · unfold cellDist
    have e : (x : PeriodicLattice.FourTorus L n) - z =
        ((x : PeriodicLattice.FourTorus L n) - y) + (y - z) := by
      abel
    rw [e]
    exact torusEuclidNorm_add_le' _ _
  · letI : Fintype (Vertex L n k k) := Fintype.ofFinite _
    refine ⟨this, fun y => ?_⟩
    have h1 := hT L n (PeriodicLattice.levelDepth k k) this hL1 hj y
    refine le_trans (Finset.sum_le_sum fun y' _ => ?_) (h1.trans (le_max_left _ _))
    set u := HessianOfTheMainTerm.supLengthInMesh (y' - y) with hu
    have hu0 : 0 ≤ u := by
      rw [hu]
      unfold HessianOfTheMainTerm.supLengthInMesh
      rw [hsp, div_one]
      exact (Real.sInf_nonneg (by rintro _ ⟨v, _, rfl⟩; exact supNormVec_nonneg' v))
    have hud : u ≤ cellDist y y' := by
      rw [hu]
      unfold HessianOfTheMainTerm.supLengthInMesh cellDist
      rw [hsp, div_one]
      have e : ((y' - y : Vertex L n k k) : PeriodicLattice.FourTorus L n) =
          -((y : PeriodicLattice.FourTorus L n) - y') := by
        push_cast
        abel
      rw [e]
      exact (torusSupNorm_le_torusEuclidNorm' _).trans_eq (torusEuclidNorm_neg' _)
    have h2 : Real.exp (-(ε * cellDist y y')) ≤ Real.exp (-ε * u) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h3 : (1 : ℝ) ≤ (1 + u) ^ 2 := by nlinarith
    calc Real.exp (-(ε * cellDist y y')) ≤ Real.exp (-ε * u) := h2
      _ = 1 * Real.exp (-ε * u) := by ring
      _ ≤ (1 + u) ^ 2 * Real.exp (-ε * u) := by gcongr
theorem localFamiliesClosed_of_siteBounds
    (hs : HessianOfTheMainTerm.SiteSums.BallDoublingAndWeightBound)
    (hl : HessianOfTheMainTerm.SiteLengthFacts) :
    LocalFamiliesClosed := by
  intro θ hθ
  obtain ⟨S₀, hS₀, hG⟩ := exists_cellGeometry hs hl (ε := θ / 1024) (by positivity)
  have hS0 : 0 ≤ S₀ := by linarith
  refine ⟨4 * S₀, by linarith, fun L n k hL hn => ?_⟩
  have G := hG L n k hL hn
  have f0 : θ / 1024 ≤ θ / 4 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ι ι' _ _ _ c c' A z M hM h
    refine local_of_fourWeights (LocalFourWeights.const hM ?_)
    unfold WeightedLocal
    rw [pairWeight_ff]
    exact h
  · intro ι ι' _ _ _ c c' T z M M' θ' hM hMM _ hθ' h
    exact local_of_fourWeights (LocalFourWeights.mono G hM hMM hθ' (fourWeights_of_local h))
  · intro ι ι' _ _ _ c c' T T' z M M' h h'
    exact local_of_fourWeights
      (LocalFourWeights.add (fourWeights_of_local h) (fourWeights_of_local h'))
  · intro ι ι' _ _ _ c c' T z M x h
    exact local_of_fourWeights (LocalFourWeights.smul x (fourWeights_of_local h))
  · intro ι ι' _ _ _ _ c c' T z M hM h
    exact local_of_fourWeights (LocalFourWeights.transpose G hθ hM (fourWeights_of_local h))
  · intro ι₁ ι₂ ι₁' ι₂' _ _ _ _ _ _ c₁ c₂ c₁' c₂' A B C D z M hA hB hC hD
    exact local_of_fourWeights (LocalFourWeights.blocks (fourWeights_of_local hA)
      (fourWeights_of_local hB) (fourWeights_of_local hC) (fourWeights_of_local hD))
  · intro ι ι' ι'' _ _ _ _ _ c c' c'' A B z M M' hM hM' hA hB
    exact local_of_fourWeights (LocalFourWeights.mul G hS0 hθ f0 hM hM'
      (fourWeights_of_local hA) (fourWeights_of_local hB))
  · intro ι _ _ c T z M hM h hdet hinv
    refine local_of_fourWeights
      (LocalFourWeights.inv G hS₀ hθ le_rfl hM (fourWeights_of_local h) hdet ?_)
    unfold WeightedLocal
    rw [pairWeight_ff]
    exact hinv
end YangMills.Construction.RunningCouplingSlope.ClosureProof
end

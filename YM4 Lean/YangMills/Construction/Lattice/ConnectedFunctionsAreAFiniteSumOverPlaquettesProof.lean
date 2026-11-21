import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsAndThePrincipalLogarithm
import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsAreSmooth
import YangMills.Construction.Lattice.ConnectedFunctionsAreAFiniteSumOverPlaquettes
import YangMills.Construction.Lattice.LatticeIntegralIsEntireAndPositive
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Filter MeasureTheory Set Topology
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.ConnectedFunctionExpansion
open SeveralComplexVariables PeriodicLattice
section Calculus
variable {ι : Type} [Fintype ι] [Nonempty ι]
def iteratedPartialDerivList (l : List ι) (h : (ι → ℂ) → ℂ) : (ι → ℂ) → ℂ :=
  l.foldr (fun q g => partialDeriv q g) h
omit [Fintype ι] [Nonempty ι] in
@[simp] lemma iteratedPartialDerivList_nil (h : (ι → ℂ) → ℂ) : iteratedPartialDerivList [] h = h := rfl
omit [Fintype ι] [Nonempty ι] in
@[simp] lemma iteratedPartialDerivList_cons (q : ι) (l : List ι) (h : (ι → ℂ) → ℂ) :
    iteratedPartialDerivList (q :: l) h = partialDeriv q (iteratedPartialDerivList l h) := rfl
omit [Nonempty ι] in
lemma eventually_add_smul_mem {U : Set (ι → ℂ)} (hU : IsOpen U) {c : ι → ℂ} (hc : c ∈ U) (v : ι → ℂ) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ), c + ζ • v ∈ U := by
  have hcont : Continuous fun ζ : ℂ => c + ζ • v := by fun_prop
  exact hcont.continuousAt.eventually (hU.mem_nhds (by simpa using hc))
omit [Nonempty ι] in
lemma partialDeriv_congr_on {U : Set (ι → ℂ)} (hU : IsOpen U) {g g' : (ι → ℂ) → ℂ}
    (hg : EqOn g g' U) (q : ι) : EqOn (partialDeriv q g) (partialDeriv q g') U := by
  intro c hc
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [eventually_add_smul_mem hU hc (basisVector q)] with ζ hζ using hg hζ
omit [Nonempty ι] in
lemma iteratedPartialDerivList_congr_on {U : Set (ι → ℂ)} (hU : IsOpen U) {g g' : (ι → ℂ) → ℂ}
    (hg : EqOn g g' U) (l : List ι) :
    EqOn (iteratedPartialDerivList l g) (iteratedPartialDerivList l g') U := by
  induction l with
  | nil => exact hg
  | cons q l ih => exact partialDeriv_congr_on hU ih q
omit [Fintype ι] [Nonempty ι] in
lemma partialDeriv_const_add (a : ℂ) (g : (ι → ℂ) → ℂ) (q : ι) :
    partialDeriv q (fun c => a + g c) = partialDeriv q g := by
  funext c
  simp [partialDeriv, deriv_const_add]
omit [Nonempty ι] in
lemma iteratedPartialDerivList_const_add (a : ℂ) (g : (ι → ℂ) → ℂ) {l : List ι}
    (hl : l ≠ []) : iteratedPartialDerivList l (fun c => a + g c) = iteratedPartialDerivList l g := by
  induction l with
  | nil => exact absurd rfl hl
  | cons q l ih =>
    rcases eq_or_ne l [] with rfl | hne
    · exact partialDeriv_const_add a g q
    · simp only [iteratedPartialDerivList_cons, ih hne]
lemma isHolomorphicOnOpen_of_differentiableOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U : Set (ι → ℂ)} {h : (ι → ℂ) → F} (hU : IsOpen U) (hd : DifferentiableOn ℂ h U) :
    IsHolomorphicOnOpen U h := by
  refine ⟨hU, hd.continuousOn, fun c hc q => ?_⟩
  have hlin : Differentiable ℂ fun ζ : ℂ => c + ζ • basisVector q := by fun_prop
  filter_upwards [eventually_add_smul_mem hU hc (basisVector q)] with ζ hζ
  exact (hd.differentiableAt (hU.mem_nhds hζ)).comp ζ (hlin ζ)
variable (hCalc : SeveralComplexVariables.HolomorphicCalculus.Statement)
  (hSmooth : SeveralComplexVariables.HolomorphicContDiff.Statement)
include hCalc in
lemma iteratedPartialDerivList_holomorphic {U : Set (ι → ℂ)} (hU : IsOpen U) {g : (ι → ℂ) → ℂ}
    (hg : IsHolomorphicOnOpen U g) (l : List ι) :
    IsHolomorphicOnOpen U (iteratedPartialDerivList l g) := by
  induction l with
  | nil => exact hg
  | cons q l ih => exact (hCalc.2.1 ι U hU _ ih).1 q
include hCalc in
lemma iteratedPartialDerivList_perm {U : Set (ι → ℂ)} (hU : IsOpen U) {g : (ι → ℂ) → ℂ}
    (hg : IsHolomorphicOnOpen U g) {l l' : List ι} (hp : l.Perm l') :
    EqOn (iteratedPartialDerivList l g) (iteratedPartialDerivList l' g) U := by
  induction hp with
  | nil => exact fun _ _ => rfl
  | cons q _ ih => exact partialDeriv_congr_on hU ih q
  | swap q q' l =>
    intro c hc
    exact (hCalc.2.1 ι U hU _ (iteratedPartialDerivList_holomorphic hCalc hU hg l)).2 q' q c hc
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
include hSmooth in
lemma differentiableOn_of_isHolomorphicOnOpen {U : Set (ι → ℂ)} {g : (ι → ℂ) → ℂ}
    (hg : IsHolomorphicOnOpen U g) : DifferentiableOn ℂ g U :=
  (hSmooth ι U g hg).differentiableOn (by simp)
lemma hasDerivAt_add_smul (c v : ι → ℂ) : HasDerivAt (fun ζ : ℂ => c + ζ • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add c
lemma hasDerivAt_comp_add_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {G : (ι → ℂ) → F} {c : ι → ℂ} (hd : DifferentiableAt ℂ G c) (v : ι → ℂ) :
    HasDerivAt (fun ζ : ℂ => G (c + ζ • v)) (fderiv ℂ G c v) 0 := by
  have hc0 : HasFDerivAt G (fderiv ℂ G c) (c + (0 : ℂ) • v) := by simpa using hd.hasFDerivAt
  exact hc0.comp_hasDerivAt 0 (hasDerivAt_add_smul c v)
lemma iteratedFDeriv_basis_eq_iteratedPartialDerivList {U : Set (ι → ℂ)} (hU : IsOpen U)
    {g : (ι → ℂ) → ℂ} (hg : ContDiffOn ℂ ∞ g U) (n : ℕ) (e : Fin n → ι) :
    ∀ c ∈ U, iteratedFDeriv ℂ n g c (fun i => basisVector (e i)) =
      iteratedPartialDerivList (List.ofFn e) g c := by
  induction n with
  | zero =>
    intro c hc
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro c hc
    have hat : ContDiffAt ℂ ∞ g c := hg.contDiffAt (hU.mem_nhds hc)
    have hG : ContDiffAt ℂ 1 (iteratedFDeriv ℂ n g) c :=
      hat.iteratedFDeriv_right (by exact_mod_cast le_top)
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ n g) c := hG.differentiableAt (by simp)
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ, iteratedPartialDerivList_cons]
    have hcongr := partialDeriv_congr_on hU
      (g := iteratedPartialDerivList (List.ofFn fun i => e i.succ) g)
      (g' := fun y => iteratedFDeriv ℂ n g y (fun i => basisVector (e i.succ)))
      (fun y hy => (ih (fun i => e i.succ) y hy).symm) (e 0)
    rw [hcongr hc]
    have hline := hasDerivAt_comp_add_smul hd (basisVector (e 0))
    have happ := ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => ι → ℂ) ℂ
      (fun i => basisVector (e i.succ))).hasFDerivAt
        (x := iteratedFDeriv ℂ n g (c + (0 : ℂ) • basisVector (e 0)))).comp_hasDerivAt
        (0 : ℂ) hline
    exact happ.deriv.symm
lemma eq_zero_of_cexp_eq_one_of_isPreconnected {E : Type*} [TopologicalSpace E] {S : Set E}
    (hS : IsPreconnected S) {u : E → ℂ} (hu : ContinuousOn u S)
    (h1 : ∀ x ∈ S, Complex.exp (u x) = 1) {x₀ : E}
    (hx₀ : x₀ ∈ S) (h0 : u x₀ = 0) : ∀ x ∈ S, u x = 0 := by
  have hint : ∀ x ∈ S, ∃ k : ℤ, u x = k * (2 * Real.pi * Complex.I) := fun x hx =>
    Complex.exp_eq_one_iff.1 (h1 x hx)
  let v : E → ℝ := fun x => (u x).im / (2 * Real.pi)
  have hv : ContinuousOn v S := (Complex.continuous_im.comp_continuousOn hu).div_const _
  have hvk : ∀ x ∈ S, ∃ k : ℤ, v x = k ∧ u x = k * (2 * Real.pi * Complex.I) := by
    intro x hx
    obtain ⟨k, hk⟩ := hint x hx
    refine ⟨k, ?_, hk⟩
    simp only [v, hk]
    simp
  have hv0 : v x₀ = 0 := by simp [v, h0]
  intro x hx
  obtain ⟨k, hk, hux⟩ := hvk x hx
  by_cases hk0 : k = 0
  · simp [hux, hk0]
  exfalso
  rcases lt_or_gt_of_ne hk0 with hneg | hpos
  · have hmem : (-(1 / 2) : ℝ) ∈ Icc (v x) (v x₀) := by
      have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      rw [hk, hv0]
      constructor <;> linarith
    obtain ⟨y, hy, hyv⟩ := hS.intermediate_value hx hx₀ hv hmem
    obtain ⟨k', hk', -⟩ := hvk y hy
    have : (2 * k' : ℝ) = -1 := by rw [← hk', hyv]; ring
    have h2 : 2 * k' = -1 := by exact_mod_cast this
    omega
  · have hmem : ((1 / 2) : ℝ) ∈ Icc (v x₀) (v x) := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      rw [hk, hv0]
      constructor <;> linarith
    obtain ⟨y, hy, hyv⟩ := hS.intermediate_value hx₀ hx hv hmem
    obtain ⟨k', hk', -⟩ := hvk y hy
    have : (2 * k' : ℝ) = 1 := by rw [← hk', hyv]; ring
    have h2 : 2 * k' = 1 := by exact_mod_cast this
    omega
lemma polydisc_eq_ball (c₀ : ι → ℂ) {δ : ℝ} (hδ : 0 < δ) : polydisc c₀ δ = Metric.ball c₀ δ := by
  ext c
  rw [Metric.mem_ball, dist_pi_lt_iff hδ]
  simp [polydisc, dist_eq_norm]
end Calculus
section LocalLog
variable {L m J : ℕ} [Fintype (Plaquette L m (J : ℤ))] [Nonempty (Plaquette L m (J : ℤ))]
  (hCalc : SeveralComplexVariables.HolomorphicCalculus.Statement)
  (hSmooth : SeveralComplexVariables.HolomorphicContDiff.Statement)
  (hZdiff : Differentiable ℂ (latticeGaugeIntegral : (Plaquette L m (J : ℤ) → ℂ) → ℂ))
lemma polydisc_subset_nonvanishing {c₀ : Plaquette L m (J : ℤ) → ℂ} {δ : ℝ}
    (hδ : IsAdmissibleRadius c₀ δ) : polydisc c₀ δ ⊆ partitionFunctionNonvanishing L m (J : ℤ) := by
  intro c hc h0
  have := hδ.2 c hc
  simp only [disc, mem_ofPred_eq] at this
  rw [show latticeGaugeIntegral c = 0 from h0] at this
  simp at this
lemma self_mem_polydisc {c₀ : Plaquette L m (J : ℤ) → ℂ} {δ : ℝ} (hδ : 0 < δ) :
    c₀ ∈ polydisc c₀ δ := fun q => by simpa using hδ
lemma isOpen_polydisc (c₀ : Plaquette L m (J : ℤ) → ℂ) {δ : ℝ} (hδ : 0 < δ) :
    IsOpen (polydisc c₀ δ) := by
  rw [polydisc_eq_ball c₀ hδ]
  exact Metric.isOpen_ball
include hZdiff in
lemma exists_admissibleRadius_le {c₀ : Plaquette L m (J : ℤ) → ℂ}
    (hc₀ : c₀ ∈ partitionFunctionNonvanishing L m (J : ℤ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, δ ≤ ε ∧ IsAdmissibleRadius c₀ δ := by
  have hcont : ContinuousAt (fun c : Plaquette L m (J : ℤ) → ℂ =>
      latticeGaugeIntegral c / latticeGaugeIntegral c₀) c₀ :=
    (hZdiff.continuous.continuousAt).div_const _
  obtain ⟨δ', hδ', hball⟩ := Metric.continuousAt_iff.1 hcont 1 one_pos
  refine ⟨min δ' ε, min_le_right _ _, lt_min hδ' hε, fun c hc => ?_⟩
  have hcb : c ∈ Metric.ball c₀ (min δ' ε) := by
    rwa [← polydisc_eq_ball c₀ (lt_min hδ' hε)]
  have := hball (lt_of_lt_of_le hcb (min_le_left _ _))
  rw [div_self hc₀, dist_eq_norm] at this
  exact this
include hCalc hZdiff in
lemma localLog_differentiableOn {c₀ : Plaquette L m (J : ℤ) → ℂ} {δ : ℝ}
    (hδ : IsAdmissibleRadius c₀ δ) : DifferentiableOn ℂ (localLog c₀) (polydisc c₀ δ) := by
  have hlog := hCalc.2.2.2.2.2.2.1
  have hq : DifferentiableOn ℂ (fun c => latticeGaugeIntegral c / latticeGaugeIntegral c₀)
      (polydisc c₀ δ) :=
    fun c _ => by
      simp only [div_eq_mul_inv]
      exact ((hZdiff c).mul_const _).differentiableWithinAt
  exact hlog.comp hq hδ.2
include hCalc in
lemma cexp_localLog {c₀ : Plaquette L m (J : ℤ) → ℂ} {δ : ℝ}
    (hδ : IsAdmissibleRadius c₀ δ) {c : Plaquette L m (J : ℤ) → ℂ} (hc : c ∈ polydisc c₀ δ) :
    Complex.exp (localLog c₀ c) = latticeGaugeIntegral c / latticeGaugeIntegral c₀ :=
  hCalc.2.2.2.2.2.2.2.2.1 _ (hδ.2 c hc)
include hCalc in
lemma localLog_self {c₀ : Plaquette L m (J : ℤ) → ℂ}
    (hc₀ : c₀ ∈ partitionFunctionNonvanishing L m (J : ℤ)) : localLog c₀ c₀ = 0 := by
  have h1 : latticeGaugeIntegral c₀ / latticeGaugeIntegral c₀ = 1 := div_self hc₀
  simp only [localLog, h1]
  exact hCalc.2.2.2.2.2.2.2.2.2.1
include hCalc hZdiff in
lemma partialDeriv_localLog {c₀ : Plaquette L m (J : ℤ) → ℂ} {δ : ℝ}
    (hc₀ : c₀ ∈ partitionFunctionNonvanishing L m (J : ℤ)) (hδ : IsAdmissibleRadius c₀ δ)
    (p : Plaquette L m (J : ℤ)) {c : Plaquette L m (J : ℤ) → ℂ} (hc : c ∈ polydisc c₀ δ) :
    partialDeriv p (localLog c₀) c =
      partialDeriv p latticeGaugeIntegral c / latticeGaugeIntegral c := by
  have hopen := isOpen_polydisc c₀ hδ.1
  have hd : DifferentiableAt ℂ (localLog c₀) c :=
    (localLog_differentiableOn hCalc hZdiff hδ).differentiableAt (hopen.mem_nhds hc)
  have hL := hasDerivAt_comp_add_smul hd (basisVector p)
  have hZl := hasDerivAt_comp_add_smul (hZdiff c) (basisVector p)
  have hLp : partialDeriv p (localLog c₀) c = fderiv ℂ (localLog c₀) c (basisVector p) :=
    hL.deriv
  have hZp : partialDeriv p latticeGaugeIntegral c =
      fderiv ℂ latticeGaugeIntegral c (basisVector p) :=
    hZl.deriv
  rw [hLp, hZp]
  have hexp := hL.cexp
  have hquot := hZl.div_const (latticeGaugeIntegral c₀)
  have heq : (fun ζ : ℂ => Complex.exp (localLog c₀ (c + ζ • basisVector p))) =ᶠ[𝓝 0]
      fun ζ => latticeGaugeIntegral (c + ζ • basisVector p) / latticeGaugeIntegral c₀ := by
    filter_upwards [eventually_add_smul_mem hopen hc (basisVector p)] with ζ hζ
    exact cexp_localLog hCalc hδ hζ
  have huniq := (hexp.congr_of_eventuallyEq heq.symm).unique hquot
  simp only [zero_smul, add_zero] at huniq
  rw [cexp_localLog hCalc hδ hc] at huniq
  have hcne : latticeGaugeIntegral c ≠ 0 := polydisc_subset_nonvanishing hδ hc
  have hc₀ne : latticeGaugeIntegral c₀ ≠ 0 := hc₀
  field_simp at huniq ⊢
  linear_combination huniq
lemma logDerivativeKernel_zero (p : Fin 1 → Plaquette L m (J : ℤ)) (c : Plaquette L m (J : ℤ) → ℂ) :
    logDerivativeKernel 0 p c = -partialDeriv (p 0) latticeGaugeIntegral c / latticeGaugeIntegral c :=
  rfl
lemma logDerivativeKernel_succ (n : ℕ) (p : Fin (n + 2) → Plaquette L m (J : ℤ))
    (c : Plaquette L m (J : ℤ) → ℂ) :
    logDerivativeKernel (n + 1) p c =
      -partialDeriv (p (Fin.last (n + 1))) (logDerivativeKernel n (Fin.init p)) c := rfl
lemma partialDeriv_const_mul {ι : Type} (a : ℂ) (g : (ι → ℂ) → ℂ) (q : ι) (c : ι → ℂ) :
    partialDeriv q (fun y => a * g y) c = a * partialDeriv q g c := by
  simp [partialDeriv, deriv_const_mul_field]
include hCalc hZdiff in
lemma logDerivativeKernel_eq_reverse {c₀ : Plaquette L m (J : ℤ) → ℂ} {δ : ℝ}
    (hc₀ : c₀ ∈ partitionFunctionNonvanishing L m (J : ℤ)) (hδ : IsAdmissibleRadius c₀ δ) (n : ℕ)
    (p : Fin (n + 1) → Plaquette L m (J : ℤ)) :
    EqOn (fun c => (-1 : ℂ) ^ (n + 1) *
        iteratedPartialDerivList (List.ofFn p).reverse (localLog c₀) c)
      (logDerivativeKernel n p) (polydisc c₀ δ) := by
  have hopen := isOpen_polydisc c₀ hδ.1
  induction n with
  | zero =>
    intro c hc
    have := partialDeriv_localLog hCalc hZdiff hc₀ hδ (p 0) hc
    simp only [List.ofFn_succ, List.ofFn_zero, List.reverse_singleton, iteratedPartialDerivList_cons,
      iteratedPartialDerivList_nil, logDerivativeKernel_zero, this]
    ring
  | succ n ih =>
    intro c hc
    have hrev : (List.ofFn p).reverse =
        p (Fin.last (n + 1)) :: (List.ofFn (Fin.init p)).reverse := by
      rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
      rfl
    rw [logDerivativeKernel_succ, hrev, iteratedPartialDerivList_cons]
    have h := partialDeriv_congr_on hopen (ih (Fin.init p)) (p (Fin.last (n + 1))) hc
    rw [← h, partialDeriv_const_mul]
    ring
include hCalc hSmooth hZdiff in
lemma localLog_holomorphic {c₀ : Plaquette L m (J : ℤ) → ℂ} {δ : ℝ}
    (hδ : IsAdmissibleRadius c₀ δ) : IsHolomorphicOnOpen (polydisc c₀ δ) (localLog c₀) :=
  isHolomorphicOnOpen_of_differentiableOn (isOpen_polydisc c₀ hδ.1)
    (localLog_differentiableOn hCalc hZdiff hδ)
include hCalc hSmooth hZdiff in
lemma logDerivativeKernel_eq_iteratedPartialDeriv {c₀ : Plaquette L m (J : ℤ) → ℂ} {δ : ℝ}
    (hc₀ : c₀ ∈ partitionFunctionNonvanishing L m (J : ℤ)) (hδ : IsAdmissibleRadius c₀ δ) (n : ℕ)
    (p : Fin (n + 1) → Plaquette L m (J : ℤ)) {c : Plaquette L m (J : ℤ) → ℂ}
    (hc : c ∈ polydisc c₀ δ) :
    (-1 : ℂ) ^ (n + 1) * iteratedPartialDerivAlong p (localLog c₀) c =
      logDerivativeKernel n p c := by
  have hperm := iteratedPartialDerivList_perm hCalc (isOpen_polydisc c₀ hδ.1)
    (localLog_holomorphic hCalc hSmooth hZdiff hδ) (List.reverse_perm (List.ofFn p)) hc
  rw [← logDerivativeKernel_eq_reverse hCalc hZdiff hc₀ hδ n p hc]
  show _ * iteratedPartialDerivList (List.ofFn p) _ c = _
  simp only [hperm]
include hCalc hZdiff in
lemma continuousLog_eq_const_add_localLog {U : Set (Plaquette L m (J : ℤ) → ℂ)}
    {h : (Plaquette L m (J : ℤ) → ℂ) → ℂ} (hU : IsOpen U) (hh : ContinuousOn h U)
    (hexp : ∀ c ∈ U, Complex.exp (h c) = latticeGaugeIntegral c) {c₀ : Plaquette L m (J : ℤ) → ℂ}
    (hc₀ : c₀ ∈ U) : ∃ δ, IsAdmissibleRadius c₀ δ ∧ polydisc c₀ δ ⊆ U ∧
      EqOn h (fun c => h c₀ + localLog c₀ c) (polydisc c₀ δ) := by
  have hne : c₀ ∈ partitionFunctionNonvanishing L m (J : ℤ) := by
    intro h0
    exact Complex.exp_ne_zero _ ((hexp c₀ hc₀).trans h0)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU c₀ hc₀
  obtain ⟨δ, hδε, hδ⟩ := exists_admissibleRadius_le hZdiff hne hε
  have hsub : polydisc c₀ δ ⊆ U := by
    rw [polydisc_eq_ball c₀ hδ.1]
    exact (Metric.ball_subset_ball hδε).trans hball
  refine ⟨δ, hδ, hsub, fun c hc => ?_⟩
  have hconv : IsPreconnected (polydisc c₀ δ) := by
    rw [polydisc_eq_ball c₀ hδ.1]
    exact (convex_ball c₀ δ).isPreconnected
  have hu : ContinuousOn (fun c => h c - h c₀ - localLog c₀ c) (polydisc c₀ δ) :=
    ((hh.mono hsub).sub continuousOn_const).sub
      (localLog_differentiableOn hCalc hZdiff hδ).continuousOn
  have h1 : ∀ c ∈ polydisc c₀ δ,
      Complex.exp (h c - h c₀ - localLog c₀ c) = 1 := by
    intro c hc
    have hcne : latticeGaugeIntegral c ≠ 0 := polydisc_subset_nonvanishing hδ hc
    have hc₀ne : latticeGaugeIntegral c₀ ≠ 0 := hne
    rw [Complex.exp_sub, Complex.exp_sub, cexp_localLog hCalc hδ hc, hexp c (hsub hc),
      hexp c₀ hc₀]
    field_simp
  have h0 := eq_zero_of_cexp_eq_one_of_isPreconnected hconv hu h1 (self_mem_polydisc hδ.1)
    (by simp [localLog_self hCalc hne]) c hc
  simp only at h0 ⊢
  linear_combination h0
include hCalc hSmooth hZdiff in
lemma logarithmBranchIndependence_holds : LogarithmBranchIndependence L m J := by
  refine ⟨fun U h hU hh hexp => ?_, fun c₀ δ hc₀ hδ => ?_⟩
  · have hsub : U ⊆ partitionFunctionNonvanishing L m (J : ℤ) := fun c hc h0 =>
      Complex.exp_ne_zero _ ((hexp c hc).trans h0)
    refine ⟨hsub, ?_, fun n p c hc => ?_⟩
    · refine isHolomorphicOnOpen_of_differentiableOn hU fun c hc => ?_
      obtain ⟨δ, hδ, hs, heq⟩ := continuousLog_eq_const_add_localLog hCalc hZdiff hU hh hexp hc
      have hopen := isOpen_polydisc c hδ.1
      have hmem := hopen.mem_nhds (self_mem_polydisc (c₀ := c) hδ.1)
      have hd : DifferentiableAt ℂ (fun y => h c + localLog c y) c :=
        (((localLog_differentiableOn hCalc hZdiff hδ).differentiableAt hmem).const_add _)
      exact (hd.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem hmem heq)).differentiableWithinAt
    · obtain ⟨δ, hδ, hs, heq⟩ := continuousLog_eq_const_add_localLog hCalc hZdiff hU hh hexp hc
      have hopen := isOpen_polydisc c hδ.1
      have hmem := self_mem_polydisc (c₀ := c) hδ.1
      have h1 := iteratedPartialDerivList_congr_on hopen heq (List.ofFn p) hmem
      have hne : List.ofFn p ≠ [] := by simp
      rw [iteratedPartialDerivList_const_add _ _ hne] at h1
      rw [← logDerivativeKernel_eq_iteratedPartialDeriv hCalc hSmooth hZdiff (hsub hc) hδ n p hmem]
      show _ * iteratedPartialDerivList (List.ofFn p) h c =
        _ * iteratedPartialDerivList (List.ofFn p) _ c
      rw [h1]
  · refine ⟨polydisc_subset_nonvanishing hδ, localLog_holomorphic hCalc hSmooth hZdiff hδ,
      fun n p c hc => logDerivativeKernel_eq_iteratedPartialDeriv hCalc hSmooth hZdiff hc₀ hδ n p hc⟩
end LocalLog
section Kernels
variable {L m J : ℕ} [Fintype (Plaquette L m (J : ℤ))] [Nonempty (Plaquette L m (J : ℤ))]
  (hCalc : SeveralComplexVariables.HolomorphicCalculus.Statement)
  (hSmooth : SeveralComplexVariables.HolomorphicContDiff.Statement)
  (hZdiff : Differentiable ℂ (latticeGaugeIntegral : (Plaquette L m (J : ℤ) → ℂ) → ℂ))
  (hopen : IsOpen (partitionFunctionNonvanishing L m (J : ℤ)))
include hCalc hSmooth hZdiff hopen in
lemma logDerivativeKernel_holomorphic (n : ℕ) (p : Fin (n + 1) → Plaquette L m (J : ℤ)) :
    IsHolomorphicOnOpen (partitionFunctionNonvanishing L m (J : ℤ)) (logDerivativeKernel n p) := by
  have hZh : IsHolomorphicOnOpen (partitionFunctionNonvanishing L m (J : ℤ)) latticeGaugeIntegral :=
    isHolomorphicOnOpen_of_differentiableOn hopen hZdiff.differentiableOn
  induction n with
  | zero =>
    have h1 := differentiableOn_of_isHolomorphicOnOpen hSmooth ((hCalc.2.1 _ _ hopen _ hZh).1 (p 0))
    have h2 : DifferentiableOn ℂ (fun c => -partialDeriv (p 0) latticeGaugeIntegral c *
        (latticeGaugeIntegral c)⁻¹) (partitionFunctionNonvanishing L m (J : ℤ)) :=
      h1.neg.mul (hZdiff.differentiableOn.inv fun c hc => hc)
    refine isHolomorphicOnOpen_of_differentiableOn hopen (h2.congr fun c _ => ?_)
    rw [logDerivativeKernel_zero, div_eq_mul_inv]
  | succ n ih =>
    have h1 := differentiableOn_of_isHolomorphicOnOpen hSmooth
      ((hCalc.2.1 _ _ hopen _ (ih (Fin.init p))).1 (p (Fin.last (n + 1))))
    exact isHolomorphicOnOpen_of_differentiableOn hopen h1.neg
include hCalc hSmooth hZdiff in
lemma logDerivativeKernel_comp_perm (n : ℕ) (p : Fin (n + 1) → Plaquette L m (J : ℤ))
    (σ : Equiv.Perm (Fin (n + 1))) {c : Plaquette L m (J : ℤ) → ℂ}
    (hc : c ∈ partitionFunctionNonvanishing L m (J : ℤ)) :
    logDerivativeKernel n (p ∘ σ) c = logDerivativeKernel n p c := by
  obtain ⟨δ, -, hδ⟩ := exists_admissibleRadius_le hZdiff hc one_pos
  have hmem := self_mem_polydisc (c₀ := c) hδ.1
  rw [← logDerivativeKernel_eq_iteratedPartialDeriv hCalc hSmooth hZdiff hc hδ n p hmem,
    ← logDerivativeKernel_eq_iteratedPartialDeriv hCalc hSmooth hZdiff hc hδ n (p ∘ σ) hmem]
  have hperm := iteratedPartialDerivList_perm hCalc (isOpen_polydisc c hδ.1)
    (localLog_holomorphic hCalc hSmooth hZdiff hδ) (Equiv.Perm.ofFn_comp_perm σ p) hmem
  show _ * iteratedPartialDerivList (List.ofFn (p ∘ σ)) _ c =
    _ * iteratedPartialDerivList (List.ofFn p) _ c
  rw [hperm]
include hCalc hSmooth hZdiff hopen in
lemma logDerivativeKernel_im_eq_zero
    (hreal : ∀ c ∈ partitionFunctionNonvanishing L m (J : ℤ) ∩
      realPoints (Plaquette L m (J : ℤ)), (latticeGaugeIntegral c).im = 0)
    (n : ℕ) (p : Fin (n + 1) → Plaquette L m (J : ℤ)) :
    ∀ c ∈ partitionFunctionNonvanishing L m (J : ℤ) ∩ realPoints (Plaquette L m (J : ℤ)),
      (logDerivativeKernel n p c).im = 0 := by
  have hZh : IsHolomorphicOnOpen (partitionFunctionNonvanishing L m (J : ℤ)) latticeGaugeIntegral :=
    isHolomorphicOnOpen_of_differentiableOn hopen hZdiff.differentiableOn
  induction n with
  | zero =>
    intro c hc
    have h1 := hCalc.2.2.2.2.2.1 _ _ hopen _ hZh hreal (p 0) c hc
    have h2 := hreal c hc
    rw [logDerivativeKernel_zero]
    simp [Complex.div_im, h1, h2]
  | succ n ih =>
    intro c hc
    have h1 := hCalc.2.2.2.2.2.1 _ _ hopen _
      (logDerivativeKernel_holomorphic hCalc hSmooth hZdiff hopen n (Fin.init p))
      (ih (Fin.init p)) (p (Fin.last (n + 1))) c hc
    rw [logDerivativeKernel_succ]
    simp [h1]
end Kernels
section Bounded
variable {L m : ℕ}
lemma torusSupNorm_ne_top_iff {E : Type*} [NormedAddCommGroup E] (g : FourTorus L m → E) :
    torusSupNorm g ≠ ⊤ ↔ ∃ C : ℝ, ∀ y, ‖g y‖ ≤ C := by
  constructor
  · intro h
    refine ⟨(torusSupNorm g).toReal, fun y => ?_⟩
    exact (ENNReal.ofReal_le_iff_le_toReal h).1 (le_iSup (fun y => ENNReal.ofReal ‖g y‖) y)
  · rintro ⟨C, hC⟩
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C)) ?_
    exact iSup_le fun y => ENNReal.ofReal_le_ofReal (hC y)
lemma weightedSource_supNorm_ne_top {N : ℕ} {f : Fin N → FourTorus L m → ℝ}
    (hf : ∀ i, IsBoundedOnTorus (f i)) (z : Fin N → ℂ) : torusSupNorm (weightedSource f z) ≠ ⊤ := by
  choose C hC using fun i => (torusSupNorm_ne_top_iff (f i)).1 (hf i)
  refine (torusSupNorm_ne_top_iff _).2 ⟨∑ i, ‖z i‖ * C i, fun y => ?_⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  have : ‖((f i y : ℝ) : ℂ)‖ ≤ C i := by simpa using hC i y
  exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
end Bounded
section Sources
variable {L m J : ℕ} [Fintype (Plaquette L m (J : ℤ))] [Nonempty (Plaquette L m (J : ℤ))]
def couplingVector (β : ℂ) {N : ℕ} (f : Fin N → FourTorus L m → ℝ) (z : Fin N → ℂ) :
    Plaquette L m (J : ℤ) → ℂ :=
  fun q => β - ∑ i, z i * (f i q.barycenter : ℂ)
lemma couplingVector_eq (β : ℂ) {N : ℕ} (f : Fin N → FourTorus L m → ℝ) (z : Fin N → ℂ) :
    (β • constantOneWeights - weightsAtBarycenters (weightedSource f z) :
      Plaquette L m (J : ℤ) → ℂ) = couplingVector β f z := by
  funext q
  simp [couplingVector, constantOneWeights, weightsAtBarycenters, weightedSource]
lemma couplingVector_zero (β : ℂ) {N : ℕ} (f : Fin N → FourTorus L m → ℝ) :
    (couplingVector β f 0 : Plaquette L m (J : ℤ) → ℂ) = β • constantOneWeights := by
  funext q
  simp [couplingVector, constantOneWeights]
lemma couplingVector_differentiable (β : ℂ) {N : ℕ} (f : Fin N → FourTorus L m → ℝ) :
    Differentiable ℂ (couplingVector β f : (Fin N → ℂ) → Plaquette L m (J : ℤ) → ℂ) := by
  refine differentiable_pi.2 fun q => ?_
  unfold couplingVector
  fun_prop
lemma partialDeriv_couplingVector (β : ℂ) {N : ℕ} (f : Fin N → FourTorus L m → ℝ) (i : Fin N)
    (q : Plaquette L m (J : ℤ)) (z : Fin N → ℂ) :
    partialDeriv i (fun z' => (couplingVector β f z' : Plaquette L m (J : ℤ) → ℂ) q) z =
      -(f i q.barycenter : ℂ) := by
  have hform : (fun ζ : ℂ => (couplingVector β f (z + ζ • basisVector i) :
      Plaquette L m (J : ℤ) → ℂ) q) =
      fun ζ => (β - ∑ k, z k * (f k q.barycenter : ℂ)) - ζ * (f i q.barycenter : ℂ) := by
    funext ζ
    simp only [couplingVector, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, basisVector]
    simp [sub_sub]
  have hd : HasDerivAt (fun ζ : ℂ => (β - ∑ k, z k * (f k q.barycenter : ℂ)) -
      ζ * (f i q.barycenter : ℂ)) (-(f i q.barycenter : ℂ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (f i q.barycenter : ℂ)).const_sub
      (β - ∑ k, z k * (f k q.barycenter : ℂ))
  unfold partialDeriv
  rw [hform]
  exact hd.deriv
def barycenterDerivOperator (g : FourTorus L m → ℝ) (F : (Plaquette L m (J : ℤ) → ℂ) → ℂ) :
    (Plaquette L m (J : ℤ) → ℂ) → ℂ :=
  fun c => -∑ q, (g q.barycenter : ℂ) * partialDeriv q F c
def barycenterDerivOperatorList {N : ℕ} (f : Fin N → FourTorus L m → ℝ) (l : List (Fin N))
    (F : (Plaquette L m (J : ℤ) → ℂ) → ℂ) : (Plaquette L m (J : ℤ) → ℂ) → ℂ :=
  l.foldr (fun i G => barycenterDerivOperator (f i) G) F
variable (hCalc : SeveralComplexVariables.HolomorphicCalculus.Statement)
  (hSmooth : SeveralComplexVariables.HolomorphicContDiff.Statement)
lemma barycenterDerivOperator_congr_on {V : Set (Plaquette L m (J : ℤ) → ℂ)} (hV : IsOpen V)
    {G G' : (Plaquette L m (J : ℤ) → ℂ) → ℂ} (hG : EqOn G G' V) (g : FourTorus L m → ℝ) :
    EqOn (barycenterDerivOperator g G) (barycenterDerivOperator g G') V := by
  intro c hc
  simp only [barycenterDerivOperator]
  congr 1
  exact Finset.sum_congr rfl fun q _ => by rw [partialDeriv_congr_on hV hG q hc]
include hCalc hSmooth in
lemma barycenterDerivOperator_holomorphic {V : Set (Plaquette L m (J : ℤ) → ℂ)} (hV : IsOpen V)
    {G : (Plaquette L m (J : ℤ) → ℂ) → ℂ} (hG : IsHolomorphicOnOpen V G) (g : FourTorus L m → ℝ) :
    IsHolomorphicOnOpen V (barycenterDerivOperator g G) := by
  refine isHolomorphicOnOpen_of_differentiableOn hV ?_
  have hd : ∀ q : Plaquette L m (J : ℤ), DifferentiableOn ℂ
      (fun c => (g q.barycenter : ℂ) * partialDeriv q G c) V := fun q =>
    (differentiableOn_of_isHolomorphicOnOpen hSmooth ((hCalc.2.1 _ _ hV _ hG).1 q)).const_mul _
  exact (DifferentiableOn.fun_sum fun q _ => hd q).neg
include hCalc hSmooth in
lemma barycenterDerivOperatorList_holomorphic {N : ℕ} (f : Fin N → FourTorus L m → ℝ)
    {V : Set (Plaquette L m (J : ℤ) → ℂ)} (hV : IsOpen V)
    {F : (Plaquette L m (J : ℤ) → ℂ) → ℂ} (hF : IsHolomorphicOnOpen V F) (l : List (Fin N)) :
    IsHolomorphicOnOpen V (barycenterDerivOperatorList f l F) := by
  induction l with
  | nil => exact hF
  | cons i l ih => exact barycenterDerivOperator_holomorphic hCalc hSmooth hV ih (f i)
include hCalc in
lemma comp_couplingVector_chain {N : ℕ} [NeZero N] (β : ℂ) (f : Fin N → FourTorus L m → ℝ)
    {V : Set (Plaquette L m (J : ℤ) → ℂ)} (hV : IsOpen V)
    {F : (Plaquette L m (J : ℤ) → ℂ) → ℂ} (hF : IsHolomorphicOnOpen V F) :
    IsHolomorphicOnOpen (couplingVector β f ⁻¹' V) (fun z => F (couplingVector β f z)) ∧
      ∀ z ∈ couplingVector β f ⁻¹' V, ∀ i,
        partialDeriv i (fun z' => F (couplingVector β f z')) z =
          barycenterDerivOperator (f i) F (couplingVector β f z) := by
  have hcont := (couplingVector_differentiable (J := J) β f).continuous
  have hW : IsOpen (couplingVector β f ⁻¹' V) := hV.preimage hcont
  have hv : IsHolomorphicOnOpen (couplingVector β f ⁻¹' V)
      (couplingVector β f : (Fin N → ℂ) → Plaquette L m (J : ℤ) → ℂ) :=
    isHolomorphicOnOpen_of_differentiableOn hW (couplingVector_differentiable β f).differentiableOn
  have hchain := hCalc.2.2.2.2.1 (Fin N) _ hW (Plaquette L m (J : ℤ)) V hV _ F hv
    (fun z hz => hz) hF
  refine ⟨hchain.1, fun z hz i => ?_⟩
  rw [hchain.2 z hz i]
  simp only [partialDeriv_couplingVector, barycenterDerivOperator]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring
include hCalc hSmooth in
lemma iteratedPartialDerivList_comp_couplingVector {N : ℕ} [NeZero N] (β : ℂ)
    (f : Fin N → FourTorus L m → ℝ)
    {V : Set (Plaquette L m (J : ℤ) → ℂ)} (hV : IsOpen V)
    {F : (Plaquette L m (J : ℤ) → ℂ) → ℂ} (hF : IsHolomorphicOnOpen V F) (l : List (Fin N)) :
    EqOn (iteratedPartialDerivList l fun z => F (couplingVector β f z))
      (fun z => barycenterDerivOperatorList f l F (couplingVector β f z))
      (couplingVector β f ⁻¹' V) := by
  have hW : IsOpen (couplingVector β f ⁻¹' V) :=
    hV.preimage (couplingVector_differentiable (J := J) β f).continuous
  induction l with
  | nil => exact fun _ _ => rfl
  | cons i l ih =>
    intro z hz
    have h1 := partialDeriv_congr_on hW ih i hz
    rw [iteratedPartialDerivList_cons, h1]
    exact (comp_couplingVector_chain hCalc β f hV
      (barycenterDerivOperatorList_holomorphic hCalc hSmooth f hV hF l)).2 z hz i
end Sources
section Sums
variable {L m J : ℕ} [Fintype (Plaquette L m (J : ℤ))] [Nonempty (Plaquette L m (J : ℤ))]
  (hCalc : SeveralComplexVariables.HolomorphicCalculus.Statement)
  (hSmooth : SeveralComplexVariables.HolomorphicContDiff.Statement)
  (hZdiff : Differentiable ℂ (latticeGaugeIntegral : (Plaquette L m (J : ℤ) → ℂ) → ℂ))
  (hopen : IsOpen (partitionFunctionNonvanishing L m (J : ℤ)))
  (hZ : ∀ (β : ℂ) (w : FourTorus L m → ℂ), torusSupNorm w ≠ ⊤ →
    sourcedPartitionFunction L m J β w =
      latticeGaugeIntegral (β • constantOneWeights - weightsAtBarycenters w :
        Plaquette L m (J : ℤ) → ℂ))
def weightedKernelSum {k : ℕ} (g : Fin (k + 1) → FourTorus L m → ℝ)
    (c : Plaquette L m (J : ℤ) → ℂ) : ℂ :=
  ∑ p : Fin (k + 1) → Plaquette L m (J : ℤ),
    logDerivativeKernel k p c * ∏ i, (g i (p i).barycenter : ℂ)
include hCalc hSmooth hZdiff hopen in
lemma partialDeriv_weightedKernelSum {k : ℕ} (g : Fin (k + 1) → FourTorus L m → ℝ)
    (q : Plaquette L m (J : ℤ)) {c : Plaquette L m (J : ℤ) → ℂ}
    (hc : c ∈ partitionFunctionNonvanishing L m (J : ℤ)) :
    partialDeriv q (weightedKernelSum g) c =
      ∑ p : Fin (k + 1) → Plaquette L m (J : ℤ),
        partialDeriv q (logDerivativeKernel k p) c * ∏ i, (g i (p i).barycenter : ℂ) := by
  have hdiff : ∀ p : Fin (k + 1) → Plaquette L m (J : ℤ),
      DifferentiableAt ℂ (fun ζ : ℂ => logDerivativeKernel k p (c + ζ • basisVector q)) 0 :=
    fun p =>
    (hasDerivAt_comp_add_smul
      ((differentiableOn_of_isHolomorphicOnOpen hSmooth
        (logDerivativeKernel_holomorphic hCalc hSmooth hZdiff hopen k p)).differentiableAt
          (hopen.mem_nhds hc))
      (basisVector q)).differentiableAt
  unfold partialDeriv weightedKernelSum
  rw [deriv_fun_sum fun p _ => (hdiff p).mul_const _]
  exact Finset.sum_congr rfl fun p _ => deriv_mul_const (hdiff p) _
include hCalc hSmooth hZdiff hopen in
lemma barycenterDerivOperatorList_reverse {N : ℕ} (f : Fin N → FourTorus L m → ℝ)
    {c₀ : Plaquette L m (J : ℤ) → ℂ} {δ : ℝ}
    (hc₀ : c₀ ∈ partitionFunctionNonvanishing L m (J : ℤ)) (hδ : IsAdmissibleRadius c₀ δ) (k : ℕ)
    (e : Fin (k + 1) → Fin N) :
    EqOn (barycenterDerivOperatorList f (List.ofFn e).reverse (localLog c₀))
      (weightedKernelSum fun i => f (e i)) (polydisc c₀ δ) := by
  have hP := isOpen_polydisc c₀ hδ.1
  induction k with
  | zero =>
    intro c hc
    simp only [List.ofFn_succ, List.ofFn_zero, List.reverse_singleton]
    show barycenterDerivOperator (f (e 0)) (localLog c₀) c = _
    simp only [barycenterDerivOperator, weightedKernelSum]
    rw [← (Equiv.funUnique (Fin 1) (Plaquette L m (J : ℤ))).symm.sum_comp,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq : (Equiv.funUnique (Fin 1) (Plaquette L m (J : ℤ))).symm q = fun _ => q := by
      funext i
      simp
    rw [hq, partialDeriv_localLog hCalc hZdiff hc₀ hδ q hc, logDerivativeKernel_zero]
    simp only []
    rw [show (∏ x : Fin (0 + 1), ((f (e x) q.barycenter : ℝ) : ℂ)) = (f (e 0) q.barycenter : ℂ) from
      Fin.prod_univ_one _]
    ring
  | succ k ih =>
    intro c hc
    have hcne : c ∈ partitionFunctionNonvanishing L m (J : ℤ) := polydisc_subset_nonvanishing hδ hc
    have hrev : (List.ofFn e).reverse =
        e (Fin.last (k + 1)) :: (List.ofFn fun i : Fin (k + 1) => e i.castSucc).reverse := by
      rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
      rfl
    rw [hrev]
    show barycenterDerivOperator (f (e (Fin.last (k + 1)))) (barycenterDerivOperatorList f _ _) c = _
    rw [barycenterDerivOperator_congr_on hP (ih fun i => e i.castSucc) _ hc]
    simp only [barycenterDerivOperator]
    simp_rw [partialDeriv_weightedKernelSum hCalc hSmooth hZdiff hopen _ _ hcne]
    rw [weightedKernelSum, ← (Fin.snocEquiv fun _ => Plaquette L m (J : ℤ)).sum_comp,
      Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hs : (Fin.snocEquiv fun _ => Plaquette L m (J : ℤ)) (q, p) = Fin.snoc p q := rfl
    rw [hs, Fin.prod_univ_castSucc (n := k + 1), logDerivativeKernel_succ]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.init_snoc]
    ring
include hZ in
lemma sourcedPartitionFunction_weightedSource {N : ℕ} (β : ℂ) {f : Fin N → FourTorus L m → ℝ}
    (hf : ∀ i, IsBoundedOnTorus (f i)) (z : Fin N → ℂ) :
    sourcedPartitionFunction L m J β (weightedSource f z) =
      latticeGaugeIntegral (couplingVector β f z : Plaquette L m (J : ℤ) → ℂ) := by
  rw [hZ _ _ (weightedSource_supNorm_ne_top hf z), couplingVector_eq]
include hZ in
lemma sourcedPartitionFunction_zero (β : ℂ) :
    sourcedPartitionFunction L m J β 0 =
      latticeGaugeIntegral (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) := by
  rw [hZ _ _ ((torusSupNorm_ne_top_iff _).2 ⟨0, by simp⟩)]
  congr 1
  funext q
  simp [weightsAtBarycenters]
include hZ in
lemma connectedFunction_eq_iteratedPartialDerivList {n : ℕ} (β : ℂ)
    {f : Fin (n + 1) → FourTorus L m → ℝ} (hf : ∀ i, IsBoundedOnTorus (f i)) :
    connectedFunction L m J β f =
      iteratedPartialDerivList (List.finRange (n + 1))
        (fun z => localLog (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ)
          (couplingVector β f z)) 0 := by
  have : (fun z => SeveralComplexVariables.logSeries
      (sourcedPartitionFunction L m J β (weightedSource f z) /
        sourcedPartitionFunction L m J β 0)) =
      fun z => localLog (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ)
        (couplingVector β f z) := by
    funext z
    rw [sourcedPartitionFunction_weightedSource hZ β hf z, sourcedPartitionFunction_zero hZ β]
    rfl
  unfold connectedFunction
  rw [this]
  rfl
include hCalc hSmooth hZdiff hopen hZ in
lemma connectedFunction_eq_kernelPlaquetteSum {n : ℕ} {β : ℂ}
    (hβ : β ∈ nonvanishingCouplings L m J)
    {f : Fin (n + 1) → FourTorus L m → ℝ} (hf : ∀ i, IsBoundedOnTorus (f i)) :
    connectedFunction L m J β f = kernelPlaquetteSum L m J β f := by
  have hc₀ : (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) ∈
      partitionFunctionNonvanishing L m (J : ℤ) := by
    have : sourcedPartitionFunction L m J β 0 ≠ 0 := hβ
    rwa [sourcedPartitionFunction_zero hZ β] at this
  obtain ⟨δ, -, hδ⟩ := exists_admissibleRadius_le hZdiff hc₀ one_pos
  have hP := isOpen_polydisc (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) hδ.1
  have hL := localLog_holomorphic hCalc hSmooth hZdiff hδ
  have hchain := comp_couplingVector_chain hCalc β f hP hL
  have hv0 : (couplingVector β f 0 : Plaquette L m (J : ℤ) → ℂ) ∈ polydisc
      (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) δ := by
    rw [couplingVector_zero]
    exact self_mem_polydisc hδ.1
  have h0 : (0 : Fin (n + 1) → ℂ) ∈ couplingVector β f ⁻¹' polydisc
      (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) δ := hv0
  have hperm : (List.finRange (n + 1)).Perm (List.ofFn fun i : Fin (n + 1) => i).reverse := by
    show (List.finRange (n + 1)).Perm (List.ofFn id).reverse
    rw [List.ofFn_id]
    exact (List.reverse_perm _).symm
  rw [connectedFunction_eq_iteratedPartialDerivList hZ β hf,
    iteratedPartialDerivList_perm hCalc hchain.1.1 hchain.1 hperm h0,
    iteratedPartialDerivList_comp_couplingVector hCalc hSmooth β f hP hL _ h0]
  have := barycenterDerivOperatorList_reverse hCalc hSmooth hZdiff hopen f hc₀ hδ n (fun i => i) hv0
  simp only at this ⊢
  rw [this, couplingVector_zero]
  simp only [weightedKernelSum, kernelPlaquetteSum]
  rw [finsum_eq_sum_of_fintype]
end Sums
section Requirements
variable {L m J : ℕ} [Fintype (Plaquette L m (J : ℤ))] [Nonempty (Plaquette L m (J : ℤ))]
  (hCalc : SeveralComplexVariables.HolomorphicCalculus.Statement)
  (hSmooth : SeveralComplexVariables.HolomorphicContDiff.Statement)
  (hZdiff : Differentiable ℂ (latticeGaugeIntegral : (Plaquette L m (J : ℤ) → ℂ) → ℂ))
  (hopen : IsOpen (partitionFunctionNonvanishing L m (J : ℤ)))
  (hZ : ∀ (β : ℂ) (w : FourTorus L m → ℂ), torusSupNorm w ≠ ⊤ →
    sourcedPartitionFunction L m J β w =
      latticeGaugeIntegral (β • constantOneWeights - weightsAtBarycenters w :
        Plaquette L m (J : ℤ) → ℂ))
include hCalc hSmooth hZdiff hopen hZ in
lemma connectedFunctionEqKernelSum_holds : ConnectedFunctionEqKernelSum L m J := by
  intro n β f hβ hf
  have hsum := connectedFunction_eq_kernelPlaquetteSum hCalc hSmooth hZdiff hopen hZ hβ hf
  have hc₀ : (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) ∈
      partitionFunctionNonvanishing L m (J : ℤ) := by
    have : sourcedPartitionFunction L m J β 0 ≠ 0 := hβ
    rwa [sourcedPartitionFunction_zero hZ β] at this
  obtain ⟨δ, -, hδ⟩ := exists_admissibleRadius_le hZdiff hc₀ one_pos
  have hP := isOpen_polydisc (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) hδ.1
  have hL := localLog_holomorphic hCalc hSmooth hZdiff hδ
  have hchain := comp_couplingVector_chain hCalc β f hP hL
  have hW := hchain.1.1
  have hv0 : (couplingVector β f 0 : Plaquette L m (J : ℤ) → ℂ) ∈ polydisc
      (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) δ := by
    rw [couplingVector_zero]
    exact self_mem_polydisc hδ.1
  have h0 : (0 : Fin (n + 1) → ℂ) ∈ couplingVector β f ⁻¹' polydisc
      (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) δ := hv0
  have hgd := differentiableOn_of_isHolomorphicOnOpen hSmooth hchain.1
  have hexpg : ∀ z ∈ couplingVector β f ⁻¹' polydisc
      (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) δ,
      Complex.exp (localLog (β • constantOneWeights) (couplingVector β f z)) =
        latticeGaugeIntegral (couplingVector β f z : Plaquette L m (J : ℤ) → ℂ) /
          latticeGaugeIntegral (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) :=
    fun z hz => cexp_localLog hCalc hδ hz
  have hg0 : localLog (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ)
      (couplingVector β f 0) = 0 := by
    rw [couplingVector_zero]
    exact localLog_self hCalc hc₀
  have hc₀ne : latticeGaugeIntegral (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) ≠ 0 := hc₀
  refine ⟨fun N h hpair => ?_, ?_, hsum⟩
  · obtain ⟨hN, h0N, hcont, hexp⟩ := hpair
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hN.inter hW) 0 ⟨h0N, h0⟩
    have hconv : IsPreconnected (Metric.ball (0 : Fin (n + 1) → ℂ) r) :=
      (convex_ball _ _).isPreconnected
    have hs₁ : Metric.ball (0 : Fin (n + 1) → ℂ) r ⊆ N := fun z hz => (hball hz).1
    have hs₂ : Metric.ball (0 : Fin (n + 1) → ℂ) r ⊆ couplingVector β f ⁻¹' polydisc
      (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) δ := fun z hz => (hball hz).2
    have hu : ContinuousOn (fun z => h z - h 0 -
        localLog (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ)
          (couplingVector β f z)) (Metric.ball (0 : Fin (n + 1) → ℂ) r) :=
      ((hcont.mono hs₁).sub continuousOn_const).sub (hgd.continuousOn.mono hs₂)
    have h1 : ∀ z ∈ Metric.ball (0 : Fin (n + 1) → ℂ) r, Complex.exp (h z - h 0 -
        localLog (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ)
          (couplingVector β f z)) = 1 := by
      intro z hz
      have hne : latticeGaugeIntegral (couplingVector β f z : Plaquette L m (J : ℤ) → ℂ) ≠ 0 :=
        polydisc_subset_nonvanishing hδ (hs₂ hz)
      rw [Complex.exp_sub, Complex.exp_sub, hexpg z (hs₂ hz), hexp z (hs₁ hz), hexp 0 h0N,
        sourcedPartitionFunction_weightedSource hZ β hf,
        sourcedPartitionFunction_weightedSource hZ β hf, couplingVector_zero]
      field_simp
    have hzero := eq_zero_of_cexp_eq_one_of_isPreconnected hconv hu h1 (Metric.mem_ball_self hr)
      (by simp [hg0])
    have heq : EqOn h (fun z => h 0 + localLog
        (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) (couplingVector β f z))
        (Metric.ball (0 : Fin (n + 1) → ℂ) r) := by
      intro z hz
      have := hzero z hz
      simp only at this ⊢
      linear_combination this
    refine ⟨⟨_, hs₁, Metric.mem_ball_self hr, ?_⟩, ?_, hsum⟩
    · exact isHolomorphicOnOpen_of_differentiableOn Metric.isOpen_ball
        (((hgd.mono hs₂).const_add _).congr heq)
    · have hne : List.finRange (n + 1) ≠ [] := by simp
      show iteratedPartialDerivList (List.finRange (n + 1)) h 0 = _
      rw [iteratedPartialDerivList_congr_on Metric.isOpen_ball heq _ (Metric.mem_ball_self hr),
        iteratedPartialDerivList_const_add _ _ hne, connectedFunction_eq_iteratedPartialDerivList hZ β hf]
  · refine ⟨_, fun z => Complex.log (latticeGaugeIntegral (β • constantOneWeights :
      Plaquette L m (J : ℤ) → ℂ)) + localLog (β • constantOneWeights :
      Plaquette L m (J : ℤ) → ℂ) (couplingVector β f z), hW, h0,
      continuousOn_const.add hgd.continuousOn, fun z hz => ?_⟩
    rw [Complex.exp_add, Complex.exp_log hc₀ne, hexpg z hz, sourcedPartitionFunction_weightedSource hZ β hf]
    field_simp
lemma isBoundedOnTorus_update {n : ℕ} {f : Fin n → FourTorus L m → ℝ}
    (hf : ∀ k, IsBoundedOnTorus (f k))
    {g : FourTorus L m → ℝ} (hg : IsBoundedOnTorus g) (i : Fin n) (k : Fin n) :
    IsBoundedOnTorus (Function.update f i g k) := by
  by_cases h : k = i
  · subst h
    simpa using hg
  · simpa [Function.update_of_ne h] using hf k
lemma isBoundedOnTorus_linearCombination {g g' : FourTorus L m → ℝ} (hg : IsBoundedOnTorus g)
    (hg' : IsBoundedOnTorus g') (a a' : ℝ) : IsBoundedOnTorus (a • g + a' • g') := by
  obtain ⟨C, hC⟩ := (torusSupNorm_ne_top_iff g).1 hg
  obtain ⟨C', hC'⟩ := (torusSupNorm_ne_top_iff g').1 hg'
  refine (torusSupNorm_ne_top_iff _).2 ⟨|a| * C + |a'| * C', fun y => ?_⟩
  have h1 : ‖a * g y‖ ≤ |a| * C := by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC y) (abs_nonneg a)
  have h2 : ‖a' * g' y‖ ≤ |a'| * C' := by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC' y) (abs_nonneg a')
  exact (norm_add_le _ _).trans (add_le_add h1 h2)
lemma kernelPlaquetteSum_eq_sum {n : ℕ} (β : ℂ) (f : Fin (n + 1) → FourTorus L m → ℝ) :
    kernelPlaquetteSum L m J β f = ∑ p : Fin (n + 1) → Plaquette L m (J : ℤ),
      logDerivativeKernel n p (β • constantOneWeights) * ∏ i, (f i (p i).barycenter : ℂ) :=
  finsum_eq_sum_of_fintype _
lemma kernelPlaquetteSum_update_linear {n : ℕ} (β : ℂ) (f : Fin (n + 1) → FourTorus L m → ℝ)
    (i : Fin (n + 1)) (g g' : FourTorus L m → ℝ) (a a' : ℝ) :
    kernelPlaquetteSum L m J β (Function.update f i (a • g + a' • g')) =
      (a : ℂ) * kernelPlaquetteSum L m J β (Function.update f i g) +
        (a' : ℂ) * kernelPlaquetteSum L m J β (Function.update f i g') := by
  simp only [kernelPlaquetteSum_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hsplit : ∀ h : FourTorus L m → ℝ,
      ∏ j, ((Function.update f i h j (p j).barycenter : ℝ) : ℂ) =
        (h (p i).barycenter : ℂ) * ∏ j ∈ Finset.univ.erase i, (f j (p j).barycenter : ℂ) := by
    intro h
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hsplit, hsplit, hsplit]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]
  ring
include hCalc hSmooth hZdiff in
lemma kernelPlaquetteSum_comp_perm {n : ℕ} {β : ℂ} (f : Fin (n + 1) → FourTorus L m → ℝ)
    (σ : Equiv.Perm (Fin (n + 1)))
    (hc : (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) ∈
      partitionFunctionNonvanishing L m (J : ℤ)) :
    kernelPlaquetteSum L m J β (f ∘ σ) = kernelPlaquetteSum L m J β f := by
  simp only [kernelPlaquetteSum_eq_sum]
  rw [← (Equiv.arrowCongr σ.symm (Equiv.refl (Plaquette L m (J : ℤ)))).sum_comp]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hq : (Equiv.arrowCongr σ.symm (Equiv.refl (Plaquette L m (J : ℤ)))) q = q ∘ σ := by
    funext i
    simp [Equiv.arrowCongr]
  rw [hq, logDerivativeKernel_comp_perm hCalc hSmooth hZdiff n q σ hc]
  congr 1
  exact Equiv.prod_comp σ fun j => (f j (q j).barycenter : ℂ)
include hCalc hSmooth hZdiff hopen hZ in
lemma connectedFunctionAnalyticMultilinear_holds
    (hreal : ∀ c ∈ partitionFunctionNonvanishing L m (J : ℤ) ∩
      realPoints (Plaquette L m (J : ℤ)), (latticeGaugeIntegral c).im = 0)
    (hU : IsOpen (nonvanishingCouplings L m J))
    (hUR : ∀ t : ℝ, (t : ℂ) ∈ nonvanishingCouplings L m J) :
    ConnectedFunctionAnalyticMultilinear L m J := by
  have hmaps : ∀ β ∈ nonvanishingCouplings L m J,
      (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) ∈
        partitionFunctionNonvanishing L m (J : ℤ) := by
    intro β hβ
    have : sourcedPartitionFunction L m J β 0 ≠ 0 := hβ
    rwa [sourcedPartitionFunction_zero hZ β] at this
  intro n
  refine ⟨fun f hf => ⟨?_, fun b => ?_⟩, fun β hβ => ⟨fun f i g g' a a' hf hg hg' => ?_,
    fun f σ hf => ?_⟩⟩
  · have hline : Differentiable ℂ (fun β : ℂ =>
        (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ)) :=
      differentiable_id.smul_const _
    have hterm : ∀ p : Fin (n + 1) → Plaquette L m (J : ℤ), DifferentiableOn ℂ
        (fun β : ℂ => logDerivativeKernel n p (β • constantOneWeights) *
          ∏ i, (f i (p i).barycenter : ℂ)) (nonvanishingCouplings L m J) := fun p =>
      ((differentiableOn_of_isHolomorphicOnOpen hSmooth
        (logDerivativeKernel_holomorphic hCalc hSmooth hZdiff hopen n p)).comp
          hline.differentiableOn hmaps).mul_const _
    have hs : DifferentiableOn ℂ (fun β : ℂ => ∑ p : Fin (n + 1) → Plaquette L m (J : ℤ),
        logDerivativeKernel n p (β • constantOneWeights) * ∏ i, (f i (p i).barycenter : ℂ))
        (nonvanishingCouplings L m J) :=
      DifferentiableOn.fun_sum (u := Finset.univ) fun p _ => hterm p
    refine hs.congr fun β hβ => ?_
    rw [connectedFunction_eq_kernelPlaquetteSum hCalc hSmooth hZdiff hopen hZ hβ hf,
      kernelPlaquetteSum_eq_sum]
  · rw [connectedFunction_eq_kernelPlaquetteSum hCalc hSmooth hZdiff hopen hZ (hUR b) hf,
      kernelPlaquetteSum_eq_sum, Complex.im_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    have hrealc : ((b : ℂ) • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) ∈
        partitionFunctionNonvanishing L m (J : ℤ) ∩ realPoints (Plaquette L m (J : ℤ)) :=
      ⟨hmaps _ (hUR b), fun q => by simp [constantOneWeights]⟩
    have hk := logDerivativeKernel_im_eq_zero hCalc hSmooth hZdiff hopen hreal n p _ hrealc
    have hprod : ∏ i, ((f i (p i).barycenter : ℝ) : ℂ) =
        ((∏ i, f i (p i).barycenter : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
    rw [hprod, Complex.mul_im, hk, Complex.ofReal_im]
    ring
  · have hb := isBoundedOnTorus_linearCombination hg hg' a a'
    rw [connectedFunction_eq_kernelPlaquetteSum hCalc hSmooth hZdiff hopen hZ hβ
        (isBoundedOnTorus_update hf hb i),
      connectedFunction_eq_kernelPlaquetteSum hCalc hSmooth hZdiff hopen hZ hβ
        (isBoundedOnTorus_update hf hg i),
      connectedFunction_eq_kernelPlaquetteSum hCalc hSmooth hZdiff hopen hZ hβ
        (isBoundedOnTorus_update hf hg' i)]
    exact kernelPlaquetteSum_update_linear β f i g g' a a'
  · rw [connectedFunction_eq_kernelPlaquetteSum hCalc hSmooth hZdiff hopen hZ hβ (f := f ∘ σ)
        (fun k => hf (σ k)),
      connectedFunction_eq_kernelPlaquetteSum hCalc hSmooth hZdiff hopen hZ hβ hf]
    exact kernelPlaquetteSum_comp_perm hCalc hSmooth hZdiff f σ (hmaps β hβ)
end Requirements
section Measures
variable {L m J : ℕ} [Fintype (Plaquette L m (J : ℤ))] [Nonempty (Plaquette L m (J : ℤ))]
  [CompactSpace (CompactGaugeField L m (J : ℤ))]
  [IsProbabilityMeasure (gaugeFieldMeasure L m (J : ℤ))]
  (hEnergy : GaugeFieldProduct.PlaquetteEnergyContinuousBounded L m (J : ℤ))
lemma continuous_linkValue (b : Bond L m (J : ℤ)) :
    Continuous (fun U : CompactGaugeField L m (J : ℤ) => CompactGaugeField.linkValue U b) :=
  continuous_iInf_dom (i := b) continuous_induced_dom
lemma continuous_gaugeField_val :
    Continuous (fun U : CompactGaugeField L m (J : ℤ) => U.1) :=
  continuous_pi fun b => continuous_subtype_val.comp (continuous_linkValue b)
lemma measurableEmbedding_gaugeField_val :
    MeasurableEmbedding (fun U : CompactGaugeField L m (J : ℤ) => U.1) := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hinj : Function.Injective (fun U : CompactGaugeField L m (J : ℤ) => U.1) :=
    Subtype.val_injective
  exact (continuous_gaugeField_val.isClosedEmbedding hinj).measurableEmbedding
lemma gaugeField_val_eq
    (hor : ∀ b : Bond L m (J : ℤ), Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (U : CompactGaugeField L m (J : ℤ)) :
    U.1 = gaugeFieldOfPositive (restrictToPositiveBonds U) := by
  funext b
  unfold gaugeFieldOfPositive
  by_cases h : b.IsPositivelyOriented
  · simp only [dif_pos h]
    rfl
  · have h' : b.opposite.IsPositivelyOriented := by
      rcases hor b with ⟨h₁, -⟩ | ⟨h₁, -⟩
      · exact absurd h₁ h
      · exact h₁
    simp only [dif_neg h, dif_pos h']
    show U.1 b = (U.1 b.opposite)⁻¹
    have hmem : U.1 b ∈ Matrices.ComplexMatrix2.specialUnitary := U.2.1 b (mem_univ b)
    rw [U.2.2 b (mem_univ b),
      Matrix.nonsing_inv_nonsing_inv _ (by
        rw [(Matrix.mem_specialUnitaryGroup_iff.1 hmem).2]
        exact isUnit_one)]
lemma measurable_gaugeFieldOfPositive :
    Measurable (gaugeFieldOfPositive :
      (PositivelyOrientedBond L m (J : ℤ) → Matrices.ComplexMatrix2.specialUnitary) →
        Bond L m (J : ℤ) → Matrices.ComplexMatrix2) := by
  refine measurable_pi_iff.2 fun b => ?_
  unfold gaugeFieldOfPositive
  have hinv : Continuous (fun g : Matrices.ComplexMatrix2.specialUnitary =>
      (g : Matrices.ComplexMatrix2)⁻¹) := by
    have : (fun g : Matrices.ComplexMatrix2.specialUnitary => (g : Matrices.ComplexMatrix2)⁻¹) =
        fun g => ((g⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) := by
      funext g
      exact Matrix.inv_eq_left_inv (by rw [← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one])
    rw [this]
    exact continuous_subtype_val.comp continuous_inv
  by_cases h : b.IsPositivelyOriented
  · simp only [dif_pos h]
    exact continuous_subtype_val.measurable.comp (measurable_pi_apply _)
  · by_cases h' : b.opposite.IsPositivelyOriented
    · simp only [dif_neg h, dif_pos h']
      exact hinv.measurable.comp (measurable_pi_apply _)
    · simp only [dif_neg h, dif_neg h']
      exact measurable_const
lemma map_gaugeField_val
    (hor : ∀ b : Bond L m (J : ℤ), Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hspec : IsProductHaarImage L m (J : ℤ) (gaugeFieldMeasure L m (J : ℤ))) :
    (gaugeFieldMeasure L m (J : ℤ)).map (fun U => U.1) =
      productHaarMeasure L m (J : ℤ) := by
  have hv : Measurable (restrictToPositiveBonds : CompactGaugeField L m (J : ℤ) → _) :=
    measurable_pi_iff.2 fun b => (continuous_linkValue b.1).measurable
  unfold productHaarMeasure gaugeFieldHaar
  rw [← show _ = Matrices.ComplexMatrix2.haarPi (PositivelyOrientedBond L m (J : ℤ)) from hspec,
    Measure.map_map measurable_gaugeFieldOfPositive hv]
  congr 1
  funext U
  exact gaugeField_val_eq hor U
def realCoupledEnergy (b : ℝ) (U : CompactGaugeField L m (J : ℤ)) : ℝ :=
  ∑ p : Plaquette L m (J : ℤ), b * (plaquetteEnergy U.1 p).re
include hEnergy in
lemma plaquetteEnergy_re_cast (p : Plaquette L m (J : ℤ)) (U : CompactGaugeField L m (J : ℤ)) :
    ((plaquetteEnergy U.1 p).re : ℂ) = plaquetteEnergy U.1 p := by
  obtain ⟨t, -, ht⟩ := (hEnergy p).2 U
  rw [← ht]
  simp
lemma plaquetteEnergy_eq_re (p : Plaquette L m (J : ℤ)) (U : Bond L m (J : ℤ) → Matrices.ComplexMatrix2) :
    plaquetteCost U p = (plaquetteEnergy U p).re := by
  simp [plaquetteCost, plaquetteEnergy]
lemma barycenterWeightedEnergy_eq_sum (c : FourTorus L m → ℂ)
    (U : Bond L m (J : ℤ) → Matrices.ComplexMatrix2) :
    barycenterWeightedEnergy c U =
      ∑ p : Plaquette L m (J : ℤ), c p.barycenter * plaquetteEnergy U p :=
  finsum_eq_sum_of_fintype _
lemma observableOnFields_eq_sum (f : FourTorus L m → ℝ) (U : CompactGaugeField L m (J : ℤ)) :
    observableOnFields (J := J) f U =
      ∑ p : Plaquette L m (J : ℤ), (plaquetteEnergy U.1 p).re * f p.barycenter := by
  unfold observableOnFields smearedObservable
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [plaquetteEnergy_eq_re, smul_eq_mul]
include hEnergy in
lemma observableOnFields_ofReal (f : FourTorus L m → ℝ) (U : CompactGaugeField L m (J : ℤ)) :
    ((observableOnFields (J := J) f U : ℝ) : ℂ) =
      ∑ p : Plaquette L m (J : ℤ), (f p.barycenter : ℂ) * plaquetteEnergy U.1 p := by
  rw [observableOnFields_eq_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.ofReal_mul, plaquetteEnergy_re_cast hEnergy p U, mul_comm]
include hEnergy in
lemma barycenterWeightedEnergy_const (b : ℝ) (U : CompactGaugeField L m (J : ℤ)) :
    barycenterWeightedEnergy (fun _ => (b : ℂ)) U.1 = (realCoupledEnergy b U : ℂ) := by
  rw [barycenterWeightedEnergy_eq_sum, realCoupledEnergy, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.ofReal_mul, plaquetteEnergy_re_cast hEnergy p U]
include hEnergy in
lemma continuous_realCoupledEnergy (b : ℝ) :
    Continuous (realCoupledEnergy b : CompactGaugeField L m (J : ℤ) → ℝ) :=
  continuous_finsetSum _ fun p _ => continuous_const.mul (Complex.continuous_re.comp (hEnergy p).1)
include hEnergy in
lemma continuous_observableOnFields (f : FourTorus L m → ℝ) :
    Continuous (observableOnFields (J := J) f) := by
  have : observableOnFields (J := J) f = fun U => ∑ p : Plaquette L m (J : ℤ),
      (plaquetteEnergy U.1 p).re * f p.barycenter := funext (observableOnFields_eq_sum f)
  rw [this]
  exact continuous_finsetSum _ fun p _ =>
    (Complex.continuous_re.comp (hEnergy p).1).mul continuous_const
include hEnergy in
lemma integrable_exp_neg_realCoupledEnergy (b : ℝ) :
    Integrable (fun U : CompactGaugeField L m (J : ℤ) => Real.exp (-realCoupledEnergy b U))
      (gaugeFieldMeasure L m (J : ℤ)) := by
  have hc : Continuous (fun U : CompactGaugeField L m (J : ℤ) =>
      Real.exp (-realCoupledEnergy b U)) :=
    Real.continuous_exp.comp (continuous_realCoupledEnergy hEnergy b).neg
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ fun U => hC U (mem_univ U))
def realPartitionIntegral (L m J : ℕ) [Fintype (Plaquette L m (J : ℤ))] (b : ℝ) : ℝ :=
  ∫ U : CompactGaugeField L m (J : ℤ), Real.exp (-realCoupledEnergy b U)
    ∂gaugeFieldMeasure L m (J : ℤ)
include hEnergy in
lemma realPartitionIntegral_pos (b : ℝ) : 0 < realPartitionIntegral L m J b :=
  integral_exp_pos (integrable_exp_neg_realCoupledEnergy hEnergy b)
include hEnergy in
lemma sourcedPartitionFunction_ofReal_zero (b : ℝ) :
    sourcedPartitionFunction L m J b 0 = (realPartitionIntegral L m J b : ℂ) := by
  unfold sourcedPartitionFunction realPartitionIntegral
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  have : (fun y : FourTorus L m => (b : ℂ) - (0 : FourTorus L m → ℂ) y) = fun _ => (b : ℂ) := by
    funext y
    simp
  simp only [this]
  rw [barycenterWeightedEnergy_const hEnergy b U, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
include hEnergy in
lemma cexp_neg_energy_re (b : ℝ) (U : CompactGaugeField L m (J : ℤ)) :
    (Complex.exp (-barycenterWeightedEnergy (fun _ => (b : ℂ)) U.1)).re =
      Real.exp (-realCoupledEnergy b U) := by
  rw [barycenterWeightedEnergy_const hEnergy b U, ← Complex.ofReal_neg, Complex.exp_ofReal_re]
include hEnergy in
lemma boltzmannMeasure_eq (b : ℝ) : normalizedActionMeasure L m J b =
    (ENNReal.ofReal (realPartitionIntegral L m J b))⁻¹ •
      (gaugeFieldMeasure L m (J : ℤ)).withDensity fun U =>
        ENNReal.ofReal (Real.exp (-realCoupledEnergy b U)) := by
  unfold normalizedActionMeasure
  rw [sourcedPartitionFunction_ofReal_zero hEnergy b, Complex.ofReal_re]
  congr 2
  funext U
  rw [cexp_neg_energy_re hEnergy b U]
include hEnergy in
lemma boltzmannMeasure_isProbability (b : ℝ) :
    IsProbabilityMeasure (normalizedActionMeasure L m J b) := by
  refine ⟨?_⟩
  rw [boltzmannMeasure_eq hEnergy b, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, smul_eq_mul,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_realCoupledEnergy hEnergy b)
      (ae_of_all _ fun U => (Real.exp_pos _).le)]
  exact ENNReal.inv_mul_cancel (by simpa using realPartitionIntegral_pos hEnergy b)
    ENNReal.ofReal_ne_top
include hEnergy in
lemma integral_boltzmannMeasure (b : ℝ) (F : CompactGaugeField L m (J : ℤ) → ℂ) :
    ∫ U, F U ∂normalizedActionMeasure L m J b = (realPartitionIntegral L m J b : ℂ)⁻¹ *
      ∫ U, (Real.exp (-realCoupledEnergy b U) : ℂ) * F U ∂gaugeFieldMeasure L m (J : ℤ) := by
  have hmeas : Measurable (fun U : CompactGaugeField L m (J : ℤ) =>
      ENNReal.ofReal (Real.exp (-realCoupledEnergy b U))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp (continuous_realCoupledEnergy hEnergy b).neg).measurable
  rw [boltzmannMeasure_eq hEnergy b, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (ae_of_all _ fun U => ENNReal.ofReal_lt_top),
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (realPartitionIntegral_pos hEnergy b).le,
    Complex.real_smul, Complex.ofReal_inv]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  simp only []
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul, Complex.ofReal_exp]
include hEnergy in
lemma neg_energy_sourced {N : ℕ} (b : ℝ) (f : Fin N → FourTorus L m → ℝ) (t : Fin N → ℂ)
    (U : CompactGaugeField L m (J : ℤ)) :
    -barycenterWeightedEnergy (fun y => (b : ℂ) - weightedSource f t y) U.1 =
      -(realCoupledEnergy b U : ℂ) + ∑ i, t i * (observableOnFields (J := J) (f i) U : ℂ) := by
  rw [← barycenterWeightedEnergy_const hEnergy b U]
  simp only [observableOnFields_ofReal hEnergy, barycenterWeightedEnergy_eq_sum, weightedSource,
    sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]
  ring
include hEnergy in
lemma momentGeneratingFunction_eq {N : ℕ} (b : ℝ) (f : Fin N → FourTorus L m → ℝ)
    (t : Fin N → ℂ) :
    Cumulants.momentGeneratingFunction (normalizedActionMeasure L m J b)
        (fun i => observableOnFields (J := J) (f i)) t =
      sourcedPartitionFunction L m J b (weightedSource f t) /
        sourcedPartitionFunction L m J b 0 := by
  unfold Cumulants.momentGeneratingFunction
  rw [integral_boltzmannMeasure hEnergy b, sourcedPartitionFunction_ofReal_zero hEnergy b,
    div_eq_inv_mul]
  congr 1
  unfold sourcedPartitionFunction
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  simp only []
  rw [neg_energy_sourced hEnergy b f t U, Complex.exp_add, Complex.ofReal_exp, Complex.ofReal_neg]
end Measures
section Cumulants
variable {L m J : ℕ} [Fintype (Plaquette L m (J : ℤ))] [Nonempty (Plaquette L m (J : ℤ))]
  [CompactSpace (CompactGaugeField L m (J : ℤ))]
  [IsProbabilityMeasure (gaugeFieldMeasure L m (J : ℤ))]
  (hEnergy : GaugeFieldProduct.PlaquetteEnergyContinuousBounded L m (J : ℤ))
  (hSmooth : SeveralComplexVariables.HolomorphicContDiff.Statement)
  (hZdiff : Differentiable ℂ (latticeGaugeIntegral : (Plaquette L m (J : ℤ) → ℂ) → ℂ))
  (hZ : ∀ (β : ℂ) (w : FourTorus L m → ℂ), torusSupNorm w ≠ ⊤ →
    sourcedPartitionFunction L m J β w =
      latticeGaugeIntegral (β • constantOneWeights - weightsAtBarycenters w :
        Plaquette L m (J : ℤ) → ℂ))
  (hsum : ConnectedFunctionEqKernelSum L m J)
  (hUR : ∀ t : ℝ, (t : ℂ) ∈ nonvanishingCouplings L m J)
lemma pi_single_eq_basisVector {N : ℕ} (i : Fin N) :
    (Pi.single i 1 : Fin N → ℂ) = basisVector i := by
  funext k
  by_cases h : k = i
  · subst h
    simp [basisVector]
  · simp [basisVector, h]
include hEnergy hSmooth hZdiff hZ hsum hUR in
lemma connectedFunction_eq_mixedCumulant {n : ℕ} (b : ℝ) {f : Fin (n + 1) → FourTorus L m → ℝ}
    (hf : ∀ i, IsBoundedOnTorus (f i)) :
    connectedFunction L m J b f =
      Cumulants.mixedCumulant (normalizedActionMeasure L m J b)
        fun i => observableOnFields (J := J) (f i) := by
  have hM := momentGeneratingFunction_eq (J := J) hEnergy b f
  have hZ0 : sourcedPartitionFunction L m J b 0 ≠ 0 := hUR b
  have hlin0 : weightedSource f (0 : Fin (n + 1) → ℂ) = 0 := by
    funext y
    simp [weightedSource]
  have hcont : Continuous (Cumulants.momentGeneratingFunction (normalizedActionMeasure L m J b)
      fun i => observableOnFields (J := J) (f i)) := by
    have : Cumulants.momentGeneratingFunction (normalizedActionMeasure L m J b)
        (fun i => observableOnFields (J := J) (f i)) = fun t =>
          latticeGaugeIntegral (couplingVector (b : ℂ) f t : Plaquette L m (J : ℤ) → ℂ) /
            sourcedPartitionFunction L m J b 0 := by
      funext t
      rw [hM t, sourcedPartitionFunction_weightedSource hZ _ hf t]
    rw [this]
    exact (hZdiff.continuous.comp (couplingVector_differentiable _ f).continuous).div_const _
  have hW : IsOpen (Cumulants.momentGeneratingFunction (normalizedActionMeasure L m J b)
      (fun i => observableOnFields (J := J) (f i)) ⁻¹' Complex.slitPlane) :=
    Complex.isOpen_slitPlane.preimage hcont
  have h0W : (0 : Fin (n + 1) → ℂ) ∈ Cumulants.momentGeneratingFunction
      (normalizedActionMeasure L m J b)
      (fun i => observableOnFields (J := J) (f i)) ⁻¹' Complex.slitPlane := by
    show _ ∈ Complex.slitPlane
    rw [hM 0, hlin0, div_self hZ0]
    exact Complex.one_mem_slitPlane
  have hpair : IsContinuousLogOfSourced L m J b f
      (Cumulants.momentGeneratingFunction (normalizedActionMeasure L m J b)
        (fun i => observableOnFields (J := J) (f i)) ⁻¹' Complex.slitPlane)
      (fun t => Complex.log (sourcedPartitionFunction L m J b 0) +
        Complex.log (Cumulants.momentGeneratingFunction (normalizedActionMeasure L m J b)
          (fun i => observableOnFields (J := J) (f i)) t)) := by
    refine ⟨hW, h0W, continuousOn_const.add (hcont.continuousOn.clog fun t ht => ht),
      fun z hz => ?_⟩
    rw [Complex.exp_add, Complex.exp_log hZ0, Complex.exp_log (Complex.slitPlane_ne_zero hz), hM z]
    field_simp
  obtain ⟨⟨N', -, h0', hhol⟩, hder, -⟩ := (hsum n b f (hUR b) hf).1 _ _ hpair
  have hgs : ContDiffOn ℂ ∞ (fun t => Complex.log (Cumulants.momentGeneratingFunction
      (normalizedActionMeasure L m J b) (fun i => observableOnFields (J := J) (f i)) t)) N' :=
    ((hSmooth _ _ _ hhol).sub (contDiffOn_const
      (c := Complex.log (sourcedPartitionFunction L m J b 0)))).congr
      fun t _ => (add_sub_cancel_left _ _).symm
  have hj := iteratedFDeriv_basis_eq_iteratedPartialDerivList hhol.1 hgs (n + 1) id 0 h0'
  have hsingle : (fun i : Fin (n + 1) => (Pi.single i 1 : Fin (n + 1) → ℂ)) =
      fun i => basisVector (id i) := by
    funext i
    exact pi_single_eq_basisVector i
  have hne : List.finRange (n + 1) ≠ [] := by simp
  unfold Cumulants.mixedCumulant
  rw [hsingle, hj, List.ofFn_id, ← hder]
  exact congrFun (iteratedPartialDerivList_const_add _ _ hne) 0
lemma partitionFunction_eq_realPartitionIntegral
    (hor : ∀ b : Bond L m (J : ℤ), Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hspec : IsProductHaarImage L m (J : ℤ) (gaugeFieldMeasure L m (J : ℤ)))
    (hEnergy : GaugeFieldProduct.PlaquetteEnergyContinuousBounded L m (J : ℤ)) (b : ℝ) :
    partitionFunction L m J b = realPartitionIntegral L m J b := by
  unfold partitionFunction realPartitionIntegral
  rw [← map_gaugeField_val hor hspec, measurableEmbedding_gaugeField_val.integral_map]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  simp only [boltzmannWeight, wilsonAction]
  rw [finsum_eq_sum_of_fintype, realCoupledEnergy, Finset.mul_sum, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [plaquetteEnergy_eq_re]
  ring
lemma map_boltzmannMeasure
    (hor : ∀ b : Bond L m (J : ℤ), Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hspec : IsProductHaarImage L m (J : ℤ) (gaugeFieldMeasure L m (J : ℤ)))
    (hEnergy : GaugeFieldProduct.PlaquetteEnergyContinuousBounded L m (J : ℤ)) (b : ℝ) :
    (normalizedActionMeasure L m J b).map (fun U => U.1) = wilsonGibbsMeasure L m J b := by
  have hme := measurableEmbedding_gaugeField_val (L := L) (m := m) (J := J)
  rw [boltzmannMeasure_eq hEnergy b]
  unfold wilsonGibbsMeasure
  rw [Measure.map_smul, partitionFunction_eq_realPartitionIntegral hor hspec hEnergy b]
  congr 1
  ext S hS
  rw [Measure.map_apply hme.measurable hS, withDensity_apply _ (hme.measurable hS),
    withDensity_apply _ hS, ← map_gaugeField_val hor hspec,
    Measure.restrict_map hme.measurable hS, hme.lintegral_map]
  refine lintegral_congr fun U => ?_
  congr 1
  simp only [boltzmannWeight, wilsonAction]
  rw [finsum_eq_sum_of_fintype, realCoupledEnergy, Finset.mul_sum, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [plaquetteEnergy_eq_re]
  ring
lemma mixedCumulant_map {n : ℕ} (ν : Measure (CompactGaugeField L m (J : ℤ)))
    (X : Fin n → (Bond L m (J : ℤ) → Matrices.ComplexMatrix2) → ℝ) :
    Cumulants.mixedCumulant (ν.map fun U => U.1) X =
      Cumulants.mixedCumulant ν fun i U => X i U.1 := by
  have hme := measurableEmbedding_gaugeField_val (L := L) (m := m) (J := J)
  have : Cumulants.momentGeneratingFunction (ν.map fun U => U.1) X =
      Cumulants.momentGeneratingFunction ν fun i U => X i U.1 := by
    funext t
    unfold Cumulants.momentGeneratingFunction
    exact hme.integral_map _
  unfold Cumulants.mixedCumulant
  rw [this]
include hEnergy hSmooth hZdiff hZ hsum hUR in
lemma connectedFunctionEqCumulant_holds
    (hor : ∀ b : Bond L m (J : ℤ), Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hspec : IsProductHaarImage L m (J : ℤ) (gaugeFieldMeasure L m (J : ℤ))) :
    ConnectedFunctionEqCumulant L m J := by
  refine ⟨fun b => ⟨?_, ?_, boltzmannMeasure_isProbability hEnergy b, fun n f hf =>
    ⟨fun i => ⟨?_, ?_⟩,
    connectedFunction_eq_mixedCumulant hEnergy hSmooth hZdiff hZ hsum hUR b hf⟩,
    fun _ _ => ⟨?_, ?_⟩⟩,
    fun n β f hβ hf => ?_⟩
  · rw [sourcedPartitionFunction_ofReal_zero hEnergy b, Complex.ofReal_re]
    exact realPartitionIntegral_pos hEnergy b
  · rw [sourcedPartitionFunction_ofReal_zero hEnergy b, Complex.ofReal_im]
  · exact (continuous_observableOnFields hEnergy (f i)).measurable
  · obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (continuous_observableOnFields hEnergy (f i)).continuousOn
    exact ⟨C, fun U => hC U (mem_univ U)⟩
  · rw [sourcedPartitionFunction_ofReal_zero hEnergy b,
      partitionFunction_eq_realPartitionIntegral hor hspec hEnergy b]
  · exact map_boltzmannMeasure hor hspec hEnergy b
  · unfold observableCumulant
    split_ifs with h
    · obtain ⟨-, -, him⟩ := h
      have hβeq : ((β.re : ℝ) : ℂ) = β := Complex.ext (by simp) (by simp [him])
      unfold gibbsCumulant
      rw [← map_boltzmannMeasure hor hspec hEnergy β.re, mixedCumulant_map]
      have := connectedFunction_eq_mixedCumulant hEnergy hSmooth hZdiff hZ hsum hUR β.re hf
      rw [hβeq] at this
      exact this.symm
    · rfl
end Cumulants
theorem statement_holds (hEntire : PartitionFunctionAnalyticity.Statement)
    (hCalc : SeveralComplexVariables.HolomorphicCalculus.Statement)
    (hProduct : GaugeFieldProduct.Statement)
    (hSmooth : SeveralComplexVariables.HolomorphicContDiff.Statement) : Statement := by
  intro L m J hL hm
  obtain ⟨hSp, hFin, hCfg, hAct⟩ := hProduct.1 L m (J : ℤ) hL hm (Int.natCast_nonneg J)
  obtain ⟨-, -, hfinP, hneP⟩ := hFin
  have := hneP
  letI := Fintype.ofFinite (Plaquette L m (J : ℤ))
  obtain ⟨-, -, hcomp, -, -, hspec, hprob⟩ := hCfg
  have := hcomp
  have := hprob
  obtain ⟨hEa, hEb, -, -, hEe, -⟩ := hEntire L m J hL hm
  have hZdiff : Differentiable ℂ (latticeGaugeIntegral : (Plaquette L m (J : ℤ) → ℂ) → ℂ) :=
    differentiableOn_univ.1 (differentiableOn_of_isHolomorphicOnOpen hSmooth hEa.1)
  have hopen := hEa.2.2.1
  have hZ := hEb.2.2.2.2
  have hreal : ∀ c ∈ partitionFunctionNonvanishing L m (J : ℤ) ∩
      realPoints (Plaquette L m (J : ℤ)), (latticeGaugeIntegral c).im = 0 := by
    intro c hc
    obtain ⟨t, ht, -⟩ := hEa.2.1 c hc.2
    rw [ht, Complex.ofReal_im]
  have hsum := connectedFunctionEqKernelSum_holds (L := L) (m := m) (J := J)
    hCalc hSmooth hZdiff hopen hZ
  refine ⟨logarithmBranchIndependence_holds hCalc hSmooth hZdiff, fun n p =>
    ⟨logDerivativeKernel_holomorphic hCalc hSmooth hZdiff hopen n p,
    fun σ c hc => logDerivativeKernel_comp_perm hCalc hSmooth hZdiff n p σ hc, fun x => ?_⟩, hsum,
    connectedFunctionAnalyticMultilinear_holds hCalc hSmooth hZdiff hopen hZ hreal hEe.2.1 hEe.2.2,
    connectedFunctionEqCumulant_holds hAct hSmooth hZdiff hZ hsum hEe.2.2 hSp.2.2.2.2.2 hspec⟩
  have hrf : (fun q => (x q : ℂ)) ∈ realPoints (Plaquette L m (J : ℤ)) := fun q => by simp
  exact logDerivativeKernel_im_eq_zero hCalc hSmooth hZdiff hopen hreal n p _ ⟨hEa.2.2.2 _ hrf, hrf⟩
end YangMills.Construction.ConnectedFunctionExpansion

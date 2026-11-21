import YangMills.Construction.Torus.ComplexExtensionOfABoundedRealForm
import YangMills.Construction.Torus.GradientNormLipschitzConstantAndSharpNorm
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
open Function
noncomputable section
namespace YangMills.Construction.AmbientPoints.ComplexExtensionProof
section Partials
variable {D : ℕ}
theorem hasLineDerivAt_linComb (a b : ℂ) {G H : (Fin D → ℝ) → ℂ} (j : Fin D)
    (hG : ∀ x, LineDifferentiableAt ℝ G x (Pi.single j 1))
    (hH : ∀ x, LineDifferentiableAt ℝ H x (Pi.single j 1)) (x : Fin D → ℝ) :
    HasLineDerivAt ℝ (fun y => a * G y + b * H y)
      (a * partialDeriv j G x + b * partialDeriv j H x) x (Pi.single j 1) :=
  (HasDerivAt.const_mul a (hG x).hasLineDerivAt).add (HasDerivAt.const_mul b (hH x).hasLineDerivAt)
theorem continuousPartialsUpTo_linComb (a b : ℂ) {G H : (Fin D → ℝ) → ℂ}
    (hG : ContinuousPartialsUpTo Set.univ 1 G) (hH : ContinuousPartialsUpTo Set.univ 1 H) :
    ContinuousPartialsUpTo Set.univ 1 (fun y => a * G y + b * H y) := by
  have hG' : ContinuousOn G Set.univ ∧ ∀ j : Fin D,
      (∀ x ∈ Set.univ, LineDifferentiableAt ℝ G x (Pi.single j 1)) ∧
        ContinuousOn (partialDeriv j G) Set.univ := hG
  have hH' : ContinuousOn H Set.univ ∧ ∀ j : Fin D,
      (∀ x ∈ Set.univ, LineDifferentiableAt ℝ H x (Pi.single j 1)) ∧
        ContinuousOn (partialDeriv j H) Set.univ := hH
  have hd : ∀ (j : Fin D) (x : Fin D → ℝ), HasLineDerivAt ℝ (fun y => a * G y + b * H y)
      (a * partialDeriv j G x + b * partialDeriv j H x) x (Pi.single j 1) := fun j x =>
    hasLineDerivAt_linComb a b j (fun x => (hG'.2 j).1 x (Set.mem_univ x))
      (fun x => (hH'.2 j).1 x (Set.mem_univ x)) x
  have hp : ∀ j : Fin D, partialDeriv j (fun y => a * G y + b * H y) =
      fun x => a * partialDeriv j G x + b * partialDeriv j H x :=
    fun j => funext fun x => (hd j x).lineDeriv
  exact show ContinuousOn (fun y => a * G y + b * H y) Set.univ ∧ ∀ j : Fin D,
      (∀ x ∈ Set.univ, LineDifferentiableAt ℝ (fun y => a * G y + b * H y) x (Pi.single j 1)) ∧
        ContinuousOn (partialDeriv j (fun y => a * G y + b * H y)) Set.univ from by
    refine ⟨(continuousOn_const.mul hG'.1).add (continuousOn_const.mul hH'.1), fun j =>
      ⟨fun x _ => (hd j x).lineDifferentiableAt, ?_⟩⟩
    rw [hp j]
    exact (continuousOn_const.mul (hG'.2 j).2).add (continuousOn_const.mul (hH'.2 j).2)
end Partials
theorem isCn_one_iff_comp_proj {s : Conventions.StandingParameters} {E : Ambient} {p : ℕ}
    (F : Tuple s E p → ℂ) :
    IsCn 1 F ↔ ContinuousPartialsUpTo Set.univ 1 (F ∘ tupleProj s E p) := by
  have h := isCnOn_coe_iff Set.univ 1 (F ∘ tupleProj s E p)
  simpa [IsCn, isOpen_univ] using h
theorem tsupport_linComb_subset {X 𝕜 : Type*} [TopologicalSpace X] [Field 𝕜] (a b : 𝕜)
    (u v : X → 𝕜) : tsupport (a • u + b • v) ⊆ tsupport u ∪ tsupport v := by
  refine closure_minimal (fun x hx => ?_) ((isClosed_tsupport u).union (isClosed_tsupport v))
  by_contra hn
  rw [Set.mem_union, not_or] at hn
  apply hx
  simp [image_eq_zero_of_notMem_tsupport hn.1, image_eq_zero_of_notMem_tsupport hn.2]
variable {s : Conventions.StandingParameters} {n : ℕ} {O : Fin n → Set (Pt s .euclidean)}
theorem linComb_mem_componentSpace {i : Fin n} {p q : Pt s .euclidean → ℝ}
    (hp : p ∈ entrySpace O i) (hq : q ∈ entrySpace O i) (α β : ℝ) :
    α • p + β • q ∈ entrySpace O i := by
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  have hsub := tsupport_linComb_subset α β p q
  refine ⟨?_, (hp2.union hq2).of_isClosed_subset (isClosed_tsupport _) hsub,
    hsub.trans (Set.union_subset hp3 hq3)⟩
  have h := continuousPartialsUpTo_linComb (α : ℂ) (β : ℂ) ((isCn_one_iff_comp_proj _).1 hp1)
    ((isCn_one_iff_comp_proj _).1 hq1)
  refine (isCn_one_iff_comp_proj _).2 ?_
  convert h using 1
  funext y
  simp [asFunctionOnOnePoint]
def ReImRegular (s : Conventions.StandingParameters) : Prop :=
  ∀ g : Pt s .euclidean → ℂ, IsCnAtPoint 1 g →
    IsCnAtPoint 1 (fun x => ((g x).re : ℂ)) ∧
    IsCnAtPoint 1 (fun x => ((g x).im : ℂ)) ∧
    c1GradNorm (fun x => ((g x).re : ℂ)) ≤ c1GradNorm g ∧
    c1GradNorm (fun x => ((g x).im : ℂ)) ≤ c1GradNorm g
def reIm (b : Bool) (h : Pt s .euclidean → ℂ) : Pt s .euclidean → ℝ :=
  fun x => cond b (h x).im (h x).re
theorem reIm_mem (hS : ReImRegular s) {i : Fin n} {h : Pt s .euclidean → ℂ}
    (hh : h ∈ complexEntrySpace O i) (b : Bool) : reIm b h ∈ entrySpace O i := by
  obtain ⟨h1, h2, h3⟩ := hh
  have hsub : tsupport (reIm b h) ⊆ tsupport h := by
    refine closure_mono fun x hx => ?_
    intro h0
    apply hx
    cases b <;> simp [reIm, h0]
  refine ⟨?_, h2.of_isClosed_subset (isClosed_tsupport _) hsub, hsub.trans h3⟩
  cases b
  · exact (hS h h1).1
  · exact (hS h h1).2.1
theorem c1GradNorm_reIm_le (hS : ReImRegular s) {h : Pt s .euclidean → ℂ}
    (hh : IsCnAtPoint 1 h) (b : Bool) :
    c1GradNorm (fun x => ((reIm b h x : ℝ) : ℂ)) ≤ c1GradNorm h := by
  cases b
  · exact (hS h hh).2.2.1
  · exact (hS h hh).2.2.2
theorem reIm_false_linComb (a b : ℂ) (u v : Pt s .euclidean → ℂ) :
    reIm false (a • u + b • v) =
      (1 : ℝ) • (a.re • reIm false u + (-a.im) • reIm true u) +
        (1 : ℝ) • (b.re • reIm false v + (-b.im) • reIm true v) := by
  funext x
  simp [reIm]
  ring
theorem reIm_true_linComb (a b : ℂ) (u v : Pt s .euclidean → ℂ) :
    reIm true (a • u + b • v) =
      (1 : ℝ) • (a.re • reIm true u + a.im • reIm false u) +
        (1 : ℝ) • (b.re • reIm true v + b.im • reIm false v) := by
  funext x
  simp [reIm]
def zeroExtend (B : EntryTuple O → ℝ) (f : Fin n → Pt s .euclidean → ℝ) : ℝ :=
  open Classical in if hf : ∀ i, f i ∈ entrySpace O i then B fun i => ⟨f i, hf i⟩ else 0
theorem zeroExtend_of_mem (B : EntryTuple O → ℝ) {f : Fin n → Pt s .euclidean → ℝ}
    (hf : ∀ i, f i ∈ entrySpace O i) : zeroExtend B f = B fun i => ⟨f i, hf i⟩ := by
  simp [zeroExtend, hf]
theorem update_mem_componentSpace {f : Fin n → Pt s .euclidean → ℝ} (hf : ∀ j, f j ∈ entrySpace O j)
    {i : Fin n} {r : Pt s .euclidean → ℝ} (hr : r ∈ entrySpace O i) (j : Fin n) :
    update f i r j ∈ entrySpace O j := by
  by_cases h : j = i
  · subst h
    simpa using hr
  · simpa [update_of_ne h] using hf j
theorem zeroExtend_update_linComb {B : EntryTuple O → ℝ} (hB : IsMultilinearOnComponents B)
    {f : Fin n → Pt s .euclidean → ℝ} (hf : ∀ j, f j ∈ entrySpace O j) (i : Fin n)
    {p q : Pt s .euclidean → ℝ} (hp : p ∈ entrySpace O i) (hq : q ∈ entrySpace O i)
    (α β : ℝ) :
    zeroExtend B (update f i (α • p + β • q)) =
      α * zeroExtend B (update f i p) + β * zeroExtend B (update f i q) := by
  have key : ∀ (r : Pt s .euclidean → ℝ) (hr : r ∈ entrySpace O i),
      zeroExtend B (update f i r) = B (update (fun j => ⟨f j, hf j⟩) i ⟨r, hr⟩) := by
    intro r hr
    rw [zeroExtend_of_mem B (update_mem_componentSpace hf hr)]
    congr 1
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [update_of_ne h]
  have hr := linComb_mem_componentSpace hp hq α β
  rw [key _ hr, key _ hp, key _ hq]
  exact hB _ i ⟨p, hp⟩ ⟨q, hq⟩ ⟨_, hr⟩ α β rfl
def entryEval (B : EntryTuple O → ℝ) (τ : Fin n → Pt s .euclidean → ℝ) (i : Fin n)
    (x : Pt s .euclidean → ℝ) : ℝ := zeroExtend B (update τ i x)
def componentComplexify (B : EntryTuple O → ℝ) (τ : Fin n → Pt s .euclidean → ℝ) (i : Fin n)
    (k : Pt s .euclidean → ℂ) : ℂ :=
  (entryEval B τ i (reIm false k) : ℂ) + Complex.I * (entryEval B τ i (reIm true k) : ℂ)
theorem componentComplexify_linComb (hS : ReImRegular s) {B : EntryTuple O → ℝ}
    (hB : IsMultilinearOnComponents B) {τ : Fin n → Pt s .euclidean → ℝ}
    (hτ : ∀ j, τ j ∈ entrySpace O j) (i : Fin n) {u v : Pt s .euclidean → ℂ}
    (hu : u ∈ complexEntrySpace O i) (hv : v ∈ complexEntrySpace O i) (a b : ℂ) :
    componentComplexify B τ i (a • u + b • v) =
      a * componentComplexify B τ i u + b * componentComplexify B τ i v := by
  have u0 := reIm_mem hS hu false
  have u1 := reIm_mem hS hu true
  have v0 := reIm_mem hS hv false
  have v1 := reIm_mem hS hv true
  have hre : entryEval B τ i (reIm false (a • u + b • v)) =
      a.re * entryEval B τ i (reIm false u) - a.im * entryEval B τ i (reIm true u) +
        (b.re * entryEval B τ i (reIm false v) - b.im * entryEval B τ i (reIm true v)) := by
    rw [reIm_false_linComb]
    simp only [entryEval]
    rw [zeroExtend_update_linComb hB hτ i (linComb_mem_componentSpace u0 u1 _ _)
        (linComb_mem_componentSpace v0 v1 _ _), zeroExtend_update_linComb hB hτ i u0 u1,
      zeroExtend_update_linComb hB hτ i v0 v1]
    ring
  have him : entryEval B τ i (reIm true (a • u + b • v)) =
      a.re * entryEval B τ i (reIm true u) + a.im * entryEval B τ i (reIm false u) +
        (b.re * entryEval B τ i (reIm true v) + b.im * entryEval B τ i (reIm false v)) := by
    rw [reIm_true_linComb]
    simp only [entryEval]
    rw [zeroExtend_update_linComb hB hτ i (linComb_mem_componentSpace u1 u0 _ _)
        (linComb_mem_componentSpace v1 v0 _ _), zeroExtend_update_linComb hB hτ i u1 u0,
      zeroExtend_update_linComb hB hτ i v1 v0]
    ring
  simp only [componentComplexify]
  rw [hre, him]
  generalize entryEval B τ i (reIm false u) = p0
  generalize entryEval B τ i (reIm true u) = p1
  generalize entryEval B τ i (reIm false v) = q0
  generalize entryEval B τ i (reIm true v) = q1
  apply Complex.ext <;> simp
def unitFactor (b : Bool) : ℂ := cond b Complex.I 1
def signWeight (ε : Fin n → Bool) : ℂ := ∏ j, unitFactor (ε j)
def reImTuple (ε : Fin n → Bool) (h : Fin n → Pt s .euclidean → ℂ) :
    Fin n → Pt s .euclidean → ℝ := fun j => reIm (ε j) (h j)
def summand (B : EntryTuple O → ℝ) (h : Fin n → Pt s .euclidean → ℂ) (ε : Fin n → Bool) : ℂ :=
  signWeight ε * (zeroExtend B (reImTuple ε h) : ℂ)
def complexification (B : EntryTuple O → ℝ) (h : Fin n → Pt s .euclidean → ℂ) : ℂ :=
  ∑ ε, summand B h ε
def toggle (i : Fin n) (ε : Fin n → Bool) : Fin n → Bool := update ε i (!ε i)
theorem toggle_toggle (i : Fin n) (ε : Fin n → Bool) : toggle i (toggle i ε) = ε := by
  funext j
  by_cases h : j = i
  · subst h
    simp [toggle]
  · simp [toggle, update_of_ne h]
theorem toggle_ne (i : Fin n) (ε : Fin n → Bool) : toggle i ε ≠ ε := by
  intro h
  have := congrFun h i
  simp [toggle] at this
def signWeightErase (i : Fin n) (ε : Fin n → Bool) : ℂ :=
  ∏ j ∈ Finset.univ.erase i, unitFactor (ε j)
theorem signWeight_eq_mul (i : Fin n) (ε : Fin n → Bool) :
    signWeight ε = unitFactor (ε i) * signWeightErase i ε :=
  (Finset.mul_prod_erase Finset.univ (fun j => unitFactor (ε j)) (Finset.mem_univ i)).symm
theorem signWeightErase_toggle (i : Fin n) (ε : Fin n → Bool) :
    signWeightErase i (toggle i ε) = signWeightErase i ε := by
  refine Finset.prod_congr rfl fun j hj => ?_
  simp [toggle, update_of_ne (Finset.ne_of_mem_erase hj)]
theorem reImTuple_update (i : Fin n) (ε : Fin n → Bool) (h : Fin n → Pt s .euclidean → ℂ)
    (k : Pt s .euclidean → ℂ) :
    reImTuple ε (update h i k) = update (reImTuple ε h) i (reIm (ε i) k) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [reImTuple]
  · simp [reImTuple, update_of_ne hj]
theorem reImTuple_toggle_update (i : Fin n) (ε : Fin n → Bool) (h : Fin n → Pt s .euclidean → ℂ)
    (k : Pt s .euclidean → ℂ) :
    reImTuple (toggle i ε) (update h i k) = update (reImTuple ε h) i (reIm (!ε i) k) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [reImTuple, toggle]
  · simp [reImTuple, toggle, update_of_ne hj]
theorem summand_add_toggle (B : EntryTuple O → ℝ) (i : Fin n) (ε : Fin n → Bool)
    (h : Fin n → Pt s .euclidean → ℂ) (k : Pt s .euclidean → ℂ) :
    summand B (update h i k) ε + summand B (update h i k) (toggle i ε) =
      signWeightErase i ε * componentComplexify B (reImTuple ε h) i k := by
  have htog : toggle i ε i = !ε i := by simp [toggle]
  simp only [summand, componentComplexify, entryEval]
  rw [reImTuple_update, reImTuple_toggle_update, signWeight_eq_mul i ε,
    signWeight_eq_mul i (toggle i ε), signWeightErase_toggle, htog]
  cases ε i <;> simp [unitFactor] <;> ring
theorem complexification_linComb (hS : ReImRegular s) {B : EntryTuple O → ℝ}
    (hB : IsMultilinearOnComponents B) {h : Fin n → Pt s .euclidean → ℂ}
    (hh : IsComplexComponentTuple O h) (i : Fin n) {u v : Pt s .euclidean → ℂ}
    (hu : u ∈ complexEntrySpace O i) (hv : v ∈ complexEntrySpace O i) (a b : ℂ) :
    complexification B (update h i (a • u + b • v)) =
      a * complexification B (update h i u) + b * complexification B (update h i v) := by
  rw [← sub_eq_zero]
  simp only [complexification, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_involution (fun ε _ => toggle i ε) (fun ε _ => ?_)
    (fun ε _ _ => toggle_ne i ε) (fun _ _ => Finset.mem_univ _) (fun ε _ => toggle_toggle i ε)
  have hτ : ∀ j, reImTuple ε h j ∈ entrySpace O j := fun j => reIm_mem hS (hh j) _
  have e1 := summand_add_toggle B i ε h (a • u + b • v)
  have e2 := summand_add_toggle B i ε h u
  have e3 := summand_add_toggle B i ε h v
  have e4 := componentComplexify_linComb hS hB hτ i hu hv a b
  rw [e4] at e1
  linear_combination e1 - a * e2 - b * e3
theorem norm_unitFactor (b : Bool) : ‖unitFactor b‖ = 1 := by
  cases b <;> simp [unitFactor]
theorem norm_signWeight (ε : Fin n → Bool) : ‖signWeight ε‖ = 1 := by
  simp [signWeight, norm_unitFactor]
theorem complexification_bound (hS : ReImRegular s) {c : ℝ} {B : EntryTuple O → ℝ}
    (hb : IsGradNormBounded c B) {h : Fin n → Pt s .euclidean → ℂ}
    (hh : IsComplexComponentTuple O h) :
    ENNReal.ofReal ‖complexification B h‖ ≤
      ENNReal.ofReal (2 ^ n * c) * ∏ i, c1GradNorm (h i) := by
  have hterm : ∀ ε : Fin n → Bool, ENNReal.ofReal ‖summand B h ε‖ ≤
      ENNReal.ofReal c * ∏ i, c1GradNorm (h i) := by
    intro ε
    have hτ : ∀ j, reImTuple ε h j ∈ entrySpace O j := fun j => reIm_mem hS (hh j) _
    have h1 : ‖summand B h ε‖ = |B fun i => ⟨reImTuple ε h i, hτ i⟩| := by
      simp [summand, norm_signWeight, zeroExtend_of_mem B hτ]
    rw [h1]
    refine (hb _).trans ?_
    refine mul_le_mul_right ?_ _
    exact Finset.prod_le_prod' fun i _ => c1GradNorm_reIm_le hS (hh i).1 (ε i)
  calc ENNReal.ofReal ‖complexification B h‖
      ≤ ENNReal.ofReal (∑ ε, ‖summand B h ε‖) :=
        ENNReal.ofReal_le_ofReal (norm_sum_le _ _)
    _ = ∑ ε, ENNReal.ofReal ‖summand B h ε‖ :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _
    _ ≤ ∑ _ε : Fin n → Bool, ENNReal.ofReal c * ∏ i, c1GradNorm (h i) :=
        Finset.sum_le_sum fun ε _ => hterm ε
    _ = ENNReal.ofReal (2 ^ n * c) * ∏ i, c1GradNorm (h i) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp [mul_assoc]
theorem complexification_ofReal {B : EntryTuple O → ℝ} (hB : IsMultilinearOnComponents B)
    (g : EntryTuple O) : complexification B (fun i x => ((g i).1 x : ℂ)) = (B g : ℂ) := by
  have hfalse : ∀ i, reIm false (fun x => ((g i).1 x : ℂ)) = (g i).1 := fun i => by
    funext x
    simp [reIm]
  have htrue : ∀ i, reIm true (fun x => ((g i).1 x : ℂ)) = 0 := fun i => by
    funext x
    simp [reIm]
  have hmem : ∀ (b : Bool) (i : Fin n), reIm b (fun x => ((g i).1 x : ℂ)) ∈ entrySpace O i := by
    intro b i
    cases b
    · rw [hfalse]
      exact (g i).2
    · rw [htrue]
      simpa using linComb_mem_componentSpace (g i).2 (g i).2 0 0
  rw [complexification, Finset.sum_eq_single (fun _ => false)]
  · have h1 : (fun j => reImTuple (fun _ => false) (fun i x => ((g i).1 x : ℂ)) j) =
        fun j => (g j).1 :=
      funext hfalse
    have h2 : ∀ j, (g j).1 ∈ entrySpace O j := fun j => (g j).2
    simp only [summand, signWeight, unitFactor, cond_false, Finset.prod_const_one, one_mul]
    have h3 : reImTuple (fun _ => false) (fun i x => ((g i).1 x : ℂ)) = fun j => (g j).1 := h1
    rw [h3, zeroExtend_of_mem B h2]
  · intro ε _ hε
    obtain ⟨i, hi⟩ : ∃ i, ε i = true := by
      by_contra hn
      exact hε (funext fun j => by
        by_contra hj
        exact hn ⟨j, by simpa using hj⟩)
    have hτ : ∀ j, reImTuple ε (fun i x => ((g i).1 x : ℂ)) j ∈ entrySpace O j :=
      fun j => hmem _ j
    have hz := zeroExtend_update_linComb hB hτ i (hτ i) (hτ i) 0 0
    have hi0 : reImTuple ε (fun i x => ((g i).1 x : ℂ)) i = 0 := by
      simp only [reImTuple, hi]
      exact htrue i
    have hu : update (reImTuple ε (fun i x => ((g i).1 x : ℂ))) i
        ((0 : ℝ) • reImTuple ε (fun i x => ((g i).1 x : ℂ)) i +
          (0 : ℝ) • reImTuple ε (fun i x => ((g i).1 x : ℂ)) i) =
        reImTuple ε (fun i x => ((g i).1 x : ℂ)) := by
      rw [hi0]
      simp only [smul_zero, add_zero]
      rw [← hi0]
      exact update_eq_self _ _
    rw [hu] at hz
    have hz0 : zeroExtend B (reImTuple ε fun i x => ((g i).1 x : ℂ)) = 0 := by
      rw [hz, zero_mul, add_zero]
    rw [summand, hz0, Complex.ofReal_zero, mul_zero]
  · intro hn
    exact absurd (Finset.mem_univ _) hn
theorem existsComplexExtension (hSharp : GradientC1Bounds.Statement) :
    ComplexExtension.ExistsComplexExtension := by
  intro s n ρ c O B _ _ hB hb
  have hS : ReImRegular s := fun g hg =>
    have h := (hSharp s .euclidean).1 g g hg hg
    ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  refine ⟨complexification B, ?_, ?_, complexification_ofReal hB⟩
  · intro h hh i u v hu hv a b
    exact complexification_linComb hS hB hh i hu hv a b
  · intro h hh
    exact complexification_bound hS hb hh
end YangMills.Construction.AmbientPoints.ComplexExtensionProof

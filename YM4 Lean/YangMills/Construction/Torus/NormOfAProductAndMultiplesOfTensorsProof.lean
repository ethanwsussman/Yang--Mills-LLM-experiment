import YangMills.Construction.Torus.CoveringMapOpenAndCompactSetsAndDerivativesOfTuples
import YangMills.Construction.Torus.NormOfAProductAndMultiplesOfTensors
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
open YangMills.Construction.AmbientPoints
noncomputable section
namespace YangMills.Construction.ProductNorms
section RealCoordinates
variable {d : ℕ}
theorem hasLineDerivAt_add_pi_single {j : Fin d} {f g : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : LineDifferentiableAt ℝ f x (Pi.single j 1))
    (hg : LineDifferentiableAt ℝ g x (Pi.single j 1)) :
    HasLineDerivAt ℝ (fun y => f y + g y) (partialDeriv j f x + partialDeriv j g x) x
      (Pi.single j 1) := by
  have h1 := hf.hasLineDerivAt
  have h2 := hg.hasLineDerivAt
  unfold HasLineDerivAt at *
  exact h1.add h2
theorem hasLineDerivAt_mul_pi_single {j : Fin d} {f g : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : LineDifferentiableAt ℝ f x (Pi.single j 1))
    (hg : LineDifferentiableAt ℝ g x (Pi.single j 1)) :
    HasLineDerivAt ℝ (fun y => f y * g y)
      (partialDeriv j f x * g x + f x * partialDeriv j g x) x (Pi.single j 1) := by
  have h1 := hf.hasLineDerivAt
  have h2 := hg.hasLineDerivAt
  unfold HasLineDerivAt at *
  have h3 := h1.mul h2
  simp only [zero_smul, add_zero] at h3
  exact h3
theorem partialDeriv_add {j : Fin d} {f g : (Fin d → ℝ) → ℂ}
    (hf : ∀ x, LineDifferentiableAt ℝ f x (Pi.single j 1))
    (hg : ∀ x, LineDifferentiableAt ℝ g x (Pi.single j 1)) :
    partialDeriv j (fun y => f y + g y) =
      fun x => partialDeriv j f x + partialDeriv j g x :=
  funext fun x => (hasLineDerivAt_add_pi_single (hf x) (hg x)).lineDeriv
theorem partialDeriv_mul {j : Fin d} {f g : (Fin d → ℝ) → ℂ}
    (hf : ∀ x, LineDifferentiableAt ℝ f x (Pi.single j 1))
    (hg : ∀ x, LineDifferentiableAt ℝ g x (Pi.single j 1)) :
    partialDeriv j (fun y => f y * g y) =
      fun x => partialDeriv j f x * g x + f x * partialDeriv j g x :=
  funext fun x => (hasLineDerivAt_mul_pi_single (hf x) (hg x)).lineDeriv
theorem continuousPartialsUpTo_add {n : ℕ} {f g : (Fin d → ℝ) → ℂ}
    (hf : ContinuousPartialsUpTo univ n f) (hg : ContinuousPartialsUpTo univ n g) :
    ContinuousPartialsUpTo univ n (fun y => f y + g y) := by
  induction n generalizing f g with
  | zero => exact ContinuousOn.add hf hg
  | succ n ih =>
    refine ⟨hf.1.add hg.1, fun j => ⟨fun x _ => ?_, ?_⟩⟩
    · exact (hasLineDerivAt_add_pi_single ((hf.2 j).1 x (mem_univ x))
        ((hg.2 j).1 x (mem_univ x))).lineDifferentiableAt
    · rw [partialDeriv_add (fun x => (hf.2 j).1 x (mem_univ x))
        (fun x => (hg.2 j).1 x (mem_univ x))]
      exact ih (hf.2 j).2 (hg.2 j).2
theorem continuousPartialsUpTo_mul {n : ℕ} {f g : (Fin d → ℝ) → ℂ}
    (hf : ContinuousPartialsUpTo univ n f) (hg : ContinuousPartialsUpTo univ n g) :
    ContinuousPartialsUpTo univ n (fun y => f y * g y) := by
  induction n generalizing f g with
  | zero => exact ContinuousOn.mul hf hg
  | succ n ih =>
    refine ⟨hf.1.mul hg.1, fun j => ⟨fun x _ => ?_, ?_⟩⟩
    · exact (hasLineDerivAt_mul_pi_single ((hf.2 j).1 x (mem_univ x))
        ((hg.2 j).1 x (mem_univ x))).lineDifferentiableAt
    · rw [partialDeriv_mul (fun x => (hf.2 j).1 x (mem_univ x))
        (fun x => (hg.2 j).1 x (mem_univ x))]
      exact continuousPartialsUpTo_add (ih (hf.2 j).2 hg.of_succ) (ih hf.of_succ (hg.2 j).2)
def iteratedPartialAlong (w : List (Fin d)) (f : (Fin d → ℝ) → ℂ) : (Fin d → ℝ) → ℂ :=
  w.foldl (fun g j => partialDeriv j g) f
theorem iteratedPartialAlong_cons (j : Fin d) (w : List (Fin d)) (f : (Fin d → ℝ) → ℂ) :
    iteratedPartialAlong (j :: w) f = iteratedPartialAlong w (partialDeriv j f) := rfl
theorem iteratedPartialAlong_append (w w' : List (Fin d)) (f : (Fin d → ℝ) → ℂ) :
    iteratedPartialAlong (w ++ w') f = iteratedPartialAlong w' (iteratedPartialAlong w f) := by
  simp [iteratedPartialAlong, List.foldl_append]
theorem iteratedPartialAlong_replicate (n : ℕ) (j : Fin d) (f : (Fin d → ℝ) → ℂ) :
    iteratedPartialAlong (List.replicate n j) f = (partialDeriv j)^[n] f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, iteratedPartialAlong_cons, ih]; rfl
theorem iteratedPartialAlong_add (w : List (Fin d)) {f g : (Fin d → ℝ) → ℂ}
    (hf : ContinuousPartialsUpTo univ w.length f)
    (hg : ContinuousPartialsUpTo univ w.length g) :
    iteratedPartialAlong w (fun y => f y + g y) =
      fun x => iteratedPartialAlong w f x + iteratedPartialAlong w g x := by
  induction w generalizing f g with
  | nil => rfl
  | cons j w ih =>
    have hf' : ContinuousPartialsUpTo univ (w.length + 1) f := hf
    have hg' : ContinuousPartialsUpTo univ (w.length + 1) g := hg
    rw [iteratedPartialAlong_cons, partialDeriv_add (fun x => (hf'.2 j).1 x (mem_univ x))
      (fun x => (hg'.2 j).1 x (mem_univ x))]
    exact ih (hf'.2 j).2 (hg'.2 j).2
theorem ofReal_norm_iteratedPartialAlong_mul_le (w : List (Fin d)) {f g : (Fin d → ℝ) → ℂ}
    (hf : ContinuousPartialsUpTo univ w.length f)
    (hg : ContinuousPartialsUpTo univ w.length g) (x : Fin d → ℝ) (a b : ℝ≥0∞)
    (ha : ∀ u, u.Sublist w → ENNReal.ofReal ‖iteratedPartialAlong u f x‖ ≤ a)
    (hb : ∀ u, u.Sublist w → ENNReal.ofReal ‖iteratedPartialAlong u g x‖ ≤ b) :
    ENNReal.ofReal ‖iteratedPartialAlong w (fun y => f y * g y) x‖ ≤ 2 ^ w.length * a * b := by
  induction w generalizing f g with
  | nil =>
    have h1 := ha [] (List.Sublist.refl _)
    have h2 := hb [] (List.Sublist.refl _)
    change ENNReal.ofReal ‖f x * g x‖ ≤ 2 ^ 0 * a * b
    rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _), pow_zero, one_mul]
    exact mul_le_mul' h1 h2
  | cons j w ih =>
    have hf' : ContinuousPartialsUpTo univ (w.length + 1) f := hf
    have hg' : ContinuousPartialsUpTo univ (w.length + 1) g := hg
    have hP := continuousPartialsUpTo_mul (hf'.2 j).2 hg'.of_succ
    have hQ := continuousPartialsUpTo_mul hf'.of_succ (hg'.2 j).2
    have h1 := ih (hf'.2 j).2 hg'.of_succ
      (fun u hu => ha (j :: u) (List.Sublist.cons_cons j hu))
      (fun u hu => hb u (List.Sublist.cons j hu))
    have h2 := ih hf'.of_succ (hg'.2 j).2
      (fun u hu => ha u (List.Sublist.cons j hu))
      (fun u hu => hb (j :: u) (List.Sublist.cons_cons j hu))
    rw [iteratedPartialAlong_cons, partialDeriv_mul (fun x => (hf'.2 j).1 x (mem_univ x))
      (fun x => (hg'.2 j).1 x (mem_univ x)), iteratedPartialAlong_add w hP hQ]
    calc ENNReal.ofReal ‖iteratedPartialAlong w (fun y => partialDeriv j f y * g y) x +
            iteratedPartialAlong w (fun y => f y * partialDeriv j g y) x‖
        ≤ ENNReal.ofReal ‖iteratedPartialAlong w (fun y => partialDeriv j f y * g y) x‖ +
            ENNReal.ofReal ‖iteratedPartialAlong w (fun y => f y * partialDeriv j g y) x‖ :=
          (ENNReal.ofReal_le_ofReal (norm_add_le _ _)).trans ENNReal.ofReal_add_le
      _ ≤ 2 ^ w.length * a * b + 2 ^ w.length * a * b := add_le_add h1 h2
      _ = 2 ^ (j :: w).length * a * b := by
          rw [List.length_cons, pow_succ]
          ring
def indexWord (α : PowerSeries.MultiIndex d) : List (Fin d) → List (Fin d)
  | [] => []
  | j :: l => indexWord α l ++ List.replicate (α j) j
theorem foldr_iterate_eq_iteratedPartialAlong (α : PowerSeries.MultiIndex d) (l : List (Fin d))
    (f : (Fin d → ℝ) → ℂ) :
    l.foldr (fun j g => (partialDeriv j)^[α j] g) f = iteratedPartialAlong (indexWord α l) f := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldr_cons, ih, indexWord, iteratedPartialAlong_append, iteratedPartialAlong_replicate]
theorem iteratedPartial_eq_iteratedPartialAlong (α : PowerSeries.MultiIndex d)
    (f : (Fin d → ℝ) → ℂ) :
    iteratedPartial α f = iteratedPartialAlong (indexWord α (List.finRange d)) f :=
  foldr_iterate_eq_iteratedPartialAlong α _ f
theorem length_indexWord (α : PowerSeries.MultiIndex d) (l : List (Fin d)) :
    (indexWord α l).length = (l.map α).sum := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [indexWord, List.length_append, List.length_replicate, List.map_cons,
      List.sum_cons, ih]
    omega
theorem length_indexWord_finRange (α : PowerSeries.MultiIndex d) :
    (indexWord α (List.finRange d)).length = α.order := by
  rw [length_indexWord, PowerSeries.MultiIndex.order, Fin.sum_univ_def]
theorem indexWord_congr {α β : PowerSeries.MultiIndex d} (l : List (Fin d))
    (h : ∀ i ∈ l, α i = β i) : indexWord α l = indexWord β l := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [indexWord]
    rw [ih fun i hi => h i (List.mem_cons_of_mem j hi), h j List.mem_cons_self]
theorem exists_le_of_sublist_indexWord (α : PowerSeries.MultiIndex d) (l : List (Fin d))
    (hl : l.Nodup) (u : List (Fin d)) (hu : u.Sublist (indexWord α l)) :
    ∃ β : PowerSeries.MultiIndex d, (∀ i, β i ≤ α i) ∧ u = indexWord β l := by
  induction l generalizing u with
  | nil =>
    refine ⟨0, fun _ => Nat.zero_le _, ?_⟩
    simpa [indexWord] using hu
  | cons j l ih =>
    obtain ⟨hj, hl'⟩ := List.nodup_cons.mp hl
    obtain ⟨u₁, u₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp hu
    obtain ⟨k, hk, rfl⟩ := List.sublist_replicate_iff.mp h₂
    obtain ⟨β, hβ, rfl⟩ := ih hl' u₁ h₁
    refine ⟨Function.update β j k, fun i => ?_, ?_⟩
    · by_cases hi : i = j
      · subst hi
        simpa using hk
      · simpa [Function.update_of_ne hi] using hβ i
    · simp only [indexWord, Function.update_self]
      rw [indexWord_congr l fun i hi => ?_]
      rw [Function.update_of_ne]
      rintro rfl
      exact hj hi
theorem ofReal_norm_iteratedPartial_mul_le (α : PowerSeries.MultiIndex d) {f g : (Fin d → ℝ) → ℂ}
    (hf : ContinuousPartialsUpTo univ α.order f)
    (hg : ContinuousPartialsUpTo univ α.order g) (x : Fin d → ℝ) (a b : ℝ≥0∞)
    (ha : ∀ β : PowerSeries.MultiIndex d, (∀ i, β i ≤ α i) →
      ENNReal.ofReal ‖iteratedPartial β f x‖ ≤ a)
    (hb : ∀ β : PowerSeries.MultiIndex d, (∀ i, β i ≤ α i) →
      ENNReal.ofReal ‖iteratedPartial β g x‖ ≤ b) :
    ENNReal.ofReal ‖iteratedPartial α (fun y => f y * g y) x‖ ≤ 2 ^ α.order * a * b := by
  have hlen := length_indexWord_finRange α
  rw [iteratedPartial_eq_iteratedPartialAlong, ← hlen]
  refine ofReal_norm_iteratedPartialAlong_mul_le _ (hlen ▸ hf) (hlen ▸ hg) x a b ?_ ?_
  · intro u hu
    obtain ⟨β, hβ, rfl⟩ := exists_le_of_sublist_indexWord α _ (List.nodup_finRange d) u hu
    rw [← iteratedPartial_eq_iteratedPartialAlong]
    exact ha β hβ
  · intro u hu
    obtain ⟨β, hβ, rfl⟩ := exists_le_of_sublist_indexWord α _ (List.nodup_finRange d) u hu
    rw [← iteratedPartial_eq_iteratedPartialAlong]
    exact hb β hβ
end RealCoordinates
variable {s : Conventions.StandingParameters} {E : Ambient} {p : ℕ}
theorem continuousPartialsUpTo_comp_tupleProj {n : ℕ} {F : Tuple s E p → ℂ}
    (hF : IsCn (n : ℕ∞) F) :
    ContinuousPartialsUpTo univ n (F ∘ tupleProj s E p) :=
  ((isCnOn_coe_iff _ _ _).1 hF).2
theorem isCn_mul {n : ℕ} {F G : Tuple s E p → ℂ} (hF : IsCn (n : ℕ∞) F)
    (hG : IsCn (n : ℕ∞) G) : IsCn (n : ℕ∞) (fun y => F y * G y) :=
  (isCnOn_coe_iff _ _ _).2 ⟨isOpen_univ, continuousPartialsUpTo_mul
    (continuousPartialsUpTo_comp_tupleProj hF) (continuousPartialsUpTo_comp_tupleProj hG)⟩
theorem multiDeriv_tupleProj (hT : TupleDerivProps s E p) {n : ℕ} {F : Tuple s E p → ℂ}
    (hF : IsCn (n : ℕ∞) F) {α : PowerSeries.MultiIndex (4 * p)} (hα : α.order ≤ n)
    (x : Fin (4 * p) → ℝ) :
    multiDeriv α F (tupleProj s E p x) =
      iteratedPartial α (F ∘ tupleProj s E p) x :=
  congrFun (multiDeriv_comp_tupleProj
    ((hT (n : ℕ∞) F hF).1 α (by exact_mod_cast hα)).1.exists) x
theorem ofReal_norm_multiDeriv_mul_le (hT : TupleDerivProps s E p) {n : ℕ}
    {F G : Tuple s E p → ℂ} (hF : IsCn (n : ℕ∞) F) (hG : IsCn (n : ℕ∞) G)
    {α : PowerSeries.MultiIndex (4 * p)} (hα : α.order ≤ n) (y : Tuple s E p) (a b : ℝ≥0∞)
    (ha : ∀ β : PowerSeries.MultiIndex (4 * p), β.order ≤ n →
      ENNReal.ofReal ‖multiDeriv β F y‖ ≤ a)
    (hb : ∀ β : PowerSeries.MultiIndex (4 * p), β.order ≤ n →
      ENNReal.ofReal ‖multiDeriv β G y‖ ≤ b) :
    ENNReal.ofReal ‖multiDeriv α (fun y => F y * G y) y‖ ≤ 2 ^ n * a * b := by
  obtain ⟨x, rfl⟩ := tupleProj_surjective s E p y
  have horder : ∀ β : PowerSeries.MultiIndex (4 * p), (∀ i, β i ≤ α i) → β.order ≤ n :=
    fun β hβ => (Finset.sum_le_sum fun i _ => hβ i).trans hα
  rw [multiDeriv_tupleProj hT (isCn_mul hF hG) hα]
  have h := ofReal_norm_iteratedPartial_mul_le α
    ((continuousPartialsUpTo_comp_tupleProj hF).mono hα)
    ((continuousPartialsUpTo_comp_tupleProj hG).mono hα) x a b
    (fun β hβ => by
      rw [← multiDeriv_tupleProj hT hF (horder β hβ)]
      exact ha β (horder β hβ))
    (fun β hβ => by
      rw [← multiDeriv_tupleProj hT hG (horder β hβ)]
      exact hb β (horder β hβ))
  refine le_trans h ?_
  have h2 : (2 : ℝ≥0∞) ^ α.order ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hα
  exact mul_le_mul' (mul_le_mul' h2 le_rfl) le_rfl
theorem ofReal_norm_multiDeriv_le_cnNorm {n : ℕ} (F : Tuple s E p → ℂ)
    {β : PowerSeries.MultiIndex (4 * p)} (hβ : β.order ≤ n) (y : Tuple s E p) :
    ENNReal.ofReal ‖multiDeriv β F y‖ ≤ cnNorm n F :=
  le_iSup_of_le β (le_iSup_of_le hβ (le_iSup (fun y => ENNReal.ofReal ‖multiDeriv β F y‖) y))
theorem ofReal_norm_multiDeriv_le_cnNormOn {n : ℕ} {A : Set (Tuple s E p)} (G : Tuple s E p → ℂ)
    {β : PowerSeries.MultiIndex (4 * p)} (hβ : β.order ≤ n) {y : Tuple s E p} (hy : y ∈ A) :
    ENNReal.ofReal ‖multiDeriv β G y‖ ≤ cnNormOn n A G :=
  le_iSup_of_le β (le_iSup_of_le hβ (le_iSup₂_of_le y hy le_rfl))
theorem multiDeriv_eq_zero_of_notMem (hT : TupleDerivProps s E p) {n : ℕ}
    {F : Tuple s E p → ℂ} (hF : IsCn (n : ℕ∞) F) {A : Set (Tuple s E p)}
    (hA : SupportedIn F A) {β : PowerSeries.MultiIndex (4 * p)} (hβ : β.order ≤ n)
    {y : Tuple s E p} (hy : y ∉ A) : multiDeriv β F y = 0 := by
  by_contra h
  have hsupp := ((hT (n : ℕ∞) F hF).1 β (by exact_mod_cast hβ)).2.2.1
  exact hy (hA (hsupp (subset_closure h)))
theorem mul_tensorProd (hp : 1 ≤ p) (φ : Fin p → Pt s E → ℂ) (c : ℂ) :
    (fun y => c * tensorProd φ y) =
      tensorProd (Function.update φ ⟨0, hp⟩ (fun x => c * φ ⟨0, hp⟩ x)) := by
  funext y
  have h : ∀ i, Function.update φ ⟨0, hp⟩ (fun x => c * φ ⟨0, hp⟩ x) i (y i) =
      Function.update (fun i => φ i (y i)) ⟨0, hp⟩ (c * φ ⟨0, hp⟩ (y ⟨0, hp⟩)) i := by
    intro i
    by_cases hi : i = ⟨0, hp⟩
    · subst hi
      simp
    · simp [Function.update_of_ne hi]
  simp only [tensorProd, h]
  rw [Finset.prod_update_of_mem (Finset.mem_univ _), mul_assoc, Finset.sdiff_singleton_eq_erase,
    Finset.mul_prod_erase _ (fun i => φ i (y i)) (Finset.mem_univ _)]
theorem productBoundsClaim_holds (hTop : TupleTopology.Holds) : ProductBoundsClaim := by
  intro s E p hp n
  have hT : TupleDerivProps s E p := ((hTop s E).1 p hp).2.2.2.2
  refine ⟨?_, ?_, fun φ c => mul_tensorProd hp φ c⟩
  · intro F G hF hG _ _
    refine ⟨isCn_mul hF hG, iSup_le fun α => iSup_le fun hα => iSup_le fun y => ?_⟩
    exact ofReal_norm_multiDeriv_mul_le hT hF hG hα y _ _
      (fun β hβ => ofReal_norm_multiDeriv_le_cnNorm F hβ y)
      (fun β hβ => ofReal_norm_multiDeriv_le_cnNorm G hβ y)
  · intro F G A hF hG _ _ hsupp _
    refine ⟨isCn_mul hF hG, iSup_le fun α => iSup_le fun hα => iSup_le fun y => ?_⟩
    by_cases hy : y ∈ A
    · exact ofReal_norm_multiDeriv_mul_le hT hF hG hα y _ _
        (fun β hβ => ofReal_norm_multiDeriv_le_cnNorm F hβ y)
        (fun β hβ => ofReal_norm_multiDeriv_le_cnNormOn G hβ hy)
    · have h0 := ofReal_norm_multiDeriv_mul_le hT hF hG hα y 0 ⊤
        (fun β hβ => by rw [multiDeriv_eq_zero_of_notMem hT hF hsupp hβ hy]; simp)
        (fun _ _ => le_top)
      simp only [mul_zero, zero_mul] at h0
      exact h0.trans zero_le
end YangMills.Construction.ProductNorms

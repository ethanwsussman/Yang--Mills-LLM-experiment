import YangMills.Construction.Continuum.OperationsKeepTheSpacesProof
import YangMills.Construction.ConfigSpace.IteratedPartialRules
import YangMills.Construction.Continuum.OperationsOnTestFunctionsProof
import Mathlib
set_option autoImplicit false
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction.ConfigSpace
namespace PartialCalculus
variable {n : ℕ}
def coordDir (c : Fin n × Fin 4) : Config n := Pi.single c.1 (Pi.single c.2 1)
def partialIn (c : Fin n × Fin 4) (g : Config n → ℂ) : Config n → ℂ :=
  coordPartial c.1 c.2 g
theorem partialIn_eq_fderiv {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (c : Fin n × Fin 4) :
    partialIn c g = fun x => fderiv ℝ g x (coordDir c) :=
  funext fun x => ((hg.differentiable (by simp)) x).lineDeriv_eq_fderiv
theorem contDiff_partialIn {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (c : Fin n × Fin 4) :
    ContDiff ℝ ∞ (partialIn c g) := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzOps.contDiff_dirPartial <;> assumption
theorem partialIn_comm {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (a b : Fin n × Fin 4) :
    partialIn a (partialIn b g) = partialIn b (partialIn a g) := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzOps.dirPartial_comm <;> assumption
theorem partialIn_add {g h : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (c : Fin n × Fin 4) : partialIn c (g + h) = partialIn c g + partialIn c h := by
  have hgh : ContDiff ℝ ∞ (g + h) := hg.add hh
  rw [partialIn_eq_fderiv hg, partialIn_eq_fderiv hh, partialIn_eq_fderiv hgh]
  funext x
  have h1 := (hg.differentiable (by simp) x).hasFDerivAt
  have h2 := (hh.differentiable (by simp) x).hasFDerivAt
  have h3 : HasFDerivAt (g + h) _ x := h1.add h2
  rw [h3.fderiv]
  simp
theorem partialIn_smul {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (k : ℂ) (c : Fin n × Fin 4) :
    partialIn c (k • g) = k • partialIn c g := by
  have hk : ContDiff ℝ ∞ (k • g) := contDiff_const.smul hg
  rw [partialIn_eq_fderiv hg, partialIn_eq_fderiv hk]
  funext x
  have h1 := (hg.differentiable (by simp) x).hasFDerivAt
  have h3 : HasFDerivAt (fun y => k * g y) _ x := h1.const_mul k
  have h4 : (k • g) = fun y => k * g y := rfl
  rw [h4, h3.fderiv]
  simp
theorem partialIn_mul {f g : Config n → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (c : Fin n × Fin 4) :
    partialIn c (fun y => f y * g y) =
      (fun y => partialIn c f y * g y) + fun y => f y * partialIn c g y := by
  have hfg : ContDiff ℝ ∞ (fun y => f y * g y) := hf.mul hg
  rw [partialIn_eq_fderiv hf, partialIn_eq_fderiv hg, partialIn_eq_fderiv hfg]
  funext x
  have h1 := (hf.differentiable (by simp) x).hasFDerivAt
  have h2 := (hg.differentiable (by simp) x).hasFDerivAt
  have h3 : HasFDerivAt (fun y => f y * g y) _ x := h1.mul h2
  rw [h3.fderiv]
  simp
  ring
theorem partialIn_eventuallyEq {g h : Config n → ℂ} {x : Config n} (e : g =ᶠ[𝓝 x] h)
    (c : Fin n × Fin 4) : partialIn c g =ᶠ[𝓝 x] partialIn c h :=
  e.eventuallyEq_nhds.mono fun _ hy => hy.lineDeriv_eq
def derivAlong (l : List (Fin n × Fin 4)) (g : Config n → ℂ) : Config n → ℂ :=
  l.foldr partialIn g
theorem derivAlong_cons (c : Fin n × Fin 4) (l : List (Fin n × Fin 4)) (g : Config n → ℂ) :
    derivAlong (c :: l) g = partialIn c (derivAlong l g) := rfl
theorem derivAlong_append (l l' : List (Fin n × Fin 4)) (g : Config n → ℂ) :
    derivAlong (l ++ l') g = derivAlong l (derivAlong l' g) := by
  simp [derivAlong, List.foldr_append]
theorem contDiff_derivAlong {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (l : List (Fin n × Fin 4)) :
    ContDiff ℝ ∞ (derivAlong l g) := by
  induction l with
  | nil => exact hg
  | cons c l ih => exact contDiff_partialIn ih c
theorem derivAlong_perm {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) {l l' : List (Fin n × Fin 4)}
    (h : l.Perm l') : derivAlong l g = derivAlong l' g := by
  induction h with
  | nil => rfl
  | cons c _ ih => rw [derivAlong_cons, derivAlong_cons, ih]
  | swap a b l => exact partialIn_comm (contDiff_derivAlong hg l) b a
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
theorem derivAlong_add {g h : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (l : List (Fin n × Fin 4)) : derivAlong l (g + h) = derivAlong l g + derivAlong l h := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [derivAlong_cons, ih, partialIn_add (contDiff_derivAlong hg l) (contDiff_derivAlong hh l)]
    rfl
theorem derivAlong_smul {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (k : ℂ)
    (l : List (Fin n × Fin 4)) : derivAlong l (k • g) = k • derivAlong l g := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [derivAlong_cons, ih, partialIn_smul (contDiff_derivAlong hg l)]
    rfl
theorem derivAlong_eventuallyEq {g h : Config n → ℂ} {x : Config n} (e : g =ᶠ[𝓝 x] h)
    (l : List (Fin n × Fin 4)) : derivAlong l g =ᶠ[𝓝 x] derivAlong l h := by
  induction l with
  | nil => exact e
  | cons c l ih => exact partialIn_eventuallyEq ih c
def coordList (α : MultiIndex n) : List (Fin n × Fin 4) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange 4).flatMap fun μ => List.replicate (α i μ) (i, μ)
theorem foldr_flatMap_eq {A B C : Type*} (f : B → C → C) (init : C) (l : List A) (t : A → List B) :
    (l.flatMap t).foldr f init = l.foldr (fun a acc => (t a).foldr f acc) init := by apply _root_.YangMills.Construction.TestFunctionOps.list_foldr_flatMap <;> assumption
theorem foldr_replicate_eq {B C : Type*} (f : B → C → C) (init : C) (m : ℕ) (a : B) :
    (List.replicate m a).foldr f init = (f a)^[m] init := by apply _root_.YangMills.Construction.TestFunctionOps.list_foldr_replicate <;> assumption
theorem iteratedPartial_eq_derivAlong (α : MultiIndex n) (g : Config n → ℂ) :
    iteratedPartial α g = derivAlong (coordList α) g := by
  unfold derivAlong coordList iteratedPartial
  rw [foldr_flatMap_eq]
  simp only [foldr_flatMap_eq, foldr_replicate_eq]
  rfl
theorem count_coordList (α : MultiIndex n) (c : Fin n × Fin 4) :
    (coordList α).count c = α c.1 c.2 := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzOps.count_indexList <;> assumption
def countIndex (l : List (Fin n × Fin 4)) : MultiIndex n := fun i μ => l.count (i, μ)
theorem length_coordList (α : MultiIndex n) : (coordList α).length = α.order := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzOps.length_indexList <;> assumption
theorem perm_coordList_countIndex (l : List (Fin n × Fin 4)) :
    l.Perm (coordList (countIndex l)) := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzOps.perm_indexList <;> assumption
theorem order_countIndex (l : List (Fin n × Fin 4)) : (countIndex l).order = l.length := by
  rw [← length_coordList, (perm_coordList_countIndex l).length_eq]
theorem derivAlong_eq_iteratedPartial {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g)
    (l : List (Fin n × Fin 4)) : derivAlong l g = iteratedPartial (countIndex l) g := by
  rw [iteratedPartial_eq_derivAlong]
  exact derivAlong_perm hg (perm_coordList_countIndex l)
theorem norm_derivAlong_mul_le (x : Config n) (a b : ℝ) (L : List (Fin n × Fin 4)) :
    ∀ {f g : Config n → ℂ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      (∀ s : List (Fin n × Fin 4), s.length ≤ L.length → ‖derivAlong s f x‖ ≤ a) →
      (∀ s : List (Fin n × Fin 4), s.length ≤ L.length → ‖derivAlong s g x‖ ≤ b) →
      ‖derivAlong L (fun y => f y * g y) x‖ ≤ 2 ^ L.length * a * b := by
  induction L using List.reverseRecOn with
  | nil =>
    intro f g _ _ hf hg
    have h1 := hf [] le_rfl
    have h2 := hg [] le_rfl
    have ha : 0 ≤ a := (norm_nonneg _).trans h1
    simp only [derivAlong, List.foldr_nil] at h1 h2 ⊢
    simpa [norm_mul] using mul_le_mul h1 h2 (norm_nonneg _) ha
  | append_singleton L c ih =>
    intro f g hf hg bf bg
    have hf' := contDiff_partialIn hf c
    have hg' := contDiff_partialIn hg c
    have hlen : (L ++ [c]).length = L.length + 1 := by simp
    have shift : ∀ (u : Config n → ℂ) (s : List (Fin n × Fin 4)),
        derivAlong s (partialIn c u) = derivAlong (s ++ [c]) u := fun u s => by
      rw [derivAlong_append]
      rfl
    have b₁ := ih hf' hg
      (fun s hs => by
        rw [shift]
        exact bf _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega))
      (fun s hs => bg s (by omega))
    have b₂ := ih hf hg'
      (fun s hs => bf s (by omega))
      (fun s hs => by
        rw [shift]
        exact bg _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega))
    have hsplit : derivAlong (L ++ [c]) (fun y => f y * g y) =
        derivAlong L (fun y => partialIn c f y * g y) +
          derivAlong L (fun y => f y * partialIn c g y) := by
      rw [← shift, partialIn_mul hf hg, derivAlong_add (hf'.mul hg) (hf.mul hg')]
    rw [hsplit, hlen, pow_succ]
    calc ‖(derivAlong L (fun y => partialIn c f y * g y) +
            derivAlong L (fun y => f y * partialIn c g y)) x‖
        ≤ ‖derivAlong L (fun y => partialIn c f y * g y) x‖ +
            ‖derivAlong L (fun y => f y * partialIn c g y) x‖ := norm_add_le _ _
      _ ≤ 2 ^ L.length * a * b + 2 ^ L.length * a * b := add_le_add b₁ b₂
      _ = 2 ^ L.length * 2 * a * b := by ring
end PartialCalculus
open PartialCalculus in
theorem iteratedPartialRules_holds : IteratedPartialRules := by
  intro n
  have hadd : ∀ (α : MultiIndex n) (g h : Config n → ℂ), ContDiff ℝ ∞ g → ContDiff ℝ ∞ h →
      iteratedPartial α (g + h) = iteratedPartial α g + iteratedPartial α h := by
    intro α g h hg hh
    simp only [iteratedPartial_eq_derivAlong]
    exact derivAlong_add hg hh _
  have hsmul : ∀ (α : MultiIndex n) (c : ℂ) (g : Config n → ℂ), ContDiff ℝ ∞ g →
      iteratedPartial α (c • g) = c • iteratedPartial α g := by
    intro α c g hg
    simp only [iteratedPartial_eq_derivAlong]
    exact derivAlong_smul hg c _
  refine ⟨?_, hadd, ?_, hsmul, ?_, ?_⟩
  · intro α g hg
    rw [iteratedPartial_eq_derivAlong]
    exact contDiff_derivAlong hg _
  · intro ι s F α hF
    classical
    induction s using Finset.induction_on with
    | empty =>
      have h0 : ContDiff ℝ ∞ (0 : Config n → ℂ) := contDiff_const
      have := hsmul α 0 0 h0
      simpa using this
    | insert i s hi ih =>
      have hFi := hF i (Finset.mem_insert_self i s)
      have hFs : ∀ j ∈ s, ContDiff ℝ ∞ (F j) := fun j hj => hF j (Finset.mem_insert_of_mem hj)
      have hsum : ContDiff ℝ ∞ (∑ j ∈ s, F j) := by
        have := ContDiff.sum (𝕜 := ℝ) (n := ∞) (s := s) (f := F) hFs
        have e : (∑ j ∈ s, F j) = fun x => ∑ j ∈ s, F j x := by
          funext x
          simp
        rw [e]
        exact this
      rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd α _ _ hFi hsum, ih hFs]
  · intro α g h x e
    rw [iteratedPartial_eq_derivAlong, iteratedPartial_eq_derivAlong]
    exact (derivAlong_eventuallyEq e _).self_of_nhds
  · intro l a b χ φ x hχ hφ bχ bφ α hα
    have ha : 0 ≤ a := (norm_nonneg _).trans (bχ 0 (by simp [MultiIndex.order]))
    have hb : 0 ≤ b := (norm_nonneg _).trans (bφ 0 (by simp [MultiIndex.order]))
    have hL : (coordList α).length ≤ l := by rw [length_coordList]; exact hα
    have key := norm_derivAlong_mul_le x a b (coordList α) hχ hφ
      (fun s hs => by
        rw [derivAlong_eq_iteratedPartial hχ]
        exact bχ _ (by rw [order_countIndex]; omega))
      (fun s hs => by
        rw [derivAlong_eq_iteratedPartial hφ]
        exact bφ _ (by rw [order_countIndex]; omega))
    rw [iteratedPartial_eq_derivAlong]
    refine key.trans ?_
    have hp : (2 : ℝ) ^ (coordList α).length ≤ 2 ^ l :=
      pow_le_pow_right₀ (by norm_num) hL
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp ha) hb
end YangMills.Construction.ConfigSpace
end

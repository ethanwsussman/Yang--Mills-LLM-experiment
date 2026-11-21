import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongAList
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfSumsAndProductsAtATop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages hiding bondSpread
open YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.IteratedDerivative
namespace ListSplits
variable {ι : Type}
def listSplits : List ι → List (List ι × List ι)
  | [] => [([], [])]
  | a :: l => (listSplits l).flatMap fun r => [(a :: r.1, r.2), (r.1, a :: r.2)]
theorem length_listSplits (l : List ι) : (listSplits l).length = 2 ^ l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h : ∀ L : List (List ι × List ι),
        (L.flatMap fun r => [(a :: r.1, r.2), (r.1, a :: r.2)]).length = 2 * L.length := by
      intro L
      induction L with
      | nil => rfl
      | cons r L ihL =>
        simp only [List.flatMap_cons, List.length_append, ihL, List.length_cons, List.length_nil]
        omega
    simp only [listSplits, h, ih, List.length_cons]
    ring
theorem mem_listSplits (l : List ι) : ∀ r ∈ listSplits l, r.1.length + r.2.length = l.length ∧
    ∀ x ∈ l, x ∈ r.1 ∨ x ∈ r.2 := by
  induction l with
  | nil =>
    intro r hr
    simp only [listSplits, List.mem_singleton] at hr
    subst hr
    simp
  | cons a l ih =>
    intro r hr
    simp only [listSplits, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain ⟨r', hr', h⟩ := hr
    obtain ⟨h1, h2⟩ := ih r' hr'
    rcases h with rfl | rfl
    · refine ⟨by simp only [List.length_cons]; omega, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · rcases h2 x hx with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
    · refine ⟨by simp only [List.length_cons]; omega, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · rcases h2 x hx with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
theorem abs_list_sum_le {β : Type} (L : List β) (φ : β → ℝ) (M : ℝ) (h : ∀ r ∈ L, |φ r| ≤ M) :
    |(L.map φ).sum| ≤ L.length * M := by
  induction L with
  | nil => simp
  | cons r L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h r List.mem_cons_self
    have h2 := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    have h3 := abs_add_le (φ r) (L.map φ).sum
    push_cast
    linarith
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem fderiv_list_sum_mul (A B : List ι → E → ℝ) (v : E) (p : E) (a : ι)
    (hA' : ∀ l, A (a :: l) p = fderiv ℝ (A l) p v) (hB' : ∀ l, B (a :: l) p = fderiv ℝ (B l) p v)
    (L : List (List ι × List ι))
    (hA : ∀ r ∈ L, DifferentiableAt ℝ (A r.1) p) (hB : ∀ r ∈ L, DifferentiableAt ℝ (B r.2) p) :
    DifferentiableAt ℝ (fun q => (L.map fun r => A r.1 q * B r.2 q).sum) p ∧
    fderiv ℝ (fun q => (L.map fun r => A r.1 q * B r.2 q).sum) p v =
      ((L.flatMap fun r => [(a :: r.1, r.2), (r.1, a :: r.2)]).map fun r => A r.1 p * B r.2 p).sum := by
  induction L with
  | nil => simp
  | cons r L ih =>
    obtain ⟨d, e⟩ := ih (fun q hq => hA q (List.mem_cons_of_mem _ hq))
      (fun q hq => hB q (List.mem_cons_of_mem _ hq))
    have ha := hA r List.mem_cons_self
    have hb := hB r List.mem_cons_self
    have hm : DifferentiableAt ℝ (fun q => A r.1 q * B r.2 q) p := ha.mul hb
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.cons_append, List.nil_append]
    refine ⟨hm.add d, ?_⟩
    rw [fderiv_fun_add hm d, add_apply, e, fderiv_fun_mul ha hb]
    simp only [add_apply, smul_apply, smul_eq_mul, hA', hB']
    ring
theorem derivAlong_mul (hr : DerivAlongRules E ℝ) (e : ι → E) (f g : E → ℝ) (A : List ι) :
    ∀ p, ContDiffAt ℝ (A.length : WithTop ℕ∞) f p → ContDiffAt ℝ (A.length : WithTop ℕ∞) g p →
      derivAlong (fun q => f q * g q) (A.map e) p =
        ((listSplits A).map fun r => derivAlong f (r.1.map e) p * derivAlong g (r.2.map e) p).sum := by
  induction A with
  | nil =>
    intro p _ _
    simp [listSplits, derivAlong]
  | cons a A ih =>
    intro p hf hg
    have le1 : ((A.length : ℕ) : WithTop ℕ∞) ≤ (((a :: A).length : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast Nat.le_succ _
    have ef := (hf.eventually (by simp)).mono fun q hq => hq.of_le le1
    have eg := (hg.eventually (by simp)).mono fun q hq => hq.of_le le1
    have hev : derivAlong (fun q => f q * g q) (A.map e) =ᶠ[𝓝 p] fun q =>
        ((listSplits A).map fun r => derivAlong f (r.1.map e) q * derivAlong g (r.2.map e) q).sum := by
      filter_upwards [ef, eg] with q h1 h2
      exact ih q h1 h2
    have hd : ∀ (h : E → ℝ), ContDiffAt ℝ (((a :: A).length : ℕ) : WithTop ℕ∞) h p → ∀ l : List ι,
        l.length ≤ A.length → DifferentiableAt ℝ (derivAlong h (l.map e)) p := by
      intro h hh l hl
      have h1 : ContDiffAt ℝ (((1 + (l.map e).length : ℕ)) : WithTop ℕ∞) h p := by
        refine hh.of_le ?_
        simp only [List.length_map, List.length_cons]
        exact_mod_cast (by omega : 1 + l.length ≤ A.length + 1)
      exact (hr.contDiffAt h p 1 _ h1).differentiableAt (by simp)
    have hs := fderiv_list_sum_mul (fun l => derivAlong f (l.map e)) (fun l => derivAlong g (l.map e)) (e a) p a
      (fun _ => rfl) (fun _ => rfl) (listSplits A)
      (fun r hr' => hd f hf _ (by have := (mem_listSplits A r hr').1; omega))
      (fun r hr' => hd g hg _ (by have := (mem_listSplits A r hr').1; omega))
    show fderiv ℝ (derivAlong (fun q => f q * g q) (A.map e)) p (e a) = _
    rw [hev.fderiv_eq]
    exact hs.2
end ListSplits
open ListSplits
variable {F : BlockFrame}
def sublistEmbedding {k : ℕ} (A : List (Fin k)) : (Fin A.length → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin A.length => ℝ) i).smulRight (Pi.single (A.get i) 1)
private theorem sublistEmbedding_apply {k : ℕ} (A : List (Fin k)) (τ : Fin A.length → ℝ) (l : Fin k) :
    sublistEmbedding A τ l = ∑ i, if A.get i = l then τ i else 0 := by
  simp only [sublistEmbedding, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : (Pi.single (A.get i) (1 : ℝ) : Fin k → ℝ) l = if A.get i = l then 1 else 0 := by
    simp [Pi.single_apply, eq_comm]
  rw [e]
  split_ifs <;> simp
private theorem sublistEmbedding_single {k : ℕ} (A : List (Fin k)) (i : Fin A.length) :
    sublistEmbedding A (Pi.single i 1) = Pi.single (A.get i) 1 := by
  funext l
  rw [sublistEmbedding_apply]
  simp only [Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp [eq_comm]
  · intro j _ hj
    simp [hj]
  · simp
private theorem bondSpread_sublistEmbedding {k : ℕ} (A : List (Fin k)) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin A.length → ℝ) :
    bondSpread c X (sublistEmbedding A τ) = bondSpread (restrictToList c A) (restrictToList X A) τ := by
  funext y d
  unfold bondSpread restrictToList
  simp only [sublistEmbedding_apply]
  have h1 : ∀ l : Fin k, (if c l = (y, d) then (∑ i, if A.get i = l then τ i else 0) • X l else 0) =
      ∑ i, if A.get i = l then (if c l = (y, d) then τ i • X l else 0) else 0 := by
    intro l
    by_cases hc : c l = (y, d)
    · simp only [if_pos hc, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : A.get i = l <;> simp [h]
    · simp [hc]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (A.get i)]
  · simp
  · intro l _ hl
    rw [if_neg fun h => hl h.symm]
  · simp
private theorem bondDeriv_restrictToList (h : DerivAlongRulesHold) {k : ℕ} (V : F.GaugeField F.top)
    (G : F.GaugeField F.top → ℝ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (A : List (Fin k)) (hA : A.length ≤ k) (hG : ContDiffAlongBonds k G V c X) :
    bondDeriv G V (restrictToList c A) (restrictToList X A) =
      derivAlong (fun σ : Fin k → ℝ => G (leftTranslate (bondSpread c X σ) V)) (A.map fun l => Pi.single l 1) 0 := by
  have hr := h.1 (Fin A.length → ℝ) ℝ
  set f : (Fin k → ℝ) → ℝ := fun σ => G (leftTranslate (bondSpread c X σ) V) with hf
  have hle : ((A.length : ℕ) : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hA
  have h0 : (0 : Fin k → ℝ) + sublistEmbedding A 0 = 0 := by simp
  have hm : ContDiffAt ℝ ((List.ofFn fun i : Fin A.length => (Pi.single i 1 : Fin A.length → ℝ)).length : WithTop ℕ∞)
      f (0 + sublistEmbedding A 0) := by
    rw [h0, List.length_ofFn]
    exact (show ContDiffAt ℝ (k : WithTop ℕ∞) f 0 from hG).of_le hle
  have hs := h.2 (Fin k → ℝ) (Fin A.length → ℝ) ℝ f (sublistEmbedding A) 0 0
    (List.ofFn fun i : Fin A.length => (Pi.single i 1 : Fin A.length → ℝ)) hm
  have hcomp : (fun t' : Fin A.length → ℝ => f (0 + sublistEmbedding A t')) =
      fun τ => G (leftTranslate (bondSpread (restrictToList c A) (restrictToList X A) τ) V) := by
    funext τ
    simp only [zero_add, hf, bondSpread_sublistEmbedding]
  have hsm : ContDiffAt ℝ ((A.length : ℕ) : WithTop ℕ∞)
      (fun τ => G (leftTranslate (bondSpread (restrictToList c A) (restrictToList X A) τ) V)) 0 := by
    rw [← hcomp]
    have h1 : ContDiffAt ℝ ((A.length : ℕ) : WithTop ℕ∞) f (sublistEmbedding A 0) := by
      rw [map_zero]
      exact (show ContDiffAt ℝ (k : WithTop ℕ∞) f 0 from hG).of_le hle
    have h2 : ContDiffAt ℝ ((A.length : ℕ) : WithTop ℕ∞) (fun t' : Fin A.length → ℝ => sublistEmbedding A t') 0 :=
      (sublistEmbedding A).contDiff.contDiffAt
    simpa only [zero_add, Function.comp_def] using ContDiffAt.comp (0 : Fin A.length → ℝ) h1 h2
  have s1 : bondDeriv G V (restrictToList c A) (restrictToList X A) =
      derivAlong (fun τ => G (leftTranslate (bondSpread (restrictToList c A) (restrictToList X A) τ) V))
        (List.ofFn fun i : Fin A.length => (Pi.single i 1 : Fin A.length → ℝ)) 0 :=
    hr.iteratedFDeriv_eq _ 0 A.length _ hsm
  rw [s1, ← hcomp, hs, h0]
  congr 1
  rw [List.map_ofFn]
  have e1 : (⇑(sublistEmbedding A) ∘ fun i : Fin A.length => (Pi.single i 1 : Fin A.length → ℝ)) =
      (fun l : Fin k => (Pi.single l 1 : Fin k → ℝ)) ∘ A.get := by
    funext i
    simp [sublistEmbedding_single]
  rw [e1, ← List.map_ofFn, List.ofFn_get]
theorem bondDerivSumProductRules_of_derivAlongRules (h : DerivAlongRulesHold) :
    BondDerivSumProductRules := by
  intro F V k c X
  have hr := h.1 (Fin k → ℝ) ℝ
  have hit : ∀ f : (Fin k → ℝ) → ℝ, ContDiffAt ℝ (k : WithTop ℕ∞) f 0 →
      iteratedFDeriv ℝ k f 0 (fun l => Pi.single l 1) =
        derivAlong f (List.ofFn fun l : Fin k => (Pi.single l 1 : Fin k → ℝ)) 0 :=
    fun f hf => hr.iteratedFDeriv_eq f 0 k _ hf
  have hlen : ((List.ofFn fun l : Fin k => (Pi.single l 1 : Fin k → ℝ)).length : WithTop ℕ∞) = k := by
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro ι s G
    classical
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.sum_empty]
      show iteratedFDeriv ℝ k (fun _ : Fin k → ℝ => (0 : ℝ)) 0 _ = 0
      simp
    | insert i s hi ih =>
      intro hG
      have hsum : ∀ V', ∑ j ∈ insert i s, G j V' = G i V' + ∑ j ∈ s, G j V' := fun V' =>
        Finset.sum_insert hi
      have g1 : ContDiffAlongBonds k (G i) V c X := hG i (Finset.mem_insert_self _ _)
      have g2 : ∀ j ∈ s, ContDiffAlongBonds k (G j) V c X := fun j hj => hG j (Finset.mem_insert_of_mem hj)
      have g3 : ContDiffAt ℝ (k : WithTop ℕ∞)
          (fun σ : Fin k → ℝ => ∑ j ∈ s, G j (leftTranslate (bondSpread c X σ) V)) 0 :=
        ContDiffAt.sum fun j hj => g2 j hj
      rw [Finset.sum_insert hi, ← ih g2]
      show iteratedFDeriv ℝ k _ 0 _ = iteratedFDeriv ℝ k _ 0 _ + iteratedFDeriv ℝ k _ 0 _
      simp only [hsum]
      rw [hit _ (ContDiffAt.add g1 g3), hit _ g1, hit _ g3]
      exact hr.add _ _ 0 _ (hlen ▸ g1) (hlen ▸ g3)
  · intro r G hG
    show iteratedFDeriv ℝ k _ 0 _ = r * iteratedFDeriv ℝ k _ 0 _
    rw [hit _ (contDiffAt_const.mul hG), hit _ hG]
    exact hr.smul r _ 0 _ (hlen ▸ hG)
  · intro G H M hG hH hM
    show |iteratedFDeriv ℝ k _ 0 _| ≤ _
    rw [hit _ (ContDiffAt.mul hG hH)]
    have e0 : (List.ofFn fun l : Fin k => (Pi.single l 1 : Fin k → ℝ)) =
        (List.finRange k).map fun l => Pi.single l 1 := List.ofFn_eq_map
    rw [e0, derivAlong_mul hr (fun l : Fin k => (Pi.single l 1 : Fin k → ℝ)) _ _ (List.finRange k) 0
      (by simp only [List.length_finRange]; exact hG) (by simp only [List.length_finRange]; exact hH)]
    have hb := abs_list_sum_le (listSplits (List.finRange k)) (fun r =>
      derivAlong (fun σ : Fin k → ℝ => G (leftTranslate (bondSpread c X σ) V)) (r.1.map fun l => Pi.single l 1) 0 *
      derivAlong (fun σ : Fin k → ℝ => H (leftTranslate (bondSpread c X σ) V)) (r.2.map fun l => Pi.single l 1) 0) M ?_
    · rw [length_listSplits, List.length_finRange] at hb
      simpa using hb
    · intro r hr'
      obtain ⟨h1, h2⟩ := mem_listSplits _ r hr'
      rw [List.length_finRange] at h1
      rw [← bondDeriv_restrictToList h V G c X r.1 (by omega) hG, ← bondDeriv_restrictToList h V H c X r.2 (by omega) hH, abs_mul]
      exact hM r.1 r.2 h1 fun l => h2 l (List.mem_finRange l)
end YangMills.Construction.IteratedDerivative
end

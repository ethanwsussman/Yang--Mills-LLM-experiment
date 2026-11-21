import YangMills.Construction.LinearAlgebra.MultilinearTelescoping
import YangMills.Construction.TorusOrFourSpace.OrderedMomentsOfAFamilyAreMultilinear
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.OrderedMoments
open YangMills.Construction.PeriodicSpace
open YangMills.Construction.PeriodicSpace.Kind
variable {D : Params} {E : Kind}
theorem prod_split_add_at {ι : Type*} [DecidableEq ι] {s : Finset ι} {b : ι} (hb : b ∈ s)
    {u v w : ι → ℝ} (hsplit : u b = v b + w b) (hv : ∀ c ∈ s, c ≠ b → u c = v c)
    (hw : ∀ c ∈ s, c ≠ b → u c = w c) :
    ∏ c ∈ s, u c = ∏ c ∈ s, v c + ∏ c ∈ s, w c := by
  rw [← Finset.mul_prod_erase s u hb, ← Finset.mul_prod_erase s v hb,
    ← Finset.mul_prod_erase s w hb]
  have hv' : ∏ c ∈ s.erase b, v c = ∏ c ∈ s.erase b, u c :=
    Finset.prod_congr rfl fun c hc =>
      (hv c (Finset.mem_of_mem_erase hc) (Finset.ne_of_mem_erase hc)).symm
  have hw' : ∏ c ∈ s.erase b, w c = ∏ c ∈ s.erase b, u c :=
    Finset.prod_congr rfl fun c hc =>
      (hw c (Finset.mem_of_mem_erase hc) (Finset.ne_of_mem_erase hc)).symm
  rw [hv', hw', hsplit]
  ring
theorem prod_smul_at {ι : Type*} [DecidableEq ι] {s : Finset ι} {b : ι} (hb : b ∈ s)
    {u v : ι → ℝ} {c₀ : ℝ} (hscale : u b = c₀ * v b) (hv : ∀ c ∈ s, c ≠ b → u c = v c) :
    ∏ c ∈ s, u c = c₀ * ∏ c ∈ s, v c := by
  rw [← Finset.mul_prod_erase s u hb, ← Finset.mul_prod_erase s v hb]
  have hv' : ∏ c ∈ s.erase b, v c = ∏ c ∈ s.erase b, u c :=
    Finset.prod_congr rfl fun c hc =>
      (hv c (Finset.mem_of_mem_erase hc) (Finset.ne_of_mem_erase hc)).symm
  rw [hv', hscale]
  ring
theorem exists_orderEmbOfFin_eq {q : ℕ} (J : Finset (Fin q)) {i : Fin q} (hi : i ∈ J) :
    ∃ j : Fin J.card, J.orderEmbOfFin rfl j = i := by apply _root_.YangMills.Construction.Multilinear.Seminormed.exists_orderEmbOfFin_eq <;> assumption
theorem restrictTuple_update_orderEmb {q : ℕ} (f : FnTuple D E q) (J : Finset (Fin q))
    (j : Fin J.card) (v : E.Pt D → ℝ) :
    restrictTuple D E (Function.update f (J.orderEmbOfFin rfl j) v) J =
      Function.update (restrictTuple D E f J) j v := by
  funext k
  by_cases hk : k = j
  · subst hk
    simp [restrictTuple]
  · have hne : J.orderEmbOfFin rfl k ≠ J.orderEmbOfFin rfl j :=
      fun e => hk ((J.orderEmbOfFin rfl).injective e)
    simp only [restrictTuple]
    rw [Function.update_of_ne hne, Function.update_of_ne hk]
    rfl
theorem restrictTuple_congr_of_notMem {q : ℕ} {f g : FnTuple D E q} {i : Fin q}
    (hfg : ∀ l, l ≠ i → f l = g l) {J : Finset (Fin q)} (hi : i ∉ J) :
    restrictTuple D E f J = restrictTuple D E g J := by
  funext k
  exact hfg _ fun e => hi (e ▸ Finset.orderEmbOfFin_mem J rfl k)
theorem func_restrict_congr_of_notMem (Φ : MultilinearFamily D E) {q : ℕ} {J : Finset (Fin q)}
    (hJ : 2 ≤ J.card) {f g : sepC1Tuples D E q} {i : Fin q}
    (hfg : ∀ l, l ≠ i → f.1 l = g.1 l) (hi : i ∉ J) :
    Φ.func J.card hJ ⟨restrictTuple D E f.1 J, restrictTuple_mem_sepC1Tuples D E f.2 J⟩ =
      Φ.func J.card hJ ⟨restrictTuple D E g.1 J, restrictTuple_mem_sepC1Tuples D E g.2 J⟩ :=
  congrArg (Φ.func J.card hJ) (Subtype.ext (restrictTuple_congr_of_notMem hfg hi))
theorem func_restrict_update_add (Φ : MultilinearFamily D E) {q : ℕ} {J : Finset (Fin q)}
    (hJ : 2 ≤ J.card) (j : Fin J.card) (f f' : sepC1Tuples D E q)
    (hagree : ∀ l, l ≠ J.orderEmbOfFin rfl j → f.1 l = f'.1 l)
    (hsum : Function.update f.1 (J.orderEmbOfFin rfl j)
      (f.1 (J.orderEmbOfFin rfl j) + f'.1 (J.orderEmbOfFin rfl j)) ∈ sepC1Tuples D E q) :
    Φ.func J.card hJ ⟨restrictTuple D E _ J, restrictTuple_mem_sepC1Tuples D E hsum J⟩ =
      Φ.func J.card hJ ⟨restrictTuple D E f.1 J, restrictTuple_mem_sepC1Tuples D E f.2 J⟩ +
        Φ.func J.card hJ ⟨restrictTuple D E f'.1 J, restrictTuple_mem_sepC1Tuples D E f'.2 J⟩ := by
  have e := restrictTuple_update_orderEmb f.1 J j
    (f.1 (J.orderEmbOfFin rfl j) + f'.1 (J.orderEmbOfFin rfl j))
  have hmem : Function.update (restrictTuple D E f.1 J) j
      (restrictTuple D E f.1 J j + restrictTuple D E f'.1 J j) ∈ sepC1Tuples D E J.card := by
    have hs := restrictTuple_mem_sepC1Tuples D E hsum J
    rw [e] at hs
    exact hs
  have hm := (Φ.multilinear J.card hJ j
    ⟨restrictTuple D E f.1 J, restrictTuple_mem_sepC1Tuples D E f.2 J⟩
    ⟨restrictTuple D E f'.1 J, restrictTuple_mem_sepC1Tuples D E f'.2 J⟩
    (fun l hl => hagree _ fun e' => hl ((J.orderEmbOfFin rfl).injective e'))).1 hmem
  rw [← hm]
  exact congrArg (Φ.func J.card hJ) (Subtype.ext e)
theorem func_restrict_update_smul (Φ : MultilinearFamily D E) {q : ℕ} {J : Finset (Fin q)}
    (hJ : 2 ≤ J.card) (j : Fin J.card) (f : sepC1Tuples D E q) (c₀ : ℝ)
    (hscaled : Function.update f.1 (J.orderEmbOfFin rfl j)
      (c₀ • f.1 (J.orderEmbOfFin rfl j)) ∈ sepC1Tuples D E q) :
    Φ.func J.card hJ ⟨restrictTuple D E _ J, restrictTuple_mem_sepC1Tuples D E hscaled J⟩ =
      c₀ * Φ.func J.card hJ
        ⟨restrictTuple D E f.1 J, restrictTuple_mem_sepC1Tuples D E f.2 J⟩ := by
  have e := restrictTuple_update_orderEmb f.1 J j (c₀ • f.1 (J.orderEmbOfFin rfl j))
  have hmem : Function.update (restrictTuple D E f.1 J) j (c₀ • restrictTuple D E f.1 J j) ∈
      sepC1Tuples D E J.card := by
    have hs := restrictTuple_mem_sepC1Tuples D E hscaled J
    rw [e] at hs
    exact hs
  have hm := (Φ.multilinear J.card hJ j
    ⟨restrictTuple D E f.1 J, restrictTuple_mem_sepC1Tuples D E f.2 J⟩
    ⟨restrictTuple D E f.1 J, restrictTuple_mem_sepC1Tuples D E f.2 J⟩
    (fun _ _ => rfl)).2 c₀ hmem
  rw [← hm]
  exact congrArg (Φ.func J.card hJ) (Subtype.ext e)
theorem notMem_of_ne_part {q : ℕ} {π : Finpartition (Finset.univ : Finset (Fin q))}
    {J K : Finset (Fin q)} (hJ : J ∈ π.parts) (hK : K ∈ π.parts) (hne : K ≠ J) {i : Fin q}
    (hi : i ∈ J) : i ∉ K := fun hiK =>
  hne (π.eq_of_mem_parts hK hJ hiK hi)
theorem indexOrderedMoment_multilinear (Φ : MultilinearFamily D E) {q : ℕ}
    (hq : 1 ≤ q) :
    IsMultilinearOn D E (sepC1Tuples D E q) (Φ.indexOrderedMoment hq) := by
  intro i f f' hagree
  constructor
  · intro hsum
    unfold MultilinearFamily.indexOrderedMoment
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun π _ => ?_
    obtain ⟨P₀, hP₀, hiP₀⟩ := π.1.exists_mem (Finset.mem_univ i)
    obtain ⟨j, hj⟩ := exists_orderEmbOfFin_eq P₀ hiP₀
    subst hj
    refine prod_split_add_at (b := ⟨P₀, hP₀⟩) (Finset.mem_attach _ _) ?_ ?_ ?_
    · exact func_restrict_update_add Φ _ j f f' hagree hsum
    · intro c _ hc
      have hi := notMem_of_ne_part hP₀ c.2 (fun e => hc (Subtype.ext e)) hiP₀
      exact func_restrict_congr_of_notMem Φ _ (f := ⟨_, hsum⟩) (g := f)
        (fun l hl => Function.update_of_ne hl _ _) hi
    · intro c _ hc
      have hi := notMem_of_ne_part hP₀ c.2 (fun e => hc (Subtype.ext e)) hiP₀
      exact func_restrict_congr_of_notMem Φ _ (f := ⟨_, hsum⟩) (g := f')
        (fun l hl => (Function.update_of_ne hl _ _).trans (hagree l hl)) hi
  · intro c₀ hscaled
    unfold MultilinearFamily.indexOrderedMoment
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    obtain ⟨P₀, hP₀, hiP₀⟩ := π.1.exists_mem (Finset.mem_univ i)
    obtain ⟨j, hj⟩ := exists_orderEmbOfFin_eq P₀ hiP₀
    subst hj
    refine prod_smul_at (b := ⟨P₀, hP₀⟩) (Finset.mem_attach _ _) ?_ ?_
    · exact func_restrict_update_smul Φ _ j f c₀ hscaled
    · intro c _ hc
      have hi := notMem_of_ne_part hP₀ c.2 (fun e => hc (Subtype.ext e)) hiP₀
      exact func_restrict_congr_of_notMem Φ _ (f := ⟨_, hscaled⟩) (g := f)
        (fun l hl => Function.update_of_ne hl _ _) hi
theorem partitionsNoSingletons_one :
    partitionsNoSingletons 1 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun π hπ => ?_
  obtain ⟨J, hJ, -⟩ := π.exists_mem (Finset.mem_univ (0 : Fin 1))
  have h₁ : 2 ≤ J.card := two_le_card_of_mem_partitionsNoSingletons hπ hJ
  have h₂ : J.card ≤ 1 := by simpa using Finset.card_le_univ J
  omega
theorem multilinearityStatement_holds : MultilinearityStatement := fun _ _ =>
  ⟨fun Φ => ⟨fun _ hq => indexOrderedMoment_multilinear Φ hq, fun _ =>
      Finset.sum_eq_zero fun π _ => by
        exact absurd π.2 (Finset.eq_empty_iff_forall_notMem.mp
          partitionsNoSingletons_one π.1)⟩,
    partitionsNoSingletons_one,
    fun _ => ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩⟩
end YangMills.Construction.PeriodicSpace.Kind.OrderedMoments

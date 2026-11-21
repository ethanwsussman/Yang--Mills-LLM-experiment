import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsOfSeveralVariablesProof
import YangMills.Construction.SourcesAndGluing.HolomorphicFunctionsOfSeveralVariablesProof
import YangMills.Construction.SourcesAndGluing.MomentCumulantFormula
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.MomentCumulant
open SeveralVariableCalculus
section Combinatorics
variable {n : ℕ}
private theorem sum_disjointCovers_eq_factorial_mul (k : ℕ) (w : Finset (Fin n) → ℂ) :
    ∑ S ∈ (disjointCovers k (firstIndices n)).filter (fun S => ∀ l, S l ≠ ∅), ∏ l, w (S l) =
      (k.factorial : ℂ) *
        ∑ P ∈ Finset.univ.filter (fun P : IndexPartition n => blockCount P = k),
          ∏ J ∈ P.parts, w J := by
  classical
  have step : ∀ P ∈ Finset.univ.filter (fun P : IndexPartition n => blockCount P = k),
      ∑ e : Fin k ≃ {J // J ∈ P.parts}, ∏ l, w (e l).1 =
        (k.factorial : ℂ) * ∏ J ∈ P.parts, w J := by
    intro P hP
    have hc : blockCount P = k := (Finset.mem_filter.1 hP).2
    have hcard : Fintype.card {J // J ∈ P.parts} = k := by
      rw [Fintype.card_coe]; exact hc
    have e0 : Fin k ≃ {J // J ∈ P.parts} := (Fintype.equivFinOfCardEq hcard).symm
    have hprod : ∀ e : Fin k ≃ {J // J ∈ P.parts}, ∏ l, w (e l).1 = ∏ J ∈ P.parts, w J := by
      intro e
      rw [← Finset.prod_coe_sort P.parts w]
      exact Equiv.prod_comp e (fun J => w J.1)
    simp only [hprod, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.card_equiv e0, Fintype.card_fin]
  have hsig := Finset.sum_sigma' (σ := fun P : IndexPartition n => Fin k ≃ {J // J ∈ P.parts})
    (Finset.univ.filter (fun P : IndexPartition n => blockCount P = k))
    (fun P => Finset.univ) (fun P e => ∏ l, w (e l).1)
  rw [Finset.mul_sum, ← Finset.sum_congr rfl step, hsig]
  symm
  have hparts : ∀ (P : IndexPartition n) (e : Fin k ≃ {J // J ∈ P.parts}),
      P.parts = Finset.univ.image fun l => (e l).1 := by
    intro P e
    ext J
    constructor
    · intro hJ
      exact Finset.mem_image.2 ⟨e.symm ⟨J, hJ⟩, Finset.mem_univ _, by simp⟩
    · intro hJ
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hJ
      exact (e l).2
  refine Finset.sum_bij (fun x _ => fun l => (x.2 l).1) ?_ ?_ ?_ ?_
  · rintro ⟨P, e⟩ -
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
    · intro l l' hll
      have hne : (e l).1 ≠ (e l').1 := fun h => hll (e.injective (Subtype.ext h))
      exact P.disjoint (e l).2 (e l').2 hne
    · ext a
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
      obtain ⟨t, ht, hat⟩ := P.exists_mem (Finset.mem_univ a)
      exact ⟨e.symm ⟨t, ht⟩, by simpa using hat⟩
    · intro l h
      have := P.nonempty_of_mem_parts (e l).2
      simp only at h
      rw [h] at this
      simp at this
  · rintro ⟨P, e⟩ - ⟨P', e'⟩ - h
    simp only at h
    have hP : P = P' := by
      apply Finpartition.ext
      rw [hparts P e, hparts P' e']
      exact congrArg (fun S : Fin k → Finset (Fin n) => Finset.univ.image S) h
    subst hP
    have he : e = e' := by
      ext1 l
      exact Subtype.ext (congrFun h l)
    rw [he]
  · intro S hS
    obtain ⟨hS1, hne⟩ := Finset.mem_filter.1 hS
    obtain ⟨-, hdis, hcov⟩ := Finset.mem_filter.1 hS1
    have hinj : Function.Injective S := by
      intro l l' h
      by_contra hll
      have := hdis l l' hll
      rw [h, disjoint_self] at this
      exact hne l' this
    let P : IndexPartition n :=
      { parts := Finset.univ.image S
        supIndep := by
          rw [Finset.supIndep_iff_pairwiseDisjoint]
          intro A hA B hB hAB
          obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hA)
          obtain ⟨l', -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hB)
          exact hdis l l' fun h => hAB (by rw [h])
        sup_parts := by
          rw [Finset.sup_image]
          simpa [Finset.sup_eq_biUnion] using hcov
        bot_notMem := by
          intro h
          obtain ⟨l, -, hl⟩ := Finset.mem_image.1 h
          exact hne l hl }
    have hbij : Function.Bijective (fun l => (⟨S l, Finset.mem_image_of_mem S (Finset.mem_univ l)⟩ :
        {J // J ∈ P.parts})) := by
      constructor
      · intro l l' h
        exact hinj (congrArg Subtype.val h)
      · rintro ⟨J, hJ⟩
        obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hJ
        exact ⟨l, rfl⟩
    refine ⟨⟨P, Equiv.ofBijective _ hbij⟩, ?_, rfl⟩
    refine Finset.mem_sigma.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩
    change (Finset.univ.image S).card = k
    rw [Finset.card_image_of_injective _ hinj]
    simp
  · rintro ⟨P, e⟩ -
    rfl
private theorem card_indexPartition_le_factorial (n : ℕ) :
    Fintype.card (IndexPartition n) ≤ n.factorial := by
  classical
  have hmem : ∀ (P : IndexPartition n) (i : Fin n), i ∈ P.part i := fun P i =>
    P.mem_part (Finset.mem_univ i)
  let m : IndexPartition n → Fin n → Fin n := fun P i => (P.part i).min' ⟨i, hmem P i⟩
  have hm_mem : ∀ P i, m P i ∈ P.part i := fun P i => Finset.min'_mem _ _
  have hm_le : ∀ P i, m P i ≤ i := fun P i => Finset.min'_le _ _ (hmem P i)
  have hpart : ∀ (P : IndexPartition n) (a b : Fin n), b ∈ P.part a ↔ m P b = m P a := by
    intro P a b
    have hmp : ∀ c, P.part c ∈ P.parts := fun c => P.part_mem.2 (Finset.mem_univ c)
    constructor
    · intro hb
      have : P.part b = P.part a := P.part_eq_of_mem (hmp a) hb
      simp only [m, this]
    · intro h
      have h1 : m P a ∈ P.part b := h ▸ hm_mem P b
      have h2 : P.part a = P.part b := by
        have e1 := P.part_eq_of_mem (hmp a) (hm_mem P a)
        have e2 := P.part_eq_of_mem (hmp b) h1
        rw [← e1, e2]
      rw [h2]
      exact hmem P b
  have hsub : ∀ P Q : IndexPartition n, m P = m Q → P.parts ⊆ Q.parts := by
    intro P Q h J hJ
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hJ
    have hJa : P.part a = J := P.part_eq_of_mem hJ ha
    have : J = Q.part a := by
      ext b
      rw [← hJa, hpart, hpart, h]
    rw [this]
    exact Q.part_mem.2 (Finset.mem_univ a)
  let lead : IndexPartition n → (i : Fin n) → Fin (i.1 + 1) := fun P i =>
    ⟨(m P i).1, Nat.lt_succ_of_le (hm_le P i)⟩
  have hinj : Function.Injective lead := by
    intro P Q h
    have hm : m P = m Q := by
      funext i
      have h2 : lead P i = lead Q i := congrFun h i
      have h3 : (lead P i).1 = (lead Q i).1 := congrArg Fin.val h2
      exact Fin.ext h3
    exact Finpartition.ext (Finset.Subset.antisymm (hsub P Q hm) (hsub Q P hm.symm))
  have hc := Fintype.card_le_of_injective lead hinj
  rw [Fintype.card_pi] at hc
  simp only [Fintype.card_fin] at hc
  rwa [Fin.prod_univ_eq_prod_range (fun i => i + 1) n,
    Finset.prod_range_add_one_eq_factorial] at hc
end Combinatorics
section Calculus
variable {n : ℕ}
private theorem holomorphicOnSet_iff_lines (V : Set (Coordinates.ComplexCoordinates n))
    (F : Coordinates.ComplexCoordinates n → ℂ) :
    HolomorphicOnSet V F ↔ IsOpen V ∧ ContinuousOn F V ∧ ∀ a ∈ V, ∀ j : Fin n,
      ∀ᶠ ζ in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ
          (fun ζ : ℂ => F (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) ζ := by
  have hsymm : ∀ x : ℂ, (Equiv.funUnique (Fin 1) ℂ).symm x = fun _ => x := by
    intro x
    funext i
    simp [Equiv.funUnique, Subsingleton.elim i default]
  have hcomp : ((Equiv.funUnique (Fin 1) ℂ).symm ∘ F) = fun z _ => F z :=
    funext fun z => hsymm (F z)
  rw [holomorphicOnSet_iff_complexCoordinates, Coordinates.ComplexCoordinates.IsHolomorphicIn, hcomp]
  refine and_congr_right fun _ => and_congr ?_ ?_
  · exact ⟨fun h => (continuous_apply (0 : Fin 1)).comp_continuousOn h,
      fun h => continuousOn_pi.2 fun _ => h⟩
  · refine forall₂_congr fun a _ => forall_congr' fun j => eventually_congr ?_
    refine Eventually.of_forall fun ζ => ?_
    rw [differentiableAt_pi]
    exact ⟨fun h => h 0, fun h _ => h⟩
private theorem holomorphicOnSet_mono {V W : Set (Coordinates.ComplexCoordinates n)}
    {F : Coordinates.ComplexCoordinates n → ℂ}
    (hW : IsOpen W) (hWV : W ⊆ V) (hF : HolomorphicOnSet V F) : HolomorphicOnSet W F := by
  rw [holomorphicOnSet_iff_lines] at hF ⊢
  obtain ⟨-, hc, hd⟩ := hF
  exact ⟨hW, hc.mono hWV, fun a ha j => hd a (hWV ha) j⟩
private theorem holomorphicOnSet_const {V : Set (Coordinates.ComplexCoordinates n)} (hV : IsOpen V)
    (c : ℂ) : HolomorphicOnSet V fun _ => c := by
  rw [holomorphicOnSet_iff_lines]
  exact ⟨hV, continuousOn_const, fun _ _ _ => Eventually.of_forall fun _ =>
    differentiableAt_const _⟩
private theorem partialDeriv_congr {V : Set (Coordinates.ComplexCoordinates n)} (hV : IsOpen V)
    {F G : Coordinates.ComplexCoordinates n → ℂ} (h : EqOn F G V) (i : Fin n) :
    EqOn (partialDeriv i F) (partialDeriv i G) V := by apply _root_.YangMills.SharedProofs.p36449 <;> assumption
private theorem iteratedPartials_congr {V : Set (Coordinates.ComplexCoordinates n)} (hV : IsOpen V)
    {F G : Coordinates.ComplexCoordinates n → ℂ} (h : EqOn F G V) (l : List (Fin n)) :
    EqOn (iteratedPartials l F) (iteratedPartials l G) V := by apply _root_.YangMills.Construction.SeveralComplexVariables.foldr_coordDeriv_eqOn_of_eqOn <;> assumption
private theorem iteratedPartials_holomorphicOnSet (H : SeveralVariableCalculus.Claim)
    (hn : 1 ≤ n) {V : Set (Coordinates.ComplexCoordinates n)} (hV : IsOpen V)
    {F : Coordinates.ComplexCoordinates n → ℂ}
    (hF : HolomorphicOnSet V F) (l : List (Fin n)) : HolomorphicOnSet V (iteratedPartials l F) := by
  induction l with
  | nil => exact hF
  | cons i l ih =>
    exact ((H n 1 hn le_rfl V hV _ (fun _ => iteratedPartials l F) ih (fun _ => ih)).1 i i).1
private theorem iteratedPartials_add (H : SeveralVariableCalculus.Claim)
    (hn : 1 ≤ n) {V : Set (Coordinates.ComplexCoordinates n)} (hV : IsOpen V)
    {F G : Coordinates.ComplexCoordinates n → ℂ}
    (hF : HolomorphicOnSet V F) (hG : HolomorphicOnSet V G) (l : List (Fin n)) :
    EqOn (iteratedPartials l fun z => F z + G z)
      (fun z => iteratedPartials l F z + iteratedPartials l G z) V := by
  induction l with
  | nil => exact fun _ _ => rfl
  | cons i l ih =>
    intro a ha
    have h1 := partialDeriv_congr hV ih i ha
    have h2 := (((H n 1 hn le_rfl V hV _ (fun _ => iteratedPartials l G)
      (iteratedPartials_holomorphicOnSet H hn hV hF l)
      (fun _ => iteratedPartials_holomorphicOnSet H hn hV hG l)).2.1).2.2 i).1 ha
    exact h1.trans h2
private theorem iteratedPartials_const_mul (c : ℂ) (F : Coordinates.ComplexCoordinates n → ℂ)
    (l : List (Fin n)) :
    iteratedPartials l (fun z => c * F z) = fun z => c * iteratedPartials l F z := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext a
    change partialDeriv i (iteratedPartials l fun z => c * F z) a =
      c * partialDeriv i (iteratedPartials l F) a
    rw [ih]
    exact deriv_const_mul_field c
private theorem iteratedPartials_sub_const (c : ℂ) (F : Coordinates.ComplexCoordinates n → ℂ)
    {l : List (Fin n)} (hl : l ≠ []) :
    iteratedPartials l (fun z => F z - c) = iteratedPartials l F := by
  induction l with
  | nil => exact absurd rfl hl
  | cons i l ih =>
    by_cases hl' : l = []
    · subst hl'
      funext a
      change deriv (fun ζ : ℂ => F (a + ζ • coordVector i) - c) 0 =
        deriv (fun ζ : ℂ => F (a + ζ • coordVector i)) 0
      simp
    · change partialDeriv i (iteratedPartials l fun z => F z - c) =
        partialDeriv i (iteratedPartials l F)
      rw [ih hl']
private theorem iteratedPartials_sum (H : SeveralVariableCalculus.Claim)
    (hn : 1 ≤ n) {V : Set (Coordinates.ComplexCoordinates n)} (hV : IsOpen V) (s : Finset ℕ)
    (c : ℕ → ℂ) (F : ℕ → Coordinates.ComplexCoordinates n → ℂ)
    (hF : ∀ k ∈ s, HolomorphicOnSet V (F k)) (l : List (Fin n)) :
    HolomorphicOnSet V (fun z => ∑ k ∈ s, c k * F k z) ∧
      EqOn (iteratedPartials l fun z => ∑ k ∈ s, c k * F k z)
        (fun z => ∑ k ∈ s, c k * iteratedPartials l (F k) z) V := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using holomorphicOnSet_const hV 0, fun a _ => ?_⟩
    have := congrFun (iteratedPartials_const_mul (n := n) 0 (fun _ => 0) l) a
    simpa using this
  | insert k s hk ih =>
    obtain ⟨ih1, ih2⟩ := ih fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have hFk := hF k (Finset.mem_insert_self k s)
    have hmul : HolomorphicOnSet V fun z => c k * F k z :=
      ((H n 1 hn le_rfl V hV (F k) (fun _ => F k) hFk (fun _ => hFk)).2.2.2.1 univ
        (fun t => c k * t) isOpen_univ (by fun_prop) (fun _ _ => mem_univ _)).1
    have hsum : ∀ z, ∑ j ∈ insert k s, c j * F j z = c k * F k z + ∑ j ∈ s, c j * F j z :=
      fun z => Finset.sum_insert hk
    have hfun : (fun z => ∑ j ∈ insert k s, c j * F j z) =
        fun z => c k * F k z + ∑ j ∈ s, c j * F j z := funext hsum
    rw [hfun]
    refine ⟨(H n 1 hn le_rfl V hV _ (fun _ => _) hmul (fun _ => ih1)).2.1.1, fun a ha => ?_⟩
    have h1 : iteratedPartials l (fun z => c k * F k z + ∑ j ∈ s, c j * F j z) a =
        iteratedPartials l (fun z => c k * F k z) a +
          iteratedPartials l (fun z => ∑ j ∈ s, c j * F j z) a :=
      iteratedPartials_add H hn hV hmul ih1 l ha
    have h2 : iteratedPartials l (fun z => ∑ j ∈ s, c j * F j z) a =
        ∑ j ∈ s, c j * iteratedPartials l (F j) a := ih2 ha
    change iteratedPartials l (fun z => c k * F k z + ∑ j ∈ s, c j * F j z) a =
      ∑ j ∈ insert k s, c j * iteratedPartials l (F j) a
    rw [h1, h2, Finset.sum_insert hk, iteratedPartials_const_mul]
private theorem setPartial_pow (H : SeveralVariableCalculus.Claim) (hn : 1 ≤ n)
    {V : Set (Coordinates.ComplexCoordinates n)} (hV : IsOpen V)
    {u : Coordinates.ComplexCoordinates n → ℂ}
    (hu : HolomorphicOnSet V u) (h0 : (0 : Coordinates.ComplexCoordinates n) ∈ V) (hu0 : u 0 = 0)
    {k : ℕ} (hk : 1 ≤ k) :
    setPartial (firstIndices n) (fun z => u z ^ k) 0 =
      (k.factorial : ℂ) *
        ∑ P ∈ Finset.univ.filter (fun P : IndexPartition n => blockCount P = k),
          ∏ J ∈ P.parts, setPartial J u 0 := by
  have hL := (H n k hn hk V hV u (fun _ => u) hu (fun _ => hu)).2.2.1 (firstIndices n) h0
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hL
  rw [hL, ← sum_disjointCovers_eq_factorial_mul k (fun J => setPartial J u 0)]
  symm
  refine Finset.sum_filter_of_ne fun S _ hS l hl => hS ?_
  refine Finset.prod_eq_zero (Finset.mem_univ l) ?_
  rw [hl, setPartial_empty, hu0]
private theorem setPartial_pow_mul_eq_zero (H : SeveralVariableCalculus.Claim)
    (hn : 1 ≤ n) {V : Set (Coordinates.ComplexCoordinates n)} (hV : IsOpen V)
    {u r : Coordinates.ComplexCoordinates n → ℂ}
    (hu : HolomorphicOnSet V u) (hr : HolomorphicOnSet V r)
    (h0 : (0 : Coordinates.ComplexCoordinates n) ∈ V) (hu0 : u 0 = 0) :
    setPartial (firstIndices n) (fun z => u z ^ (n + 1) * r z) 0 = 0 := by
  classical
  let Fs : Fin (n + 2) → Coordinates.ComplexCoordinates n → ℂ := Fin.lastCases r (fun _ => u)
  have hFs : ∀ l, HolomorphicOnSet V (Fs l) := by
    intro l
    refine Fin.lastCases ?_ (fun i => ?_) l
    · simpa [Fs] using hr
    · simpa [Fs] using hu
  have hL := (H n (n + 2) hn (by omega) V hV u Fs hu hFs).2.2.1 (firstIndices n) h0
  have hprod : (fun z => ∏ l, Fs l z) = fun z => u z ^ (n + 1) * r z := by
    funext z
    rw [Fin.prod_univ_castSucc]
    simp [Fs]
  rw [hprod] at hL
  rw [hL]
  refine Finset.sum_eq_zero fun S hS => ?_
  obtain ⟨-, hdis, -⟩ := Finset.mem_filter.1 hS
  have hex : ∃ l : Fin (n + 1), S l.castSucc = ∅ := by
    by_contra hall
    have hne : ∀ l : Fin (n + 1), (S l.castSucc).Nonempty := fun l =>
      Finset.nonempty_iff_ne_empty.2 fun h => hall ⟨l, h⟩
    choose a ha using hne
    have hinj : Function.Injective a := by
      intro l l' h
      by_contra hll
      have hd := hdis l.castSucc l'.castSucc (fun h' => hll (Fin.castSucc_injective _ h'))
      exact Finset.disjoint_left.1 hd (ha l) (h ▸ ha l')
    have := Fintype.card_le_of_injective a hinj
    simp at this
  obtain ⟨l, hl⟩ := hex
  refine Finset.prod_eq_zero (Finset.mem_univ l.castSucc) ?_
  rw [hl, setPartial_empty]
  simpa [Fs] using hu0
end Calculus
section Logarithm
private def logTail (n : ℕ) (t : ℂ) : ℂ := ∑' q : ℕ, (-t) ^ q / ((q + (n + 1) : ℕ) : ℂ)
private theorem differentiableOn_logTail (n : ℕ) :
    DifferentiableOn ℂ (logTail n) (Metric.ball 0 (1 / 2)) := by
  refine Complex.differentiableOn_tsum_of_summable_norm (u := fun q => (1 / 2 : ℝ) ^ q)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    (fun q => by fun_prop) Metric.isOpen_ball (fun q w hw => ?_)
  have hw' : ‖w‖ ≤ 1 / 2 := by simpa using (Metric.mem_ball.1 hw).le
  have hden : (1 : ℝ) ≤ ‖((q + (n + 1) : ℕ) : ℂ)‖ := by
    rw [Complex.norm_natCast]
    exact_mod_cast Nat.succ_le_of_lt (by omega)
  rw [norm_div, norm_pow, norm_neg]
  calc ‖w‖ ^ q / ‖((q + (n + 1) : ℕ) : ℂ)‖ ≤ ‖w‖ ^ q / 1 :=
        div_le_div_of_nonneg_left (by positivity) one_pos hden
    _ = ‖w‖ ^ q := div_one _
    _ ≤ (1 / 2) ^ q := pow_le_pow_left₀ (norm_nonneg _) hw' q
private theorem principalLog_one_add_eq (n : ℕ) {t : ℂ} (ht : ‖t‖ < 1) :
    principalLog (1 + t) =
      ∑ i ∈ Finset.range n, (-1) ^ i / ((i : ℂ) + 1) * t ^ (i + 1) +
        t ^ (n + 1) * (-(-1) ^ (n + 1) * logTail n t) := by
  have hz : ‖-t‖ < 1 := by simpa using ht
  have hdisc : 1 + t ∈ unitDiscAtOne := by simpa [unitDiscAtOne] using ht
  have h := Complex.hasSum_taylorSeries_neg_log hz
  have hs := (hasSum_nat_add_iff' (n + 1)).2 h
  have hterm : ∀ q : ℕ, (-t) ^ (q + (n + 1)) / ((q + (n + 1) : ℕ) : ℂ) =
      (-t) ^ (n + 1) * ((-t) ^ q / ((q + (n + 1) : ℕ) : ℂ)) := by
    intro q
    rw [pow_add]
    ring
  have hval := hs.tsum_eq
  simp only [hterm] at hval
  rw [tsum_mul_left] at hval
  have hsub : (1 : ℂ) - -t = 1 + t := by ring
  rw [hsub] at hval
  rw [principalLog_eq_log hdisc]
  have hsum : ∑ i ∈ Finset.range (n + 1), (-t) ^ i / (i : ℂ) =
      ∑ i ∈ Finset.range n, (-t) ^ (i + 1) / ((i + 1 : ℕ) : ℂ) := by
    rw [Finset.sum_range_succ']
    simp
  rw [hsum] at hval
  have hneg : ∀ i : ℕ, (-t) ^ i = (-1) ^ i * t ^ i := fun i => by rw [neg_pow]
  have hsum2 : ∑ i ∈ Finset.range n, (-1) ^ i / ((i : ℂ) + 1) * t ^ (i + 1) =
      -∑ i ∈ Finset.range n, (-t) ^ (i + 1) / ((i + 1 : ℕ) : ℂ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hneg, pow_succ (-1 : ℂ) i]
    push_cast
    ring
  rw [hsum2]
  have hR : (-t) ^ (n + 1) * logTail n t =
      -Complex.log (1 + t) - ∑ i ∈ Finset.range n, (-t) ^ (i + 1) / ((i + 1 : ℕ) : ℂ) := hval
  rw [hneg (n + 1)] at hR
  linear_combination hR
end Logarithm
section Formula
variable {n : ℕ}
private theorem one_le_blockCount (hn : 1 ≤ n) (P : IndexPartition n) : 1 ≤ blockCount P := by
  obtain ⟨t, ht, -⟩ := P.exists_mem (Finset.mem_univ (⟨0, hn⟩ : Fin n))
  exact Finset.card_pos.2 ⟨t, ht⟩
private theorem blockCount_le (P : IndexPartition n) : blockCount P ≤ n := by
  have := P.card_parts_le_card
  simpa [blockCount] using this
private theorem setPartial_log_eq (H : SeveralVariableCalculus.Claim) (hn : 1 ≤ n)
    (U : Set (Coordinates.ComplexCoordinates n)) (h : Coordinates.ComplexCoordinates n → ℂ)
    (hU : IsOpen U) (h0 : (0 : Coordinates.ComplexCoordinates n) ∈ U) (hh : HolomorphicOnSet U h)
    (h1 : h 0 = 1) :
    setPartial (firstIndices n) (fun z => principalLog (h z)) 0 =
      ∑ P : IndexPartition n,
        (-1 : ℂ) ^ (blockCount P - 1) * ((blockCount P - 1).factorial : ℂ) *
          ∏ J ∈ P.parts, setPartial J h 0 := by
  classical
  have hcont : ContinuousOn h U := ((holomorphicOnSet_iff_lines U h).1 hh).2.1
  let B : Set ℂ := Metric.ball 0 (1 / 2)
  have hBo : IsOpen B := Metric.isOpen_ball
  let u : Coordinates.ComplexCoordinates n → ℂ := fun z => h z - 1
  let V : Set (Coordinates.ComplexCoordinates n) := U ∩ u ⁻¹' B
  have hV : IsOpen V := (hcont.sub continuousOn_const).isOpen_inter_preimage hU hBo
  have hV0 : (0 : Coordinates.ComplexCoordinates n) ∈ V := ⟨h0, by simp [u, B, h1]⟩
  have hhV : HolomorphicOnSet V h := holomorphicOnSet_mono hV inter_subset_left hh
  have hcompH := (H n 1 hn le_rfl V hV h (fun _ => h) hhV (fun _ => hhV)).2.2.2.1
  have hu : HolomorphicOnSet V u :=
    (hcompH univ (fun w => w - 1) isOpen_univ (by fun_prop) (fun _ _ => mem_univ _)).1
  have hu0 : u 0 = 0 := by simp [u, h1]
  have hcompU := (H n 1 hn le_rfl V hV u (fun _ => u) hu (fun _ => hu)).2.2.2.1
  have huB : MapsTo u V B := fun z hz => hz.2
  let c : ℕ → ℂ := fun i => (-1) ^ i / ((i : ℂ) + 1)
  let F : ℕ → Coordinates.ComplexCoordinates n → ℂ := fun i z => u z ^ (i + 1)
  let r : Coordinates.ComplexCoordinates n → ℂ := fun z => -(-1) ^ (n + 1) * logTail n (u z)
  have hF : ∀ i ∈ Finset.range n, HolomorphicOnSet V (F i) := fun i _ =>
    (hcompU univ (fun t => t ^ (i + 1)) isOpen_univ (by fun_prop) (fun _ _ => mem_univ _)).1
  have hdiffR := differentiableOn_logTail n
  have hr : HolomorphicOnSet V r :=
    (hcompU B (fun t => -(-1) ^ (n + 1) * logTail n t) hBo
      (hdiffR.const_mul _) huB).1
  have hrem : HolomorphicOnSet V fun z => u z ^ (n + 1) * r z :=
    (hcompU B (fun t => t ^ (n + 1) * (-(-1) ^ (n + 1) * logTail n t)) hBo
      ((by fun_prop : DifferentiableOn ℂ (fun t : ℂ => t ^ (n + 1)) B).mul
        (hdiffR.const_mul _)) huB).1
  have hEq : EqOn (fun z => principalLog (h z))
      (fun z => (∑ i ∈ Finset.range n, c i * F i z) + u z ^ (n + 1) * r z) V := by
    intro z hz
    have hlt : ‖u z‖ < 1 := by
      have : ‖u z‖ < 1 / 2 := by simpa [B] using hz.2
      linarith
    have := principalLog_one_add_eq n hlt
    have hhz : 1 + u z = h z := by simp [u]
    rw [hhz] at this
    exact this
  obtain ⟨hA, hAsum⟩ := iteratedPartials_sum H hn hV (Finset.range n) c F hF (firstIndices n).sort
  have hstep : setPartial (firstIndices n) (fun z => principalLog (h z)) 0 =
      ∑ i ∈ Finset.range n, c i * setPartial (firstIndices n) (F i) 0 := by
    have e1 := iteratedPartials_congr hV hEq (firstIndices n).sort hV0
    have e2 := iteratedPartials_add H hn hV hA hrem (firstIndices n).sort hV0
    have e3 := hAsum hV0
    have e4 := setPartial_pow_mul_eq_zero H hn hV hu hr hV0 hu0
    simp only [setPartial] at e4 ⊢
    beta_reduce at e2 e3
    rw [e1, e2, e3, e4, add_zero]
  rw [hstep]
  have hblock : ∀ (P : IndexPartition n), ∏ J ∈ P.parts, setPartial J u 0 =
      ∏ J ∈ P.parts, setPartial J h 0 := by
    intro P
    refine Finset.prod_congr rfl fun J hJ => ?_
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hJ
    have hl : J.sort ≠ [] := by
      intro hnil
      have : a ∈ J.sort := (Finset.mem_sort _).2 ha
      rw [hnil] at this
      simp at this
    exact congrFun (iteratedPartials_sub_const 1 h hl) 0
  have hterm : ∀ i ∈ Finset.range n, c i * setPartial (firstIndices n) (F i) 0 =
      ∑ P ∈ Finset.univ.filter (fun P : IndexPartition n => blockCount P - 1 = i),
        (-1 : ℂ) ^ (blockCount P - 1) * ((blockCount P - 1).factorial : ℂ) *
          ∏ J ∈ P.parts, setPartial J h 0 := by
    intro i _
    have hP := setPartial_pow H hn hV hu hV0 hu0 (k := i + 1) (by omega)
    have hfilter : Finset.univ.filter (fun P : IndexPartition n => blockCount P = i + 1) =
        Finset.univ.filter (fun P : IndexPartition n => blockCount P - 1 = i) := by
      refine Finset.filter_congr fun P _ => ?_
      have := one_le_blockCount hn P
      omega
    change c i * setPartial (firstIndices n) (fun z => u z ^ (i + 1)) 0 = _
    rw [hP, hfilter, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun P hPmem => ?_
    have hb : blockCount P - 1 = i := (Finset.mem_filter.1 hPmem).2
    rw [hb, hblock P, ← mul_assoc]
    congr 1
    have hi : ((i : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
    simp only [c]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm]
  refine Finset.sum_fiberwise_of_maps_to (fun P _ => ?_) _
  have h1' := one_le_blockCount hn P
  have h2' := blockCount_le P
  exact Finset.mem_range.2 (by omega)
end Formula
section Count
private def invPow (c : ℂ) (m : ℕ) (s : ℂ) : ℂ := ((1 - c * s)⁻¹) ^ (m + 1)
private theorem invPow_zero (c : ℂ) (m : ℕ) : invPow c m 0 = 1 := by
  simp [invPow]
private theorem hasDerivAt_invPow (c : ℂ) (m : ℕ) {s : ℂ} (hs : 1 - c * s ≠ 0) :
    HasDerivAt (invPow c m) (((m : ℂ) + 1) * c * invPow c (m + 1) s) s := by
  have h1 : HasDerivAt (fun s : ℂ => 1 - c * s) (-c) s := by
    simpa using ((hasDerivAt_id s).const_mul c).const_sub 1
  have h2 := h1.fun_inv hs
  have h3 := h2.fun_pow (m + 1)
  have hval : ((m + 1 : ℕ) : ℂ) * ((1 - c * s)⁻¹) ^ (m + 1 - 1) * (- -c / (1 - c * s) ^ 2) =
      ((m : ℂ) + 1) * c * invPow c (m + 1) s := by
    simp only [invPow, Nat.add_sub_cancel]
    push_cast
    rw [pow_succ _ (m + 1), pow_succ _ m]
    field_simp
  rw [hval] at h3
  exact h3
private theorem iterate_deriv_eqOn_of_hasDerivAt {B : Set ℂ} (hB : IsOpen B) (A : ℕ → ℂ → ℂ)
    (hA : ∀ m, ∀ s ∈ B, HasDerivAt (A m) (A (m + 1) s) s) (m : ℕ) :
    EqOn (deriv^[m] (A 0)) (A m) B := by
  induction m with
  | zero => exact fun _ _ => rfl
  | succ m ih =>
    intro s hs
    rw [Function.iterate_succ_apply']
    have he : deriv^[m] (A 0) =ᶠ[𝓝 s] A m := Filter.eventuallyEq_of_mem (hB.mem_nhds hs) ih
    rw [he.deriv_eq]
    exact (hA m s hs).deriv
private def testFunction (s : ℂ) : ℂ := 2 - invPow 1 0 s
private theorem one_sub_one_mul_ne_zero {s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (1 / 2)) :
    1 - (1 : ℂ) * s ≠ 0 := by
  intro h
  have h1 : s = 1 := by linear_combination -h
  rw [h1] at hs
  norm_num at hs
private theorem one_sub_two_mul_ne_zero {s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (1 / 2)) :
    1 - (2 : ℂ) * s ≠ 0 := by
  intro h
  have h1 : s = 1 / 2 := by linear_combination -h / 2
  rw [h1] at hs
  norm_num at hs
private theorem testFunction_eq {s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (1 / 2)) :
    testFunction s = (1 - 2 * s) / (1 - 1 * s) := by
  have h1 := one_sub_one_mul_ne_zero hs
  simp only [testFunction, invPow, zero_add, pow_one]
  rw [eq_div_iff h1, sub_mul, inv_mul_cancel₀ h1]
  ring
private theorem testFunction_mem_unitDiscAtOne {s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (1 / 2)) :
    testFunction s ∈ unitDiscAtOne := by
  have h1 := one_sub_one_mul_ne_zero hs
  have hlt : ‖s‖ < 1 / 2 := by simpa using hs
  have hge : 1 - ‖s‖ ≤ ‖1 - 1 * s‖ := by
    have := norm_sub_norm_le (1 : ℂ) s
    simpa using this
  have heq : testFunction s - 1 = -s / (1 - 1 * s) := by
    rw [testFunction_eq hs, eq_div_iff h1, sub_mul, div_mul_cancel₀ _ h1]
    ring
  change ‖testFunction s - 1‖ < 1
  rw [heq, norm_div, norm_neg, div_lt_one (norm_pos_iff.2 h1)]
  linarith
private def testDerivs : ℕ → ℂ → ℂ
  | 0 => testFunction
  | m + 1 => fun s => -((m + 1).factorial : ℂ) * invPow 1 (m + 1) s
private theorem hasDerivAt_testDerivs (m : ℕ) (s : ℂ)
    (hs : s ∈ Metric.ball (0 : ℂ) (1 / 2)) :
    HasDerivAt (testDerivs m) (testDerivs (m + 1) s) s := by
  have h1 := one_sub_one_mul_ne_zero hs
  cases m with
  | zero =>
    have h : HasDerivAt (testDerivs 0) _ s :=
      (hasDerivAt_invPow 1 0 h1).const_sub 2
    refine h.congr_deriv ?_
    change -((((0 : ℕ) : ℂ) + 1) * 1 * invPow 1 (0 + 1) s) =
      -(((0 + 1).factorial : ℕ) : ℂ) * invPow 1 (0 + 1) s
    simp
  | succ m =>
    have h : HasDerivAt (testDerivs (m + 1)) _ s :=
      (hasDerivAt_invPow 1 (m + 1) h1).const_mul (-((m + 1).factorial : ℂ))
    refine h.congr_deriv ?_
    change -((m + 1).factorial : ℂ) * ((((m + 1 : ℕ) : ℂ) + 1) * 1 * invPow 1 (m + 1 + 1) s) =
      -((m + 1 + 1).factorial : ℂ) * invPow 1 (m + 1 + 1) s
    rw [Nat.factorial_succ (m + 1)]
    push_cast
    ring
private def logTestDerivs : ℕ → ℂ → ℂ
  | 0 => fun s => principalLog (testFunction s)
  | m + 1 => fun s => (m.factorial : ℂ) * (invPow 1 m s - 2 ^ (m + 1) * invPow 2 m s)
private theorem hasDerivAt_logTestDerivs (m : ℕ) (s : ℂ)
    (hs : s ∈ Metric.ball (0 : ℂ) (1 / 2)) :
    HasDerivAt (logTestDerivs m) (logTestDerivs (m + 1) s) s := by
  have h1 := one_sub_one_mul_ne_zero hs
  have h2 := one_sub_two_mul_ne_zero hs
  cases m with
  | zero =>
    have hg : HasDerivAt testFunction (testDerivs 1 s) s :=
      hasDerivAt_testDerivs 0 s hs
    have h : HasDerivAt (logTestDerivs 0) _ s :=
      (hasDerivAt_principalLog (testFunction_mem_unitDiscAtOne hs)).comp s hg
    refine h.congr_deriv ?_
    have e1 : testDerivs 1 s = -invPow 1 1 s := by
      change -(((0 + 1).factorial : ℕ) : ℂ) * invPow 1 (0 + 1) s = _
      simp
    have e2 : logTestDerivs (0 + 1) s = invPow 1 0 s - 2 * invPow 2 0 s := by
      change ((0 : ℕ).factorial : ℂ) * (invPow 1 0 s - 2 ^ (0 + 1) * invPow 2 0 s) = _
      simp
    rw [e1, e2, testFunction_eq hs]
    simp only [invPow, one_mul, zero_add, pow_one] at h1 ⊢
    have ha : (1 - s)⁻¹ * (1 - s) = 1 := inv_mul_cancel₀ h1
    field_simp
    linear_combination (-((1 - s)⁻¹ * (1 - s)) - 1) * ha
  | succ m =>
    have h : HasDerivAt (logTestDerivs (m + 1)) _ s :=
      ((hasDerivAt_invPow 1 m h1).sub
        ((hasDerivAt_invPow 2 m h2).const_mul (2 ^ (m + 1) : ℂ))).const_mul (m.factorial : ℂ)
    refine h.congr_deriv ?_
    change (m.factorial : ℂ) * (((m : ℂ) + 1) * 1 * invPow 1 (m + 1) s -
        2 ^ (m + 1) * (((m : ℂ) + 1) * 2 * invPow 2 (m + 1) s)) =
      ((m + 1).factorial : ℂ) * (invPow 1 (m + 1) s - 2 ^ (m + 1 + 1) * invPow 2 (m + 1) s)
    rw [Nat.factorial_succ]
    push_cast
    ring
variable {n : ℕ}
private theorem partialDeriv_comp_sum (f : ℂ → ℂ) (i : Fin n) :
    partialDeriv i (fun z => f (∑ j, z j)) = fun z => deriv f (∑ j, z j) := by
  funext a
  have hsum : ∀ ζ : ℂ, ∑ j, (a + ζ • coordVector i) j = (∑ j, a j) + ζ := by
    intro ζ
    simp [Finset.sum_add_distrib, coordVector, ← Finset.mul_sum]
  change deriv (fun ζ : ℂ => f (∑ j, (a + ζ • coordVector i) j)) 0 = _
  simp only [hsum]
  rw [deriv_comp_const_add]
  simp
private theorem iteratedPartials_comp_sum (f : ℂ → ℂ) (l : List (Fin n)) :
    iteratedPartials l (fun z => f (∑ j, z j)) = fun z => deriv^[l.length] f (∑ j, z j) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change partialDeriv i (iteratedPartials l _) = _
    rw [ih, partialDeriv_comp_sum, List.length_cons]
    funext z
    rw [Function.iterate_succ_apply']
private theorem setPartial_comp_sum (f : ℂ → ℂ) (J : Finset (Fin n)) :
    setPartial J (fun z => f (∑ j, z j)) 0 = deriv^[J.card] f 0 := by
  rw [setPartial, iteratedPartials_comp_sum, Finset.length_sort]
  simp
private theorem sum_blockCount_factorial_eq (H : SeveralVariableCalculus.Claim) (hn : 1 ≤ n) :
    (∑ P : IndexPartition n, (blockCount P - 1).factorial * ∏ J ∈ P.parts, J.card.factorial) =
      (n - 1).factorial * (2 ^ n - 1) := by
  classical
  let B : Set ℂ := Metric.ball 0 (1 / 2)
  have hBo : IsOpen B := Metric.isOpen_ball
  have h0B : (0 : ℂ) ∈ B := Metric.mem_ball_self (by norm_num)
  have hsumc : Continuous fun z : Coordinates.ComplexCoordinates n => ∑ j, z j := by fun_prop
  let U : Set (Coordinates.ComplexCoordinates n) := (fun z => ∑ j, z j) ⁻¹' B
  have hU : IsOpen U := hBo.preimage hsumc
  have hU0 : (0 : Coordinates.ComplexCoordinates n) ∈ U := by
    change ∑ j, (0 : Coordinates.ComplexCoordinates n) j ∈ B
    simpa using h0B
  have hsum : HolomorphicOnSet U fun z : Coordinates.ComplexCoordinates n => ∑ j, z j := by
    rw [holomorphicOnSet_iff_lines]
    refine ⟨hU, hsumc.continuousOn, fun a _ j => Eventually.of_forall fun ζ => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hgdiff : DifferentiableOn ℂ testFunction B := fun s hs =>
    (hasDerivAt_testDerivs 0 s hs).differentiableAt.differentiableWithinAt
  have hh : HolomorphicOnSet U fun z : Coordinates.ComplexCoordinates n => testFunction (∑ j, z j) :=
    ((H n 1 hn le_rfl U hU _ (fun _ => _) hsum (fun _ => hsum)).2.2.2.1 B testFunction hBo hgdiff
      (fun z hz => hz)).1
  have h1 : testFunction (∑ j, (0 : Coordinates.ComplexCoordinates n) j) = 1 := by
    simp only [Pi.zero_apply, Finset.sum_const_zero, testFunction, invPow_zero]
    norm_num
  have hf := setPartial_log_eq H hn U _ hU hU0 hh h1
  have hb : ∀ J : Finset (Fin n), J.Nonempty →
      setPartial J (fun z => testFunction (∑ j, z j)) 0 = -(J.card.factorial : ℂ) := by
    intro J hJ
    obtain ⟨m, hm⟩ : ∃ m, J.card = m + 1 := ⟨J.card - 1, by have := hJ.card_pos; omega⟩
    rw [setPartial_comp_sum, hm]
    have := iterate_deriv_eqOn_of_hasDerivAt hBo testDerivs hasDerivAt_testDerivs (m + 1) h0B
    rw [show testDerivs 0 = testFunction from rfl] at this
    rw [this]
    simp [testDerivs, invPow_zero]
  have hl : setPartial (firstIndices n) (fun z => principalLog (testFunction (∑ j, z j))) 0 =
      deriv^[n] (fun s => principalLog (testFunction s)) 0 := by
    have := setPartial_comp_sum (n := n) (fun s => principalLog (testFunction s)) (firstIndices n)
    simpa using this
  rw [hl] at hf
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hv := iterate_deriv_eqOn_of_hasDerivAt hBo logTestDerivs hasDerivAt_logTestDerivs (m + 1)
    h0B
  rw [show logTestDerivs 0 = fun s => principalLog (testFunction s) from rfl] at hv
  rw [hv] at hf
  have hterm : ∀ P : IndexPartition (m + 1),
      (-1 : ℂ) ^ (blockCount P - 1) * ((blockCount P - 1).factorial : ℂ) *
        ∏ J ∈ P.parts, setPartial J (fun z => testFunction (∑ j, z j)) 0 =
      -(((blockCount P - 1).factorial * ∏ J ∈ P.parts, J.card.factorial : ℕ) : ℂ) := by
    intro P
    have hprod : ∏ J ∈ P.parts, setPartial J (fun z => testFunction (∑ j, z j)) 0 =
        (-1) ^ blockCount P * ∏ J ∈ P.parts, (J.card.factorial : ℂ) := by
      calc ∏ J ∈ P.parts, setPartial J (fun z => testFunction (∑ j, z j)) 0
          = ∏ J ∈ P.parts, (-1 : ℂ) * (J.card.factorial : ℂ) :=
            Finset.prod_congr rfl fun J hJ => by
              rw [hb J (P.nonempty_of_mem_parts hJ)]
              ring
        _ = (-1) ^ blockCount P * ∏ J ∈ P.parts, (J.card.factorial : ℂ) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
            rfl
    obtain ⟨c, hc⟩ : ∃ c, blockCount P = c + 1 :=
      ⟨blockCount P - 1, by have := one_le_blockCount (by omega) P; omega⟩
    rw [hprod, hc]
    simp only [Nat.add_sub_cancel]
    push_cast
    have hsq : (-1 : ℂ) ^ c * (-1) ^ (c + 1) = -1 := by
      rw [← pow_add, show c + (c + 1) = 2 * c + 1 by ring, pow_succ, pow_mul]
      simp
    linear_combination (((c.factorial : ℂ)) * ∏ J ∈ P.parts, (J.card.factorial : ℂ)) * hsq
  rw [Finset.sum_congr rfl fun P _ => hterm P, Finset.sum_neg_distrib] at hf
  simp only [logTestDerivs, invPow_zero] at hf
  have hone : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  have hcast : ((∑ P : IndexPartition (m + 1),
        (blockCount P - 1).factorial * ∏ J ∈ P.parts, J.card.factorial : ℕ) : ℂ) =
      (((m + 1 - 1).factorial * (2 ^ (m + 1) - 1) : ℕ) : ℂ) := by
    rw [Nat.cast_mul, Nat.cast_sub hone, Nat.add_sub_cancel, Nat.cast_sum]
    push_cast
    push_cast at hf
    linear_combination hf
  exact_mod_cast hcast
end Count
theorem claim_holds (H : SeveralVariableCalculus.Claim) : MomentCumulant.Claim :=
  fun _ hn => ⟨fun U h hU h0 hh h1 => setPartial_log_eq H hn U h hU h0 hh h1,
    sum_blockCount_factorial_eq H hn, card_indexPartition_le_factorial _⟩
end YangMills.Construction.SourcesAndGluing.MomentCumulant
end

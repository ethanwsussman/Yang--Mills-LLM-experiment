import YangMills.Construction.ResponseInTheExpansion.PairingsOfASum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open Finset
variable {ι : Type} [LinearOrder ι]
open Classical in
private def matchings (S : Finset ι) : Finset (Finset (Finset ι)) :=
  S.powerset.powerset.filter (IsPairing S)
private def pairWeight (G : ι → ι → ℝ) (B : Finset ι) : ℝ :=
  if h : B.Nonempty then G (B.min' h) (B.max' h) else 1
private theorem matchingSum_eq_sum (S : Finset ι) (G : ι → ι → ℝ) :
    matchingSum S G = ∑ P ∈ matchings S, ∏ B ∈ P, pairWeight G B := rfl
private theorem mem_matchings {S : Finset ι} {P : Finset (Finset ι)} :
    P ∈ matchings S ↔ IsPairing S P := by
  classical
  unfold matchings
  rw [mem_filter, mem_powerset]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨fun B hB => mem_powerset.2 (h.card_two_subset B hB).2, h⟩
private theorem pairWeight_pair (G : ι → ι → ℝ) {a b : ι} (hab : a < b) :
    pairWeight G {a, b} = G a b := by
  have hne : ({a, b} : Finset ι).Nonempty := ⟨a, by simp⟩
  unfold pairWeight
  rw [dif_pos hne]
  have h1 : ({a, b} : Finset ι).min' hne = a := by
    apply le_antisymm
    · exact min'_le _ _ (by simp)
    · apply le_min'
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact le_rfl
      · exact hab.le
  have h2 : ({a, b} : Finset ι).max' hne = b := by
    apply le_antisymm
    · apply max'_le
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hab.le
      · exact le_rfl
    · exact le_max' _ _ (by simp)
  rw [h1, h2]
private theorem matchings_eq_biUnion (S : Finset ι) (hS : S.Nonempty) :
    matchings S = (S.erase (S.min' hS)).biUnion fun b =>
      (matchings ((S.erase (S.min' hS)).erase b)).image (insert {S.min' hS, b}) := by
  classical
  set a := S.min' hS with ha
  have haS : a ∈ S := min'_mem _ _
  ext P
  simp only [mem_biUnion, mem_image, mem_matchings]
  constructor
  · intro h
    obtain ⟨B, hB, haB⟩ := h.covers a haS
    obtain ⟨hc, hsub⟩ := h.card_two_subset B hB
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 hc
    obtain ⟨b, hba, hBeq⟩ : ∃ b, b ≠ a ∧ ({x, y} : Finset ι) = {a, b} := by
      simp only [mem_insert, mem_singleton] at haB
      rcases haB with rfl | rfl
      · exact ⟨y, hxy.symm, rfl⟩
      · exact ⟨x, hxy, pair_comm _ _⟩
    rw [hBeq] at hB hsub
    have hbS : b ∈ S := hsub (by simp)
    refine ⟨b, mem_erase.2 ⟨hba, hbS⟩, P.erase {a, b}, ?_, insert_erase hB⟩
    refine ⟨?_, ?_, ?_⟩
    · intro B' hB'
      obtain ⟨hne, hB'P⟩ := mem_erase.1 hB'
      refine ⟨(h.card_two_subset B' hB'P).1, ?_⟩
      intro i hi
      have hd' : Disjoint B' {a, b} := h.disjoint B' hB'P {a, b} hB hne
      have hia : i ≠ a := fun e => (disjoint_left.1 hd' hi) (by simp [e])
      have hib : i ≠ b := fun e => (disjoint_left.1 hd' hi) (by simp [e])
      exact mem_erase.2 ⟨hib, mem_erase.2 ⟨hia, (h.card_two_subset B' hB'P).2 hi⟩⟩
    · intro B₁ h₁ B₂ h₂ hne
      exact h.disjoint B₁ (mem_of_mem_erase h₁) B₂ (mem_of_mem_erase h₂) hne
    · intro i hi
      obtain ⟨hib, hi'⟩ := mem_erase.1 hi
      obtain ⟨hia, hiS⟩ := mem_erase.1 hi'
      obtain ⟨B', hB', hiB'⟩ := h.covers i hiS
      refine ⟨B', mem_erase.2 ⟨?_, hB'⟩, hiB'⟩
      rintro rfl
      simp only [mem_insert, mem_singleton] at hiB'
      tauto
  · rintro ⟨b, hb, P', hP', rfl⟩
    obtain ⟨hba, hbS⟩ := mem_erase.1 hb
    have hnot : ∀ B' ∈ P', Disjoint B' {a, b} := by
      intro B' hB'
      rw [disjoint_left]
      intro i hi hi2
      have := (hP'.card_two_subset B' hB').2 hi
      simp only [mem_insert, mem_singleton] at hi2
      rcases hi2 with rfl | rfl
      · exact (mem_erase.1 (mem_erase.1 this).2).1 rfl
      · exact (mem_erase.1 this).1 rfl
    refine ⟨?_, ?_, ?_⟩
    · intro B hB
      rcases mem_insert.1 hB with rfl | hB
      · refine ⟨card_pair hba.symm, ?_⟩
        intro i hi
        simp only [mem_insert, mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact haS
        · exact hbS
      · refine ⟨(hP'.card_two_subset B hB).1, ?_⟩
        intro i hi
        exact mem_of_mem_erase (mem_of_mem_erase ((hP'.card_two_subset B hB).2 hi))
    · intro B₁ h₁ B₂ h₂ hne
      rcases mem_insert.1 h₁ with rfl | h₁
      · rcases mem_insert.1 h₂ with rfl | h₂
        · exact absurd rfl hne
        · exact (hnot B₂ h₂).symm
      · rcases mem_insert.1 h₂ with rfl | h₂
        · exact hnot B₁ h₁
        · exact hP'.disjoint B₁ h₁ B₂ h₂ hne
    · intro i hi
      by_cases hia : i = a
      · exact ⟨{a, b}, mem_insert_self _ _, by simp [hia]⟩
      by_cases hib : i = b
      · exact ⟨{a, b}, mem_insert_self _ _, by simp [hib]⟩
      obtain ⟨B', hB', hiB'⟩ := hP'.covers i (mem_erase.2 ⟨hib, mem_erase.2 ⟨hia, hi⟩⟩)
      exact ⟨B', mem_insert_of_mem hB', hiB'⟩
private theorem matchingSum_min_rec (S : Finset ι) (hS : S.Nonempty) (G : ι → ι → ℝ) :
    matchingSum S G = ∑ b ∈ S.erase (S.min' hS),
      G (S.min' hS) b * matchingSum ((S.erase (S.min' hS)).erase b) G := by
  classical
  set a := S.min' hS with ha
  rw [matchingSum_eq_sum, matchings_eq_biUnion S hS, sum_biUnion]
  · refine sum_congr rfl fun b hb => ?_
    obtain ⟨hba, hbS⟩ := mem_erase.1 hb
    have hlt : a < b := lt_of_le_of_ne (min'_le _ _ hbS) (Ne.symm hba)
    have hnotin : ∀ P ∈ matchings ((S.erase a).erase b), ({a, b} : Finset ι) ∉ P := by
      intro P hP hmem
      have := ((mem_matchings.1 hP).card_two_subset _ hmem).2 (show a ∈ ({a, b} : Finset ι) by simp)
      exact (mem_erase.1 (mem_erase.1 this).2).1 rfl
    rw [sum_image, matchingSum_eq_sum, mul_sum]
    · refine sum_congr rfl fun P hP => ?_
      rw [prod_insert (hnotin P hP), pairWeight_pair G hlt]
    · intro P₁ h₁ P₂ h₂ he
      have h₁' := hnotin P₁ h₁
      have h₂' := hnotin P₂ h₂
      have he' : insert ({a, b} : Finset ι) P₁ = insert {a, b} P₂ := he
      have := congrArg (fun Q => Q.erase ({a, b} : Finset ι)) he'
      simpa [erase_insert h₁', erase_insert h₂'] using this
  · intro b hb b' hb' hne
    rw [Function.onFun, disjoint_left]
    intro P hP hP'
    obtain ⟨P₁, h₁, rfl⟩ := mem_image.1 hP
    obtain ⟨P₂, h₂, he⟩ := mem_image.1 hP'
    have hS1 : IsPairing S (insert {a, b} P₁) := by
      have hmem : insert {a, b} P₁ ∈ matchings S := by
        rw [matchings_eq_biUnion S hS]
        exact mem_biUnion.2 ⟨b, hb, mem_image.2 ⟨P₁, h₁, rfl⟩⟩
      exact mem_matchings.1 hmem
    have hin : ({a, b'} : Finset ι) ∈ insert {a, b} P₁ := by
      rw [← he]; exact mem_insert_self _ _
    have hne2 : ({a, b} : Finset ι) ≠ {a, b'} := by
      intro e
      have : b ∈ ({a, b'} : Finset ι) := by rw [← e]; simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h
      · exact (mem_erase.1 hb).1 h
      · exact hne h
    have hd := hS1.disjoint _ (mem_insert_self _ _) _ hin hne2
    exact (disjoint_left.1 hd (show a ∈ ({a, b} : Finset ι) by simp)) (by simp)
private theorem matchingSum_empty (G : ι → ι → ℝ) : matchingSum (∅ : Finset ι) G = 1 := by
  classical
  have h : matchings (∅ : Finset ι) = {∅} := by
    ext P
    rw [mem_matchings, mem_singleton]
    constructor
    · intro hP
      rw [eq_empty_iff_forall_notMem]
      intro B hB
      have h2 := hP.card_two_subset B hB
      have : B = ∅ := subset_empty.1 h2.2
      rw [this] at h2
      simp at h2
    · rintro rfl
      exact ⟨by simp, by simp, by simp⟩
  rw [matchingSum_eq_sum, h]
  simp
private theorem card_erase_erase_add_two {S : Finset ι} {a b : ι} (ha : a ∈ S) (hb : b ∈ S.erase a) :
    ((S.erase a).erase b).card + 2 = S.card := by
  have h1 := card_erase_of_mem hb
  have h2 := card_erase_of_mem ha
  have h3 : 0 < (S.erase a).card := card_pos.2 ⟨b, hb⟩
  omega
private theorem abs_matchingSum_le (S : Finset ι) (G : ι → ι → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hG : ∀ i j, |G i j| ≤ b ^ 2) :
    |matchingSum S G| ≤ (S.card).factorial * b ^ S.card := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp at hn
      subst hn
      simp [matchingSum_empty]
    · rw [matchingSum_min_rec S hS]
      set a := S.min' hS
      have haS : a ∈ S := min'_mem _ _
      have hcard : (S.erase a).card + 1 = n := by
        rw [card_erase_of_mem haS]; have := card_pos.2 hS; omega
      have hterm : ∀ c ∈ S.erase a, |G a c * matchingSum ((S.erase a).erase c) G| ≤
          ((n - 2).factorial : ℝ) * b ^ n := by
        intro c hc
        have hr := card_erase_erase_add_two haS hc
        have hi := ih ((S.erase a).erase c).card (by omega) ((S.erase a).erase c) rfl
        have hn2 : ((S.erase a).erase c).card = n - 2 := by omega
        rw [hn2] at hi
        rw [abs_mul]
        calc |G a c| * |matchingSum ((S.erase a).erase c) G|
            ≤ b ^ 2 * (((n - 2).factorial : ℝ) * b ^ (n - 2)) :=
              mul_le_mul (hG _ _) hi (abs_nonneg _) (by positivity)
          _ = ((n - 2).factorial : ℝ) * b ^ n := by
              have : b ^ n = b ^ (n - 2) * b ^ 2 := by
                rw [← pow_add]; congr 1; omega
              rw [this]
              ring
      by_cases hn1 : n = 1
      · have : S.erase a = ∅ := by
          rw [← card_eq_zero]; omega
        simp [this]
        positivity
      have hn2 : 2 ≤ n := by omega
      calc |∑ c ∈ S.erase a, G a c * matchingSum ((S.erase a).erase c) G|
          ≤ ∑ c ∈ S.erase a, |G a c * matchingSum ((S.erase a).erase c) G| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ _c ∈ S.erase a, ((n - 2).factorial : ℝ) * b ^ n := sum_le_sum hterm
        _ = ((n - 1 : ℕ) : ℝ) * (((n - 2).factorial : ℝ) * b ^ n) := by
            rw [sum_const, nsmul_eq_mul]
            have : (S.erase a).card = n - 1 := by omega
            rw [this]
        _ = ((n - 1).factorial : ℝ) * b ^ n := by
            have : n - 1 = (n - 2) + 1 := by omega
            rw [this, Nat.factorial_succ]
            push_cast
            ring
        _ ≤ (n.factorial : ℝ) * b ^ n := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast Nat.factorial_le (by omega)
private theorem abs_matchingSum_le_of_small (S : Finset ι) (G : ι → ι → ℝ) (b δ : ℝ) (hb : 0 ≤ b)
    (hS : S.Nonempty) (hδ : δ ≤ b ^ 2) (hG : ∀ i j, |G i j| ≤ δ) :
    |matchingSum S G| ≤ (S.card).factorial * δ * b ^ (S.card - 2) := by
  rw [matchingSum_min_rec S hS]
  set a := S.min' hS
  have haS : a ∈ S := min'_mem _ _
  set n := S.card with hn
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hG a a)
  have hterm : ∀ c ∈ S.erase a, |G a c * matchingSum ((S.erase a).erase c) G| ≤
      δ * (((n - 2).factorial : ℝ) * b ^ (n - 2)) := by
    intro c hc
    have hr := card_erase_erase_add_two haS hc
    have hi := abs_matchingSum_le ((S.erase a).erase c) G b hb (fun i j => (hG i j).trans hδ)
    have hn2 : ((S.erase a).erase c).card = n - 2 := by omega
    rw [hn2] at hi
    rw [abs_mul]
    exact mul_le_mul (hG _ _) hi (abs_nonneg _) hδ0
  have hcard : (S.erase a).card = n - 1 := by rw [card_erase_of_mem haS]
  by_cases hn1 : n ≤ 1
  · have : S.erase a = ∅ := by
      rw [← card_eq_zero]; omega
    simp [this]
    positivity
  calc |∑ c ∈ S.erase a, G a c * matchingSum ((S.erase a).erase c) G|
      ≤ ∑ c ∈ S.erase a, |G a c * matchingSum ((S.erase a).erase c) G| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ S.erase a, δ * (((n - 2).factorial : ℝ) * b ^ (n - 2)) := sum_le_sum hterm
    _ = ((n - 1 : ℕ) : ℝ) * (δ * (((n - 2).factorial : ℝ) * b ^ (n - 2))) := by
        rw [sum_const, nsmul_eq_mul, hcard]
    _ = ((n - 1).factorial : ℝ) * δ * b ^ (n - 2) := by
        have : n - 1 = (n - 2) + 1 := by omega
        rw [this, Nat.factorial_succ]
        push_cast
        ring
    _ ≤ (n.factorial : ℝ) * δ * b ^ (n - 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hδ0
        exact_mod_cast Nat.factorial_le (by omega)
private theorem matchingSum_sq_smul (S : Finset ι) (G : ι → ι → ℝ) (c : ℝ) :
    matchingSum S (fun i j => c ^ 2 * G i j) = c ^ S.card * matchingSum S G := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp at hn
      subst hn
      simp [matchingSum_empty]
    · rw [matchingSum_min_rec S hS, matchingSum_min_rec S hS G, mul_sum]
      set a := S.min' hS
      have haS : a ∈ S := min'_mem _ _
      refine sum_congr rfl fun d hd => ?_
      have hr := card_erase_erase_add_two haS hd
      rw [ih _ (by omega) _ rfl]
      have : n = ((S.erase a).erase d).card + 2 := by omega
      conv_rhs => rw [this, pow_add]
      ring
private theorem matchingSum_add (S : Finset ι) (A B : ι → ι → ℝ) :
    matchingSum S (fun i j => A i j + B i j) =
      ∑ I ∈ S.powerset, matchingSum I A * matchingSum (S \ I) B := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp [matchingSum_empty]
    · set a := S.min' hS with ha
      have haS : a ∈ S := min'_mem _ _
      set R := S.erase a with hR
      have hSR : S = insert a R := (insert_erase haS).symm
      have haR : a ∉ R := notMem_erase _ _
      have hmin : ∀ i ∈ R, a < i := fun i hi =>
        lt_of_le_of_ne (min'_le _ _ (mem_of_mem_erase hi)) (Ne.symm (mem_erase.1 hi).1)
      have hrecI : ∀ (I : Finset ι) (G : ι → ι → ℝ), I ⊆ R →
          matchingSum (insert a I) G = ∑ b ∈ I, G a b * matchingSum (I.erase b) G := by
        intro I G hI
        have hne : (insert a I).Nonempty := ⟨a, mem_insert_self _ _⟩
        have hm : (insert a I).min' hne = a := by
          apply le_antisymm
          · exact min'_le _ _ (mem_insert_self _ _)
          · apply le_min'
            intro y hy
            rcases mem_insert.1 hy with rfl | hy
            · exact le_rfl
            · exact (hmin y (hI hy)).le
        have hnot : a ∉ I := fun h => haR (hI h)
        rw [matchingSum_min_rec _ hne, hm, erase_insert hnot]
      rw [hSR, hrecI R _ subset_rfl, sum_powerset_insert haR]
      have hdiff1 : ∀ I ∈ R.powerset, insert a R \ I = insert a (R \ I) := by
        intro I hI
        have : a ∉ I := fun h => haR (mem_powerset.1 hI h)
        rw [insert_sdiff_of_notMem _ this]
      have hdiff2 : ∀ I ∈ R.powerset, insert a R \ insert a I = R \ I := by
        intro I hI
        ext z
        simp only [mem_sdiff, mem_insert]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact absurd (Or.inl h1) h2
          · exact ⟨h1, fun h => h2 (Or.inr h)⟩
        · rintro ⟨h1, h2⟩
          exact ⟨Or.inr h1, fun h => h.elim (fun e => haR (e ▸ h1)) h2⟩
      have hcardR : R.card < n := by
        rw [← hn, hR, card_erase_of_mem haS]
        have := card_pos.2 hS
        omega
      have hA : ∑ b ∈ R, A a b * ∑ I ∈ (R.erase b).powerset,
            matchingSum I A * matchingSum (R.erase b \ I) B =
          ∑ I ∈ R.powerset, matchingSum (insert a I) A * matchingSum (R \ I) B := by
        have : ∀ I ∈ R.powerset, matchingSum (insert a I) A * matchingSum (R \ I) B =
            ∑ b ∈ I, A a b * (matchingSum (I.erase b) A * matchingSum (R \ I) B) := by
          intro I hI
          rw [hrecI I A (mem_powerset.1 hI), sum_mul]
          exact sum_congr rfl fun b _ => by ring
        rw [sum_congr rfl this]
        simp_rw [mul_sum]
        rw [sum_sigma', sum_sigma']
        refine sum_bij' (fun x _ => ⟨insert x.1 x.2, x.1⟩) (fun y _ => ⟨y.2, y.1.erase y.2⟩) ?_ ?_ ?_ ?_ ?_
        · rintro ⟨b, I⟩ h
          simp only [mem_sigma, mem_powerset] at h ⊢
          refine ⟨insert_subset h.1 (h.2.trans (erase_subset _ _)), mem_insert_self _ _⟩
        · rintro ⟨I, b⟩ h
          simp only [mem_sigma, mem_powerset] at h ⊢
          exact ⟨h.1 h.2, erase_subset_erase _ h.1⟩
        · rintro ⟨b, I⟩ h
          simp only [mem_sigma, mem_powerset] at h
          have hb : b ∉ I := fun hb => (mem_erase.1 (h.2 hb)).1 rfl
          simp [erase_insert hb]
        · rintro ⟨I, b⟩ h
          simp only [mem_sigma, mem_powerset] at h
          simp [insert_erase h.2]
        · rintro ⟨b, I⟩ h
          simp only [mem_sigma, mem_powerset] at h
          have hb : b ∉ I := fun hb => (mem_erase.1 (h.2 hb)).1 rfl
          simp only [erase_insert hb]
          have : R.erase b \ I = R \ insert b I := by
            ext z; simp only [mem_sdiff, mem_erase, mem_insert]; tauto
          rw [this]
      have hB : ∑ b ∈ R, B a b * ∑ I ∈ (R.erase b).powerset,
            matchingSum I A * matchingSum (R.erase b \ I) B =
          ∑ I ∈ R.powerset, matchingSum I A * matchingSum (insert a (R \ I)) B := by
        have : ∀ I ∈ R.powerset, matchingSum I A * matchingSum (insert a (R \ I)) B =
            ∑ b ∈ R \ I, B a b * (matchingSum I A * matchingSum ((R \ I).erase b) B) := by
          intro I hI
          rw [hrecI (R \ I) B sdiff_subset, mul_sum]
          exact sum_congr rfl fun b _ => by ring
        rw [sum_congr rfl this]
        simp_rw [mul_sum]
        rw [sum_comm' (t' := R.powerset) (s' := fun I => R \ I)]
        · refine sum_congr rfl fun I hI => sum_congr rfl fun b hb => ?_
          have : R.erase b \ I = (R \ I).erase b := by
            ext z; simp only [mem_sdiff, mem_erase]; tauto
          rw [this]
        · intro b I
          simp only [mem_powerset, mem_sdiff]
          constructor
          · rintro ⟨hb, hI⟩
            have hbI : b ∉ I := fun h => (mem_erase.1 (hI h)).1 rfl
            exact ⟨⟨hb, hbI⟩, hI.trans (erase_subset _ _)⟩
          · rintro ⟨⟨hb, hbI⟩, hI⟩
            refine ⟨hb, fun z hz => mem_erase.2 ⟨fun e => hbI (e ▸ hz), hI hz⟩⟩
      calc ∑ b ∈ R, (A a b + B a b) * matchingSum (R.erase b) (fun i j => A i j + B i j)
          = ∑ b ∈ R, (A a b + B a b) *
              ∑ I ∈ (R.erase b).powerset, matchingSum I A * matchingSum (R.erase b \ I) B := by
            refine sum_congr rfl fun b hb => ?_
            have : (R.erase b).card < n := lt_of_le_of_lt (card_le_card (erase_subset _ _)) hcardR
            rw [ih _ this _ rfl]
        _ = ∑ I ∈ R.powerset, matchingSum I A * matchingSum (insert a R \ I) B +
              ∑ I ∈ R.powerset, matchingSum (insert a I) A * matchingSum (insert a R \ insert a I) B := by
            simp_rw [add_mul]
            rw [sum_add_distrib, hA, hB, add_comm]
            congr 1
            · exact sum_congr rfl fun I hI => by rw [hdiff1 I hI]
            · exact sum_congr rfl fun I hI => by rw [hdiff2 I hI]
private theorem matchingSum_map {κ : Type} [LinearOrder κ] (f : ι ↪o κ) (S : Finset ι)
    (G : κ → κ → ℝ) :
    matchingSum (S.map f.toEmbedding) G = matchingSum S (fun a b => G (f a) (f b)) := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp [matchingSum_empty]
    · have hne : (S.map f.toEmbedding).Nonempty := hS.map
      have hmin : (S.map f.toEmbedding).min' hne = f (S.min' hS) := by
        apply le_antisymm
        · exact min'_le _ _ (mem_map_of_mem _ (min'_mem _ _))
        · apply le_min'
          intro y hy
          obtain ⟨z, hz, rfl⟩ := mem_map.1 hy
          exact f.monotone (min'_le _ _ hz)
      have hera : ∀ (Q : Finset ι) (c : ι),
          (Q.map f.toEmbedding).erase (f c) = (Q.erase c).map f.toEmbedding := by
        intro Q c
        ext z
        simp only [mem_erase, mem_map, RelEmbedding.coe_toEmbedding]
        constructor
        · rintro ⟨h1, w, hw, rfl⟩
          exact ⟨w, ⟨fun e => h1 (by rw [e]), hw⟩, rfl⟩
        · rintro ⟨w, ⟨h1, hw⟩, rfl⟩
          exact ⟨fun e => h1 (f.injective e), w, hw, rfl⟩
      rw [matchingSum_min_rec _ hne, matchingSum_min_rec S hS, hmin]
      have e1 := hera S (S.min' hS)
      change (S.map f.toEmbedding).erase (f (S.min' hS)) = _ at e1
      rw [e1, sum_map]
      refine sum_congr rfl fun b hb => ?_
      have hr := card_erase_erase_add_two (min'_mem S hS) hb
      have e2 := hera (S.erase (S.min' hS)) b
      change ((S.erase (S.min' hS)).map f.toEmbedding).erase (f b) = _ at e2
      simp only [RelEmbedding.coe_toEmbedding]
      rw [e2, ih _ (by omega) _ rfl]
private theorem wickPairingSum_eq_matchingSum (q : ℕ) (G : Fin q → Fin q → ℝ) :
    wickPairingSum G = matchingSum Finset.univ G := by
  classical
  unfold wickPairingSum
  rw [← sum_filter, matchingSum]
  refine sum_bij (fun π _ => π.parts) ?_ ?_ ?_ ?_
  · intro π hπ
    have hg := (mem_filter.1 hπ).2
    refine mem_filter.2 ⟨mem_powerset.2 fun B _ => mem_powerset.2 (subset_univ _), ?_, ?_, ?_⟩
    · exact fun B hB => ⟨hg B hB, subset_univ _⟩
    · exact fun B hB B' hB' hne => π.disjoint hB hB' hne
    · intro i hi
      obtain ⟨B, hB, hiB⟩ := π.exists_mem hi
      exact ⟨B, hB, hiB⟩
  · intro π₁ _ π₂ _ h
    exact Finpartition.ext h
  · intro P hP
    have hPp := (mem_filter.1 hP).2
    refine ⟨⟨P, ?_, ?_, ?_⟩, ?_, rfl⟩
    · rw [Finset.supIndep_iff_pairwiseDisjoint]
      intro B hB B' hB' hne
      exact hPp.disjoint B hB B' hB' hne
    · ext i
      simp only [mem_sup, id, mem_univ, iff_true]
      obtain ⟨B, hB, hiB⟩ := hPp.covers i (mem_univ _)
      exact ⟨B, hB, hiB⟩
    · intro h0
      have := (hPp.card_two_subset _ h0).1
      simp at this
    · exact mem_filter.2 ⟨mem_univ _, fun B hB => (hPp.card_two_subset B hB).1⟩
  · intro π hπ
    rfl
theorem matchingSumProperties_holds : matchingSumPropertiesStatement := by
  refine ⟨wickPairingSum_eq_matchingSum, ?_, ?_⟩
  · intro q I G
    rw [wickPairingSum_eq_matchingSum]
    have h := matchingSum_map (I.orderEmbOfFin rfl) (Finset.univ : Finset (Fin I.card)) G
    rw [← h]
    congr 1
    ext z
    simp only [mem_map, mem_univ, true_and, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨a, rfl⟩
      exact orderEmbOfFin_mem _ _ _
    · intro hz
      have : z ∈ Set.range (I.orderEmbOfFin rfl) := by
        rw [range_orderEmbOfFin]; exact hz
      exact this
  · intro ι _
    exact ⟨matchingSum_empty, matchingSum_add, abs_matchingSum_le, abs_matchingSum_le_of_small,
      matchingSum_sq_smul⟩
end YangMills.Construction.ResponseInTheExpansion
end

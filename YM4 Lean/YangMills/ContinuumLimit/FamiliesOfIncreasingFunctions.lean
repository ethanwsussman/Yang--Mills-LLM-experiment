import Mathlib
namespace YangMills.ContinuumLimit

open Set Filter Topology

def aboveFloor (F : ℝ) (x : ℕ → ℝ → ℝ) (k : ℕ) : Set ℝ :=
  {β | F < β ∧ ∀ j < k, F < x j β}

def stayingAbove (f : ℝ) (x : ℕ → ℝ → ℝ) (k : ℕ) (β : ℝ) : Prop :=
  f ≤ β ∧ ∀ j < k, f ≤ x j β

def HasSlopeNearOneAboveFloor (F : ℝ) (x : ℕ → ℝ → ℝ) (k : ℕ) : Prop :=
  ∃ d : ℝ → ℝ, ∀ β ∈ aboveFloor F x k, HasDerivAt (x k) (d β) β ∧ 3 / 4 ≤ d β ∧ d β ≤ 5 / 4

theorem aboveFloor_zero (F : ℝ) (x : ℕ → ℝ → ℝ) : aboveFloor F x 0 = Ioi F := by
  ext β
  simp [aboveFloor]

theorem aboveFloor_succ (F : ℝ) (x : ℕ → ℝ → ℝ) (k : ℕ) :
    aboveFloor F x (k + 1) = aboveFloor F x k ∩ x k ⁻¹' Ioi F := by
  ext β
  simp only [aboveFloor, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioi]
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨⟨h0, fun j hj => h j (hj.trans (Nat.lt_add_one k))⟩, h k (Nat.lt_add_one k)⟩
  · rintro ⟨⟨h0, h⟩, hk⟩
    refine ⟨h0, fun j hj => ?_⟩
    rcases lt_or_eq_of_le (Nat.lt_add_one_iff.mp hj) with hj | hj
    · exact h j hj
    · rw [hj]
      exact hk

theorem aboveFloor_subset_of_le (F : ℝ) (x : ℕ → ℝ → ℝ) {k k' : ℕ} (h : k ≤ k') :
    aboveFloor F x k' ⊆ aboveFloor F x k :=
  fun _ hβ => ⟨hβ.1, fun j hj => hβ.2 j (lt_of_lt_of_le hj h)⟩

theorem stayingAbove_of_mem_aboveFloor {f F : ℝ} (hfF : f < F) (x : ℕ → ℝ → ℝ) {k : ℕ}
    {β : ℝ} (hβ : β ∈ aboveFloor F x k) : stayingAbove f x k β :=
  ⟨le_of_lt (hfF.trans hβ.1), fun j hj => le_of_lt (hfF.trans (hβ.2 j hj))⟩

theorem continuousOn_of_hasSlopeNearOneAboveFloor {F : ℝ} {x : ℕ → ℝ → ℝ} {k : ℕ}
    (hk : HasSlopeNearOneAboveFloor F x k) : ContinuousOn (x k) (aboveFloor F x k) := by
  obtain ⟨d, hd⟩ := hk
  exact fun γ hγ => (hd γ hγ).1.continuousAt.continuousWithinAt

theorem sub_bounds_of_hasSlopeNearOneAboveFloor {F : ℝ} {x : ℕ → ℝ → ℝ} {k : ℕ}
    (hup : IsUpperSet (aboveFloor F x k)) (hk : HasSlopeNearOneAboveFloor F x k)
    {β β' : ℝ} (hβ : β ∈ aboveFloor F x k) (hββ' : β ≤ β') :
    3 / 4 * (β' - β) ≤ x k β' - x k β ∧ x k β' - x k β ≤ 5 / 4 * (β' - β) := by
  obtain ⟨d, hd⟩ := hk
  rcases eq_or_lt_of_le hββ' with h | h
  · subst h
    simp
  · have hIcc : Icc β β' ⊆ aboveFloor F x k := fun γ hγ => hup hγ.1 hβ
    have hcont : ContinuousOn (x k) (Icc β β') := fun γ hγ =>
      (hd γ (hIcc hγ)).1.continuousAt.continuousWithinAt
    obtain ⟨c, hc, hdc⟩ := exists_hasDerivAt_eq_slope (x k) d h hcont
      (fun γ hγ => (hd γ (hIcc (Ioo_subset_Icc_self hγ))).1)
    have hpos : 0 < β' - β := sub_pos.mpr h
    have hc' := hd c (hIcc (Ioo_subset_Icc_self hc))
    have heq : x k β' - x k β = d c * (β' - β) := by
      rw [hdc]
      exact (div_mul_cancel₀ _ hpos.ne').symm
    rw [heq]
    exact ⟨mul_le_mul_of_nonneg_right hc'.2.1 hpos.le, mul_le_mul_of_nonneg_right hc'.2.2 hpos.le⟩

theorem strictMonoOn_of_hasSlopeNearOneAboveFloor {F : ℝ} {x : ℕ → ℝ → ℝ} {k : ℕ}
    (hup : IsUpperSet (aboveFloor F x k)) (hk : HasSlopeNearOneAboveFloor F x k) :
    StrictMonoOn (x k) (aboveFloor F x k) := by
  intro β hβ β' _ h
  have h1 := (sub_bounds_of_hasSlopeNearOneAboveFloor hup hk hβ h.le).1
  have h2 : 0 < β' - β := sub_pos.mpr h
  linarith

theorem aboveFloor_succ_isOpen_isUpperSet_nonempty {F : ℝ} {x : ℕ → ℝ → ℝ} {k : ℕ}
    (hopen : IsOpen (aboveFloor F x k)) (hup : IsUpperSet (aboveFloor F x k))
    (hne : (aboveFloor F x k).Nonempty) (hk : HasSlopeNearOneAboveFloor F x k) :
    IsOpen (aboveFloor F x (k + 1)) ∧ IsUpperSet (aboveFloor F x (k + 1)) ∧
      (aboveFloor F x (k + 1)).Nonempty := by
  rw [aboveFloor_succ]
  refine ⟨?_, ?_, ?_⟩
  · exact (continuousOn_of_hasSlopeNearOneAboveFloor hk).isOpen_inter_preimage hopen isOpen_Ioi
  · intro β β' hββ' hβ
    refine ⟨hup hββ' hβ.1, ?_⟩
    have h1 := (sub_bounds_of_hasSlopeNearOneAboveFloor hup hk hβ.1 hββ').1
    have h2 : 0 ≤ β' - β := sub_nonneg.mpr hββ'
    have h3 : F < x k β := hβ.2
    show F < x k β'
    linarith
  · obtain ⟨β₁, hβ₁⟩ := hne
    have ha := abs_nonneg (F - x k β₁)
    have hle : β₁ ≤ β₁ + 4 / 3 * (|F - x k β₁| + 1) := by linarith
    refine ⟨β₁ + 4 / 3 * (|F - x k β₁| + 1), hup hle hβ₁, ?_⟩
    have h1 := (sub_bounds_of_hasSlopeNearOneAboveFloor hup hk hβ₁ hle).1
    have h4 : F - x k β₁ ≤ |F - x k β₁| := le_abs_self _
    show F < x k (β₁ + 4 / 3 * (|F - x k β₁| + 1))
    linarith

theorem aboveFloor_zero_isOpen_isUpperSet_nonempty (F : ℝ) (x : ℕ → ℝ → ℝ) :
    IsOpen (aboveFloor F x 0) ∧ IsUpperSet (aboveFloor F x 0) ∧ (aboveFloor F x 0).Nonempty := by
  rw [aboveFloor_zero]
  exact ⟨isOpen_Ioi, isUpperSet_Ioi F, nonempty_Ioi⟩

theorem aboveFloor_isOpen_isUpperSet_nonempty {F : ℝ} {x : ℕ → ℝ → ℝ} {k : ℕ}
    (hgood : ∀ j < k, HasSlopeNearOneAboveFloor F x j) :
    IsOpen (aboveFloor F x k) ∧ IsUpperSet (aboveFloor F x k) ∧ (aboveFloor F x k).Nonempty := by
  induction k with
  | zero => exact aboveFloor_zero_isOpen_isUpperSet_nonempty F x
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun j hj => hgood j (hj.trans (Nat.lt_add_one k)))
    exact aboveFloor_succ_isOpen_isUpperSet_nonempty h1 h2 h3 (hgood k (Nat.lt_add_one k))

theorem exists_mem_aboveFloor_near_floor {F : ℝ} {x : ℕ → ℝ → ℝ} {K : ℕ}
    (hK : ∀ j < K, IsUpperSet (aboveFloor F x j) ∧ HasSlopeNearOneAboveFloor F x j)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ β ∈ aboveFloor F x K, β < F + ε ∨ ∃ j < K, x j β < F + ε := by
  induction K with
  | zero =>
    refine ⟨F + ε / 2, ?_, Or.inl (by linarith)⟩
    rw [aboveFloor_zero]
    show F < F + ε / 2
    linarith
  | succ K ih =>
    obtain ⟨β₁, hβ₁, hw⟩ := ih (fun j hj => hK j (hj.trans (Nat.lt_add_one K)))
    obtain ⟨hup, hk⟩ := hK K (Nat.lt_add_one K)
    by_cases hF : F < x K β₁
    · refine ⟨β₁, ?_, ?_⟩
      · rw [aboveFloor_succ]
        exact ⟨hβ₁, hF⟩
      · rcases hw with hw | ⟨j, hj, hw⟩
        · exact Or.inl hw
        · exact Or.inr ⟨j, hj.trans (Nat.lt_add_one K), hw⟩
    · push Not at hF
      have hle : β₁ ≤ β₁ + 4 / 3 * (F + ε / 2 - x K β₁) := by linarith
      have h1 := (sub_bounds_of_hasSlopeNearOneAboveFloor hup hk hβ₁ hle).1
      have hIcc : Icc β₁ (β₁ + 4 / 3 * (F + ε / 2 - x K β₁)) ⊆ aboveFloor F x K :=
        fun γ hγ => hup hγ.1 hβ₁
      have hcont := (continuousOn_of_hasSlopeNearOneAboveFloor hk).mono hIcc
      have hmem : F + ε / 2 ∈ Icc (x K β₁) (x K (β₁ + 4 / 3 * (F + ε / 2 - x K β₁))) :=
        ⟨by linarith, by linarith⟩
      obtain ⟨β₃, hβ₃, hval⟩ := intermediate_value_Icc hle hcont hmem
      refine ⟨β₃, ?_, Or.inr ⟨K, Nat.lt_add_one K, by linarith⟩⟩
      rw [aboveFloor_succ]
      exact ⟨hIcc hβ₃, show F < x K β₃ by linarith⟩

theorem exists_unique_of_increasing_family {f F c : ℝ} {x : ℕ → ℝ → ℝ} (hx0 : x 0 = id)
    (hfF : f < F) (hgood : ∀ j, HasSlopeNearOneAboveFloor F x j)
    (hdesc : ∀ K β, stayingAbove f x K β → ∀ i ≤ K, x K β ≤ x i β + c)
    (K : ℕ) {P : ℝ} (hP : F + |c| + 1 ≤ P) :
    (∃! β, stayingAbove f x K β ∧ x K β = P) ∧
      ∀ β, stayingAbove f x K β → x K β = P → β ∈ aboveFloor F x K := by
  have hx0' : ∀ β, x 0 β = β := fun β => by rw [hx0]; rfl
  have hc : c ≤ |c| := le_abs_self c
  have hup : IsUpperSet (aboveFloor F x K) :=
    (aboveFloor_isOpen_isUpperSet_nonempty (fun j _ => hgood j)).2.1
  have hmem : ∀ β, stayingAbove f x K β → x K β = P → β ∈ aboveFloor F x K := by
    intro β hβ hval
    by_contra hnot
    have hlow : ∃ i ≤ K, x i β ≤ F := by
      by_cases h0 : F < β
      · have hn : ¬ ∀ j < K, F < x j β := fun h => hnot ⟨h0, h⟩
        push Not at hn
        obtain ⟨j, hj, hjF⟩ := hn
        exact ⟨j, hj.le, hjF⟩
      · exact ⟨0, Nat.zero_le K, by rw [hx0' β]; exact not_lt.mp h0⟩
    obtain ⟨i, hi, hiF⟩ := hlow
    have hd := hdesc K β hβ i hi
    linarith
  refine ⟨?_, hmem⟩
  have hmono := strictMonoOn_of_hasSlopeNearOneAboveFloor hup (hgood K)
  obtain ⟨β₁, hβ₁, hw⟩ := exists_mem_aboveFloor_near_floor (K := K)
    (fun j _ => ⟨(aboveFloor_isOpen_isUpperSet_nonempty (fun i _ => hgood i)).2.1, hgood j⟩)
    one_pos
  have hlow : ∃ i ≤ K, x i β₁ < F + 1 := by
    rcases hw with hw | ⟨j, hj, hw⟩
    · exact ⟨0, Nat.zero_le K, by rw [hx0' β₁]; exact hw⟩
    · exact ⟨j, hj.le, hw⟩
  obtain ⟨i, hi, hiF⟩ := hlow
  have hβ₁s := stayingAbove_of_mem_aboveFloor hfF x hβ₁
  have hK1 : x K β₁ < P := by
    have hd := hdesc K β₁ hβ₁s i hi
    linarith
  have hle : β₁ ≤ β₁ + 4 / 3 * (P - x K β₁) := by linarith
  have h1 := (sub_bounds_of_hasSlopeNearOneAboveFloor hup (hgood K) hβ₁ hle).1
  have hIcc : Icc β₁ (β₁ + 4 / 3 * (P - x K β₁)) ⊆ aboveFloor F x K :=
    fun γ hγ => hup hγ.1 hβ₁
  have hcont := (continuousOn_of_hasSlopeNearOneAboveFloor (hgood K)).mono hIcc
  obtain ⟨β, hβ, hval⟩ := intermediate_value_Icc hle hcont ⟨hK1.le, by linarith⟩
  refine ⟨β, ⟨stayingAbove_of_mem_aboveFloor hfF x (hIcc hβ), hval⟩, ?_⟩
  rintro β' ⟨hβ's, hβ'val⟩
  exact hmono.injOn (hmem β' hβ's hβ'val) (hIcc hβ) (hβ'val.trans hval.symm)

theorem strictMonoOn_inverse_of_increasing_family {f F c : ℝ} {x : ℕ → ℝ → ℝ}
    (hx0 : x 0 = id) (hfF : f < F) (hgood : ∀ j, HasSlopeNearOneAboveFloor F x j)
    (hdesc : ∀ K β, stayingAbove f x K β → ∀ i ≤ K, x K β ≤ x i β + c) (K : ℕ) {B : ℝ → ℝ}
    (hB : ∀ P, F + |c| + 1 ≤ P → stayingAbove f x K (B P) ∧ x K (B P) = P) :
    StrictMonoOn B (Ici (F + |c| + 1)) := by
  have hmemB : ∀ P, F + |c| + 1 ≤ P → B P ∈ aboveFloor F x K := fun P hP =>
    (exists_unique_of_increasing_family hx0 hfF hgood hdesc K hP).2 (B P) (hB P hP).1 (hB P hP).2
  have hmono := strictMonoOn_of_hasSlopeNearOneAboveFloor
    (aboveFloor_isOpen_isUpperSet_nonempty (fun j _ => hgood j)).2.1 (hgood K)
  intro P hP P' hP' hlt
  rw [← hmono.lt_iff_lt (hmemB P hP) (hmemB P' hP'), (hB P hP).2, (hB P' hP').2]
  exact hlt

theorem hasDerivAt_inverse_of_increasing_family {f F c : ℝ} {x : ℕ → ℝ → ℝ}
    (hx0 : x 0 = id) (hfF : f < F) (hgood : ∀ j, HasSlopeNearOneAboveFloor F x j)
    (hdesc : ∀ K β, stayingAbove f x K β → ∀ i ≤ K, x K β ≤ x i β + c) (K : ℕ) {B : ℝ → ℝ}
    (hB : ∀ P, F + |c| + 1 ≤ P → stayingAbove f x K (B P) ∧ x K (B P) = P)
    {d : ℝ → ℝ} (hd : ∀ β ∈ aboveFloor F x K, HasDerivAt (x K) (d β) β)
    {P : ℝ} (hP : F + |c| + 1 < P) :
    HasDerivAt B (d (B P))⁻¹ P := by
  have hmemB : ∀ Q, F + |c| + 1 ≤ Q → B Q ∈ aboveFloor F x K := fun Q hQ =>
    (exists_unique_of_increasing_family hx0 hfF hgood hdesc K hQ).2 (B Q) (hB Q hQ).1 (hB Q hQ).2
  have hup : IsUpperSet (aboveFloor F x K) :=
    (aboveFloor_isOpen_isUpperSet_nonempty (fun j _ => hgood j)).2.1
  have hlip : ∀ Q Q', F + |c| + 1 ≤ Q → F + |c| + 1 ≤ Q' →
      |B Q - B Q'| ≤ 4 / 3 * |Q - Q'| := by
    intro Q Q' hQ hQ'
    rcases le_total (B Q) (B Q') with h | h
    · have h1 := (sub_bounds_of_hasSlopeNearOneAboveFloor hup (hgood K) (hmemB Q hQ) h).1
      rw [(hB Q hQ).2, (hB Q' hQ').2] at h1
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h), abs_sub_comm]
      have h2 := le_abs_self (Q' - Q)
      linarith
    · have h1 := (sub_bounds_of_hasSlopeNearOneAboveFloor hup (hgood K) (hmemB Q' hQ') h).1
      rw [(hB Q hQ).2, (hB Q' hQ').2] at h1
      rw [abs_of_nonneg (sub_nonneg.mpr h)]
      have h2 := le_abs_self (Q - Q')
      linarith
  have hcontB : ContinuousAt B P := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨min (P - (F + |c| + 1)) (ε / 2), lt_min (sub_pos.mpr hP) (half_pos hε), ?_⟩
    intro Q hQ
    rw [Real.dist_eq] at hQ ⊢
    have hQ1 := abs_sub_lt_iff.mp (lt_of_lt_of_le hQ (min_le_left _ _))
    have hQ2 : |Q - P| < ε / 2 := lt_of_lt_of_le hQ (min_le_right _ _)
    have hQP : F + |c| + 1 ≤ Q := by linarith [hQ1.2]
    have h3 := hlip Q P hQP hP.le
    linarith
  obtain ⟨d₀, hd₀⟩ := hgood K
  have hm := hmemB P hP.le
  have hdd : d (B P) = d₀ (B P) := (hd (B P) hm).unique (hd₀ (B P) hm).1
  have hne : d (B P) ≠ 0 := by
    have h4 := (hd₀ (B P) hm).2.1
    rw [hdd]
    linarith
  have hev : ∀ᶠ Q in 𝓝 P, x K (B Q) = Q :=
    Filter.eventually_of_mem (Ici_mem_nhds hP) (fun Q hQ => (hB Q hQ).2)
  exact HasDerivAt.of_local_left_inverse hcontB (hd (B P) hm) hne hev

open Classical in
noncomputable def tunedPoint (f : ℝ) (x : ℕ → ℝ → ℝ) (K : ℕ) (P : ℝ) : ℝ :=
  if h : ∃ β, stayingAbove f x K β ∧ x K β = P then h.choose else P

theorem tunedPoint_spec {f F c : ℝ} {x : ℕ → ℝ → ℝ} (hx0 : x 0 = id) (hfF : f < F)
    (hgood : ∀ j, HasSlopeNearOneAboveFloor F x j)
    (hdesc : ∀ K β, stayingAbove f x K β → ∀ i ≤ K, x K β ≤ x i β + c) (K : ℕ) {P : ℝ}
    (hP : F + |c| + 1 ≤ P) :
    stayingAbove f x K (tunedPoint f x K P) ∧ x K (tunedPoint f x K P) = P ∧
      tunedPoint f x K P ∈ aboveFloor F x K := by
  have hu := exists_unique_of_increasing_family hx0 hfF hgood hdesc K hP
  have h := hu.1.exists
  have hs : stayingAbove f x K (tunedPoint f x K P) ∧ x K (tunedPoint f x K P) = P := by
    unfold tunedPoint
    rw [dif_pos h]
    exact h.choose_spec
  exact ⟨hs.1, hs.2, hu.2 _ hs.1 hs.2⟩

theorem strictMonoOn_tunedPoint {f F c : ℝ} {x : ℕ → ℝ → ℝ} (hx0 : x 0 = id) (hfF : f < F)
    (hgood : ∀ j, HasSlopeNearOneAboveFloor F x j)
    (hdesc : ∀ K β, stayingAbove f x K β → ∀ i ≤ K, x K β ≤ x i β + c) (K : ℕ) :
    StrictMonoOn (tunedPoint f x K) (Ici (F + |c| + 1)) :=
  strictMonoOn_inverse_of_increasing_family hx0 hfF hgood hdesc K fun _ hP =>
    ⟨(tunedPoint_spec hx0 hfF hgood hdesc K hP).1, (tunedPoint_spec hx0 hfF hgood hdesc K hP).2.1⟩

theorem hasDerivAt_tunedPoint {f F c : ℝ} {x : ℕ → ℝ → ℝ} (hx0 : x 0 = id) (hfF : f < F)
    (hgood : ∀ j, HasSlopeNearOneAboveFloor F x j)
    (hdesc : ∀ K β, stayingAbove f x K β → ∀ i ≤ K, x K β ≤ x i β + c) (K : ℕ)
    {d : ℝ → ℝ} (hd : ∀ β ∈ aboveFloor F x K, HasDerivAt (x K) (d β) β)
    {P : ℝ} (hP : F + |c| + 1 < P) :
    HasDerivAt (tunedPoint f x K) (d (tunedPoint f x K P))⁻¹ P :=
  hasDerivAt_inverse_of_increasing_family hx0 hfF hgood hdesc K
    (fun _ hQ => ⟨(tunedPoint_spec hx0 hfF hgood hdesc K hQ).1,
      (tunedPoint_spec hx0 hfF hgood hdesc K hQ).2.1⟩) hd hP

end YangMills.ContinuumLimit

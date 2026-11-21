import YangMills.Construction.Dirichlet.CutoffDifferenceBoundsProof
import YangMills.Construction.RegionSequence.WeightedDistTriangleProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.WeightedLength
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
variable {d : ℕ} {S : ℝ}
theorem torusProj_add (v w : Fin d → ℝ) : torusProj d S (v + w) = torusProj d S v + torusProj d S w := by apply _root_.YangMills.Construction.Dirichlet.Commutator.torusProj_add <;> assumption
theorem torusProj_sub (v w : Fin d → ℝ) : torusProj d S (v - w) = torusProj d S v - torusProj d S w := by apply _root_.YangMills.Construction.Dirichlet.CutoffDifferences.torusProj_sub <;> assumption
theorem torusProj_neg (v : Fin d → ℝ) : torusProj d S (-v) = -torusProj d S v := by apply _root_.YangMills.Construction.Dirichlet.Commutator.torusProj_neg <;> assumption
theorem torusProj_surjective : Function.Surjective (torusProj d S) := by apply _root_.YangMills.Construction.Dirichlet.CoverCountProof.torusProj_surjective <;> assumption
theorem continuous_torusSegment_pointAt (s : TorusSegment d) : Continuous (s.pointAt S) := by apply _root_.YangMills.Construction.LevelUnitFacts.pointAt_continuous <;> assumption
theorem pointAt_zero (s : TorusSegment d) : s.pointAt S 0 = torusProj d S s.start := by
  simp [TorusSegment.pointAt]
theorem pointAt_one (s : TorusSegment d) :
    s.pointAt S 1 = torusProj d S (s.start + s.direction) := by
  simp [TorusSegment.pointAt]
theorem segmentUnion_singleton (s : TorusSegment d) :
    segmentUnion S [s] = s.pointAt S '' Icc 0 1 := by apply _root_.YangMills.Construction.RegionSequence.WeightedDist.segmentUnion_singleton <;> assumption
theorem segmentUnion_append (Γ Γ' : List (TorusSegment d)) :
    segmentUnion S (Γ ++ Γ') = segmentUnion S Γ ∪ segmentUnion S Γ' := by apply _root_.YangMills.Construction.LevelUnitFacts.segmentUnion_append <;> assumption
theorem isConnected_segmentUnion_singleton (s : TorusSegment d) :
    IsConnected (segmentUnion S [s]) := by
  rw [segmentUnion_singleton]
  exact (isConnected_Icc zero_le_one).image _ (continuous_torusSegment_pointAt s).continuousOn
theorem pointAt_mem_segmentUnion_singleton (s : TorusSegment d) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    s.pointAt S τ ∈ segmentUnion S [s] := by
  rw [segmentUnion_singleton]
  exact ⟨τ, hτ, rfl⟩
theorem lengthWithin_singleton (s : TorusSegment d) (X : Set (PeriodicTorus d S)) :
    lengthWithin [s] X =
      s.lOneLength * (volume {τ ∈ Icc (0 : ℝ) 1 | s.pointAt S τ ∈ X}).toReal := by
  simp [lengthWithin]
theorem torusSegment_lOneLength_nonneg (s : TorusSegment d) : 0 ≤ s.lOneLength :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem lengthWithin_nonneg (Γ : List (TorusSegment d)) (X : Set (PeriodicTorus d S)) :
    0 ≤ lengthWithin Γ X := by apply _root_.YangMills.Construction.Dirichlet.Crossing.lengthWithin_nonneg <;> assumption
theorem chainWeightedLength_append (L : ℕ) (ξ : ℝ) (t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S))
    (Γ Γ' : List (TorusSegment d)) :
    chainWeightedLength L ξ t Ω (Γ ++ Γ') =
      chainWeightedLength L ξ t Ω Γ + chainWeightedLength L ξ t Ω Γ' := by apply _root_.YangMills.Construction.LevelUnitFacts.chainWeightedLength_append <;> assumption
theorem scaleSpacing_pos {L : ℕ} (hL : 1 ≤ L) {ξ : ℝ} (hξ : 0 < ξ) (n : ℤ) :
    0 < scaleSpacing L ξ n := by
  unfold scaleSpacing
  positivity
theorem scaleSpacing_mono {L : ℕ} (hL : 1 ≤ L) {ξ : ℝ} (hξ : 0 < ξ) {k m : ℤ} (h : k ≤ m) :
    scaleSpacing L ξ k ≤ scaleSpacing L ξ m := by
  unfold scaleSpacing
  exact mul_le_mul_of_nonneg_right
    (zpow_le_zpow_right₀ (by exact_mod_cast hL) h) hξ.le
theorem chainWeightedLength_nonneg {L : ℕ} (hL : 1 ≤ L) {ξ : ℝ} (hξ : 0 < ξ) (t : ℕ)
    (Ω : ℕ → Set (PeriodicTorus d S)) (Γ : List (TorusSegment d)) :
    0 ≤ chainWeightedLength L ξ t Ω Γ := by
  refine add_nonneg (Finset.sum_nonneg fun n _ => ?_) ?_
  · exact mul_nonneg (inv_nonneg.mpr (scaleSpacing_pos hL hξ _).le) (lengthWithin_nonneg _ _)
  · exact mul_nonneg (inv_nonneg.mpr (scaleSpacing_pos hL hξ _).le) (lengthWithin_nonneg _ _)
def admissibleLengths (L : ℕ) (ξ : ℝ) (t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S))
    (p q : PeriodicTorus d S) : Set ℝ :=
  {r | ∃ Γ : List (TorusSegment d), IsConnected (segmentUnion S Γ) ∧ p ∈ segmentUnion S Γ ∧
    q ∈ segmentUnion S Γ ∧ r = chainWeightedLength L ξ t Ω Γ}
theorem admissibleLengths_nonempty (L : ℕ) (ξ : ℝ) (t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S))
    (p q : PeriodicTorus d S) : (admissibleLengths L ξ t Ω p q).Nonempty := by
  obtain ⟨v, rfl⟩ := torusProj_surjective (d := d) (S := S) p
  obtain ⟨w, rfl⟩ := torusProj_surjective (d := d) (S := S) q
  let s : TorusSegment d := ⟨v, w - v⟩
  refine ⟨_, [s], isConnected_segmentUnion_singleton s, ?_, ?_, rfl⟩
  · have h := pointAt_mem_segmentUnion_singleton (S := S) s (τ := 0) (by simp)
    rwa [pointAt_zero] at h
  · have h := pointAt_mem_segmentUnion_singleton (S := S) s (τ := 1) (by simp)
    rw [pointAt_one] at h
    simpa [s] using h
theorem admissibleLengths_bddBelow {L : ℕ} (hL : 1 ≤ L) {ξ : ℝ} (hξ : 0 < ξ) (t : ℕ)
    (Ω : ℕ → Set (PeriodicTorus d S)) (p q : PeriodicTorus d S) :
    BddBelow (admissibleLengths L ξ t Ω p q) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨Γ, -, -, -, rfl⟩
  exact chainWeightedLength_nonneg hL hξ t Ω Γ
theorem chainWeightedDist_triangle {L : ℕ} (hL : 1 ≤ L) {ξ : ℝ} (hξ : 0 < ξ) (t : ℕ)
    (Ω : ℕ → Set (PeriodicTorus d S)) (p q q' : PeriodicTorus d S) :
    chainWeightedDist L ξ t Ω p q' ≤
      chainWeightedDist L ξ t Ω p q + chainWeightedDist L ξ t Ω q q' := by
  have hsum : ∀ a ∈ admissibleLengths L ξ t Ω p q, ∀ b ∈ admissibleLengths L ξ t Ω q q',
      chainWeightedDist L ξ t Ω p q' ≤ a + b := by
    rintro _ ⟨Γ, hΓ, hp, hq, rfl⟩ _ ⟨Γ', hΓ', hq', hq'', rfl⟩
    rw [← chainWeightedLength_append]
    refine csInf_le (admissibleLengths_bddBelow hL hξ t Ω p q') ⟨Γ ++ Γ', ?_, ?_, ?_, rfl⟩
    · rw [segmentUnion_append]
      exact ⟨hΓ.nonempty.mono subset_union_left,
        hΓ.isPreconnected.union q hq hq' hΓ'.isPreconnected⟩
    · rw [segmentUnion_append]
      exact Or.inl hp
    · rw [segmentUnion_append]
      exact Or.inr hq''
  have h₁ : ∀ b ∈ admissibleLengths L ξ t Ω q q',
      chainWeightedDist L ξ t Ω p q' - b ≤ chainWeightedDist L ξ t Ω p q := fun b hb =>
    le_csInf (admissibleLengths_nonempty L ξ t Ω p q) fun a ha => by linarith [hsum a ha b hb]
  have h₂ : chainWeightedDist L ξ t Ω p q' - chainWeightedDist L ξ t Ω p q ≤
      chainWeightedDist L ξ t Ω q q' :=
    le_csInf (admissibleLengths_nonempty L ξ t Ω q q') fun b hb => by linarith [h₁ b hb]
  linarith
theorem exists_mem_shell_of_mem (Ω : ℕ → Set (PeriodicTorus d S)) {z : PeriodicTorus d S} {m : ℕ}
    (h₁ : z ∈ Ω 1) (hm : z ∉ Ω (m + 1)) : ∃ k ∈ Finset.Icc 1 m, z ∈ shell Ω k := by
  classical
  have hex : ∃ j, z ∉ Ω (j + 1) := ⟨m, hm⟩
  obtain ⟨j, hj, hmin, hjm⟩ : ∃ j, z ∉ Ω (j + 1) ∧ (∀ i < j, ¬ z ∉ Ω (i + 1)) ∧ j ≤ m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi, Nat.find_min' hex hm⟩
  have hj₁ : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · exact absurd h₁ hj
    · exact h
  have hzj : z ∈ Ω j := by
    have h := hmin (j - 1) (by omega)
    rw [Nat.sub_add_cancel hj₁] at h
    exact not_not.mp h
  exact ⟨j, Finset.mem_Icc.mpr ⟨hj₁, hjm⟩, subset_closure ⟨hzj, hj⟩⟩
theorem volume_pointAt_preimage_finite (s : TorusSegment d) (hne : s.direction ≠ 0)
    {F : Set (PeriodicTorus d S)} (hF : F.Finite) : volume {τ : ℝ | s.pointAt S τ ∈ F} = 0 := by
  obtain ⟨μ, hμ⟩ := Function.ne_iff.mp hne
  have hμ' : s.direction μ ≠ 0 := hμ
  have hsub : {τ : ℝ | s.pointAt S τ ∈ F} ⊆ ⋃ f ∈ F, {τ : ℝ | s.pointAt S τ = f} := by
    intro τ hτ
    exact mem_biUnion hτ rfl
  refine Countable.measure_zero (Countable.mono hsub (hF.countable.biUnion fun f _ => ?_)) _
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective (f μ)
  refine (countable_range fun n : ℤ => (c - s.start μ + (n : ℝ) * S) / s.direction μ).mono ?_
  intro τ hτ
  have h₁ : ((s.start μ + τ * s.direction μ : ℝ) : AddCircle S) = (c : AddCircle S) := by
    have h := congrFun (show s.pointAt S τ = f from hτ) μ
    rw [show ((c : ℝ) : AddCircle S) = f μ from hc, ← h]
    simp [TorusSegment.pointAt, torusProj]
  have h₂ : ((s.start μ + τ * s.direction μ - c : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_sub, h₁, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff S).mp h₂
  rw [zsmul_eq_mul] at hn
  refine ⟨n, ?_⟩
  show (c - s.start μ + (n : ℝ) * S) / s.direction μ = τ
  rw [div_eq_iff hμ']
  linarith
theorem inv_scaleSpacing_mul_le_segment {L : ℕ} (hL : 1 ≤ L) {ξ : ℝ} (hξ : 0 < ξ) {t m : ℕ}
    (hm : m ≤ t) (Ω : ℕ → Set (PeriodicTorus d S)) (s : TorusSegment d)
    {F : Set (PeriodicTorus d S)} (hF : F.Finite)
    (hs : ∀ τ ∈ Icc (0 : ℝ) 1, s.pointAt S τ ∈ Ω (m + 1) → s.pointAt S τ ∈ F) :
    (scaleSpacing L ξ m)⁻¹ * s.lOneLength ≤ chainWeightedLength L ξ t Ω [s] := by
  by_cases h0 : s.direction = 0
  · have hl : s.lOneLength = 0 := by simp [TorusSegment.lOneLength, h0]
    rw [hl, mul_zero]
    exact chainWeightedLength_nonneg hL hξ t Ω [s]
  set A : ℕ → Set ℝ := fun k => {τ ∈ Icc (0 : ℝ) 1 | s.pointAt S τ ∈ shell Ω k} with hA
  set B : Set ℝ := {τ ∈ Icc (0 : ℝ) 1 | s.pointAt S τ ∈ (Ω 1)ᶜ} with hB
  set N : Set ℝ := {τ : ℝ | s.pointAt S τ ∈ F} with hN
  have hNnull : volume N = 0 := volume_pointAt_preimage_finite s h0 hF
  have hcover : Icc (0 : ℝ) 1 ⊆ N ∪ B ∪ ⋃ k ∈ Finset.Icc 1 m, A k := by
    intro τ hτ
    by_cases hz : s.pointAt S τ ∈ Ω (m + 1)
    · exact Or.inl (Or.inl (hs τ hτ hz))
    by_cases h1 : s.pointAt S τ ∈ Ω 1
    · obtain ⟨k, hk, hkl⟩ := exists_mem_shell_of_mem Ω h1 hz
      exact Or.inr (mem_biUnion hk ⟨hτ, hkl⟩)
    · exact Or.inl (Or.inr ⟨hτ, h1⟩)
  have hfin : ∀ X : Set ℝ, X ⊆ Icc (0 : ℝ) 1 → volume X ≠ ⊤ := fun X hX =>
    ne_top_of_le_ne_top (by simp) (measure_mono hX)
  have hmeas : (1 : ENNReal) ≤ volume B + ∑ k ∈ Finset.Icc 1 m, volume (A k) := by
    calc (1 : ENNReal) = volume (Icc (0 : ℝ) 1) := by simp
      _ ≤ volume (N ∪ B ∪ ⋃ k ∈ Finset.Icc 1 m, A k) := measure_mono hcover
      _ ≤ volume (N ∪ B) + volume (⋃ k ∈ Finset.Icc 1 m, A k) := measure_union_le _ _
      _ ≤ (volume N + volume B) + ∑ k ∈ Finset.Icc 1 m, volume (A k) :=
        add_le_add (measure_union_le _ _) (measure_biUnion_finset_le _ _)
      _ = volume B + ∑ k ∈ Finset.Icc 1 m, volume (A k) := by rw [hNnull, zero_add]
  have hAfin : ∀ k, volume (A k) ≠ ⊤ := fun k => hfin _ fun τ hτ => hτ.1
  have hBfin : volume B ≠ ⊤ := hfin _ fun τ hτ => hτ.1
  have hreal : 1 ≤ (volume B).toReal + ∑ k ∈ Finset.Icc 1 m, (volume (A k)).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hBfin, ENNReal.sum_ne_top.mpr fun k _ => hAfin k⟩) hmeas
    rwa [ENNReal.toReal_add hBfin (ENNReal.sum_ne_top.mpr fun k _ => hAfin k),
      ENNReal.toReal_sum fun k _ => hAfin k, ENNReal.toReal_one] at h
  set ℓ : ℝ := s.lOneLength with hℓ
  have hℓ0 : 0 ≤ ℓ := torusSegment_lOneLength_nonneg s
  have hinv : ∀ k : ℕ, k ≤ m → (scaleSpacing L ξ m)⁻¹ ≤ (scaleSpacing L ξ k)⁻¹ := fun k hk =>
    inv_anti₀ (scaleSpacing_pos hL hξ _) (scaleSpacing_mono hL hξ (by exact_mod_cast hk))
  have hpos : 0 ≤ (scaleSpacing L ξ m)⁻¹ := inv_nonneg.mpr (scaleSpacing_pos hL hξ _).le
  have hform : chainWeightedLength L ξ t Ω [s] =
      ∑ n ∈ Finset.Icc 1 t, (scaleSpacing L ξ n)⁻¹ * (ℓ * (volume (A n)).toReal) +
        (scaleSpacing L ξ 0)⁻¹ * (ℓ * (volume B).toReal) := by
    simp only [chainWeightedLength, lengthWithin_singleton]
    rfl
  have hsum : ∑ k ∈ Finset.Icc 1 m, (scaleSpacing L ξ m)⁻¹ * (ℓ * (volume (A k)).toReal) ≤
      ∑ n ∈ Finset.Icc 1 t, (scaleSpacing L ξ n)⁻¹ * (ℓ * (volume (A n)).toReal) := by
    refine le_trans (Finset.sum_le_sum fun k hk => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right hm) fun k _ _ => ?_)
    · exact mul_le_mul_of_nonneg_right (hinv k (Finset.mem_Icc.mp hk).2)
        (mul_nonneg hℓ0 ENNReal.toReal_nonneg)
    · exact mul_nonneg (inv_nonneg.mpr (scaleSpacing_pos hL hξ _).le)
        (mul_nonneg hℓ0 ENNReal.toReal_nonneg)
  have hzero : (scaleSpacing L ξ m)⁻¹ * (ℓ * (volume B).toReal) ≤
      (scaleSpacing L ξ 0)⁻¹ * (ℓ * (volume B).toReal) :=
    mul_le_mul_of_nonneg_right (by simpa using hinv 0 (Nat.zero_le m))
      (mul_nonneg hℓ0 ENNReal.toReal_nonneg)
  have hone : (scaleSpacing L ξ m)⁻¹ * ℓ ≤ (scaleSpacing L ξ m)⁻¹ * ℓ *
      ((volume B).toReal + ∑ k ∈ Finset.Icc 1 m, (volume (A k)).toReal) :=
    le_mul_of_one_le_right (mul_nonneg hpos hℓ0) hreal
  have hexpand : (scaleSpacing L ξ m)⁻¹ * ℓ *
      ((volume B).toReal + ∑ k ∈ Finset.Icc 1 m, (volume (A k)).toReal) =
      (scaleSpacing L ξ m)⁻¹ * (ℓ * (volume B).toReal) +
        ∑ k ∈ Finset.Icc 1 m, (scaleSpacing L ξ m)⁻¹ * (ℓ * (volume (A k)).toReal) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring
  rw [hform]
  linarith
theorem isSegmentPath_of_isSegmentChain : ∀ (Γ : List (TorusSegment d)) (p q : PeriodicTorus d S),
    IsSegmentChain S p Γ q → IsSegmentPath S p q Γ
  | [], _, _, h => h.elim
  | [_], _, _, h => ⟨h.1, h.2⟩
  | _ :: s' :: Γ, _, _, h => ⟨h.1, isSegmentPath_of_isSegmentChain (s' :: Γ) _ _ h.2⟩
theorem inv_scaleSpacing_mul_le_chain {L : ℕ} (hL : 1 ≤ L) {ξ : ℝ} (hξ : 0 < ξ) {t m : ℕ}
    (hm : m ≤ t) (Ω : ℕ → Set (PeriodicTorus d S)) (Γ : List (TorusSegment d))
    (hΓ : (segmentUnion S Γ ∩ Ω (m + 1)).Finite) :
    (scaleSpacing L ξ m)⁻¹ * segmentPathLength Γ ≤ chainWeightedLength L ξ t Ω Γ := by
  induction Γ with
  | nil => simp [segmentPathLength, chainWeightedLength, lengthWithin]
  | cons s Γ ih =>
    have hcons : s :: Γ = [s] ++ Γ := rfl
    have hsub : segmentUnion S Γ ⊆ segmentUnion S (s :: Γ) := by
      rw [hcons, segmentUnion_append]
      exact subset_union_right
    have hfirst := inv_scaleSpacing_mul_le_segment hL hξ hm Ω s hΓ fun τ hτ hz =>
      ⟨⟨s, List.mem_cons_self, τ, hτ, rfl⟩, hz⟩
    have hrest := ih (hΓ.subset (inter_subset_inter_left _ hsub))
    have hlen : segmentPathLength (s :: Γ) = s.lOneLength + segmentPathLength Γ := by
      simp [segmentPathLength]
    rw [hlen, mul_add, hcons, chainWeightedLength_append]
    linarith
theorem volume_inter_le_ite {A I : Set ℝ} (a : Prop) [Decidable a] {c : ℝ}
    (hI : volume I = ENNReal.ofReal c) (h : ∀ τ ∈ I, τ ∈ A → a) :
    volume (A ∩ I) ≤ ENNReal.ofReal (if a then c else 0) := by
  split_ifs with ha
  · exact (measure_mono inter_subset_right).trans hI.le
  · have he : A ∩ I = ∅ := by
      ext τ
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
      exact fun hτ => ha (h τ hτ.2 hτ.1)
    simp [he]
theorem volume_toReal_le_halves {A : Set ℝ} (hA : A ⊆ Icc 0 1) (a b : Prop) [Decidable a]
    [Decidable b] (h₁ : ∀ τ ∈ Ioo (0 : ℝ) (1 / 2), τ ∈ A → a)
    (h₂ : ∀ τ ∈ Ioo (1 / 2 : ℝ) 1, τ ∈ A → b) :
    (volume A).toReal ≤ (if a then (1 / 2 : ℝ) else 0) + (if b then (1 / 2 : ℝ) else 0) := by
  have hsub : A ⊆ ({0, 1 / 2, 1} : Set ℝ) ∪ (A ∩ Ioo 0 (1 / 2)) ∪ (A ∩ Ioo (1 / 2) 1) := by
    intro τ hτ
    obtain ⟨h0, h1⟩ := hA hτ
    rcases h0.eq_or_lt with rfl | h0
    · exact Or.inl (Or.inl (by simp))
    rcases h1.eq_or_lt with rfl | h1
    · exact Or.inl (Or.inl (by simp))
    rcases lt_trichotomy τ (1 / 2) with h | rfl | h
    · exact Or.inl (Or.inr ⟨hτ, h0, h⟩)
    · exact Or.inl (Or.inl (by simp))
    · exact Or.inr ⟨hτ, h, h1⟩
  have hfinite : volume ({0, 1 / 2, 1} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) _
  have hx : (0 : ℝ) ≤ if a then (1 / 2 : ℝ) else 0 := by split_ifs <;> norm_num
  have hy : (0 : ℝ) ≤ if b then (1 / 2 : ℝ) else 0 := by split_ifs <;> norm_num
  have hv₁ : volume (Ioo (0 : ℝ) (1 / 2)) = ENNReal.ofReal (1 / 2) := by
    rw [Real.volume_Ioo]
    norm_num
  have hv₂ : volume (Ioo (1 / 2 : ℝ) 1) = ENNReal.ofReal (1 / 2) := by
    rw [Real.volume_Ioo]
    norm_num
  refine ENNReal.toReal_le_of_le_ofReal (add_nonneg hx hy) ?_
  rw [ENNReal.ofReal_add hx hy]
  calc volume A ≤ volume (({0, 1 / 2, 1} : Set ℝ) ∪ (A ∩ Ioo 0 (1 / 2)) ∪ (A ∩ Ioo (1 / 2) 1)) :=
        measure_mono hsub
    _ ≤ volume (({0, 1 / 2, 1} : Set ℝ) ∪ (A ∩ Ioo 0 (1 / 2))) + volume (A ∩ Ioo (1 / 2) 1) :=
        measure_union_le _ _
    _ ≤ (volume ({0, 1 / 2, 1} : Set ℝ) + volume (A ∩ Ioo 0 (1 / 2))) +
          volume (A ∩ Ioo (1 / 2) 1) := add_le_add_left (measure_union_le _ _) _
    _ ≤ ENNReal.ofReal (if a then (1 / 2 : ℝ) else 0) +
          ENNReal.ofReal (if b then (1 / 2 : ℝ) else 0) := by
        rw [hfinite, zero_add]
        exact add_le_add (volume_inter_le_ite a hv₁ h₁) (volume_inter_le_ite b hv₂ h₂)
theorem sum_inv_scaleSpacing_half (L : ℕ) (ξ : ℝ) {t n : ℕ} (hn : n ≤ t) :
    ∑ k ∈ Finset.Icc 1 t, (scaleSpacing L ξ k)⁻¹ * (if k = n then (1 / 2 : ℝ) else 0) +
        (scaleSpacing L ξ 0)⁻¹ * (if n = 0 then (1 / 2 : ℝ) else 0) =
      1 / 2 * (scaleSpacing L ξ n)⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · have hz : ∑ k ∈ Finset.Icc 1 t,
        (scaleSpacing L ξ k)⁻¹ * (if k = 0 then (1 / 2 : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero fun k hk => by
        have h1 := (Finset.mem_Icc.mp hk).1
        rw [if_neg (by omega), mul_zero]
    rw [hz, if_pos rfl, zero_add, Nat.cast_zero]
    ring
  · rw [if_neg (by omega), mul_zero, add_zero, Finset.sum_eq_single n]
    · rw [if_pos rfl]
      ring
    · intro k _ hk
      rw [if_neg hk, mul_zero]
    · intro h'
      exact absurd (Finset.mem_Icc.mpr ⟨h, hn⟩) h'
theorem chainWeightedLength_singleton_le_halves (L : ℕ) {ξ : ℝ} (hL : 1 ≤ L) (hξ : 0 < ξ)
    {t n n' : ℕ} (hn : n ≤ t) (hn' : n' ≤ t) (Ω : ℕ → Set (PeriodicTorus d S))
    (s : TorusSegment d)
    (h₁ : ∀ τ ∈ Ioo (0 : ℝ) (1 / 2),
      (∀ k ∈ Finset.Icc 1 t, s.pointAt S τ ∈ shell Ω k → k = n) ∧
        (s.pointAt S τ ∉ Ω 1 → n = 0))
    (h₂ : ∀ τ ∈ Ioo (1 / 2 : ℝ) 1,
      (∀ k ∈ Finset.Icc 1 t, s.pointAt S τ ∈ shell Ω k → k = n') ∧
        (s.pointAt S τ ∉ Ω 1 → n' = 0)) :
    chainWeightedLength L ξ t Ω [s] ≤
      1 / 2 * s.lOneLength * ((scaleSpacing L ξ n)⁻¹ + (scaleSpacing L ξ n')⁻¹) := by
  have hℓ : 0 ≤ s.lOneLength := torusSegment_lOneLength_nonneg s
  have hlayer : ∀ k ∈ Finset.Icc 1 t,
      (scaleSpacing L ξ k)⁻¹ * lengthWithin [s] (shell Ω k) ≤
        s.lOneLength * ((scaleSpacing L ξ k)⁻¹ * (if k = n then (1 / 2 : ℝ) else 0)) +
          s.lOneLength * ((scaleSpacing L ξ k)⁻¹ * (if k = n' then (1 / 2 : ℝ) else 0)) := by
    intro k hk
    have hv := volume_toReal_le_halves (A := {τ ∈ Icc (0 : ℝ) 1 | s.pointAt S τ ∈ shell Ω k})
      (fun τ hτ => hτ.1) (k = n) (k = n')
      (fun τ hτ hm => (h₁ τ hτ).1 k hk hm.2) (fun τ hτ hm => (h₂ τ hτ).1 k hk hm.2)
    rw [lengthWithin_singleton]
    have hw := (inv_pos.mpr (scaleSpacing_pos hL hξ (k : ℤ))).le
    calc (scaleSpacing L ξ k)⁻¹ * (s.lOneLength * _) ≤ (scaleSpacing L ξ k)⁻¹ * (s.lOneLength *
            ((if k = n then (1 / 2 : ℝ) else 0) + (if k = n' then (1 / 2 : ℝ) else 0))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hℓ) hw
      _ = _ := by ring
  have houtside : (scaleSpacing L ξ 0)⁻¹ * lengthWithin [s] (Ω 1)ᶜ ≤
      s.lOneLength * ((scaleSpacing L ξ 0)⁻¹ * (if n = 0 then (1 / 2 : ℝ) else 0)) +
        s.lOneLength * ((scaleSpacing L ξ 0)⁻¹ * (if n' = 0 then (1 / 2 : ℝ) else 0)) := by
    have hv := volume_toReal_le_halves (A := {τ ∈ Icc (0 : ℝ) 1 | s.pointAt S τ ∈ (Ω 1)ᶜ})
      (fun τ hτ => hτ.1) (n = 0) (n' = 0)
      (fun τ hτ hm => (h₁ τ hτ).2 hm.2) (fun τ hτ hm => (h₂ τ hτ).2 hm.2)
    rw [lengthWithin_singleton]
    have hw := (inv_pos.mpr (scaleSpacing_pos hL hξ (0 : ℤ))).le
    calc (scaleSpacing L ξ 0)⁻¹ * (s.lOneLength * _) ≤ (scaleSpacing L ξ 0)⁻¹ * (s.lOneLength *
            ((if n = 0 then (1 / 2 : ℝ) else 0) + (if n' = 0 then (1 / 2 : ℝ) else 0))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hℓ) hw
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hlayer
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have e₁ := sum_inv_scaleSpacing_half L ξ hn
  have e₂ := sum_inv_scaleSpacing_half L ξ hn'
  have hgoal : 1 / 2 * s.lOneLength * ((scaleSpacing L ξ n)⁻¹ + (scaleSpacing L ξ n')⁻¹) =
      s.lOneLength * (1 / 2 * (scaleSpacing L ξ n)⁻¹) +
        s.lOneLength * (1 / 2 * (scaleSpacing L ξ n')⁻¹) := by ring
  rw [hgoal, ← e₁, ← e₂]
  unfold chainWeightedLength
  linarith
theorem mem_interior_cubeAt {p c : PeriodicTorus d S} {σ : ℝ} (hσ : 0 < σ)
    (h : ∀ μ, ‖(p - c) μ‖ < σ / 2) : p ∈ interior (cubeAt c σ) := by
  have hopen : IsOpen {p : PeriodicTorus d S | ∀ μ, ‖(p - c) μ‖ < σ / 2} := by
    have he : {p : PeriodicTorus d S | ∀ μ, ‖(p - c) μ‖ < σ / 2} =
        ⋂ μ, {p : PeriodicTorus d S | ‖(p - c) μ‖ < σ / 2} := by
      ext p
      simp
    rw [he]
    exact isOpen_iInter_of_finite fun μ => isOpen_lt
      ((continuous_apply μ).comp (continuous_id.sub continuous_const)).norm continuous_const
  refine mem_interior.mpr ⟨_, ?_, hopen, h⟩
  intro q hq
  choose v hv hv' using fun μ => TorusMetric.exists_coe_eq_abs_eq_norm ((q - c) μ)
  have hcov : torusProj d S v = q - c := funext hv
  have hnorm : ‖v‖ ≤ σ / 2 := (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun μ => by
    rw [Real.norm_eq_abs, hv' μ]
    exact (hq μ).le
  have hle : supNorm (q - c) ≤ ‖v‖ := by
    refine csInf_le ⟨0, ?_⟩ ⟨v, hcov, rfl⟩
    rintro _ ⟨w, -, rfl⟩
    exact norm_nonneg _
  exact hle.trans hnorm
theorem torusProj_add_smul_single_mem_interior {ξ a u : ℝ} (hξ : 0 < ξ) (ha : |a| = ξ)
    (hu : |u| < 1 / 2) (v : Fin d → ℝ) (μ : Fin d) :
    torusProj d S (v + u • (Pi.single μ a : Fin d → ℝ)) ∈
      interior (cubeAt (torusProj d S v) ξ) := by
  refine mem_interior_cubeAt hξ fun ν => ?_
  rw [← torusProj_sub, add_sub_cancel_left]
  refine lt_of_le_of_lt (TorusMetric.addCircle_norm_coe_le_abs _) ?_
  have hw : |(Pi.single μ a : Fin d → ℝ) ν| ≤ ξ := by
    by_cases h : ν = μ
    · subst h
      simp [ha]
    · simp [Pi.single_eq_of_ne h, hξ.le]
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  have h₁ := mul_le_mul_of_nonneg_left hw (abs_nonneg u)
  have h₂ := mul_lt_mul_of_pos_right hu hξ
  linarith
theorem exists_neighbor_segment {ξ : ℝ} (hξ : 0 < ξ) {x x' : LatticeSite d S ξ}
    (h : IsNeighbor x x') :
    ∃ s : TorusSegment d, s.pointAt S 0 = x ∧ s.pointAt S 1 = x' ∧ s.lOneLength = ξ ∧
      (∀ τ ∈ Ioo (0 : ℝ) (1 / 2),
        s.pointAt S τ ∈ interior (cubeAt (x : PeriodicTorus d S) ξ)) ∧
      ∀ τ ∈ Ioo (1 / 2 : ℝ) 1, s.pointAt S τ ∈ interior (cubeAt (x' : PeriodicTorus d S) ξ) := by
  obtain ⟨v, hv⟩ := torusProj_surjective (d := d) (S := S) (x : PeriodicTorus d S)
  obtain ⟨μ, e⟩ := h
  obtain ⟨a, ha, hx'⟩ : ∃ a : ℝ, |a| = ξ ∧
      (x' : PeriodicTorus d S) = torusProj d S (v + Pi.single μ a) := by
    rcases e with rfl | rfl
    · refine ⟨ξ, abs_of_pos hξ, ?_⟩
      rw [torusProj_add, hv]
      rfl
    · refine ⟨-ξ, by rw [abs_neg, abs_of_pos hξ], ?_⟩
      rw [torusProj_add, hv, Pi.single_neg, torusProj_neg, ← sub_eq_add_neg]
      rfl
  refine ⟨⟨v, Pi.single μ a⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pointAt_zero]
    exact hv
  · rw [pointAt_one]
    exact hx'.symm
  · show ∑ ν, |(Pi.single μ a : Fin d → ℝ) ν| = ξ
    rw [Finset.sum_eq_single μ]
    · simp [ha]
    · intro ν _ hν
      simp [Pi.single_eq_of_ne hν]
    · intro h'
      exact absurd (Finset.mem_univ μ) h'
  · intro τ hτ
    rw [← hv]
    refine torusProj_add_smul_single_mem_interior hξ ha ?_ v μ
    rw [abs_of_pos hτ.1]
    exact hτ.2
  · intro τ hτ
    rw [hx']
    have hu : |τ - 1| < 1 / 2 := by
      rw [abs_lt]
      constructor <;> linarith [hτ.1, hτ.2]
    have hpoint : (⟨v, Pi.single μ a⟩ : TorusSegment d).pointAt S τ =
        torusProj d S ((v + Pi.single μ a) + (τ - 1) • (Pi.single μ a : Fin d → ℝ)) := by
      show torusProj d S (v + τ • (Pi.single μ a : Fin d → ℝ)) = _
      congr 1
      rw [sub_smul, one_smul]
      abel
    rw [hpoint]
    exact torusProj_add_smul_single_mem_interior hξ ha hu _ μ
theorem separatedChain_subset_of_le {L : ℕ} {ξ : ℝ} {M R₁ t : ℕ}
    {Ω : ℕ → Set (PeriodicTorus d S)} (h : IsSeparatedChain L ξ M R₁ t Ω) {j k : ℕ}
    (hjk : j ≤ k) (hk : k ≤ t) : Ω k ⊆ Ω j := by
  induction k, hjk using Nat.le_induction with
  | base => exact subset_rfl
  | succ k _ ih => exact (h.succ_subset k (by omega)).trans (ih (by omega))
variable {L : ℕ} {aMinus aPlus : ℝ}
theorem exists_scale_of_site (𝒮 : BlockSetting d L aMinus aPlus S)
    (hmem : ChainMemberFacts L 𝒮.ξ 𝒮.M 𝒮.t 𝒮.Ω)
    (hblock : ∀ n ≤ lastNonemptyIndex 𝒮.Ω, ShellCubeFacts L 𝒮.ξ 𝒮.M 𝒮.t 𝒮.Ω n)
    (hsite : SiteLocationFacts L 𝒮.ξ 𝒮.t 𝒮.Ω)
    (x : LatticeSite d S 𝒮.ξ) :
    ∃ n ≤ 𝒮.t, 𝒮.localScale x = scaleSpacing L 𝒮.ξ n ∧
      ∀ z ∈ interior (cubeAt (x : PeriodicTorus d S) 𝒮.ξ),
        (∀ k ∈ Finset.Icc 1 𝒮.t, z ∈ shell 𝒮.Ω k → k = n) ∧ (z ∉ 𝒮.Ω 1 → n = 0) := by
  classical
  by_cases hx : (x : PeriodicTorus d S) ∈ 𝒮.Ω 0
  · obtain ⟨y, hy, -, huniq, hsub, -⟩ := hsite.exists_of_mem x x.2 hx
    have hxy : (x : PeriodicTorus d S) ∈ siteCube L 𝒮.ξ 𝒮.Ω y := hsub (by
      show supNorm ((x : PeriodicTorus d S) - (x : PeriodicTorus d S)) ≤ 𝒮.ξ / 2
      have h0 : supNorm (0 : PeriodicTorus d S) ≤ 0 := by
        refine csInf_le ⟨0, ?_⟩ ⟨0, ?_, by simp⟩
        · rintro _ ⟨w, -, rfl⟩
          exact norm_nonneg _
        · funext μ
          simp [torusProj]
      rw [sub_self]
      linarith [𝒮.isSeparatedChain.scale_pos])
    have hcentre : 𝒮.centreOf x = y := by
      have hspec : 𝒮.centreOf x ∈ 𝒮.centres ∧ (x : PeriodicTorus d S) ∈ 𝒮.cell (𝒮.centreOf x) :=
        Classical.epsilon_spec (p := fun y => y ∈ 𝒮.centres ∧ (x : PeriodicTorus d S) ∈ 𝒮.cell y)
          ⟨y, hy, hxy⟩
      by_contra hne
      exact huniq _ hspec.1 hne hspec.2
    obtain ⟨n₀, hn₀, hy₀⟩ := hy
    have hne : {n | y ∈ shellSites L 𝒮.ξ 𝒮.Ω n}.Nonempty := ⟨n₀, hy₀⟩
    have hyn : y ∈ shellSites L 𝒮.ξ 𝒮.Ω (shellIndex L 𝒮.ξ 𝒮.Ω y) := Nat.sInf_mem hne
    have hle : shellIndex L 𝒮.ξ 𝒮.Ω y ≤ n₀ := Nat.sInf_le hy₀
    refine ⟨shellIndex L 𝒮.ξ 𝒮.Ω y, hle.trans hn₀, ?_, ?_⟩
    · unfold BlockSetting.localScale
      rw [if_pos hx, BlockSetting.centreSpacing, hcentre]
      rfl
    intro z hz
    set n := shellIndex L 𝒮.ξ 𝒮.Ω y with hn
    have htop : n ≤ lastNonemptyIndex 𝒮.Ω := hyn.1
    have hint : z ∈ interior (siteCube L 𝒮.ξ 𝒮.Ω y) := interior_mono hsub hz
    refine ⟨fun k hk hzk => ?_, fun hz1 => ?_⟩
    · by_contra hkn
      exact disjoint_left.mp ((hblock n htop).disjoint_shell y hyn k
        (Finset.mem_Icc.mp hk).2 hkn) hint hzk
    · by_contra hn0
      have hzn : z ∈ shell 𝒮.Ω n := by
        rw [(hblock n htop).shell_eq_iUnion]
        exact mem_biUnion hyn (interior_subset hint)
      exact hz1 (separatedChain_subset_of_le 𝒮.isSeparatedChain (by omega) (hle.trans hn₀)
        (hmem.shell_subset n htop hzn).1)
  · refine ⟨0, Nat.zero_le _, ?_, fun z hz => ⟨fun k hk hzk => ?_, fun _ => rfl⟩⟩
    · unfold BlockSetting.localScale
      rw [if_neg hx]
      simp [scaleSpacing]
    · exfalso
      have hk' := Finset.mem_Icc.mp hk
      have hdis := hsite.disjoint_of_not_mem x x.2 hx
      by_cases htop : k ≤ lastNonemptyIndex 𝒮.Ω
      · exact disjoint_left.mp hdis hz
          (separatedChain_subset_of_le 𝒮.isSeparatedChain (Nat.zero_le k) hk'.2
            (hmem.shell_subset k htop hzk).1)
      · have he := hmem.shell_eq_empty k (by omega) hk'.2
        rw [he] at hzk
        exact hzk
theorem bounds_of_facts (hL : 1 ≤ L) (𝒮 : BlockSetting d L aMinus aPlus S)
    (hcov : ProjectionFacts d S)
    (hmem : ChainMemberFacts L 𝒮.ξ 𝒮.M 𝒮.t 𝒮.Ω)
    (hblock : ∀ n ≤ lastNonemptyIndex 𝒮.Ω, ShellCubeFacts L 𝒮.ξ 𝒮.M 𝒮.t 𝒮.Ω n)
    (hsite : SiteLocationFacts L 𝒮.ξ 𝒮.t 𝒮.Ω) : Bounds 𝒮 := by
  have hξ : 0 < 𝒮.ξ := 𝒮.isSeparatedChain.scale_pos
  refine ⟨fun p q q' => chainWeightedDist_triangle hL hξ 𝒮.t 𝒮.Ω p q q', ?_, ?_⟩
  · intro m hm σ p q hσ hfin
    have hpath := hcov.lOneNorm_le_length p q σ (isSegmentPath_of_isSegmentChain σ p q hσ)
    have hinv : 0 ≤ (𝒮.scaleAt m)⁻¹ := inv_nonneg.mpr (scaleSpacing_pos hL hξ _).le
    exact (mul_le_mul_of_nonneg_left hpath hinv).trans
      (inv_scaleSpacing_mul_le_chain hL hξ hm 𝒮.Ω σ hfin)
  · intro x x' hadj
    obtain ⟨n, hn, hρ, hplace⟩ := exists_scale_of_site 𝒮 hmem hblock hsite x
    obtain ⟨n', hn', hρ', hplace'⟩ := exists_scale_of_site 𝒮 hmem hblock hsite x'
    obtain ⟨s, h0, h1, hlen, hfirst, hsecond⟩ := exists_neighbor_segment hξ hadj
    have hξn : 𝒮.ξ ≤ scaleSpacing L 𝒮.ξ n := by
      have h := scaleSpacing_mono hL hξ (Int.natCast_nonneg n)
      simpa [scaleSpacing] using h
    have hξn' : 𝒮.ξ ≤ scaleSpacing L 𝒮.ξ n' := by
      have h := scaleSpacing_mono hL hξ (Int.natCast_nonneg n')
      simpa [scaleSpacing] using h
    have hbond := chainWeightedLength_singleton_le_halves L hL hξ hn hn' 𝒮.Ω s
      (fun τ hτ => hplace _ (hfirst τ hτ)) (fun τ hτ => hplace' _ (hsecond τ hτ))
    have hdist : 𝒮.blockDist (x : PeriodicTorus d S) (x' : PeriodicTorus d S) ≤
        chainWeightedLength L 𝒮.ξ 𝒮.t 𝒮.Ω [s] := by
      refine csInf_le (admissibleLengths_bddBelow hL hξ 𝒮.t 𝒮.Ω _ _)
        ⟨[s], isConnected_segmentUnion_singleton s, ?_, ?_, rfl⟩
      · rw [← h0]
        exact pointAt_mem_segmentUnion_singleton s (by simp)
      · rw [← h1]
        exact pointAt_mem_segmentUnion_singleton s (by simp)
    rw [hρ, hρ']
    rw [hlen] at hbond
    set a := scaleSpacing L 𝒮.ξ n with ha
    set b := scaleSpacing L 𝒮.ξ n' with hb
    have ha0 : 0 < a := lt_of_lt_of_le hξ hξn
    have hb0 : 0 < b := lt_of_lt_of_le hξ hξn'
    have hmin0 : 0 < min a b := lt_min ha0 hb0
    have hinva : a⁻¹ ≤ (min a b)⁻¹ := inv_anti₀ hmin0 (min_le_left a b)
    have hinvb : b⁻¹ ≤ (min a b)⁻¹ := inv_anti₀ hmin0 (min_le_right a b)
    refine ⟨hdist.trans hbond, ?_, ?_⟩
    · have e : 𝒮.ξ / min a b = 𝒮.ξ * (min a b)⁻¹ := div_eq_mul_inv _ _
      have h := mul_le_mul_of_nonneg_left (add_le_add hinva hinvb) hξ.le
      rw [e]
      linarith
    · rw [div_le_one hmin0]
      exact le_min hξn hξn'
theorem holdsForAll_of_partitionsHold (h : PartitionsHold) : HoldsForAll := by
  intro d L aMinus aPlus hletters S 𝒮
  have hL : 1 ≤ L := by
    have := hletters.three_le_blockFactor
    omega
  obtain ⟨hcov, -, hseq⟩ := h d L aMinus aPlus hletters 𝒮.ξ S 𝒮.isSeparatedChain.scale_pos
    𝒮.isSeparatedChain.period_pos
  obtain ⟨-, hmem, hblock, hsite, -, -⟩ := hseq 𝒮.M 𝒮.R₁ 𝒮.t 𝒮.Ω 𝒮.isSeparatedChain
  exact bounds_of_facts hL 𝒮 hcov hmem hblock hsite
end YangMills.Construction.WeightedLength

import YangMills.Construction.LawInAState.WilsonSharesAreACurvatureFamilyProof
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.SummableBoundsOfTheFlow.SquaresOfLocalFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps
namespace LocalFunctionals
variable {N m : ℕ}
private theorem siteOfInt_eq_iff_dvd (z z' : Fin 4 → ℤ) :
    (siteOfInt z : TorusSite m) = siteOfInt z' ↔ ∀ i, (m : ℤ) ∣ z' i - z i := by
  constructor
  · intro h i
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (congrFun h i)
  · intro h
    funext i
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (h i)
private theorem siteOfInt_add_eq (z z' : Fin 4 → ℤ) :
    (siteOfInt (z + z') : TorusSite m) = siteOfInt z + siteOfInt z' := by apply _root_.YangMills.Construction.BlockOffsets.siteOfInt_add <;> assumption
private theorem bondFrom_add_siteOfInt_eq_iff (x : TorusSite m) (w : Fin 4 → ℤ) (u e : LatticeBond) :
    bondFrom (x + siteOfInt w) u = bondFrom x e ↔ u.2 = e.2 ∧ ∀ i, (m : ℤ) ∣ e.1 i - (w i + u.1 i) := by
  unfold bondFrom
  rw [Prod.mk.injEq, add_assoc, add_right_inj, ← siteOfInt_add_eq, siteOfInt_eq_iff_dvd]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩
private def offsetBox (R : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R
private theorem mem_offsetBox {R : ℕ} {v : Fin 4 → ℤ} : v ∈ offsetBox R ↔ ∀ i, |v i| ≤ (R : ℤ) := by
  simp [offsetBox, Fintype.mem_piFinset, abs_le]
private def bondOffsetBox (R : ℕ) : Finset LatticeBond := offsetBox R ×ˢ Finset.univ
private theorem mem_bondOffsetBox {R : ℕ} {e : LatticeBond} (h : BondOffsetInBox R e) : e ∈ bondOffsetBox R := by
  simp only [bondOffsetBox, Finset.mem_product, Finset.mem_univ, and_true]
  exact mem_offsetBox.2 h.1
private def offsetRadius (e : LatticeBond) : ℕ := Finset.univ.sup fun i => (e.1 i).natAbs
private theorem abs_le_offsetRadius (e : LatticeBond) (i : Fin 4) : |e.1 i| ≤ (offsetRadius e : ℤ) := by
  have h : (e.1 i).natAbs ≤ offsetRadius e :=
    Finset.le_sup (f := fun i => (e.1 i).natAbs) (Finset.mem_univ i)
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h
private theorem offsetRadius_le {r : ℕ} {e : LatticeBond} (h : BondOffsetInBox r e) : offsetRadius e ≤ r := by apply _root_.YangMills.DeltaSharedProofs.p502589 <;> assumption
private def coarseShift (S : ℕ) (e : LatticeBond) (v : Fin 4 → ℤ) : LatticeBond :=
  (fun i => e.1 i - (S : ℤ) * v i, e.2)
open Classical in
private def offsetIndicator (h : LatticeBond) : LatticeBond → ℝ := fun u => if u = h then 1 else 0
private theorem bondIndicator_shift {S r ρ R : ℕ} (hbig : 2 * (r + ρ + 2 * S + 2) ≤ m)
    (hR : S * R ≤ r + ρ + S) (x : TorusSite m) (v : Fin 4 → ℤ) (hv : ∀ i, |v i| ≤ (R : ℤ))
    (e u : LatticeBond) (he : BondOffsetInBox r e) (hu : BondOffsetInBox ρ u) :
    bondIndicator (bondFrom x e) (bondFrom (x + siteOfInt fun i => (S : ℤ) * v i) u) =
      offsetIndicator (coarseShift S e v) u := by
  classical
  have hiff : bondFrom (x + siteOfInt fun i => (S : ℤ) * v i) u = bondFrom x e ↔ u = coarseShift S e v := by
    rw [bondFrom_add_siteOfInt_eq_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine Prod.ext ?_ h1
      funext i
      have hz : e.1 i - ((S : ℤ) * v i + u.1 i) = 0 := by
        refine Int.eq_zero_of_abs_lt_dvd (h2 i) ?_
        have a1 := he.1 i
        have a2 := hu.1 i
        have a3 := hv i
        have a4 : |(S : ℤ) * v i| ≤ (S : ℤ) * R := by
          rw [abs_mul, Nat.abs_cast]
          exact mul_le_mul_of_nonneg_left a3 (by positivity)
        have a5 : (S : ℤ) * R ≤ r + ρ + S := by exact_mod_cast hR
        have a6 : (2 : ℤ) * (r + ρ + 2 * S + 2) ≤ m := by exact_mod_cast hbig
        rw [abs_le] at a1 a2 a4
        rw [abs_lt]
        constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2, a4.1, a4.2]
      simp only [coarseShift]
      linarith
    · intro h
      subst h
      refine ⟨rfl, fun i => ?_⟩
      have : e.1 i - ((S : ℤ) * v i + (coarseShift S e v).1 i) = 0 := by
        simp only [coarseShift]
        ring
      rw [this]
      exact dvd_zero _
  unfold bondIndicator offsetIndicator
  by_cases h : u = coarseShift S e v
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
private theorem localFunctional_eq_zero {ρ : ℕ} {Λ : (LatticeBond → ℝ) → ℝ} (h : IsLocalFunctional ρ Λ)
    (f : LatticeBond → ℝ) (hf : ∀ u, BondOffsetInBox ρ u → f u = 0) : Λ f = 0 := by
  rw [h.congr f 0 hf, h.zero]
private theorem exists_offset_of_ne_zero {ρ : ℕ} {Λ : (LatticeBond → ℝ) → ℝ} (h : IsLocalFunctional ρ Λ)
    {f : LatticeBond → ℝ} (hf : Λ f ≠ 0) : ∃ u, BondOffsetInBox ρ u ∧ f u ≠ 0 := by
  by_contra hn
  push Not at hn
  exact hf (localFunctional_eq_zero h f hn)
private theorem bondFrom_eq_of_bondIndicator_ne_zero {x : TorusSite m} {b : TorusBond m} {u : LatticeBond}
    (h : bondIndicator b (bondFrom x u) ≠ 0) : bondFrom x u = b := by
  classical
  by_contra hn
  exact h (by simp [bondIndicator, hn])
private theorem supDist_le_of_bondFrom_eq [NeZero m] {x : TorusSite m} {b : TorusBond m} {u : LatticeBond}
    {ρ : ℕ} (hu : BondOffsetInBox ρ u) (h : bondFrom x u = b) : supDist x b.1 ≤ ρ := by
  subst h
  refine supDist_add_siteOfInt_le x u.1 ρ fun i => ?_
  have := hu.1 i
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this
private theorem sum_eq_sum_offsetBox [NeZero N] {R : ℕ} (hR : 2 * R < N) (y : TorusSite N) (f : TorusSite N → ℝ)
    (hf : ∀ v : Fin 4 → ℤ, (∀ i, 2 * |v i| ≤ (N : ℤ)) → (¬ ∀ i, |v i| ≤ (R : ℤ)) → f (y + siteOfInt v) = 0) :
    ∑ x, f x = ∑ v ∈ offsetBox R, f (y + siteOfInt v) := by
  classical
  have hinj : Set.InjOn (fun v : Fin 4 → ℤ => y + (siteOfInt v : TorusSite N)) (offsetBox R : Set (Fin 4 → ℤ)) := by
    intro v hv v' hv' h
    have h1 : (siteOfInt v : TorusSite N) = siteOfInt v' := add_left_cancel h
    have h2 := (siteOfInt_eq_iff_dvd v v').1 h1
    funext i
    have a1 := mem_offsetBox.1 (Finset.mem_coe.1 hv) i
    have a2 := mem_offsetBox.1 (Finset.mem_coe.1 hv') i
    have hz : v' i - v i = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd (h2 i) ?_
      have hN : (2 : ℤ) * R < N := by exact_mod_cast hR
      rw [abs_le] at a1 a2
      rw [abs_lt]
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
    linarith
  rw [← Finset.sum_image (f := f) hinj]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_
  have hoff : x = y + siteOfInt fun i => ((x - y) i).valMinAbs := by
    funext i
    simp [siteOfInt]
  rw [hoff]
  refine hf _ (fun i => ?_) fun hin => hx ?_
  · have := ZMod.natAbs_valMinAbs_le ((x - y) i)
    rw [Int.abs_eq_natAbs]
    have h2 : 2 * ((x - y) i).valMinAbs.natAbs ≤ N := by omega
    exact_mod_cast h2
  · refine Finset.mem_image.2 ⟨_, mem_offsetBox.2 hin, hoff.symm⟩
theorem gramEntriesTranslationInvariant : GramEntriesTranslationInvariant := by
  classical
  intro κ _ ρ S Λ hS hΛ
  set Rr : LatticeBond → LatticeBond → ℕ :=
    fun e e' => (max (offsetRadius e) (offsetRadius e') + ρ) / S + 1 with hRr
  set Γ : LatticeBond → LatticeBond → ℝ := fun e e' =>
    ∑ v ∈ offsetBox (Rr e e'), ∑ k, Λ k (offsetIndicator (coarseShift S e v)) *
      Λ k (offsetIndicator (coarseShift S e' v)) with hΓ
  set r₀ : ℕ := S + 2 * ρ + 1 with hr₀
  refine ⟨Γ, ∑ e ∈ bondOffsetBox r₀, ∑ e' ∈ bondOffsetBox r₀, |Γ e e'|,
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro N m _ _ sc hm hsc
  have hS0 : 0 < S := hS
  have hNm : m = S * N := by exact_mod_cast hm
  have main : ∀ (y : TorusSite N) (r : ℕ) (e e' : LatticeBond), 2 * (r + ρ + 2 * S + 2) ≤ m →
      BondOffsetInBox r e → BondOffsetInBox r e' →
      gramEntry sc Λ (bondFrom (sc y) e) (bondFrom (sc y) e') = Γ e e' := by
    intro y r e e' hbig he he'
    set R := Rr e e' with hR
    have hSR : S * R ≤ r + ρ + S := by
      have h1 : S * ((max (offsetRadius e) (offsetRadius e') + ρ) / S) ≤
          max (offsetRadius e) (offsetRadius e') + ρ := Nat.mul_div_le _ _
      have h2 : max (offsetRadius e) (offsetRadius e') ≤ r := max_le (offsetRadius_le he) (offsetRadius_le he')
      have : S * R = S * ((max (offsetRadius e) (offsetRadius e') + ρ) / S) + S := by
        rw [hR, hRr]
        ring
      omega
    have h2R : 2 * R < N := by
      have : S * (2 * R) < S * N := by
        rw [← hNm]
        nlinarith
      exact Nat.lt_of_mul_lt_mul_left this
    unfold gramEntry
    rw [sum_eq_sum_offsetBox h2R y]
    · refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun k _ => ?_
      rw [hsc]
      have hv' := mem_offsetBox.1 hv
      congr 1
      · refine (hΛ k).congr _ _ fun u hu => ?_
        exact bondIndicator_shift hbig hSR _ v hv' e u he hu
      · refine (hΛ k).congr _ _ fun u hu => ?_
        exact bondIndicator_shift hbig hSR _ v hv' e' u he' hu
    · intro v hvN hvR
      refine Finset.sum_eq_zero fun k _ => ?_
      push Not at hvR
      obtain ⟨i, hi⟩ := hvR
      suffices hz : Λ k (fun u => bondIndicator (bondFrom (sc y) e) (bondFrom (sc (y + siteOfInt v)) u)) = 0 by
        rw [hz, zero_mul]
      by_contra hne
      obtain ⟨u, hu, hfu⟩ := exists_offset_of_ne_zero (hΛ k) hne
      have hb := bondFrom_eq_of_bondIndicator_ne_zero hfu
      rw [hsc, bondFrom_add_siteOfInt_eq_iff] at hb
      have hz : e.1 i - ((S : ℤ) * v i + u.1 i) = 0 := by
        refine Int.eq_zero_of_abs_lt_dvd (hb.2 i) ?_
        have a1 := he.1 i
        have a2 := hu.1 i
        have a4 : 2 * |(S : ℤ) * v i| ≤ m := by
          rw [abs_mul, Nat.abs_cast, hm]
          have := hvN i
          nlinarith
        have a5 := abs_le.1 (le_refl |(S : ℤ) * v i|)
        rw [abs_le] at a1 a2
        rw [abs_lt]
        constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2, a5.1, a5.2]
      have h1 : (S : ℤ) * |v i| ≤ (offsetRadius e : ℤ) + ρ := by
        have e1 : (S : ℤ) * v i = e.1 i - u.1 i := by linarith
        have : |(S : ℤ) * v i| ≤ (offsetRadius e : ℤ) + ρ := by
          rw [e1]
          exact (abs_sub _ _).trans (add_le_add (abs_le_offsetRadius e i) (hu.1 i))
        rwa [abs_mul, Nat.abs_cast] at this
      have h2 : max (offsetRadius e) (offsetRadius e') + ρ < S * R := Nat.lt_mul_div_succ _ hS0
      have h3 : (R : ℤ) + 1 ≤ |v i| := hi
      have h4 : offsetRadius e ≤ max (offsetRadius e) (offsetRadius e') := le_max_left _ _
      nlinarith
  refine ⟨main, ?_, ?_⟩
  · intro b b' hd
    unfold gramEntry
    refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun k _ => ?_
    by_contra hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
    obtain ⟨u, hu, hfu⟩ := exists_offset_of_ne_zero (hΛ k) h1
    obtain ⟨u', hu', hfu'⟩ := exists_offset_of_ne_zero (hΛ k) h2
    have n1 := supDist_le_of_bondFrom_eq hu (bondFrom_eq_of_bondIndicator_ne_zero hfu)
    have n2 := supDist_le_of_bondFrom_eq hu' (bondFrom_eq_of_bondIndicator_ne_zero hfu')
    have h3 := supDist_triangle b.1 (sc y) b'.1
    rw [supDist_comm b.1 (sc y)] at h3
    omega
  · intro hsurj hbig b b'
    by_cases hd : 2 * ρ < supDist b.1 b'.1
    · have : gramEntry sc Λ b b' = 0 := by
        unfold gramEntry
        refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun k _ => ?_
        by_contra hne
        obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
        obtain ⟨u, hu, hfu⟩ := exists_offset_of_ne_zero (hΛ k) h1
        obtain ⟨u', hu', hfu'⟩ := exists_offset_of_ne_zero (hΛ k) h2
        have n1 := supDist_le_of_bondFrom_eq hu (bondFrom_eq_of_bondIndicator_ne_zero hfu)
        have n2 := supDist_le_of_bondFrom_eq hu' (bondFrom_eq_of_bondIndicator_ne_zero hfu')
        have h3 := supDist_triangle b.1 (sc y) b'.1
        rw [supDist_comm b.1 (sc y)] at h3
        omega
      rw [this, abs_zero]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    · obtain ⟨y, v, hx, hv⟩ := hsurj b.1
      obtain ⟨w, hw, hwb⟩ := exists_offset_of_supDist b.1 b'.1
      have hwb' : ∀ i, |w i| ≤ 2 * (ρ : ℤ) := by
        intro i
        have h1 := hwb i
        have h2 : (w i).natAbs ≤ 2 * ρ := by omega
        rw [Int.abs_eq_natAbs]
        exact_mod_cast h2
      set e : LatticeBond := (v, b.2) with he
      set e' : LatticeBond := (v + w, b'.2) with he'
      have hb : bondFrom (sc y) e = b := by
        unfold bondFrom
        rw [he]
        exact Prod.ext hx.symm rfl
      have hb' : bondFrom (sc y) e' = b' := by
        unfold bondFrom
        rw [he']
        refine Prod.ext ?_ rfl
        show sc y + siteOfInt (v + w) = b'.1
        rw [siteOfInt_add_eq, ← add_assoc, ← hx, ← hw]
      have single_le : ∀ (d i : Fin 4), |(Pi.single d 1 : Fin 4 → ℤ) i| ≤ 1 := by
        intro d i
        by_cases h : i = d
        · subst h
          simp
        · simp [h]
      have box_e : BondOffsetInBox r₀ e := by
        have hr : (r₀ : ℤ) = S + 2 * ρ + 1 := by rw [hr₀]; push_cast; ring
        refine ⟨fun i => ?_, fun i => ?_⟩
        · have := hv i
          show |v i| ≤ (r₀ : ℤ)
          rw [hr]
          have : (0 : ℤ) ≤ ρ := by positivity
          linarith [hv i]
        · show |(v + (Pi.single b.2 1 : Fin 4 → ℤ)) i| ≤ (r₀ : ℤ)
          rw [hr, Pi.add_apply]
          have : (0 : ℤ) ≤ ρ := by positivity
          linarith [abs_add_le (v i) ((Pi.single b.2 1 : Fin 4 → ℤ) i), hv i, single_le b.2 i]
      have box_e' : BondOffsetInBox r₀ e' := by
        have hr : (r₀ : ℤ) = S + 2 * ρ + 1 := by rw [hr₀]; push_cast; ring
        refine ⟨fun i => ?_, fun i => ?_⟩
        · show |(v + w) i| ≤ (r₀ : ℤ)
          rw [hr, Pi.add_apply]
          linarith [abs_add_le (v i) (w i), hv i, hwb' i]
        · show |(v + w + (Pi.single b'.2 1 : Fin 4 → ℤ)) i| ≤ (r₀ : ℤ)
          rw [hr, Pi.add_apply, Pi.add_apply]
          linarith [abs_add_le (v i + w i) ((Pi.single b'.2 1 : Fin 4 → ℤ) i), abs_add_le (v i) (w i), hv i,
            hwb' i, single_le b'.2 i]
      have hbig' : 2 * (r₀ + ρ + 2 * S + 2) ≤ m := by
        rw [hr₀]
        omega
      have hmain := main y r₀ e e' hbig' box_e box_e'
      rw [hb, hb'] at hmain
      rw [hmain]
      have hne : |Γ e e'| ≤ ∑ e'' ∈ bondOffsetBox r₀, |Γ e e''| :=
        Finset.single_le_sum (f := fun e'' => |Γ e e''|) (fun _ _ => abs_nonneg _) (mem_bondOffsetBox box_e')
      exact hne.trans (Finset.single_le_sum (f := fun e'' => ∑ e''' ∈ bondOffsetBox r₀, |Γ e'' e'''|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (mem_bondOffsetBox box_e))
end LocalFunctionals
end YangMills.Construction
end

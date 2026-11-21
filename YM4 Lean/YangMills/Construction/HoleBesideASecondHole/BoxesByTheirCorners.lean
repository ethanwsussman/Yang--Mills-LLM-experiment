import YangMills.Construction.ClusterExpansionOfAStep.LumpsAreFibres
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace CornerBoxes
open BlockAverages LumpContours
variable {F : BlockFrame} {j : ℕ}
abbrev CornerPair : Type := (Fin 4 → ℤ) × (Fin 4 → ℤ)
def boxOfCorners (F : BlockFrame) (j : ℕ) (q : CornerPair) : Finset (F.Site j) := boxSites j q.1 q.2
def sideWidth (q : CornerPair) (i : Fin 4) : ℤ := q.2 i - q.1 i + 1
def largestSide {j : ℕ} (Z : Finset (F.Site j)) : ℕ :=
  Finset.univ.sup fun i : Fin 4 => (Z.image fun x => x i).card
def maxSideWidth (q : CornerPair) : ℕ := Finset.univ.sup fun i : Fin 4 => (sideWidth q i).toNat
theorem sideWidth_le_maxSideWidth (q : CornerPair) (i : Fin 4) : sideWidth q i ≤ maxSideWidth q := by
  have h : (sideWidth q i).toNat ≤ maxSideWidth q :=
    Finset.le_sup (f := fun i : Fin 4 => (sideWidth q i).toNat) (Finset.mem_univ i)
  omega
theorem mem_boxOfCorners {q : CornerPair} {x : F.Site j} :
    x ∈ boxOfCorners F j q ↔ ∃ a : Fin 4 → ℤ, (∀ i, q.1 i ≤ a i ∧ a i ≤ q.2 i) ∧ siteOfCoords j a = x := by
  simp only [boxOfCorners, boxSites, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc]
theorem siteOfCoords_add_period_mul (a k : Fin 4 → ℤ) :
    (siteOfCoords j (fun i => a i + (F.period j i : ℤ) * k i) : F.Site j) = siteOfCoords j a := by
  funext i
  simp [siteOfCoords]
theorem exists_period_translate_of_interval {P : ℕ} (a₁ a₂ b₁ b₂ : ℤ) (ha : a₁ ≤ a₂) (hw : b₂ - b₁ + 2 ≤ P)
    (h : ∀ c, a₁ ≤ c → c ≤ a₂ → ∃ b, b₁ ≤ b ∧ b ≤ b₂ ∧ (c : ZMod P) = (b : ZMod P)) :
    ∃ k : ℤ, b₁ + k * P ≤ a₁ ∧ a₂ ≤ b₂ + k * P := by
  obtain ⟨b, hb₁, hb₂, hb⟩ := h a₁ le_rfl ha
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hb
  obtain ⟨k, hk⟩ := hb
  have hk' : a₁ = b + (-k) * P := by linarith
  refine ⟨-k, by rw [hk']; linarith, ?_⟩
  have key : ∀ n : ℕ, a₁ + n ≤ a₂ → a₁ + n ≤ b₂ + (-k) * P := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [hk']
      push_cast
      linarith
    | succ n ih =>
      intro hn
      push_cast at hn ⊢
      have h1 := ih (by push_cast; linarith)
      obtain ⟨b', hb'₁, hb'₂, hb'⟩ := h (a₁ + (n + 1)) (by linarith) hn
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hb'
      obtain ⟨k', hk''⟩ := hb'
      have hlow : b₁ + (-k) * P ≤ a₁ + n := by
        have : (0 : ℤ) ≤ n := by positivity
        rw [hk']
        linarith
      rcases lt_trichotomy (-k') (-k) with c | c | c
      · have h2 : (-k' + 1) * (P : ℤ) ≤ (-k) * P :=
          mul_le_mul_of_nonneg_right (by omega) (by positivity)
        nlinarith
      · have : k' = k := by omega
        subst this
        nlinarith
      · have h2 : (-k + 1) * (P : ℤ) ≤ (-k') * P :=
          mul_le_mul_of_nonneg_right (by omega) (by positivity)
        nlinarith
  have := key (a₂ - a₁).toNat (by omega)
  have e : a₁ + ((a₂ - a₁).toNat : ℤ) = a₂ := by omega
  rwa [e] at this
theorem exists_residue_of_boxOfCorners_subset {q : CornerPair} {lo hi : Fin 4 → ℤ} (hq : ∀ i, q.1 i ≤ q.2 i)
    (hsub : boxOfCorners F j q ⊆ boxSites j lo hi) (i : Fin 4) (c : ℤ) (h₁ : q.1 i ≤ c) (h₂ : c ≤ q.2 i) :
    ∃ b, lo i ≤ b ∧ b ≤ hi i ∧ (c : ZMod (F.period j i)) = (b : ZMod (F.period j i)) := by
  classical
  have hm : siteOfCoords j (Function.update q.1 i c) ∈ boxOfCorners F j q := by
    refine mem_boxOfCorners.mpr ⟨Function.update q.1 i c, fun l => ?_, rfl⟩
    by_cases hl : l = i
    · subst hl
      simpa using ⟨h₁, h₂⟩
    · simpa [Function.update_of_ne hl] using hq l
  obtain ⟨a, ha, he⟩ := mem_boxOfCorners.mp (show _ ∈ boxOfCorners F j (lo, hi) from hsub hm)
  refine ⟨a i, (ha i).1, (ha i).2, ?_⟩
  have := congrFun he i
  simpa [siteOfCoords] using this.symm
theorem boxOfCorners_subset_of_translate {q : CornerPair} {lo hi k : Fin 4 → ℤ}
    (H : ∀ i, lo i + k i * F.period j i ≤ q.1 i ∧ q.2 i ≤ hi i + k i * F.period j i) :
    boxOfCorners F j q ⊆ boxSites j lo hi := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_boxOfCorners.mp hx
  refine (mem_boxOfCorners (q := (lo, hi))).mpr ⟨fun i => a i - k i * F.period j i, fun i => ?_, ?_⟩
  · have h1 := H i
    have h2 := ha i
    simp only
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · have := siteOfCoords_add_period_mul (F := F) (j := j) (fun i => a i - k i * F.period j i) k
    rw [← this]
    congr 1
    funext i
    ring
theorem thicken_boxSites (m : ℕ) (lo hi : Fin 4 → ℤ) (hlo : ∀ i, lo i ≤ hi i) :
    thicken m (boxSites j lo hi : Finset (F.Site j)) =
      boxOfCorners F j (fun i => lo i - m, fun i => hi i + m) := by
  classical
  ext z
  simp only [thicken, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, h, hh, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have ha' := Fintype.mem_piFinset.mp ha
    have hh' := Fintype.mem_piFinset.mp hh
    refine mem_boxOfCorners.mpr ⟨a + h, fun i => ?_, ?_⟩
    · have h1 := Finset.mem_Icc.mp (ha' i)
      have h2 := Finset.mem_Icc.mp (hh' i)
      have hm : (((2 * m + 1 : ℕ) : ℤ) - 1) / 2 = m := by
        push_cast
        omega
      rw [hm] at h2
      simp only [Pi.add_apply]
      constructor <;> omega
    · funext i
      simp [siteOfCoords]
  · intro hz
    obtain ⟨b, hb, rfl⟩ := mem_boxOfCorners.mp hz
    let a : Fin 4 → ℤ := fun i => max (lo i) (min (hi i) (b i))
    refine ⟨siteOfCoords j a, Finset.mem_image.mpr ⟨a, Fintype.mem_piFinset.mpr fun i => ?_, rfl⟩,
      b - a, Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩
    · have := hlo i
      refine Finset.mem_Icc.mpr ⟨le_max_left _ _, max_le this (min_le_left _ _)⟩
    · have hm : (((2 * m + 1 : ℕ) : ℤ) - 1) / 2 = m := by
        push_cast
        omega
      rw [hm]
      have h1 := hb i
      simp only at h1
      have h2 := hlo i
      simp only [Pi.sub_apply, a]
      refine Finset.mem_Icc.mpr ?_
      rcases le_total (hi i) (b i) with c1 | c1 <;> rcases le_total (lo i) (min (hi i) (b i)) with c2 | c2 <;>
        simp only [min_eq_left c1, min_eq_right c1, max_eq_left c2, max_eq_right c2] at c2 ⊢ <;>
        omega
    · funext i
      simp [siteOfCoords]
theorem offsetFromCentre_spec {L : ℕ} (hL : 0 < L) (hodd : Odd L) (c : ℤ) :
    (L : ℤ) ∣ c - offsetFromCentre L c ∧ |offsetFromCentre L c| ≤ ((L : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.TorusLumps.offsetFromCentre_spec <;> assumption
def lumpCornerPair {L : ℕ} (g : LumpGrid L) {j : ℕ} (x : F.Site j) : CornerPair :=
  (fun i => siteCoords x i - offsetFromCentre L (siteCoords x i) + g.lower (offsetFromCentre L (siteCoords x i)),
    fun i => siteCoords x i - offsetFromCentre L (siteCoords x i) + g.upper (offsetFromCentre L (siteCoords x i)))
theorem lumpCornerPair_side {L : ℕ} (hL : 0 < L) (hodd : Odd L) (g : LumpGrid L) (x : F.Site j) (i : Fin 4) :
    (lumpCornerPair g x).1 i ≤ (lumpCornerPair g x).2 i ∧ sideWidth (lumpCornerPair g x) i < 2 ^ 15 := by
  obtain ⟨_, ho⟩ := offsetFromCentre_spec hL hodd (siteCoords x i)
  have hs := g.interval_length _ ho
  simp only [lumpCornerPair, sideWidth]
  constructor <;> linarith [hs.1, hs.2]
theorem lumpCollar_eq_box {L : ℕ} (hL : 0 < L) (hodd : Odd L) (g : LumpGrid L) (x : F.Site j) :
    ∃ q : CornerPair, (∀ i, q.1 i ≤ q.2 i) ∧ lumpCollar (lumpOf g x) = boxOfCorners F j q ∧
      maxSideWidth q + 2 ≤ 11 * 2 ^ 12 := by
  have hb := lumpCornerPair_side (F := F) (j := j) hL hodd g x
  have hw : lumpRange + 2 = 4098 := rfl
  refine ⟨(fun i => (lumpCornerPair g x).1 i - ((lumpRange + 2 : ℕ) : ℤ),
    fun i => (lumpCornerPair g x).2 i + ((lumpRange + 2 : ℕ) : ℤ)), fun i => ?_,
    thicken_boxSites _ _ _ fun i => (hb i).1, ?_⟩
  · have := (hb i).1
    simp only [hw]
    omega
  · have : maxSideWidth (fun i => (lumpCornerPair g x).1 i - ((lumpRange + 2 : ℕ) : ℤ),
        fun i => (lumpCornerPair g x).2 i + ((lumpRange + 2 : ℕ) : ℤ)) ≤ 11 * 2 ^ 12 - 2 := by
      refine Finset.sup_le fun i _ => ?_
      have h1 := (hb i).2
      simp only [sideWidth, hw] at h1 ⊢
      omega
    omega
theorem largestSide_boxOfCorners_le (q : CornerPair) (hq : ∀ i, q.1 i ≤ q.2 i) :
    largestSide (boxOfCorners F j q) ≤ maxSideWidth q := by
  refine Finset.sup_le fun i _ => ?_
  have h1 : (boxOfCorners F j q).image (fun x => x i) ⊆
      (Finset.Icc (q.1 i) (q.2 i)).image fun c : ℤ => (c : ZMod (F.period j i)) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a, ha, rfl⟩ := mem_boxOfCorners.mp hx
    exact Finset.mem_image.mpr ⟨a i, Finset.mem_Icc.mpr (ha i), rfl⟩
  have h2 := (Finset.card_le_card h1).trans Finset.card_image_le
  rw [Int.card_Icc] at h2
  have h3 : (sideWidth q i).toNat ≤ maxSideWidth q :=
    Finset.le_sup (f := fun i : Fin 4 => (sideWidth q i).toNat) (Finset.mem_univ i)
  simp only [sideWidth] at h3
  omega
end CornerBoxes
end YangMills.Construction
end

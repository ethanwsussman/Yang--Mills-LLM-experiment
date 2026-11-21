import YangMills.Construction.ColdChainAtEveryLevel.HomotopyFormulaProof
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.LawOnABoxOfTheFlow.FormOfACubeProof
import YangMills.Construction.FormsOnATorus.AxialLadderOnACube
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open TorusFields ResponseInTheExpansion
open BlockAverages hiding unitStep
namespace AxialGauge
section IntervalSums
variable {E : Type*} [AddCommGroup E]
private def intervalSum (f : ℤ → E) (a b : ℤ) : E := ∑ t ∈ Finset.Ico a b, f t - ∑ t ∈ Finset.Ico b a, f t
private theorem intervalSum_succ (f : ℤ → E) (a b : ℤ) : intervalSum f a (b + 1) = intervalSum f a b + f b := by
  classical
  unfold intervalSum
  by_cases hab : a ≤ b
  · have e1 : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
      ext t
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have e2 : Finset.Ico (b + 1) a = ∅ := Finset.Ico_eq_empty (by omega)
    have e3 : Finset.Ico b a = ∅ := Finset.Ico_eq_empty (by omega)
    rw [e1, e2, e3, Finset.sum_insert (by simp)]
    simp only [Finset.sum_empty, sub_zero]
    abel
  · have e1 : Finset.Ico a (b + 1) = ∅ := Finset.Ico_eq_empty (by omega)
    have e2 : Finset.Ico a b = ∅ := Finset.Ico_eq_empty (by omega)
    have e3 : Finset.Ico b a = insert b (Finset.Ico (b + 1) a) := by
      ext t
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [e1, e2, e3, Finset.sum_insert (by simp)]
    simp only [Finset.sum_empty]
    abel
private theorem intervalSum_telescope (F : ℤ → E) (a b : ℤ) :
    intervalSum (fun t => F (t + 1) - F t) a b = F b - F a := by
  refine Int.inductionOn' b a ?_ ?_ ?_
  · simp [intervalSum]
  · intro k _ ih
    rw [intervalSum_succ, ih]
    abel
  · intro k _ ih
    have hk := intervalSum_succ (fun t => F (t + 1) - F t) a (k - 1)
    rw [sub_add_cancel, ih] at hk
    have hk2 : intervalSum (fun t => F (t + 1) - F t) a (k - 1) = F k - F a - (F k - F (k - 1)) := by
      rw [hk]
      abel
    rw [hk2]
    abel
private theorem intervalSum_sub (f g : ℤ → E) (a b : ℤ) :
    intervalSum (fun t => f t - g t) a b = intervalSum f a b - intervalSum g a b := by
  simp only [intervalSum, Finset.sum_sub_distrib]
  abel
private theorem intervalSum_neg (f : ℤ → E) (a b : ℤ) : intervalSum (fun t => - f t) a b = - intervalSum f a b := by
  simp only [intervalSum, Finset.sum_neg_distrib]
  abel
end IntervalSums
private theorem norm_intervalSum_le {E : Type*} [NormedAddCommGroup E] (f : ℤ → E) (a b : ℤ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ t, min a b ≤ t → t < max a b → ‖f t‖ ≤ M) : ‖intervalSum f a b‖ ≤ (|b - a| : ℤ) * M := by
  unfold intervalSum
  by_cases hab : a ≤ b
  · rw [Finset.Ico_eq_empty (by omega : ¬ b < a), Finset.sum_empty, sub_zero]
    have h1 : ‖∑ t ∈ Finset.Ico a b, f t‖ ≤ (Finset.Ico a b).card * M := by
      refine (norm_sum_le_of_le (n := fun _ => M) _ fun t ht => ?_).trans (by simp)
      have := Finset.mem_Ico.mp ht
      exact hf t (by rw [min_eq_left hab]; exact this.1) (by rw [max_eq_right hab]; exact this.2)
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ hM)
    rw [Int.card_Ico, abs_of_nonneg (by omega)]
    have : (((b - a).toNat : ℤ)) = b - a := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this.le
  · have hba : b ≤ a := by omega
    rw [Finset.Ico_eq_empty (by omega : ¬ a < b), Finset.sum_empty, zero_sub, norm_neg]
    have h1 : ‖∑ t ∈ Finset.Ico b a, f t‖ ≤ (Finset.Ico b a).card * M := by
      refine (norm_sum_le_of_le (n := fun _ => M) _ fun t ht => ?_).trans (by simp)
      have := Finset.mem_Ico.mp ht
      exact hf t (by rw [min_eq_right hba]; exact this.1) (by rw [max_eq_left hba]; exact this.2)
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ hM)
    rw [Int.card_Ico, abs_of_nonpos (by omega)]
    have : (((a - b).toNat : ℤ)) = a - b := Int.toNat_of_nonneg (by omega)
    have h2 : (((a - b).toNat : ℤ)) ≤ -(b - a) := by omega
    exact_mod_cast h2
section AxialPath
private abbrev IntPoint : Type := Fin 4 → ℤ
private def basisVec (i : Fin 4) : IntPoint := Pi.single i 1
private def splice (g h : IntPoint) (j : ℕ) : IntPoint := fun l => if l.val < j then h l else g l
private def legPoint (g h : IntPoint) (j : Fin 4) (t : ℤ) : IntPoint := Function.update (splice g h j.val) j t
private theorem legPoint_succ (g h : IntPoint) (j : Fin 4) (t : ℤ) :
    legPoint g h j (t + 1) = legPoint g h j t + basisVec j := by
  funext l
  by_cases hl : l = j
  · subst hl
    simp [legPoint, basisVec]
  · simp [legPoint, basisVec, hl, Function.update_of_ne]
private theorem legPoint_end (g h : IntPoint) (j : Fin 4) : legPoint g h j (h j) = splice g h (j.val + 1) := by
  funext l
  by_cases hl : l = j
  · subst hl
    simp [legPoint, splice]
  · have hv : l.val ≠ j.val := fun e => hl (Fin.ext e)
    simp only [legPoint, splice, Function.update_of_ne hl]
    by_cases h1 : l.val < j.val
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]
private theorem legPoint_start (g h : IntPoint) (j : Fin 4) : legPoint g h j (g j) = splice g h j.val := by
  funext l
  by_cases hl : l = j
  · subst hl
    simp [legPoint, splice]
  · simp [legPoint, hl, Function.update_of_ne]
private theorem splice_four (g h : IntPoint) : splice g h 4 = h := by apply _root_.YangMills.Construction.LatticeFractionalIntegration.StaircaseHomotopy.staircasePoint_four <;> assumption
private theorem legPoint_shift_of_lt (g h : IntPoint) {i j : Fin 4} (hij : i < j) (t : ℤ) :
    legPoint g (h + basisVec i) j t = legPoint g h j t + basisVec i := by
  funext l
  by_cases hl : l = j
  · subst hl
    have hne : l ≠ i := (ne_of_lt hij).symm
    simp [legPoint, basisVec, hne]
  · by_cases hi : l = i
    · subst hi
      have h1 : l.val < j.val := hij
      simp [legPoint, splice, basisVec, hl, Function.update_of_ne, h1]
    · have h3 : (basisVec i) l = 0 := by simp [basisVec, hi]
      simp only [legPoint, Function.update_of_ne hl, Pi.add_apply, h3, add_zero, splice]
private theorem legPoint_shift_of_le (g h : IntPoint) {i j : Fin 4} (hij : j ≤ i) (t : ℤ) :
    legPoint g (h + basisVec i) j t = legPoint g h j t := by
  funext l
  by_cases hl : l = j
  · subst hl
    simp [legPoint]
  · have hli : l.val < j.val → l ≠ i := fun h1 e => by
      subst e
      exact absurd hij (not_le.mpr h1)
    simp only [legPoint, Function.update_of_ne hl, splice]
    split_ifs with h1
    · simp [basisVec, hli h1]
    · rfl
variable {E : Type*} [AddCommGroup E]
private def legSum (f : IntPoint → Fin 4 → E) (g h : IntPoint) (j : Fin 4) : E :=
  intervalSum (fun t => f (legPoint g h j t) j) (g j) (h j)
private def pathPotential (f : IntPoint → Fin 4 → E) (g h : IntPoint) : E := ∑ j, legSum f g h j
private def plaquetteCurl (f : IntPoint → Fin 4 → E) (w : IntPoint) (i j : Fin 4) : E :=
  f w i + f (w + basisVec i) j - f (w + basisVec j) i - f w j
private theorem legSum_of_lt (f : IntPoint → Fin 4 → E) (g h : IntPoint) {i j : Fin 4} (hij : j < i) :
    legSum f g (h + basisVec i) j = legSum f g h j := by
  have h1 : (h + basisVec i) j = h j := by simp [basisVec, (ne_of_lt hij)]
  unfold legSum
  rw [h1]
  simp only [legPoint_shift_of_le g h hij.le]
private theorem legSum_self (f : IntPoint → Fin 4 → E) (g h : IntPoint) (i : Fin 4) :
    legSum f g (h + basisVec i) i = legSum f g h i + f (splice g h (i.val + 1)) i := by
  have h1 : (h + basisVec i) i = h i + 1 := by simp [basisVec]
  unfold legSum
  rw [h1]
  simp only [legPoint_shift_of_le g h (le_refl i)]
  rw [intervalSum_succ, legPoint_end]
private theorem legSum_of_gt (f : IntPoint → Fin 4 → E) (g h : IntPoint) {i j : Fin 4} (hij : i < j) :
    legSum f g (h + basisVec i) j - legSum f g h j =
      intervalSum (fun t => f (legPoint g h j t + basisVec i) j - f (legPoint g h j t) j) (g j) (h j) := by
  have h1 : (h + basisVec i) j = h j := by simp [basisVec, (ne_of_lt hij).symm]
  unfold legSum
  rw [h1]
  simp only [legPoint_shift_of_lt g h hij]
  rw [intervalSum_sub]
private theorem splice_step (f : IntPoint → Fin 4 → E) (g h : IntPoint) (i j : Fin 4) :
    f (splice g h (j.val + 1)) i - f (splice g h j.val) i =
      intervalSum (fun t => f (legPoint g h j t + basisVec j) i - f (legPoint g h j t) i) (g j) (h j) := by
  have h1 := intervalSum_telescope (fun t => f (legPoint g h j t) i) (g j) (h j)
  simp only [legPoint_succ, legPoint_end, legPoint_start] at h1
  exact h1.symm
private theorem telescope_fin_four (G : ℕ → E) (i : Fin 4) :
    G 4 - G (i.val + 1) = ∑ j : Fin 4, if i < j then G (j.val + 1) - G j.val else 0 := by
  fin_cases i <;> simp [Fin.sum_univ_four]
open Classical in
private theorem sub_pathPotential_step (f : IntPoint → Fin 4 → E) (g h : IntPoint) (i : Fin 4) :
    f h i - (pathPotential f g (h + basisVec i) - pathPotential f g h) =
      ∑ j : Fin 4, if i < j then - intervalSum (fun t => plaquetteCurl f (legPoint g h j t) i j) (g j) (h j) else 0 := by
  have hd : ∀ j : Fin 4, legSum f g (h + basisVec i) j - legSum f g h j =
      (if j = i then f (splice g h (i.val + 1)) i else 0) +
        (if i < j then intervalSum (fun t => f (legPoint g h j t + basisVec i) j - f (legPoint g h j t) j) (g j) (h j)
          else 0) := by
    intro j
    rcases lt_trichotomy j i with hj | hj | hj
    · rw [legSum_of_lt f g h hj, if_neg (ne_of_lt hj), if_neg (not_lt.mpr hj.le)]
      simp
    · subst hj
      rw [legSum_self]
      simp
    · rw [legSum_of_gt f g h hj, if_neg (ne_of_lt hj).symm, if_pos hj, zero_add]
  have h2 : pathPotential f g (h + basisVec i) - pathPotential f g h =
      f (splice g h (i.val + 1)) i +
        ∑ j : Fin 4, if i < j then
          intervalSum (fun t => f (legPoint g h j t + basisVec i) j - f (legPoint g h j t) j) (g j) (h j)
          else 0 := by
    unfold pathPotential
    rw [← Finset.sum_sub_distrib]
    simp only [hd]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ]
    simp
  have h3 := telescope_fin_four (fun m => f (splice g h m) i) i
  simp only [splice_four] at h3
  have h4 : f h i = f (splice g h (i.val + 1)) i + ∑ j : Fin 4, if i < j then
      intervalSum (fun t => f (legPoint g h j t + basisVec j) i - f (legPoint g h j t) i) (g j) (h j) else 0 := by
    have h5 : (∑ j : Fin 4, if i < j then
        intervalSum (fun t => f (legPoint g h j t + basisVec j) i - f (legPoint g h j t) i) (g j) (h j) else 0) =
        f h i - f (splice g h (i.val + 1)) i := by
      rw [h3]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · exact (splice_step f g h i j).symm
      · rfl
    rw [h5]
    abel
  rw [h2, h4, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rw [← intervalSum_sub, ← intervalSum_neg]
    congr 1
    funext t
    simp only [plaquetteCurl]
    abel
  · simp
end AxialPath
section Gauge
variable {n : ℕ} [NeZero n]
private def coords (o x : TorusSite n) : IntPoint := fun l => (x l - o l).valMinAbs
private def siteAt (o : TorusSite n) (h : IntPoint) : TorusSite n := o + siteOfInt h
private theorem siteAt_coords (o x : TorusSite n) : siteAt o (coords o x) = x := by apply _root_.YangMills.DeltaSharedProofs.p500399 <;> assumption
private theorem siteAt_add_basisVec (o : TorusSite n) (h : IntPoint) (i : Fin 4) :
    siteAt o (h + basisVec i) = siteAt o h + unitStep n i := by
  funext l
  by_cases hl : l = i
  · subst hl
    simp [siteAt, siteOfInt, basisVec, unitStep]
    ring
  · simp [siteAt, siteOfInt, basisVec, unitStep, hl]
abbrev _root_.YangMills.DeltaSharedProofs.p500616 := @siteAt_add_basisVec
private theorem valMinAbs_intCast {a : ℤ} (ha : 2 * |a| < n) : ((a : ZMod n)).valMinAbs = a := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
private theorem mem_supBall_iff {o x : TorusSite n} {R : ℕ} :
    x ∈ supBall o (2 * R) ↔ ∀ l, |coords o x l| ≤ 2 * (R : ℤ) := by apply _root_.YangMills.DeltaSharedProofs.p501575 <;> assumption
private theorem coords_add_unitStep {o x : TorusSite n} {R : ℕ} (hR : 1 ≤ R) (hn : 16 * R < n)
    (hx : x ∈ supBall o (2 * R)) (i : Fin 4) :
    coords o (x + unitStep n i) = coords o x + basisVec i := by
  funext l
  have hb := mem_supBall_iff.mp hx l
  have e : (x + unitStep n i) l - o l = ((coords o x l + basisVec i l : ℤ) : ZMod n) := by
    by_cases hl : l = i
    · subst hl
      simp [coords, basisVec, unitStep, ZMod.coe_valMinAbs]
      ring
    · simp [coords, basisVec, unitStep, hl, ZMod.coe_valMinAbs]
  have h1 : |basisVec i l| ≤ 1 := by
    by_cases hl : l = i
    · subst hl
      simp [basisVec]
    · simp [basisVec, hl]
  show ((x + unitStep n i) l - o l).valMinAbs = _
  rw [e, valMinAbs_intCast]
  · rfl
  · simp only [Int.abs_eq_natAbs] at hb h1 ⊢
    omega
private theorem abs_coords_sub_le {o x y : TorusSite n} {R : ℕ} (hn : 16 * R < n) (hx : x ∈ supBall o (2 * R))
    (hy : y ∈ supBall o (2 * R)) (l : Fin 4) : |coords o x l - coords o y l| ≤ (supDist x y : ℤ) := by
  have h1 := mem_supBall_iff.mp hx l
  have h2 := mem_supBall_iff.mp hy l
  have e : x l - y l = ((coords o x l - coords o y l : ℤ) : ZMod n) := by
    simp [coords, ZMod.coe_valMinAbs]
  have h3 : 2 * |coords o x l - coords o y l| < n := by
    simp only [Int.abs_eq_natAbs] at h1 h2 ⊢
    omega
  have h4 := (supDist_le_iff x y _).mp le_rfl l
  rw [e, valMinAbs_intCast h3] at h4
  simp only [Int.abs_eq_natAbs]
  omega
private theorem supDist_siteAt_le {o : TorusSite n} {w g : IntPoint} {d : ℕ} (hd : 2 * d < n)
    (hwg : ∀ l, |w l - g l| ≤ (d : ℤ)) : supDist (siteAt o w) (siteAt o g) ≤ d := by
  rw [supDist_le_iff]
  intro l
  have e : siteAt o w l - siteAt o g l = ((w l - g l : ℤ) : ZMod n) := by
    simp [siteAt, siteOfInt]
  have h4 := hwg l
  have h3 : 2 * |w l - g l| < n := by
    omega
  rw [e, valMinAbs_intCast h3]
  rw [Int.abs_eq_natAbs] at h4
  omega
private theorem siteAt_mem_supBall {o : TorusSite n} {R : ℕ} (hn : 16 * R < n) {u : IntPoint}
    (hu : ∀ l, |u l| ≤ 2 * (R : ℤ)) : siteAt o u ∈ supBall o (2 * R) := by
  have h1 : supDist (siteAt o u) (siteAt o 0) ≤ 2 * R := by
    refine supDist_siteAt_le (by omega) fun l => ?_
    simpa using hu l
  have h2 : siteAt o 0 = o := by
    funext l
    simp [siteAt, siteOfInt]
  rw [h2] at h1
  simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and]
  exact_mod_cast h1
private theorem plaquetteCurl_siteAt (v : TorusBond n → imaginaryQuaternions) (o : TorusSite n) (w : IntPoint)
    (i j : Fin 4) :
    plaquetteCurl (fun w i => v (siteAt o w, i)) w i j = lieFormCurl v (siteAt o w, i, j) := by
  simp only [plaquetteCurl, lieFormCurl, siteAt_add_basisVec]
private theorem sum_ite_lt_le {i : Fin 4} {m : ℝ} (hm : 0 ≤ m) : ∑ j : Fin 4, (if i < j then m else 0) ≤ 3 * m := by
  fin_cases i <;> simp [Fin.sum_univ_four] <;> linarith
private theorem mem_plaquettesIn {S : Finset (TorusSite n)} {p : TorusPlaquette n} :
    p ∈ plaquettesIn S ↔ p.2.1 < p.2.2 ∧ ∀ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, z ∈ S := by apply _root_.YangMills.Construction.TorusLumps.mem_plaquettesIn_iff_forall_vertex <;> assumption
open Classical in
private theorem exists_axial_gauge {R : ℕ} (hR : 1 ≤ R) (hn : 16 * R < n) {o y : TorusSite n}
    (hy : y ∈ supBall o (2 * R)) (v : TorusBond n → imaginaryQuaternions) :
    ∃ A : TorusBond n → imaginaryQuaternions,
      (∀ (x : TorusSite n) (i : Fin 4),
        ¬ (x ∈ supBall o (2 * R) ∧ x + unitStep n i ∈ supBall o (2 * R)) → A (x, i) = 0) ∧
      (∀ p ∈ plaquettesIn (supBall o (2 * R)), lieFormCurl (v - A) p = 0) ∧
      ∀ (x : TorusSite n) (i : Fin 4) (M : ℝ), 0 ≤ M → x ∈ supBall o (2 * R) →
        x + unitStep n i ∈ supBall o (2 * R) →
        (∀ p ∈ plaquettesIn (supBall o (2 * R)), supDist p.1 y ≤ supDist x y → ‖lieFormCurl v p‖ ≤ M) →
        ‖A (x, i)‖ ≤ 3 * ((supDist x y : ℝ) * M) := by
  set S := supBall o (2 * R) with hS
  set f : IntPoint → Fin 4 → imaginaryQuaternions := fun w i => v (siteAt o w, i) with hf
  set g : IntPoint := coords o y with hg
  set Psi : TorusSite n → imaginaryQuaternions := fun x => pathPotential f g (coords o x) with hPsi
  refine ⟨fun b => if b.1 ∈ S ∧ b.1 + unitStep n b.2 ∈ S then v b - (Psi (b.1 + unitStep n b.2) - Psi b.1) else 0,
    fun x i hb => if_neg hb, ?_, ?_⟩
  · rintro ⟨x, μ, ν⟩ hp
    have hc := (mem_plaquettesIn.mp hp).2
    have c1 : x ∈ S := hc _ (by simp [plaquetteVertices])
    have c2 : x + unitStep n μ ∈ S := hc _ (by simp [plaquetteVertices])
    have c3 : x + unitStep n ν ∈ S := hc _ (by simp [plaquetteVertices])
    have c4 : x + unitStep n μ + unitStep n ν ∈ S := hc _ (by simp [plaquetteVertices])
    have c4' : x + unitStep n ν + unitStep n μ ∈ S := by rwa [add_right_comm]
    simp only [lieFormCurl, Pi.sub_apply]
    rw [if_pos (⟨c1, c2⟩ : x ∈ S ∧ x + unitStep n μ ∈ S),
      if_pos (⟨c2, c4⟩ : x + unitStep n μ ∈ S ∧ x + unitStep n μ + unitStep n ν ∈ S),
      if_pos (⟨c3, c4'⟩ : x + unitStep n ν ∈ S ∧ x + unitStep n ν + unitStep n μ ∈ S),
      if_pos (⟨c1, c3⟩ : x ∈ S ∧ x + unitStep n ν ∈ S)]
    simp only [add_right_comm x (unitStep n ν) (unitStep n μ)]
    abel
  · intro x i M hM hx hx' hcurl
    beta_reduce
    rw [if_pos (⟨hx, hx'⟩ : x ∈ S ∧ x + unitStep n i ∈ S)]
    set h : IntPoint := coords o x with hh
    have hd : (x, i).1 + unitStep n (x, i).2 = x + unitStep n i := rfl
    have e1 : v (x, i) = f h i := by simp only [hf, hh, siteAt_coords]
    have e2 : Psi (x + unitStep n i) = pathPotential f g (h + basisVec i) := by
      simp only [hPsi, hh, coords_add_unitStep hR hn hx]
    have e3 : Psi x = pathPotential f g h := rfl
    show ‖v (x, i) - (Psi (x + unitStep n i) - Psi x)‖ ≤ _
    rw [e1, e2, e3, sub_pathPotential_step]
    set d : ℕ := supDist x y with hdd
    have hdM : 0 ≤ (d : ℝ) * M := by positivity
    refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_ite_lt_le (i := i) hdM))
    split_ifs with hij
    swap
    · simp
    rw [norm_neg]
    have hgb := fun l => mem_supBall_iff.mp hy l
    have hhb := fun l => mem_supBall_iff.mp hx l
    have hib : ∀ l, |(h + basisVec i) l| ≤ 2 * (R : ℤ) := fun l => by
      have := mem_supBall_iff.mp hx' l
      rwa [coords_add_unitStep hR hn hx] at this
    have hdist : ∀ l, |h l - g l| ≤ (d : ℤ) := fun l => abs_coords_sub_le hn hx hy l
    have hd2 : 2 * d < n := by
      have h1 : d ≤ 4 * R := by
        rw [hdd, supDist_le_iff]
        intro l
        have e : x l - y l = ((coords o x l - coords o y l : ℤ) : ZMod n) := by
          simp [coords, ZMod.coe_valMinAbs]
        have a1 := hhb l
        have a2 := hgb l
        simp only [Int.abs_eq_natAbs] at a1 a2
        rw [e, valMinAbs_intCast (by simp only [Int.abs_eq_natAbs]; omega)]
        omega
      omega
    have hbound := norm_intervalSum_le (fun t => plaquetteCurl f (legPoint g h j t) i j) (g j) (h j) hM
      (fun t ht1 ht2 => ?_)
    · refine hbound.trans (mul_le_mul_of_nonneg_right ?_ hM)
      have := hdist j
      exact_mod_cast this
    · set w := legPoint g h j t with hw
      have hwi : w i = h i := by
        have hne : i ≠ j := ne_of_lt hij
        have hlt : i.val < j.val := hij
        simp [hw, legPoint, splice, hne, Function.update_of_ne, hlt]
      have hwj : w j = t := by simp [hw, legPoint]
      have hwl : ∀ l, l ≠ j → w l = h l ∨ w l = g l := by
        intro l hl
        simp only [hw, legPoint, splice, Function.update_of_ne hl]
        split_ifs
        · exact Or.inl rfl
        · exact Or.inr rfl
      have ht3 : min (g j) (h j) ≤ t ∧ t + 1 ≤ max (g j) (h j) := ⟨ht1, ht2⟩
      have hgj := abs_le.mp (hgb j)
      have hhj := abs_le.mp (hhb j)
      have hmin : -(2 * (R : ℤ)) ≤ t := le_trans (le_min hgj.1 hhj.1) ht1
      have hmax : t + 1 ≤ 2 * (R : ℤ) := le_trans ht2 (max_le hgj.2 hhj.2)
      have hne : i ≠ j := ne_of_lt hij
      have h0 : ∀ l, |w l| ≤ 2 * (R : ℤ) := by
        intro l
        by_cases hl : l = j
        · subst hl
          rw [hwj, abs_le]
          constructor <;> omega
        · rcases hwl l hl with e | e
          · rw [e]
            exact hhb l
          · rw [e]
            exact hgb l
      have hI : ∀ l, |(w + basisVec i) l| ≤ 2 * (R : ℤ) := by
        intro l
        by_cases hl : l = i
        · subst hl
          have := hib l
          simpa [hwi] using this
        · simpa [basisVec, hl] using h0 l
      have hJ : ∀ l, |(w + basisVec j) l| ≤ 2 * (R : ℤ) := by
        intro l
        by_cases hl : l = j
        · subst hl
          have e : (w + basisVec l) l = t + 1 := by simp [basisVec, hwj]
          rw [e, abs_le]
          constructor <;> omega
        · simpa [basisVec, hl] using h0 l
      have hIJ : ∀ l, |(w + basisVec i + basisVec j) l| ≤ 2 * (R : ℤ) := by
        intro l
        by_cases hl : l = j
        · subst hl
          have e : (w + basisVec i + basisVec l) l = t + 1 := by simp [basisVec, hwj, hne.symm]
          rw [e, abs_le]
          constructor <;> omega
        · simpa [basisVec, hl] using hI l
      have hmem : (siteAt o w, i, j) ∈ plaquettesIn S := by
        refine mem_plaquettesIn.mpr ⟨hij, fun z hz => ?_⟩
        simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact siteAt_mem_supBall hn h0
        · rw [← siteAt_add_basisVec]
          exact siteAt_mem_supBall hn hI
        · rw [← siteAt_add_basisVec]
          exact siteAt_mem_supBall hn hJ
        · rw [← siteAt_add_basisVec, ← siteAt_add_basisVec]
          exact siteAt_mem_supBall hn hIJ
      have hclose : supDist (siteAt o w) y ≤ d := by
        have e : siteAt o g = y := siteAt_coords o y
        rw [← e]
        refine supDist_siteAt_le hd2 fun l => ?_
        by_cases hl : l = j
        · subst hl
          rw [hwj]
          have a := abs_le.mp (hdist l)
          rw [abs_le]
          rcases le_total (g l) (h l) with hle | hle
          · rw [min_eq_left hle] at ht1
            rw [max_eq_right hle] at ht2
            constructor <;> omega
          · rw [min_eq_right hle] at ht1
            rw [max_eq_left hle] at ht2
            constructor <;> omega
        · rcases hwl l hl with e' | e'
          · rw [e']
            exact hdist l
          · rw [e']
            simp
      rw [hf, plaquetteCurl_siteAt]
      exact hcurl _ hmem hclose
end Gauge
theorem axialGaugeCurlBound : axialGaugeCurlBoundStatement := fun _ _ _ hR hn _ _ hy v => exists_axial_gauge hR hn hy v
end AxialGauge
end YangMills.Construction
end

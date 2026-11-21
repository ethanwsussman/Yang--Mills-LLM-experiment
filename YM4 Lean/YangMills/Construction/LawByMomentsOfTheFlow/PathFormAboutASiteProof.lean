import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ResponseInTheExpansion.RestAtACurvatureProof
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import YangMills.Construction.LawByMomentsOfTheFlow.PathFormAboutASite
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction
open TorusFields WeightedResponses
namespace PathForms
namespace Offsets
private def prim (f : ℤ → ℝ) : ℤ → ℝ
  | Int.ofNat m => ∑ s ∈ Finset.range m, f s
  | Int.negSucc m => - ∑ s ∈ Finset.range (m + 1), f (-1 - s)
private theorem prim_zero (f : ℤ → ℝ) : prim f 0 = 0 := by
  show prim f (Int.ofNat 0) = 0
  simp [prim]
private theorem prim_succ (f : ℤ → ℝ) (t : ℤ) : prim f (t + 1) = prim f t + f t := by
  rcases t with m | m
  · show prim f (Int.ofNat (m + 1)) = prim f (Int.ofNat m) + f (Int.ofNat m)
    simp [prim, Finset.sum_range_succ]
  · rcases m with _ | m
    · have e : Int.negSucc 0 + 1 = Int.ofNat 0 := rfl
      have e2 : Int.negSucc 0 = -1 - ((0 : ℕ) : ℤ) := rfl
      rw [e]
      simp only [prim, Finset.range_zero, Finset.sum_empty, Finset.range_one, Finset.sum_singleton]
      rw [e2]
      simp
    · have e : Int.negSucc (m + 1) + 1 = Int.negSucc m := rfl
      have e2 : Int.negSucc (m + 1) = -1 - ((m + 1 : ℕ) : ℤ) := by
        rw [Int.negSucc_eq]
        push_cast
        ring
      rw [e]
      simp only [prim]
      rw [Finset.sum_range_succ (n := m + 1), e2]
      ring
private theorem prim_pred (f : ℤ → ℝ) (t : ℤ) : prim f (t - 1) = prim f t - f (t - 1) := by
  have h := prim_succ f (t - 1)
  rw [sub_add_cancel] at h
  linarith
private theorem prim_sub (f g : ℤ → ℝ) (t : ℤ) : prim (fun s => f s - g s) t = prim f t - prim g t := by
  induction t using Int.induction_on with
  | zero => simp [prim_zero]
  | succ i ih => rw [prim_succ, prim_succ f, prim_succ g, ih]; ring
  | pred i ih => rw [prim_pred, prim_pred f, prim_pred g, ih]; ring
private theorem prim_diff (h : ℤ → ℝ) (t : ℤ) : prim (fun s => h (s + 1) - h s) t = h t - h 0 := by
  induction t using Int.induction_on with
  | zero => simp [prim_zero]
  | succ i ih => rw [prim_succ, ih]; ring
  | pred i ih =>
    rw [prim_pred, ih]
    simp only [sub_add_cancel]
    ring
variable {n : ℕ} [NeZero n]
private def siteAt (Y : TorusSite n) (v : Fin 4 → ℤ) : TorusSite n := fun i => Y i + ((v i : ℤ) : ZMod n)
private def unitOff (i : Fin 4) : Fin 4 → ℤ := Pi.single i 1
private def periodOff (n : ℕ) (i : Fin 4) : Fin 4 → ℤ := Pi.single i (n : ℤ)
private theorem unitOff_ne {i j : Fin 4} (h : j ≠ i) : unitOff i j = 0 := by simp [unitOff, Pi.single_apply, h]
private theorem unitOff_self (i : Fin 4) : unitOff i i = 1 := by simp [unitOff]
private theorem periodOff_ne {i j : Fin 4} (h : j ≠ i) : periodOff n i j = 0 := by
  simp [periodOff, Pi.single_apply, h]
private theorem periodOff_self (i : Fin 4) : periodOff n i i = n := by simp [periodOff]
private theorem siteAt_add (Y : TorusSite n) (v : Fin 4 → ℤ) (i : Fin 4) :
    siteAt Y (v + unitOff i) = siteAt Y v + unitStep n i := by
  funext j
  by_cases h : j = i
  · subst h
    simp [siteAt, unitStep, unitOff, add_assoc]
  · simp [siteAt, unitStep, unitOff, Pi.single_apply, h]
private theorem siteAt_period (Y : TorusSite n) (v : Fin 4 → ℤ) (i : Fin 4) :
    siteAt Y (v - periodOff n i) = siteAt Y v := by
  funext j
  by_cases h : j = i
  · subst h
    simp [siteAt, periodOff]
  · simp [siteAt, periodOff, Pi.single_apply, h]
private def offset (Y x : TorusSite n) : Fin 4 → ℤ := fun i => (x i - Y i).valMinAbs
private theorem siteAt_offset (Y x : TorusSite n) : siteAt Y (offset Y x) = x := by
  funext i
  simp [siteAt, offset, ZMod.coe_valMinAbs]
private def supNorm (v : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun i => (v i).natAbs
private theorem le_supNorm (v : Fin 4 → ℤ) (i : Fin 4) : (v i).natAbs ≤ supNorm v := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
private theorem supNorm_le {v : Fin 4 → ℤ} {B : ℕ} (h : ∀ i, (v i).natAbs ≤ B) : supNorm v ≤ B := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.offsetNorm_le <;> assumption
private theorem supNorm_offset (Y x : TorusSite n) : supNorm (offset Y x) = supDist x Y := rfl
private theorem natAbs_valMinAbs_intCast_le (k : ℤ) : ((k : ZMod n).valMinAbs).natAbs ≤ k.natAbs := by apply _root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le <;> assumption
private theorem supDist_siteAt_le (Y : TorusSite n) (v : Fin 4 → ℤ) : supDist (siteAt Y v) Y ≤ supNorm v := by
  unfold supDist
  refine Finset.sup_le fun i _ => ?_
  have e : siteAt Y v i - Y i = ((v i : ℤ) : ZMod n) := by simp [siteAt]
  rw [e]
  exact (natAbs_valMinAbs_intCast_le (v i)).trans (le_supNorm v i)
private theorem offset_add_unitStep (Y x : TorusSite n) (i : Fin 4) :
    offset Y (x + unitStep n i) = offset Y x + unitOff i -
      (if (x i - Y i).valMinAbs = ((n / 2 : ℕ) : ℤ) then periodOff n i else 0) := by
  funext j
  by_cases h : j = i
  · subst h
    have hM := ZMod.valMinAbs_mem_Ioc (x j - Y j)
    have e1 : x j + unitStep n j j - Y j = (x j - Y j) + 1 := by simp [unitStep]; ring
    have e2 : ((x j - Y j).valMinAbs : ZMod n) = x j - Y j := ZMod.coe_valMinAbs _
    set m := (x j - Y j).valMinAbs with hmdef
    simp only [offset, Pi.sub_apply, Pi.add_apply, unitOff_self, e1]
    rw [← hmdef]
    split_ifs with hc
    · rw [ZMod.valMinAbs_spec]
      simp only [periodOff_self]
      refine ⟨?_, ?_⟩
      · rw [← e2]
        push_cast
        simp
      · obtain ⟨h1, h2⟩ := hM
        constructor <;> omega
    · rw [ZMod.valMinAbs_spec]
      simp only [Pi.zero_apply, sub_zero]
      refine ⟨?_, ?_⟩
      · rw [← e2]
        push_cast
        simp
      · obtain ⟨h1, h2⟩ := hM
        constructor <;> omega
  · have e1 : (x + unitStep n i) j = x j := by simp [unitStep, Pi.single_apply, h]
    simp only [offset, Pi.sub_apply, Pi.add_apply, e1, unitOff_ne h]
    split_ifs
    · simp [periodOff_ne h]
    · simp
private def tailOff (k : ℕ) (v : Fin 4 → ℤ) : Fin 4 → ℤ := fun j => if (j : ℕ) < k then 0 else v j
private def legPoint (k : Fin 4) (v : Fin 4 → ℤ) (s : ℤ) : Fin 4 → ℤ := Function.update (tailOff k v) k s
private theorem legPoint_add_of_lt {k i : Fin 4} (h : k < i) (v : Fin 4 → ℤ) (s : ℤ) :
    legPoint k (v + unitOff i) s = legPoint k v s + unitOff i := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp [legPoint, unitOff_ne h.ne]
  · have hji : (j : ℕ) < k → j ≠ i := by
      intro h1 h2
      subst h2
      have := Fin.lt_def.mp h
      omega
    simp only [legPoint, Function.update_of_ne hj, tailOff, Pi.add_apply]
    split_ifs with h1
    · simp [unitOff_ne (hji h1)]
    · rfl
private theorem legPoint_add_of_gt {k i : Fin 4} (h : i < k) (v : Fin 4 → ℤ) (s : ℤ) :
    legPoint k (v + unitOff i) s = legPoint k v s := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp [legPoint]
  · simp only [legPoint, Function.update_of_ne hj, tailOff, Pi.add_apply]
    split_ifs with h1
    · rfl
    · have : j ≠ i := by
        intro h2
        subst h2
        exact h1 (Fin.lt_def.mp h)
      simp [unitOff_ne this]
private theorem legPoint_add_self (i : Fin 4) (v : Fin 4 → ℤ) (s : ℤ) :
    legPoint i (v + unitOff i) s = legPoint i v s := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [legPoint]
  · simp [legPoint, Function.update_of_ne hj, tailOff, unitOff_ne hj]
private theorem legPoint_succ (k : Fin 4) (v : Fin 4 → ℤ) (s : ℤ) :
    legPoint k v (s + 1) = legPoint k v s + unitOff k := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp [legPoint, unitOff_self]
  · simp [legPoint, Function.update_of_ne hj, unitOff_ne hj]
private theorem legPoint_self (k : Fin 4) (v : Fin 4 → ℤ) : legPoint k v (v k) = tailOff k v := by
  have e : tailOff k v k = v k := by simp [tailOff]
  rw [legPoint, ← e, Function.update_eq_self]
private theorem legPoint_zero (k : Fin 4) (v : Fin 4 → ℤ) : legPoint k v 0 = tailOff (k + 1) v := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp [legPoint, tailOff]
  · have : (j : ℕ) ≠ k := fun h => hj (Fin.ext h)
    simp only [legPoint, Function.update_of_ne hj, tailOff]
    by_cases h1 : (j : ℕ) < k
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]
private theorem supNorm_legPoint_le (k : Fin 4) (v : Fin 4 → ℤ) {s : ℤ} (hs : s.natAbs ≤ (v k).natAbs) :
    supNorm (legPoint k v s) ≤ supNorm v := by
  refine supNorm_le fun j => ?_
  by_cases hj : j = k
  · subst hj
    simpa [legPoint] using hs.trans (le_supNorm v j)
  · simp only [legPoint, Function.update_of_ne hj, tailOff]
    split_ifs
    · simp
    · exact le_supNorm v j
private def legSum (Y : TorusSite n) (A : TorusBond n → ℝ) (k : Fin 4) (v : Fin 4 → ℤ) : ℝ :=
  prim (fun s => A (siteAt Y (legPoint k v s), k)) (v k)
private def pathSum (Y : TorusSite n) (A : TorusBond n → ℝ) (v : Fin 4 → ℤ) : ℝ := ∑ k, legSum Y A k v
private def gradDefect (Y : TorusSite n) (A : TorusBond n → ℝ) (v : Fin 4 → ℤ) (i : Fin 4) : ℝ :=
  A (siteAt Y v, i) - (pathSum Y A (v + unitOff i) - pathSum Y A v)
private def stripCurl (Y : TorusSite n) (A : TorusBond n → ℝ) (v : Fin 4 → ℤ) (k i : Fin 4) : ℝ :=
  prim (fun s => curl A (siteAt Y (legPoint k v s), k, i)) (v k)
private theorem legSum_of_gt (Y : TorusSite n) (A : TorusBond n → ℝ) {k i : Fin 4} (h : i < k) (v : Fin 4 → ℤ) :
    legSum Y A k (v + unitOff i) = legSum Y A k v := by
  have e : (v + unitOff i) k = v k := by simp [unitOff_ne h.ne']
  simp only [legSum, legPoint_add_of_gt h, e]
private theorem legSum_self (Y : TorusSite n) (A : TorusBond n → ℝ) (i : Fin 4) (v : Fin 4 → ℤ) :
    legSum Y A i (v + unitOff i) = legSum Y A i v + A (siteAt Y (tailOff i v), i) := by
  have e : (v + unitOff i) i = v i + 1 := by simp [unitOff_self]
  simp only [legSum, legPoint_add_self, e]
  rw [prim_succ, legPoint_self]
private theorem legSum_of_lt (Y : TorusSite n) (A : TorusBond n → ℝ) {k i : Fin 4} (h : k < i) (v : Fin 4 → ℤ) :
    legSum Y A k (v + unitOff i) - legSum Y A k v =
      A (siteAt Y (tailOff k v), i) - A (siteAt Y (tailOff (k + 1) v), i) - stripCurl Y A v k i := by
  have e : (v + unitOff i) k = v k := by simp [unitOff_ne h.ne]
  have hh := prim_diff (fun s => A (siteAt Y (legPoint k v s), i)) (v k)
  simp only [legSum, stripCurl, legPoint_add_of_lt h, e]
  rw [← prim_sub]
  have e3 : (fun s => A (siteAt Y (legPoint k v s + unitOff i), k) - A (siteAt Y (legPoint k v s), k)) =
      fun s => (A (siteAt Y (legPoint k v (s + 1)), i) - A (siteAt Y (legPoint k v s), i)) -
        curl A (siteAt Y (legPoint k v s), k, i) := by
    funext s
    simp only [curl, legPoint_succ, siteAt_add]
    ring
  rw [e3, prim_sub, hh, legPoint_self, legPoint_zero]
private theorem sum_fin_four_telescope (g : ℕ → ℝ) (S : Fin 4 → ℝ) (i : Fin 4) :
    ∑ k : Fin 4, (if k < i then g k - g (k + 1) - S k else if k = i then g k else 0) =
      g 0 - ∑ k : Fin 4, if k < i then S k else 0 := by
  fin_cases i <;> simp [Fin.sum_univ_four] <;> ring
private theorem tailOff_zero (v : Fin 4 → ℤ) : tailOff 0 v = v := by
  funext j
  simp [tailOff]
private theorem gradDefect_eq (Y : TorusSite n) (A : TorusBond n → ℝ) (v : Fin 4 → ℤ) (i : Fin 4) :
    gradDefect Y A v i = ∑ k : Fin 4, if k < i then stripCurl Y A v k i else 0 := by
  have h1 : pathSum Y A (v + unitOff i) - pathSum Y A v = ∑ k : Fin 4,
      (if k < i then A (siteAt Y (tailOff k v), i) - A (siteAt Y (tailOff (k + 1) v), i) - stripCurl Y A v k i
        else if k = i then A (siteAt Y (tailOff k v), i) else 0) := by
    rw [pathSum, pathSum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with h2 h3
    · exact legSum_of_lt Y A h2 v
    · subst h3
      rw [legSum_self]
      ring
    · have : i < k := by
        rcases lt_trichotomy k i with h | h | h
        · exact absurd h h2
        · exact absurd h h3
        · exact h
      rw [legSum_of_gt Y A this]
      ring
  rw [gradDefect, h1, sum_fin_four_telescope (fun m => A (siteAt Y (tailOff m v), i))
    (fun k => stripCurl Y A v k i) i, tailOff_zero]
  ring
private def CurlRep (Y : TorusSite n) (K : ℝ) (R : ℕ) (f : (TorusBond n → ℝ) → ℝ) : Prop :=
  ∃ a : OrientedPlaquette n → ℝ, (∀ A, f A = ∑ p, a p * curl A p.1) ∧ ∑ p, |a p| ≤ K ∧
    ∀ p, a p ≠ 0 → supDist p.1.1 Y ≤ R
private theorem CurlRep.mono {Y : TorusSite n} {K K' : ℝ} {R R' : ℕ} {f : (TorusBond n → ℝ) → ℝ}
    (h : CurlRep Y K R f) (hK : K ≤ K') (hR : R ≤ R') : CurlRep Y K' R' f := by
  obtain ⟨a, h1, h2, h3⟩ := h
  exact ⟨a, h1, h2.trans hK, fun p hp => (h3 p hp).trans hR⟩
private theorem CurlRep.congr {Y : TorusSite n} {K : ℝ} {R : ℕ} {f g : (TorusBond n → ℝ) → ℝ}
    (h : CurlRep Y K R f) (e : ∀ A, g A = f A) : CurlRep Y K R g := by
  obtain ⟨a, h1, h2, h3⟩ := h
  exact ⟨a, fun A => (e A).trans (h1 A), h2, h3⟩
private theorem CurlRep.zero (Y : TorusSite n) (R : ℕ) : CurlRep Y 0 R fun _ => 0 :=
  ⟨0, fun A => by simp, by simp, fun p hp => absurd rfl hp⟩
private theorem CurlRep.add {Y : TorusSite n} {K K' : ℝ} {R : ℕ} {f g : (TorusBond n → ℝ) → ℝ}
    (hf : CurlRep Y K R f) (hg : CurlRep Y K' R g) : CurlRep Y (K + K') R fun A => f A + g A := by
  obtain ⟨a, h1, h2, h3⟩ := hf
  obtain ⟨b, k1, k2, k3⟩ := hg
  refine ⟨a + b, fun A => ?_, ?_, fun p hp => ?_⟩
  · show f A + g A = _
    rw [h1, k1, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by simp [add_mul]
  · calc ∑ p, |(a + b) p| ≤ ∑ p, (|a p| + |b p|) := Finset.sum_le_sum fun p _ => abs_add_le _ _
      _ = ∑ p, |a p| + ∑ p, |b p| := Finset.sum_add_distrib
      _ ≤ K + K' := add_le_add h2 k2
  · by_cases h : a p = 0
    · have : b p ≠ 0 := fun h' => hp (by simp [h, h'])
      exact k3 p this
    · exact h3 p h
private theorem CurlRep.neg {Y : TorusSite n} {K : ℝ} {R : ℕ} {f : (TorusBond n → ℝ) → ℝ}
    (hf : CurlRep Y K R f) : CurlRep Y K R fun A => - f A := by
  obtain ⟨a, h1, h2, h3⟩ := hf
  refine ⟨-a, fun A => ?_, ?_, fun p hp => h3 p fun h => hp (by simp [h])⟩
  · show - f A = _
    rw [h1, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ => by simp
  · simpa using h2
private theorem CurlRep.sub {Y : TorusSite n} {K K' : ℝ} {R : ℕ} {f g : (TorusBond n → ℝ) → ℝ}
    (hf : CurlRep Y K R f) (hg : CurlRep Y K' R g) : CurlRep Y (K + K') R fun A => f A - g A :=
  (hf.add hg.neg).congr fun A => sub_eq_add_neg _ _
private theorem CurlRep.single (Y x : TorusSite n) {k i : Fin 4} (h : k < i) {R : ℕ} (hR : supDist x Y ≤ R) :
    CurlRep Y 1 R fun A => curl A (x, k, i) := by
  classical
  let P : OrientedPlaquette n := ⟨(x, k, i), h⟩
  refine ⟨fun p => if p = P then 1 else 0, fun A => ?_, ?_, fun p hp => ?_⟩
  · simp [P]
  · have : ∑ p, |(if p = P then (1 : ℝ) else 0)| = 1 := by
      rw [Finset.sum_eq_single P]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    exact this.le
  · have : p = P := by
      by_contra hne
      exact hp (if_neg hne)
    subst this
    exact hR
private theorem CurlRep.primitive {Y : TorusSite n} {K : ℝ} {R : ℕ} (hK : 0 ≤ K)
    (f : (TorusBond n → ℝ) → ℤ → ℝ) (t : ℤ)
    (h : ∀ s : ℤ, s.natAbs ≤ t.natAbs → CurlRep Y K R fun A => f A s) :
    CurlRep Y ((t.natAbs : ℝ) * K) R fun A => prim (f A) t := by
  induction t using Int.induction_on with
  | zero =>
    simp only [Int.natAbs_zero, Nat.cast_zero, zero_mul]
    exact (CurlRep.zero Y R).congr fun A => prim_zero _
  | succ i ih =>
    have e : ((i : ℤ) + 1).natAbs = i + 1 := by omega
    have h1 := ih fun s hs => h s (by omega)
    have h2 := h (i : ℤ) (by omega)
    have h3 := (h1.add h2).congr (g := fun A => prim (f A) ((i : ℤ) + 1)) fun A => prim_succ _ _
    refine h3.mono ?_ le_rfl
    rw [e]
    have e2 : (((i : ℤ)).natAbs : ℝ) = i := by simp
    rw [e2]
    push_cast
    linarith
  | pred i ih =>
    have e : (-(i : ℤ) - 1).natAbs = i + 1 := by omega
    have h1 := ih fun s hs => h s (by omega)
    have h2 := h (-(i : ℤ) - 1) le_rfl
    have h3 := (h1.sub h2).congr (g := fun A => prim (f A) (-(i : ℤ) - 1)) fun A => prim_pred _ _
    refine h3.mono ?_ le_rfl
    rw [e]
    have e2 : ((-(i : ℤ)).natAbs : ℝ) = i := by simp
    rw [e2]
    push_cast
    linarith
private theorem curlRep_stripCurl (Y : TorusSite n) (v : Fin 4 → ℤ) {k i : Fin 4} (h : k < i) :
    CurlRep Y (supNorm v : ℝ) (supNorm v) fun A => stripCurl Y A v k i := by
  have h1 := CurlRep.primitive (Y := Y) (K := 1) (R := supNorm v) zero_le_one
    (fun A s => curl A (siteAt Y (legPoint k v s), k, i)) (v k) fun s hs =>
      CurlRep.single Y _ h ((supDist_siteAt_le Y _).trans (supNorm_legPoint_le k v hs))
  refine h1.mono ?_ le_rfl
  rw [mul_one]
  exact_mod_cast le_supNorm v k
private theorem curlRep_gradDefect (Y : TorusSite n) (v : Fin 4 → ℤ) (i : Fin 4) :
    CurlRep Y (4 * (supNorm v : ℝ)) (supNorm v) fun A => gradDefect Y A v i := by
  have hk : ∀ k : Fin 4, CurlRep Y (supNorm v : ℝ) (supNorm v)
      fun A => if k < i then stripCurl Y A v k i else 0 := by
    intro k
    by_cases h : k < i
    · simpa [h] using curlRep_stripCurl Y v h
    · simp only [h, if_false]
      exact (CurlRep.zero Y _).mono (Nat.cast_nonneg _) le_rfl
  have h4 := (((hk 0).add (hk 1)).add (hk 2)).add (hk 3)
  refine (h4.congr fun A => ?_).mono (by linarith) le_rfl
  rw [gradDefect_eq, Fin.sum_univ_four]
private def periodJump (Y : TorusSite n) (A : TorusBond n → ℝ) (i : Fin 4) (w : Fin 4 → ℤ) : ℝ :=
  pathSum Y A w - pathSum Y A (w - periodOff n i)
private theorem periodJump_step (Y : TorusSite n) (A : TorusBond n → ℝ) (i j : Fin 4) (w : Fin 4 → ℤ) :
    periodJump Y A i (w + unitOff j) - periodJump Y A i w =
      gradDefect Y A (w - periodOff n i) j - gradDefect Y A w j := by
  have e : w + unitOff j - periodOff n i = w - periodOff n i + unitOff j := by abel
  simp only [periodJump, gradDefect, siteAt_period, e]
  ring
private theorem update_add_one (w : Fin 4 → ℤ) (j : Fin 4) (s : ℤ) :
    Function.update w j (s + 1) = Function.update w j s + unitOff j := by apply _root_.YangMills.DeltaSharedProofs.p502038 <;> assumption
private theorem periodJump_sub_update (Y : TorusSite n) (A : TorusBond n → ℝ) (i j : Fin 4) (w : Fin 4 → ℤ) :
    periodJump Y A i w - periodJump Y A i (Function.update w j 0) =
      prim (fun s => gradDefect Y A (Function.update w j s - periodOff n i) j -
        gradDefect Y A (Function.update w j s) j) (w j) := by
  have h := prim_diff (fun s => periodJump Y A i (Function.update w j s)) (w j)
  have e : (fun s => periodJump Y A i (Function.update w j (s + 1)) - periodJump Y A i (Function.update w j s)) =
      fun s => gradDefect Y A (Function.update w j s - periodOff n i) j - gradDefect Y A (Function.update w j s) j := by
    funext s
    rw [update_add_one, periodJump_step]
  rw [e] at h
  rw [h, Function.update_eq_self]
private theorem curlRep_periodJump_sub_update (Y : TorusSite n) (i j : Fin 4) (w : Fin 4 → ℤ) {B : ℕ}
    (hB : ∀ s : ℤ, s.natAbs ≤ (w j).natAbs →
      supNorm (Function.update w j s) ≤ B ∧ supNorm (Function.update w j s - periodOff n i) ≤ B) :
    CurlRep Y (((w j).natAbs : ℝ) * (8 * B)) B
      fun A => periodJump Y A i w - periodJump Y A i (Function.update w j 0) := by
  have hB0 : (0 : ℝ) ≤ 8 * B := by positivity
  have h := CurlRep.primitive (Y := Y) (K := 8 * B) (R := B) hB0
    (fun A s => gradDefect Y A (Function.update w j s - periodOff n i) j -
      gradDefect Y A (Function.update w j s) j) (w j)
    fun s hs => by
      obtain ⟨h1, h2⟩ := hB s hs
      have g1 := (curlRep_gradDefect Y (Function.update w j s - periodOff n i) j).mono (K' := 4 * B) (R' := B)
        (by have : (supNorm (Function.update w j s - periodOff n i) : ℝ) ≤ B := by exact_mod_cast h2
            linarith) h2
      have g2 := (curlRep_gradDefect Y (Function.update w j s) j).mono (K' := 4 * B) (R' := B)
        (by have : (supNorm (Function.update w j s) : ℝ) ≤ B := by exact_mod_cast h1
            linarith) h1
      exact (g1.sub g2).mono (by linarith) le_rfl
  exact h.congr fun A => periodJump_sub_update Y A i j w
private def pastTop (n : ℕ) (i : Fin 4) : Fin 4 → ℤ := Pi.single i (((n / 2 : ℕ) : ℤ) + 1)
private def zeroBelow (i : Fin 4) (m : ℕ) (w : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun j => if (j : ℕ) < m ∧ j ≠ i then 0 else w j
private theorem natAbs_zeroBelow_le (i : Fin 4) (m : ℕ) (w : Fin 4 → ℤ) (l : Fin 4) :
    (zeroBelow i m w l).natAbs ≤ (w l).natAbs := by
  simp only [zeroBelow]
  split_ifs <;> simp
private theorem curlRep_periodJump (Y : TorusSite n) (v : Fin 4 → ℤ) (i : Fin 4) (hv : v i = ((n / 2 : ℕ) : ℤ)) :
    CurlRep Y (32 * ((supNorm v : ℝ) + 1) ^ 2) (supNorm v + 1)
      fun A => periodJump Y A i (v + unitOff i) - periodJump Y A i (pastTop n i) := by
  set w := v + unitOff i with hw
  have hwi : w i = ((n / 2 : ℕ) : ℤ) + 1 := by simp [hw, unitOff_self, hv]
  have hvi := le_supNorm v i
  rw [hv] at hvi
  have hwB : ∀ l, (w l).natAbs ≤ supNorm v + 1 := by
    intro l
    by_cases hl : l = i
    · subst hl
      rw [hwi]
      omega
    · have : w l = v l := by simp [hw, unitOff_ne hl]
      rw [this]
      exact (le_supNorm v l).trans (Nat.le_succ _)
  have hstep : ∀ (m : ℕ), m < 4 → CurlRep Y (8 * ((supNorm v : ℝ) + 1) ^ 2) (supNorm v + 1)
      fun A => periodJump Y A i (zeroBelow i m w) - periodJump Y A i (zeroBelow i (m + 1) w) := by
    intro m hm
    let j : Fin 4 := ⟨m, hm⟩
    by_cases hj : j = i
    · have e : zeroBelow i (m + 1) w = zeroBelow i m w := by
        funext l
        simp only [zeroBelow]
        by_cases hl : l = i
        · simp [hl]
        · have : (l : ℕ) ≠ m := fun h => hl (by rw [← hj]; exact Fin.ext h)
          have e2 : ((l : ℕ) < m + 1) ↔ (l : ℕ) < m := by omega
          simp only [e2]
      rw [e]
      exact ((CurlRep.zero Y _).congr fun A => sub_self _).mono (by positivity) le_rfl
    · have e : zeroBelow i (m + 1) w = Function.update (zeroBelow i m w) j 0 := by
        funext l
        by_cases hl : l = j
        · subst hl
          simp only [Function.update_self, zeroBelow]
          rw [if_pos]
          exact ⟨by simp [j], hj⟩
        · have hl2 : (l : ℕ) ≠ m := fun h => hl (Fin.ext h)
          rw [Function.update_of_ne hl]
          simp only [zeroBelow]
          have e2 : ((l : ℕ) < m + 1) ↔ (l : ℕ) < m := by omega
          simp only [e2]
      rw [e]
      have hup : ∀ s : ℤ, s.natAbs ≤ (zeroBelow i m w j).natAbs → ∀ l, l ≠ i ∨ True →
          ((Function.update (zeroBelow i m w) j s) l).natAbs ≤ supNorm v + 1 := by
        intro s hs l _
        by_cases hl : l = j
        · rw [hl]
          simpa using hs.trans ((natAbs_zeroBelow_le i m w j).trans (hwB j))
        · rw [Function.update_of_ne hl]
          exact (natAbs_zeroBelow_le i m w l).trans (hwB l)
      have hc := curlRep_periodJump_sub_update Y i j (zeroBelow i m w) (B := supNorm v + 1) fun s hs => by
        refine ⟨supNorm_le fun l => hup s hs l (Or.inr trivial), supNorm_le fun l => ?_⟩
        by_cases hl : l = i
        · subst hl
          have hlj : l ≠ j := fun h => hj h.symm
          have e3 : (Function.update (zeroBelow l m w) j s - periodOff n l) l = w l - n := by
            simp only [Pi.sub_apply, Function.update_of_ne hlj, periodOff_self]
            simp [zeroBelow]
          rw [e3, hwi]
          omega
        · have e3 : (Function.update (zeroBelow i m w) j s - periodOff n i) l =
              Function.update (zeroBelow i m w) j s l := by
            simp [periodOff_ne hl]
          rw [e3]
          exact hup s hs l (Or.inr trivial)
      refine hc.mono ?_ le_rfl
      have h1 : (((zeroBelow i m w j).natAbs : ℕ) : ℝ) ≤ (supNorm v : ℝ) + 1 := by
        exact_mod_cast (natAbs_zeroBelow_le i m w j).trans (hwB j)
      have h0 : (0 : ℝ) ≤ (supNorm v : ℝ) + 1 := by positivity
      push_cast
      nlinarith
  have e0 : zeroBelow i 0 w = w := by
    funext l
    simp [zeroBelow]
  have e4 : zeroBelow i 4 w = pastTop n i := by
    funext l
    by_cases hl : l = i
    · subst hl
      simp [zeroBelow, pastTop, hwi]
    · have : (l : ℕ) < 4 := l.isLt
      simp [zeroBelow, pastTop, hl, this, Pi.single_apply]
  have h4 := (((hstep 0 (by norm_num)).add (hstep 1 (by norm_num))).add (hstep 2 (by norm_num))).add
    (hstep 3 (by norm_num))
  refine (h4.congr fun A => ?_).mono (by linarith) le_rfl
  simp only [e0, e4, zero_add, Nat.reduceAdd]
  rw [e0] at *
  ring
private def crossing (Y : TorusSite n) (i : Fin 4) (c : TorusBond n) : ℝ :=
  if c.2 = i ∧ (c.1 i - Y i).valMinAbs = ((n / 2 : ℕ) : ℤ) then 1 else 0
private theorem crossing_of_ne (Y : TorusSite n) {i : Fin 4} {c : TorusBond n} (h : c.2 ≠ i) :
    crossing Y i c = 0 := by
  simp [crossing, h]
private theorem crossing_shift (Y x : TorusSite n) {i l : Fin 4} (h : l ≠ i) :
    crossing Y i (x + unitStep n l, i) = crossing Y i (x, i) := by
  have e : (x + unitStep n l) i = x i := by simp [unitStep, Pi.single_apply, h.symm]
  simp [crossing, e]
private theorem curl_crossing (Y : TorusSite n) (i : Fin 4) (x : TorusSite n) (j k : Fin 4) :
    crossing Y i (x, j) + crossing Y i (x + unitStep n j, k) - crossing Y i (x + unitStep n k, j) -
      crossing Y i (x, k) = 0 := by
  by_cases hj : j = i
  · by_cases hk : k = i
    · subst hj
      subst hk
      ring
    · subst hj
      rw [crossing_shift Y x hk, crossing_of_ne Y (c := (x + unitStep n j, k)) hk,
        crossing_of_ne Y (c := (x, k)) hk]
      ring
  · by_cases hk : k = i
    · subst hk
      rw [crossing_shift Y x hj, crossing_of_ne Y (c := (x, j)) hj,
        crossing_of_ne Y (c := (x + unitStep n k, j)) hj]
      ring
    · rw [crossing_of_ne Y (c := (x, j)) hj, crossing_of_ne Y (c := (x + unitStep n k, j)) hj,
        crossing_of_ne Y (c := (x, k)) hk, crossing_of_ne Y (c := (x + unitStep n j, k)) hk]
      ring
private def correctedForm (Y : TorusSite n) (A : TorusBond n → ℝ) (c : TorusBond n) : ℝ :=
  A c - (pathSum Y A (offset Y (c.1 + unitStep n c.2)) - pathSum Y A (offset Y c.1)) -
    ∑ i, periodJump Y A i (pastTop n i) * crossing Y i c
private theorem curl_correctedForm (Y : TorusSite n) (A : TorusBond n → ℝ) (p : TorusPlaquette n) :
    curl (correctedForm Y A) p = curl A p := by
  obtain ⟨x, j, k⟩ := p
  have e : x + unitStep n j + unitStep n k = x + unitStep n k + unitStep n j := add_right_comm _ _ _
  simp only [curl, correctedForm, e, Fin.sum_univ_four]
  linear_combination (-(periodJump Y A 0 (pastTop n 0))) * curl_crossing Y 0 x j k -
    (periodJump Y A 1 (pastTop n 1)) * curl_crossing Y 1 x j k -
    (periodJump Y A 2 (pastTop n 2)) * curl_crossing Y 2 x j k -
    (periodJump Y A 3 (pastTop n 3)) * curl_crossing Y 3 x j k
private theorem curlRep_correctedForm (Y : TorusSite n) (c : TorusBond n) :
    CurlRep Y (36 * (1 + (supDist c.1 Y : ℝ)) ^ 2) (supDist c.1 Y + 1) fun A => correctedForm Y A c := by
  obtain ⟨x, i⟩ := c
  have hx0 : siteAt Y (offset Y x) = x := siteAt_offset Y x
  have hd : (supNorm (offset Y x) : ℝ) = supDist x Y := by rw [supNorm_offset]
  show CurlRep Y (36 * (1 + (supDist x Y : ℝ)) ^ 2) (supDist x Y + 1) fun A => correctedForm Y A (x, i)
  by_cases hx : (x i - Y i).valMinAbs = ((n / 2 : ℕ) : ℤ)
  · have e1 : offset Y (x + unitStep n i) = offset Y x + unitOff i - periodOff n i := by
      rw [offset_add_unitStep, if_pos hx]
    have hs : ∀ A : TorusBond n → ℝ,
        ∑ l, periodJump Y A l (pastTop n l) * crossing Y l (x, i) = periodJump Y A i (pastTop n i) := by
      intro A
      rw [Finset.sum_eq_single i]
      · simp [crossing, hx]
      · intro b _ hb
        rw [crossing_of_ne Y (c := (x, i)) (Ne.symm hb), mul_zero]
      · simp
    have h1 := (curlRep_gradDefect Y (offset Y x) i).mono (K' := 4 * (supNorm (offset Y x) : ℝ))
      (R' := supNorm (offset Y x) + 1) le_rfl (Nat.le_succ _)
    have h2 := curlRep_periodJump Y (offset Y x) i hx
    refine ((h1.add h2).congr fun A => ?_).mono ?_ ?_
    · simp only [correctedForm]
      rw [hs A]
      simp only [e1, gradDefect, periodJump, hx0]
      ring
    · rw [hd]
      nlinarith
    · rw [supNorm_offset]
  · have e1 : offset Y (x + unitStep n i) = offset Y x + unitOff i := by
      rw [offset_add_unitStep, if_neg hx, sub_zero]
    have hs : ∀ A : TorusBond n → ℝ, ∑ l, periodJump Y A l (pastTop n l) * crossing Y l (x, i) = 0 := by
      intro A
      refine Finset.sum_eq_zero fun l _ => ?_
      have : crossing Y l (x, i) = 0 := by
        simp only [crossing]
        rw [if_neg]
        rintro ⟨h1, h2⟩
        have h1' : i = l := h1
        apply hx
        rw [h1']
        exact h2
      rw [this, mul_zero]
    refine ((curlRep_gradDefect Y (offset Y x) i).congr fun A => ?_).mono ?_ ?_
    · simp only [correctedForm]
      rw [hs A]
      simp only [e1, gradDefect, hx0]
      ring
    · rw [hd]
      nlinarith
    · rw [supNorm_offset]
      exact Nat.le_succ _
end Offsets
open Offsets in
theorem pathFormAboutSite : pathFormAboutSiteStatement := by
  refine ⟨36, by norm_num, fun n _ _ Y => ?_⟩
  have key := fun c : TorusBond n => curlRep_correctedForm Y c
  choose co h₁ h₂ h₃ using key
  refine ⟨co, h₂, fun c p h => h₃ c p h, fun A p => ?_⟩
  have e : (fun c => ∑ p' : OrientedPlaquette n, co c p' * curl A p'.1) = correctedForm Y A :=
    funext fun c => (h₁ c A).symm
  rw [e]
  exact curl_correctedForm Y A p
end PathForms
end YangMills.Construction
end

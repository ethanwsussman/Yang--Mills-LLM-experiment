import YangMills.Construction.ColdChainAtEveryLevel.LocalFormOfTheLinesProof
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.PeriodicOperators.NormOfTheSymbolProof
import YangMills.Construction.FormsOnATorus.AnalyticSumOfExponentials
import YangMills.Construction.FormsOnATorus.ColumnOfTheLimitFormProof
import YangMills.Construction.FormsOnATorus.DerivativesOfAnExponentialSum
import YangMills.Construction.FormsOnATorus.LimitFormIsSymmetric
import YangMills.Construction.FormsOnATorus.PropertiesOfTheSymbol
import YangMills.Construction.FormsOnATorus.SecondMomentOfTheLimitForm
import YangMills.Construction.FormsOnATorus.TrigonometryOfTheSymbol
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitForms
open Filter Topology
open YangMills.Construction.TorusFields (TorusIsometry)
open YangMills.Construction.ExponentialSums
private structure LimitFormData (cK c C : ℝ) (Q : IntBond → IntBond → ℝ) : Prop where
  invariant : ∀ (g : TorusIsometry) (b b' : IntBond),
    (bondImage g b).2 * (bondImage g b').2 * Q (bondImage g b).1 (bondImage g b').1 = Q b b'
  decay : ∀ b b', |Q b b'| ≤ C * Real.exp (-(c * bondSupDist b b'))
  gradFree : ∀ (b : IntBond) (f : (Fin 4 → ℤ) →₀ ℝ),
    HasSum (fun b' : IntBond => Q b b' * (f b'.1 - f (b'.1 + Pi.single b'.2 1))) 0
  lowerBound : ∀ (v : IntBond →₀ ℝ) (P : Finset ((Fin 4 → ℤ) × Fin 4 × Fin 4)), (∀ p ∈ P, p.2.1 < p.2.2) →
    2 * cK * ∑ p ∈ P, intCurl v p ^ 2 ≤ ∑ b ∈ v.support, ∑ b' ∈ v.support, v b * Q b b' * v b'
private def supNorm (z : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun l => (z l).natAbs
private lemma natAbs_le_supNorm (z : Fin 4 → ℤ) (l : Fin 4) : (z l).natAbs ≤ supNorm z := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
private lemma abs_le_supNorm (z : Fin 4 → ℤ) (l : Fin 4) : |(z l : ℝ)| ≤ supNorm z := by apply _root_.YangMills.Construction.BlockAverages.abs_coord_le_supNorm <;> assumption
private lemma supNorm_le_sum_abs (z : Fin 4 → ℤ) : (supNorm z : ℝ) ≤ ∑ l, |(z l : ℝ)| := by
  have h : supNorm z ≤ ∑ l, (z l).natAbs :=
    Finset.sup_le fun l _ => Finset.single_le_sum (f := fun l => (z l).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  have h2 : (supNorm z : ℝ) ≤ ((∑ l, (z l).natAbs : ℕ) : ℝ) := by exact_mod_cast h
  refine h2.trans (le_of_eq ?_)
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Nat.cast_natAbs, Int.cast_abs]
abbrev _root_.YangMills.DeltaSharedProofs.p500619 := @supNorm_le_sum_abs
private lemma supNorm_add_le (z v : Fin 4 → ℤ) : supNorm (z + v) ≤ supNorm z + supNorm v := by apply _root_.YangMills.Construction.LatticePaths.supNorm_add_le <;> assumption
private def expWeight (c : ℝ) (m : ℕ) (z : Fin 4 → ℤ) : ℝ :=
  Real.exp (-(c * supNorm z)) * (1 + (supNorm z : ℝ)) ^ m
private lemma summable_exp_mul_pow_nat {c : ℝ} (hc : 0 < c) (m : ℕ) :
    Summable fun n : ℕ => Real.exp (-(c * n)) * (1 + (n : ℝ)) ^ m := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul m hc)
  refine (h.mul_left (Real.exp c)).congr fun n => ?_
  push_cast
  have : Real.exp (-(c * n)) = Real.exp c * Real.exp (-c * (n + 1)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]; ring
private lemma summable_exp_mul_pow_int {c : ℝ} (hc : 0 < c) (m : ℕ) :
    Summable fun t : ℤ => Real.exp (-(c * |(t : ℝ)|)) * (1 + |(t : ℝ)|) ^ m := by
  refine Summable.of_nat_of_neg ?_ ?_
  · refine (summable_exp_mul_pow_nat hc m).congr fun n => ?_
    simp
  · refine (summable_exp_mul_pow_nat hc m).congr fun n => ?_
    simp
private lemma summable_prod_pi {f : ℤ → ℝ} (hf0 : ∀ t, 0 ≤ f t) (hf : Summable f) :
    ∀ n : ℕ, Summable fun z : Fin n → ℤ => ∏ l, f (z l)
  | 0 => by
    exact (hasSum_fintype _).summable
  | n + 1 => by
    have ih := summable_prod_pi hf0 hf n
    have h := Summable.mul_of_nonneg hf ih hf0 (fun z => Finset.prod_nonneg fun l _ => hf0 _)
    refine ((Fin.insertNthEquiv (fun _ => ℤ) 0).summable_iff).1 ?_
    refine h.congr fun x => ?_
    simp [Function.comp, Fin.prod_univ_succ]
private lemma summable_expWeight {c : ℝ} (hc : 0 < c) (m : ℕ) : Summable (expWeight c m) := by
  have hc4 : 0 < c / 4 := by positivity
  have hs := summable_prod_pi (f := fun t : ℤ => Real.exp (-(c / 4 * |(t : ℝ)|)) * (1 + |(t : ℝ)|) ^ m)
    (fun t => by positivity) (summable_exp_mul_pow_int hc4 m) 4
  refine Summable.of_nonneg_of_le (fun z => by unfold expWeight; positivity) (fun z => ?_) hs
  unfold expWeight
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_pow]
  have h1 : ∑ l, |(z l : ℝ)| ≤ 4 * supNorm z := by
    have : ∑ l : Fin 4, |(z l : ℝ)| ≤ ∑ _l : Fin 4, (supNorm z : ℝ) :=
      Finset.sum_le_sum fun l _ => abs_le_supNorm z l
    simpa using this
  have h2 : Real.exp (-(c * supNorm z)) ≤ Real.exp (∑ l, -(c / 4 * |(z l : ℝ)|)) := by
    apply Real.exp_le_exp.2
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
    nlinarith
  have h3 : (1 + (supNorm z : ℝ)) ≤ ∏ l, (1 + |(z l : ℝ)|) := by
    have h4 := supNorm_le_sum_abs z
    rw [Fin.sum_univ_four] at h4
    rw [Fin.prod_univ_four]
    have ha := abs_nonneg (z 0 : ℝ)
    have hb := abs_nonneg (z 1 : ℝ)
    have hc' := abs_nonneg (z 2 : ℝ)
    have hd := abs_nonneg (z 3 : ℝ)
    nlinarith [mul_nonneg ha hb, mul_nonneg ha hc', mul_nonneg ha hd, mul_nonneg hb hc', mul_nonneg hb hd,
      mul_nonneg hc' hd, mul_nonneg (mul_nonneg ha hb) hc', mul_nonneg (mul_nonneg ha hb) hd,
      mul_nonneg (mul_nonneg ha hc') hd, mul_nonneg (mul_nonneg hb hc') hd,
      mul_nonneg (mul_nonneg (mul_nonneg ha hb) hc') hd]
  have h5 : (1 + (supNorm z : ℝ)) ^ m ≤ (∏ l, (1 + |(z l : ℝ)|)) ^ m :=
    pow_le_pow_left₀ (by positivity) h3 m
  exact mul_le_mul h2 h5 (by positivity) (by positivity)
private def PolyGrowth (g : (Fin 4 → ℤ) → ℝ) : Prop :=
  ∃ (B : ℝ) (m : ℕ), ∀ z, |g z| ≤ B * (1 + (supNorm z : ℝ)) ^ m
private lemma one_le_one_add_supNorm (z : Fin 4 → ℤ) : (1 : ℝ) ≤ 1 + (supNorm z : ℝ) := by
  have : (0 : ℝ) ≤ supNorm z := by positivity
  linarith
private lemma PolyGrowth.const (a : ℝ) : PolyGrowth fun _ => a := ⟨|a|, 0, fun z => by simp⟩
private lemma PolyGrowth.coord (l : Fin 4) : PolyGrowth fun z => (z l : ℝ) :=
  ⟨1, 1, fun z => by have := abs_le_supNorm z l; simp only [pow_one, one_mul]; linarith⟩
private lemma PolyGrowth.add {f g : (Fin 4 → ℤ) → ℝ} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth fun z => f z + g z := by
  obtain ⟨B₁, m₁, h₁⟩ := hf
  obtain ⟨B₂, m₂, h₂⟩ := hg
  refine ⟨|B₁| + |B₂|, m₁ + m₂, fun z => ?_⟩
  have hs := one_le_one_add_supNorm z
  have e1 : (1 + (supNorm z : ℝ)) ^ m₁ ≤ (1 + (supNorm z : ℝ)) ^ (m₁ + m₂) :=
    pow_le_pow_right₀ hs (by omega)
  have e2 : (1 + (supNorm z : ℝ)) ^ m₂ ≤ (1 + (supNorm z : ℝ)) ^ (m₁ + m₂) :=
    pow_le_pow_right₀ hs (by omega)
  have p1 : (0 : ℝ) ≤ (1 + (supNorm z : ℝ)) ^ m₁ := by positivity
  have p2 : (0 : ℝ) ≤ (1 + (supNorm z : ℝ)) ^ m₂ := by positivity
  calc |f z + g z| ≤ |f z| + |g z| := abs_add_le _ _
    _ ≤ B₁ * (1 + (supNorm z : ℝ)) ^ m₁ + B₂ * (1 + (supNorm z : ℝ)) ^ m₂ := add_le_add (h₁ z) (h₂ z)
    _ ≤ |B₁| * (1 + (supNorm z : ℝ)) ^ (m₁ + m₂) + |B₂| * (1 + (supNorm z : ℝ)) ^ (m₁ + m₂) := by
        refine add_le_add ?_ ?_
        · exact (mul_le_mul_of_nonneg_right (le_abs_self _) p1).trans
            (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
        · exact (mul_le_mul_of_nonneg_right (le_abs_self _) p2).trans
            (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
    _ = _ := by ring
private lemma PolyGrowth.mul {f g : (Fin 4 → ℤ) → ℝ} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth fun z => f z * g z := by
  obtain ⟨B₁, m₁, h₁⟩ := hf
  obtain ⟨B₂, m₂, h₂⟩ := hg
  refine ⟨B₁ * B₂, m₁ + m₂, fun z => ?_⟩
  rw [abs_mul, pow_add]
  calc |f z| * |g z| ≤ (B₁ * (1 + (supNorm z : ℝ)) ^ m₁) * (B₂ * (1 + (supNorm z : ℝ)) ^ m₂) :=
        mul_le_mul (h₁ z) (h₂ z) (abs_nonneg _) ((abs_nonneg _).trans (h₁ z))
    _ = _ := by ring
private lemma PolyGrowth.sub {f g : (Fin 4 → ℤ) → ℝ} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth fun z => f z - g z := by
  have := hf.add ((PolyGrowth.const (-1)).mul hg)
  simpa [sub_eq_add_neg] using this
private lemma PolyGrowth.shift {g : (Fin 4 → ℤ) → ℝ} (hg : PolyGrowth g) (v : Fin 4 → ℤ) :
    PolyGrowth fun z => g (z + v) := by
  obtain ⟨B, m, h⟩ := hg
  refine ⟨|B| * (1 + (supNorm v : ℝ)) ^ m, m, fun z => ?_⟩
  have h1 : (1 + (supNorm (z + v) : ℝ)) ≤ (1 + (supNorm v : ℝ)) * (1 + (supNorm z : ℝ)) := by
    have : (supNorm (z + v) : ℝ) ≤ supNorm z + supNorm v := by exact_mod_cast supNorm_add_le z v
    have h0 : (0 : ℝ) ≤ (supNorm z : ℝ) * supNorm v := by positivity
    nlinarith
  have h2 : (1 + (supNorm (z + v) : ℝ)) ^ m ≤ ((1 + (supNorm v : ℝ)) * (1 + (supNorm z : ℝ))) ^ m :=
    pow_le_pow_left₀ (by positivity) h1 m
  calc |g (z + v)| ≤ B * (1 + (supNorm (z + v) : ℝ)) ^ m := h _
    _ ≤ |B| * (1 + (supNorm (z + v) : ℝ)) ^ m :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |B| * ((1 + (supNorm v : ℝ)) * (1 + (supNorm z : ℝ))) ^ m :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = _ := by rw [mul_pow]; ring
section Form
variable {cK c C : ℝ} {Q : IntBond → IntBond → ℝ}
private lemma bondSupDist_zero_left (i j : Fin 4) (z : Fin 4 → ℤ) :
    bondSupDist (0, i) (z, j) = supNorm z := by
  simp [bondSupDist, supNorm]
private lemma LimitFormData.abs_le (F : LimitFormData cK c C Q) (i j : Fin 4) (z : Fin 4 → ℤ) :
    |Q (0, i) (z, j)| ≤ C * Real.exp (-(c * supNorm z)) := by
  have := F.decay (0, i) (z, j)
  rwa [bondSupDist_zero_left] at this
private lemma LimitFormData.summable_mul (F : LimitFormData cK c C Q) (hc : 0 < c) (i j : Fin 4)
    {g : (Fin 4 → ℤ) → ℝ} (hg : PolyGrowth g) :
    Summable fun z => Q (0, i) (z, j) * g z := by
  obtain ⟨B, m, h⟩ := hg
  refine Summable.of_norm_bounded (((summable_expWeight hc m).mul_left (C * B))) fun z => ?_
  rw [Real.norm_eq_abs, abs_mul]
  have := mul_le_mul (F.abs_le i j z) (h z) (abs_nonneg _) ((abs_nonneg _).trans (F.abs_le i j z))
  refine this.trans (le_of_eq ?_)
  unfold expWeight; ring
end Form
section Moments
variable {cK c C : ℝ} {Q : IntBond → IntBond → ℝ}
private def midStep (i j : Fin 4) (z : Fin 4 → ℤ) (l : Fin 4) : ℝ :=
  (z l : ℝ) + (if l = j then 1 / 2 else 0) - (if l = i then 1 / 2 else 0)
private lemma midStep_self (i : Fin 4) (z : Fin 4 → ℤ) (l : Fin 4) : midStep i i z l = z l := by
  simp [midStep]
private lemma polyGrowth_midStep (i j l : Fin 4) : PolyGrowth fun z => midStep i j z l :=
  ((PolyGrowth.coord l).add (PolyGrowth.const _)).sub (PolyGrowth.const _)
private lemma abs_midStep_le (i j : Fin 4) (z : Fin 4 → ℤ) (l : Fin 4) :
    |midStep i j z l| ≤ 1 + (supNorm z : ℝ) := by
  have h := abs_le_supNorm z l
  unfold midStep
  have h1 : |(if l = j then (1 / 2 : ℝ) else 0)| ≤ 1 / 2 := by
    split_ifs <;> norm_num
  have h2 : |(if l = i then (1 / 2 : ℝ) else 0)| ≤ 1 / 2 := by
    split_ifs <;> norm_num
  calc _ ≤ |(z l : ℝ) + (if l = j then (1 / 2 : ℝ) else 0)| + |(if l = i then (1 / 2 : ℝ) else 0)| := abs_sub _ _
    _ ≤ |(z l : ℝ)| + |(if l = j then (1 / 2 : ℝ) else 0)| + |(if l = i then (1 / 2 : ℝ) else 0)| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith
private lemma bondImage_translation (x : Fin 4 → ℤ) (b : IntBond) :
    bondImage ⟨1, fun _ => 1, x, fun _ => Or.inl rfl⟩ b = ((b.1 + x, b.2), 1) := by
  rcases b with ⟨y, i⟩
  simp only [bondImage, if_true]
  congr 2
  · funext k; simp
private lemma LimitFormData.translate (F : LimitFormData cK c C Q) (x y : Fin 4 → ℤ) (i j : Fin 4) :
    Q (x, i) (y, j) = Q (0, i) (y - x, j) := by
  have h := F.invariant ⟨1, fun _ => 1, x, fun _ => Or.inl rfl⟩ (0, i) (y - x, j)
  rw [bondImage_translation, bondImage_translation] at h
  simpa using h
private def reflShift (s : Fin 4 → ℤ) (i : Fin 4) : Fin 4 → ℤ := fun l => if l = i ∧ s i ≠ 1 then -1 else 0
private def reflSign (s : Fin 4 → ℤ) (i : Fin 4) : ℝ := if s i = 1 then 1 else -1
private lemma reflSign_mul_self (s : Fin 4 → ℤ) (i : Fin 4) : reflSign s i * reflSign s i = 1 := by
  unfold reflSign; split_ifs <;> norm_num
private lemma bondImage_reflection (s : Fin 4 → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (x : Fin 4 → ℤ) (i : Fin 4) :
    bondImage ⟨1, s, 0, hs⟩ (x, i) = (((fun l => s l * x l) + reflShift s i, i), reflSign s i) := by
  simp only [bondImage, reflSign]
  have e1 : (1 : Equiv.Perm (Fin 4)).symm = 1 := rfl
  simp only [e1, Equiv.Perm.coe_one, id]
  by_cases h : s i = 1
  · simp only [h, if_true]
    congr 2
    funext k
    simp [reflShift, h]
  · simp only [h, if_false]
    congr 2
    funext k
    by_cases hk : k = i
    · subst hk; simp [reflShift, h, sub_eq_add_neg]
    · simp [reflShift, hk]
private def twoAxisReflectedSite (s : Fin 4 → ℤ) (i j : Fin 4) (z : Fin 4 → ℤ) : Fin 4 → ℤ :=
  (fun l => s l * z l) + reflShift s j - reflShift s i
private lemma LimitFormData.apply_rotatedSite (F : LimitFormData cK c C Q) (s : Fin 4 → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (i j : Fin 4) (z : Fin 4 → ℤ) :
    Q (0, i) (twoAxisReflectedSite s i j z, j) = reflSign s i * reflSign s j * Q (0, i) (z, j) := by
  have h := F.invariant ⟨1, s, 0, hs⟩ (0, i) (z, j)
  rw [bondImage_reflection, bondImage_reflection] at h
  simp only at h
  rw [F.translate] at h
  have e : ((fun l => s l * z l) + reflShift s j) - ((fun l => s l * (0 : Fin 4 → ℤ) l) + reflShift s i) =
      twoAxisReflectedSite s i j z := by
    funext l; simp [twoAxisReflectedSite]
  rw [e] at h
  rw [← h]
  have h1 := reflSign_mul_self s i
  have h2 := reflSign_mul_self s j
  calc Q (0, i) (twoAxisReflectedSite s i j z, j) =
        (reflSign s i * reflSign s i) * (reflSign s j * reflSign s j) * Q (0, i) (twoAxisReflectedSite s i j z, j) := by
        rw [h1, h2]; ring
    _ = _ := by ring
private lemma midStep_flipSite (s : Fin 4 → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (i j : Fin 4) (z : Fin 4 → ℤ)
    (l : Fin 4) : midStep i j (twoAxisReflectedSite s i j z) l = (s l : ℝ) * midStep i j z l := by
  unfold midStep twoAxisReflectedSite reflShift
  simp only [Pi.add_apply, Pi.sub_apply]
  push_cast
  by_cases hj : l = j <;> by_cases hi : l = i
  · subst hj; subst hi
    rcases hs l with a | a <;> simp [a]
  · subst hj
    rcases hs l with a | a <;> simp [a, hi] <;> ring
  · subst hi
    rcases hs l with a | a <;> simp [a, hj] <;> ring
  · simp [hj, hi]
private lemma reflectSite_involutive (s : Fin 4 → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (i j : Fin 4) :
    Function.Involutive (twoAxisReflectedSite s i j) := by
  intro z
  funext l
  have h : ∀ (w : Fin 4 → ℤ), ((midStep i j w l : ℝ)) =
      (w l : ℝ) + (if l = j then 1 / 2 else 0) - (if l = i then 1 / 2 else 0) :=
    fun _ => rfl
  have h1 := midStep_flipSite s hs i j (twoAxisReflectedSite s i j z) l
  have h2 := midStep_flipSite s hs i j z l
  rw [h2, ← mul_assoc] at h1
  have h3 : (s l : ℝ) * (s l : ℝ) = 1 := by
    rcases hs l with a | a <;> simp [a]
  rw [h3, one_mul, h, h] at h1
  have h4 : ((twoAxisReflectedSite s i j (twoAxisReflectedSite s i j z) l : ℤ) : ℝ) = (z l : ℝ) := by linarith
  exact_mod_cast h4
private def reflectSitePerm (s : Fin 4 → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (i j : Fin 4) :
    Equiv.Perm (Fin 4 → ℤ) :=
  (reflectSite_involutive s hs i j).toPerm
private lemma LimitFormData.tsum_reflectSite (F : LimitFormData cK c C Q) (s : Fin 4 → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (i j : Fin 4)
    (g : (Fin 4 → ℤ) → ℝ) (e : ℝ) (hg : ∀ z, g (twoAxisReflectedSite s i j z) = e * g z) :
    ∑' z, Q (0, i) (z, j) * g z = reflSign s i * reflSign s j * e * ∑' z, Q (0, i) (z, j) * g z := by
  conv_lhs => rw [← (reflectSitePerm s hs i j).tsum_eq (fun z => Q (0, i) (z, j) * g z)]
  rw [← tsum_mul_left]
  refine tsum_congr fun z => ?_
  show Q (0, i) (twoAxisReflectedSite s i j z, j) * g (twoAxisReflectedSite s i j z) = _
  rw [F.apply_rotatedSite s hs, hg]; ring
private lemma LimitFormData.divergence_free (F : LimitFormData cK c C Q) (i : Fin 4) (u : Fin 4 → ℤ) :
    ∑ j, (Q (0, i) (u, j) - Q (0, i) (u - Pi.single j 1, j)) = 0 := by
  classical
  have h := F.gradFree (0, i) (Finsupp.single u 1)
  let e1 : Fin 4 ↪ IntBond := ⟨fun j => (u, j), fun a b h => (Prod.ext_iff.1 h).2⟩
  let e2 : Fin 4 ↪ IntBond := ⟨fun j => (u - Pi.single j 1, j), fun a b h => (Prod.ext_iff.1 h).2⟩
  have h1 : HasSum (fun b' : IntBond => Q (0, i) b' * (Finsupp.single u (1 : ℝ)) b'.1)
      (∑ j, Q (0, i) (u, j)) := by
    have : HasSum (fun b' : IntBond => Q (0, i) b' * (Finsupp.single u (1 : ℝ)) b'.1)
        (∑ b ∈ Finset.univ.map e1, Q (0, i) b * (Finsupp.single u (1 : ℝ)) b.1) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => by
        rcases b with ⟨x, j⟩
        have : x ≠ u := fun hx => hb (Finset.mem_map.2 ⟨j, Finset.mem_univ j, by show (u, j) = (x, j); rw [hx]⟩)
        simp [this.symm])
    rw [Finset.sum_map] at this
    have e : ∀ j, Q (0, i) (e1 j) * (Finsupp.single u (1 : ℝ)) (e1 j).1 = Q (0, i) (u, j) := fun j => by
      show Q (0, i) (u, j) * (Finsupp.single u (1 : ℝ)) u = _
      simp
    simpa only [e] using this
  have h2 : HasSum (fun b' : IntBond => Q (0, i) b' * (Finsupp.single u (1 : ℝ)) (b'.1 + Pi.single b'.2 1))
      (∑ j, Q (0, i) (u - Pi.single j 1, j)) := by
    have : HasSum (fun b' : IntBond => Q (0, i) b' * (Finsupp.single u (1 : ℝ)) (b'.1 + Pi.single b'.2 1))
        (∑ b ∈ Finset.univ.map e2, Q (0, i) b * (Finsupp.single u (1 : ℝ)) (b.1 + Pi.single b.2 1)) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => by
        rcases b with ⟨x, j⟩
        have : x + Pi.single j 1 ≠ u := fun hx => hb (Finset.mem_map.2 ⟨j, Finset.mem_univ j, by
          show (u - Pi.single j 1, j) = (x, j)
          rw [← hx]; simp⟩)
        simp [this.symm])
    rw [Finset.sum_map] at this
    have e : ∀ j, Q (0, i) (e2 j) * (Finsupp.single u (1 : ℝ)) ((e2 j).1 + Pi.single (e2 j).2 1) =
        Q (0, i) (u - Pi.single j 1, j) := fun j => by
      show Q (0, i) (u - Pi.single j 1, j) * (Finsupp.single u (1 : ℝ)) (u - Pi.single j 1 + Pi.single j 1) = _
      simp
    simpa only [e] using this
  have h3 := (h1.sub h2).unique (by simpa [mul_sub] using h)
  rw [Finset.sum_sub_distrib]; exact h3
private lemma LimitFormData.sum_tsum_diff_eq_zero (F : LimitFormData cK c C Q) (hc : 0 < c) (i : Fin 4)
    {f : (Fin 4 → ℤ) → ℝ} (hf : PolyGrowth f) :
    ∑ j, ∑' u, Q (0, i) (u, j) * (f (u + Pi.single j 1) - f u) = 0 := by
  have s3 : ∀ j, Summable fun u => f u * Q (0, i) (u - Pi.single j 1, j) := by
    intro j
    refine ((Equiv.addRight (Pi.single j (1 : ℤ) : Fin 4 → ℤ)).summable_iff).1 ?_
    refine (F.summable_mul hc i j (hf.shift (Pi.single j 1))).congr fun u => ?_
    simp [mul_comm]
  have key : ∀ j, ∑' u, f u * (Q (0, i) (u, j) - Q (0, i) (u - Pi.single j 1, j)) =
      - ∑' u, Q (0, i) (u, j) * (f (u + Pi.single j 1) - f u) := by
    intro j
    have s1 : Summable fun u => Q (0, i) (u, j) * f u := F.summable_mul hc i j hf
    have s2 : Summable fun u => Q (0, i) (u, j) * f (u + Pi.single j 1) :=
      F.summable_mul hc i j (hf.shift _)
    have e3 : ∑' u, f u * Q (0, i) (u - Pi.single j 1, j) =
        ∑' u, Q (0, i) (u, j) * f (u + Pi.single j 1) := by
      refine ((Equiv.addRight (Pi.single j (1 : ℤ) : Fin 4 → ℤ)).tsum_eq
        (fun u => f u * Q (0, i) (u - Pi.single j 1, j))).symm.trans (tsum_congr fun u => ?_)
      simp [mul_comm]
    have e4 : ∑' u, f u * (Q (0, i) (u, j) - Q (0, i) (u - Pi.single j 1, j)) =
        ∑' u, Q (0, i) (u, j) * f u - ∑' u, f u * Q (0, i) (u - Pi.single j 1, j) := by
      rw [← s1.tsum_sub (s3 j)]
      exact tsum_congr fun u => by ring
    have e5 : ∑' u, Q (0, i) (u, j) * (f (u + Pi.single j 1) - f u) =
        ∑' u, Q (0, i) (u, j) * f (u + Pi.single j 1) - ∑' u, Q (0, i) (u, j) * f u := by
      rw [← s2.tsum_sub s1]
      exact tsum_congr fun u => by ring
    rw [e4, e5, e3]; ring
  have s : ∀ j ∈ (Finset.univ : Finset (Fin 4)),
      Summable fun u => f u * (Q (0, i) (u, j) - Q (0, i) (u - Pi.single j 1, j)) := by
    intro j _
    exact ((F.summable_mul hc i j hf).sub (s3 j)).congr fun u => by ring
  have h0 : ∑ j, ∑' u, f u * (Q (0, i) (u, j) - Q (0, i) (u - Pi.single j 1, j)) = 0 := by
    rw [← Summable.tsum_finsetSum s]
    have : ∀ u, ∑ j, f u * (Q (0, i) (u, j) - Q (0, i) (u - Pi.single j 1, j)) = 0 := by
      intro u
      rw [← Finset.mul_sum, F.divergence_free, mul_zero]
    simp [this]
  simp only [key, Finset.sum_neg_distrib, neg_eq_zero] at h0
  exact h0
end Moments
section Table
variable {cK c C : ℝ} {Q : IntBond → IntBond → ℝ}
private def secondMoment (Q : IntBond → IntBond → ℝ) (i j a b : Fin 4) : ℝ :=
  ∑' z, Q (0, i) (z, j) * (midStep i j z a * midStep i j z b)
private lemma LimitFormData.tsum_expansion_eq_zero (F : LimitFormData cK c C Q) (hc : 0 < c) (i k : Fin 4) :
    ∑' z, Q (0, i) (z, k) = 0 := by
  have h := F.sum_tsum_diff_eq_zero hc i (PolyGrowth.coord k)
  have e : ∀ (j : Fin 4) (u : Fin 4 → ℤ), (((u + Pi.single j 1 : Fin 4 → ℤ) k : ℤ) : ℝ) - (u k : ℝ) =
      if j = k then 1 else 0 := by
    intro j u
    by_cases hj : j = k
    · subst hj; simp
    · simp [hj, Ne.symm hj]
  simp only [e] at h
  rw [Finset.sum_eq_single k] at h
  · simpa using h
  · intro j _ hj; simp [hj]
  · simp
private lemma LimitFormData.secondMoment_diag (F : LimitFormData cK c C Q) (hc : 0 < c) (i : Fin 4) :
    secondMoment Q i i i i = 0 := by
  have hg : PolyGrowth fun u : Fin 4 → ℤ => (u i : ℝ) - 1 / 2 := (PolyGrowth.coord i).sub (PolyGrowth.const _)
  have h := F.sum_tsum_diff_eq_zero hc i ((hg.mul hg).mul hg)
  rw [Finset.sum_eq_single i] at h
  · have s1 : Summable fun z => Q (0, i) (z, i) * (midStep i i z i * midStep i i z i) :=
      F.summable_mul hc i i ((polyGrowth_midStep i i i).mul (polyGrowth_midStep i i i))
    have s2 : Summable fun z => Q (0, i) (z, i) := by
      simpa using F.summable_mul hc i i (PolyGrowth.const 1)
    have h3 : ∑' z, Q (0, i) (z, i) * (midStep i i z i * midStep i i z i) * 3 +
        ∑' z, Q (0, i) (z, i) * (1 / 4) = 0 := by
      rw [tsum_mul_right, tsum_mul_right, ← tsum_mul_right, ← tsum_mul_right,
        ← s1.mul_right 3 |>.tsum_add (s2.mul_right (1 / 4))]
      rw [← h]
      refine tsum_congr fun u => ?_
      simp only [midStep_self, Pi.add_apply, Pi.single_eq_same]
      push_cast
      ring
    rw [tsum_mul_right, tsum_mul_right, F.tsum_expansion_eq_zero hc] at h3
    unfold secondMoment
    linarith
  · intro j _ hj
    have : ∀ u : Fin 4 → ℤ, (u + Pi.single j 1 : Fin 4 → ℤ) i = u i := by
      intro u; simp [Ne.symm hj]
    simp only [this, sub_self, mul_zero, tsum_zero]
  · simp
private lemma LimitFormData.secondMoment_relation (F : LimitFormData cK c C Q) (hc : 0 < c) (i l : Fin 4)
    (hil : i ≠ l) :
    2 * secondMoment Q i l l i + secondMoment Q i i l l = 0 := by
  have hg : PolyGrowth fun u : Fin 4 → ℤ => (u i : ℝ) - 1 / 2 := (PolyGrowth.coord i).sub (PolyGrowth.const _)
  have h := F.sum_tsum_diff_eq_zero hc i (((PolyGrowth.coord l).mul (PolyGrowth.coord l)).mul hg)
  rw [Finset.sum_eq_add l i (Ne.symm hil) ?_ (by simp) (by simp)] at h
  · have h1 : ∑' u, Q (0, i) (u, l) * ((((u + Pi.single l 1 : Fin 4 → ℤ) l : ℤ) : ℝ) *
        (((u + Pi.single l 1 : Fin 4 → ℤ) l : ℤ) : ℝ) *
        ((((u + Pi.single l 1 : Fin 4 → ℤ) i : ℤ) : ℝ) - 1 / 2) - (u l : ℝ) * (u l : ℝ) * ((u i : ℝ) - 1 / 2)) =
        2 * secondMoment Q i l l i := by
      unfold secondMoment
      rw [← tsum_mul_left]
      refine tsum_congr fun u => ?_
      simp only [midStep, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hil]
      simp [Ne.symm hil, hil]
      ring
    have h2 : ∑' u, Q (0, i) (u, i) * ((((u + Pi.single i 1 : Fin 4 → ℤ) l : ℤ) : ℝ) *
        (((u + Pi.single i 1 : Fin 4 → ℤ) l : ℤ) : ℝ) *
        ((((u + Pi.single i 1 : Fin 4 → ℤ) i : ℤ) : ℝ) - 1 / 2) - (u l : ℝ) * (u l : ℝ) * ((u i : ℝ) - 1 / 2)) =
        secondMoment Q i i l l := by
      unfold secondMoment
      refine tsum_congr fun u => ?_
      simp only [midStep_self, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hil)]
      push_cast
      ring
    rw [h1, h2] at h
    exact h
  · intro j _ hj
    have e1 : ∀ u : Fin 4 → ℤ, (u + Pi.single j 1 : Fin 4 → ℤ) i = u i := by
      intro u; simp [Ne.symm hj.2]
    have e2 : ∀ u : Fin 4 → ℤ, (u + Pi.single j 1 : Fin 4 → ℤ) l = u l := by
      intro u; simp [Ne.symm hj.1]
    simp only [e1, e2, sub_self, mul_zero, tsum_zero]
private def axisReflection (c : Fin 4) : Fin 4 → ℤ := fun l => if l = c then -1 else 1
private lemma axisReflection_unit (c l : Fin 4) : axisReflection c l = 1 ∨ axisReflection c l = -1 := by
  unfold axisReflection; split_ifs <;> simp
private lemma reflSign_axisReflection (c i : Fin 4) : reflSign (axisReflection c) i = if i = c then -1 else 1 := by
  unfold reflSign axisReflection
  by_cases h : i = c <;> simp [h]
private lemma LimitFormData.secondMoment_reflect (F : LimitFormData cK c C Q) (d i j a b : Fin 4) :
    secondMoment Q i j a b = (if i = d then -1 else 1) * (if j = d then -1 else 1) *
      ((if a = d then -1 else 1) * (if b = d then -1 else 1)) * secondMoment Q i j a b := by
  unfold secondMoment
  have h := F.tsum_reflectSite (axisReflection d) (axisReflection_unit d) i j (fun z => midStep i j z a * midStep i j z b)
    ((if a = d then -1 else 1) * (if b = d then -1 else 1)) (fun z => by
      rw [midStep_flipSite _ (axisReflection_unit d), midStep_flipSite _ (axisReflection_unit d)]
      unfold axisReflection
      by_cases h1 : a = d <;> by_cases h2 : b = d <;> simp [h1, h2])
  rw [reflSign_axisReflection, reflSign_axisReflection] at h
  exact h
private def momentCoeff (i j a b : Fin 4) : ℝ :=
  if i = j then (if a = b ∧ a ≠ i then -2 else 0)
  else (if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then 1 else 0)
private lemma eq_zero_of_eq_neg_one_mul {x : ℝ} (h : x = -1 * x) : x = 0 := by linarith
private lemma LimitFormData.secondMoment_eq_parameters (F : LimitFormData cK c C Q) (hc : 0 < c)
    (hM : ∀ i l : Fin 4, i ≠ l → HasSum (fun z : Fin 4 → ℤ => Q (0, i) (z, i) * (z l : ℝ) ^ 2) (-2))
    (i j a b : Fin 4) : secondMoment Q i j a b = momentCoeff i j a b := by
  by_cases hij : i = j
  · subst hij
    by_cases hab : a = b
    · subst hab
      by_cases hai : a = i
      · subst hai
        simp [momentCoeff, F.secondMoment_diag hc]
      · have h := (hM i a (Ne.symm hai)).tsum_eq
        have e : secondMoment Q i i a a = -2 := by
          rw [← h]
          unfold secondMoment
          refine tsum_congr fun z => ?_
          rw [midStep_self]; ring
        simp [momentCoeff, hai, e]
    · have h := F.secondMoment_reflect a i i a b
      have e : secondMoment Q i i a b = 0 := by
        refine eq_zero_of_eq_neg_one_mul ?_
        conv_lhs => rw [h]
        by_cases h1 : i = a <;> simp [h1, Ne.symm hab]
      simp [momentCoeff, hab, e]
  · by_cases hab : a = b
    · subst hab
      have h := F.secondMoment_reflect i i j a a
      have e : secondMoment Q i j a a = 0 := by
        refine eq_zero_of_eq_neg_one_mul ?_
        conv_lhs => rw [h]
        by_cases h1 : a = i <;> simp [h1, Ne.symm hij]
      rw [e]
      simp only [momentCoeff, hij, if_false]
      rw [if_neg]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hij (h1.symm.trans h2)
      · exact hij (h2.symm.trans h1)
    · have hcomm : secondMoment Q i j a b = secondMoment Q i j b a := by
        unfold secondMoment
        exact tsum_congr fun z => by ring
      have h2 := F.secondMoment_relation hc i j hij
      have hd : secondMoment Q i i j j = -2 := by
        have h := (hM i j hij).tsum_eq
        rw [← h]
        unfold secondMoment
        refine tsum_congr fun z => ?_
        rw [midStep_self]; ring
      by_cases hp : (a = i ∧ b = j) ∨ (a = j ∧ b = i)
      · have e : secondMoment Q i j j i = 1 := by linarith
        have e2 : secondMoment Q i j i j = 1 := by
          have : secondMoment Q i j i j = secondMoment Q i j j i := by
            unfold secondMoment
            exact tsum_congr fun z => by ring
          linarith
        rcases hp with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · subst h3; subst h4; simp [momentCoeff, hij, e2]
        · subst h3; subst h4; simp [momentCoeff, hij, e]
      · have e : secondMoment Q i j a b = 0 := by
          by_cases ha : a = i ∨ a = j
          · have hb : b ≠ i ∧ b ≠ j := by
              constructor
              · intro h3
                rcases ha with h4 | h4
                · exact hab (h4.trans h3.symm)
                · exact hp (Or.inr ⟨h4, h3⟩)
              · intro h3
                rcases ha with h4 | h4
                · exact hp (Or.inl ⟨h4, h3⟩)
                · exact hab (h4.trans h3.symm)
            have h := F.secondMoment_reflect b i j a b
            refine eq_zero_of_eq_neg_one_mul ?_
            conv_lhs => rw [h]
            simp [Ne.symm hb.1, Ne.symm hb.2, hab]
          · have h := F.secondMoment_reflect a i j a b
            push Not at ha
            refine eq_zero_of_eq_neg_one_mul ?_
            conv_lhs => rw [h]
            simp [Ne.symm ha.1, Ne.symm ha.2, Ne.symm hab]
        rw [e]
        simp [momentCoeff, hij, hp]
private lemma momentMatrix_quadratic (p : Fin 4 → ℝ) (i j : Fin 4) :
    ∑ a, ∑ b, p a * p b * momentCoeff i j a b = -2 * ((if i = j then momentumNormSq p else 0) - p i * p j) := by
  fin_cases i <;> fin_cases j <;> simp [momentCoeff, Fin.sum_univ_four, momentumNormSq] <;> ring
private def phase (i j : Fin 4) (p : Fin 4 → ℝ) (z : Fin 4 → ℤ) : ℝ := ∑ l, p l * midStep i j z l
private lemma polyGrowth_phase (i j : Fin 4) (p : Fin 4 → ℝ) : PolyGrowth (phase i j p) := by
  refine ⟨∑ l, |p l|, 1, fun z => ?_⟩
  unfold phase
  calc _ ≤ ∑ l, |p l * midStep i j z l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, |p l| * (1 + (supNorm z : ℝ)) ^ 1 := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [abs_mul, pow_one]
        exact mul_le_mul_of_nonneg_left (abs_midStep_le i j z l) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]
private lemma PolyGrowth.of_abs_le_one {g : (Fin 4 → ℤ) → ℝ} (h : ∀ z, |g z| ≤ 1) : PolyGrowth g :=
  ⟨1, 0, fun z => by simpa using h z⟩
private def cosSymbol (Q : IntBond → IntBond → ℝ) (i j : Fin 4) (p : Fin 4 → ℝ) : ℝ :=
  ∑' z, Q (0, i) (z, j) * Real.cos (phase i j p z)
private lemma phase_sq_le (i j : Fin 4) (p : Fin 4 → ℝ) (z : Fin 4 → ℤ) :
    phase i j p z ^ 2 ≤ momentumNormSq p * (4 * (1 + (supNorm z : ℝ)) ^ 2) := by
  have h1 : phase i j p z ^ 2 ≤ (∑ l, p l ^ 2) * ∑ l, midStep i j z l ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h2 : ∑ l, midStep i j z l ^ 2 ≤ 4 * (1 + (supNorm z : ℝ)) ^ 2 := by
    have : ∑ l : Fin 4, midStep i j z l ^ 2 ≤ ∑ _l : Fin 4, (1 + (supNorm z : ℝ)) ^ 2 := by
      refine Finset.sum_le_sum fun l _ => ?_
      exact sq_le_sq' (by have := abs_le.1 (abs_midStep_le i j z l); linarith [this.1])
        (abs_le.1 (abs_midStep_le i j z l)).2
    simpa using this
  refine h1.trans ?_
  unfold momentumNormSq
  exact mul_le_mul_of_nonneg_left h2 (Finset.sum_nonneg fun l _ => by positivity)
private lemma LimitFormData.cosSymbol_near (F : LimitFormData cK c C Q) (hc : 0 < c)
    (hT : latticeMomentumTrigStatement)
    (hM : ∀ i l : Fin 4, i ≠ l → HasSum (fun z : Fin 4 → ℤ => Q (0, i) (z, i) * (z l : ℝ) ^ 2) (-2))
    (i j : Fin 4) (p : Fin 4 → ℝ) :
    |cosSymbol Q i j p - ((if i = j then momentumNormSq p else 0) - p i * p j)| ≤
      8 * C * (∑' z, expWeight c 4 z) * momentumNormSq p ^ 2 := by
  have hPt := polyGrowth_phase i j p
  have hcos : PolyGrowth fun z => Real.cos (phase i j p z) :=
    PolyGrowth.of_abs_le_one fun z => Real.abs_cos_le_one _
  have hr : PolyGrowth fun z => Real.cos (phase i j p z) - 1 + phase i j p z * phase i j p z * (1 / 2) :=
    (hcos.sub (PolyGrowth.const 1)).add ((hPt.mul hPt).mul (PolyGrowth.const (1 / 2)))
  have s0 : Summable fun z => Q (0, i) (z, j) := by simpa using F.summable_mul hc i j (PolyGrowth.const 1)
  have h0 : HasSum (fun z => Q (0, i) (z, j)) 0 := by
    have := s0.hasSum
    rwa [F.tsum_expansion_eq_zero hc] at this
  have h2 : HasSum (fun z => Q (0, i) (z, j) * (phase i j p z * phase i j p z))
      (-2 * ((if i = j then momentumNormSq p else 0) - p i * p j)) := by
    have hab : ∀ a b, HasSum (fun z => p a * p b * (Q (0, i) (z, j) * (midStep i j z a * midStep i j z b)))
        (p a * p b * momentCoeff i j a b) := by
      intro a b
      have s : Summable fun z => Q (0, i) (z, j) * (midStep i j z a * midStep i j z b) :=
        F.summable_mul hc i j ((polyGrowth_midStep i j a).mul (polyGrowth_midStep i j b))
      have h := s.hasSum.mul_left (p a * p b)
      have e : ∑' z, Q (0, i) (z, j) * (midStep i j z a * midStep i j z b) = momentCoeff i j a b :=
        F.secondMoment_eq_parameters hc hM i j a b
      rwa [e] at h
    have h3 := hasSum_sum (s := Finset.univ) (fun a _ => hasSum_sum (s := Finset.univ) (fun b _ => hab a b))
    rw [momentMatrix_quadratic] at h3
    convert h3 using 1
    funext z
    have e : phase i j p z * phase i j p z = ∑ a, ∑ b, (p a * midStep i j z a) * (p b * midStep i j z b) := by
      unfold phase
      exact Finset.sum_mul_sum _ _ _ _
    rw [e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have s3 : Summable fun z => Q (0, i) (z, j) *
      (Real.cos (phase i j p z) - 1 + phase i j p z * phase i j p z * (1 / 2)) := F.summable_mul hc i j hr
  have h4 := (h0.add (h2.mul_left (-(1 / 2)))).add s3.hasSum
  have e4 : cosSymbol Q i j p = 0 + -(1 / 2) * (-2 * ((if i = j then momentumNormSq p else 0) - p i * p j)) +
      ∑' z, Q (0, i) (z, j) * (Real.cos (phase i j p z) - 1 + phase i j p z * phase i j p z * (1 / 2)) := by
    rw [← h4.tsum_eq]
    unfold cosSymbol
    exact tsum_congr fun z => by ring
  have e5 : cosSymbol Q i j p - ((if i = j then momentumNormSq p else 0) - p i * p j) =
      ∑' z, Q (0, i) (z, j) * (Real.cos (phase i j p z) - 1 + phase i j p z * phase i j p z * (1 / 2)) := by
    rw [e4]; ring
  rw [e5, ← Real.norm_eq_abs]
  refine tsum_of_norm_bounded
    (((summable_expWeight hc 4).hasSum.mul_left (8 * C)).mul_right (momentumNormSq p ^ 2)) fun z => ?_
  rw [Real.norm_eq_abs, abs_mul]
  have hb : |Real.cos (phase i j p z) - 1 + phase i j p z * phase i j p z * (1 / 2)| ≤
      16 * momentumNormSq p ^ 2 * (1 + (supNorm z : ℝ)) ^ 4 / 2 := by
    have h5 := hT.1 (phase i j p z)
    have h6 := phase_sq_le i j p z
    have e6 : Real.cos (phase i j p z) - 1 + phase i j p z * phase i j p z * (1 / 2) =
        Real.cos (phase i j p z) - 1 + phase i j p z ^ 2 / 2 := by ring
    rw [e6]
    refine h5.trans ?_
    have h7 : phase i j p z ^ 4 ≤ (momentumNormSq p * (4 * (1 + (supNorm z : ℝ)) ^ 2)) ^ 2 := by
      have : phase i j p z ^ 4 = (phase i j p z ^ 2) ^ 2 := by ring
      rw [this]
      exact pow_le_pow_left₀ (by positivity) h6 2
    nlinarith
  have := mul_le_mul (F.abs_le i j z) hb (abs_nonneg _) ((abs_nonneg _).trans (F.abs_le i j z))
  refine this.trans (le_of_eq ?_)
  unfold expWeight; ring
private lemma LimitFormData.tsum_sin_eq_zero (F : LimitFormData cK c C Q) (i j : Fin 4) (p : Fin 4 → ℝ) :
    ∑' z, Q (0, i) (z, j) * Real.sin (phase i j p z) = 0 := by
  have hs : ∀ l : Fin 4, (fun _ : Fin 4 => (-1 : ℤ)) l = 1 ∨ (fun _ : Fin 4 => (-1 : ℤ)) l = -1 :=
    fun _ => Or.inr rfl
  have h := F.tsum_reflectSite (fun _ => -1) hs i j (fun z => Real.sin (phase i j p z)) (-1) (fun z => by
    have : phase i j p (twoAxisReflectedSite (fun _ => -1) i j z) = - phase i j p z := by
      unfold phase
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [midStep_flipSite _ hs]
      push_cast
      ring
    rw [this, Real.sin_neg]; ring)
  have e : reflSign (fun _ => -1) i * reflSign (fun _ => -1) j = 1 := by simp [reflSign]
  rw [e] at h
  linarith
private lemma phase_eq (i j : Fin 4) (p : Fin 4 → ℝ) (z : Fin 4 → ℤ) :
    phase i j p z = ∑ l, p l * (z l : ℝ) + (p j - p i) / 2 := by
  unfold phase midStep
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring
private def gradPart (i j : Fin 4) (z : Fin 4 → ℤ) : ℝ :=
  ((if (0 : Fin 4 → ℤ) = z then 1 else 0) - (if (0 : Fin 4 → ℤ) = z + Pi.single j 1 then 1 else 0) -
    (if (0 : Fin 4 → ℤ) + Pi.single i 1 = z then 1 else 0) +
    (if (0 : Fin 4 → ℤ) + Pi.single i 1 = z + Pi.single j 1 then 1 else 0))
private lemma hasSum_indicator_mul (E : (Fin 4 → ℤ) → ℂ) (v : Fin 4 → ℤ) :
    HasSum (fun z => (((if z = v then (1 : ℝ) else 0) : ℝ) : ℂ) * E z) (E v) := by
  have := hasSum_single (f := fun z => (((if z = v then (1 : ℝ) else 0) : ℝ) : ℂ) * E z) v
    (fun z hz => by simp [hz])
  simpa using this
private lemma exp_combination (α β : ℝ) :
    Complex.exp (Complex.I * ((β - α : ℝ) : ℂ)) - Complex.exp (Complex.I * ((-β - α : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((α + β : ℝ) : ℂ)) + Complex.exp (Complex.I * ((α - β : ℝ) : ℂ)) =
      ((4 * Real.sin α * Real.sin β : ℝ) : ℂ) := by apply _root_.YangMills.SharedProofs.p9881 <;> assumption
private lemma exp_I_mul_ofReal (t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ)) = ((Real.cos t : ℝ) : ℂ) + ((Real.sin t : ℝ) : ℂ) * Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
private lemma LimitFormData.hasSum_symbolPart (F : LimitFormData cK c C Q) (hc : 0 < c) (i j : Fin 4)
    (p : Fin 4 → ℝ) :
    HasSum (fun z => ((Q (0, i) (z, j) : ℝ) : ℂ) * Complex.exp (Complex.I * ((phase i j p z : ℝ) : ℂ)))
      ((cosSymbol Q i j p : ℝ) : ℂ) := by
  have hsin : PolyGrowth fun z => Real.sin (phase i j p z) :=
    PolyGrowth.of_abs_le_one fun z => Real.abs_sin_le_one _
  have hcos : PolyGrowth fun z => Real.cos (phase i j p z) :=
    PolyGrowth.of_abs_le_one fun z => Real.abs_cos_le_one _
  have h1 : HasSum (fun z => Q (0, i) (z, j) * Real.cos (phase i j p z)) (cosSymbol Q i j p) :=
    (F.summable_mul hc i j hcos).hasSum
  have h2 : HasSum (fun z => Q (0, i) (z, j) * Real.sin (phase i j p z)) 0 := by
    have := (F.summable_mul hc i j hsin).hasSum
    rwa [F.tsum_sin_eq_zero] at this
  have h1' := Complex.ofRealCLM.hasSum h1
  have h2' := (Complex.ofRealCLM.hasSum h2).mul_right Complex.I
  have hK := h1'.add h2'
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_zero, zero_mul, add_zero] at hK
  convert hK using 1
  funext z
  rw [exp_I_mul_ofReal]
  push_cast
  ring
private lemma LimitFormData.symbol_eq (F : LimitFormData cK c C Q) (hc : 0 < c) (i j : Fin 4) (p : Fin 4 → ℝ) :
    midpointSymbol Q i j p = ((cosSymbol Q i j p + 4 * Real.sin (p i / 2) * Real.sin (p j / 2) : ℝ) : ℂ) := by
  have hK := F.hasSum_symbolPart hc i j p
  set E : (Fin 4 → ℤ) → ℂ := fun z => Complex.exp (Complex.I * ((phase i j p z : ℝ) : ℂ)) with hE
  have hD : HasSum (fun z => ((gradPart i j z : ℝ) : ℂ) * E z)
      ((4 * Real.sin (p i / 2) * Real.sin (p j / 2) : ℝ) : ℂ) := by
    have a1 := hasSum_indicator_mul E 0
    have a2 := hasSum_indicator_mul E (- Pi.single j 1)
    have a3 := hasSum_indicator_mul E (Pi.single i 1)
    have a4 := hasSum_indicator_mul E (Pi.single i 1 - Pi.single j 1)
    have h := ((a1.sub a2).sub a3).add a4
    have v1 : E 0 = Complex.exp (Complex.I * ((p j / 2 - p i / 2 : ℝ) : ℂ)) := by
      simp only [hE, phase_eq]
      congr 3
      simp; ring
    have v2 : E (- Pi.single j 1) = Complex.exp (Complex.I * ((-(p j / 2) - p i / 2 : ℝ) : ℂ)) := by
      simp only [hE, phase_eq]
      congr 3
      simp [Pi.single_apply]; ring
    have v3 : E (Pi.single i 1) = Complex.exp (Complex.I * ((p i / 2 + p j / 2 : ℝ) : ℂ)) := by
      simp only [hE, phase_eq]
      congr 3
      simp [Pi.single_apply]; ring
    have v4 : E (Pi.single i 1 - Pi.single j 1) = Complex.exp (Complex.I * ((p i / 2 - p j / 2 : ℝ) : ℂ)) := by
      simp only [hE, phase_eq]
      congr 3
      simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib]; ring
    rw [v1, v2, v3, v4, exp_combination] at h
    refine (congrArg (fun f : (Fin 4 → ℤ) → ℂ => HasSum f _) ?_).mpr h
    funext z
    have c1 : (0 : Fin 4 → ℤ) = z ↔ z = 0 := eq_comm
    have c2 : (0 : Fin 4 → ℤ) = z + Pi.single j 1 ↔ z = - Pi.single j 1 := by
      rw [eq_comm, add_eq_zero_iff_eq_neg]
    have c3 : (0 : Fin 4 → ℤ) + Pi.single i 1 = z ↔ z = Pi.single i 1 := by
      rw [zero_add, eq_comm]
    have c4 : (0 : Fin 4 → ℤ) + Pi.single i 1 = z + Pi.single j 1 ↔ z = Pi.single i 1 - Pi.single j 1 := by
      rw [zero_add, eq_sub_iff_add_eq, eq_comm]
    simp only [gradPart, c1, c2, c3, c4]
    push_cast
    ring
  have hs := hK.add hD
  rw [← Complex.ofReal_add] at hs
  rw [← hs.tsum_eq]
  unfold midpointSymbol
  refine tsum_congr fun z => ?_
  have e1 : gaugeFixedKernel Q (0, i) (z, j) = Q (0, i) (z, j) + gradPart i j z := rfl
  have e2 : Complex.exp (Complex.I * ((∑ l, p l * ((z l : ℝ) + (if l = j then 1 / 2 else 0) -
      (if l = i then 1 / 2 else 0)) : ℝ) : ℂ)) = E z := rfl
  rw [e1, e2]
  push_cast
  ring
end Table
section Coercive
variable {cK c C : ℝ} {Q : IntBond → IntBond → ℝ}
private def box (N : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N
private lemma mem_box {N : ℕ} {z : Fin 4 → ℤ} : z ∈ box N ↔ ∀ l, |z l| ≤ N := by
  simp [box, Fintype.mem_piFinset, abs_le]
private lemma card_box (N : ℕ) : ((box N).card : ℝ) = (2 * (N : ℝ) + 1) ^ 4 := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolNorm.card_intCube <;> assumption
private lemma add_single_mem_box {N : ℕ} {x : Fin 4 → ℤ} (hx : x ∈ box N) (l : Fin 4) :
    x + Pi.single l 1 ∈ box (N + 1) := by
  rw [mem_box] at hx ⊢
  intro k
  have h := hx k
  rw [abs_le] at h ⊢
  by_cases hk : k = l
  · subst hk; simp; omega
  · simp [hk]; omega
private lemma mem_box_succ {N : ℕ} {x : Fin 4 → ℤ} (hx : x ∈ box N) : x ∈ box (N + 1) := by
  rw [mem_box] at hx ⊢
  intro k
  have h := hx k
  push_cast
  omega
private def boxPlaquettes (N : ℕ) : Finset ((Fin 4 → ℤ) × Fin 4 × Fin 4) :=
  (box N) ×ˢ (Finset.univ.filter fun q : Fin 4 × Fin 4 => q.1 < q.2)
private lemma LimitFormData.box_lowerBound (F : LimitFormData cK c C Q) (f : IntBond → ℝ) (N : ℕ) :
    2 * cK * ∑ q ∈ boxPlaquettes N, intCurl f q ^ 2 ≤
      ∑ x ∈ box (N + 1), ∑ i, ∑ y ∈ box (N + 1), ∑ j, f (x, i) * Q (x, i) (y, j) * f (y, j) := by
  classical
  set Bb : Finset IntBond := (box (N + 1)) ×ˢ (Finset.univ : Finset (Fin 4)) with hBb
  let v : IntBond →₀ ℝ := Finsupp.onFinset Bb (fun b => if b ∈ Bb then f b else 0)
    (fun b hb => by
      by_contra h
      simp [h] at hb)
  have hv : ∀ b ∈ Bb, v b = f b := fun b hb => by
    simp [v, Finsupp.onFinset_apply, hb]
  have hP : ∀ q ∈ boxPlaquettes N, q.2.1 < q.2.2 := fun q hq => by
    simpa [boxPlaquettes] using (Finset.mem_product.1 hq).2
  have h := F.lowerBound v (boxPlaquettes N) hP
  have hcurl : ∀ q ∈ boxPlaquettes N, intCurl v q = intCurl f q := by
    intro q hq
    have hx : q.1 ∈ box N := (Finset.mem_product.1 hq).1
    have m1 : (q.1, q.2.1) ∈ Bb := Finset.mem_product.2 ⟨mem_box_succ hx, Finset.mem_univ _⟩
    have m2 : (q.1, q.2.2) ∈ Bb := Finset.mem_product.2 ⟨mem_box_succ hx, Finset.mem_univ _⟩
    have m3 : (q.1 + Pi.single q.2.1 1, q.2.2) ∈ Bb :=
      Finset.mem_product.2 ⟨add_single_mem_box hx _, Finset.mem_univ _⟩
    have m4 : (q.1 + Pi.single q.2.2 1, q.2.1) ∈ Bb :=
      Finset.mem_product.2 ⟨add_single_mem_box hx _, Finset.mem_univ _⟩
    unfold intCurl
    rw [hv _ m1, hv _ m2, hv _ m3, hv _ m4]
  have hsup : v.support ⊆ Bb := Finsupp.support_onFinset_subset
  have hsum : ∑ b ∈ v.support, ∑ b' ∈ v.support, v b * Q b b' * v b' =
      ∑ b ∈ Bb, ∑ b' ∈ Bb, f b * Q b b' * f b' := by
    have e1 : ∀ b, ∑ b' ∈ v.support, v b * Q b b' * v b' = ∑ b' ∈ Bb, v b * Q b b' * v b' := by
      intro b
      refine Finset.sum_subset hsup fun b' _ hb' => ?_
      simp [Finsupp.notMem_support_iff.1 hb']
    simp only [e1]
    rw [Finset.sum_subset hsup (fun b _ hb => by simp [Finsupp.notMem_support_iff.1 hb])]
    refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun b' hb' => ?_
    rw [hv b hb, hv b' hb']
  rw [hsum, Finset.sum_congr rfl (fun q hq => by rw [hcurl q hq])] at h
  refine h.trans (le_of_eq ?_)
  rw [hBb, Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_product]
private def midAngle (p : Fin 4 → ℝ) (b : IntBond) : ℝ :=
  ∑ l, p l * ((b.1 l : ℝ) + (if l = b.2 then 1 / 2 else 0))
private lemma midAngle_sub (p : Fin 4 → ℝ) (i j : Fin 4) (x y : Fin 4 → ℤ) :
    midAngle p (y, j) - midAngle p (x, i) = phase i j p (y - x) := by
  unfold midAngle phase midStep
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.sub_apply]
  push_cast
  ring
private lemma midAngle_eq (p : Fin 4 → ℝ) (j : Fin 4) (x : Fin 4 → ℤ) :
    midAngle p (x, j) = ∑ l, p l * (x l : ℝ) + p j / 2 := by
  unfold midAngle
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring
private lemma midAngle_add_single (p : Fin 4 → ℝ) (i j : Fin 4) (x : Fin 4 → ℤ) :
    midAngle p (x + Pi.single i 1, j) = ∑ l, p l * (x l : ℝ) + p i + p j / 2 := by
  rw [midAngle_eq]
  have : ∑ l, p l * (((x + Pi.single i 1 : Fin 4 → ℤ) l : ℤ) : ℝ) = ∑ l, p l * (x l : ℝ) + p i := by
    simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
    congr 1
    simp [Pi.single_apply]
  rw [this]
private def latticeMom (p : Fin 4 → ℝ) (l : Fin 4) : ℝ := 2 * Real.sin (p l / 2)
private def cosWave (a p : Fin 4 → ℝ) (b : IntBond) : ℝ := a b.2 * Real.cos (midAngle p b)
private def sinWave (a p : Fin 4 → ℝ) (b : IntBond) : ℝ := a b.2 * Real.sin (midAngle p b)
private lemma intCurl_waves_sq (a p : Fin 4 → ℝ) (x : Fin 4 → ℤ) (i j : Fin 4) :
    intCurl (cosWave a p) (x, i, j) ^ 2 + intCurl (sinWave a p) (x, i, j) ^ 2 =
      (a i * latticeMom p j - a j * latticeMom p i) ^ 2 := by
  set A := ∑ l, p l * (x l : ℝ) with hA
  set α := p i / 2 with hα
  set β := p j / 2 with hβ
  have e1 : midAngle p (x, i) = (A + α + β) - β := by rw [midAngle_eq]; ring
  have e2 : midAngle p (x + Pi.single i 1, j) = (A + α + β) + α := by
    rw [midAngle_add_single]; simp only [hα, hβ]; ring
  have e3 : midAngle p (x + Pi.single j 1, i) = (A + α + β) + β := by
    rw [midAngle_add_single]; simp only [hα, hβ]; ring
  have e4 : midAngle p (x, j) = (A + α + β) - α := by rw [midAngle_eq]; ring
  set μ := A + α + β with hμ
  have c1 : intCurl (cosWave a p) (x, i, j) = Real.sin μ * (a i * latticeMom p j - a j * latticeMom p i) := by
    simp only [intCurl, cosWave, e1, e2, e3, e4, latticeMom, Real.cos_add, Real.cos_sub]
    rw [← hα, ← hβ]
    ring
  have c2 : intCurl (sinWave a p) (x, i, j) = - Real.cos μ * (a i * latticeMom p j - a j * latticeMom p i) := by
    simp only [intCurl, sinWave, e1, e2, e3, e4, latticeMom, Real.sin_add, Real.sin_sub]
    rw [← hα, ← hβ]
    ring
  rw [c1, c2]
  have := Real.sin_sq_add_cos_sq μ
  calc _ = (Real.sin μ ^ 2 + Real.cos μ ^ 2) * (a i * latticeMom p j - a j * latticeMom p i) ^ 2 := by ring
    _ = _ := by rw [this, one_mul]
private def waveSum (Q : IntBond → IntBond → ℝ) (a p : Fin 4 → ℝ) (z : Fin 4 → ℤ) : ℝ :=
  ∑ i, ∑ j, a i * a j * (Q (0, i) (z, j) * Real.cos (phase i j p z))
private lemma LimitFormData.hasSum_waveSum (F : LimitFormData cK c C Q) (hc : 0 < c) (a p : Fin 4 → ℝ) :
    HasSum (waveSum Q a p) (∑ i, ∑ j, a i * a j * cosSymbol Q i j p) := by
  refine hasSum_sum (s := Finset.univ) fun i _ => hasSum_sum (s := Finset.univ) fun j _ => ?_
  have hcos : PolyGrowth fun z => Real.cos (phase i j p z) :=
    PolyGrowth.of_abs_le_one fun z => Real.abs_cos_le_one _
  exact (F.summable_mul hc i j hcos).hasSum.mul_left _
private def overlapCount (M : ℕ) (z : Fin 4 → ℤ) : ℕ := ((box M).filter fun x => x + z ∈ box M).card
private lemma sum_box_sub (G : (Fin 4 → ℤ) → ℝ) (hG : Summable G) (M : ℕ) :
    ∑ x ∈ box M, ∑ y ∈ box M, G (y - x) = ∑' z, G z * (overlapCount M z : ℝ) := by
  classical
  have h1 : ∀ x, ∑ y ∈ box M, G (y - x) = ∑' z, if x + z ∈ box M then G z else 0 := by
    intro x
    have e1 : ∑' y, (if y ∈ box M then G (y - x) else 0) = ∑ y ∈ box M, G (y - x) := by
      rw [tsum_eq_sum (s := box M) (fun y hy => by simp [hy])]
      exact Finset.sum_congr rfl fun y hy => by simp [hy]
    rw [← e1]
    refine ((Equiv.addLeft x).tsum_eq (fun y => if y ∈ box M then G (y - x) else 0)).symm.trans ?_
    refine tsum_congr fun z => ?_
    simp
  simp only [h1]
  rw [← Summable.tsum_finsetSum]
  · refine tsum_congr fun z => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    unfold overlapCount
    ring
  · intro x _
    refine Summable.of_norm_bounded hG.norm fun z => ?_
    split_ifs <;> simp
private lemma overlapCount_le (M : ℕ) (z : Fin 4 → ℤ) : overlapCount M z ≤ (box M).card :=
  Finset.card_filter_le _ _
private lemma overlapCount_ge (M : ℕ) (z : Fin 4 → ℤ) (h : supNorm z ≤ M) :
    (box (M - supNorm z)).card ≤ overlapCount M z := by
  refine Finset.card_le_card fun x hx => ?_
  rw [mem_box] at hx
  refine Finset.mem_filter.2 ⟨mem_box.2 fun l => ?_, mem_box.2 fun l => ?_⟩
  · have h1 := hx l
    have : ((M - supNorm z : ℕ) : ℤ) ≤ M := by omega
    omega
  · have h1 := hx l
    have h2 : ((z l).natAbs : ℤ) ≤ supNorm z := by exact_mod_cast natAbs_le_supNorm z l
    have h3 : ((M - supNorm z : ℕ) : ℤ) = M - supNorm z := by omega
    rw [h3] at h1
    simp only [Pi.add_apply]
    rw [abs_le] at h1 ⊢
    have h4 : |z l| = ((z l).natAbs : ℤ) := Int.abs_eq_natAbs _
    have h5 := abs_le.1 (h4.le.trans h2)
    omega
private lemma tendsto_shrink_ratio (s : ℕ) :
    Tendsto (fun N : ℕ => ((2 * ((N : ℝ) + 1) + 1 - 2 * s) / (2 * ((N : ℝ) + 1) + 1)) ^ 4) atTop (𝓝 1) := by
  have h1 : Tendsto (fun N : ℕ => 2 * ((N : ℝ) + 1) + 1) atTop atTop := by
    have : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    refine tendsto_atTop_add_const_right _ _ ?_
    refine Tendsto.const_mul_atTop (by norm_num) ?_
    exact tendsto_atTop_add_const_right _ _ this
  have h2 : Tendsto (fun N : ℕ => (2 * (s : ℝ)) / (2 * ((N : ℝ) + 1) + 1)) atTop (𝓝 0) :=
    h1.const_div_atTop _
  have h3 : Tendsto (fun N : ℕ => (1 - (2 * (s : ℝ)) / (2 * ((N : ℝ) + 1) + 1)) ^ 4) atTop (𝓝 ((1 - 0) ^ 4)) :=
    (tendsto_const_nhds.sub h2).pow 4
  simp only [sub_zero, one_pow] at h3
  refine h3.congr fun N => ?_
  have : (2 * ((N : ℝ) + 1) + 1) ≠ 0 := by positivity
  congr 1
  field_simp
private lemma tendsto_overlap_ratio (z : Fin 4 → ℤ) :
    Tendsto (fun N : ℕ => (overlapCount (N + 1) z : ℝ) / ((box (N + 1)).card : ℝ)) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_shrink_ratio (supNorm z)) tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (supNorm z)] with N hN
    have hM : supNorm z ≤ N + 1 := by omega
    have h1 : ((box (N + 1 - supNorm z)).card : ℝ) ≤ overlapCount (N + 1) z := by
      exact_mod_cast overlapCount_ge _ z hM
    rw [card_box] at h1
    rw [card_box]
    have e : ((N + 1 - supNorm z : ℕ) : ℝ) = (N : ℝ) + 1 - supNorm z := by
      rw [Nat.cast_sub hM]; push_cast; ring
    rw [e] at h1
    have hp : (0 : ℝ) < (2 * (((N + 1 : ℕ)) : ℝ) + 1) ^ 4 := by positivity
    rw [le_div_iff₀ hp]
    push_cast
    rw [div_pow, div_mul_cancel₀ _ (by positivity)]
    refine le_trans (le_of_eq ?_) h1
    ring
  · filter_upwards with N
    have h1 : (overlapCount (N + 1) z : ℝ) ≤ (box (N + 1)).card := by exact_mod_cast overlapCount_le _ z
    have hp : (0 : ℝ) < ((box (N + 1)).card : ℝ) := by
      rw [card_box]; positivity
    rw [div_le_one hp]
    exact h1
private def waveCurlSq (a p : Fin 4 → ℝ) : ℝ :=
  ∑ q ∈ Finset.univ.filter (fun q : Fin 4 × Fin 4 => q.1 < q.2),
    (a q.1 * latticeMom p q.2 - a q.2 * latticeMom p q.1) ^ 2
private lemma LimitFormData.box_wave_bound (F : LimitFormData cK c C Q) (hc : 0 < c) (a p : Fin 4 → ℝ) (N : ℕ) :
    2 * cK * (((box N).card : ℝ) * waveCurlSq a p) ≤ ∑' z, waveSum Q a p z * (overlapCount (N + 1) z : ℝ) := by
  have h1 := F.box_lowerBound (cosWave a p) N
  have h2 := F.box_lowerBound (sinWave a p) N
  have hG := (F.hasSum_waveSum hc a p).summable
  have e1 : ∑ q ∈ boxPlaquettes N, intCurl (cosWave a p) q ^ 2 + ∑ q ∈ boxPlaquettes N, intCurl (sinWave a p) q ^ 2 =
      ((box N).card : ℝ) * waveCurlSq a p := by
    rw [← Finset.sum_add_distrib, boxPlaquettes, Finset.sum_product]
    have : ∀ x ∈ box N, ∑ y ∈ Finset.univ.filter (fun q : Fin 4 × Fin 4 => q.1 < q.2),
        (intCurl (cosWave a p) (x, y) ^ 2 + intCurl (sinWave a p) (x, y) ^ 2) = waveCurlSq a p := by
      intro x _
      unfold waveCurlSq
      exact Finset.sum_congr rfl fun q _ => intCurl_waves_sq a p x q.1 q.2
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  have e2 : ∑ x ∈ box (N + 1), ∑ i, ∑ y ∈ box (N + 1), ∑ j, cosWave a p (x, i) * Q (x, i) (y, j) * cosWave a p (y, j) +
      ∑ x ∈ box (N + 1), ∑ i, ∑ y ∈ box (N + 1), ∑ j, sinWave a p (x, i) * Q (x, i) (y, j) * sinWave a p (y, j) =
      ∑ x ∈ box (N + 1), ∑ y ∈ box (N + 1), waveSum Q a p (y - x) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold waveSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← midAngle_sub, Real.cos_sub, F.translate]
    simp only [cosWave, sinWave]
    ring
  rw [← sum_box_sub _ hG, ← e2]
  rw [← e1]
  linarith
private lemma LimitFormData.wave_lowerBound (F : LimitFormData cK c C Q) (hc : 0 < c) (a p : Fin 4 → ℝ) :
    2 * cK * waveCurlSq a p ≤ ∑ i, ∑ j, a i * a j * cosSymbol Q i j p := by
  have hG := F.hasSum_waveSum hc a p
  have hlim : Tendsto (fun N : ℕ => ∑' z, waveSum Q a p z * ((overlapCount (N + 1) z : ℝ) / ((box (N + 1)).card : ℝ)))
      atTop (𝓝 (∑' z, waveSum Q a p z * 1)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun z => ‖waveSum Q a p z‖) hG.summable.norm
      (fun z => (tendsto_overlap_ratio z).const_mul _) (Eventually.of_forall fun N z => ?_)
    rw [norm_mul]
    have hp : (0 : ℝ) < ((box (N + 1)).card : ℝ) := by
      rw [card_box]; positivity
    have h1 : (overlapCount (N + 1) z : ℝ) ≤ (box (N + 1)).card := by exact_mod_cast overlapCount_le _ z
    have h2 : ‖(overlapCount (N + 1) z : ℝ) / ((box (N + 1)).card : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one hp]
      exact h1
    exact mul_le_of_le_one_right (norm_nonneg _) h2
  simp only [mul_one] at hlim
  rw [hG.tsum_eq] at hlim
  have hlow : Tendsto (fun N : ℕ => 2 * cK * waveCurlSq a p *
      ((2 * ((N : ℝ) + 1) + 1 - 2 * ((1 : ℕ) : ℝ)) / (2 * ((N : ℝ) + 1) + 1)) ^ 4)
      atTop (𝓝 (2 * cK * waveCurlSq a p * 1)) := (tendsto_shrink_ratio 1).const_mul _
  rw [mul_one] at hlow
  refine le_of_tendsto_of_tendsto hlow hlim (Eventually.of_forall fun N => ?_)
  have h := F.box_wave_bound hc a p N
  have hp : (0 : ℝ) < ((box (N + 1)).card : ℝ) := by
    rw [card_box]; positivity
  have e : ∑' z, waveSum Q a p z * ((overlapCount (N + 1) z : ℝ) / ((box (N + 1)).card : ℝ)) =
      (∑' z, waveSum Q a p z * (overlapCount (N + 1) z : ℝ)) / ((box (N + 1)).card : ℝ) := by
    rw [← tsum_div_const]
    exact tsum_congr fun z => by ring
  beta_reduce
  rw [e, le_div_iff₀ hp]
  refine le_trans (le_of_eq ?_) h
  rw [card_box, card_box]
  push_cast
  have : (2 * ((N : ℝ) + 1) + 1) ≠ 0 := by positivity
  field_simp
  ring
end Coercive
private abbrev Momentum : Type := Fin 4 → ℝ
section Final
variable {cK c C : ℝ} {Q : IntBond → IntBond → ℝ}
private lemma phase_add (i j : Fin 4) (p y : Fin 4 → ℝ) (z : Fin 4 → ℤ) :
    phase i j (p + y) z = phase i j p z + phase i j y z := by
  unfold phase
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.add_apply]
  ring
private lemma LimitFormData.analyticAt_cosSymbol (F : LimitFormData cK c C Q) (hc : 0 < c)
    (hA : AnalyticAtSumOfExponentials) (i j : Fin 4) (p₀ : Fin 4 → ℝ) :
    AnalyticAt ℝ (fun p => ((cosSymbol Q i j p : ℝ) : ℂ)) p₀ := by
  let a : (Fin 4 → ℤ) → ℂ := fun z =>
    ((Q (0, i) (z, j) : ℝ) : ℂ) * Complex.exp (Complex.I * ((phase i j p₀ z : ℝ) : ℂ))
  let Lz : (Fin 4 → ℤ) → (Momentum →L[ℝ] ℂ) := fun z =>
    Complex.I • (Complex.ofRealCLM.comp (∑ l, midStep i j z l • (ContinuousLinearMap.proj l : Momentum →L[ℝ] ℝ)))
  have hLy : ∀ z y, Lz z y = Complex.I * ((phase i j y z : ℝ) : ℂ) := by
    intro z y
    simp [Lz, phase, sum_apply, mul_comm]
  have hL : ∀ z, ‖Lz z‖ ≤ 4 * (1 + (supNorm z : ℝ)) := by
    intro z
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
    rw [hLy, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    unfold phase
    calc _ ≤ ∑ l, |y l * midStep i j z l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin 4, ‖y‖ * (1 + (supNorm z : ℝ)) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [abs_mul]
          exact mul_le_mul (norm_le_pi_norm y l) (abs_midStep_le i j z l) (abs_nonneg _) (norm_nonneg _)
      _ = _ := by simp; ring
  have hS : Summable fun z => ‖a z‖ * Real.exp (4 * (1 + (supNorm z : ℝ)) * (c / 8)) := by
    have hw := (summable_expWeight (c := c / 2) (by positivity) 0).mul_left (C * Real.exp (c / 2))
    refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_) hw
    have e1 : ‖a z‖ = |Q (0, i) (z, j)| := by
      simp only [a]
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [e1]
    have h1 := F.abs_le i j z
    calc _ ≤ (C * Real.exp (-(c * supNorm z))) * Real.exp (4 * (1 + (supNorm z : ℝ)) * (c / 8)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = C * Real.exp (c / 2) * expWeight (c / 2) 0 z := by
          have e : Real.exp (-(c * supNorm z)) * Real.exp (4 * (1 + (supNorm z : ℝ)) * (c / 8)) =
              Real.exp (c / 2) * Real.exp (-(c / 2 * supNorm z)) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
          unfold expWeight
          rw [pow_zero, mul_one, mul_assoc, e, mul_assoc]
  have hg := hA a (fun z => 4 * (1 + (supNorm z : ℝ))) Lz (c / 8) (by positivity) hL hS
  have key : (fun p => ((cosSymbol Q i j p : ℝ) : ℂ)) =
      (fun y => ∑' z, a z * Complex.exp (Lz z y)) ∘ (fun p => p - p₀) := by
    funext p
    simp only [Function.comp]
    rw [← (F.hasSum_symbolPart hc i j p).tsum_eq]
    refine tsum_congr fun z => ?_
    simp only [a]
    rw [hLy, mul_assoc, ← Complex.exp_add]
    have e : phase i j p z = phase i j p₀ z + phase i j (p - p₀) z := by
      rw [← phase_add]; simp
    rw [e]
    push_cast
    congr 2
    ring
  rw [key]
  have hf : AnalyticAt ℝ (fun p : Momentum => p - p₀) p₀ := analyticAt_id.sub analyticAt_const
  refine AnalyticAt.comp (f := fun p : Momentum => p - p₀) ?_ hf
  simpa using hg
private lemma analyticAt_sin_product (i j : Fin 4) (p₀ : Fin 4 → ℝ) :
    AnalyticAt ℝ (fun p : Momentum => ((4 * Real.sin (p i / 2) * Real.sin (p j / 2) : ℝ) : ℂ)) p₀ := by
  have hp : ∀ l, AnalyticAt ℝ (fun p : Momentum => p l / 2) p₀ := fun l => by
    have := ((ContinuousLinearMap.proj l : Momentum →L[ℝ] ℝ).analyticAt p₀).mul
      (analyticAt_const (v := (1 / 2 : ℝ)))
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp [div_eq_mul_inv]
  have hs : ∀ l, AnalyticAt ℝ (fun p : Momentum => Real.sin (p l / 2)) p₀ := fun l =>
    Real.analyticAt_sin.comp (hp l)
  have h := (analyticAt_const (v := (4 : ℝ))).mul (hs i) |>.mul (hs j)
  exact (Complex.ofRealCLM.analyticAt _).comp h
private lemma LimitFormData.real_quadratic_lowerBound (F : LimitFormData cK c C Q) (hc : 0 < c)
    (hT : latticeMomentumTrigStatement) (p a : Fin 4 → ℝ) :
    min (2 * cK) 1 * ((∑ l, latticeMom p l ^ 2) * ∑ l, a l ^ 2) ≤
      ∑ i, ∑ j, a i * a j * (cosSymbol Q i j p + 4 * Real.sin (p i / 2) * Real.sin (p j / 2)) := by
  have h1 := F.wave_lowerBound hc a p
  have h2 : ∑ i, ∑ j, a i * a j * (4 * Real.sin (p i / 2) * Real.sin (p j / 2)) =
      (∑ l, a l * latticeMom p l) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    unfold latticeMom; ring
  have h3 : waveCurlSq a p = (∑ l, latticeMom p l ^ 2) * (∑ l, a l ^ 2) - (∑ l, a l * latticeMom p l) ^ 2 :=
    hT.2.2.1 a (latticeMom p)
  have hX : 0 ≤ waveCurlSq a p := Finset.sum_nonneg fun q _ => by positivity
  have hY : 0 ≤ (∑ l, a l * latticeMom p l) ^ 2 := by positivity
  have e : ∑ i, ∑ j, a i * a j * (cosSymbol Q i j p + 4 * Real.sin (p i / 2) * Real.sin (p j / 2)) =
      ∑ i, ∑ j, a i * a j * cosSymbol Q i j p + (∑ l, a l * latticeMom p l) ^ 2 := by
    rw [← h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  have hm1 : min (2 * cK) 1 ≤ 2 * cK := min_le_left _ _
  have hm2 : min (2 * cK) 1 ≤ 1 := min_le_right _ _
  have e2 : (∑ l, latticeMom p l ^ 2) * ∑ l, a l ^ 2 = waveCurlSq a p + (∑ l, a l * latticeMom p l) ^ 2 := by
    rw [h3]; ring
  rw [e2]
  nlinarith [mul_le_mul_of_nonneg_right hm1 hX, mul_le_mul_of_nonneg_right hm2 hY]
private lemma LimitFormData.quadratic_lowerBound (F : LimitFormData cK c C Q) (hc : 0 < c) (hK : 0 < cK)
    (hT : latticeMomentumTrigStatement) (p : Fin 4 → ℝ) (hp : p ∈ brillouinBox) (ξ : Fin 4 → ℂ) :
    min (2 * cK) 1 * (4 / Real.pi ^ 2) * momentumNormSq p * ∑ i, ‖ξ i‖ ^ 2 ≤
      (∑ i, ∑ j, (starRingEnd ℂ) (ξ i) * midpointSymbol Q i j p * ξ j).re := by
  set m : Fin 4 → Fin 4 → ℝ := fun i j => cosSymbol Q i j p + 4 * Real.sin (p i / 2) * Real.sin (p j / 2) with hm'
  have e : (∑ i, ∑ j, (starRingEnd ℂ) (ξ i) * midpointSymbol Q i j p * ξ j).re =
      ∑ i, ∑ j, (ξ i).re * (ξ j).re * m i j + ∑ i, ∑ j, (ξ i).im * (ξ j).im * m i j := by
    rw [Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [F.symbol_eq hc]
    simp only [hm', Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [e]
  have h1 := F.real_quadratic_lowerBound hc hT p (fun l => (ξ l).re)
  have h2 := F.real_quadratic_lowerBound hc hT p (fun l => (ξ l).im)
  have h3 : 4 / Real.pi ^ 2 * momentumNormSq p ≤ ∑ l, latticeMom p l ^ 2 := hT.2.2.2 p hp
  have hn : ∑ i, ‖ξ i‖ ^ 2 = ∑ l, (ξ l).re ^ 2 + ∑ l, (ξ l).im ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hn]
  have hκ : 0 ≤ min (2 * cK) 1 := le_min (by positivity) zero_le_one
  have hA : 0 ≤ ∑ l, (ξ l).re ^ 2 + ∑ l, (ξ l).im ^ 2 := by positivity
  have h4 : min (2 * cK) 1 * (4 / Real.pi ^ 2 * momentumNormSq p) * (∑ l, (ξ l).re ^ 2 + ∑ l, (ξ l).im ^ 2) ≤
      min (2 * cK) 1 * (∑ l, latticeMom p l ^ 2) * (∑ l, (ξ l).re ^ 2 + ∑ l, (ξ l).im ^ 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hκ) hA
  calc _ = min (2 * cK) 1 * (4 / Real.pi ^ 2 * momentumNormSq p) * (∑ l, (ξ l).re ^ 2 + ∑ l, (ξ l).im ^ 2) := by
        ring
    _ ≤ _ := h4
    _ = min (2 * cK) 1 * ((∑ l, latticeMom p l ^ 2) * ∑ l, (ξ l).re ^ 2) +
        min (2 * cK) 1 * ((∑ l, latticeMom p l ^ 2) * ∑ l, (ξ l).im ^ 2) := by ring
    _ ≤ _ := add_le_add h1 h2
private lemma LimitFormData.symbol_main (F : LimitFormData cK c C Q) (hc : 0 < c) (hK : 0 < cK)
    (hT : latticeMomentumTrigStatement) (hA : AnalyticAtSumOfExponentials)
    (hM : ∀ i l : Fin 4, i ≠ l → HasSum (fun z : Fin 4 → ℤ => Q (0, i) (z, i) * (z l : ℝ) ^ 2) (-2)) :
    (∀ (i j : Fin 4) (p : Fin 4 → ℝ), AnalyticAt ℝ (midpointSymbol Q i j) p) ∧
    (∀ (p : Fin 4 → ℝ) (ξ : Fin 4 → ℂ), p ∈ brillouinBox →
      min (2 * cK) 1 * (4 / Real.pi ^ 2) * momentumNormSq p * ∑ i, ‖ξ i‖ ^ 2 ≤
        (∑ i, ∑ j, (starRingEnd ℂ) (ξ i) * midpointSymbol Q i j p * ξ j).re) ∧
    ∀ (i j : Fin 4) (p : Fin 4 → ℝ), p ∈ brillouinBox →
      ‖midpointSymbol Q i j p - (if i = j then (momentumNormSq p : ℂ) else 0)‖ ≤
        (8 * C * (∑' z, expWeight c 4 z) + 2) * momentumNormSq p ^ 2 := by
  refine ⟨fun i j p => ?_, fun p ξ hp => F.quadratic_lowerBound hc hK hT p hp ξ, fun i j p _ => ?_⟩
  · have e : midpointSymbol Q i j = fun q => ((cosSymbol Q i j q : ℝ) : ℂ) +
        ((4 * Real.sin (q i / 2) * Real.sin (q j / 2) : ℝ) : ℂ) := by
      funext q
      rw [F.symbol_eq hc, Complex.ofReal_add]
    rw [e]
    exact (F.analyticAt_cosSymbol hc hA i j p).add (analyticAt_sin_product i j p)
  · have h1 := F.cosSymbol_near hc hT hM i j p
    have h2 := hT.2.1 p i j
    have e : midpointSymbol Q i j p - (if i = j then (momentumNormSq p : ℂ) else 0) =
        (((cosSymbol Q i j p - ((if i = j then momentumNormSq p else 0) - p i * p j)) +
          (4 * Real.sin (p i / 2) * Real.sin (p j / 2) - p i * p j) : ℝ) : ℂ) := by
      rw [F.symbol_eq hc]
      by_cases h : i = j
      · subst h; simp
        ring
      · simp [h]
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring
end Final
section Extra
variable {cK c C : ℝ} {Q : IntBond → IntBond → ℝ}
private lemma LimitFormData.cosSymbol_transverse (F : LimitFormData cK c C Q) (hc : 0 < c) (i : Fin 4)
    (p : Fin 4 → ℝ) :
    ∑ j, cosSymbol Q i j p * (2 * Real.sin (p j / 2)) = 0 := by
  have hf : PolyGrowth fun u : Fin 4 → ℤ => Real.sin (∑ l, p l * (u l : ℝ) - p i / 2) :=
    PolyGrowth.of_abs_le_one fun z => Real.abs_sin_le_one _
  have h := F.sum_tsum_diff_eq_zero hc i hf
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
  unfold cosSymbol
  rw [← tsum_mul_right]
  refine tsum_congr fun u => ?_
  have e1 : ∑ l, p l * (((u + Pi.single j 1 : Fin 4 → ℤ) l : ℤ) : ℝ) = ∑ l, p l * (u l : ℝ) + p j := by
    simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
    congr 1
    simp [Pi.single_apply]
  rw [e1, phase_eq]
  have a1 : ∑ l, p l * (u l : ℝ) + p j - p i / 2 = (∑ l, p l * (u l : ℝ) + (p j - p i) / 2) + p j / 2 := by ring
  have a2 : ∑ l, p l * (u l : ℝ) - p i / 2 = (∑ l, p l * (u l : ℝ) + (p j - p i) / 2) - p j / 2 := by ring
  rw [a1, a2, Real.sin_add, Real.sin_sub]
  ring
private lemma LimitFormData.cosSymbol_symm (F : LimitFormData cK c C Q) (hs : ∀ b b', Q b b' = Q b' b)
    (i j : Fin 4) (p : Fin 4 → ℝ) :
    cosSymbol Q i j p = cosSymbol Q j i p := by
  unfold cosSymbol
  refine Eq.trans (tsum_congr fun z => ?_) ((Equiv.neg (Fin 4 → ℤ)).tsum_eq
    (fun z => Q (0, j) (z, i) * Real.cos (phase j i p z)))
  have e1 : Q (0, i) (z, j) = Q (0, j) (-z, i) := by
    rw [hs, F.translate]
    simp
  have e2 : phase j i p (-z) = - phase i j p z := by
    rw [phase_eq, phase_eq]
    simp only [Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib]
    ring
  simp only [Equiv.neg_apply]
  rw [e1, e2, Real.cos_neg]
private lemma supNorm_single_le (m : Fin 4) : supNorm (Pi.single m 1) ≤ 1 := by apply _root_.YangMills.DeltaSharedProofs.p501726 <;> assumption
private lemma supNorm_neg (v : Fin 4 → ℤ) : supNorm (-v) = supNorm v := by apply _root_.YangMills.Construction.LatticePaths.supNorm_neg <;> assumption
private lemma abs_gradPart_le (i j : Fin 4) (z : Fin 4 → ℤ) :
    |gradPart i j z| ≤ 4 * Real.exp 2 * Real.exp (-(1 * (supNorm z : ℝ))) := by
  by_cases h : supNorm z ≤ 2
  · have h1 : |gradPart i j z| ≤ 4 := by
      unfold gradPart
      split_ifs <;> norm_num
    have h2 : (supNorm z : ℝ) ≤ 2 := by exact_mod_cast h
    have h3 : 1 ≤ Real.exp 2 * Real.exp (-(1 * (supNorm z : ℝ))) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    nlinarith
  · have c1 : (0 : Fin 4 → ℤ) ≠ z := fun e => h (by simp [← e, supNorm])
    have c2 : (0 : Fin 4 → ℤ) ≠ z + Pi.single j 1 := fun e => h (by
      have : z = - Pi.single j 1 := eq_neg_of_add_eq_zero_left e.symm
      rw [this, supNorm_neg]
      have := supNorm_single_le j
      omega)
    have c3 : (0 : Fin 4 → ℤ) + Pi.single i 1 ≠ z := fun e => h (by
      rw [← e, zero_add]
      have := supNorm_single_le i
      omega)
    have c4 : (0 : Fin 4 → ℤ) + Pi.single i 1 ≠ z + Pi.single j 1 := fun e => h (by
      have : z = Pi.single i 1 + - Pi.single j 1 := by
        rw [zero_add] at e
        rw [e]
        simp
      rw [this]
      have h1 := supNorm_add_le (Pi.single i 1) (- Pi.single j 1)
      rw [supNorm_neg] at h1
      have h2 := supNorm_single_le i
      have h3 := supNorm_single_le j
      omega)
    have : gradPart i j z = 0 := by
      unfold gradPart
      rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4]
      norm_num
    rw [this, abs_zero]
    positivity
private lemma LimitFormData.iteratedDeriv_symbol_le (F : LimitFormData cK c C Q) (hc : 0 < c)
    (hD : IteratedDerivBoundOfExponentialSum) (i j l : Fin 4) (d : ℕ) (p : Fin 4 → ℝ) :
    ‖iteratedDeriv d (fun t : ℝ => midpointSymbol Q i j (Function.update p l t)) (p l)‖ ≤
      C * ∑' z, expWeight c d z + 4 * Real.exp 2 * ∑' z, expWeight 1 d z := by
  have hw1 := summable_expWeight hc d
  have hw2 := summable_expWeight (c := 1) one_pos d
  have hB : ∀ (e : ℕ) (z : Fin 4 → ℤ), ‖((gaugeFixedKernel Q (0, i) (z, j) : ℝ) : ℂ)‖ * |midStep i j z l| ^ e ≤
      C * expWeight c e z + 4 * Real.exp 2 * expWeight 1 e z := by
    intro e z
    have h1 : gaugeFixedKernel Q (0, i) (z, j) = Q (0, i) (z, j) + gradPart i j z := rfl
    have h2 : |midStep i j z l| ^ e ≤ (1 + (supNorm z : ℝ)) ^ e :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_midStep_le i j z l) e
    have h3 : |gaugeFixedKernel Q (0, i) (z, j)| ≤
        C * Real.exp (-(c * supNorm z)) + 4 * Real.exp 2 * Real.exp (-(1 * (supNorm z : ℝ))) := by
      rw [h1]
      exact (abs_add_le _ _).trans (add_le_add (F.abs_le i j z) (abs_gradPart_le i j z))
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ (C * Real.exp (-(c * supNorm z)) + 4 * Real.exp 2 * Real.exp (-(1 * (supNorm z : ℝ)))) *
          (1 + (supNorm z : ℝ)) ^ e :=
          mul_le_mul h3 h2 (by positivity) ((abs_nonneg _).trans h3)
      _ = _ := by unfold expWeight; ring
  have hS : ∀ e : ℕ, Summable fun z => ‖((gaugeFixedKernel Q (0, i) (z, j) : ℝ) : ℂ)‖ * |midStep i j z l| ^ e :=
    fun e =>
    Summable.of_nonneg_of_le (fun z => by positivity) (hB e)
      (((summable_expWeight hc e).mul_left C).add ((summable_expWeight (c := 1) one_pos e).mul_left (4 * Real.exp 2)))
  have e : (fun t : ℝ => midpointSymbol Q i j (Function.update p l t)) =
      fun s : ℝ => ∑' z, ((gaugeFixedKernel Q (0, i) (z, j) : ℝ) : ℂ) * Complex.exp (Complex.I *
        ((s * midStep i j z l + (phase i j p z - p l * midStep i j z l) : ℝ) : ℂ)) := by
    funext t
    unfold midpointSymbol
    refine tsum_congr fun z => ?_
    have e1 : phase i j (Function.update p l t) z = t * midStep i j z l + (phase i j p z - p l * midStep i j z l) := by
      have e2 : phase i j (Function.update p l t) z - phase i j p z = (t - p l) * midStep i j z l := by
        unfold phase
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single l]
        · simp; ring
        · intro b _ hb
          simp [Function.update_of_ne hb]
        · simp
      linarith
    rw [← e1]
    rfl
  rw [e]
  refine (hD _ _ _ hS d (p l)).trans ?_
  refine (Summable.tsum_le_tsum (hB d) (hS d) ((hw1.mul_left C).add (hw2.mul_left (4 * Real.exp 2)))).trans
    (le_of_eq ?_)
  rw [(hw1.mul_left C).tsum_add (hw2.mul_left (4 * Real.exp 2)), tsum_mul_left, tsum_mul_left]
end Extra
theorem symbolPropertiesStatement_holds (h : limitFormSecondMomentStatement)
    (hA : AnalyticAtSumOfExponentials) (hS : limitFormSymmetricStatement)
    (hD : IteratedDerivBoundOfExponentialSum) (hT' : latticeMomentumTrigStatement) :
    symbolPropertiesStatement := by
  intro a _
  refine ⟨0, fun _ => 1, fun _ => one_pos, fun L _ _ T _ _ hT _ => ⟨0, fun y _ _ _ => ?_⟩⟩
  intro c₁ C₁ hc₁
  have hK : 0 < T.coercivity := hT.cK_pos
  refine ⟨min (2 * T.coercivity) 1 * (4 / Real.pi ^ 2), 8 * C₁ * (∑' z, expWeight c₁ 4 z) + 2,
    fun d => C₁ * ∑' z, expWeight c₁ d z + 4 * Real.exp 2 * ∑' z, expWeight 1 d z, ?_, fun k Q hQ => ?_⟩
  · have h1 : 0 < min (2 * T.coercivity) 1 := lt_min (by positivity) one_pos
    positivity
  · have F : LimitFormData T.coercivity c₁ C₁ Q := ⟨hQ.invariant, hQ.decay, hQ.kills_gradients, hQ.coercive⟩
    have hs := hS T hT c₁ C₁ k Q hQ
    refine ⟨F.symbol_main hc₁ hK hT' hA (h T hT c₁ C₁ k Q hc₁ hQ),
      fun i j l d p => F.iteratedDeriv_symbol_le hc₁ hD i j l d p,
      fun i j p => ?_, fun i j p => ?_, fun i p => ?_⟩
    · rw [F.symbol_eq hc₁, Complex.ofReal_im]
    · rw [F.symbol_eq hc₁, F.symbol_eq hc₁, F.cosSymbol_symm hs i j p]
      congr 2
      ring
    · have hb := F.cosSymbol_transverse hc₁ i p
      have e : ∀ j, (midpointSymbol Q i j p - ((4 * Real.sin (p i / 2) * Real.sin (p j / 2) : ℝ) : ℂ)) *
          ((2 * Real.sin (p j / 2) : ℝ) : ℂ) = ((cosSymbol Q i j p * (2 * Real.sin (p j / 2)) : ℝ) : ℂ) := by
        intro j
        rw [F.symbol_eq hc₁]
        push_cast
        ring
      simp only [e]
      rw [← Complex.ofReal_sum, hb, Complex.ofReal_zero]
end YangMills.Construction.LimitForms
end

import YangMills.Construction.LatticeFields.FieldsAndDifferences
import YangMills.Construction.LatticeFields.CompressedGreenDecayProof
import YangMills.Construction.LatticeFields.DifferenceIdentities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.DifferenceIdentities
section Scalar
variable {X : Type}
def SqSummable (g : X → ℝ) : Prop := Summable fun x => g x ^ 2
def innerFn (g h : X → ℝ) : ℝ := ∑' x, g x * h x
def normSqFn (g : X → ℝ) : ℝ := innerFn g g
theorem summable_mul_of_sqSummable {g h : X → ℝ} (hg : SqSummable g) (hh : SqSummable h) :
    Summable fun x => g x * h x := by apply _root_.YangMills.DeltaSharedProofs.p500472 <;> assumption
theorem SqSummable.add {g h : X → ℝ} (hg : SqSummable g) (hh : SqSummable h) :
    SqSummable (fun x => g x + h x) := by apply _root_.YangMills.DeltaSharedProofs.p1251 <;> assumption
theorem SqSummable.const_mul (c : ℝ) {g : X → ℝ} (hg : SqSummable g) :
    SqSummable (fun x => c * g x) := by apply _root_.YangMills.DeltaSharedProofs.p501093 <;> assumption
theorem SqSummable.sub {g h : X → ℝ} (hg : SqSummable g) (hh : SqSummable h) :
    SqSummable (fun x => g x - h x) := by
  have := hg.add (hh.const_mul (-1))
  simpa [SqSummable, sub_eq_add_neg] using this
theorem SqSummable.finset_sum {ι : Type} (t : Finset ι) {g : ι → X → ℝ}
    (hg : ∀ i ∈ t, SqSummable (g i)) : SqSummable (fun x => ∑ i ∈ t, g i x) := by apply _root_.YangMills.DeltaSharedProofs.p501383 <;> assumption
theorem innerFn_comm (g h : X → ℝ) : innerFn g h = innerFn h g := by
  unfold innerFn
  exact tsum_congr fun x => mul_comm _ _
theorem innerFn_sub_left {g g' h : X → ℝ} (hg : SqSummable g) (hg' : SqSummable g')
    (hh : SqSummable h) :
    innerFn (fun x => g x - g' x) h = innerFn g h - innerFn g' h := by
  unfold innerFn
  rw [← (summable_mul_of_sqSummable hg hh).tsum_sub (summable_mul_of_sqSummable hg' hh)]
  exact tsum_congr fun x => by ring
theorem innerFn_sub_right {g h h' : X → ℝ} (hg : SqSummable g) (hh : SqSummable h)
    (hh' : SqSummable h') :
    innerFn g (fun x => h x - h' x) = innerFn g h - innerFn g h' := by
  rw [innerFn_comm, innerFn_sub_left hh hh' hg, innerFn_comm h, innerFn_comm h']
theorem innerFn_const_mul_left (e : ℝ) (g h : X → ℝ) :
    innerFn (fun x => e * g x) h = e * innerFn g h := by
  unfold innerFn
  rw [← tsum_mul_left]
  exact tsum_congr fun x => by ring
theorem innerFn_const_mul_right (e : ℝ) (g h : X → ℝ) :
    innerFn g (fun x => e * h x) = e * innerFn g h := by
  rw [innerFn_comm, innerFn_const_mul_left, innerFn_comm]
theorem innerFn_finset_sum_left {ι : Type} (t : Finset ι) {g : ι → X → ℝ} {h : X → ℝ}
    (hg : ∀ i ∈ t, SqSummable (g i)) (hh : SqSummable h) :
    innerFn (fun x => ∑ i ∈ t, g i x) h = ∑ i ∈ t, innerFn (g i) h := by
  unfold innerFn
  rw [← Summable.tsum_finsetSum fun i hi => summable_mul_of_sqSummable (hg i hi) hh]
  exact tsum_congr fun _ => by rw [Finset.sum_mul]
theorem normSqFn_nonneg (g : X → ℝ) : 0 ≤ normSqFn g :=
  tsum_nonneg fun _ => mul_self_nonneg _
theorem normSqFn_finset_sum {ι : Type} (t : Finset ι) {g : ι → X → ℝ}
    (hg : ∀ i ∈ t, SqSummable (g i)) :
    normSqFn (fun x => ∑ i ∈ t, g i x) = ∑ i ∈ t, ∑ j ∈ t, innerFn (g i) (g j) := by
  unfold normSqFn
  rw [innerFn_finset_sum_left t hg (SqSummable.finset_sum t hg)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [innerFn_comm, innerFn_finset_sum_left t hg (hg i hi)]
  exact Finset.sum_congr rfl fun j _ => innerFn_comm _ _
theorem normSqFn_sub {a b : X → ℝ} (ha : SqSummable a) (hb : SqSummable b) :
    normSqFn (fun x => a x - b x) = normSqFn a + normSqFn b - 2 * innerFn a b := by
  unfold normSqFn
  rw [innerFn_sub_left ha hb (ha.sub hb), innerFn_sub_right ha ha hb, innerFn_sub_right hb ha hb,
    innerFn_comm b a]
  ring
theorem normSqFn_sum_le_card_mul {ι : Type} [Fintype ι] {h : ι → X → ℝ}
    (hh : ∀ i, SqSummable (h i)) :
    normSqFn (fun x => ∑ i, h i x) ≤ Fintype.card ι * ∑ i, normSqFn (h i) := by
  have hs : SqSummable (fun x => ∑ i, h i x) := SqSummable.finset_sum _ fun i _ => hh i
  have hsum : ∀ i ∈ (Finset.univ : Finset ι), Summable fun x => h i x * h i x :=
    fun i _ => summable_mul_of_sqSummable (hh i) (hh i)
  have hr : (Fintype.card ι : ℝ) * ∑ i, normSqFn (h i) =
      ∑' x, (Fintype.card ι : ℝ) * ∑ i, h i x * h i x := by
    rw [tsum_mul_left, Summable.tsum_finsetSum hsum]
    rfl
  rw [hr]
  refine (summable_mul_of_sqSummable hs hs).tsum_le_tsum (fun x => ?_)
    ((summable_sum hsum).mul_left _)
  have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => h i x)
  simp only [Finset.card_univ] at this
  calc (∑ i, h i x) * ∑ i, h i x = (∑ i, h i x) ^ 2 := (sq _).symm
    _ ≤ _ := this
    _ = _ := by simp only [sq]
variable [AddCommGroup X]
theorem SqSummable.comp_add {g : X → ℝ} (hg : SqSummable g) (s : X) :
    SqSummable (fun x => g (x + s)) := by
  unfold SqSummable at hg ⊢
  exact ((Equiv.addRight s).summable_iff (f := fun x => g x ^ 2)).mpr hg
theorem SqSummable.comp_sub {g : X → ℝ} (hg : SqSummable g) (s : X) :
    SqSummable (fun x => g (x - s)) := by
  simpa [sub_eq_add_neg] using hg.comp_add (-s)
theorem innerFn_comp_add (g h : X → ℝ) (s : X) :
    innerFn (fun x => g (x + s)) h = innerFn g (fun x => h (x - s)) := by
  unfold innerFn
  rw [← (Equiv.addRight s).tsum_eq (fun x => g x * h (x - s))]
  exact tsum_congr fun x => by simp
theorem normSqFn_comp_add (g : X → ℝ) (s : X) : normSqFn (fun x => g (x + s)) = normSqFn g := by
  unfold normSqFn innerFn
  exact (Equiv.addRight s).tsum_eq (fun x => g x * g x)
def stepDiff (e : ℝ) (s : X) (g : X → ℝ) : X → ℝ := fun x => e * (g (x + s) - g x)
def stepDiffBack (e : ℝ) (s : X) (g : X → ℝ) : X → ℝ := fun x => e * (g (x - s) - g x)
theorem SqSummable.stepDiff (e : ℝ) (s : X) {g : X → ℝ} (hg : SqSummable g) :
    SqSummable (stepDiff e s g) :=
  ((hg.comp_add s).sub hg).const_mul e
theorem SqSummable.stepDiffBack (e : ℝ) (s : X) {g : X → ℝ} (hg : SqSummable g) :
    SqSummable (stepDiffBack e s g) :=
  ((hg.comp_sub s).sub hg).const_mul e
theorem innerFn_stepDiff (e : ℝ) (s : X) {g h : X → ℝ} (hg : SqSummable g) (hh : SqSummable h) :
    innerFn (stepDiff e s g) h = innerFn g (stepDiffBack e s h) := by
  unfold stepDiff stepDiffBack
  rw [innerFn_const_mul_left, innerFn_const_mul_right, innerFn_sub_left (hg.comp_add s) hg hh,
    innerFn_sub_right hg (hh.comp_sub s) hh, innerFn_comp_add]
theorem stepDiff_comm (e : ℝ) (s t : X) (g : X → ℝ) :
    stepDiff e s (stepDiff e t g) = stepDiff e t (stepDiff e s g) := by
  funext x
  simp only [stepDiff, add_right_comm x s t]
  ring
theorem stepDiff_stepDiffBack_comm (e : ℝ) (s t : X) (g : X → ℝ) :
    stepDiff e s (stepDiffBack e t g) = stepDiffBack e t (stepDiff e s g) := by
  funext x
  simp only [stepDiff, stepDiffBack, sub_add_eq_add_sub]
  ring
theorem innerFn_stepDiff_stepDiff (e : ℝ) (s t : X) {a b : X → ℝ} (ha : SqSummable a)
    (hb : SqSummable b) :
    innerFn (stepDiff e s a) (stepDiff e t b) = innerFn (stepDiffBack e t a) (stepDiffBack e s b) := by
  rw [innerFn_stepDiff e s ha (hb.stepDiff e t), ← stepDiff_stepDiffBack_comm, innerFn_comm,
    innerFn_stepDiff e t (hb.stepDiffBack e s) ha, innerFn_comm]
theorem normSqFn_stepDiffBack (e : ℝ) (s : X) (g : X → ℝ) :
    normSqFn (stepDiffBack e s g) = normSqFn (stepDiff e s g) := by
  have h : stepDiff e s g = fun x => -(stepDiffBack e s g) (x + s) := by
    funext x
    simp only [stepDiff, stepDiffBack, add_sub_cancel_right]
    ring
  rw [h]
  have h2 : normSqFn (fun x => -(stepDiffBack e s g) (x + s)) =
      normSqFn (fun x => (stepDiffBack e s g) (x + s)) := by
    unfold normSqFn innerFn
    exact tsum_congr fun x => by ring
  rw [h2, normSqFn_comp_add]
theorem normSqFn_stepDiff_le (e : ℝ) (s : X) {g : X → ℝ} (hg : SqSummable g) :
    normSqFn (stepDiff e s g) ≤ 4 * e ^ 2 * normSqFn g := by
  have hfwd : normSqFn (stepDiff e s g) = e ^ 2 * normSqFn (fun x => g (x + s) - g x) := by
    unfold stepDiff normSqFn
    rw [innerFn_const_mul_left, innerFn_const_mul_right]
    ring
  have hsub := normSqFn_sub (hg.comp_add s) hg
  have hadd : 0 ≤ normSqFn (fun x => g (x + s)) + normSqFn g +
      2 * innerFn (fun x => g (x + s)) g := by
    have hsq := normSqFn_sub (hg.comp_add s) (hg.const_mul (-1))
    have hp : innerFn (fun x => g (x + s)) (fun x => -1 * g x) =
        -innerFn (fun x => g (x + s)) g := by
      rw [innerFn_const_mul_right]
      ring
    have hn : normSqFn (fun x => -1 * g x) = normSqFn g := by
      unfold normSqFn
      rw [innerFn_const_mul_left, innerFn_const_mul_right]
      ring
    rw [hp, hn] at hsq
    have := normSqFn_nonneg (fun x => g (x + s) - -1 * g x)
    linarith
  rw [normSqFn_comp_add] at hsub hadd
  rw [hfwd, hsub]
  nlinarith [sq_nonneg e, normSqFn_nonneg g, mul_nonneg (sq_nonneg e) hadd]
theorem innerFn_stepDiffBack_stepDiff (e : ℝ) (s t : X) {g : X → ℝ} (hg : SqSummable g) :
    innerFn (stepDiffBack e s (stepDiff e s g)) (stepDiffBack e t (stepDiff e t g)) =
      normSqFn (stepDiff e s (stepDiff e t g)) := by
  rw [← innerFn_stepDiff_stepDiff e t s (hg.stepDiff e s) (hg.stepDiff e t), stepDiff_comm e t s g]
  rfl
end Scalar
section Components
variable {X J : Type} [Fintype J]
theorem tsum_prod_eq_sum_tsum {G : X → J → ℝ} (hnn : ∀ x i, 0 ≤ G x i)
    (hG : ∀ i, Summable fun x => G x i) :
    ∑' p : X × J, G p.1 p.2 = ∑ i, ∑' x, G x i := by
  have hs' : Summable fun q : J × X => G q.2 q.1 :=
    (summable_prod_of_nonneg (fun q => hnn _ _)).mpr ⟨fun i => hG i, Summable.of_finite⟩
  calc ∑' p : X × J, G p.1 p.2
      = ∑' q : J × X, G q.2 q.1 := ((Equiv.prodComm J X).tsum_eq fun p : X × J => G p.1 p.2).symm
    _ = ∑' i, ∑' x, G x i := hs'.tsum_prod
    _ = ∑ i, ∑' x, G x i := tsum_fintype _
theorem sqSummable_component {J : Type} {F : X → J → ℝ}
    (hF : Summable fun p : X × J => F p.1 p.2 ^ 2) (i : J) : SqSummable (fun x => F x i) := by apply _root_.YangMills.DeltaSharedProofs.p501012 <;> assumption
end Components
section Pairs
theorem sum_sum_eq_diag_add_pairs {d : ℕ} (f : Fin d → Fin d → ℝ) :
    ∑ μ, ∑ ν, f μ ν =
      ∑ μ, f μ μ + ∑ p : PlaquetteDirection d, (f p.1.1 p.1.2 + f p.1.2 p.1.1) := by
  have hlt : ∑ p : PlaquetteDirection d, f p.1.1 p.1.2 =
      ∑ q : Fin d × Fin d, if q.1 < q.2 then f q.1 q.2 else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter fun q : Fin d × Fin d => q.1 < q.2)
      (fun q => by simp) (fun q => f q.1 q.2)).symm
  have hgt : ∑ p : PlaquetteDirection d, f p.1.2 p.1.1 =
      ∑ q : Fin d × Fin d, if q.2 < q.1 then f q.1 q.2 else 0 := by
    have h1 : ∑ p : PlaquetteDirection d, f p.1.2 p.1.1 =
        ∑ q : Fin d × Fin d, if q.1 < q.2 then f q.2 q.1 else 0 := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (Finset.univ.filter fun q : Fin d × Fin d => q.1 < q.2)
        (fun q => by simp) (fun q => f q.2 q.1)).symm
    rw [h1, ← (Equiv.prodComm (Fin d) (Fin d)).sum_comp]
    rfl
  have hdiag : ∑ μ, f μ μ = ∑ q : Fin d × Fin d, if q.1 = q.2 then f q.1 q.2 else 0 := by
    rw [Fintype.sum_prod_type]
    simp
  rw [Finset.sum_add_distrib, hlt, hgt, hdiag, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Fintype.sum_prod_type']
  refine Finset.sum_congr rfl fun q _ => ?_
  rcases lt_trichotomy q.1 q.2 with h | h | h
  · simp [h, h.ne, h.le.not_gt]
  · simp [h]
  · simp [h, h.ne', h.le.not_gt]
end Pairs
section Lattice
variable {d N : ℕ} {κ : LatticeShape d} {I : Type}
theorem latticeSpacing_nonneg : 0 ≤ latticeSpacing N := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.latticeSpacing_nonneg <;> assumption
theorem sum_fin_cons_index {r : ℕ} (G : (Fin (r + 1) → Fin d) → ℝ) :
    ∑ i, G i = ∑ μ : Fin d, ∑ j : Fin r → Fin d, G (Fin.cons μ j) := by
  let E : (Fin d × (Fin r → Fin d)) ≃ (Fin (r + 1) → Fin d) :=
    { toFun := fun p => Fin.cons p.1 p.2
      invFun := fun i => (i 0, Fin.tail i)
      left_inv := fun p => by simp
      right_inv := fun i => Fin.cons_self_tail i }
  rw [← E.sum_comp, Fintype.sum_prod_type]
  rfl
def directionIndexEquiv : Fin d ≃ (Fin 1 → Fin d) where
  toFun := directionIndex
  invFun i := i 0
  left_inv _ := rfl
  right_inv i := by
    funext j
    rw [Subsingleton.elim j 0]
    rfl
theorem fieldNorm_sq (F : LatticeField N κ I) : fieldNorm F ^ 2 = fieldInner F F := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldNorm_sq_eq <;> assumption
theorem fieldInner_self_eq [Fintype I] (F : LatticeField N κ I)
    (hF : ∀ i, SqSummable fun x => F x i) :
    fieldInner F F = latticeSpacing N ^ d * ∑ i, normSqFn fun x => F x i := by
  have hc : 0 ≤ latticeSpacing N ^ d := pow_nonneg latticeSpacing_nonneg d
  unfold fieldInner
  rw [tsum_prod_eq_sum_tsum (G := fun x i => latticeSpacing N ^ d * F x i * F x i)
    (fun x i => by rw [mul_assoc]; exact mul_nonneg hc (mul_self_nonneg _))
    (fun i => by
      refine ((summable_mul_of_sqSummable (hF i) (hF i)).mul_left (latticeSpacing N ^ d)).congr
        fun x => ?_
      ring), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold normSqFn innerFn
  rw [← tsum_mul_left]
  exact tsum_congr fun x => by ring
theorem component_tensorGrad_cons {r : ℕ} (F : LatticeTensor N κ r) (μ : Fin d)
    (j : Fin r → Fin d) :
    (fun x => tensorGrad F x (Fin.cons μ j)) =
      stepDiff (latticeSpacing N)⁻¹ (unitStep N κ μ) (fun x => F x j) := by
  funext x
  simp only [tensorGrad, Fin.cons_zero, Fin.tail_cons]
  rfl
theorem sqSummable_tensorGrad {r : ℕ} {F : LatticeTensor N κ r}
    (hF : ∀ i, SqSummable fun x => F x i)
    (i : Fin (r + 1) → Fin d) : SqSummable fun x => tensorGrad F x i :=
  (hF _).stepDiff _ _
theorem fieldInner_tensorGrad {r : ℕ} {F : LatticeTensor N κ r}
    (hF : ∀ i, SqSummable fun x => F x i) :
    fieldInner (tensorGrad F) (tensorGrad F) = latticeSpacing N ^ d *
      ∑ μ : Fin d, ∑ j : Fin r → Fin d,
        normSqFn (stepDiff (latticeSpacing N)⁻¹ (unitStep N κ μ) (fun x => F x j)) := by
  rw [fieldInner_self_eq _ (sqSummable_tensorGrad hF), sum_fin_cons_index]
  simp only [component_tensorGrad_cons]
theorem fieldNorm_le_of_fieldInner_le {J J' : Type} {F : LatticeField N κ J}
    {G : LatticeField N κ J'} {e : ℝ} (he : 0 ≤ e)
    (h : fieldInner F F ≤ 4 * d * e ^ 2 * fieldInner G G) :
    fieldNorm F ≤ 2 * Real.sqrt d * e * fieldNorm G := by
  have hF : 0 ≤ fieldNorm F := Real.sqrt_nonneg _
  have hG : 0 ≤ fieldNorm G := Real.sqrt_nonneg _
  refine (sq_le_sq₀ hF (by positivity)).mp ?_
  rw [fieldNorm_sq, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d), fieldNorm_sq]
  linarith
theorem fieldNorm_tensorGrad_sq (A : LatticeOneForm N κ) (hA : FieldSquareSummable A) :
    fieldNorm (tensorGrad A) ^ 2 = fieldNorm (latticeCurl A) ^ 2 + fieldNorm (latticeDiv A) ^ 2 := by
  let a : Fin d → LatticeSite N κ → ℝ := fun ρ x => A x (directionIndex ρ)
  let b : Fin d → LatticeSite N κ → ℝ := fun ρ => stepDiffBack (latticeSpacing N)⁻¹ (unitStep N κ ρ) (a ρ)
  let T : Fin d → Fin d → ℝ := fun μ ν => normSqFn (stepDiff (latticeSpacing N)⁻¹ (unitStep N κ μ) (a ν))
  let C : Fin d → Fin d → ℝ := fun μ ν => innerFn (b μ) (b ν)
  have hAc : ∀ i, SqSummable fun x => A x i := sqSummable_component hA
  have ha : ∀ ρ, SqSummable (a ρ) := fun ρ => hAc _
  have hb : ∀ ρ, SqSummable (b ρ) := fun ρ => (ha ρ).stepDiffBack _ _
  have hgrad : fieldInner (tensorGrad A) (tensorGrad A) = latticeSpacing N ^ d * ∑ μ, ∑ ν, T μ ν := by
    rw [fieldInner_tensorGrad hAc]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← (directionIndexEquiv (d := d)).sum_comp]
    rfl
  have hcurlp : ∀ p : PlaquetteDirection d, (fun x => latticeCurl A x p) =
      fun x => stepDiff (latticeSpacing N)⁻¹ (unitStep N κ p.1.1) (a p.1.2) x -
        stepDiff (latticeSpacing N)⁻¹ (unitStep N κ p.1.2) (a p.1.1) x :=
    fun _ => rfl
  have hcurl : fieldInner (latticeCurl A) (latticeCurl A) = latticeSpacing N ^ d *
      ∑ p : PlaquetteDirection d, (T p.1.1 p.1.2 + T p.1.2 p.1.1 - 2 * C p.1.1 p.1.2) := by
    rw [fieldInner_self_eq _ (fun p => by
      rw [hcurlp p]
      exact ((ha _).stepDiff _ _).sub ((ha _).stepDiff _ _))]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hcurlp p, normSqFn_sub ((ha _).stepDiff _ _) ((ha _).stepDiff _ _),
      innerFn_stepDiff_stepDiff _ _ _ (ha _) (ha _), innerFn_comm]
  have hdivc : ∀ j : Fin 0 → Fin d, (fun x => latticeDiv A x j) = fun x => ∑ μ, b μ x :=
    fun _ => rfl
  have hdiv : fieldInner (latticeDiv A) (latticeDiv A) = latticeSpacing N ^ d *
      ∑ μ, ∑ ν, C μ ν := by
    rw [fieldInner_self_eq _ (fun j => by
      rw [hdivc j]
      exact SqSummable.finset_sum _ fun μ _ => hb μ)]
    congr 1
    simp only [Fintype.sum_unique, hdivc]
    exact normSqFn_finset_sum _ fun μ _ => hb μ
  rw [fieldNorm_sq, fieldNorm_sq, fieldNorm_sq, hgrad, hcurl, hdiv, sum_sum_eq_diag_add_pairs T,
    sum_sum_eq_diag_add_pairs C, ← mul_add]
  congr 1
  have hdiag : ∀ μ, C μ μ = T μ μ := fun μ => normSqFn_stepDiffBack _ _ _
  have hsym : ∀ p : PlaquetteDirection d, C p.1.2 p.1.1 = C p.1.1 p.1.2 := fun p => innerFn_comm _ _
  simp only [hdiag, hsym, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
theorem latticeCurl_latticeGrad_eq_zero (f : ScalarField N κ) : latticeCurl (latticeGrad f) = 0 := by
  funext x p
  simp only [latticeCurl, forwardDiff, latticeGrad, shiftForward, directionIndex, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul, Pi.zero_apply,
    add_right_comm x (unitStep N κ p.1.1) (unitStep N κ p.1.2)]
  ring
theorem fieldNorm_tensorGrad_tensorGrad {r : ℕ} (F : LatticeTensor N κ r)
    (hFs : FieldSquareSummable F) :
    fieldNorm (tensorGrad (tensorGrad F)) = fieldNorm (tensorLaplacian F) := by
  have hF : ∀ i, SqSummable fun x => F x i := sqSummable_component hFs
  have hlapc : ∀ i, (fun x => tensorLaplacian F x i) =
      fun x => ∑ μ, stepDiffBack (latticeSpacing N)⁻¹ (unitStep N κ μ)
        (stepDiff (latticeSpacing N)⁻¹ (unitStep N κ μ) (fun y => F y i)) x := by
    intro i
    funext x
    change ∑ μ, backwardDiff μ (tensorGrad F) x (Fin.cons μ i) = _
    refine Finset.sum_congr rfl fun μ _ => ?_
    have : (fun y => tensorGrad F y (Fin.cons μ i)) =
        stepDiff (latticeSpacing N)⁻¹ (unitStep N κ μ) (fun y => F y i) :=
      component_tensorGrad_cons F μ i
    change stepDiffBack (latticeSpacing N)⁻¹ (unitStep N κ μ) (fun y => tensorGrad F y (Fin.cons μ i)) x = _
    rw [this]
  unfold fieldNorm
  congr 1
  rw [fieldInner_tensorGrad (sqSummable_tensorGrad hF), fieldInner_self_eq _ (fun i => by
    rw [hlapc i]
    exact SqSummable.finset_sum _ fun μ _ => ((hF i).stepDiff _ _).stepDiffBack _ _)]
  congr 1
  simp only [hlapc]
  have hR : ∀ i : Fin r → Fin d,
      normSqFn (fun x => ∑ μ, stepDiffBack (latticeSpacing N)⁻¹ (unitStep N κ μ)
        (stepDiff (latticeSpacing N)⁻¹ (unitStep N κ μ) (fun y => F y i)) x) =
        ∑ μ : Fin d, ∑ ν : Fin d,
          normSqFn (stepDiff (latticeSpacing N)⁻¹ (unitStep N κ μ)
            (stepDiff (latticeSpacing N)⁻¹ (unitStep N κ ν) (fun y => F y i))) := by
    intro i
    rw [normSqFn_finset_sum _ fun μ _ => ((hF i).stepDiff _ _).stepDiffBack _ _]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
      innerFn_stepDiffBack_stepDiff _ _ _ (hF i)
  have hL : ∀ μ : Fin d, ∑ j : Fin (r + 1) → Fin d,
      normSqFn (stepDiff (latticeSpacing N)⁻¹ (unitStep N κ μ) (fun x => tensorGrad F x j)) =
        ∑ ν : Fin d, ∑ i : Fin r → Fin d,
          normSqFn (stepDiff (latticeSpacing N)⁻¹ (unitStep N κ μ)
            (stepDiff (latticeSpacing N)⁻¹ (unitStep N κ ν) (fun y => F y i))) := by
    intro μ
    rw [sum_fin_cons_index]
    simp only [component_tensorGrad_cons]
  simp only [hR, hL]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
theorem fieldNorm_tensorGrad_le {r : ℕ} (F : LatticeTensor N κ r) (hFs : FieldSquareSummable F) :
    fieldNorm (tensorGrad F) ≤ 2 * Real.sqrt d * (latticeSpacing N)⁻¹ * fieldNorm F := by
  have hF : ∀ i, SqSummable fun x => F x i := sqSummable_component hFs
  have hc : 0 ≤ latticeSpacing N ^ d := pow_nonneg latticeSpacing_nonneg d
  refine fieldNorm_le_of_fieldInner_le (inv_nonneg.mpr latticeSpacing_nonneg) ?_
  rw [fieldInner_tensorGrad hF, fieldInner_self_eq F hF]
  have : ∑ μ : Fin d, ∑ j : Fin r → Fin d,
      normSqFn (stepDiff (latticeSpacing N)⁻¹ (unitStep N κ μ) (fun x => F x j)) ≤
      ∑ _μ : Fin d, ∑ j : Fin r → Fin d,
        4 * ((latticeSpacing N)⁻¹) ^ 2 * normSqFn (fun x => F x j) :=
    Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun j _ => normSqFn_stepDiff_le _ _ (hF j)
  calc _ ≤ latticeSpacing N ^ d * _ := mul_le_mul_of_nonneg_left this hc
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← Finset.mul_sum]
      ring
theorem fieldNorm_tensorGradAdjoint_le {r : ℕ} (F : LatticeTensor N κ (r + 1))
    (hFs : FieldSquareSummable F) :
    fieldNorm (tensorGradAdjoint F) ≤ 2 * Real.sqrt d * (latticeSpacing N)⁻¹ * fieldNorm F := by
  have hF : ∀ i, SqSummable fun x => F x i := sqSummable_component hFs
  have hc : 0 ≤ latticeSpacing N ^ d := pow_nonneg latticeSpacing_nonneg d
  have hcomp : ∀ i : Fin r → Fin d, (fun x => tensorGradAdjoint F x i) =
      fun x => ∑ μ, stepDiffBack (latticeSpacing N)⁻¹ (unitStep N κ μ)
        (fun y => F y (Fin.cons μ i)) x := fun _ => rfl
  refine fieldNorm_le_of_fieldInner_le (inv_nonneg.mpr latticeSpacing_nonneg) ?_
  rw [fieldInner_self_eq _ (fun i => by
    rw [hcomp i]
    exact SqSummable.finset_sum _ fun μ _ => (hF _).stepDiffBack _ _), fieldInner_self_eq F hF,
    sum_fin_cons_index]
  have hstep : ∀ i : Fin r → Fin d, normSqFn (fun x => tensorGradAdjoint F x i) ≤
      (d : ℝ) * ∑ μ : Fin d,
        4 * ((latticeSpacing N)⁻¹) ^ 2 * normSqFn (fun y => F y (Fin.cons μ i)) := by
    intro i
    rw [hcomp i]
    have h1 := normSqFn_sum_le_card_mul (h := fun μ : Fin d =>
      stepDiffBack (latticeSpacing N)⁻¹ (unitStep N κ μ)
      (fun y => F y (Fin.cons μ i))) (fun μ => (hF _).stepDiffBack _ _)
    rw [Fintype.card_fin] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d))
    refine Finset.sum_le_sum fun μ _ => ?_
    rw [normSqFn_stepDiffBack]
    exact normSqFn_stepDiff_le _ _ (hF _)
  calc _ ≤ latticeSpacing N ^ d * ∑ i : Fin r → Fin d,
        ((d : ℝ) * ∑ μ : Fin d,
          4 * ((latticeSpacing N)⁻¹) ^ 2 * normSqFn (fun y => F y (Fin.cons μ i))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hstep i) hc
    _ = _ := by
      simp only [← Finset.mul_sum]
      rw [Finset.sum_comm]
      ring
end Lattice
theorem claim_holds : Claim := by
  intro P κ
  exact
    { norm_tensorGrad_sq := fun A hA => fieldNorm_tensorGrad_sq A hA
      latticeCurl_latticeGrad := fun f _ => latticeCurl_latticeGrad_eq_zero f
      norm_tensorGrad_tensorGrad := fun _ F hF => fieldNorm_tensorGrad_tensorGrad F hF
      norm_tensorGrad_le := fun _ F hF => fieldNorm_tensorGrad_le F hF
      norm_tensorGradAdjoint_le := fun _ F hF => fieldNorm_tensorGradAdjoint_le F hF }
end YangMills.Construction.LatticeFields.DifferenceIdentities

import Mathlib
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeFields
inductive LatticeShape (d : ℕ) : Type where
  | whole : LatticeShape d
  | torus (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) : LatticeShape d
def latticeSpacing (N : ℕ) : ℝ := (N : ℝ)⁻¹
def scaledIntLattice (d N : ℕ) : AddSubgroup (Fin d → ℝ) where
  carrier := {x | ∀ μ, ∃ n : ℤ, x μ = latticeSpacing N * n}
  zero_mem' := fun _ => ⟨0, by simp⟩
  add_mem' := by
    intro a b ha hb μ
    obtain ⟨m, hm⟩ := ha μ
    obtain ⟨n, hn⟩ := hb μ
    exact ⟨m + n, by simp [hm, hn, mul_add]⟩
  neg_mem' := by
    intro a ha μ
    obtain ⟨m, hm⟩ := ha μ
    exact ⟨-m, by simp [hm]⟩
def periodLattice {d : ℕ} (ℓ : Fin d → ℕ) : AddSubgroup (Fin d → ℝ) where
  carrier := {x | ∀ μ, ∃ n : ℤ, x μ = (ℓ μ : ℝ) * n}
  zero_mem' := fun _ => ⟨0, by simp⟩
  add_mem' := by
    intro a b ha hb μ
    obtain ⟨m, hm⟩ := ha μ
    obtain ⟨n, hn⟩ := hb μ
    exact ⟨m + n, by simp [hm, hn, mul_add]⟩
  neg_mem' := by
    intro a ha μ
    obtain ⟨m, hm⟩ := ha μ
    exact ⟨-m, by simp [hm]⟩
def periodSubgroup {d : ℕ} : LatticeShape d → AddSubgroup (Fin d → ℝ)
  | .whole => ⊥
  | .torus ℓ _ => periodLattice ℓ
variable {d : ℕ}
theorem periodSubgroup_le_scaledIntLattice (N : ℕ) [NeZero N] (κ : LatticeShape d) :
    periodSubgroup κ ≤ scaledIntLattice d N := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  cases κ with
  | whole => exact bot_le
  | torus ℓ hℓ =>
    intro x hx μ
    obtain ⟨n, hn⟩ := hx μ
    refine ⟨N * (ℓ μ * n), ?_⟩
    rw [hn, latticeSpacing]
    push_cast
    field_simp
def LatticeSite (N : ℕ) (κ : LatticeShape d) : Type :=
  scaledIntLattice d N ⧸ (periodSubgroup κ).addSubgroupOf (scaledIntLattice d N)
instance (N : ℕ) (κ : LatticeShape d) : AddCommGroup (LatticeSite N κ) :=
  inferInstanceAs (AddCommGroup (scaledIntLattice d N ⧸ (periodSubgroup κ).addSubgroupOf (scaledIntLattice d N)))
def toSite (N : ℕ) (κ : LatticeShape d) : scaledIntLattice d N →+ LatticeSite N κ :=
  QuotientAddGroup.mk' _
theorem toSite_surjective (N : ℕ) (κ : LatticeShape d) : Function.Surjective (toSite N κ) :=
  QuotientAddGroup.mk'_surjective _
theorem toSite_eq_zero_iff (N : ℕ) (κ : LatticeShape d) (v : scaledIntLattice d N) :
    toSite N κ v = 0 ↔ (v : Fin d → ℝ) ∈ periodSubgroup κ := by
  rw [← AddSubgroup.mem_addSubgroupOf]
  exact QuotientAddGroup.eq_zero_iff v
theorem scaledIntLattice_one_le (N : ℕ) [NeZero N] : scaledIntLattice d 1 ≤ scaledIntLattice d N := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  intro x hx μ
  obtain ⟨n, hn⟩ := hx μ
  refine ⟨N * n, ?_⟩
  rw [hn, latticeSpacing, latticeSpacing]
  push_cast
  field_simp
def unitSiteHom (N : ℕ) [NeZero N] (κ : LatticeShape d) : LatticeSite 1 κ →+ LatticeSite N κ :=
  QuotientAddGroup.map _ _ (AddSubgroup.inclusion (scaledIntLattice_one_le (d := d) N)) (by
    intro v hv
    simpa [AddSubgroup.mem_addSubgroupOf] using hv)
theorem unitSiteHom_toSite (N : ℕ) [NeZero N] (κ : LatticeShape d) (v : scaledIntLattice d 1) :
    unitSiteHom N κ (toSite 1 κ v) =
      toSite N κ (AddSubgroup.inclusion (scaledIntLattice_one_le (d := d) N) v) := rfl
def siteDist {N : ℕ} {κ : LatticeShape d} (x x' : LatticeSite N κ) : ℝ :=
  sInf {t | ∃ v : scaledIntLattice d N, toSite N κ v = x - x' ∧ t = ∑ μ, |(v : Fin d → ℝ) μ|}
def siteSetDist {N : ℕ} {κ : LatticeShape d} (U U' : Set (LatticeSite N κ)) : ℝ :=
  sInf {t | ∃ x ∈ U, ∃ x' ∈ U', t = siteDist x x'}
abbrev PlaquetteDirection (d : ℕ) : Type := {p : Fin d × Fin d // p.1 < p.2}
abbrev LatticeBond (N : ℕ) (κ : LatticeShape d) : Type := LatticeSite N κ × Fin d
abbrev LatticePlaquette (N : ℕ) (κ : LatticeShape d) : Type := LatticeSite N κ × PlaquetteDirection d
abbrev LatticeField (N : ℕ) (κ : LatticeShape d) (I : Type) : Type := LatticeSite N κ → I → ℝ
abbrev LatticeTensor (N : ℕ) (κ : LatticeShape d) (r : ℕ) : Type := LatticeField N κ (Fin r → Fin d)
abbrev ScalarField (N : ℕ) (κ : LatticeShape d) : Type := LatticeTensor N κ 0
abbrev LatticeOneForm (N : ℕ) (κ : LatticeShape d) : Type := LatticeTensor N κ 1
abbrev LatticeTwoForm (N : ℕ) (κ : LatticeShape d) : Type := LatticeField N κ (PlaquetteDirection d)
def scalarIndex : Fin 0 → Fin d := Fin.elim0
def directionIndex (μ : Fin d) : Fin 1 → Fin d := fun _ => μ
def ScalarField.eval {N : ℕ} {κ : LatticeShape d} (f : ScalarField N κ) (x : LatticeSite N κ) : ℝ :=
  f x scalarIndex
def LatticeOneForm.coord {N : ℕ} {κ : LatticeShape d} (A : LatticeOneForm N κ) (μ : Fin d)
    (x : LatticeSite N κ) : ℝ :=
  A x (directionIndex μ)
def LatticeOneForm.bondValue {N : ℕ} {κ : LatticeShape d} (A : LatticeOneForm N κ)
    (b : LatticeBond N κ) : ℝ :=
  LatticeOneForm.coord A b.2 b.1
variable {N : ℕ} {κ : LatticeShape d} {I : Type}
def fieldInner (F F' : LatticeField N κ I) : ℝ :=
  ∑' p : LatticeSite N κ × I, latticeSpacing N ^ d * F p.1 p.2 * F' p.1 p.2
def fieldNorm (F : LatticeField N κ I) : ℝ := Real.sqrt (fieldInner F F)
def FieldSquareSummable (F : LatticeField N κ I) : Prop :=
  Summable fun p : LatticeSite N κ × I => F p.1 p.2 ^ 2
def maxAbsCoord (v : I → ℝ) : ℝ := ⨆ i, |v i|
def fieldPointNorm (F : LatticeField N κ I) (x : LatticeSite N κ) : ℝ := maxAbsCoord (F x)
def fieldSupNorm (F : LatticeField N κ I) : ℝ≥0∞ := ⨆ x, ENNReal.ofReal (fieldPointNorm F x)
def mulBase (θ : LatticeSite N κ → ℝ) (F : LatticeField N κ I) : LatticeField N κ I :=
  fun x i => θ x * F x i
def restrictSites (U : Set (LatticeSite N κ)) (F : LatticeField N κ I) : LatticeField N κ I :=
  mulBase (U.indicator 1) F
def restrictBonds (S : Set (LatticeBond N κ)) (A : LatticeOneForm N κ) : LatticeOneForm N κ :=
  fun x i => S.indicator 1 (x, i 0) * A x i
def restrictPlaquettes (S : Set (LatticePlaquette N κ)) (B : LatticeTwoForm N κ) : LatticeTwoForm N κ :=
  fun x p => S.indicator 1 (x, p) * B x p
def unitStep (N : ℕ) (κ : LatticeShape d) (μ : Fin d) : LatticeSite N κ :=
  toSite N κ ⟨Pi.single μ (latticeSpacing N), by
    intro ν
    by_cases h : ν = μ
    · subst h
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.single_eq_of_ne h]⟩⟩
def shiftForward (μ : Fin d) (F : LatticeField N κ I) : LatticeField N κ I :=
  fun x => F (x + unitStep N κ μ)
def shiftBackward (μ : Fin d) (F : LatticeField N κ I) : LatticeField N κ I :=
  fun x => F (x - unitStep N κ μ)
def forwardDiff (μ : Fin d) (F : LatticeField N κ I) : LatticeField N κ I :=
  (latticeSpacing N)⁻¹ • (shiftForward μ F - F)
def backwardDiff (μ : Fin d) (F : LatticeField N κ I) : LatticeField N κ I :=
  (latticeSpacing N)⁻¹ • (shiftBackward μ F - F)
def latticeGrad (f : ScalarField N κ) : LatticeOneForm N κ :=
  fun x i => forwardDiff (i 0) f x scalarIndex
def latticeCurl (A : LatticeOneForm N κ) : LatticeTwoForm N κ :=
  fun x p => forwardDiff p.1.1 A x (directionIndex p.1.2) - forwardDiff p.1.2 A x (directionIndex p.1.1)
def latticeDiv (A : LatticeOneForm N κ) : ScalarField N κ :=
  fun x _ => ∑ μ, backwardDiff μ A x (directionIndex μ)
def latticeCurlAdjoint (B : LatticeTwoForm N κ) : LatticeOneForm N κ :=
  fun x i => ∑ p : PlaquetteDirection d,
    ((if p.1.2 = i 0 then backwardDiff p.1.1 B x p else 0) -
      (if p.1.1 = i 0 then backwardDiff p.1.2 B x p else 0))
def tensorGrad {r : ℕ} (F : LatticeTensor N κ r) : LatticeTensor N κ (r + 1) :=
  fun x i => forwardDiff (i 0) F x (Fin.tail i)
def tensorGradAdjoint {r : ℕ} (F : LatticeTensor N κ (r + 1)) : LatticeTensor N κ r :=
  fun x i => ∑ μ, backwardDiff μ F x (Fin.cons μ i)
def tensorLaplacian {r : ℕ} (F : LatticeTensor N κ r) : LatticeTensor N κ r :=
  tensorGradAdjoint (tensorGrad F)
def IsFieldAdjoint {J : Type} (T : LatticeField N κ I → LatticeField N κ J)
    (S : LatticeField N κ J → LatticeField N κ I) : Prop :=
  ∀ F G, FieldSquareSummable F → FieldSquareSummable G → fieldInner (T F) G = fieldInner F (S G)
def fieldHolderSeminorm (α : ℝ) (F : LatticeField N κ I) : ℝ≥0∞ :=
  ⨆ (x : LatticeSite N κ) (x' : LatticeSite N κ) (_ : 0 < siteDist x x' ∧ siteDist x x' ≤ 1),
    ENNReal.ofReal (siteDist x x' ^ (-α) * maxAbsCoord (F x - F x'))
def unitCube (N : ℕ) (y : LatticeSite 1 κ) : Set (LatticeSite N κ) :=
  {x | ∃ (w : scaledIntLattice d 1) (v : scaledIntLattice d N), toSite 1 κ w = y ∧ toSite N κ v = x ∧
    ∀ μ, (w : Fin d → ℝ) μ ≤ (v : Fin d → ℝ) μ ∧ (v : Fin d → ℝ) μ < (w : Fin d → ℝ) μ + 1}
def doubledCube (N : ℕ) (y : LatticeSite 1 κ) : Set (LatticeSite N κ) :=
  {x | ∃ (w : scaledIntLattice d 1) (v : scaledIntLattice d N), toSite 1 κ w = y ∧ toSite N κ v = x ∧
    ∀ μ, (w : Fin d → ℝ) μ - 1 ≤ (v : Fin d → ℝ) μ ∧ (v : Fin d → ℝ) μ < (w : Fin d → ℝ) μ + 1}
section Adjoint
variable {X : Type}
private theorem summable_mul_of_sq_summable {ι : Type} {u v : ι → ℝ} (hu : Summable fun i => u i ^ 2)
    (hv : Summable fun i => v i ^ 2) : Summable fun i => u i * v i := by
  refine Summable.of_norm_bounded (g := fun i => u i ^ 2 + v i ^ 2) (hu.add hv) fun i => ?_
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|u i| - |v i|), sq_abs (u i), sq_abs (v i), abs_nonneg (u i),
    abs_nonneg (v i)]
abbrev _root_.YangMills.DeltaSharedProofs.p500472 := @summable_mul_of_sq_summable
abbrev _root_.YangMills.SharedProofs.p5943 := @summable_mul_of_sq_summable
private def IsSqSummable (g : X → ℝ) : Prop := Summable fun x => g x ^ 2
private theorem IsSqSummable.add {g h : X → ℝ} (hg : IsSqSummable g) (hh : IsSqSummable h) :
    IsSqSummable (fun x => g x + h x) := by
  have := (Summable.add hg hh).add ((summable_mul_of_sq_summable hg hh).mul_left 2)
  refine this.congr fun x => ?_
  ring
abbrev _root_.YangMills.DeltaSharedProofs.p1251 := @IsSqSummable.add
private theorem IsSqSummable.smul (c : ℝ) {g : X → ℝ} (hg : IsSqSummable g) :
    IsSqSummable (fun x => c * g x) := by
  refine (Summable.mul_left (c ^ 2) hg).congr fun x => ?_
  ring
abbrev _root_.YangMills.DeltaSharedProofs.p501093 := @IsSqSummable.smul
private theorem IsSqSummable.sub {g h : X → ℝ} (hg : IsSqSummable g) (hh : IsSqSummable h) :
    IsSqSummable (fun x => g x - h x) := by
  have := hg.add (hh.smul (-1))
  simpa [IsSqSummable, sub_eq_add_neg] using this
private theorem IsSqSummable.shift [AddCommGroup X] {g : X → ℝ} (hg : IsSqSummable g) (s : X) :
    IsSqSummable (fun x => g (x + s)) := by
  unfold IsSqSummable at hg ⊢
  exact ((Equiv.addRight s).summable_iff (f := fun x => g x ^ 2)).mpr hg
private theorem IsSqSummable.shiftSub [AddCommGroup X] {g : X → ℝ} (hg : IsSqSummable g) (s : X) :
    IsSqSummable (fun x => g (x - s)) := by
  simpa [sub_eq_add_neg] using hg.shift (-s)
private theorem IsSqSummable.ite (c : Prop) [Decidable c] {g : X → ℝ} (hg : IsSqSummable g) :
    IsSqSummable (fun x => if c then g x else 0) := by
  by_cases h : c
  · simpa [h] using hg
  · simp [h, IsSqSummable, summable_zero]
private theorem IsSqSummable.sum {ι : Type} (t : Finset ι) {g : ι → X → ℝ}
    (hg : ∀ i ∈ t, IsSqSummable (g i)) : IsSqSummable (fun x => ∑ i ∈ t, g i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [IsSqSummable, summable_zero]
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self a t)).add
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
abbrev _root_.YangMills.DeltaSharedProofs.p501383 := @IsSqSummable.sum
private def weightedPairing (c : ℝ) (g h : X → ℝ) : ℝ := ∑' x, c * g x * h x
private theorem summable_weightedPairing (c : ℝ) {g h : X → ℝ} (hg : IsSqSummable g)
    (hh : IsSqSummable h) : Summable fun x => c * g x * h x := by
  refine ((summable_mul_of_sq_summable hg hh).mul_left c).congr fun x => ?_
  ring
private theorem weightedPairing_sub_left (c : ℝ) {g g' h : X → ℝ} (hg : IsSqSummable g)
    (hg' : IsSqSummable g') (hh : IsSqSummable h) :
    weightedPairing c (fun x => g x - g' x) h = weightedPairing c g h - weightedPairing c g' h := by
  unfold weightedPairing
  rw [← (summable_weightedPairing c hg hh).tsum_sub (summable_weightedPairing c hg' hh)]
  exact tsum_congr fun x => by ring
private theorem weightedPairing_sub_right (c : ℝ) {g h h' : X → ℝ} (hg : IsSqSummable g)
    (hh : IsSqSummable h) (hh' : IsSqSummable h') :
    weightedPairing c g (fun x => h x - h' x) = weightedPairing c g h - weightedPairing c g h' := by
  unfold weightedPairing
  rw [← (summable_weightedPairing c hg hh).tsum_sub (summable_weightedPairing c hg hh')]
  exact tsum_congr fun x => by ring
private theorem weightedPairing_sum_right (c : ℝ) {ι : Type} (t : Finset ι) {g : X → ℝ}
    {h : ι → X → ℝ} (hg : IsSqSummable g) (hh : ∀ i ∈ t, IsSqSummable (h i)) :
    weightedPairing c g (fun x => ∑ i ∈ t, h i x) = ∑ i ∈ t, weightedPairing c g (h i) := by
  unfold weightedPairing
  rw [← Summable.tsum_finsetSum fun i hi => summable_weightedPairing c hg (hh i hi)]
  exact tsum_congr fun x => by rw [Finset.mul_sum]
private theorem weightedPairing_ite_right (c : ℝ) (q : Prop) [Decidable q] (g h : X → ℝ) :
    weightedPairing c g (fun x => if q then h x else 0) = if q then weightedPairing c g h else 0 := by
  by_cases hq : q <;> simp [hq, weightedPairing]
private theorem weightedPairing_smul_left (c e : ℝ) (g h : X → ℝ) :
    weightedPairing c (fun x => e * g x) h = e * weightedPairing c g h := by
  unfold weightedPairing
  rw [← tsum_mul_left]
  exact tsum_congr fun x => by ring
private theorem weightedPairing_smul_right (c e : ℝ) (g h : X → ℝ) :
    weightedPairing c g (fun x => e * h x) = e * weightedPairing c g h := by
  unfold weightedPairing
  rw [← tsum_mul_left]
  exact tsum_congr fun x => by ring
private theorem weightedPairing_shift [AddCommGroup X] (c : ℝ) (g h : X → ℝ) (s : X) :
    weightedPairing c (fun x => g (x + s)) h = weightedPairing c g (fun x => h (x - s)) := by
  unfold weightedPairing
  rw [← (Equiv.addRight s).tsum_eq (fun x => c * g x * h (x - s))]
  exact tsum_congr fun x => by simp
private def scalarForwardDiff [AddCommGroup X] (e : ℝ) (s : X) (g : X → ℝ) : X → ℝ :=
  fun x => e * (g (x + s) - g x)
private def scalarBackwardDiff [AddCommGroup X] (e : ℝ) (s : X) (g : X → ℝ) : X → ℝ :=
  fun x => e * (g (x - s) - g x)
private theorem IsSqSummable.scalarForwardDiff [AddCommGroup X] (e : ℝ) (s : X) {g : X → ℝ}
    (hg : IsSqSummable g) : IsSqSummable (scalarForwardDiff e s g) :=
  ((hg.shift s).sub hg).smul e
private theorem IsSqSummable.scalarBackwardDiff [AddCommGroup X] (e : ℝ) (s : X) {g : X → ℝ}
    (hg : IsSqSummable g) : IsSqSummable (scalarBackwardDiff e s g) :=
  ((hg.shiftSub s).sub hg).smul e
private theorem weightedPairing_scalarForwardDiff [AddCommGroup X] (c e : ℝ) (s : X) {g h : X → ℝ}
    (hg : IsSqSummable g) (hh : IsSqSummable h) :
    weightedPairing c (scalarForwardDiff e s g) h = weightedPairing c g (scalarBackwardDiff e s h) := by
  unfold scalarForwardDiff scalarBackwardDiff
  rw [weightedPairing_smul_left, weightedPairing_smul_right,
    weightedPairing_sub_left c (hg.shift s) hg hh,
    weightedPairing_sub_right c hg (hh.shiftSub s) hh, weightedPairing_shift]
private theorem isSqSummable_component {J : Type} {F : X → J → ℝ}
    (hF : Summable fun p : X × J => F p.1 p.2 ^ 2) (i : J) : IsSqSummable (fun x => F x i) := by
  have hinj : Function.Injective fun x : X => (x, i) := fun _ _ h => (Prod.ext_iff.mp h).1
  have h := hF.comp_injective hinj
  simpa [IsSqSummable, Function.comp_def] using h
abbrev _root_.YangMills.DeltaSharedProofs.p501012 := @isSqSummable_component
private theorem summable_sq_of_components {J : Type} [Finite J] {F : X → J → ℝ}
    (hF : ∀ i, IsSqSummable (fun x => F x i)) : Summable fun p : X × J => F p.1 p.2 ^ 2 := by
  have hs : Summable fun q : J × X => F q.2 q.1 ^ 2 :=
    (summable_prod_of_nonneg (fun q => sq_nonneg _)).mpr
      ⟨fun i => hF i, Summable.of_finite⟩
  have h := ((Equiv.prodComm X J).summable_iff (f := fun q : J × X => F q.2 q.1 ^ 2)).mpr hs
  simpa [Function.comp_def] using h
abbrev _root_.YangMills.DeltaSharedProofs.p500755 := @summable_sq_of_components
private theorem tsum_eq_sum_weightedPairing {J : Type} [Fintype J] (c : ℝ) {F G : X → J → ℝ}
    (hF : Summable fun p : X × J => F p.1 p.2 ^ 2)
    (hG : Summable fun p : X × J => G p.1 p.2 ^ 2) :
    ∑' p : X × J, c * F p.1 p.2 * G p.1 p.2 =
      ∑ i, weightedPairing c (fun x => F x i) (fun x => G x i) := by
  have hs : Summable fun p : X × J => c * F p.1 p.2 * G p.1 p.2 := by
    refine ((summable_mul_of_sq_summable hF hG).mul_left c).congr fun p => ?_
    ring
  have hs' : Summable fun q : J × X => c * F q.2 q.1 * G q.2 q.1 :=
    (Equiv.prodComm J X).summable_iff.mpr hs
  calc ∑' p : X × J, c * F p.1 p.2 * G p.1 p.2
      = ∑' q : J × X, c * F q.2 q.1 * G q.2 q.1 :=
        ((Equiv.prodComm J X).tsum_eq fun p : X × J => c * F p.1 p.2 * G p.1 p.2).symm
    _ = ∑' i, ∑' x, c * F x i * G x i := hs'.tsum_prod
    _ = ∑ i, weightedPairing c (fun x => F x i) (fun x => G x i) := tsum_fintype _
private def directionIndexEquiv : Fin d ≃ (Fin 1 → Fin d) where
  toFun := directionIndex
  invFun i := i 0
  left_inv _ := rfl
  right_inv i := by
    funext j
    rw [Subsingleton.elim j 0]
    rfl
theorem latticeCurl_isFieldAdjoint :
    IsFieldAdjoint (latticeCurl : LatticeOneForm N κ → LatticeTwoForm N κ) latticeCurlAdjoint := by
  intro A B hA hB
  set c := latticeSpacing N ^ d with hc
  set e := (latticeSpacing N)⁻¹ with he
  let a : Fin d → LatticeSite N κ → ℝ := fun ρ x => A x (directionIndex ρ)
  let b : PlaquetteDirection d → LatticeSite N κ → ℝ := fun p x => B x p
  let u : Fin d → PlaquetteDirection d → LatticeSite N κ → ℝ := fun ρ p x =>
    (if p.1.2 = ρ then scalarBackwardDiff e (unitStep N κ p.1.1) (b p) x else 0) -
      (if p.1.1 = ρ then scalarBackwardDiff e (unitStep N κ p.1.2) (b p) x else 0)
  have ha : ∀ ρ, IsSqSummable (a ρ) := fun ρ => isSqSummable_component hA _
  have hb : ∀ p, IsSqSummable (b p) := fun p => isSqSummable_component hB p
  have hu : ∀ ρ p, IsSqSummable (u ρ p) := fun ρ p =>
    (((hb p).scalarBackwardDiff e _).ite _).sub (((hb p).scalarBackwardDiff e _).ite _)
  have hcurl : ∀ p, (fun x => latticeCurl A x p) =
      fun x => scalarForwardDiff e (unitStep N κ p.1.1) (a p.1.2) x -
        scalarForwardDiff e (unitStep N κ p.1.2) (a p.1.1) x :=
    fun _ => rfl
  have hadj : ∀ i, (fun x => latticeCurlAdjoint B x (directionIndex i)) = fun x => ∑ p, u i p x :=
    fun _ => rfl
  have hcurlSq : FieldSquareSummable (latticeCurl A) := by
    refine summable_sq_of_components fun p => ?_
    rw [hcurl p]
    exact ((ha _).scalarForwardDiff e _).sub ((ha _).scalarForwardDiff e _)
  have hadjSq : FieldSquareSummable (latticeCurlAdjoint B) := by
    refine summable_sq_of_components fun i => ?_
    have hi : i = directionIndex (i 0) := (directionIndexEquiv.right_inv i).symm
    rw [hi, hadj (i 0)]
    exact IsSqSummable.sum _ fun p _ => hu _ p
  unfold fieldInner
  rw [tsum_eq_sum_weightedPairing c hcurlSq hB, tsum_eq_sum_weightedPairing c hA hadjSq,
    ← (directionIndexEquiv (d := d)).sum_comp]
  have hright : ∀ ρ, weightedPairing c (fun x => A x (directionIndexEquiv ρ))
      (fun x => latticeCurlAdjoint B x (directionIndexEquiv ρ)) =
      ∑ p : PlaquetteDirection d,
        ((if p.1.2 = ρ then weightedPairing c (a ρ) (scalarBackwardDiff e (unitStep N κ p.1.1) (b p)) else 0) -
          (if p.1.1 = ρ then weightedPairing c (a ρ) (scalarBackwardDiff e (unitStep N κ p.1.2) (b p)) else 0)) := by
    intro ρ
    change weightedPairing c (a ρ) (fun x => latticeCurlAdjoint B x (directionIndex ρ)) = _
    rw [hadj ρ, weightedPairing_sum_right c _ (ha ρ) fun p _ => hu ρ p]
    refine Finset.sum_congr rfl fun p _ => ?_
    change weightedPairing c (a ρ) (fun x => _ - _) = _
    rw [weightedPairing_sub_right c (ha ρ) (((hb p).scalarBackwardDiff e _).ite _)
        (((hb p).scalarBackwardDiff e _).ite _),
      weightedPairing_ite_right, weightedPairing_ite_right]
  simp only [hright]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hcurl p, weightedPairing_sub_left c ((ha _).scalarForwardDiff e _) ((ha _).scalarForwardDiff e _) (hb p),
    weightedPairing_scalarForwardDiff c e _ (ha _) (hb p), weightedPairing_scalarForwardDiff c e _ (ha _) (hb p),
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp
end Adjoint
end YangMills.Construction.LatticeFields

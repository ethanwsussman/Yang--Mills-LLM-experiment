import YangMills.Construction.LatticeFields.BlockAvgAdjointsProof
import YangMills.Construction.LatticeFields.BlockPartitionMassiveLaplacian
import YangMills.Construction.LatticeFields.TransverseDecompositionProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.BlockPartitionMassiveLaplacian
variable {d : ℕ}
def latticePoint (N : ℕ) (n : Fin d → ℤ) : scaledIntLattice d N :=
  ⟨fun μ => latticeSpacing N * n μ, fun μ => ⟨n μ, rfl⟩⟩
theorem coe_latticePoint (N : ℕ) (n : Fin d → ℤ) (μ : Fin d) :
    ((latticePoint N n : scaledIntLattice d N) : Fin d → ℝ) μ = latticeSpacing N * n μ := rfl
theorem latticeSpacing_one : latticeSpacing 1 = 1 := by simp [latticeSpacing]
theorem period_coord_int {κ : LatticeShape d} {p : Fin d → ℝ} (hp : p ∈ periodSubgroup κ)
    (μ : Fin d) : ∃ m : ℤ, p μ = m := by
  cases κ with
  | whole =>
    have h : p = 0 := (AddSubgroup.mem_bot).mp hp
    exact ⟨0, by simp [h]⟩
  | torus ℓ hℓ =>
    obtain ⟨n, hn⟩ := hp μ
    exact ⟨ℓ μ * n, by rw [hn]; push_cast; ring⟩
theorem toSite_eq_iff {N : ℕ} {κ : LatticeShape d} (v v' : scaledIntLattice d N) :
    toSite N κ v = toSite N κ v' ↔ ((v : Fin d → ℝ) - v') ∈ periodSubgroup κ := by
  rw [← sub_eq_zero, ← map_sub, toSite_eq_zero_iff]
  rfl
theorem eq_zero_of_abs_cast_lt_one {m : ℤ} (h : |(m : ℝ)| < 1) : m = 0 := by
  have h' : |m| < 1 := by exact_mod_cast h
  exact Int.abs_lt_one_iff.mp h'
theorem mem_coarseBlock_iff {N : ℕ} {κ : LatticeShape d} {y : LatticeSite 1 κ}
    {x : LatticeSite N κ} :
    x ∈ coarseBlock N y ↔ ∃ (w : scaledIntLattice d 1) (v : scaledIntLattice d N),
      toSite 1 κ w = y ∧ toSite N κ v = x ∧
      ∀ μ, (w : Fin d → ℝ) μ ≤ (v : Fin d → ℝ) μ ∧ (v : Fin d → ℝ) μ < (w : Fin d → ℝ) μ + 1 :=
  Iff.rfl
theorem exists_mem_coarseBlock (N : ℕ) (κ : LatticeShape d) (x : LatticeSite N κ) :
    ∃ y : LatticeSite 1 κ, x ∈ coarseBlock N y := by
  obtain ⟨v, rfl⟩ := toSite_surjective N κ x
  refine ⟨toSite 1 κ (latticePoint 1 fun μ => ⌊(v : Fin d → ℝ) μ⌋), mem_coarseBlock_iff.mpr
    ⟨latticePoint 1 _, v, rfl, rfl, fun μ => ?_⟩⟩
  simp only [coe_latticePoint, latticeSpacing_one, one_mul]
  exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
theorem coarseBlock_unique {N : ℕ} {κ : LatticeShape d} {x : LatticeSite N κ}
    {y y' : LatticeSite 1 κ} (h : x ∈ coarseBlock N y) (h' : x ∈ coarseBlock N y') : y = y' := by
  obtain ⟨w, v, rfl, hv, hb⟩ := mem_coarseBlock_iff.mp h
  obtain ⟨w', v', rfl, hv', hb'⟩ := mem_coarseBlock_iff.mp h'
  have hp : ((v : Fin d → ℝ) - v') ∈ periodSubgroup κ :=
    (toSite_eq_iff v v').mp (hv.trans hv'.symm)
  refine (toSite_eq_iff w w').mpr ?_
  have hw : ((w : Fin d → ℝ) - w') = (v : Fin d → ℝ) - v' := by
    funext μ
    obtain ⟨m, hm⟩ := period_coord_int hp μ
    obtain ⟨a, ha⟩ := w.2 μ
    obtain ⟨b, hb2⟩ := w'.2 μ
    rw [latticeSpacing_one, one_mul] at ha hb2
    have h1 := hb μ
    have h2 := hb' μ
    have hm' : (v : Fin d → ℝ) μ - (v' : Fin d → ℝ) μ = m := hm
    have hz : a - b - m = 0 := by
      apply eq_zero_of_abs_cast_lt_one
      push_cast
      rw [abs_lt]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hz' : (a : ℝ) - b - m = 0 := by exact_mod_cast hz
    show (w : Fin d → ℝ) μ - (w' : Fin d → ℝ) μ = (v : Fin d → ℝ) μ - (v' : Fin d → ℝ) μ
    rw [hm', ha, hb2]
    linarith
  rw [hw]
  exact hp
def cellSite (N : ℕ) [NeZero N] (κ : LatticeShape d) (w : scaledIntLattice d 1)
    (n : Fin d → Fin N) : LatticeSite N κ :=
  toSite N κ (AddSubgroup.inclusion (scaledIntLattice_one_le (d := d) N) w +
    latticePoint N fun μ => ((n μ : ℕ) : ℤ))
theorem latticeSpacing_mul_self (N : ℕ) [NeZero N] : latticeSpacing N * (N : ℝ) = 1 := by apply _root_.YangMills.Construction.LatticeFields.BlockAveraging.latticeSpacing_mul_cast <;> assumption
theorem latticeSpacing_pos (N : ℕ) [NeZero N] : 0 < latticeSpacing N := by apply _root_.YangMills.Construction.LatticeFields.PointwiseOfDecay.latticeSpacing_pos <;> assumption
theorem latticeSpacing_mul_fin_lt_one (N : ℕ) [NeZero N] (i : Fin N) :
    latticeSpacing N * ((i : ℕ) : ℝ) < 1 := by
  have h1 : ((i : ℕ) : ℝ) < N := by exact_mod_cast i.2
  have := mul_lt_mul_of_pos_left h1 (latticeSpacing_pos N)
  rwa [latticeSpacing_mul_self] at this
theorem cellSite_injective (N : ℕ) [NeZero N] (κ : LatticeShape d) (w : scaledIntLattice d 1) :
    Function.Injective (cellSite N κ w) := by
  intro n n' h
  have hp := (toSite_eq_iff _ _).mp h
  funext μ
  obtain ⟨m, hm⟩ := period_coord_int hp μ
  have hm' : latticeSpacing N * (((n μ : ℕ) : ℤ) : ℝ) -
      latticeSpacing N * (((n' μ : ℕ) : ℤ) : ℝ) = m := by
    rw [← hm]
    show _ = ((w : Fin d → ℝ) μ + _) - ((w : Fin d → ℝ) μ + _)
    simp [coe_latticePoint]
  have h0 := (latticeSpacing_pos N).le
  have h1 := latticeSpacing_mul_fin_lt_one N (n μ)
  have h2 := latticeSpacing_mul_fin_lt_one N (n' μ)
  have h3 : 0 ≤ latticeSpacing N * ((n μ : ℕ) : ℝ) := by positivity
  have h4 : 0 ≤ latticeSpacing N * ((n' μ : ℕ) : ℝ) := by positivity
  push_cast at hm'
  have hz : m = 0 := by
    apply eq_zero_of_abs_cast_lt_one
    rw [abs_lt, ← hm']
    constructor <;> linarith
  rw [hz] at hm'
  push_cast at hm'
  have h5 : latticeSpacing N * (((n μ : ℕ) : ℝ) - ((n' μ : ℕ) : ℝ)) = 0 := by linarith
  have h6 : ((n μ : ℕ) : ℝ) - ((n' μ : ℕ) : ℝ) = 0 := by
    rcases mul_eq_zero.mp h5 with h7 | h7
    · exact absurd h7 (latticeSpacing_pos N).ne'
    · exact h7
  apply Fin.ext
  have h7 : ((n μ : ℕ) : ℝ) = ((n' μ : ℕ) : ℝ) := by linarith
  exact_mod_cast h7
theorem range_cellSite (N : ℕ) [NeZero N] (κ : LatticeShape d) (w : scaledIntLattice d 1) :
    Set.range (cellSite N κ w) = coarseBlock N (toSite 1 κ w) := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    refine mem_coarseBlock_iff.mpr ⟨w, _, rfl, rfl, fun μ => ?_⟩
    have h1 := latticeSpacing_mul_fin_lt_one N (n μ)
    have h0 := (latticeSpacing_pos N).le
    have h3 : 0 ≤ latticeSpacing N * ((n μ : ℕ) : ℝ) := by positivity
    show (w : Fin d → ℝ) μ ≤ (w : Fin d → ℝ) μ + latticeSpacing N * (((n μ : ℕ) : ℤ) : ℝ) ∧
      (w : Fin d → ℝ) μ + latticeSpacing N * (((n μ : ℕ) : ℤ) : ℝ) < (w : Fin d → ℝ) μ + 1
    push_cast
    constructor <;> linarith
  · intro hx
    obtain ⟨w', v, hw, rfl, hb⟩ := mem_coarseBlock_iff.mp hx
    have hp : ((w' : Fin d → ℝ) - w) ∈ periodSubgroup κ := (toSite_eq_iff w' w).mp hw
    let p' : scaledIntLattice d N :=
      ⟨(w' : Fin d → ℝ) - w, periodSubgroup_le_scaledIntLattice N κ hp⟩
    have hv2 : toSite N κ (v - p') = toSite N κ v := by
      refine (toSite_eq_iff _ _).mpr ?_
      have : (((v - p' : scaledIntLattice d N) : Fin d → ℝ) - v) = -((w' : Fin d → ℝ) - w) := by
        funext μ
        show ((v : Fin d → ℝ) μ - ((w' : Fin d → ℝ) μ - (w : Fin d → ℝ) μ)) - (v : Fin d → ℝ) μ =
          -((w' : Fin d → ℝ) μ - (w : Fin d → ℝ) μ)
        ring
      rw [this]
      exact neg_mem hp
    have hc : ∀ μ, ((v - p' : scaledIntLattice d N) : Fin d → ℝ) μ =
        (v : Fin d → ℝ) μ - ((w' : Fin d → ℝ) μ - (w : Fin d → ℝ) μ) := fun _ => rfl
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
    have key : ∀ μ, ∃ i : Fin N, ((v - p' : scaledIntLattice d N) : Fin d → ℝ) μ =
        (w : Fin d → ℝ) μ + latticeSpacing N * ((i : ℕ) : ℝ) := by
      intro μ
      obtain ⟨a, ha⟩ := (v - p').2 μ
      obtain ⟨b, hb2⟩ := w.2 μ
      rw [latticeSpacing_one, one_mul] at hb2
      have hs := latticeSpacing_mul_self N
      have ha' : ((v - p' : scaledIntLattice d N) : Fin d → ℝ) μ = latticeSpacing N * a := ha
      have hle := (hb μ).1
      have hlt := (hb μ).2
      have hr : ((v - p' : scaledIntLattice d N) : Fin d → ℝ) μ - (w : Fin d → ℝ) μ =
          latticeSpacing N * ((a - N * b : ℤ) : ℝ) := by
        rw [ha', hb2]
        push_cast
        have : latticeSpacing N * ((N : ℝ) * b) = b := by rw [← mul_assoc, hs, one_mul]
        rw [mul_sub, this]
      have hge0 : 0 ≤ latticeSpacing N * ((a - N * b : ℤ) : ℝ) := by
        rw [← hr, hc]; linarith
      have hlt1 : latticeSpacing N * ((a - N * b : ℤ) : ℝ) < 1 := by
        rw [← hr, hc]; linarith
      have hm0 : (0 : ℝ) ≤ ((a - N * b : ℤ) : ℝ) :=
        nonneg_of_mul_nonneg_right hge0 (latticeSpacing_pos N)
      have hmN : ((a - N * b : ℤ) : ℝ) < N := by
        have := mul_lt_mul_of_pos_left hlt1 hN
        rw [← mul_assoc, mul_comm (N : ℝ), hs, one_mul, mul_one] at this
        exact this
      have hm0' : 0 ≤ a - N * b := by exact_mod_cast hm0
      have hmN' : a - N * b < N := by exact_mod_cast hmN
      refine ⟨⟨(a - N * b).toNat, by omega⟩, ?_⟩
      have hcast : (((a - N * b).toNat : ℕ) : ℝ) = ((a - N * b : ℤ) : ℝ) := by
        have : (((a - N * b).toNat : ℕ) : ℤ) = a - N * b := Int.toNat_of_nonneg hm0'
        exact_mod_cast this
      show _ = _ + latticeSpacing N * (((a - N * b).toNat : ℕ) : ℝ)
      rw [hcast, ← hr]
      ring
    choose n hn using key
    refine ⟨n, ?_⟩
    rw [← hv2]
    show toSite N κ _ = _
    congr 1
    apply Subtype.ext
    funext μ
    rw [hn μ]
    show (w : Fin d → ℝ) μ + latticeSpacing N * (((n μ : ℕ) : ℤ) : ℝ) = _
    push_cast
    rfl
theorem coarseBlock_ncard (N : ℕ) [NeZero N] (κ : LatticeShape d) (y : LatticeSite 1 κ) :
    (coarseBlock N y).ncard = N ^ d := by
  obtain ⟨w, rfl⟩ := toSite_surjective 1 κ y
  rw [← range_cellSite, ← Set.image_univ,
    Set.ncard_image_of_injective _ (cellSite_injective N κ w), Set.ncard_univ,
    Nat.card_eq_fintype_card]
  simp
theorem finite_torus_sites (N : ℕ) [NeZero N] (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Finite (LatticeSite N (LatticeShape.torus ℓ hℓ)) := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.finite_torusSites <;> assumption
theorem directionIndex_zero (i : Fin 1 → Fin d) : directionIndex (i 0) = i := by apply _root_.YangMills.Construction.LatticeFields.BlockAveraging.directionIndex_apply_zero <;> assumption
theorem coarseBlock_unit (κ : LatticeShape d) (y : LatticeSite 1 κ) : coarseBlock 1 y = {y} := by
  ext x
  simp only [Set.mem_singleton_iff]
  constructor
  · intro h
    obtain ⟨w, v, rfl, rfl, hb⟩ := mem_coarseBlock_iff.mp h
    congr 1
    apply Subtype.ext
    funext μ
    obtain ⟨a, ha⟩ := v.2 μ
    obtain ⟨b, hb2⟩ := w.2 μ
    rw [latticeSpacing_one, one_mul] at ha hb2
    have h1 := hb μ
    rw [ha, hb2] at h1
    have hz : a - b = 0 := by
      apply eq_zero_of_abs_cast_lt_one
      push_cast
      have h3 : (b : ℝ) ≤ a := h1.1
      have h4 : (a : ℝ) < b + 1 := h1.2
      have h5 : b ≤ a := by exact_mod_cast h3
      have h6 : a < b + 1 := by exact_mod_cast h4
      have h7 : a = b := by omega
      rw [h7]
      simp
    have hz' : a = b := by omega
    rw [ha, hb2, hz']
  · rintro rfl
    obtain ⟨w, rfl⟩ := toSite_surjective 1 κ x
    exact mem_coarseBlock_iff.mpr ⟨w, w, rfl, rfl, fun μ => ⟨le_rfl, lt_add_one _⟩⟩
theorem blockExitFace_unit (κ : LatticeShape d) (y : LatticeSite 1 κ) (μ : Fin d) :
    blockExitFace 1 y μ = {y} := by
  ext x
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, v, hw, hv, hb, -⟩
    have hx : x ∈ coarseBlock 1 y := mem_coarseBlock_iff.mpr ⟨w, v, hw, hv, hb⟩
    rw [coarseBlock_unit] at hx
    exact hx
  · rintro rfl
    obtain ⟨w, rfl⟩ := toSite_surjective 1 κ x
    refine ⟨w, w, rfl, rfl, fun μ => ⟨le_rfl, lt_add_one _⟩, ?_⟩
    rw [latticeSpacing_one]
    ring
theorem siteBlockAvg_unit {κ : LatticeShape d} (f : ScalarField 1 κ) : siteBlockAvg f = f := by
  funext y i
  show ∑ᶠ x ∈ coarseBlock 1 y, latticeSpacing 1 ^ d * ScalarField.eval f x = _
  rw [coarseBlock_unit, finsum_mem_singleton, latticeSpacing_one, one_pow, one_mul]
  show f y scalarIndex = f y i
  rw [Subsingleton.elim i scalarIndex]
theorem bondBlockAvg_unit {κ : LatticeShape d} (A : LatticeOneForm 1 κ) : bondBlockAvg A = A := by
  funext y i
  show ∑ᶠ x ∈ coarseBlock 1 y, latticeSpacing 1 ^ d *
    ∑ j ∈ Finset.range 1, latticeSpacing 1 *
      LatticeOneForm.coord A (i 0) (x + j • unitStep 1 κ (i 0)) = _
  rw [coarseBlock_unit, finsum_mem_singleton, latticeSpacing_one, one_pow, one_mul]
  simp only [Finset.range_one, Finset.sum_singleton, zero_smul, add_zero, one_mul]
  show A y (directionIndex (i 0)) = A y i
  rw [directionIndex_zero]
theorem exitFaceAvg_unit {κ : LatticeShape d} (A : LatticeOneForm 1 κ) : exitFaceAvg A = A := by
  funext y i
  show ∑ᶠ x ∈ blockExitFace 1 y (i 0), latticeSpacing 1 ^ (d - 1) *
    LatticeOneForm.coord A (i 0) x = _
  rw [blockExitFace_unit, finsum_mem_singleton, latticeSpacing_one, one_pow, one_mul]
  show A y (directionIndex (i 0)) = A y i
  rw [directionIndex_zero]
theorem eval_deltaField_self {N : ℕ} {κ : LatticeShape d} (x : LatticeSite N κ)
    (i : Fin 0 → Fin d) : ScalarField.eval (deltaField x i : ScalarField N κ) x = 1 := by
  have hi : scalarIndex = i := Subsingleton.elim _ _
  simp [ScalarField.eval, deltaField, hi]
theorem eval_deltaField_of_ne {N : ℕ} {κ : LatticeShape d} {x x' : LatticeSite N κ} (h : x' ≠ x)
    (i : Fin 0 → Fin d) : ScalarField.eval (deltaField x i : ScalarField N κ) x' = 0 := by
  simp [ScalarField.eval, deltaField, h]
theorem siteBlockAvg_deltaField {N : ℕ} {κ : LatticeShape d} (x : LatticeSite N κ)
    (y : LatticeSite 1 κ) (i i' : Fin 0 → Fin d) :
    siteBlockAvg (deltaField x i : ScalarField N κ) y i' =
      (coarseBlock N y).indicator (fun _ => latticeSpacing N ^ d) x := by
  show ∑ᶠ x' ∈ coarseBlock N y, latticeSpacing N ^ d *
    ScalarField.eval (deltaField x i : ScalarField N κ) x' = _
  rw [finsum_mem_def, finsum_eq_single _ x]
  · by_cases h : x ∈ coarseBlock N y <;> simp [h, eval_deltaField_self]
  · intro x' hx'
    by_cases h : x' ∈ coarseBlock N y <;> simp [h, eval_deltaField_of_ne hx']
theorem eval_siteBlockAvgAdj {N : ℕ} [NeZero N] {κ : LatticeShape d} (ω : ScalarField 1 κ)
    {x : LatticeSite N κ} {y : LatticeSite 1 κ} (h : x ∈ coarseBlock N y) :
    ScalarField.eval (siteBlockAvgAdj ω : ScalarField N κ) x = ScalarField.eval ω y := by
  show (latticeSpacing N ^ d)⁻¹ *
    fieldInner (siteBlockAvg (deltaField x scalarIndex : ScalarField N κ)) ω = ω y scalarIndex
  have hne : latticeSpacing N ^ d ≠ 0 := pow_ne_zero _ (latticeSpacing_pos N).ne'
  unfold fieldInner
  rw [tsum_eq_single (y, scalarIndex)]
  · simp only [siteBlockAvg_deltaField, Set.indicator_of_mem h, latticeSpacing_one, one_pow,
      one_mul]
    field_simp
  · rintro ⟨y', i'⟩ hp
    have hy : y' ≠ y := fun e => hp (by rw [e, Subsingleton.elim i' scalarIndex])
    have hx : x ∉ coarseBlock N y' := fun hx => hy (coarseBlock_unique hx h)
    simp only [siteBlockAvg_deltaField, Set.indicator_of_notMem hx, mul_zero, zero_mul]
theorem blocksPartitionSites_holds (N : ℕ) [NeZero N] (κ : LatticeShape d) :
    BlocksPartitionSites N κ := by
  refine ⟨coarseBlock_ncard N κ, fun x => ?_, fun ω y x h => eval_siteBlockAvgAdj ω h⟩
  obtain ⟨y, hy⟩ := exists_mem_coarseBlock N κ x
  exact ⟨y, hy, fun y' hy' => coarseBlock_unique hy' hy⟩
theorem averagesTrivialAtUnitSpacing_holds (κ : LatticeShape d) :
    AveragesTrivialAtUnitSpacing κ :=
  ⟨siteBlockAvg_unit, bondBlockAvg_unit, exitFaceAvg_unit⟩
theorem fieldInner_deltaField {N : ℕ} {κ : LatticeShape d} {I : Type} (x : LatticeSite N κ)
    (i : I) (B : LatticeField N κ I) :
    fieldInner (deltaField x i : LatticeField N κ I) B = latticeSpacing N ^ d * B x i := by apply _root_.YangMills.Construction.LatticeFields.BlockAvgDuality.fieldInner_deltaField <;> assumption
theorem bondBlockAvgAdj_unit {κ : LatticeShape d} (B : LatticeOneForm 1 κ) :
    bondBlockAvgAdj B = B := by
  funext x i
  show (latticeSpacing 1 ^ d)⁻¹ * fieldInner (bondBlockAvg (deltaField x i : LatticeOneForm 1 κ)) B = _
  rw [bondBlockAvg_unit, fieldInner_deltaField, latticeSpacing_one]
  simp
section FiniteSites
variable {N : ℕ} {κ : LatticeShape d} {I : Type}
theorem fieldInner_comm (F G : LatticeField N κ I) : fieldInner F G = fieldInner G F :=
  tsum_congr fun _ => by ring
theorem fieldNorm_sq (F : LatticeField N κ I) : fieldNorm F ^ 2 = fieldInner F F := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldNorm_sq_eq <;> assumption
variable [Finite (LatticeSite N κ)] [Finite I]
theorem fieldInner_add_left (F F' G : LatticeField N κ I) :
    fieldInner (F + F') G = fieldInner F G + fieldInner F' G := by apply _root_.YangMills.Construction.LatticeFields.Transverse.fieldInner_add_left <;> assumption
theorem fieldInner_sub_left (F F' G : LatticeField N κ I) :
    fieldInner (F - F') G = fieldInner F G - fieldInner F' G := by apply _root_.YangMills.SharedProofs.p65939 <;> assumption
omit [Finite (LatticeSite N κ)] [Finite I] in
theorem fieldInner_smul_left (c : ℝ) (F G : LatticeField N κ I) :
    fieldInner (c • F) G = c * fieldInner F G := by apply _root_.YangMills.Construction.LatticeFields.Transverse.fieldInner_smul_left <;> assumption
def directionEquiv : Fin d ≃ (Fin 1 → Fin d) where
  toFun := directionIndex
  invFun i := i 0
  left_inv _ := rfl
  right_inv := directionIndex_zero
theorem fieldInner_latticeGrad (f : ScalarField N κ) (B : LatticeOneForm N κ) :
    fieldInner (latticeGrad f) B = fieldInner f (latticeDiv B) := by
  have := Fintype.ofFinite (LatticeSite N κ)
  set c := latticeSpacing N ^ d with hc
  set e := (latticeSpacing N)⁻¹ with he
  let g : LatticeSite N κ → ℝ := fun x => f x scalarIndex
  let b : Fin d → LatticeSite N κ → ℝ := fun μ x => B x (directionIndex μ)
  have hL : fieldInner (latticeGrad f) B =
      ∑ μ, ∑ x, c * (e * (g (x + unitStep N κ μ) - g x)) * b μ x := by
    unfold fieldInner
    rw [tsum_fintype, Fintype.sum_prod_type_right, ← (directionEquiv (d := d)).sum_comp]
    rfl
  have hR : fieldInner f (latticeDiv B) =
      ∑ μ, ∑ x, c * g x * (e * (b μ (x - unitStep N κ μ) - b μ x)) := by
    unfold fieldInner
    have h : ∀ x, (∑ i : Fin 0 → Fin d, latticeSpacing N ^ d * f x i * latticeDiv B x i) =
        ∑ μ, c * g x * (e * (b μ (x - unitStep N κ μ) - b μ x)) := by
      intro x
      rw [Fintype.sum_unique, ← Finset.mul_sum,
        Subsingleton.elim (default : Fin 0 → Fin d) scalarIndex]
      rfl
    rw [tsum_fintype, Fintype.sum_prod_type, Finset.sum_congr rfl fun x _ => h x, Finset.sum_comm]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hshift : ∑ x, g (x + unitStep N κ μ) * b μ x = ∑ x, g x * b μ (x - unitStep N κ μ) := by
    rw [← Equiv.sum_comp (Equiv.addRight (unitStep N κ μ))
      (fun x => g x * b μ (x - unitStep N κ μ))]
    simp
  calc ∑ x, c * (e * (g (x + unitStep N κ μ) - g x)) * b μ x
      = c * e * (∑ x, g (x + unitStep N κ μ) * b μ x - ∑ x, g x * b μ x) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ = c * e * (∑ x, g x * b μ (x - unitStep N κ μ) - ∑ x, g x * b μ x) := by rw [hshift]
    _ = ∑ x, c * g x * (e * (b μ (x - unitStep N κ μ) - b μ x)) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
end FiniteSites
theorem sum_plaquette_terms (C : Fin d → Fin d → ℝ) (hC : ∀ ν, C ν ν = 0) (ν : Fin d) :
    ∑ p : PlaquetteDirection d, ((if p.1.2 = ν then C p.1.1 p.1.2 else 0) +
      (if p.1.1 = ν then C p.1.2 p.1.1 else 0)) = ∑ μ, C μ ν := by
  have h1 : ∑ p : PlaquetteDirection d, ((if p.1.2 = ν then C p.1.1 p.1.2 else 0) +
      (if p.1.1 = ν then C p.1.2 p.1.1 else 0)) =
      ∑ q : Fin d × Fin d, if q.1 < q.2 then ((if q.2 = ν then C q.1 q.2 else 0) +
        (if q.1 = ν then C q.2 q.1 else 0)) else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) (fun q : Fin d × Fin d =>
      (if q.2 = ν then C q.1 q.2 else 0) + (if q.1 = ν then C q.2 q.1 else 0))).symm
  have h2 : ∀ μ ρ : Fin d, (if μ < ρ then ((if ρ = ν then C μ ρ else 0) +
      (if μ = ν then C ρ μ else 0)) else 0) =
      (if μ < ρ then (if ρ = ν then C μ ρ else 0) else 0) +
        (if μ < ρ then (if μ = ν then C ρ μ else 0) else 0) := by
    intro μ ρ
    split_ifs <;> simp
  have h3 : ∀ μ : Fin d, ∑ ρ, (if μ < ρ then (if ρ = ν then C μ ρ else 0) else 0) =
      if μ < ν then C μ ν else 0 := by
    intro μ
    rw [Finset.sum_eq_single ν]
    · simp
    · intro ρ _ hρ
      simp [hρ]
    · simp
  have h4 : ∀ ρ : Fin d, ∑ μ, (if μ < ρ then (if μ = ν then C ρ μ else 0) else 0) =
      if ν < ρ then C ρ ν else 0 := by
    intro ρ
    rw [Finset.sum_eq_single ν]
    · simp
    · intro μ _ hμ
      simp [hμ]
    · simp
  rw [h1, Fintype.sum_prod_type]
  simp only [h2, Finset.sum_add_distrib, h3]
  rw [Finset.sum_comm (f := fun μ ρ => if μ < ρ then (if μ = ν then C ρ μ else 0) else 0)]
  simp only [h4]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rcases lt_trichotomy μ ν with h | h | h
  · simp [h, not_lt.mpr h.le]
  · simp [h, hC]
  · simp [h, not_lt.mpr h.le]
theorem tensorLaplacian_eq_curl_add_grad {N : ℕ} {κ : LatticeShape d} (A : LatticeOneForm N κ) :
    tensorLaplacian A = latticeCurlAdjoint (latticeCurl A) + latticeGrad (latticeDiv A) := by
  funext x i
  obtain ⟨ν, rfl⟩ : ∃ ν, i = directionIndex ν := ⟨i 0, (directionIndex_zero i).symm⟩
  set e := (latticeSpacing N)⁻¹ with he
  let a : Fin d → LatticeSite N κ → ℝ := fun ρ y => A y (directionIndex ρ)
  let s : Fin d → LatticeSite N κ := unitStep N κ
  let cu : Fin d → Fin d → LatticeSite N κ → ℝ := fun μ ρ y =>
    e * (a ρ (y + s μ) - a ρ y) - e * (a μ (y + s ρ) - a μ y)
  let C : Fin d → Fin d → ℝ := fun μ ρ => e * (cu μ ρ (x - s μ) - cu μ ρ x)
  have hadj : latticeCurlAdjoint (latticeCurl A) x (directionIndex ν) =
      ∑ p : PlaquetteDirection d, ((if p.1.2 = ν then C p.1.1 p.1.2 else 0) +
        (if p.1.1 = ν then C p.1.2 p.1.1 else 0)) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    have h1 : backwardDiff p.1.1 (latticeCurl A) x p = C p.1.1 p.1.2 := rfl
    have h2 : backwardDiff p.1.2 (latticeCurl A) x p = -C p.1.2 p.1.1 := by
      show e * (cu p.1.1 p.1.2 (x - s p.1.2) - cu p.1.1 p.1.2 x) =
        -(e * (cu p.1.2 p.1.1 (x - s p.1.2) - cu p.1.2 p.1.1 x))
      simp only [cu]
      ring
    show (if p.1.2 = ν then backwardDiff p.1.1 (latticeCurl A) x p else 0) -
      (if p.1.1 = ν then backwardDiff p.1.2 (latticeCurl A) x p else 0) = _
    rw [h1, h2]
    split_ifs <;> ring
  have hC : ∀ ν, C ν ν = 0 := fun ν => by simp [C, cu]
  have hlap : tensorLaplacian A x (directionIndex ν) =
      ∑ μ, e * (e * (a ν (x - s μ + s μ) - a ν (x - s μ)) - e * (a ν (x + s μ) - a ν x)) := rfl
  have hG : latticeGrad (latticeDiv A) x (directionIndex ν) =
      ∑ μ, e * (e * (a μ (x + s ν - s μ) - a μ (x + s ν)) - e * (a μ (x - s μ) - a μ x)) := by
    show e * ((∑ μ, e * (a μ (x + s ν - s μ) - a μ (x + s ν))) -
      ∑ μ, e * (a μ (x - s μ) - a μ x)) = _
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  show tensorLaplacian A x (directionIndex ν) =
    latticeCurlAdjoint (latticeCurl A) x (directionIndex ν) +
      latticeGrad (latticeDiv A) x (directionIndex ν)
  rw [hlap, hadj, sum_plaquette_terms C hC ν, hG, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hc : x - s μ + s ν = x + s ν - s μ := by abel
  simp only [C, cu, hc]
  ring
theorem latticeGrad_sub {N : ℕ} {κ : LatticeShape d} (f g : ScalarField N κ) :
    latticeGrad (f - g) = latticeGrad f - latticeGrad g := by
  funext x i
  show (latticeSpacing N)⁻¹ *
      ((f - g) (x + unitStep N κ (i 0)) scalarIndex - (f - g) x scalarIndex) =
    (latticeSpacing N)⁻¹ * (f (x + unitStep N κ (i 0)) scalarIndex - f x scalarIndex) -
      (latticeSpacing N)⁻¹ * (g (x + unitStep N κ (i 0)) scalarIndex - g x scalarIndex)
  simp only [Pi.sub_apply]
  ring
theorem latticeGrad_zero {N : ℕ} {κ : LatticeShape d} :
    latticeGrad (0 : ScalarField N κ) = 0 := by
  simpa using latticeGrad_sub (0 : ScalarField N κ) 0
theorem tensorLaplacian_zero {N : ℕ} {κ : LatticeShape d} :
    tensorLaplacian (0 : ScalarField N κ) = 0 := by
  funext x i
  simp [tensorLaplacian, tensorGradAdjoint, tensorGrad, backwardDiff, forwardDiff, shiftForward,
    shiftBackward]
section Torus
variable {N : ℕ} [NeZero N] {ℓ : Fin d → ℕ} {hℓ : ∀ μ, 1 ≤ ℓ μ}
theorem fieldInner_sub_kerLaplacianProj (h₂ : KernelProjectionUnique.Claim)
    (f g : ScalarField N (LatticeShape.torus ℓ hℓ)) :
    fieldInner (f - kerLaplacianProj f) (kerLaplacianProj g) = 0 :=
  (h₂ d N ℓ hℓ f).1.2 _ (h₂ d N ℓ hℓ g).1.1
theorem fieldInner_kerLaplacianProj_left (h₂ : KernelProjectionUnique.Claim)
    (f g : ScalarField N (LatticeShape.torus ℓ hℓ)) :
    fieldInner (kerLaplacianProj f) g =
      fieldInner (kerLaplacianProj f) (kerLaplacianProj g) := by
  have := finite_torus_sites N ℓ hℓ
  have h := fieldInner_sub_kerLaplacianProj h₂ g f
  rw [fieldInner_sub_left, sub_eq_zero] at h
  rw [fieldInner_comm, h, fieldInner_comm]
theorem fieldInner_massiveLaplacian (h₁ : BlockAvgAdjointFacts) (a : ℝ)
    (A B : LatticeOneForm N (LatticeShape.torus ℓ hℓ)) :
    fieldInner (massiveLaplacian a A) B =
      fieldInner (latticeCurl A) (latticeCurl B) +
        fieldInner (kerLaplacianProj (latticeDiv A)) (latticeDiv B) +
        a * fieldInner (bondBlockAvg A) (bondBlockAvg B) := by
  have hN := finite_torus_sites N ℓ hℓ
  have h1 := finite_torus_sites 1 ℓ hℓ
  have hcurl : fieldInner (latticeCurlAdjoint (latticeCurl A)) B =
      fieldInner (latticeCurl A) (latticeCurl B) := by
    rw [fieldInner_comm, ← latticeCurl_isFieldAdjoint B (latticeCurl A) Summable.of_finite
      Summable.of_finite, fieldInner_comm]
  have hQ : fieldInner (bondBlockAvgAdj (bondBlockAvg A) : LatticeOneForm N (LatticeShape.torus ℓ hℓ)) B =
      fieldInner (bondBlockAvg A) (bondBlockAvg B) := by
    rw [fieldInner_comm, ← (h₁ d N (LatticeShape.torus ℓ hℓ)).2.2.2 B (bondBlockAvg A)
      Summable.of_finite Summable.of_finite, fieldInner_comm]
  unfold massiveLaplacian
  rw [fieldInner_add_left, fieldInner_add_left, fieldInner_smul_left, hcurl, hQ,
    fieldInner_latticeGrad]
theorem torusMassiveLaplacianIdentities_holds (h₁ : BlockAvgAdjointFacts)
    (h₂ : KernelProjectionUnique.Claim) (N : ℕ) [NeZero N] (ℓ : Fin d → ℕ)
    (hℓ : ∀ μ, 1 ≤ ℓ μ) (a : ℝ) : TorusMassiveLaplacianIdentities N ℓ hℓ a := by
  refine ⟨tensorLaplacian_eq_curl_add_grad, fun A => ?_, fun A B => ?_, fun A => ?_⟩
  · unfold massiveLaplacian massiveLaplacianAlt kerLaplacianProjCompl
    rw [tensorLaplacian_eq_curl_add_grad, latticeGrad_sub]
    abel
  · rw [fieldInner_comm A, fieldInner_massiveLaplacian h₁, fieldInner_massiveLaplacian h₁,
      fieldInner_comm (latticeCurl B), fieldInner_comm (bondBlockAvg B),
      fieldInner_kerLaplacianProj_left h₂, fieldInner_kerLaplacianProj_left h₂ (latticeDiv B),
      fieldInner_comm (kerLaplacianProj (latticeDiv B))]
  · rw [fieldInner_comm, fieldInner_massiveLaplacian h₁, fieldInner_kerLaplacianProj_left h₂,
      fieldNorm_sq, fieldNorm_sq, fieldNorm_sq]
end Torus
theorem torusUnitSpacingIdentities_holds (h₂ : KernelProjectionUnique.Claim) (ℓ : Fin d → ℕ)
    (hℓ : ∀ μ, 1 ≤ ℓ μ) (a : ℝ) : TorusUnitSpacingIdentities ℓ hℓ a := by
  have hker : siteBlockAvgKer 1 ℓ hℓ = {0} := by
    ext l
    show siteBlockAvg l = 0 ↔ l = 0
    rw [siteBlockAvg_unit]
  have hR : ∀ f : ScalarField 1 (LatticeShape.torus ℓ hℓ), kerLaplacianProj f = 0 := by
    intro f
    obtain ⟨l, hl, he⟩ := (h₂ d 1 ℓ hℓ f).1.1
    rw [hker] at hl
    rw [← he, Set.mem_singleton_iff.mp hl, tensorLaplacian_zero]
  refine ⟨hker, hR, fun f => ?_, bondBlockAvg_unit, fun A => ?_⟩
  · unfold kerLaplacianProjCompl
    rw [hR, sub_zero]
  · unfold massiveLaplacian massiveLaplacianUnit
    rw [hR, latticeGrad_zero, bondBlockAvg_unit, bondBlockAvgAdj_unit, add_zero]
theorem claim_holds (h₁ : BlockAvgAdjointFacts) (h₂ : KernelProjectionUnique.Claim) :
    BlockPartitionMassiveLaplacian.Claim := by
  intro d L k _ hL a _
  have : NeZero (L ^ k) := ⟨pow_ne_zero _ (by omega)⟩
  exact ⟨fun κ => blocksPartitionSites_holds (L ^ k) κ,
    fun κ => averagesTrivialAtUnitSpacing_holds κ,
    fun ℓ hℓ => torusMassiveLaplacianIdentities_holds h₁ h₂ (L ^ k) ℓ hℓ a,
    fun ℓ hℓ => torusUnitSpacingIdentities_holds h₂ ℓ hℓ a⟩
end YangMills.Construction.LatticeFields.BlockPartitionMassiveLaplacian

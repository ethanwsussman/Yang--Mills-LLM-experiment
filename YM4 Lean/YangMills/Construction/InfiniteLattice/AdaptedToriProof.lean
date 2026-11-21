import YangMills.Construction.DirichletOperator.DifferenceOperatorsAgreeOnTheLocalTorusProof
import YangMills.Construction.InfiniteLattice.BoxRepresentsTheTorusAndItsThinBoundaryLayerProof
import YangMills.Construction.InfiniteLattice.AdaptedTori
import YangMills.Construction.InfiniteLattice.PropertiesOfThePeriodGroups
import YangMills.Construction.InfiniteLattice.VectorsOfARectangularPeriodLatticeProof
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies.AdaptedTori
open InfiniteLattice
open PeriodicLattice (coordVec)
theorem coordVec_apply (μ ν : Fin 4) :
    coordVec μ ν = (((Pi.single μ 1 : Fin 4 → ℤ) ν : ℤ) : ℝ) := by apply _root_.YangMills.Construction.InfiniteLattice.RectangularPeriods.coordVec_apply <;> assumption
theorem coordVec_dotProduct (μ : Fin 4) (x : AmbientSpace) : coordVec μ ⬝ᵥ x = x μ := by apply _root_.YangMills.Construction.InfiniteLattice.BoxQuotient.coordVec_dotProduct <;> assumption
theorem abs_apply_le_norm (x : AmbientSpace) (μ : Fin 4) : |x μ| ≤ ‖x‖ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.abs_apply_le_pi_norm <;> assumption
theorem isNormalVector_props {m : AmbientSpace} (hm : IsNormalVector m) :
    (∃ z : Fin 4 → ℤ, ∀ ν, m ν = (z ν : ℝ)) ∧ (m ⬝ᵥ m = 1 ∨ m ⬝ᵥ m = 2) ∧
      ∀ x : AmbientSpace, |m ⬝ᵥ x| ≤ (m ⬝ᵥ m) * ‖x‖ := by
  rcases hm with ⟨μ, rfl⟩ | ⟨μ, lam, hlt, rfl | rfl⟩
  · have hq : coordVec μ ⬝ᵥ coordVec μ = 1 := coordVec_dot_coordVec_self μ
    refine ⟨⟨Pi.single μ 1, coordVec_apply μ⟩, Or.inl hq, fun x => ?_⟩
    rw [hq, coordVec_dotProduct, one_mul]
    exact abs_apply_le_norm x μ
  · have hne : μ ≠ lam := ne_of_lt hlt
    have hq : (coordVec μ + coordVec lam) ⬝ᵥ (coordVec μ + coordVec lam) = 2 := by
      simp only [dotProduct_add, add_dotProduct, coordVec_dot_coordVec_self,
        coordVec_dot_coordVec_of_ne hne, coordVec_dot_coordVec_of_ne hne.symm]
      norm_num
    refine ⟨⟨Pi.single μ 1 + Pi.single lam 1, fun ν => ?_⟩, Or.inr hq, fun x => ?_⟩
    · simp only [Pi.add_apply, coordVec_apply, Int.cast_add]
    · rw [hq, add_dotProduct, coordVec_dotProduct, coordVec_dotProduct]
      have h₁ := abs_apply_le_norm x μ
      have h₂ := abs_apply_le_norm x lam
      have h₃ := abs_add_le (x μ) (x lam)
      linarith
  · have hne : μ ≠ lam := ne_of_lt hlt
    have hq : (coordVec μ - coordVec lam) ⬝ᵥ (coordVec μ - coordVec lam) = 2 := by
      simp only [dotProduct_sub, sub_dotProduct, coordVec_dot_coordVec_self,
        coordVec_dot_coordVec_of_ne hne, coordVec_dot_coordVec_of_ne hne.symm]
      norm_num
    refine ⟨⟨Pi.single μ 1 - Pi.single lam 1, fun ν => ?_⟩, Or.inr hq, fun x => ?_⟩
    · simp only [Pi.sub_apply, coordVec_apply, Int.cast_sub]
    · rw [hq, sub_dotProduct, coordVec_dotProduct, coordVec_dotProduct]
      have h₁ := abs_apply_le_norm x μ
      have h₂ := abs_apply_le_norm x lam
      have h₃ := abs_sub (x μ) (x lam)
      linarith
theorem dotProduct_self_pos {m : AmbientSpace} (hm : IsNormalVector m) : 0 < m ⬝ᵥ m := by
  rcases (isNormalVector_props hm).2.1 with h | h <;> rw [h] <;> norm_num
def basisScale (n : AmbientSpace) (h J w : ℤ) : Fin 4 → ℝ :=
  Fin.cons (2 * (J : ℝ) * (h : ℝ) / (n ⬝ᵥ n)) fun _ => (w : ℝ)
section
variable {n : AmbientSpace} (hn : IsNormalVector n) {h J w : ℤ}
include hn in
theorem adaptedBasis_eq_smul (h J w : ℤ) (i : Fin 4) :
    adaptedBasis n hn h J w i = basisScale n h J w i • (normalFrame n hn).vec i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [normalFrame_vec_zero]
    simp only [adaptedBasis, basisScale, Fin.cons_zero, longPeriod, dualVector,
      normSq_eq_dotProduct, smul_smul, div_eq_mul_inv]
  · simp only [adaptedBasis, basisScale, Fin.cons_succ, shortPeriod]
theorem two_le_mul (ha : AdmissibleParams h J w) : 2 ≤ J * h := by
  obtain ⟨-, h₂, h₁, -, -⟩ := ha
  nlinarith
theorem two_le_min (ha : AdmissibleParams h J w) : 2 ≤ min (J * h) w :=
  le_min (two_le_mul ha) ha.2.2.2.2
include hn in
theorem min_le_basisScale (ha : AdmissibleParams h J w) (i : Fin 4) :
    ((min (J * h) w : ℤ) : ℝ) ≤ basisScale n h J w i := by
  have hJh : (2 : ℝ) ≤ (J : ℝ) * (h : ℝ) := by exact_mod_cast two_le_mul ha
  refine Fin.cases ?_ (fun i => ?_) i
  · have hle : ((min (J * h) w : ℤ) : ℝ) ≤ (J : ℝ) * (h : ℝ) := by
      exact_mod_cast min_le_left (J * h) w
    refine hle.trans ?_
    simp only [basisScale, Fin.cons_zero]
    rcases (isNormalVector_props hn).2.1 with hq | hq <;> rw [hq] <;> linarith
  · simp only [basisScale, Fin.cons_succ]
    exact_mod_cast min_le_right (J * h) w
theorem adaptedBasis_orthogonal (h J w : ℤ) :
    Pairwise fun i j => adaptedBasis n hn h J w i ⬝ᵥ adaptedBasis n hn h J w j = 0 := by
  intro i j hij
  rw [adaptedBasis_eq_smul, adaptedBasis_eq_smul, smul_dotProduct, dotProduct_smul,
    (normalFrame n hn).pairwise_orthogonal hij]
  simp
theorem mem_adaptedLattice_iff_sum {x : AmbientSpace} :
    x ∈ adaptedLattice n hn h J w ↔
      ∃ a : Fin 4 → ℤ, x = ∑ i, a i • adaptedBasis n hn h J w i := by
  rw [mem_adaptedLattice_iff]
  constructor
  · rintro ⟨b, c, rfl⟩
    refine ⟨Fin.cons b c, ?_⟩
    simp [Fin.sum_univ_succ, adaptedBasis]
  · rintro ⟨a, rfl⟩
    refine ⟨a 0, fun i => a i.succ, ?_⟩
    simp [Fin.sum_univ_succ, adaptedBasis]
theorem normalFrame_dotProduct_sum (h J w : ℤ) (a : Fin 4 → ℤ) (j : Fin 4) :
    (normalFrame n hn).vec j ⬝ᵥ ∑ i, a i • adaptedBasis n hn h J w i =
      (a j : ℝ) * basisScale n h J w j *
        ((normalFrame n hn).vec j ⬝ᵥ (normalFrame n hn).vec j) := by
  rw [dotProduct_sum, Finset.sum_eq_single j]
  · rw [adaptedBasis_eq_smul, dotProduct_smul, dotProduct_smul, zsmul_eq_mul, smul_eq_mul]
    ring
  · intro i _ hij
    rw [adaptedBasis_eq_smul, dotProduct_smul, dotProduct_smul,
      (normalFrame n hn).pairwise_orthogonal hij.symm]
    simp
  · simp
include hn in
theorem min_le_norm_sum (ha : AdmissibleParams h J w) (a : Fin 4 → ℤ) {j : Fin 4} (hj : a j ≠ 0) :
    ((min (J * h) w : ℤ) : ℝ) ≤ ‖∑ i, a i • adaptedBasis n hn h J w i‖ := by
  set x := ∑ i, a i • adaptedBasis n hn h J w i with hx
  have hm := (normalFrame n hn).isNormal j
  have hq := dotProduct_self_pos hm
  have hb := (isNormalVector_props hm).2.2 x
  rw [hx, normalFrame_dotProduct_sum, ← hx, abs_mul, abs_mul, abs_of_pos hq] at hb
  have hb' : |(a j : ℝ)| * |basisScale n h J w j| ≤ ‖x‖ := le_of_mul_le_mul_right
    (by linarith) hq
  have hc := min_le_basisScale hn ha j
  have h2 : (2 : ℝ) ≤ ((min (J * h) w : ℤ) : ℝ) := by exact_mod_cast two_le_min ha
  have ha1 : (1 : ℝ) ≤ |(a j : ℝ)| := by
    have : (1 : ℤ) ≤ |a j| := Int.one_le_abs hj
    exact_mod_cast this
  rw [abs_of_pos (by linarith : 0 < basisScale n h J w j)] at hb'
  nlinarith
include hn in
theorem min_le_norm (ha : AdmissibleParams h J w) {x : AmbientSpace}
    (hx : x ∈ adaptedLattice n hn h J w) (h0 : x ≠ 0) : ((min (J * h) w : ℤ) : ℝ) ≤ ‖x‖ := by
  obtain ⟨a, rfl⟩ := (mem_adaptedLattice_iff_sum hn).mp hx
  have : ∃ j, a j ≠ 0 := by
    by_contra hall
    have hall' : ∀ j, a j = 0 := fun j => by_contra fun hj => hall ⟨j, hj⟩
    exact h0 (by simp [hall'])
  obtain ⟨j, hj⟩ := this
  exact min_le_norm_sum hn ha a hj
include hn in
theorem adaptedBasis_ne_zero (ha : AdmissibleParams h J w) (i : Fin 4) :
    adaptedBasis n hn h J w i ≠ 0 := by
  intro h0
  have hc := min_le_basisScale hn ha i
  have h2 : (2 : ℝ) ≤ ((min (J * h) w : ℤ) : ℝ) := by exact_mod_cast two_le_min ha
  rw [adaptedBasis_eq_smul] at h0
  rcases smul_eq_zero.mp h0 with h1 | h1
  · linarith
  · have hq := dotProduct_self_pos ((normalFrame n hn).isNormal i)
    rw [h1] at hq
    simp at hq
include hn in
theorem adaptedBasis_dotProduct_self_ne_zero (ha : AdmissibleParams h J w) (i : Fin 4) :
    adaptedBasis n hn h J w i ⬝ᵥ adaptedBasis n hn h J w i ≠ 0 := by
  intro h0
  exact adaptedBasis_ne_zero hn ha i (dotProduct_self_eq_zero.mp h0)
include hn in
theorem adaptedBasis_linearIndependent (ha : AdmissibleParams h J w) :
    LinearIndependent ℝ (adaptedBasis n hn h J w) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h1 := congrArg (fun y : AmbientSpace => adaptedBasis n hn h J w j ⬝ᵥ y) hg
  simp only [dotProduct_sum, dotProduct_zero] at h1
  rw [Finset.sum_eq_single j] at h1
  · rw [dotProduct_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_right (adaptedBasis_dotProduct_self_ne_zero hn ha j)
  · intro i _ hij
    rw [dotProduct_smul, adaptedBasis_orthogonal hn h J w hij.symm, smul_zero]
  · simp
include hn in
theorem adaptedBasis_iSupIndep (ha : AdmissibleParams h J w) :
    iSupIndep fun i => AddSubgroup.zmultiples (adaptedBasis n hn h J w i) := by
  rw [iSupIndep_def]
  intro i
  rw [AddSubgroup.disjoint_def]
  intro x hx hy
  have hle : (⨆ (j : Fin 4) (_ : j ≠ i), AddSubgroup.zmultiples (adaptedBasis n hn h J w j)) ≤
      orthogonalSubgroup (adaptedBasis n hn h J w i) := by
    refine iSup₂_le fun j hj y hy => ?_
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    refine zsmul_mem ?_ k
    exact adaptedBasis_orthogonal hn h J w hj.symm
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  have h0 : adaptedBasis n hn h J w i ⬝ᵥ (k • adaptedBasis n hn h J w i) = 0 := hle hy
  rw [dotProduct_smul, zsmul_eq_mul] at h0
  have hk : (k : ℝ) = 0 :=
    (mul_eq_zero.mp h0).resolve_right (adaptedBasis_dotProduct_self_ne_zero hn ha i)
  have hk' : k = 0 := by exact_mod_cast hk
  simp [hk']
include hn in
theorem adaptedBasis_mem_latticeSubgroup (i : Fin 4) :
    adaptedBasis n hn h J w i ∈ latticeSubgroup 1 := by
  refine Fin.cases ?_ (fun i => ?_) i
  · obtain ⟨⟨z, hz⟩, hq, -⟩ := isNormalVector_props hn
    rcases hq with hq | hq
    · refine ⟨fun μ => 2 * J * h * z μ, fun μ => ?_⟩
      rw [adaptedBasis_eq_smul, normalFrame_vec_zero]
      simp only [basisScale, Fin.cons_zero, hq, Pi.smul_apply, smul_eq_mul, hz]
      push_cast
      ring
    · refine ⟨fun μ => J * h * z μ, fun μ => ?_⟩
      rw [adaptedBasis_eq_smul, normalFrame_vec_zero]
      simp only [basisScale, Fin.cons_zero, hq, Pi.smul_apply, smul_eq_mul, hz]
      push_cast
      ring
  · obtain ⟨⟨z, hz⟩, -, -⟩ := isNormalVector_props ((normalFrame n hn).isNormal i.succ)
    refine ⟨fun μ => w * z μ, fun μ => ?_⟩
    rw [adaptedBasis_eq_smul]
    simp only [basisScale, Fin.cons_succ, Pi.smul_apply, smul_eq_mul, hz]
    push_cast
    ring
include hn in
theorem adaptedBasis_mem_adaptedLattice (i : Fin 4) :
    adaptedBasis n hn h J w i ∈ adaptedLattice n hn h J w :=
  (mem_adaptedLattice_iff_sum hn).mpr ⟨Pi.single i 1, by simp [Pi.single_apply, ite_smul]⟩
include hn in
theorem adaptedLattice_le_latticeSubgroup : adaptedLattice n hn h J w ≤ latticeSubgroup 1 := by
  intro x hx
  obtain ⟨a, rfl⟩ := (mem_adaptedLattice_iff_sum hn).mp hx
  exact sum_mem fun i _ => zsmul_mem (adaptedBasis_mem_latticeSubgroup hn i) _
include hn in
theorem isPeriodSubgroup_adaptedLattice (ha : AdmissibleParams h J w) (h3 : 3 ≤ min (J * h) w) :
    IsPeriodSubgroup (adaptedLattice n hn h J w) := by
  refine ⟨⟨(adaptedLattice n hn h J w).comap (latticeSubgroup 1).subtype,
    ⟨fun i => ⟨adaptedBasis n hn h J w i, adaptedBasis_mem_latticeSubgroup hn i⟩,
      fun i => adaptedBasis_mem_adaptedLattice hn i, adaptedBasis_linearIndependent hn ha⟩, ?_⟩, ?_⟩
  · intro γ hγ h0
    have hb := min_le_norm hn ha (x := (γ : AmbientSpace)) hγ (by simpa using h0)
    have h3' : (3 : ℝ) ≤ ((min (J * h) w : ℤ) : ℝ) := by exact_mod_cast h3
    rw [minimalPeriodRatio, mul_one]
    linarith
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, adaptedLattice_le_latticeSubgroup hn hx⟩, hx, rfl⟩
include hn in
theorem shortPeriod_mem_orthogonalSubgroup (w : ℤ) (i : Fin 3) :
    shortPeriod n hn w i ∈ orthogonalSubgroup n := by
  have h0 : (normalFrame n hn).vec 0 ⬝ᵥ (normalFrame n hn).vec i.succ = 0 :=
    (normalFrame n hn).pairwise_orthogonal (Fin.succ_ne_zero i).symm
  rw [normalFrame_vec_zero] at h0
  show n ⬝ᵥ shortPeriod n hn w i = 0
  rw [shortPeriod, dotProduct_smul, h0, smul_zero]
include hn in
theorem adaptedTransverseLattice_le_orthogonalSubgroup (w : ℤ) :
    adaptedTransverseLattice n hn w ≤ orthogonalSubgroup n := by
  refine iSup_le fun i y hy => ?_
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
  exact zsmul_mem (shortPeriod_mem_orthogonalSubgroup hn w i) k
include hn in
theorem dotProduct_longPeriod (h J : ℤ) :
    n ⬝ᵥ longPeriod n h J = 2 * (J : ℝ) * (h : ℝ) := by
  rw [longPeriod, dotProduct_smul, dotProduct_dualVector hn, smul_eq_mul, mul_one]
include hn in
theorem linearHeight_combination (h J w b : ℤ) (c : Fin 3 → ℤ) :
    linearHeight n (b • longPeriod n h J + ∑ i, c i • shortPeriod n hn w i) =
      2 * (b : ℝ) * (J : ℝ) * (h : ℝ) := by
  have h0 : (∑ i, c i • shortPeriod n hn w i) ∈ orthogonalSubgroup n :=
    sum_mem fun i _ => zsmul_mem (shortPeriod_mem_orthogonalSubgroup hn w i) _
  have h0' : n ⬝ᵥ (∑ i, c i • shortPeriod n hn w i) = 0 := h0
  rw [linearHeight, dotProduct_add, h0', dotProduct_smul, dotProduct_longPeriod hn, zsmul_eq_mul,
    add_zero]
  ring
theorem two_mul_mul_ne_zero (ha : AdmissibleParams h J w) : 2 * (J : ℝ) * (h : ℝ) ≠ 0 := by
  have hJh : (2 : ℝ) ≤ (J : ℝ) * (h : ℝ) := by exact_mod_cast two_le_mul ha
  nlinarith
include hn in
theorem eq_zero_of_mem_zmultiples_longPeriod (ha : AdmissibleParams h J w) {x : AmbientSpace}
    (hx : x ∈ AddSubgroup.zmultiples (longPeriod n h J)) (h0 : n ⬝ᵥ x = 0) : x = 0 := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  rw [dotProduct_smul, dotProduct_longPeriod hn, zsmul_eq_mul] at h0
  have hk : (k : ℝ) = 0 := (mul_eq_zero.mp h0).resolve_right (two_mul_mul_ne_zero ha)
  have hk' : k = 0 := by exact_mod_cast hk
  simp [hk']
include hn in
theorem mem_adaptedTransverseLattice_of_dotProduct_eq_zero (ha : AdmissibleParams h J w)
    {x : AmbientSpace} (hx : x ∈ adaptedLattice n hn h J w) (h0 : n ⬝ᵥ x = 0) :
    x ∈ adaptedTransverseLattice n hn w := by
  obtain ⟨b, c, rfl⟩ := mem_adaptedLattice_iff.mp hx
  have h1 := linearHeight_combination hn h J w b c
  rw [linearHeight, h0] at h1
  have hb : (b : ℝ) = 0 := by
    have h2 : (b : ℝ) * (2 * (J : ℝ) * (h : ℝ)) = 0 := by linarith
    exact (mul_eq_zero.mp h2).resolve_right (two_mul_mul_ne_zero ha)
  have hb' : b = 0 := by exact_mod_cast hb
  rw [hb', zero_smul, zero_add]
  refine sum_mem fun i _ => zsmul_mem ?_ _
  exact (le_iSup (fun i => AddSubgroup.zmultiples (shortPeriod n hn w i)) i)
    (AddSubgroup.mem_zmultiples _)
theorem adaptedTransverseLattice_le (h J w : ℤ) :
    adaptedTransverseLattice n hn w ≤ adaptedLattice n hn h J w :=
  le_sup_right
theorem axialSubgroup_eq (h J : ℤ) :
    PeriodSublattice.axialSubgroup n (J * h) = AddSubgroup.zmultiples (longPeriod n h J) := by
  rw [PeriodSublattice.axialSubgroup, longPeriod, dualVector, normSq_eq_dotProduct,
    ReflectionPositivity.NormalPlanes.normalOverNormSq]
  push_cast
  rw [mul_assoc]
include hn in
theorem isTransverseComplement (ha : AdmissibleParams h J w) (Γ : PeriodSublattice 1)
    (hΓ : Γ.toAmbient = adaptedLattice n hn h J w) :
    Γ.IsTransverseComplement n (J * h) (adaptedTransverseLattice n hn w) where
  le_toAmbient := hΓ ▸ adaptedTransverseLattice_le hn h J w
  sup_eq := by
    rw [axialSubgroup_eq, hΓ, sup_comm]
    rfl
  inf_eq := by
    rw [axialSubgroup_eq, eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := AddSubgroup.mem_inf.mp hx
    exact (AddSubgroup.mem_bot).mpr
      (eq_zero_of_mem_zmultiples_longPeriod hn ha hx₂
        (adaptedTransverseLattice_le_orthogonalSubgroup hn w hx₁))
  height_eq_zero := fun _ hx => adaptedTransverseLattice_le_orthogonalSubgroup hn w hx
include hn in
theorem splitsAlongWithHalfPeriod (ha : AdmissibleParams h J w) (Γ : PeriodSublattice 1)
    (hΓ : Γ.toAmbient = adaptedLattice n hn h J w) : Γ.SplitsAlongWithHalfPeriod n (J * h) := by
  refine ⟨?_, two_le_mul ha, _, isTransverseComplement hn ha Γ hΓ⟩
  rcases hn with ⟨μ, rfl⟩ | ⟨μ, lam, hlt, hm⟩
  · exact Or.inl ⟨μ, rfl⟩
  · exact Or.inr ⟨μ, lam, hlt, hm⟩
include hn in
theorem transversePart_eq (ha : AdmissibleParams h J w) (Γ : PeriodSublattice 1)
    (hΓ : Γ.toAmbient = adaptedLattice n hn h J w) :
    Γ.transversePart n (J * h) = adaptedTransverseLattice n hn w := by
  have hP := PeriodSublattice.isTransverseComplement_transversePart
    (splitsAlongWithHalfPeriod hn ha Γ hΓ)
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · exact mem_adaptedTransverseLattice_of_dotProduct_eq_zero hn ha (hΓ ▸ hP.le_toAmbient hx)
      (hP.height_eq_zero x hx)
  · have hxΓ : x ∈ Γ.transversePart n (J * h) ⊔ PeriodSublattice.axialSubgroup n (J * h) := by
      rw [hP.sup_eq, hΓ]
      exact adaptedTransverseLattice_le hn h J w hx
    obtain ⟨p, hp, l, hl, rfl⟩ := AddSubgroup.mem_sup.mp hxΓ
    rw [axialSubgroup_eq] at hl
    have h0 : n ⬝ᵥ (p + l) = 0 := adaptedTransverseLattice_le_orthogonalSubgroup hn w hx
    have hp0 : n ⬝ᵥ p = 0 := hP.height_eq_zero p hp
    rw [dotProduct_add, hp0, zero_add] at h0
    rw [eq_zero_of_mem_zmultiples_longPeriod hn ha hl h0, add_zero]
    exact hp
theorem exists_pnat_coe_eq (k : ℤ) (hk : 0 < k) : ∃ t : ℕ+, (((t : ℕ) : ℤ)) = k := by
  refine ⟨⟨k.toNat, by omega⟩, ?_⟩
  simp only [PNat.mk_coe]
  omega
include hn in
theorem exists_isAdaptedSideTuple (ha : AdmissibleParams h J w) :
    ∃ s, IsAdaptedSideTuple n hn h J w s := by
  have hw : 0 < w := by linarith [ha.2.2.2.2]
  have hm : ∀ i : Fin 4, ∃ t : ℕ+,
      ((t : ℕ) : ℝ) = (w : ℝ) * (normalFrame n hn).lengthSq i := by
    intro i
    have hq := (isNormalVector_props ((normalFrame n hn).isNormal i)).2.1
    rw [OrthogonalNormalFrame.lengthSq, normSq_eq_dotProduct]
    rcases hq with hq | hq
    · obtain ⟨t, ht⟩ := exists_pnat_coe_eq w hw
      refine ⟨t, ?_⟩
      rw [hq, mul_one]
      exact_mod_cast ht
    · obtain ⟨t, ht⟩ := exists_pnat_coe_eq (w * 2) (by linarith)
      refine ⟨t, ?_⟩
      rw [hq]
      exact_mod_cast ht
  choose m hm using hm
  have hJh := two_le_mul ha
  obtain ⟨t, ht⟩ := exists_pnat_coe_eq (2 * J * h) (by nlinarith)
  refine ⟨Fin.cons t fun i => m i.succ, ?_, fun i => ?_⟩
  · simp only [Fin.cons_zero]
    exact_mod_cast ht
  · simp only [Fin.cons_succ]
    exact hm _
include hn in
theorem sideVec_eq {s : Fin 4 → ℕ+} (hs : IsAdaptedSideTuple n hn h J w s) (i : Fin 4) :
    (normalFrame n hn).sideVec s i = adaptedBasis n hn h J w i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [OrthogonalNormalFrame.sideVec, hs.1, OrthogonalNormalFrame.dual, normalFrame_vec_zero]
    rfl
  · have hq : (normalFrame n hn).lengthSq i.succ ≠ 0 := by
      rw [OrthogonalNormalFrame.lengthSq, normSq_eq_dotProduct]
      exact (dotProduct_self_pos ((normalFrame n hn).isNormal i.succ)).ne'
    have hv : (normalFrame n hn).dual i.succ =
        ((normalFrame n hn).lengthSq i.succ)⁻¹ • (normalFrame n hn).vec i.succ := rfl
    rw [OrthogonalNormalFrame.sideVec, hs.2 i, hv, smul_smul, mul_assoc, mul_inv_cancel₀ hq,
      mul_one]
    rfl
include hn in
theorem isBoxShaped {s : Fin 4 → ℕ+} (hs : IsAdaptedSideTuple n hn h J w s)
    (Γ : PeriodSublattice 1) (hΓ : Γ.toAmbient = adaptedLattice n hn h J w) :
    Γ.IsBoxShaped (normalFrame n hn) s := by
  refine ⟨?_, fun i => ?_⟩
  · ext x
    have hsum : ∀ k : Fin 4 → ℤ,
        ∑ i, (k i : ℝ) • (normalFrame n hn).sideVec s i =
          ∑ i, k i • adaptedBasis n hn h J w i := fun k =>
      Finset.sum_congr rfl fun i _ => by rw [sideVec_eq hn hs, Int.cast_smul_eq_zsmul]
    have hmem : x ∈ (fun γ : LatticePoint 1 => (γ : AmbientSpace)) ''
        (Γ.periods : Set (LatticePoint 1)) ↔ x ∈ Γ.toAmbient := by
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    rw [hmem, hΓ, mem_adaptedLattice_iff_sum hn]
    simp only [OrthogonalNormalFrame.sideSpan, Set.mem_ofPred_eq, hsum]
  · rw [sideVec_eq hn hs]
    exact adaptedBasis_mem_latticeSubgroup hn i
include hn in
theorem shortPeriod_mem_parallelPeriodLattice (ha : AdmissibleParams h J w) (i : Fin 3) :
    shortPeriod n hn w i ∈ parallelPeriodLattice n := by
  refine AddSubgroup.mem_inf.mpr ⟨?_, shortPeriod_mem_orthogonalSubgroup hn w i⟩
  obtain ⟨k, hk⟩ := ha.2.2.2.1
  obtain ⟨⟨z, hz⟩, -, -⟩ := isNormalVector_props ((normalFrame n hn).isNormal i.succ)
  refine ⟨fun μ => k * z μ, fun μ => ?_⟩
  simp only [shortPeriod, Pi.smul_apply, smul_eq_mul, hz, hk]
  push_cast
  ring
theorem longPeriod_mem_normalPeriodLattice (h J : ℤ) :
    longPeriod n h J ∈ normalPeriodLattice n h := by
  refine mem_normalPeriodLattice_iff.mpr ⟨0, zero_mem _, J, ?_⟩
  rw [zero_add, longPeriod, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
  congr 1
  ring
include hn in
theorem adaptedLattice_le_normalPeriodLattice (ha : AdmissibleParams h J w) :
    adaptedLattice n hn h J w ≤ normalPeriodLattice n h := by
  refine sup_le ?_ (iSup_le fun i y hy => ?_)
  · intro y hy
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    exact zsmul_mem (longPeriod_mem_normalPeriodLattice h J) k
  · obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    exact zsmul_mem
      (le_sup_left (a := parallelPeriodLattice n) (shortPeriod_mem_parallelPeriodLattice hn ha i)) k
include hn in
theorem adaptedLattice_inf_parallelPeriodLattice (ha : AdmissibleParams h J w) :
    adaptedLattice n hn h J w ⊓ parallelPeriodLattice n = adaptedTransverseLattice n hn w := by
  refine le_antisymm (fun x hx => ?_) (le_inf (adaptedTransverseLattice_le hn h J w) ?_)
  · obtain ⟨hx₁, hx₂⟩ := AddSubgroup.mem_inf.mp hx
    exact mem_adaptedTransverseLattice_of_dotProduct_eq_zero hn ha hx₁
      (AddSubgroup.mem_inf.mp hx₂).2
  · refine iSup_le fun i y hy => ?_
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    exact zsmul_mem (shortPeriod_mem_parallelPeriodLattice hn ha i) k
end
theorem adaptedTorusProperties (hperiods : PeriodLatticeProperties) : AdaptedTorusProperties := by
  intro n hn h J w ha
  have hs : IsAdaptedSideTuple n hn h J w (adaptedSideLengths n hn h J w) :=
    Classical.epsilon_spec (exists_isAdaptedSideTuple hn ha)
  have h2 : 2 ≤ min (J * h) w := two_le_min ha
  refine ⟨⟨adaptedBasis_orthogonal hn h J w, adaptedBasis_mem_latticeSubgroup hn,
      adaptedBasis_iSupIndep hn ha,
      ⟨_, adaptedBasis_mem_adaptedLattice hn, adaptedBasis_linearIndependent hn ha⟩,
      fun γ hγ h0 => min_le_norm hn ha hγ h0, fun h3 => isPeriodSubgroup_adaptedLattice hn ha h3,
      fun r hr hlt => ⟨isPeriodSubgroup_adaptedLattice hn ha (by omega), fun γ hγ h0 => ?_⟩⟩,
    fun h3 Γ hΓ => ⟨splitsAlongWithHalfPeriod hn ha Γ hΓ, transversePart_eq hn ha Γ hΓ, hs,
      isBoxShaped hn hs Γ hΓ⟩,
    shortPeriod_mem_parallelPeriodLattice hn ha, longPeriod_mem_normalPeriodLattice h J,
    adaptedLattice_le_normalPeriodLattice hn ha,
    (hperiods.1 n hn h ha.1 ha.2.1).2.2.2.2.2.1, linearHeight_combination hn h J w,
    adaptedLattice_inf_parallelPeriodLattice hn ha, fun h3 Γ hΓ => ?_⟩
  · have hb := min_le_norm hn ha hγ h0
    have hlt' : (r : ℝ) + 1 < ((min (J * h) w : ℤ) : ℝ) := by exact_mod_cast hlt
    linarith
  · rw [transversePart_eq hn ha Γ hΓ]
    exact adaptedLattice_inf_parallelPeriodLattice hn ha
end YangMills.Construction.NormalFamilies.AdaptedTori

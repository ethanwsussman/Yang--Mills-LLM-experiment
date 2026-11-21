import YangMills.Construction.InfiniteLattice.AdaptedTori
import YangMills.Construction.InfiniteLattice.AllMirrorsAtSpacingOneProof
import YangMills.Construction.InfiniteLattice.FoldedArrayAndTheMirrorsOfTheLadder
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfATorusOfAnyShape
import YangMills.Construction.InfiniteLattice.PropertiesOfThePeriodGroups
import YangMills.Construction.InfiniteLattice.RulesOfTheActionOfTheLatticeIsometries
import YangMills.Construction.ReflectionPositivity.ChessboardEstimateOnTheSlabsOfASplitTorus
import YangMills.Construction.ReflectionPositivity.ChessboardEstimateTurnsTheUnfoldedArrayIntoTheFoldedOne
import YangMills.Construction.ReflectionPositivity.PullBacksOnASplitTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Matrix ComplexConjugate
noncomputable section
namespace YangMills.Construction.NormalFamilies
open InfiniteLattice
namespace ChessboardFolding
structure Assumptions (β : ℝ) (L : MirrorLadder) (w : ℤ) (S : SlabDecomposition) : Prop where
  beta_pos : 0 < β
  adapted : L.IsAdaptedSlabDecomposition w S
  torusFacts : AdaptedTorusProperties
  foldFacts : FoldedArrayMirrorProperties
  quotientFacts : PeriodicQuotient.FinitenessClaim
  latticeFacts : PeriodLatticeProperties
  actionRules : SymmetryActionRules.Statement
  pullbackFacts : SplitTorusPullbacks
  transitivity : SlabActionSimplyTransitive
theorem latticeSymmetry_ext_toFun {r r' : LatticeSymmetry 1} (h : r.toFun = r'.toFun) : r = r' := by apply _root_.YangMills.Construction.InfiniteLattice.UnitMeshReflectionPositivity.latticeSymmetry_ext_toFun <;> assumption
variable {β : ℝ} {L : MirrorLadder} {w : ℤ} {S : SlabDecomposition}
namespace Assumptions
variable (H : Assumptions β L w S)
include H
theorem splits_spacing : S.period.SplitsAlongWithHalfPeriod L.normal ((S.count : ℤ) * L.spacing) := by
  have h := S.splits
  rwa [H.adapted.normal_eq, H.adapted.width_eq] at h
theorem toAmbient_eq_adaptedLattice : S.period.toAmbient =
    adaptedLattice L.normal L.normal_mem L.spacing (S.count : ℤ) w :=
  H.adapted.toAmbient_eq
theorem mem_periods_iff (x : LatticePoint 1) : x ∈ S.period.periods ↔
    (x : AmbientSpace) ∈ adaptedLattice L.normal L.normal_mem L.spacing (S.count : ℤ) w := by
  rw [← H.toAmbient_eq_adaptedLattice]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]
theorem inf_parallelPeriodLattice_eq :
    adaptedLattice L.normal L.normal_mem L.spacing (S.count : ℤ) w ⊓ parallelPeriodLattice L.normal =
      S.period.transversePart L.normal ((S.count : ℤ) * L.spacing) := by
  obtain ⟨-, -, ⟨-, -, -, -, -, -, h⟩⟩ := H.torusFacts L.normal L.normal_mem L.spacing (S.count : ℤ) w
    H.adapted.admissible
  exact h H.adapted.three_le S.period H.toAmbient_eq_adaptedLattice
theorem mem_periods_iff_of_mem_parallel {x : LatticePoint 1}
    (hx : (x : AmbientSpace) ∈ parallelPeriodLattice L.normal) :
    x ∈ S.period.periods ↔
      (x : AmbientSpace) ∈ S.period.transversePart L.normal ((S.count : ℤ) * L.spacing) := by
  rw [H.mem_periods_iff, ← H.inf_parallelPeriodLattice_eq, AddSubgroup.mem_inf]
  exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩
theorem periods_le_normalSublattice : S.period.periods ≤ L.normalSublattice := by
  intro x hx
  obtain ⟨-, -, ⟨-, -, h, -⟩⟩ := H.torusFacts L.normal L.normal_mem L.spacing (S.count : ℤ) w
    H.adapted.admissible
  exact AddSubgroup.mem_addSubgroupOf.mpr (h ((H.mem_periods_iff x).mp hx))
theorem isAdaptedTorus : L.IsAdaptedTorus S.period S.count :=
  ⟨S.one_le_count, H.periods_le_normalSublattice, H.splits_spacing⟩
theorem dualShift_count_mem : L.dualShift (S.count : ℤ) ∈ S.period.periods := by
  rw [H.mem_periods_iff]
  exact (mem_adaptedLattice_iff).mpr ⟨1, 0, by simp [longPeriod, MirrorLadder.dualShift]⟩
theorem shift_actOn_shift {E : Type*} (x y : LatticePoint 1) (F : GaugeField 1 → E) :
    (shift x).actOn ((shift y).actOn F) =
      (shift (x + y)).actOn F := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := H.actionRules (shift x) (shift y)
  have e : (shift x).comp (shift y) = shift (x + y) := by
    refine latticeSymmetry_ext_toFun (funext fun u => ?_)
    change u + (y : AmbientSpace) + (x : AmbientSpace) = u + ((x : AmbientSpace) + (y : AmbientSpace))
    abel
  rw [e] at h
  funext U
  change F ((shift y).pullbackField ((shift x).pullbackField U)) =
    F ((shift (x + y)).pullbackField U)
  rw [h]
  rfl
end Assumptions
theorem shift_actOn_mem {F : GaugeField 1 → ℂ} (hF : F ∈ continuousLocalFunctions 1)
    (x : LatticePoint 1) : (shift x).actOn F ∈ continuousLocalFunctions 1 :=
  actOn_mem_continuousLocalFunctions _ (continuous_id.add continuous_const) hF
theorem levelShift_add (k m : ℤ) :
    L.levelShift (k + m) = L.levelShift k + L.levelShift m := by
  refine Subtype.ext ?_
  change (((k + m : ℤ) : ℝ) * (L.spacing : ℝ)) • firstNonzeroBasisVec L.normal =
    ((k : ℝ) * (L.spacing : ℝ)) • firstNonzeroBasisVec L.normal +
      ((m : ℝ) * (L.spacing : ℝ)) • firstNonzeroBasisVec L.normal
  push_cast
  module
theorem levelShift_zero : L.levelShift 0 = 0 := by
  refine Subtype.ext ?_
  change (((0 : ℤ) : ℝ) * (L.spacing : ℝ)) • firstNonzeroBasisVec L.normal = 0
  simp
theorem dualShift_add (k m : ℤ) :
    L.dualShift (k + m) = L.dualShift k + L.dualShift m := by
  refine Subtype.ext ?_
  change (2 * ((k + m : ℤ) : ℝ) * (L.spacing : ℝ)) • dualVector L.normal =
    (2 * (k : ℝ) * (L.spacing : ℝ)) • dualVector L.normal +
      (2 * (m : ℝ) * (L.spacing : ℝ)) • dualVector L.normal
  push_cast
  module
theorem parallelPoint_sub (v v' : parallelPeriodLattice L.normal) :
    L.parallelPoint (v - v') = L.parallelPoint v - L.parallelPoint v' := rfl
theorem parallelPoint_zsmul (i : ℤ) (v : parallelPeriodLattice L.normal) :
    L.parallelPoint (i • v) = i • L.parallelPoint v := rfl
namespace Assumptions
variable (H : Assumptions β L w S)
def transverseShift : parallelPeriodLattice L.normal :=
  ⟨(2 * (L.spacing : ℝ)) • dualVector L.normal -
      (2 * (L.spacing : ℝ)) • firstNonzeroBasisVec L.normal,
    ((H.latticeFacts.1 L.normal L.normal_mem L.spacing L.even_spacing L.two_le_spacing).2.2).1⟩
include H
theorem dualShift_eq (i : ℤ) :
    L.dualShift i = i • L.parallelPoint H.transverseShift + L.levelShift (2 * i) := by
  refine Subtype.ext ?_
  change (2 * (i : ℝ) * (L.spacing : ℝ)) • dualVector L.normal =
    i • ((2 * (L.spacing : ℝ)) • dualVector L.normal -
      (2 * (L.spacing : ℝ)) • firstNonzeroBasisVec L.normal) +
      (((2 * i : ℤ) : ℝ) * (L.spacing : ℝ)) • firstNonzeroBasisVec L.normal
  rw [← Int.cast_smul_eq_zsmul ℝ]
  push_cast
  module
theorem axialPoint_add_two_mul (v : parallelPeriodLattice L.normal) (k i : ℤ) :
    L.axialPoint v (k + 2 * i) = L.axialPoint (v - i • H.transverseShift) k + L.dualShift i := by
  rw [MirrorLadder.axialPoint, MirrorLadder.axialPoint, H.dualShift_eq, levelShift_add,
    parallelPoint_sub, parallelPoint_zsmul]
  abel
theorem parallelPoint_sub_mem {v v' : parallelPeriodLattice L.normal}
    (h : (v : L.TransverseQuotient S.period S.count) = v') :
    L.parallelPoint v - L.parallelPoint v' ∈ S.period.periods := by
  have h1 := QuotientAddGroup.eq.mp h.symm
  have h2 : ((-v' + v : parallelPeriodLattice L.normal) : AmbientSpace) ∈
      S.period.transversePart L.normal ((S.count : ℤ) * L.spacing) :=
    AddSubgroup.mem_addSubgroupOf.mp h1
  have hx : L.parallelPoint v - L.parallelPoint v' = L.parallelPoint (-v' + v) := by
    rw [sub_eq_neg_add]
    rfl
  rw [hx, H.mem_periods_iff_of_mem_parallel (x := L.parallelPoint (-v' + v)) (-v' + v).2]
  exact h2
theorem mk_eq_of_parallelPoint_sub_mem {v v' : parallelPeriodLattice L.normal}
    (h : L.parallelPoint v - L.parallelPoint v' ∈ S.period.periods) :
    (v : L.TransverseQuotient S.period S.count) = v' := by
  have hx : L.parallelPoint v - L.parallelPoint v' = L.parallelPoint (-v' + v) := by
    rw [sub_eq_neg_add]
    rfl
  rw [hx, H.mem_periods_iff_of_mem_parallel (x := L.parallelPoint (-v' + v)) (-v' + v).2] at h
  exact (QuotientAddGroup.eq.mpr (AddSubgroup.mem_addSubgroupOf.mpr h)).symm
theorem finite_transverseQuotient : Finite (L.TransverseQuotient S.period S.count) := by
  have := (H.quotientFacts.1 S.period).finite_quotientTorus
  refine Finite.of_injective
    (fun c : L.TransverseQuotient S.period S.count => S.period.quotientMap (L.parallelPoint c.out))
    fun c c' hcc => ?_
  have hm : L.parallelPoint c.out - L.parallelPoint c'.out ∈ S.period.periods := by
    have h1 := QuotientAddGroup.eq.mp hcc.symm
    rw [sub_eq_neg_add]
    exact h1
  have := H.mk_eq_of_parallelPoint_sub_mem hm
  rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this
theorem periodize_shift_congr {F : GaugeField 1 → ℂ}
    (hF : F ∈ continuousLocalFunctions 1) {x y : LatticePoint 1} (h : x - y ∈ S.period.periods) :
    S.period.periodize ((shift x).actOn F) =
      S.period.periodize ((shift y).actOn F) := by
  obtain ⟨-, -, hγ, -, -⟩ := H.pullbackFacts β H.beta_pos S.period L.normal L.normal_mem _ H.splits_spacing
  have := hγ _ h _ (shift_actOn_mem hF y)
  rwa [H.shift_actOn_shift, sub_add_cancel] at this
theorem periodicTerm_congr (A : L.SlabZeroGenerator) (k : ℤ) {v v' : parallelPeriodLattice L.normal}
    (h : (v : L.TransverseQuotient S.period S.count) = v') :
    A.periodicTerm S.period v k = A.periodicTerm S.period v' k := by
  refine H.periodize_shift_congr A.mem_continuousLocal ?_
  rw [MirrorLadder.axialPoint, MirrorLadder.axialPoint, add_sub_add_right_eq_sub]
  exact H.parallelPoint_sub_mem h
end Assumptions
section Exponent
variable (A : L.SlabZeroGenerator) (Γ : PeriodSublattice 1) (J : ℕ)
theorem periodicTerm_im (v : parallelPeriodLattice L.normal) (k : ℤ) (U : Γ.QuotientField) :
    (A.periodicTerm Γ v k U).im = 0 :=
  A.im_eq_zero _
theorem periodicTerm_eq_ofReal (v : parallelPeriodLattice L.normal) (k : ℤ) (U : Γ.QuotientField) :
    A.periodicTerm Γ v k U = ((A.periodicTerm Γ v k U).re : ℂ) :=
  Complex.ext (by simp) (by simp [periodicTerm_im])
def levelExponent (k : ℤ) (U : Γ.QuotientField) : ℝ :=
  ∑ᶠ c : L.TransverseQuotient Γ J, (A.periodicTerm Γ (Quotient.out c) k U).re
end Exponent
theorem norm_periodicTerm_le (A : L.SlabZeroGenerator) (Γ : PeriodSublattice 1)
    (v : parallelPeriodLattice L.normal) (k : ℤ) (U : Γ.QuotientField) :
    ‖A.periodicTerm Γ v k U‖ ≤ TestFunctions.uniformNorm A.toFun := by
  obtain ⟨⟨-, C, hC⟩, -, -⟩ := A.mem_continuousLocal
  exact le_ciSup (f := fun U => ‖A.toFun U‖) ⟨C, by rintro _ ⟨U, rfl⟩; exact hC U⟩ _
namespace Assumptions
variable (H : Assumptions β L w S) (A : L.SlabZeroGenerator)
include H
theorem slabExp_eq_exp (t : ℝ) (k : ℤ) (U : S.period.QuotientField) :
    A.slabExp S.period S.count t k U =
      ((Real.exp (t * levelExponent A S.period S.count k U) : ℝ) : ℂ) := by
  have := H.finite_transverseQuotient
  have := Fintype.ofFinite (L.TransverseQuotient S.period S.count)
  rw [MirrorLadder.SlabZeroGenerator.slabExp, levelExponent, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype]
  push_cast
  congr 2
  exact Finset.sum_congr rfl fun c _ => periodicTerm_eq_ofReal A _ _ _ _
theorem levelExponent_add_two_mul (k : ℤ) (U : S.period.QuotientField) :
    levelExponent A S.period S.count (k + 2 * (S.count : ℤ)) U =
      levelExponent A S.period S.count k U := by
  set d : parallelPeriodLattice L.normal := (S.count : ℤ) • H.transverseShift with hd
  let e : L.TransverseQuotient S.period S.count ≃ L.TransverseQuotient S.period S.count :=
    Equiv.subRight (d : L.TransverseQuotient S.period S.count)
  have key : ∀ c : L.TransverseQuotient S.period S.count,
      A.periodicTerm S.period (Quotient.out c) (k + 2 * (S.count : ℤ)) =
        A.periodicTerm S.period (Quotient.out (e c)) k := by
    intro c
    have h1 : A.periodicTerm S.period (Quotient.out c) (k + 2 * (S.count : ℤ)) =
        A.periodicTerm S.period (Quotient.out c - d) k := by
      refine H.periodize_shift_congr A.mem_continuousLocal ?_
      rw [H.axialPoint_add_two_mul, add_sub_cancel_left]
      exact H.dualShift_count_mem
    rw [h1]
    refine H.periodicTerm_congr A k ?_
    rw [QuotientAddGroup.mk_sub, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
    rfl
  rw [levelExponent, levelExponent]
  exact (finsum_congr fun c => by rw [key]).trans (finsum_comp_equiv e
    (f := fun c => (A.periodicTerm S.period (Quotient.out c) k U).re))
theorem slabExp_add_two_mul (t : ℝ) (k : ℤ) :
    A.slabExp S.period S.count t (k + 2 * (S.count : ℤ)) =
      A.slabExp S.period S.count t k := by
  funext U
  rw [H.slabExp_eq_exp, H.slabExp_eq_exp, H.levelExponent_add_two_mul]
theorem abs_levelExponent_le (k : ℤ) (U : S.period.QuotientField) :
    |levelExponent A S.period S.count k U| ≤
      (Nat.card (L.TransverseQuotient S.period S.count) : ℝ) * TestFunctions.uniformNorm A.toFun := by
  have := H.finite_transverseQuotient
  have := Fintype.ofFinite (L.TransverseQuotient S.period S.count)
  rw [levelExponent, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ c ∈ (Finset.univ : Finset (L.TransverseQuotient S.period S.count)),
      |(A.periodicTerm S.period (Quotient.out c) k U).re| ≤ TestFunctions.uniformNorm A.toFun :=
    fun c _ => (Complex.abs_re_le_norm _).trans (norm_periodicTerm_le A _ _ _ _)
  simpa using Finset.sum_le_card_nsmul _ _ _ this
theorem continuous_periodicTerm (v : parallelPeriodLattice L.normal) (k : ℤ) :
    Continuous (A.periodicTerm S.period v k) :=
  (H.quotientFacts.1 S.period).continuous_periodize _ (shift_actOn_mem A.mem_continuousLocal _)
theorem continuous_slabExp (t : ℝ) (k : ℤ) :
    Continuous (A.slabExp S.period S.count t k) := by
  have := H.finite_transverseQuotient
  have := Fintype.ofFinite (L.TransverseQuotient S.period S.count)
  have : A.slabExp S.period S.count t k = fun U =>
      Complex.exp ((t : ℂ) * ∑ c : L.TransverseQuotient S.period S.count,
        A.periodicTerm S.period (Quotient.out c) k U) := by
    funext U
    rw [MirrorLadder.SlabZeroGenerator.slabExp, finsum_eq_sum_of_fintype]
  rw [this]
  exact Complex.continuous_exp.comp (continuous_const.mul
    (continuous_finsetSum _ fun c _ => H.continuous_periodicTerm A _ _))
theorem level_eq (k : ℤ) : S.level k = L.offset + (k : ℝ) * (L.spacing : ℝ) := by
  rw [SlabDecomposition.level, H.adapted.baseLevel_eq, H.adapted.width_eq]
theorem quotientMap_mem_slabAt {x : LatticePoint 1} {k : ℤ} (hx : (x : AmbientSpace) ∈ L.slab k) :
    S.period.quotientMap x ∈ S.slabAt k := by
  refine ⟨S.normal ⬝ᵥ (x : AmbientSpace), ⟨x, rfl, 0, by simp⟩, ?_, ?_⟩
  · rw [H.level_eq, H.adapted.normal_eq]
    exact hx.1
  · rw [H.level_eq, H.adapted.normal_eq]
    have := hx.2
    push_cast
    exact this
theorem linkClassImage_subset {F : GaugeField 1 → ℂ} {k : ℤ}
    (hF : SupportLiesIn F (L.slab k)) :
    S.period.linkClassImage (observableSupport F) ⊆
      S.period.linksInside (S.slabAt k) := by
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨h₁, h₂⟩ := hF b.1 hb
  obtain ⟨γ, hγ, hrep⟩ := S.period.exists_linkRep_eq b
  have hmove : ∀ x : LatticePoint 1,
      S.period.quotientMap ((shift γ).pointMap x) = S.period.quotientMap x := by
    intro x
    have : (shift γ).pointMap x = x + γ := Subtype.ext rfl
    rw [this, map_add]
    have hz : S.period.quotientMap γ = 0 := (QuotientAddGroup.eq_zero_iff γ).mpr hγ
    rw [hz, add_zero]
  intro s hs
  rw [PeriodSublattice.linkEndpoints, hrep] at hs
  rcases hs with rfl | rfl
  · exact (hmove _).symm ▸ H.quotientMap_mem_slabAt h₁
  · exact (hmove _).symm ▸ H.quotientMap_mem_slabAt h₂
theorem shift_supportLiesIn (v : parallelPeriodLattice L.normal) (k : ℤ) :
    SupportLiesIn ((shift (L.axialPoint v k)).actOn A.toFun) (L.slab k) := by
  obtain ⟨-, h, -⟩ := H.foldFacts L A
  exact h k (⟨L.axialPoint v k, L.axialPoint_mem_axialSublattice v k⟩, (0 : Fin 1)) ⟨v, v.2, rfl⟩
theorem slabExp_dependsOn (t : ℝ) (k : ℤ) :
    PeriodSublattice.DependsOnlyOn (A.slabExp S.period S.count t k)
      (S.period.linksInside (S.slabAt k)) := by
  intro U U' hUU
  have hs : ∀ v : parallelPeriodLattice L.normal,
      A.periodicTerm S.period v k U = A.periodicTerm S.period v k U' :=
    fun v => (H.quotientFacts.1 S.period).periodize_dependsOn _
      (shift_actOn_mem A.mem_continuousLocal _) U U'
      fun b hb => hUU b (H.linkClassImage_subset (H.shift_supportLiesIn A v k) hb)
  simp only [MirrorLadder.SlabZeroGenerator.slabExp, hs]
theorem slabExp_mem (t : ℝ) (ht : 0 ≤ t) (k : ℤ) :
    A.slabExp S.period S.count t k ∈ S.slabAlgebra k := by
  refine ⟨(H.continuous_slabExp A t k).measurable,
    ⟨Real.exp (t * ((Nat.card (L.TransverseQuotient S.period S.count) : ℝ) *
      TestFunctions.uniformNorm A.toFun)), fun U => ?_⟩, H.slabExp_dependsOn A t k⟩
  rw [H.slabExp_eq_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (H.abs_levelExponent_le A k U)) ht)
theorem slabExp_im (t : ℝ) (k : ℤ) (U : S.period.QuotientField) :
    (A.slabExp S.period S.count t k U).im = 0 := by
  rw [H.slabExp_eq_exp, Complex.ofReal_im]
theorem exp_bound_le_iInf (t : ℝ) (ht : 0 ≤ t) (k : ℤ) :
    Real.exp (-(t * (Nat.card (L.TransverseQuotient S.period S.count) : ℝ) *
      TestFunctions.uniformNorm A.toFun)) ≤
    ⨅ U, (A.slabExp S.period S.count t k U).re := by
  refine le_ciInf fun U => ?_
  rw [H.slabExp_eq_exp, Complex.ofReal_re]
  refine Real.exp_le_exp.mpr ?_
  have h1 := neg_le_of_abs_le (H.abs_levelExponent_le A k U)
  have h2 := mul_le_mul_of_nonneg_left h1 ht
  linarith
end Assumptions
structure Enumerates (L : MirrorLadder) (Γ : PeriodSublattice 1) (J : ℕ) {I C : Type*}
    (point : parallelPeriodLattice L.normal → I → C) : Prop where
  respects : ∀ (v v' : parallelPeriodLattice L.normal) (i : I),
    (v : L.TransverseQuotient Γ J) = v' → point v i = point v' i
  covers : ∀ c : C, ∃ v i, point v i = c
  separates : ∀ (v v' : parallelPeriodLattice L.normal) (i i' : I), point v i = point v' i' →
    i = i' ∧ (v : L.TransverseQuotient Γ J) = v'
namespace Enumerates
variable {Γ : PeriodSublattice 1} {J : ℕ} {I C : Type*}
  {point : parallelPeriodLattice L.normal → I → C}
theorem uniqueRepresentation (h : Enumerates L Γ J point) : L.UniqueRepresentation Γ J point := by
  intro c
  obtain ⟨v, i, rfl⟩ := h.covers c
  refine ⟨((v : L.TransverseQuotient Γ J), i), fun v' hv' => h.respects _ _ _ hv', ?_⟩
  rintro ⟨c', i'⟩ hp
  obtain ⟨v', rfl⟩ := QuotientAddGroup.mk_surjective c'
  obtain ⟨rfl, hc⟩ := h.separates _ _ _ _ (hp v' rfl)
  exact Prod.ext hc rfl
def equiv (h : Enumerates L Γ J point) : L.TransverseQuotient Γ J × I ≃ C :=
  Equiv.ofBijective (fun p => point (Quotient.out p.1) p.2) (by
    constructor
    · rintro ⟨c, i⟩ ⟨c', i'⟩ hp
      obtain ⟨rfl, hc⟩ := h.separates _ _ _ _ hp
      rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at hc
      exact Prod.ext hc rfl
    · intro c
      obtain ⟨v, i, rfl⟩ := h.covers c
      refine ⟨((v : L.TransverseQuotient Γ J), i), h.respects _ _ _ ?_⟩
      rw [QuotientAddGroup.out_eq'])
theorem finsum_eq (h : Enumerates L Γ J point) [Finite (L.TransverseQuotient Γ J)] [Fintype I]
    (g : C → ℝ) :
    ∑ᶠ c : C, g c = ∑ i : I, ∑ᶠ x : L.TransverseQuotient Γ J, g (point (Quotient.out x) i) := by
  have := Fintype.ofFinite (L.TransverseQuotient Γ J)
  rw [← finsum_comp_equiv h.equiv, finsum_eq_sum_of_fintype, Fintype.sum_prod_type_right]
  exact Finset.sum_congr rfl fun i _ => (finsum_eq_sum_of_fintype _).symm
end Enumerates
theorem cosets_mk_eq_iff (𝔸 : LocalObservableArray) (Γ : PeriodSublattice 1) (u u' : 𝔸.sublattice) :
    (u : 𝔸.Cosets Γ) = u' ↔ (u : LatticePoint 1) - (u' : LatticePoint 1) ∈ Γ.periods := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, ← neg_mem_iff]
  simp only [AddSubgroup.coe_add, NegMemClass.coe_neg, neg_add_rev, neg_neg]
  rw [sub_eq_add_neg, add_comm]
theorem normal_dotProduct_axialPoint (v : parallelPeriodLattice L.normal) (k : ℤ) :
    L.normal ⬝ᵥ (L.axialPoint v k : AmbientSpace) = (k : ℝ) * (L.spacing : ℝ) := by
  change L.normal ⬝ᵥ ((v : AmbientSpace) +
    ((k : ℝ) * (L.spacing : ℝ)) • firstNonzeroBasisVec L.normal) = _
  rw [dotProduct_add, MirrorLadder.dotProduct_eq_zero_of_mem_parallelPeriodLattice v.2,
    dotProduct_smul, dotProduct_firstNonzeroBasisVec L.normal_mem]
  simp
theorem normal_dotProduct_normalPoint (v : parallelPeriodLattice L.normal) (i : ℤ) :
    L.normal ⬝ᵥ (L.normalPoint v i : AmbientSpace) = 2 * (i : ℝ) * (L.spacing : ℝ) := by
  change L.normal ⬝ᵥ ((v : AmbientSpace) +
    (2 * (i : ℝ) * (L.spacing : ℝ)) • dualVector L.normal) = _
  rw [dotProduct_add, MirrorLadder.dotProduct_eq_zero_of_mem_parallelPeriodLattice v.2,
    dotProduct_smul, dotProduct_dualVector L.normal_mem]
  simp
theorem dualShift_mul (a i : ℤ) : L.dualShift (a * i) = i • L.dualShift a := by
  refine Subtype.ext ?_
  change (2 * ((a * i : ℤ) : ℝ) * (L.spacing : ℝ)) • dualVector L.normal =
    i • ((2 * (a : ℝ) * (L.spacing : ℝ)) • dualVector L.normal)
  rw [← Int.cast_smul_eq_zsmul ℝ]
  push_cast
  module
theorem eq_of_dvd_sub_of_lt {N a b : ℤ} (ha : 0 ≤ a) (ha' : a < N) (hb : 0 ≤ b) (hb' : b < N)
    (h : N ∣ a - b) : a = b := by
  have : a - b = 0 := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
  omega
namespace Assumptions
variable (H : Assumptions β L w S) (A : L.SlabZeroGenerator)
include H
theorem dualShift_count_mul_mem (i : ℤ) :
    L.dualShift ((S.count : ℤ) * i) ∈ S.period.periods := by
  rw [dualShift_mul]
  exact zsmul_mem H.dualShift_count_mem i
theorem dvd_of_axialPoint_sub_mem {v v' : parallelPeriodLattice L.normal} {k k' : ℤ}
    (h : L.axialPoint v k - L.axialPoint v' k' ∈ S.period.periods) :
    2 * (S.count : ℤ) ∣ k - k' := by
  obtain ⟨m, hm⟩ := H.isAdaptedTorus.exists_dotProduct_eq h
  have h1 : L.normal ⬝ᵥ ((L.axialPoint v k - L.axialPoint v' k' : LatticePoint 1) : AmbientSpace) =
      (k : ℝ) * (L.spacing : ℝ) - (k' : ℝ) * (L.spacing : ℝ) := by
    rw [AddSubgroup.coe_sub, dotProduct_sub, normal_dotProduct_axialPoint,
      normal_dotProduct_axialPoint]
  rw [h1] at hm
  have hne := MirrorLadder.spacing_ne_zero L
  refine ⟨m, ?_⟩
  have h2 : ((k - k' : ℤ) : ℝ) = ((2 * (S.count : ℤ) * m : ℤ) : ℝ) := by
    push_cast
    apply mul_right_cancel₀ hne
    linarith
  exact_mod_cast h2
theorem dvd_of_normalPoint_sub_mem {v v' : parallelPeriodLattice L.normal} {i i' : ℤ}
    (h : L.normalPoint v i - L.normalPoint v' i' ∈ S.period.periods) :
    (S.count : ℤ) ∣ i - i' := by
  obtain ⟨m, hm⟩ := H.isAdaptedTorus.exists_dotProduct_eq h
  have h1 : L.normal ⬝ᵥ ((L.normalPoint v i - L.normalPoint v' i' : LatticePoint 1) : AmbientSpace) =
      2 * (i : ℝ) * (L.spacing : ℝ) - 2 * (i' : ℝ) * (L.spacing : ℝ) := by
    rw [AddSubgroup.coe_sub, dotProduct_sub, normal_dotProduct_normalPoint,
      normal_dotProduct_normalPoint]
  rw [h1] at hm
  have hne := MirrorLadder.spacing_ne_zero L
  refine ⟨m, ?_⟩
  have h2 : ((i - i' : ℤ) : ℝ) = (((S.count : ℤ) * m : ℤ) : ℝ) := by
    push_cast
    apply mul_right_cancel₀ hne
    apply mul_left_cancel₀ (two_ne_zero (α := ℝ))
    linarith
  exact_mod_cast h2
theorem enumerates_axial : Enumerates L S.period S.count
    (fun v (k : Fin (2 * S.count)) => A.axialClass S.period v ((k : ℕ) : ℤ)) := by
  refine ⟨fun v v' k h => ?_, fun c => ?_, fun v v' k k' h => ?_⟩
  · refine (cosets_mk_eq_iff _ _ _ _).mpr ?_
    change L.axialPoint v _ - L.axialPoint v' _ ∈ _
    rw [MirrorLadder.axialPoint, MirrorLadder.axialPoint, add_sub_add_right_eq_sub]
    exact H.parallelPoint_sub_mem h
  · obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective c
    have hmem : ((u : LatticePoint 1) : AmbientSpace) ∈ axialPeriodLattice L.normal L.spacing :=
      AddSubgroup.mem_addSubgroupOf.mp u.2
    obtain ⟨y, hy, m, hyu⟩ := mem_axialPeriodLattice_iff.mp hmem
    have hJ : 0 < 2 * (S.count : ℤ) := by
      have := S.one_le_count
      omega
    set k := m % (2 * (S.count : ℤ)) with hk
    set i := m / (2 * (S.count : ℤ)) with hi
    have hk0 : 0 ≤ k := Int.emod_nonneg _ hJ.ne'
    have hk1 : k < 2 * (S.count : ℤ) := Int.emod_lt_of_pos _ hJ
    have hmk : m = k + 2 * ((S.count : ℤ) * i) := by
      have := Int.emod_add_mul_ediv m (2 * (S.count : ℤ))
      rw [← hk, ← hi] at this
      rw [← mul_assoc]
      exact this.symm
    have hu : (u : LatticePoint 1) = L.axialPoint ⟨y, hy⟩ m := by
      refine Subtype.ext ?_
      change ((u : LatticePoint 1) : AmbientSpace) =
        y + ((m : ℝ) * (L.spacing : ℝ)) • firstNonzeroBasisVec L.normal
      rw [← hyu, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    refine ⟨⟨y, hy⟩ - ((S.count : ℤ) * i) • H.transverseShift, ⟨k.toNat, by omega⟩, ?_⟩
    refine (cosets_mk_eq_iff _ _ _ _).mpr ?_
    have hkk : (((k.toNat : ℕ) : ℤ)) = k := Int.toNat_of_nonneg hk0
    change L.axialPoint _ (((k.toNat : ℕ) : ℤ)) - (u : LatticePoint 1) ∈ _
    rw [hu, hmk, H.axialPoint_add_two_mul, hkk, sub_add_cancel_left]
    exact neg_mem (H.dualShift_count_mul_mem i)
  · have hm : L.axialPoint v ((k : ℕ) : ℤ) - L.axialPoint v' ((k' : ℕ) : ℤ) ∈ S.period.periods :=
      (cosets_mk_eq_iff _ _ _ _).mp h
    have hkk : ((k : ℕ) : ℤ) = ((k' : ℕ) : ℤ) := by
      have h1 := k.2
      have h2 := k'.2
      exact eq_of_dvd_sub_of_lt (by omega) (by omega) (by omega) (by omega)
        (H.dvd_of_axialPoint_sub_mem hm)
    refine ⟨Fin.ext (by exact_mod_cast hkk), H.mk_eq_of_parallelPoint_sub_mem ?_⟩
    rw [hkk, MirrorLadder.axialPoint, MirrorLadder.axialPoint, add_sub_add_right_eq_sub] at hm
    exact hm
theorem enumerates_normal : Enumerates L S.period S.count
    (fun v (i : Fin S.count) => A.normalClass S.period v ((i : ℕ) : ℤ)) := by
  refine ⟨fun v v' k h => ?_, fun c => ?_, fun v v' k k' h => ?_⟩
  · refine (cosets_mk_eq_iff _ _ _ _).mpr ?_
    change L.normalPoint v _ - L.normalPoint v' _ ∈ _
    rw [MirrorLadder.normalPoint, MirrorLadder.normalPoint, add_sub_add_right_eq_sub]
    exact H.parallelPoint_sub_mem h
  · obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective c
    have hmem : ((u : LatticePoint 1) : AmbientSpace) ∈ normalPeriodLattice L.normal L.spacing :=
      AddSubgroup.mem_addSubgroupOf.mp u.2
    obtain ⟨y, hy, m, hyu⟩ := mem_normalPeriodLattice_iff.mp hmem
    have hJ : 0 < (S.count : ℤ) := by
      have := S.one_le_count
      omega
    set k := m % (S.count : ℤ) with hk
    set i := m / (S.count : ℤ) with hi
    have hk0 : 0 ≤ k := Int.emod_nonneg _ hJ.ne'
    have hk1 : k < (S.count : ℤ) := Int.emod_lt_of_pos _ hJ
    have hmk : m = k + (S.count : ℤ) * i := by
      have := Int.emod_add_mul_ediv m (S.count : ℤ)
      rw [← hk, ← hi] at this
      exact this.symm
    have hu : (u : LatticePoint 1) = L.normalPoint ⟨y, hy⟩ m := by
      refine Subtype.ext ?_
      change ((u : LatticePoint 1) : AmbientSpace) =
        y + (2 * (m : ℝ) * (L.spacing : ℝ)) • dualVector L.normal
      rw [← hyu, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
      congr 2
      ring
    refine ⟨⟨y, hy⟩, ⟨k.toNat, by omega⟩, ?_⟩
    refine (cosets_mk_eq_iff _ _ _ _).mpr ?_
    have hkk : (((k.toNat : ℕ) : ℤ)) = k := Int.toNat_of_nonneg hk0
    change L.normalPoint _ (((k.toNat : ℕ) : ℤ)) - (u : LatticePoint 1) ∈ _
    rw [hu, hmk, hkk, MirrorLadder.normalPoint, MirrorLadder.normalPoint, dualShift_add]
    have : L.parallelPoint ⟨y, hy⟩ + L.dualShift k -
        (L.parallelPoint ⟨y, hy⟩ + (L.dualShift k + L.dualShift ((S.count : ℤ) * i))) =
        -L.dualShift ((S.count : ℤ) * i) := by abel
    rw [this]
    exact neg_mem (H.dualShift_count_mul_mem i)
  · have hm : L.normalPoint v ((k : ℕ) : ℤ) - L.normalPoint v' ((k' : ℕ) : ℤ) ∈ S.period.periods :=
      (cosets_mk_eq_iff _ _ _ _).mp h
    have hkk : ((k : ℕ) : ℤ) = ((k' : ℕ) : ℤ) := by
      have h1 := k.2
      have h2 := k'.2
      exact eq_of_dvd_sub_of_lt (by omega) (by omega) (by omega) (by omega)
        (H.dvd_of_normalPoint_sub_mem hm)
    refine ⟨Fin.ext (by exact_mod_cast hkk), H.mk_eq_of_parallelPoint_sub_mem ?_⟩
    rw [hkk, MirrorLadder.normalPoint, MirrorLadder.normalPoint, add_sub_add_right_eq_sub] at hm
    exact hm
end Assumptions
theorem finsum_prod_finTwo {C : Type*} [Finite C] (G : C × Fin 2 → ℝ) :
    ∑ᶠ p : C × Fin 2, G p = ∑ᶠ c : C, G (c, 0) + ∑ᶠ c : C, G (c, 1) := by
  have := Fintype.ofFinite C
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Fintype.sum_prod_type_right, Fin.sum_univ_two]
theorem finsum_prod_finOne {C : Type*} (G : C × Fin 1 → ℝ) :
    ∑ᶠ p : C × Fin 1, G p = ∑ᶠ c : C, G (c, 0) :=
  (finsum_comp_equiv (Equiv.prodUnique C (Fin 1)).symm (f := G)).symm
theorem cosetRep_sub_mem (𝔸 : LocalObservableArray) (Γ : PeriodSublattice 1) (u : 𝔸.sublattice) :
    ((𝔸.cosetRep Γ (u : 𝔸.Cosets Γ) : 𝔸.sublattice) : LatticePoint 1) - (u : LatticePoint 1) ∈
      Γ.periods :=
  (cosets_mk_eq_iff 𝔸 Γ _ _).mp (QuotientAddGroup.out_eq' _)
def zmodValEquiv (N : ℕ) [NeZero N] : ZMod N ≃ Fin N where
  toFun k := ⟨k.val, ZMod.val_lt k⟩
  invFun i := ((i : ℕ) : ZMod N)
  left_inv k := ZMod.natCast_zmod_val k
  right_inv i := Fin.ext (ZMod.val_natCast_of_lt i.2)
theorem sum_zmod_val_eq_sum_fin {N : ℕ} [NeZero N] (g : ℕ → ℝ) :
    ∑ k : ZMod N, g k.val = ∑ i : Fin N, g i :=
  Fintype.sum_equiv (zmodValEquiv N) _ _ fun _ => rfl
theorem cexp_mul_finsum_of_real {C : Type*} [Finite C] (z : C → ℂ) (hz : ∀ c, (z c).im = 0)
    (t : ℝ) :
    Complex.exp ((t : ℂ) * ∑ᶠ c, z c) = ((Real.exp (t * ∑ᶠ c, (z c).re) : ℝ) : ℂ) := by
  have := Fintype.ofFinite C
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  push_cast
  congr 2
  exact Finset.sum_congr rfl fun c _ => Complex.ext (by simp) (by simp [hz c])
namespace Assumptions
variable (H : Assumptions β L w S) (A : L.SlabZeroGenerator)
include H
theorem periodicSum_axial (U : S.period.QuotientField) :
    A.unfoldedArray.periodicSum S.period U =
      ∑ k : Fin (2 * S.count), levelExponent A S.period S.count ((k : ℕ) : ℤ) U := by
  have := H.finite_transverseQuotient
  refine (finsum_prod_finOne (C := A.unfoldedArray.Cosets S.period) _).trans ?_
  refine ((H.enumerates_axial A).finsum_eq _).trans ?_
  refine Finset.sum_congr rfl fun k _ => finsum_congr fun x => ?_
  have h := H.periodize_shift_congr A.mem_continuousLocal
    (cosetRep_sub_mem A.unfoldedArray S.period
      ⟨L.axialPoint (Quotient.out x) ((k : ℕ) : ℤ), L.axialPoint_mem_axialSublattice _ _⟩)
  exact congrArg Complex.re (congrFun h U)
def normalExponent (L : MirrorLadder) (S : SlabDecomposition) (F : GaugeField 1 → ℂ) (i : ℤ)
    (U : S.period.QuotientField) : ℝ :=
  ∑ᶠ c : L.TransverseQuotient S.period S.count,
    (S.period.periodize ((shift (L.normalPoint (Quotient.out c) i)).actOn F) U).re
theorem periodicSum_normal (U : S.period.QuotientField) :
    A.foldedArray.periodicSum S.period U =
      ∑ i : Fin S.count, (normalExponent L S A.toFun ((i : ℕ) : ℤ) U +
        normalExponent L S A.reflected ((i : ℕ) : ℤ) U) := by
  have := H.finite_transverseQuotient
  have hrep := H.enumerates_normal A
  have : Finite (A.foldedArray.Cosets S.period) :=
    Finite.of_equiv _ hrep.equiv
  refine (finsum_prod_finTwo (C := A.foldedArray.Cosets S.period) _).trans ?_
  rw [hrep.finsum_eq, hrep.finsum_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  · refine finsum_congr fun x => ?_
    have h := H.periodize_shift_congr A.mem_continuousLocal
      (cosetRep_sub_mem A.foldedArray S.period
        ⟨L.normalPoint (Quotient.out x) ((i : ℕ) : ℤ), L.normalPoint_mem_normalSublattice _ _⟩)
    exact congrArg Complex.re (congrFun h U)
  · refine finsum_congr fun x => ?_
    have h := H.periodize_shift_congr A.reflected_mem
      (cosetRep_sub_mem A.foldedArray S.period
        ⟨L.normalPoint (Quotient.out x) ((i : ℕ) : ℤ), L.normalPoint_mem_normalSublattice _ _⟩)
    exact congrArg Complex.re (congrFun h U)
theorem prod_slabExp (t : ℝ) :
    (fun U => ∏ k : ZMod (2 * S.count), A.slabExp S.period S.count t (k.val : ℤ) U) =
      fun U => ((Real.exp (t * A.unfoldedArray.periodicSum S.period U) : ℝ) : ℂ) := by
  funext U
  simp only [H.slabExp_eq_exp]
  rw [← Complex.ofReal_prod, ← Real.exp_sum, H.periodicSum_axial, Finset.mul_sum,
    sum_zmod_val_eq_sum_fin (fun k => t * levelExponent A S.period S.count (k : ℤ) U)]
end Assumptions
namespace Assumptions
variable (H : Assumptions β L w S) (A : L.SlabZeroGenerator)
include H
theorem pullbackField_congr {r r' : LatticeSymmetry 1} (hr : IsClassIsometry S.normal r.toFun)
    (hr' : IsClassIsometry S.normal r'.toFun)
    (h : S.period.descendOrientedLink r = S.period.descendOrientedLink r') :
    S.period.pullbackField r = S.period.pullbackField r' := by
  obtain ⟨-, hB, -, -, -⟩ := H.pullbackFacts β H.beta_pos S.period S.normal S.normal_mem _ S.splits
  obtain ⟨-, -, -, hdep, -⟩ := hB r hr
  exact hdep r' hr' h
theorem groupPullback_eq {r : LatticeSymmetry 1}
    (hr : IsClassIsometry S.normal r.toFun) :
    S.groupPullback (S.period.descendedTorusMap r) =
      S.period.pullbackField r := by
  have hspec : S.InducesTorusMap (S.period.descendedTorusMap r)
      (S.inducingSymmetry (S.period.descendedTorusMap r)) :=
    Classical.epsilon_spec (p := S.InducesTorusMap (S.period.descendedTorusMap r)) ⟨r, hr, rfl⟩
  funext U
  exact congrFun (H.pullbackField_congr hspec.1 hr (congrArg (·.linkMap) hspec.2)) U
theorem torusReflection_add_count_mul (k m : ℤ) :
    S.torusReflection (k + (S.count : ℤ) * m) = S.torusReflection k := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := H.transitivity S
  induction m using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [show k + (S.count : ℤ) * ((i : ℤ) + 1) = (k + (S.count : ℤ) * i) + (S.count : ℤ) by ring, h,
      ih]
  | pred i ih =>
    rw [← ih, ← h (k + (S.count : ℤ) * (-(i : ℤ) - 1))]
    congr 1
    ring
theorem torusReflectionOfClass_intCast (s : ℤ) :
    S.torusReflectionOfClass (s : ZMod (2 * S.count)) = S.torusReflection s := by
  obtain ⟨m, hm⟩ := S.exists_val_eq_add_two_mul_mul s
  rw [SlabDecomposition.torusReflectionOfClass, hm,
    show s + 2 * (S.count : ℤ) * m = s + (S.count : ℤ) * (2 * m) by ring,
    H.torusReflection_add_count_mul]
theorem slabCopy_shift (p : ZMod (2 * S.count)) (i : ℤ) (F : S.period.QuotientField → ℂ) :
    S.slabCopy p (p + 2 * (i : ZMod (2 * S.count))) F =
      S.period.compPullback (shift (S.stepVec i)) F := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h14, -, -, -, -, -, -, -, h22, h23, -, -⟩ :=
    H.transitivity S
  have hc : S.MapsSlabTo p (p + 2 * (i : ZMod (2 * S.count)))
      (S.period.descendedTorusMap (shift (S.stepVec i))) :=
    ⟨Or.inl ⟨i, rfl⟩, h14 i p⟩
  have hg : S.slabTransporter p (p + 2 * (i : ZMod (2 * S.count))) =
      S.period.descendedTorusMap (shift (S.stepVec i)) :=
    (h22 _ _).unique (h23 _ _) hc
  have ht : S.IsGroupTranslation
      (S.slabTransporter p (p + 2 * (i : ZMod (2 * S.count)))) := by
    rw [hg]
    exact ⟨i, rfl⟩
  rw [SlabDecomposition.slabCopy, if_pos ht, hg]
  funext U
  change F (S.groupPullback _ U) = _
  rw [H.groupPullback_eq (isClassIsometry_shift _ _)]
  rfl
theorem slabCopy_reflect (p : ZMod (2 * S.count)) (s : ℤ) (F : S.period.QuotientField → ℂ) :
    S.slabCopy p (2 * (s : ZMod (2 * S.count)) - 1 - p) F =
      fun U => conj (S.period.compPullback (S.reflectSym s) F U) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, -, -, -, -, -, -, -, -, h22, h23, -, h25⟩ :=
    H.transitivity S
  have himg := h13 (s : ZMod (2 * S.count)) (p - (s : ZMod (2 * S.count)))
  rw [H.torusReflectionOfClass_intCast, add_sub_cancel,
    show (s : ZMod (2 * S.count)) - 1 - (p - (s : ZMod (2 * S.count))) =
      2 * (s : ZMod (2 * S.count)) - 1 - p by ring] at himg
  have hc : S.MapsSlabTo p (2 * (s : ZMod (2 * S.count)) - 1 - p)
      (S.torusReflection s) := ⟨Or.inr ⟨s, rfl⟩, himg⟩
  have hg : S.slabTransporter p (2 * (s : ZMod (2 * S.count)) - 1 - p) =
      S.torusReflection s :=
    (h22 _ _).unique (h23 _ _) hc
  have ht : ¬ S.IsGroupTranslation
      (S.slabTransporter p (2 * (s : ZMod (2 * S.count)) - 1 - p)) := by
    rw [hg]
    exact fun h => h25 _ ⟨h, s, rfl⟩
  rw [SlabDecomposition.slabCopy, if_neg ht, hg]
  funext U
  change conj (F (S.groupPullback _ U)) = _
  have hr : IsClassIsometry S.normal (S.reflectSym s).toFun :=
    isClassIsometry_reflectAcross (S.level_allowed s)
  rw [SlabDecomposition.torusReflection, H.groupPullback_eq hr]
  rfl
theorem compPullback_comp {r r' r'' : LatticeSymmetry 1} (hr : IsClassIsometry S.normal r.toFun)
    (hr' : IsClassIsometry S.normal r'.toFun) (h : r''.toFun = r.toFun ∘ r'.toFun)
    {F : S.period.QuotientField → ℂ} (hF : S.period.IsBoundedBorelFn F) :
    S.period.compPullback r (S.period.compPullback r' F) =
      S.period.compPullback r'' F := by
  obtain ⟨-, hB, -, -, -⟩ := H.pullbackFacts β H.beta_pos S.period S.normal S.normal_mem _ S.splits
  obtain ⟨-, -, -, -, -, -, -, -, hc, -⟩ := hB r hr
  exact hc r' r'' hr' h F hF
theorem periodize_actOn {r : LatticeSymmetry 1} (hr : IsClassIsometry S.normal r.toFun)
    {F : GaugeField 1 → ℂ} (hF : F ∈ continuousLocalFunctions 1) :
    S.period.periodize (r.actOn F) =
      S.period.compPullback r (S.period.periodize F) := by
  obtain ⟨-, hB, -, -, -⟩ := H.pullbackFacts β H.beta_pos S.period S.normal S.normal_mem _ S.splits
  obtain ⟨-, -, -, -, -, hp, -⟩ := hB r hr
  exact hp F hF
theorem compPullback_isBoundedBorelFn {r : LatticeSymmetry 1}
    (hr : IsClassIsometry S.normal r.toFun)
    {F : S.period.QuotientField → ℂ} (hF : S.period.IsBoundedBorelFn F) :
    S.period.IsBoundedBorelFn (S.period.compPullback r F) := by
  obtain ⟨-, hB, -, -, -⟩ := H.pullbackFacts β H.beta_pos S.period S.normal S.normal_mem _ S.splits
  obtain ⟨-, -, -, -, -, -, hb, -⟩ := hB r hr
  exact (hb F hF).1
theorem slabExp_isBoundedBorelFn (t : ℝ) (ht : 0 ≤ t) (k : ℤ) :
    S.period.IsBoundedBorelFn (A.slabExp S.period S.count t k) := by
  obtain ⟨h1, h2, -⟩ := H.slabExp_mem A t ht k
  exact ⟨h1, h2⟩
theorem compPullback_slabExp_zero {r : LatticeSymmetry 1}
    (hr : IsClassIsometry S.normal r.toFun) (t : ℝ) (U : S.period.QuotientField) :
    S.period.compPullback r (A.slabExp S.period S.count t 0) U =
      Complex.exp ((t : ℂ) * ∑ᶠ c : L.TransverseQuotient S.period S.count,
        S.period.periodize
          (r.actOn ((shift (L.parallelPoint (Quotient.out c))).actOn
            A.toFun)) U) := by
  have hs : ∀ v : parallelPeriodLattice L.normal, L.axialPoint v 0 = L.parallelPoint v := by
    intro v
    rw [MirrorLadder.axialPoint, levelShift_zero, add_zero]
  refine congrArg Complex.exp (congrArg ((t : ℂ) * ·) (finsum_congr fun c => ?_))
  rw [H.periodize_actOn hr (shift_actOn_mem A.mem_continuousLocal _)]
  simp only [PeriodSublattice.compPullback, MirrorLadder.SlabZeroGenerator.periodicTerm, hs]
theorem slabExp_eq_compPullback (t : ℝ) (k : ℤ) :
    A.slabExp S.period S.count t k =
      S.period.compPullback (shift (L.levelShift k))
        (A.slabExp S.period S.count t 0) := by
  funext U
  rw [H.compPullback_slabExp_zero A (isClassIsometry_shift _ _),
    MirrorLadder.SlabZeroGenerator.slabExp]
  refine congrArg Complex.exp (congrArg ((t : ℂ) * ·) (finsum_congr fun c => ?_))
  rw [H.shift_actOn_shift, MirrorLadder.SlabZeroGenerator.periodicTerm, MirrorLadder.axialPoint,
    add_comm]
end Assumptions
theorem zmod_eq_two_mul_or_two_mul_sub_one {N : ℕ} [NeZero N] (j : ZMod N) :
    (∃ i : ℤ, j = 2 * (i : ZMod N)) ∨ ∃ s : ℤ, j = 2 * (s : ZMod N) - 1 := by
  have hj : ((j.val : ℤ) : ZMod N) = j := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rcases Int.even_or_odd' (j.val : ℤ) with ⟨c, hc | hc⟩
  · refine Or.inl ⟨c, ?_⟩
    have : j = ((2 * c : ℤ) : ZMod N) := by rw [← hc]; exact hj.symm
    rw [this]
    push_cast
    ring
  · refine Or.inr ⟨c + 1, ?_⟩
    have : j = ((2 * c + 1 : ℤ) : ZMod N) := by rw [← hc]; exact hj.symm
    rw [this]
    push_cast
    ring
namespace Assumptions
variable (H : Assumptions β L w S) (A : L.SlabZeroGenerator)
include H
theorem compPullback_shift_shift (x y : LatticePoint 1) {F : S.period.QuotientField → ℂ}
    (hF : S.period.IsBoundedBorelFn F) :
    S.period.compPullback (shift x) (S.period.compPullback (shift y) F) =
      S.period.compPullback (shift (x + y)) F :=
  H.compPullback_comp (isClassIsometry_shift _ _) (isClassIsometry_shift _ _)
    (funext fun u => by
      change u + ((x : AmbientSpace) + (y : AmbientSpace)) = u + (y : AmbientSpace) + (x : AmbientSpace)
      abel) hF
theorem normal_dotProduct_levelShift (k : ℤ) :
    S.normal ⬝ᵥ (L.levelShift k : AmbientSpace) = (k : ℝ) * (S.width : ℝ) := by
  change S.normal ⬝ᵥ (((k : ℝ) * (L.spacing : ℝ)) • firstNonzeroBasisVec L.normal) = _
  rw [H.adapted.normal_eq, H.adapted.width_eq, dotProduct_smul,
    dotProduct_firstNonzeroBasisVec L.normal_mem]
  simp
theorem reflectSym_comp_shift (s k : ℤ) :
    (S.reflectSym (s + k)).toFun ∘ (shift (L.levelShift k)).toFun =
      (shift (L.levelShift k)).toFun ∘ (S.reflectSym s).toFun := by
  funext x
  change reflectAcross S.normal (S.level (s + k)) (x + (L.levelShift k : AmbientSpace)) =
    reflectAcross S.normal (S.level s) x + (L.levelShift k : AmbientSpace)
  simp only [reflectAcross, dotProduct_add, H.normal_dotProduct_levelShift, SlabDecomposition.level]
  push_cast
  have : S.normal ⬝ᵥ x + (k : ℝ) * (S.width : ℝ) -
      (S.baseLevel + ((s : ℝ) + (k : ℝ)) * (S.width : ℝ)) =
      S.normal ⬝ᵥ x - (S.baseLevel + (s : ℝ) * (S.width : ℝ)) := by ring
  rw [this]
  abel
theorem slabCopy_slabExp (t : ℝ) (ht : 0 ≤ t) (k : ℤ) (j : ZMod (2 * S.count)) :
    S.slabCopy (k : ZMod (2 * S.count)) (j + (k : ZMod (2 * S.count)))
        (A.slabExp S.period S.count t k) =
      S.period.compPullback (shift (L.levelShift k))
        (S.slabCopy 0 j (A.slabExp S.period S.count t 0)) := by
  have hb := H.slabExp_isBoundedBorelFn A t ht 0
  rcases zmod_eq_two_mul_or_two_mul_sub_one j with ⟨i, rfl⟩ | ⟨s, rfl⟩
  · have h0 := H.slabCopy_shift 0 i (A.slabExp S.period S.count t 0)
    rw [zero_add] at h0
    rw [h0, add_comm, H.slabCopy_shift, H.slabExp_eq_compPullback A t k,
      H.compPullback_shift_shift _ _ hb, H.compPullback_shift_shift _ _ hb, add_comm]
  · have h0 := H.slabCopy_reflect 0 s (A.slabExp S.period S.count t 0)
    rw [sub_zero] at h0
    have hk := H.slabCopy_reflect (k : ZMod (2 * S.count)) (s + k)
      (A.slabExp S.period S.count t k)
    rw [show 2 * ((s + k : ℤ) : ZMod (2 * S.count)) - 1 - (k : ZMod (2 * S.count)) =
      2 * (s : ZMod (2 * S.count)) - 1 + (k : ZMod (2 * S.count)) by push_cast; ring] at hk
    rw [h0, hk, H.slabExp_eq_compPullback A t k]
    have hθ : ∀ s : ℤ, IsClassIsometry S.normal (S.reflectSym s).toFun := fun s =>
      isClassIsometry_reflectAcross (S.level_allowed s)
    have hτ : IsClassIsometry S.normal (shift (L.levelShift k)).toFun :=
      isClassIsometry_shift _ _
    have e1 := H.compPullback_comp (r'' := (S.reflectSym (s + k)).comp (shift (L.levelShift k)))
      (hθ (s + k)) hτ rfl hb
    have e2 := H.compPullback_comp (r'' := (S.reflectSym (s + k)).comp (shift (L.levelShift k)))
      hτ (hθ s) (H.reflectSym_comp_shift s k) hb
    funext U
    change conj (S.period.compPullback (S.reflectSym (s + k))
        (S.period.compPullback (shift (L.levelShift k))
          (A.slabExp S.period S.count t 0)) U) =
      conj (S.period.compPullback (shift (L.levelShift k))
        (S.period.compPullback (S.reflectSym s) (A.slabExp S.period S.count t 0)) U)
    rw [e1, e2]
theorem slabCopy_isBoundedBorelFn (j : ZMod (2 * S.count)) {F : S.period.QuotientField → ℂ}
    (hF : S.period.IsBoundedBorelFn F) : S.period.IsBoundedBorelFn (S.slabCopy 0 j F) := by
  rcases zmod_eq_two_mul_or_two_mul_sub_one j with ⟨i, rfl⟩ | ⟨s, rfl⟩
  · have h0 := H.slabCopy_shift 0 i F
    rw [zero_add] at h0
    rw [h0]
    exact H.compPullback_isBoundedBorelFn (isClassIsometry_shift _ _) hF
  · have h0 := H.slabCopy_reflect 0 s F
    rw [sub_zero] at h0
    rw [h0]
    obtain ⟨hm, C, hC⟩ := H.compPullback_isBoundedBorelFn (r := S.reflectSym s)
      (isClassIsometry_reflectAcross (S.level_allowed s)) hF
    exact ⟨Complex.continuous_conj.measurable.comp hm, C, fun U => by
      rw [RCLike.norm_conj]
      exact hC U⟩
theorem continuous_totalFaceEnergy : Continuous S.period.totalFaceEnergy := by
  have hE := H.quotientFacts.1 S.period
  have := hE.finite_quotientPlaquette
  have := Fintype.ofFinite S.period.QuotientPlaquette
  have e : S.period.totalFaceEnergy = fun U =>
      ∑ p : S.period.QuotientPlaquette, S.period.quotientFaceEnergy U p := by
    funext U
    rw [PeriodSublattice.totalFaceEnergy, finsum_eq_sum_of_fintype]
  rw [e]
  exact continuous_finsetSum _ fun p _ => hE.continuous_quotientFaceEnergy p
theorem totalFaceEnergy_nonneg (U : S.period.QuotientField) :
    0 ≤ S.period.totalFaceEnergy U := by
  have hE := H.quotientFacts.1 S.period
  have := hE.finite_quotientPlaquette
  have := Fintype.ofFinite S.period.QuotientPlaquette
  rw [PeriodSublattice.totalFaceEnergy, finsum_eq_sum_of_fintype]
  exact Finset.sum_nonneg fun p _ => (hE.quotientFaceEnergy_mem_Icc p U).1
theorem boltzmannWeight_isBoundedBorelFn :
    S.period.IsBoundedBorelFn (fun U => ((S.period.boltzmannWeight β U : ℝ) : ℂ)) := by
  have hc : Continuous fun U => ((S.period.boltzmannWeight β U : ℝ) : ℂ) := by
    refine Complex.continuous_ofReal.comp (Real.continuous_exp.comp ?_)
    exact continuous_const.mul H.continuous_totalFaceEnergy
  refine ⟨hc.measurable, 1, fun U => ?_⟩
  rw [Complex.norm_real, PeriodSublattice.boltzmannWeight, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  have h := H.totalFaceEnergy_nonneg U
  have hp := H.beta_pos
  change -β * S.period.totalFaceEnergy U ≤ 0
  nlinarith
theorem isBoundedBorelFn_prod {ι : Type*} (s : Finset ι)
    {F : ι → S.period.QuotientField → ℂ}
    (h : ∀ i, S.period.IsBoundedBorelFn (F i)) :
    S.period.IsBoundedBorelFn (fun U => ∏ i ∈ s, F i U) := by
  have hd : ∀ G : S.period.QuotientField → ℂ,
      PeriodSublattice.DependsOnlyOn G Set.univ := fun G U U' hU => by
    rw [funext fun b => hU b (Set.mem_univ b)]
  have hm : ∀ i, F i ∈ S.period.boundedAlgebra Set.univ := fun i =>
    ⟨(h i).1, (h i).2, hd _⟩
  have hp := Subalgebra.prod_mem _ (t := s) fun i _ => hm i
  obtain ⟨h1, h2, -⟩ := hp
  have e : (∏ i ∈ s, F i) = fun U => ∏ i ∈ s, F i U := by
    funext U
    simp
  rw [e] at h1 h2
  exact ⟨h1, h2⟩
theorem fold_slabExp (t : ℝ) (ht : 0 ≤ t) (k : ℤ) :
    S.fold β (k : ZMod (2 * S.count)) (A.slabExp S.period S.count t k) =
      S.fold β 0 (A.slabExp S.period S.count t 0) := by
  obtain ⟨-, hB, -, -, -⟩ := H.pullbackFacts β H.beta_pos S.period S.normal S.normal_mem _ S.splits
  have hτ : IsClassIsometry S.normal (shift (L.levelShift k)).toFun :=
    isClassIsometry_shift _ _
  obtain ⟨-, hhaar, -, -, -, -, -, -, -, -, hsum, -, -⟩ := hB _ hτ
  set G : S.period.QuotientField → ℂ := fun U =>
    (∏ j : ZMod (2 * S.count), S.slabCopy 0 j (A.slabExp S.period S.count t 0) U) *
      ((S.period.boltzmannWeight β U : ℝ) : ℂ) with hG
  have hGb : S.period.IsBoundedBorelFn G := by
    have h1 := H.isBoundedBorelFn_prod Finset.univ
      (fun j => H.slabCopy_isBoundedBorelFn j (H.slabExp_isBoundedBorelFn A t ht 0))
    have h2 := H.boltzmannWeight_isBoundedBorelFn
    obtain ⟨C, hC⟩ := h1.2
    obtain ⟨C', hC'⟩ := h2.2
    refine ⟨h1.1.mul h2.1, C * C', fun U => ?_⟩
    rw [hG, norm_mul]
    exact mul_le_mul (hC U) (hC' U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
  have hW : ∀ U, S.period.boltzmannWeight β
      (S.period.pullbackField (shift (L.levelShift k)) U) =
      S.period.boltzmannWeight β U := by
    intro U
    have := congrFun hsum U
    change S.period.totalFaceEnergy _ = S.period.totalFaceEnergy U at this
    change Real.exp (-β * S.period.totalFaceEnergy _) =
      Real.exp (-β * S.period.totalFaceEnergy U)
    rw [this]
  have hinteg : ∀ U,
      (∏ j : ZMod (2 * S.count), S.slabCopy (k : ZMod (2 * S.count)) j
          (A.slabExp S.period S.count t k) U) * ((S.period.boltzmannWeight β U : ℝ) : ℂ) =
        G (S.period.pullbackField (shift (L.levelShift k)) U) := by
    intro U
    rw [hG]
    simp only
    rw [hW U, ← Equiv.prod_comp (Equiv.addRight (k : ZMod (2 * S.count)))]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    exact congrFun (H.slabCopy_slabExp A t ht k j) U
  rw [SlabDecomposition.fold, SlabDecomposition.fold]
  simp only [hinteg]
  exact hhaar.2.2 G hGb.1 hGb.2
end Assumptions
namespace Assumptions
variable (H : Assumptions β L w S) (A : L.SlabZeroGenerator)
include H
theorem stepVec_eq (i : ℤ) : S.stepVec i = L.dualShift i := by
  refine Subtype.ext ?_
  change (2 * (i : ℝ) * (S.width : ℝ)) • dualVector S.normal =
    (2 * (i : ℝ) * (L.spacing : ℝ)) • dualVector L.normal
  rw [H.adapted.normal_eq, H.adapted.width_eq]
theorem slabCopy_two_mul (t : ℝ) (i : ℤ) (U : S.period.QuotientField) :
    S.slabCopy 0 (2 * (i : ZMod (2 * S.count))) (A.slabExp S.period S.count t 0) U =
      ((Real.exp (t * normalExponent L S A.toFun i U) : ℝ) : ℂ) := by
  have := H.finite_transverseQuotient
  have h0 := H.slabCopy_shift 0 i (A.slabExp S.period S.count t 0)
  rw [zero_add] at h0
  rw [h0, H.compPullback_slabExp_zero A (isClassIsometry_shift _ _) t U]
  have e : ∀ c : L.TransverseQuotient S.period S.count,
      S.period.periodize ((shift (S.stepVec i)).actOn
        ((shift (L.parallelPoint (Quotient.out c))).actOn A.toFun)) U =
      S.period.periodize ((shift (L.normalPoint (Quotient.out c) i)).actOn
        A.toFun) U := fun c => by
    rw [H.shift_actOn_shift, H.stepVec_eq, MirrorLadder.normalPoint, add_comm]
  simp only [e]
  exact cexp_mul_finsum_of_real _ (fun c => A.im_eq_zero _) t
theorem reflectSym_shift (i : ℤ) (v : parallelPeriodLattice L.normal) :
    (S.reflectSym (i + 1)).actOn ((shift (L.parallelPoint v)).actOn A.toFun) =
      (shift (L.normalPoint v i)).actOn A.reflected := by
  obtain ⟨-, -, -, -, -, -, -, hk⟩ := H.foldFacts L A
  have hv : L.parallelPoint v ∈ L.normalSublattice :=
    AddSubgroup.mem_addSubgroupOf.mpr (mem_normalPeriodLattice_iff.mpr ⟨v, v.2, 0, by
      simp [MirrorLadder.parallelPoint]⟩)
  have hfix : linearReflect L.normal (v : AmbientSpace) = v :=
    (H.latticeFacts.1 L.normal L.normal_mem L.spacing L.even_spacing L.two_le_spacing).1.2.2 v v.2
  have h := (hk (i + 1)).2.1 ⟨L.parallelPoint v, hv⟩
    ⟨L.normalPoint v i, L.normalPoint_mem_normalSublattice v i⟩
    (0 : Fin 2) (by
      change (v : AmbientSpace) + (2 * (i : ℝ) * (L.spacing : ℝ)) • dualVector L.normal =
        linearReflect L.normal (v : AmbientSpace) + _
      rw [hfix]
      congr 2
      push_cast
      ring)
  have e : S.reflectSym (i + 1) = (L.rungAt (i + 1)).reflectSymmetry := by
    refine latticeSymmetry_ext_toFun ?_
    change reflectAcross S.normal (S.level (i + 1)) =
      reflectAcross L.normal (L.offset + ((i + 1 : ℤ) : ℝ) * (L.spacing : ℝ))
    rw [H.adapted.normal_eq, H.level_eq]
  rw [e]
  exact h
theorem slabCopy_two_mul_add_one (t : ℝ) (i : ℤ) (U : S.period.QuotientField) :
    S.slabCopy 0 (2 * (i : ZMod (2 * S.count)) + 1) (A.slabExp S.period S.count t 0) U =
      ((Real.exp (t * normalExponent L S A.reflected i U) : ℝ) : ℂ) := by
  have := H.finite_transverseQuotient
  have h0 := H.slabCopy_reflect 0 (i + 1) (A.slabExp S.period S.count t 0)
  rw [show 2 * ((i + 1 : ℤ) : ZMod (2 * S.count)) - 1 - 0 =
    2 * (i : ZMod (2 * S.count)) + 1 by push_cast; ring] at h0
  rw [h0]
  have hr : IsClassIsometry S.normal (S.reflectSym (i + 1)).toFun :=
    isClassIsometry_reflectAcross (S.level_allowed _)
  simp only []
  rw [H.compPullback_slabExp_zero A hr t U]
  simp only [H.reflectSym_shift A i]
  rw [cexp_mul_finsum_of_real (fun c : L.TransverseQuotient S.period S.count => S.period.periodize
    ((shift (L.normalPoint (Quotient.out c) i)).actOn A.reflected) U)
    (fun c => A.reflected_im _) t, Complex.conj_ofReal]
  rfl
theorem prod_slabCopy (t : ℝ) :
    (fun U => ∏ j : ZMod (2 * S.count), S.slabCopy 0 j (A.slabExp S.period S.count t 0) U) =
      fun U => ((Real.exp (t * A.foldedArray.periodicSum S.period U) : ℝ) : ℂ) := by
  funext U
  have hinj : Function.Injective (fun p : Fin S.count × Fin 2 =>
      (((2 * (p.1 : ℕ) + (p.2 : ℕ) : ℕ)) : ZMod (2 * S.count))) := by
    rintro ⟨i, ι⟩ ⟨i', ι'⟩ h
    have hi := i.2
    have hi' := i'.2
    have hι := ι.2
    have hι' := ι'.2
    have h1 := congrArg ZMod.val h
    simp only at h1
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1
    exact Prod.ext (Fin.ext (by simp only; omega)) (Fin.ext (by simp only; omega))
  have hbij : Function.Bijective (fun p : Fin S.count × Fin 2 =>
      (((2 * (p.1 : ℕ) + (p.2 : ℕ) : ℕ)) : ZMod (2 * S.count))) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by
      rw [ZMod.card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm]⟩
  rw [← hbij.prod_comp (fun j => S.slabCopy 0 j (A.slabExp S.period S.count t 0) U),
    Fintype.prod_prod_type, H.periodicSum_normal, Finset.mul_sum, Real.exp_sum,
    Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_two]
  have e0 : ((2 * ((i : ℕ)) + ((0 : Fin 2) : ℕ) : ℕ) : ZMod (2 * S.count)) =
      2 * ((((i : ℕ) : ℤ)) : ZMod (2 * S.count)) := by
    push_cast
    simp
  have e1 : ((2 * ((i : ℕ)) + ((1 : Fin 2) : ℕ) : ℕ) : ZMod (2 * S.count)) =
      2 * ((((i : ℕ) : ℤ)) : ZMod (2 * S.count)) + 1 := by
    push_cast
    simp
  simp only []
  rw [e0, e1, H.slabCopy_two_mul, H.slabCopy_two_mul_add_one, ← Complex.ofReal_mul,
    ← Real.exp_add, mul_add]
theorem integral_eq_tiltedPartition (𝔸 : LocalObservableArray) (t : ℝ) :
    ∫ U, ((Real.exp (t * 𝔸.periodicSum S.period U) : ℝ) : ℂ) *
        ((S.period.boltzmannWeight β U : ℝ) : ℂ) ∂S.period.quotientHaar =
      ((𝔸.tiltedPartition S.period β t : ℝ) : ℂ) := by
  rw [LocalObservableArray.tiltedPartition, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only
  rw [← Complex.ofReal_mul, LocalObservableArray.tiltedWeight, PeriodSublattice.boltzmannWeight,
    ← Real.exp_add]
  congr 2
  ring
theorem fold_eq_tiltedPartition (t : ℝ) :
    S.fold β 0 (A.slabExp S.period S.count t 0) =
      ((A.foldedArray.tiltedPartition S.period β t : ℝ) : ℂ) := by
  rw [← H.integral_eq_tiltedPartition, SlabDecomposition.fold]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  exact congrArg (· * ((S.period.boltzmannWeight β U : ℝ) : ℂ)) (congrFun (H.prod_slabCopy A t) U)
theorem tiltedPartition_le (hC : SlabChessboardEstimate) (t : ℝ)
    (ht : 0 ≤ t) :
    A.unfoldedArray.tiltedPartition S.period β t ≤
      A.foldedArray.tiltedPartition S.period β t := by
  set F : ZMod (2 * S.count) → S.period.QuotientField → ℂ := fun k =>
    A.slabExp S.period S.count t (k.val : ℤ) with hF
  have hmem : ∀ k, F k ∈ S.slabAlgebraOfClass k := fun k => H.slabExp_mem A t ht _
  have hreal : ∀ k, S.IsRealWithPosInf (F k) := fun k =>
    ⟨H.slabExp_im A t _, lt_of_lt_of_le (Real.exp_pos _) (H.exp_bound_le_iInf A t ht _)⟩
  obtain ⟨hpos, -, hle⟩ : _ ∧ _ := hC S β H.beta_pos F hmem hreal
  have hfold : ∀ k, S.fold β k (F k) =
      ((A.foldedArray.tiltedPartition S.period β t : ℝ) : ℂ) := by
    intro k
    have h := H.fold_slabExp A t ht (k.val : ℤ)
    rw [Int.cast_natCast, ZMod.natCast_zmod_val] at h
    rw [hF]
    simp only
    rw [h, H.fold_eq_tiltedPartition]
  have hint : S.familyIntegral β F =
      ((A.unfoldedArray.tiltedPartition S.period β t : ℝ) : ℂ) := by
    rw [← H.integral_eq_tiltedPartition, SlabDecomposition.familyIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    exact congrArg (· * ((S.period.boltzmannWeight β U : ℝ) : ℂ)) (congrFun (H.prod_slabExp A t) U)
  have hZ : 0 < A.foldedArray.tiltedPartition S.period β t := by
    have h := (hpos 0).2
    rwa [hfold, Complex.ofReal_re] at h
  rw [hint, Complex.ofReal_re] at hle
  simp only [hfold, Complex.ofReal_re] at hle
  rw [Finset.prod_const, Finset.card_univ, ZMod.card, ← Real.rpow_natCast,
    ← Real.rpow_mul hZ.le] at hle
  have hJ : (2 * (S.count : ℝ)) ≠ 0 := by
    have := S.one_le_count
    have h1 : (1 : ℝ) ≤ S.count := by exact_mod_cast this
    linarith
  have h1 : 1 / (2 * (S.count : ℝ)) * ((2 * S.count : ℕ) : ℝ) = 1 := by
    push_cast
    exact one_div_mul_cancel hJ
  rwa [h1, Real.rpow_one] at hle
end Assumptions
theorem chessboardFoldingEstimate_holds (h₁ : AdaptedTorusProperties)
    (h₂ : FoldedArrayMirrorProperties)
    (h₃ : PeriodicQuotient.FinitenessClaim)
    (h₄ : PeriodLatticeProperties)
    (h₅ : SymmetryActionRules.Statement)
    (h₆ : SplitTorusPullbacks) (h₇ : SlabActionSimplyTransitive)
    (h₈ : SlabChessboardEstimate) :
    ChessboardFoldingEstimate := by
  intro β hβ L A w S hS
  have H : Assumptions β L w S := ⟨hβ, hS, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  refine ⟨H.finite_transverseQuotient, fun k v v' h => H.periodicTerm_congr A k h, fun t ht => ?_⟩
  intro f bound
  refine ⟨H.slabExp_add_two_mul A t, fun k => ⟨H.slabExp_mem A t ht k, H.slabExp_im A t k,
    H.exp_bound_le_iInf A t ht k⟩, Real.exp_pos _, (H.enumerates_axial A).uniqueRepresentation,
    H.prod_slabExp A t, fun k => ⟨H.slabExp_eq_compPullback A t k,
      fun j => H.slabCopy_slabExp A t ht k j, H.fold_slabExp A t ht k⟩,
    (H.enumerates_normal A).uniqueRepresentation, H.prod_slabCopy A t, H.tiltedPartition_le A h₈ t ht⟩
end ChessboardFolding
end YangMills.Construction.NormalFamilies

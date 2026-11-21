import YangMills.Construction.ReflectionPositivity.SimpleTransitivityOnTheSlabs
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
open NormalFamilies
open PeriodicLattice (coordVec)
namespace SlabTransitivity
theorem dotProduct_reflectAcross {n : AmbientSpace} (hn : n ∈ normalSet) (c : ℝ) (x : AmbientSpace) :
    n ⬝ᵥ reflectAcross n c x = 2 * c - n ⬝ᵥ x := by
  rw [reflectAcross, dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_dualVector hn]
  ring
variable (S : SlabDecomposition)
abbrev shiftMap (j : ℤ) : S.period.TorusMap :=
  S.period.descendedTorusMap (shift (S.stepVec j))
theorem stepVec_coe (j : ℤ) :
    ((S.stepVec j : LatticePoint 1) : AmbientSpace) =
      (2 * (j : ℝ) * (S.width : ℝ)) • dualVector S.normal := rfl
theorem width_pos : (0 : ℝ) < (S.width : ℝ) := by
  have h := S.two_le_width
  exact_mod_cast (by omega : (0 : ℤ) < S.width)
theorem dotProduct_add_stepVec (j : ℤ) (x : AmbientSpace) :
    S.normal ⬝ᵥ (x + ((S.stepVec j : LatticePoint 1) : AmbientSpace)) =
      S.normal ⬝ᵥ x + 2 * (j : ℝ) * (S.width : ℝ) := by
  rw [dotProduct_add, stepVec_coe, dotProduct_smul, smul_eq_mul,
    dotProduct_dualVector S.normal_mem, mul_one]
theorem isClassIsometry_reflectSym (k : ℤ) : IsClassIsometry S.normal (S.reflectSym k).toFun :=
  isClassIsometry_reflectAcross (S.level_allowed k)
theorem isClassIsometry_shiftStep (j : ℤ) :
    IsClassIsometry S.normal (shift (S.stepVec j)).toFun :=
  isClassIsometry_shift _ _
theorem stepVec_count_mul_mem_periods (m : ℤ) :
    S.stepVec ((S.count : ℤ) * m) ∈ S.period.periods := by
  obtain ⟨P, hP⟩ := S.splits.2.2
  have h₁ : (2 * (((S.count : ℤ) * S.width : ℤ) : ℝ)) •
      ReflectionPositivity.NormalPlanes.normalOverNormSq S.normal ∈ S.period.toAmbient := by
    rw [← hP.sup_eq]
    exact (le_sup_right : PeriodSublattice.axialSubgroup S.normal _ ≤ _)
      (AddSubgroup.mem_zmultiples _)
  have h₂ := zsmul_mem h₁ m
  obtain ⟨γ, hγ, e⟩ := AddSubgroup.mem_map.1 h₂
  have e' : γ = S.stepVec ((S.count : ℤ) * m) := by
    apply Subtype.ext
    have e₂ : (γ : AmbientSpace) = _ := e
    have hs : ReflectionPositivity.NormalPlanes.normalOverNormSq S.normal = dualVector S.normal := by
      rw [ReflectionPositivity.NormalPlanes.normalOverNormSq, dualVector, normSq_eq_dotProduct]
    rw [e₂, stepVec_coe, hs, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    congr 1
    push_cast
    ring
  exact e' ▸ hγ
section Descent
variable (D : SplitTorusDescent)
include D
theorem exists_height_sub_eq {x y : LatticePoint 1}
    (h : S.period.quotientMap x = S.period.quotientMap y) :
    ∃ k : ℤ, S.normal ⬝ᵥ (x : AmbientSpace) - S.normal ⬝ᵥ (y : AmbientSpace) =
      2 * (S.halfPeriod : ℝ) * (k : ℝ) := by
  obtain ⟨-, -, -, h4, -⟩ := D S.period S.normal S.normal_mem S.halfPeriod S.baseLevel
    S.baseLevel_allowed 0 S.splits
  exact h4 x y h
theorem shift_descends (j : ℤ) : S.period.DescendsToQuotient (shift (S.stepVec j)) := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := D S.period S.normal S.normal_mem S.halfPeriod S.baseLevel
    S.baseLevel_allowed (S.stepVec j) S.splits
  exact h8
theorem reflectSym_descends (k : ℤ) : S.period.DescendsToQuotient (S.reflectSym k) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := D S.period S.normal S.normal_mem S.halfPeriod
    (S.level k) (S.level_allowed k) 0 S.splits
  exact h10
theorem descendedTorusMap_compose {R R' R'' : LatticeSymmetry 1}
    (hR : IsClassIsometry S.normal R.toFun)
    (hR' : IsClassIsometry S.normal R'.toFun) (h : R''.toFun = R.toFun ∘ R'.toFun) :
    (S.period.descendedTorusMap R).compose (S.period.descendedTorusMap R') =
      S.period.descendedTorusMap R'' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h15, -⟩ := D S.period S.normal S.normal_mem
    S.halfPeriod S.baseLevel S.baseLevel_allowed 0 S.splits
  obtain ⟨a, b, c⟩ := h15 R R' R'' hR hR' h
  exact PeriodSublattice.TorusMap.ext a.symm b.symm c.symm
theorem shiftMap_count_mul (m : ℤ) :
    shiftMap S ((S.count : ℤ) * m) = PeriodSublattice.TorusMap.identity S.period := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, -⟩ := D S.period S.normal S.normal_mem
    S.halfPeriod S.baseLevel S.baseLevel_allowed (S.stepVec ((S.count : ℤ) * m)) S.splits
  obtain ⟨a, b, c⟩ := h12 (stepVec_count_mul_mem_periods S m)
  exact PeriodSublattice.TorusMap.ext a b c
theorem shiftMap_zero : shiftMap S 0 = PeriodSublattice.TorusMap.identity S.period := by
  have h := shiftMap_count_mul S D 0
  rwa [mul_zero] at h
theorem shiftMap_compose_shiftMap (j j' : ℤ) :
    (shiftMap S j).compose (shiftMap S j') = shiftMap S (j + j') := by
  refine descendedTorusMap_compose S D (isClassIsometry_shiftStep S j)
    (isClassIsometry_shiftStep S j') ?_
  funext x
  change x + ((S.stepVec (j + j') : LatticePoint 1) : AmbientSpace) =
    x + ((S.stepVec j' : LatticePoint 1) : AmbientSpace) +
      ((S.stepVec j : LatticePoint 1) : AmbientSpace)
  simp only [stepVec_coe]
  push_cast
  module
theorem shiftMap_compose_torusReflection (j s : ℤ) :
    (shiftMap S j).compose (S.torusReflection s) = S.torusReflection (s + j) := by
  refine descendedTorusMap_compose S D (isClassIsometry_shiftStep S j)
    (isClassIsometry_reflectSym S s) ?_
  funext x
  change reflectAcross S.normal (S.level (s + j)) x =
    reflectAcross S.normal (S.level s) x + ((S.stepVec j : LatticePoint 1) : AmbientSpace)
  simp only [reflectAcross, stepVec_coe, SlabDecomposition.level]
  push_cast
  module
theorem torusReflection_compose_shiftMap (s j : ℤ) :
    (S.torusReflection s).compose (shiftMap S j) = S.torusReflection (s - j) := by
  refine descendedTorusMap_compose S D (isClassIsometry_reflectSym S s)
    (isClassIsometry_shiftStep S j) ?_
  funext x
  change reflectAcross S.normal (S.level (s - j)) x =
    reflectAcross S.normal (S.level s) (x + ((S.stepVec j : LatticePoint 1) : AmbientSpace))
  simp only [reflectAcross, dotProduct_add_stepVec]
  simp only [stepVec_coe, SlabDecomposition.level]
  push_cast
  module
theorem torusReflection_compose_torusReflection (s' s : ℤ) :
    (S.torusReflection s').compose (S.torusReflection s) = shiftMap S (s' - s) := by
  refine descendedTorusMap_compose S D (isClassIsometry_reflectSym S s')
    (isClassIsometry_reflectSym S s) ?_
  funext x
  change x + ((S.stepVec (s' - s) : LatticePoint 1) : AmbientSpace) =
    reflectAcross S.normal (S.level s') (reflectAcross S.normal (S.level s) x)
  rw [reflectAcross, dotProduct_reflectAcross S.normal_mem]
  simp only [reflectAcross, stepVec_coe, SlabDecomposition.level]
  push_cast
  module
theorem shiftMap_eq_of_dvd {j j' : ℤ} (h : (S.count : ℤ) ∣ j - j') :
    shiftMap S j = shiftMap S j' := by
  obtain ⟨m, hm⟩ := h
  have e : j = j' + (S.count : ℤ) * m := by linarith
  rw [e, ← shiftMap_compose_shiftMap S D, shiftMap_count_mul S D]
  rfl
theorem torusReflection_eq_of_dvd {s s' : ℤ} (h : (S.count : ℤ) ∣ s - s') :
    S.torusReflection s = S.torusReflection s' := by
  obtain ⟨m, hm⟩ := h
  have e : s = s' + (S.count : ℤ) * m := by linarith
  rw [e, ← shiftMap_compose_torusReflection S D, shiftMap_count_mul S D]
  rfl
end Descent
theorem quotientMap_mem_slabAt (k : ℤ) (x : LatticePoint 1) (m : ℤ)
    (h₁ : S.level k ≤ S.normal ⬝ᵥ (x : AmbientSpace) + 2 * (S.halfPeriod : ℝ) * (m : ℝ))
    (h₂ : S.normal ⬝ᵥ (x : AmbientSpace) + 2 * (S.halfPeriod : ℝ) * (m : ℝ) ≤ S.level (k + 1)) :
    S.period.quotientMap x ∈ S.slabAt k :=
  ⟨_, ⟨x, rfl, m, rfl⟩, h₁, h₂⟩
theorem image_eq_of_compose_eq_identity {g g' : S.period.TorusMap} {A B : Set S.period.QuotientTorus}
    (h : g.compose g' = PeriodSublattice.TorusMap.identity S.period) (hA : g.pointMap '' A ⊆ B)
    (hB : g'.pointMap '' B ⊆ A) : g.pointMap '' A = B :=
  hA.antisymm fun y hy => ⟨g'.pointMap y, hB ⟨y, hy, rfl⟩,
    congrFun (congrArg PeriodSublattice.TorusMap.pointMap h) y⟩
theorem exists_latticePoint_height (u : ℤ) :
    ∃ x : LatticePoint 1, S.normal ⬝ᵥ (x : AmbientSpace) = (u : ℝ) := by
  have hm : firstNonzeroBasisVec S.normal ∈ latticeSubgroup 1 :=
    ⟨Pi.single (firstNonzeroIndex S.normal) 1, fun μ => by
      by_cases h : μ = firstNonzeroIndex S.normal
      · subst h
        simp [firstNonzeroBasisVec, coordVec]
      · simp [firstNonzeroBasisVec, coordVec, h]⟩
  refine ⟨u • ⟨_, hm⟩, ?_⟩
  change S.normal ⬝ᵥ (u • firstNonzeroBasisVec S.normal) = (u : ℝ)
  rw [← Int.cast_smul_eq_zsmul ℝ, dotProduct_smul, smul_eq_mul,
    dotProduct_firstNonzeroBasisVec S.normal_mem, mul_one]
theorem mirrorLocus_subset_slabAt (k : ℤ) : S.mirrorLocus k ⊆ S.slabAt k := by
  have hh := width_pos S
  refine fun s hs => ⟨S.level k, hs, le_rfl, ?_⟩
  simp only [SlabDecomposition.level]
  push_cast
  linarith
theorem mirrorLocus_subset_slabAt_sub_one (k : ℤ) : S.mirrorLocus k ⊆ S.slabAt (k - 1) := by
  have hh := width_pos S
  refine fun s hs => ⟨S.level k, hs, ?_, ?_⟩
  · simp only [SlabDecomposition.level]
    push_cast
    linarith
  · simp only [SlabDecomposition.level]
    push_cast
    linarith
section Action
variable (D : SplitTorusDescent)
include D
theorem shiftMap_image_subset (j k : ℤ) :
    (shiftMap S j).pointMap '' S.slabAt k ⊆ S.slabAt (k + 2 * j) := by
  rintro _ ⟨_, ⟨_, ⟨x, rfl, m, rfl⟩, h₁, h₂⟩, rfl⟩
  have e : (shiftMap S j).pointMap (S.period.quotientMap x) =
      S.period.quotientMap ((shift (S.stepVec j)).pointMap x) :=
    (shift_descends S D j).descendPoint_quotientMap x
  have e' : S.normal ⬝ᵥ (((shift (S.stepVec j)).pointMap x : LatticePoint 1) : AmbientSpace) =
      S.normal ⬝ᵥ (x : AmbientSpace) + 2 * (j : ℝ) * (S.width : ℝ) :=
    dotProduct_add_stepVec S j x
  rw [e]
  simp only [SlabDecomposition.level] at h₁ h₂
  push_cast at h₁ h₂
  apply quotientMap_mem_slabAt S _ _ m
  · rw [e']
    simp only [SlabDecomposition.level]
    push_cast
    linarith
  · rw [e']
    simp only [SlabDecomposition.level]
    push_cast
    linarith
theorem shiftMap_image (j k : ℤ) : (shiftMap S j).pointMap '' S.slabAt k = S.slabAt (k + 2 * j) := by
  refine image_eq_of_compose_eq_identity S (g' := shiftMap S (-j)) ?_
    (shiftMap_image_subset S D j k) ?_
  · rw [shiftMap_compose_shiftMap S D, add_neg_cancel, shiftMap_zero S D]
  · have h := shiftMap_image_subset S D (-j) (k + 2 * j)
    rwa [show k + 2 * j + 2 * -j = k by ring] at h
theorem torusReflection_image_subset (s i : ℤ) :
    (S.torusReflection s).pointMap '' S.slabAt (s + i) ⊆ S.slabAt (s - 1 - i) := by
  rintro _ ⟨_, ⟨_, ⟨x, rfl, m, rfl⟩, h₁, h₂⟩, rfl⟩
  have e : (S.torusReflection s).pointMap (S.period.quotientMap x) =
      S.period.quotientMap ((S.reflectSym s).pointMap x) :=
    (reflectSym_descends S D s).descendPoint_quotientMap x
  have e' : S.normal ⬝ᵥ (((S.reflectSym s).pointMap x : LatticePoint 1) : AmbientSpace) =
      2 * S.level s - S.normal ⬝ᵥ (x : AmbientSpace) :=
    dotProduct_reflectAcross S.normal_mem _ _
  rw [e]
  simp only [SlabDecomposition.level] at h₁ h₂
  push_cast at h₁ h₂
  apply quotientMap_mem_slabAt S _ _ (-m)
  · rw [e']
    simp only [SlabDecomposition.level]
    push_cast
    linarith
  · rw [e']
    simp only [SlabDecomposition.level]
    push_cast
    linarith
theorem torusReflection_image (s i : ℤ) :
    (S.torusReflection s).pointMap '' S.slabAt (s + i) = S.slabAt (s - 1 - i) := by
  refine image_eq_of_compose_eq_identity S (g' := S.torusReflection s) ?_
    (torusReflection_image_subset S D s i) ?_
  · rw [torusReflection_compose_torusReflection S D, sub_self, shiftMap_zero S D]
  · have h := torusReflection_image_subset S D s (-1 - i)
    rwa [show s + (-1 - i) = s - 1 - i by ring, show s - 1 - (-1 - i) = s + i by ring] at h
theorem torusReflection_image_slabAt (s a : ℤ) :
    (S.torusReflection s).pointMap '' S.slabAt a = S.slabAt (2 * s - 1 - a) := by
  have h := torusReflection_image S D s (a - s)
  rwa [show s + (a - s) = a by ring, show s - 1 - (a - s) = 2 * s - 1 - a by ring] at h
theorem dvd_of_slabAt_eq {a b : ℤ} (h : S.slabAt a = S.slabAt b) : 2 * (S.count : ℤ) ∣ b - a := by
  have hh := width_pos S
  have h2 : (2 : ℝ) ≤ (S.width : ℝ) := by exact_mod_cast S.two_le_width
  obtain ⟨u, hu₁, hu₂⟩ : ∃ u : ℤ, S.level a < (u : ℝ) ∧ (u : ℝ) ≤ S.level a + 1 :=
    ⟨⌊S.level a⌋ + 1, by push_cast; exact Int.lt_floor_add_one _,
      by push_cast; linarith [Int.floor_le (S.level a)]⟩
  obtain ⟨x, hx⟩ := exists_latticePoint_height S u
  have hmem : S.period.quotientMap x ∈ S.slabAt a := by
    apply quotientMap_mem_slabAt S a x 0
    · rw [hx]
      simpa using hu₁.le
    · rw [hx]
      simp only [SlabDecomposition.level] at hu₂ ⊢
      push_cast
      linarith
  rw [h] at hmem
  obtain ⟨_, ⟨y, hy, m, rfl⟩, h₁, h₂⟩ := hmem
  obtain ⟨k, hk⟩ := exists_height_sub_eq S D hy
  rw [hx] at hk
  have hy' : S.normal ⬝ᵥ (y : AmbientSpace) = (u : ℝ) + 2 * (S.halfPeriod : ℝ) * (k : ℝ) := by
    linarith
  rw [hy'] at h₁ h₂
  simp only [SlabDecomposition.level, SlabDecomposition.halfPeriod] at h₁ h₂ hu₁ hu₂
  push_cast at h₁ h₂
  have i₁ : ((b : ℤ) : ℝ) * (S.width : ℝ) <
      ((a + 1 + 2 * (S.count : ℤ) * (k + m) : ℤ) : ℝ) * (S.width : ℝ) := by
    push_cast
    linarith
  have i₂ : ((a + 2 * (S.count : ℤ) * (k + m) : ℤ) : ℝ) * (S.width : ℝ) <
      ((b + 1 : ℤ) : ℝ) * (S.width : ℝ) := by
    push_cast
    linarith
  have j₁ : b < a + 1 + 2 * (S.count : ℤ) * (k + m) := by
    exact_mod_cast lt_of_mul_lt_mul_right i₁ hh.le
  have j₂ : a + 2 * (S.count : ℤ) * (k + m) < b + 1 := by
    exact_mod_cast lt_of_mul_lt_mul_right i₂ hh.le
  exact ⟨k + m, by linarith [show b = a + 2 * (S.count : ℤ) * (k + m) by omega]⟩
theorem slabOfClass_injective : Function.Injective S.slabOfClass := by
  intro j k h
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective j
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective k
  rw [S.slabOfClass_intCast, S.slabOfClass_intCast] at h
  refine (ZMod.intCast_eq_intCast_iff_dvd_sub a b (2 * S.count)).2 ?_
  push_cast
  exact dvd_of_slabAt_eq S D h
end Action
theorem shiftMap_mem (j : ℤ) : shiftMap S j ∈ S.generatedMaps := Or.inl ⟨j, rfl⟩
theorem torusReflection_mem (s : ℤ) : S.torusReflection s ∈ S.generatedMaps := Or.inr ⟨s, rfl⟩
section Group
variable (D : SplitTorusDescent)
include D
theorem compose_mem {g g' : S.period.TorusMap} (hg : g ∈ S.generatedMaps)
    (hg' : g' ∈ S.generatedMaps) : g.compose g' ∈ S.generatedMaps := by
  rcases hg with ⟨j, rfl⟩ | ⟨s, rfl⟩ <;> rcases hg' with ⟨j', rfl⟩ | ⟨s', rfl⟩
  · exact Set.mem_of_eq_of_mem (shiftMap_compose_shiftMap S D j j') (shiftMap_mem S _)
  · exact Set.mem_of_eq_of_mem (shiftMap_compose_torusReflection S D j s') (torusReflection_mem S _)
  · exact Set.mem_of_eq_of_mem (torusReflection_compose_shiftMap S D s j') (torusReflection_mem S _)
  · exact Set.mem_of_eq_of_mem (torusReflection_compose_torusReflection S D s s') (shiftMap_mem S _)
theorem exists_inverse {g : S.period.TorusMap} (hg : g ∈ S.generatedMaps) :
    ∃ g' ∈ S.generatedMaps, g.compose g' = PeriodSublattice.TorusMap.identity S.period ∧
      g'.compose g = PeriodSublattice.TorusMap.identity S.period := by
  rcases hg with ⟨j, rfl⟩ | ⟨s, rfl⟩
  · refine ⟨shiftMap S (-j), shiftMap_mem S _, ?_, ?_⟩
    · exact (shiftMap_compose_shiftMap S D j (-j)).trans (by
        rw [add_neg_cancel, shiftMap_zero S D])
    · exact (shiftMap_compose_shiftMap S D (-j) j).trans (by
        rw [neg_add_cancel, shiftMap_zero S D])
  · refine ⟨S.torusReflection s, torusReflection_mem S _, ?_, ?_⟩ <;>
    exact (torusReflection_compose_torusReflection S D s s).trans
      (by rw [sub_self, shiftMap_zero S D])
theorem exists_image_slabAt {g : S.period.TorusMap} (hg : g ∈ S.generatedMaps) (a : ℤ) :
    ∃ b : ℤ, g.pointMap '' S.slabAt a = S.slabAt b := by
  rcases hg with ⟨j, rfl⟩ | ⟨s, rfl⟩
  · exact ⟨_, shiftMap_image S D j a⟩
  · exact ⟨_, torusReflection_image_slabAt S D s a⟩
theorem exists_mem_image_slabAt (a b : ℤ) :
    ∃ g ∈ S.generatedMaps, g.pointMap '' S.slabAt a = S.slabAt b := by
  rcases Int.even_or_odd' (b - a) with ⟨i, hi | hi⟩
  · refine ⟨shiftMap S i, shiftMap_mem S _, ?_⟩
    rw [shiftMap_image S D, show a + 2 * i = b by omega]
  · refine ⟨S.torusReflection (a + i + 1), torusReflection_mem S _, ?_⟩
    rw [torusReflection_image_slabAt S D, show 2 * (a + i + 1) - 1 - a = b by omega]
theorem eq_of_image_slabAt {a b : ℤ} {g g' : S.period.TorusMap} (hg : g ∈ S.generatedMaps)
    (hg' : g' ∈ S.generatedMaps) (h : g.pointMap '' S.slabAt a = S.slabAt b)
    (h' : g'.pointMap '' S.slabAt a = S.slabAt b) : g = g' := by
  rcases hg with ⟨i, rfl⟩ | ⟨s, rfl⟩ <;> rcases hg' with ⟨i', rfl⟩ | ⟨s', rfl⟩
  · have e₁ := shiftMap_image S D i a
    have e₂ := shiftMap_image S D i' a
    obtain ⟨c, hc⟩ := dvd_of_slabAt_eq S D (e₁.symm.trans (h.trans (h'.symm.trans e₂)))
    exact shiftMap_eq_of_dvd S D ⟨-c, by linarith⟩
  · exfalso
    have e₁ := shiftMap_image S D i a
    have e₂ := torusReflection_image_slabAt S D s' a
    obtain ⟨c, hc⟩ := dvd_of_slabAt_eq S D (e₁.symm.trans (h.trans (h'.symm.trans e₂)))
    have hc' : 2 * s' - 1 - a - (a + 2 * i) = 2 * ((S.count : ℤ) * c) := by rw [hc]; ring
    omega
  · exfalso
    have e₁ := torusReflection_image_slabAt S D s a
    have e₂ := shiftMap_image S D i' a
    obtain ⟨c, hc⟩ := dvd_of_slabAt_eq S D (e₁.symm.trans (h.trans (h'.symm.trans e₂)))
    have hc' : a + 2 * i' - (2 * s - 1 - a) = 2 * ((S.count : ℤ) * c) := by rw [hc]; ring
    omega
  · have e₁ := torusReflection_image_slabAt S D s a
    have e₂ := torusReflection_image_slabAt S D s' a
    obtain ⟨c, hc⟩ := dvd_of_slabAt_eq S D (e₁.symm.trans (h.trans (h'.symm.trans e₂)))
    exact torusReflection_eq_of_dvd S D ⟨-c, by linarith⟩
theorem exists_mapsSlabTo (j k : ZMod (2 * S.count)) : ∃ g, S.MapsSlabTo j k g := by
  obtain ⟨g, hg, h⟩ := exists_mem_image_slabAt S D (j.val : ℤ) (k.val : ℤ)
  exact ⟨g, hg, h⟩
theorem existsUnique_mapsSlabTo (j k : ZMod (2 * S.count)) : ∃! g, S.MapsSlabTo j k g := by
  obtain ⟨g, hg⟩ := exists_mapsSlabTo S D j k
  exact ⟨g, hg, fun g' hg' => eq_of_image_slabAt S D hg'.1 hg.1 hg'.2 hg.2⟩
theorem mapsSlabTo_slabTransporter (j k : ZMod (2 * S.count)) :
    S.MapsSlabTo j k (S.slabTransporter j k) :=
  Classical.epsilon_spec (exists_mapsSlabTo S D j k)
theorem kind_of_mapsSlabTo (j k : ZMod (2 * S.count)) (g : S.period.TorusMap)
    (h : S.MapsSlabTo j k g) :
    (S.ValModEqTwo k j → S.IsGroupTranslation g) ∧
      (¬ S.ValModEqTwo k j → S.IsGroupReflection g) := by
  obtain ⟨hg, hi⟩ := h
  change g.pointMap '' S.slabAt (j.val : ℤ) = S.slabAt (k.val : ℤ) at hi
  rcases hg with ⟨i, rfl⟩ | ⟨s, rfl⟩
  · have e := shiftMap_image S D i (j.val : ℤ)
    obtain ⟨c, hc⟩ := dvd_of_slabAt_eq S D (e.symm.trans hi)
    have hc' : (k.val : ℤ) - ((j.val : ℤ) + 2 * i) = 2 * ((S.count : ℤ) * c) := by rw [hc]; ring
    refine ⟨fun _ => ⟨i, rfl⟩, fun hn => absurd ?_ hn⟩
    change ((k.val : ℤ)) % 2 = ((j.val : ℤ)) % 2
    omega
  · have e := torusReflection_image_slabAt S D s (j.val : ℤ)
    obtain ⟨c, hc⟩ := dvd_of_slabAt_eq S D (e.symm.trans hi)
    have hc' : (k.val : ℤ) - (2 * s - 1 - (j.val : ℤ)) = 2 * ((S.count : ℤ) * c) := by
      rw [hc]; ring
    refine ⟨fun hm => ?_, fun _ => ⟨s, rfl⟩⟩
    exfalso
    have hm' : ((k.val : ℤ)) % 2 = ((j.val : ℤ)) % 2 := hm
    omega
theorem not_isGroupTranslation_and_isGroupReflection (g : S.period.TorusMap) :
    ¬ (S.IsGroupTranslation g ∧ S.IsGroupReflection g) := by
  rintro ⟨⟨j, rfl⟩, ⟨s, hs⟩⟩
  have e₁ := shiftMap_image S D j 0
  have e₂ := torusReflection_image_slabAt S D s 0
  have e₃ : shiftMap S j = S.torusReflection s := hs
  rw [e₃] at e₁
  obtain ⟨c, hc⟩ := dvd_of_slabAt_eq S D (e₁.symm.trans e₂)
  have hc' : 2 * s - 1 - 0 - (0 + 2 * j) = 2 * ((S.count : ℤ) * c) := by rw [hc]; ring
  omega
theorem generatedMaps_eq_range :
    S.generatedMaps = Set.range fun k : ZMod (2 * S.count) => S.slabTransporter 0 k := by
  ext g
  constructor
  · intro hg
    obtain ⟨b, hb⟩ := exists_image_slabAt S D hg ((0 : ZMod (2 * S.count)).val : ℤ)
    refine ⟨(b : ZMod (2 * S.count)), ?_⟩
    have hc := mapsSlabTo_slabTransporter S D 0 (b : ZMod (2 * S.count))
    have hc₂ := hc.2
    rw [S.slabOfClass_intCast] at hc₂
    exact eq_of_image_slabAt S D hc.1 hg hc₂ hb
  · rintro ⟨k, rfl⟩
    exact (mapsSlabTo_slabTransporter S D 0 k).1
theorem slabTransporter_injective :
    Function.Injective fun k : ZMod (2 * S.count) => S.slabTransporter 0 k := by
  intro k k' h
  apply slabOfClass_injective S D
  have h₁ := (mapsSlabTo_slabTransporter S D 0 k).2
  have h₂ := (mapsSlabTo_slabTransporter S D 0 k').2
  have h' : S.slabTransporter 0 k = S.slabTransporter 0 k' := h
  rw [← h₁, ← h₂, h']
theorem generatedMaps_finite : S.generatedMaps.Finite := by
  rw [generatedMaps_eq_range S D]
  exact Set.finite_range _
theorem generatedMaps_ncard : S.generatedMaps.ncard = 2 * S.count := by
  rw [generatedMaps_eq_range S D, ← Set.image_univ,
    Set.ncard_image_of_injective _ (slabTransporter_injective S D), Set.ncard_univ,
    Nat.card_eq_fintype_card, ZMod.card]
end Group
theorem two_width_smul_mem : (2 * (S.width : ℝ)) • dualVector S.normal ∈ latticeSubgroup 1 := by
  have h := (S.stepVec 1).2
  rw [stepVec_coe] at h
  simpa using h
theorem dotProduct_two_width_smul :
    S.normal ⬝ᵥ ((2 * (S.width : ℝ)) • dualVector S.normal) = 2 * (S.width : ℝ) := by
  rw [dotProduct_smul, smul_eq_mul, dotProduct_dualVector S.normal_mem, mul_one]
theorem smul_dualVector_of_coordVec (μ : Fin 4) (hμ : S.normal = coordVec μ) :
    (2 * (S.width : ℝ)) • dualVector S.normal = (2 * (S.width : ℝ)) • coordVec μ := by
  have q : normSq (coordVec μ) = 1 := by
    rw [normSq_eq_dotProduct]
    simp [coordVec]
  rw [hμ, dualVector, q, inv_one, one_smul]
theorem smul_dualVector_of_normSq_two (hq : normSq S.normal = 2) :
    (2 * (S.width : ℝ)) • dualVector S.normal = (S.width : ℝ) • S.normal := by
  rw [dualVector, hq, smul_smul]
  congr 1
  ring
theorem reflectAcross_add_width (c : ℝ) (x : AmbientSpace) :
    reflectAcross S.normal (c + (S.width : ℝ)) (reflectAcross S.normal c x) =
      x + (2 * (S.width : ℝ)) • dualVector S.normal := by
  rw [reflectAcross, dotProduct_reflectAcross S.normal_mem]
  simp only [reflectAcross]
  module
theorem two_halfPeriod_smul :
    (2 * (S.halfPeriod : ℝ)) • dualVector S.normal =
      (S.count : ℝ) • ((2 * (S.width : ℝ)) • dualVector S.normal) := by
  rw [smul_smul]
  congr 1
  simp only [SlabDecomposition.halfPeriod]
  push_cast
  ring
section Classes
variable (D : SplitTorusDescent)
include D
theorem torusReflectionOfClass_image (s i : ZMod (2 * S.count)) :
    (S.torusReflectionOfClass s).pointMap '' S.slabOfClass (s + i) = S.slabOfClass (s - 1 - i) := by
  obtain ⟨i', rfl⟩ := ZMod.intCast_surjective i
  have hs : (((s.val : ℕ) : ℤ) : ZMod (2 * S.count)) = s := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have e₁ : s + (i' : ZMod (2 * S.count)) = (((s.val : ℤ) + i' : ℤ) : ZMod (2 * S.count)) := by
    rw [Int.cast_add, hs]
  have e₂ : s - 1 - (i' : ZMod (2 * S.count)) =
      (((s.val : ℤ) - 1 - i' : ℤ) : ZMod (2 * S.count)) := by
    rw [Int.cast_sub, Int.cast_sub, hs, Int.cast_one]
  rw [e₁, e₂, S.slabOfClass_intCast, S.slabOfClass_intCast]
  exact torusReflection_image S D _ _
theorem shiftMap_slabOfClass_image (j : ℤ) (k : ZMod (2 * S.count)) :
    (shiftMap S j).pointMap '' S.slabOfClass k =
      S.slabOfClass (k + 2 * (j : ZMod (2 * S.count))) := by
  obtain ⟨k', rfl⟩ := ZMod.intCast_surjective k
  have e : (k' : ZMod (2 * S.count)) + 2 * (j : ZMod (2 * S.count)) =
      ((k' + 2 * j : ℤ) : ZMod (2 * S.count)) := by
    push_cast
    ring
  rw [e, S.slabOfClass_intCast, S.slabOfClass_intCast]
  exact shiftMap_image S D _ _
end Classes
theorem slabActionSimplyTransitive_of_splitTorusDescent (D : SplitTorusDescent) :
    SlabActionSimplyTransitive := by
  intro S
  refine ⟨two_width_smul_mem S, dotProduct_two_width_smul S, smul_dualVector_of_coordVec S,
    smul_dualVector_of_normSq_two S, fun c _ x => reflectAcross_add_width S c x,
    two_halfPeriod_smul S, rfl, S.splits.2.1, S.level_allowed,
    fun k => torusReflection_eq_of_dvd S D ⟨1, by ring⟩,
    fun k b hb => ⟨hb.trans (mirrorLocus_subset_slabAt_sub_one S k),
      hb.trans (mirrorLocus_subset_slabAt S k)⟩,
    slabOfClass_injective S D, torusReflectionOfClass_image S D, shiftMap_slabOfClass_image S D, ?_,
    Set.mem_of_eq_of_mem (shiftMap_zero S D).symm (shiftMap_mem S 0),
    fun g hg g' hg' => compose_mem S D hg hg', fun g hg => exists_inverse S D hg,
    generatedMaps_finite S D, generatedMaps_ncard S D, torusReflection_mem S,
    existsUnique_mapsSlabTo S D, mapsSlabTo_slabTransporter S D, kind_of_mapsSlabTo S D,
    not_isGroupTranslation_and_isGroupReflection S D⟩
  have h := shiftMap_count_mul S D 1
  rwa [mul_one] at h
end SlabTransitivity
end InfiniteLattice
end YangMills.Construction

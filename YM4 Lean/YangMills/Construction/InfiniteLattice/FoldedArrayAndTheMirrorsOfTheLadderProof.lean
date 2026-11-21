import YangMills.Construction.InfiniteLattice.AllMirrorsAtSpacingOneProof
import YangMills.Construction.InfiniteLattice.FoldedArrayAndTheMirrorsOfTheLadder
import YangMills.Construction.InfiniteLattice.LinearPartAndIdentitiesOfTheReflections
import YangMills.Construction.InfiniteLattice.PropertiesOfThePeriodGroups
import YangMills.Construction.InfiniteLattice.RulesOfTheActionOfTheLatticeIsometries
import YangMills.Construction.ReflectionPositivity.SimpleTransitivityOnTheSlabsProof
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open InfiniteLattice
namespace FoldedArrayMirrors
theorem latticeSymmetry_ext {r s : LatticeSymmetry 1} (h : r.toFun = s.toFun) : r = s := by apply _root_.YangMills.Construction.InfiniteLattice.UnitMeshReflectionPositivity.latticeSymmetry_ext_toFun <;> assumption
theorem orientedRepresentative_endpoints {b : Link 1} {T : Set AmbientSpace}
    (h : (b.initial : AmbientSpace) ∈ T ∧ (b.terminal : AmbientSpace) ∈ T) :
    (b.orientedRepresentative.initial : AmbientSpace) ∈ T ∧
      (b.orientedRepresentative.terminal : AmbientSpace) ∈ T := by
  unfold Link.orientedRepresentative
  split_ifs
  · exact h
  · exact ⟨h.2, h.1⟩
theorem actOn_mem (hR : SymmetryActionRules.Statement)
    (r : LatticeSymmetry 1) {F : GaugeField 1 → ℂ} (hF : F ∈ continuousLocalFunctions 1) :
    r.actOn F ∈ continuousLocalFunctions 1 :=
  (hR r r).2.2.2.2.2.1.subset ⟨F, hF, rfl⟩
theorem supportLiesIn_actOn (hR : SymmetryActionRules.Statement)
    (r : LatticeSymmetry 1) {F : GaugeField 1 → ℂ} (hF : F ∈ continuousLocalFunctions 1)
    {S T : Set AmbientSpace} (hS : SupportLiesIn F S) (hT : r.toFun '' S ⊆ T) :
    SupportLiesIn (r.actOn F) T := by
  have hsupp := (hR r r).2.2.2.2.2.2.1 F hF.1 hF.2.1
  intro b hb
  rw [hsupp] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  have h := hS b₀ hb₀
  exact orientedRepresentative_endpoints ⟨hT ⟨_, h.1, rfl⟩, hT ⟨_, h.2, rfl⟩⟩
theorem dotProduct_reflectAcross {n : AmbientSpace} (hn : n ∈ normalSet) (c : ℝ)
    (x : AmbientSpace) :
    n ⬝ᵥ reflectAcross n c x = 2 * c - n ⬝ᵥ x := by apply _root_.YangMills.Construction.InfiniteLattice.SlabTransitivity.dotProduct_reflectAcross <;> assumption
variable {L : MirrorLadder}
theorem reflectAcross_image_slab_zero :
    reflectAcross L.normal (L.offset + (L.spacing : ℝ)) '' L.slab 0 ⊆ L.slab 1 := by
  rintro _ ⟨x, ⟨h₀, h₁⟩, rfl⟩
  have h := dotProduct_reflectAcross L.normal_mem (L.offset + (L.spacing : ℝ)) x
  push_cast at h₀ h₁
  refine ⟨?_, ?_⟩
  · rw [h]
    push_cast
    linarith
  · rw [h]
    push_cast
    linarith
theorem upper_reflectObservable_shift (hI : ReflectionLinearPart.Statement)
    (L : MirrorLadder) (v w : LatticePoint 1)
    (hw : (w : AmbientSpace) = linearReflect L.normal (v : AmbientSpace))
    {F : GaugeField 1 → ℂ} (hF : IsBoundedObservable F) :
    L.upperWallOfSlabZero.reflectObservable ((shift v).actOn F) =
      (shift w).actOn (L.upperWallOfSlabZero.reflectObservable F) := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨w', hw', h⟩, -⟩ :=
    hI L.normal L.normal_mem (L.offset + (L.spacing : ℝ)) (L.offset + (L.spacing : ℝ))
      L.upperWallOfSlabZero.allowed L.upperWallOfSlabZero.allowed v
  obtain rfl : w' = w := Subtype.ext (hw'.trans hw.symm)
  exact h F hF
theorem upper_reflectObservable_reflectObservable (hI : ReflectionLinearPart.Statement)
    (L : MirrorLadder) {F : GaugeField 1 → ℂ} (hF : IsBoundedObservable F) :
    L.upperWallOfSlabZero.reflectObservable (L.upperWallOfSlabZero.reflectObservable F) = F := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    hI L.normal L.normal_mem (L.offset + (L.spacing : ℝ)) (L.offset + (L.spacing : ℝ))
      L.upperWallOfSlabZero.allowed L.upperWallOfSlabZero.allowed 0
  exact h F hF
theorem exists_point_rungAt (hI : ReflectionLinearPart.Statement)
    (hR : SymmetryActionRules.Statement) (L : MirrorLadder) (k : ℤ) :
    ∃ d : LatticePoint 1,
      (d : AmbientSpace) = (2 * ((k : ℝ) - 1) * (L.spacing : ℝ)) • dualVector L.normal ∧
      (∀ F ∈ continuousLocalFunctions 1, (L.rungAt k).reflectObservable F =
        (shift d).actOn (L.upperWallOfSlabZero.reflectObservable F)) ∧
      reflectAcross L.normal (L.offset + (k : ℝ) * (L.spacing : ℝ)) =
        (shift d).toFun ∘ reflectAcross L.normal (L.offset + (L.spacing : ℝ)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hinv, -, hcomp, -, hobs, ⟨d, hd, hmir⟩, -⟩ :=
    hI L.normal L.normal_mem (L.offset + (L.spacing : ℝ)) (L.offset + (k : ℝ) * (L.spacing : ℝ))
      L.upperWallOfSlabZero.allowed (L.rungAt k).allowed 0
  refine ⟨d, ?_, fun F hF => ?_, ?_⟩
  · rw [hd]
    congr 1
    ring
  · have h₁ := hmir (L.upperWallOfSlabZero.reflectObservable F) (actOn_mem hR _ hF).1
    have h₂ : L.upperWallOfSlabZero.reflectObservable
        (L.upperWallOfSlabZero.reflectObservable F) = F :=
      hobs F hF.1
    have h₃ : (L.rungAt k).reflectObservable
        (L.upperWallOfSlabZero.reflectObservable (L.upperWallOfSlabZero.reflectObservable F)) =
        (shift d).actOn (L.upperWallOfSlabZero.reflectObservable F) := h₁
    rwa [h₂] at h₃
  · funext x
    have h₁ := congrFun hcomp (reflectAcross L.normal (L.offset + (L.spacing : ℝ)) x)
    have h₂ := congrFun hinv x
    simp only [Function.comp_apply, id] at h₁ h₂
    rw [h₂] at h₁
    rw [h₁, Function.comp_apply, shift_toFun_eq_translateBy, hd]
theorem exists_equiv_normalSublattice (hI : ReflectionLinearPart.Statement)
    (hP : PeriodLatticeProperties) (L : MirrorLadder) :
    ∃ e : L.normalSublattice ≃ L.normalSublattice, ∀ v,
      ((e v : LatticePoint 1) : AmbientSpace) =
        linearReflect L.normal ((v : LatticePoint 1) : AmbientSpace) := by
  have himg :=
    (hP.1 L.normal L.normal_mem L.spacing L.even_spacing L.two_le_spacing).2.1.2.2.2.2.2.2.2.2.2.2.2
  have hmem : ∀ v : L.normalSublattice, ∃ u : L.normalSublattice,
      ((u : LatticePoint 1) : AmbientSpace) =
        linearReflect L.normal ((v : LatticePoint 1) : AmbientSpace) := by
    intro v
    obtain ⟨-, -, -, -, -, -, -, -, ⟨w, hw, -⟩, -⟩ :=
      hI L.normal L.normal_mem L.offset L.offset L.offset_allowed L.offset_allowed
        (v : LatticePoint 1)
    have hv : ((v : LatticePoint 1) : AmbientSpace) ∈ normalPeriodLattice L.normal L.spacing :=
      AddSubgroup.mem_addSubgroupOf.mp v.2
    have hw' : (w : AmbientSpace) ∈ normalPeriodLattice L.normal L.spacing := by
      have : (w : AmbientSpace) ∈ (normalPeriodLattice L.normal L.spacing : Set AmbientSpace) := by
        rw [← himg, hw]
        exact ⟨_, hv, rfl⟩
      exact this
    exact ⟨⟨w, AddSubgroup.mem_addSubgroupOf.mpr hw'⟩, hw⟩
  choose f hf using hmem
  obtain ⟨-, -, -, h0, -⟩ :=
    hI L.normal L.normal_mem L.offset L.offset L.offset_allowed L.offset_allowed 0
  obtain ⟨-, -, -, -, -, -, -, -, -, hinv, -⟩ :=
    hI L.normal L.normal_mem 0 0 h0 h0 0
  have hf2 : Function.Involutive f := by
    intro v
    apply Subtype.ext
    apply Subtype.ext
    rw [hf, hf]
    exact congrFun hinv _
  exact ⟨Function.Involutive.toPerm f hf2, hf⟩
theorem cast_val_rev (ι : Fin 2) : (((Fin.rev ι : Fin 2) : ℕ) : ℝ) = 1 - ((ι : ℕ) : ℝ) := by
  revert ι
  rw [Fin.forall_fin_two]
  constructor <;> norm_num [Fin.rev]
theorem foldedArrayMirrorProperties_holds (hI : ReflectionLinearPart.Statement)
    (hR : SymmetryActionRules.Statement)
    (hP : PeriodLatticeProperties) :
    FoldedArrayMirrorProperties := by
  intro L A
  have hA := A.mem_continuousLocal
  have hA₂ := A.reflected_mem
  have hne := MirrorLadder.spacing_ne_zero L
  have hslab₁ : SupportLiesIn A.reflected (L.slab 1) :=
    supportLiesIn_actOn hR L.upperWallOfSlabZero.reflectSymmetry hA A.supportLiesIn
      reflectAcross_image_slab_zero
  have hper := hP.2 L
  have hle := (hP.1 L.normal L.normal_mem L.spacing L.even_spacing L.two_le_spacing).2.2.2.2.2.1
  have hmove : ∀ (v : LatticePoint 1) (j m : ℤ) {F : GaugeField 1 → ℂ},
      F ∈ continuousLocalFunctions 1 → (v : AmbientSpace) ∈ axialPeriodLattice L.normal L.spacing →
      (m : ℝ) = L.normal ⬝ᵥ (v : AmbientSpace) / (L.spacing : ℝ) → SupportLiesIn F (L.slab j) →
      SupportLiesIn ((shift v).actOn F) (L.slab (j + m)) :=
    fun v j m _ hF hv hm hS =>
      supportLiesIn_actOn hR _ hF hS (hper.2.2.1 v j m hv hm).subset
  have hfolded : ∀ (a : ℤ) (v : L.normalSublattice),
      (∃ y ∈ parallelPeriodLattice L.normal,
        ((v : LatticePoint 1) : AmbientSpace) =
          y + (2 * (a : ℝ) * (L.spacing : ℝ)) • dualVector L.normal) →
      SupportLiesIn ((shift (v : LatticePoint 1)).actOn A.toFun) (L.slab (2 * a)) ∧
      SupportLiesIn ((shift (v : LatticePoint 1)).actOn A.reflected)
        (L.slab (2 * a + 1)) := by
    rintro a v ⟨y, hy, hv⟩
    have hvl : ((v : LatticePoint 1) : AmbientSpace) ∈ axialPeriodLattice L.normal L.spacing :=
      hle (AddSubgroup.mem_addSubgroupOf.mp v.2)
    have hm : ((2 * a : ℤ) : ℝ) =
        L.normal ⬝ᵥ ((v : LatticePoint 1) : AmbientSpace) / (L.spacing : ℝ) := by
      rw [hv, hper.2.2.2.2.2.2 a y hy]
      push_cast
      field_simp
    have h₀ := hmove _ 0 (2 * a) hA hvl hm A.supportLiesIn
    have h₁ := hmove _ 1 (2 * a) hA₂ hvl hm hslab₁
    rw [zero_add] at h₀
    rw [show (1 : ℤ) + 2 * a = 2 * a + 1 by ring] at h₁
    exact ⟨h₀, h₁⟩
  have hid : ∀ v w : L.normalSublattice,
      ((w : LatticePoint 1) : AmbientSpace) =
        linearReflect L.normal ((v : LatticePoint 1) : AmbientSpace) →
      L.upperWallOfSlabZero.reflectObservable ((shift (v : LatticePoint 1)).actOn A.toFun) =
          (shift (w : LatticePoint 1)).actOn A.reflected ∧
      L.upperWallOfSlabZero.reflectObservable ((shift (v : LatticePoint 1)).actOn A.reflected) =
          (shift (w : LatticePoint 1)).actOn A.toFun := by
    intro v w hw
    refine ⟨upper_reflectObservable_shift hI L _ _ hw hA.1, ?_⟩
    rw [upper_reflectObservable_shift hI L _ _ hw hA₂.1]
    exact congrArg _ (upper_reflectObservable_reflectObservable hI L hA.1)
  have hgen : ∀ (v w : L.normalSublattice),
      ((w : LatticePoint 1) : AmbientSpace) =
        linearReflect L.normal ((v : LatticePoint 1) : AmbientSpace) →
      ∀ ι : Fin 2,
        L.upperWallOfSlabZero.reflectObservable ((shift (v : LatticePoint 1)).actOn
            ((![A.toFun, A.reflected] : Fin 2 → GaugeField 1 → ℂ) ι)) =
          (shift (w : LatticePoint 1)).actOn
            ((![A.toFun, A.reflected] : Fin 2 → GaugeField 1 → ℂ) (Fin.rev ι)) := by
    intro v w hw
    rw [Fin.forall_fin_two]
    exact hid v w hw
  obtain ⟨e, he⟩ := exists_equiv_normalSublattice hI hP L
  refine ⟨⟨A.reflected_mem, A.reflected_im, hslab₁⟩, ?_, hfolded, ?_, hid, ⟨e, he⟩,
    ⟨Equiv.prodCongr e Fin.revPerm, fun i => ⟨he i.1, rfl, hgen i.1 _ (he i.1) i.2⟩⟩, ?_⟩
  · intro k i hi
    have hm := (MirrorLadder.unfoldedLabelInSlab_iff A i k).mp hi
    have h := hmove (i.1 : LatticePoint 1) 0 k hA (AddSubgroup.mem_addSubgroupOf.mp i.1.2) hm
      A.supportLiesIn
    rw [zero_add] at h
    exact h
  · rintro k ⟨v, ι⟩ ⟨a, y, hy, hv, rfl⟩
    have h := hfolded a v ⟨y, hy, hv⟩
    have hι : ∀ ι : Fin 2, SupportLiesIn ((shift (v : LatticePoint 1)).actOn
        ((![A.toFun, A.reflected] : Fin 2 → GaugeField 1 → ℂ) ι))
        (L.slab (2 * a + ((ι : ℕ) : ℤ))) := by
      rw [Fin.forall_fin_two]
      exact ⟨by simpa using h.1, by simpa using h.2⟩
    exact hι ι
  · intro k
    obtain ⟨d, hd, hmir, hmap⟩ := exists_point_rungAt hI hR L k
    have hdmem : d ∈ L.normalSublattice := by
      refine AddSubgroup.mem_addSubgroupOf.mpr (mem_normalPeriodLattice_iff.mpr
        ⟨0, zero_mem _, k - 1, ?_⟩)
      rw [hd, zero_add, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
      congr 1
      push_cast
      ring
    have hterm : ∀ (v u : L.normalSublattice) (ι : Fin 2),
        ((u : LatticePoint 1) : AmbientSpace) =
          linearReflect L.normal ((v : LatticePoint 1) : AmbientSpace) +
            (2 * ((k : ℝ) - 1) * (L.spacing : ℝ)) • dualVector L.normal →
        (L.rungAt k).reflectObservable ((shift (v : LatticePoint 1)).actOn
            ((![A.toFun, A.reflected] : Fin 2 → GaugeField 1 → ℂ) ι)) =
          (shift (u : LatticePoint 1)).actOn
            ((![A.toFun, A.reflected] : Fin 2 → GaugeField 1 → ℂ) (Fin.rev ι)) := by
      intro v u ι hu
      have hmemι : ∀ ι : Fin 2, (![A.toFun, A.reflected] : Fin 2 → GaugeField 1 → ℂ) ι ∈
          continuousLocalFunctions 1 := A.foldedArray.gen_mem
      rw [hmir _ (actOn_mem hR _ (hmemι ι)), hgen v (e v) (he v) ι,
        (hR (shift d) (shift ((e v : L.normalSublattice) : LatticePoint 1))).1 _ (hmemι _).1]
      have hcomp : (shift d).comp (shift ((e v : L.normalSublattice) : LatticePoint 1)) =
          shift (u : LatticePoint 1) := by
        refine latticeSymmetry_ext (funext fun x => ?_)
        change x + (((e v : L.normalSublattice) : LatticePoint 1) : AmbientSpace) +
            (d : AmbientSpace) = x + ((u : LatticePoint 1) : AmbientSpace)
        rw [hu, he, hd, add_assoc]
      rw [hcomp]
    let D : L.normalSublattice := ⟨d, hdmem⟩
    have hval : ∀ v : L.normalSublattice,
        (((e.trans (Equiv.addRight D)) v : LatticePoint 1) : AmbientSpace) =
          linearReflect L.normal ((v : LatticePoint 1) : AmbientSpace) +
            (2 * ((k : ℝ) - 1) * (L.spacing : ℝ)) • dualVector L.normal := by
      intro v
      change (((e v : L.normalSublattice) : LatticePoint 1) : AmbientSpace) +
        (d : AmbientSpace) = _
      rw [he, hd]
    refine ⟨⟨⟨d, hdmem⟩, hd, hmap⟩, fun v u ι hu => hterm v u ι hu,
      Equiv.prodCongr (e.trans (Equiv.addRight D)) Fin.revPerm,
      fun i => ⟨hval i.1, rfl, hterm i.1 _ i.2 (hval i.1)⟩, fun i j => ?_⟩
    rw [MirrorLadder.foldedLabelInSlab_iff, MirrorLadder.foldedLabelInSlab_iff]
    have hheight : L.normal ⬝ᵥ
        ((((Equiv.prodCongr (e.trans (Equiv.addRight D)) Fin.revPerm :
            A.foldedArray.Label ≃ A.foldedArray.Label) i).1 : LatticePoint 1) : AmbientSpace) =
        -(L.normal ⬝ᵥ ((i.1 : LatticePoint 1) : AmbientSpace)) +
          2 * ((k : ℝ) - 1) * (L.spacing : ℝ) := by
      have h₁ : ((((Equiv.prodCongr (e.trans (Equiv.addRight D)) Fin.revPerm :
            A.foldedArray.Label ≃ A.foldedArray.Label) i).1 : LatticePoint 1) : AmbientSpace) =
          linearReflect L.normal ((i.1 : LatticePoint 1) : AmbientSpace) +
            (2 * ((k : ℝ) - 1) * (L.spacing : ℝ)) • dualVector L.normal := hval i.1
      rw [h₁, dotProduct_add, dotProduct_smul, dotProduct_dualVector L.normal_mem,
        linearReflect, dotProduct_reflectAcross L.normal_mem, smul_eq_mul]
      ring
    have hrev : (((((Equiv.prodCongr (e.trans (Equiv.addRight D)) Fin.revPerm :
            A.foldedArray.Label ≃ A.foldedArray.Label) i).2 : Fin 2) : ℕ) : ℝ) =
        1 - (((i.2 : Fin 2) : ℕ) : ℝ) := cast_val_rev i.2
    have hdiv : (-(L.normal ⬝ᵥ ((i.1 : LatticePoint 1) : AmbientSpace)) +
          2 * ((k : ℝ) - 1) * (L.spacing : ℝ)) / (L.spacing : ℝ) =
        -(L.normal ⬝ᵥ ((i.1 : LatticePoint 1) : AmbientSpace) / (L.spacing : ℝ)) +
          2 * ((k : ℝ) - 1) := by
      field_simp
    rw [hheight, hdiv]
    erw [hrev]
    push_cast
    constructor <;> intro h <;> linarith
end FoldedArrayMirrors
end YangMills.Construction.NormalFamilies

import YangMills.Construction.ReflectionPositivity.CopyRuleOnTheSlabs
import YangMills.Construction.ReflectionPositivity.PullBacksOnASplitTorus
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open NormalFamilies
namespace SlabCopy
theorem linkEndpoints_linkImage_subset {Γ : PeriodSublattice 1} {r : LatticeSymmetry 1}
    (hi : Γ.DescendsToQuotient r) (b : Γ.QuotientLink) :
    Γ.linkEndpoints (Γ.linkImage r b) ⊆ Γ.descendPoint r '' Γ.linkEndpoints b := by
  have hd : ({Γ.sourcePoint (Γ.descendOrientedLink r (Γ.orientedOfLink b)),
      Γ.targetPoint (Γ.descendOrientedLink r (Γ.orientedOfLink b))} : Set Γ.QuotientTorus) ⊆
      Γ.descendPoint r '' Γ.linkEndpoints b := by
    rw [Γ.linkEndpoints_eq b]
    rintro _ (rfl | rfl)
    · exact ⟨_, Or.inl rfl, (hi.sourcePoint_descend _).symm⟩
    · exact ⟨_, Or.inr rfl, (hi.targetPoint_descend _).symm⟩
  by_cases h : Γ.OrientedIsPositive (Γ.descendOrientedLink r (Γ.orientedOfLink b))
  · rw [PeriodSublattice.linkImage, dif_pos h, Γ.linkEndpoints_eq, Γ.orientedOfLink_linkClass,
      Γ.orientedClass_orientedRep]
    exact hd
  · rw [PeriodSublattice.linkImage, dif_neg h, Γ.linkEndpoints_eq, Γ.orientedOfLink_linkClass,
      Γ.sourcePoint_orientedClass, Γ.targetPoint_orientedClass]
    rintro _ (rfl | rfl)
    · exact hd (Or.inr rfl)
    · exact hd (Or.inl rfl)
variable (S : SlabDecomposition)
theorem mapsOrbits_and_descends (hD : SplitTorusDescent) {r : LatticeSymmetry 1}
    (hr : IsClassIsometry S.normal r.toFun) :
    S.period.MapsOrbits r ∧ S.period.DescendsToQuotient r := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    hD S.period S.normal S.normal_mem ((S.count : ℤ) * S.width) S.baseLevel S.baseLevel_allowed 0
      S.splits
  exact h r hr
theorem exists_comp_symmetry (hD : SplitTorusDescent) {r r' : LatticeSymmetry 1}
    (hr : IsClassIsometry S.normal r.toFun) (hr' : IsClassIsometry S.normal r'.toFun) :
    ∃ R : LatticeSymmetry 1, R.toFun = r.toFun ∘ r'.toFun ∧
      IsClassIsometry S.normal R.toFun ∧
      S.period.descendedTorusMap R =
        PeriodSublattice.TorusMap.compose (S.period.descendedTorusMap r)
          (S.period.descendedTorusMap r') := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hl, -, hc, -⟩ :=
    hD S.period S.normal S.normal_mem ((S.count : ℤ) * S.width) S.baseLevel S.baseLevel_allowed 0
      S.splits
  obtain ⟨R, hR⟩ := hl _ (hr.comp hr')
  have hf : IsClassIsometry S.normal R.toFun := hR ▸ hr.comp hr'
  obtain ⟨e₁, e₂, e₃⟩ := hc r r' R hr hr' hR
  exact ⟨R, hR, hf, PeriodSublattice.TorusMap.ext e₁ e₂ e₃⟩
theorem pullbackField_eq_self (hD : SplitTorusDescent) {r : LatticeSymmetry 1}
    (hr : IsClassIsometry S.normal r.toFun)
    (h : S.period.descendOrientedLink r = id) (U : S.period.QuotientField) :
    S.period.pullbackField r U = U := by
  obtain ⟨hc, hi⟩ := mapsOrbits_and_descends S hD hr
  funext b
  obtain ⟨b', rfl⟩ : ∃ b', S.period.linkClass b' = b :=
    ⟨_, S.period.linkClass_linkRep b⟩
  rw [S.period.pullbackField_linkClass hc, ← hi.descendOrientedLink_orientedClass, h, id,
    S.period.orientedValue_positive]
theorem exists_inducingSymmetry {g : S.period.TorusMap} (hg : g ∈ S.generatedMaps) :
    ∃ r, S.InducesTorusMap g r := by
  rcases hg with ⟨j, rfl⟩ | ⟨s, rfl⟩
  · exact ⟨shift (S.stepVec j), isClassIsometry_shift _ _, rfl⟩
  · exact ⟨S.reflectSym s, isClassIsometry_reflectAcross (S.level_allowed s), rfl⟩
theorem inducingSymmetry_spec {g : S.period.TorusMap} (hg : g ∈ S.generatedMaps) :
    S.InducesTorusMap g (S.inducingSymmetry g) :=
  Classical.epsilon_spec (exists_inducingSymmetry S hg)
theorem slabCopy_of_translation {j k : ZMod (2 * S.count)} (f : S.period.QuotientField → ℂ)
    (h : S.IsGroupTranslation (S.slabTransporter j k)) :
    S.slabCopy j k f =
      S.period.compPullback (S.inducingSymmetry (S.slabTransporter j k)) f := by
  rw [SlabDecomposition.slabCopy, if_pos h]
  rfl
theorem slabCopy_of_not_translation {j k : ZMod (2 * S.count)} (f : S.period.QuotientField → ℂ)
    (h : ¬ S.IsGroupTranslation (S.slabTransporter j k)) :
    S.slabCopy j k f = fun U =>
      conj (S.period.compPullback (S.inducingSymmetry (S.slabTransporter j k)) f U) := by
  rw [SlabDecomposition.slabCopy, if_neg h]
  rfl
theorem slabCopy_cases (j k : ZMod (2 * S.count)) (f : S.period.QuotientField → ℂ) :
    S.slabCopy j k f =
        S.period.compPullback (S.inducingSymmetry (S.slabTransporter j k)) f ∨
      S.slabCopy j k f = fun U =>
        conj (S.period.compPullback (S.inducingSymmetry (S.slabTransporter j k)) f U) := by
  by_cases h : S.IsGroupTranslation (S.slabTransporter j k)
  · exact Or.inl (slabCopy_of_translation S f h)
  · exact Or.inr (slabCopy_of_not_translation S f h)
def parityHom : ZMod (2 * S.count) →+* ZMod 2 := ZMod.castHom (Dvd.intro _ rfl) (ZMod 2)
theorem valModEqTwo_iff (a b : ZMod (2 * S.count)) :
    S.ValModEqTwo a b ↔ parityHom S a = parityHom S b := by
  have e : ∀ x : ZMod (2 * S.count), ((x.val : ℤ) : ZMod 2) = parityHom S x := fun x => by
    simp [parityHom, ZMod.natCast_val]
  rw [← e, ← e, SlabDecomposition.ValModEqTwo]
  exact (ZMod.intCast_eq_intCast_iff _ _ 2).symm
theorem valModEqTwo_iff_not (s i j : ZMod (2 * S.count)) :
    S.ValModEqTwo (s + i) j ↔ ¬ S.ValModEqTwo (s - 1 - i) j := by
  rw [valModEqTwo_iff, valModEqTwo_iff]
  have h : parityHom S (s + i) = parityHom S (s - 1 - i) + 1 := by
    have h₂ : (2 : ZMod 2) = 0 := rfl
    have e : s + i = (s - 1 - i) + 1 + 2 * i := by ring
    rw [e, map_add, map_add, map_mul, map_one, map_ofNat, h₂, zero_mul, add_zero]
  rw [h]
  generalize parityHom S (s - 1 - i) = x
  generalize parityHom S j = y
  revert x y
  decide
end SlabCopy
theorem slabCopyRule_holds (hP : SplitTorusPullbacks)
    (hT : SlabActionSimplyTransitive) (hD : SplitTorusDescent) :
    SlabCopyRule := by
  intro S j f hf
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hθ, -, hone, hidmem, hcompmem, -, -, -, hθmem, huniq,
    hspec, hclass, hnot⟩ := hT S
  obtain ⟨-, hall, -⟩ := hP 1 one_pos S.period S.normal S.normal_mem
    ((S.count : ℤ) * S.width) S.splits
  have hmem : ∀ k, S.slabTransporter j k ∈ S.generatedMaps := fun k => (hspec j k).1
  have hiso : ∀ k, S.InducesTorusMap (S.slabTransporter j k)
      (S.inducingSymmetry (S.slabTransporter j k)) := fun k =>
    SlabCopy.inducingSymmetry_spec S (hmem k)
  have hbdd : S.period.IsBoundedBorelFn f := ⟨hf.1, hf.2.1⟩
  have hsurj : ∀ k, Function.Surjective (S.period.pullbackField
      (S.inducingSymmetry (S.slabTransporter j k))) := fun k =>
    (hall _ (hiso k).1).1.bijective.2
  have hact : ∀ k, S.period.compPullback
      (S.inducingSymmetry (S.slabTransporter j k)) f ∈ S.slabAlgebraOfClass k := by
    intro k
    obtain ⟨hb, -, -, hdep⟩ := (hall _ (hiso k).1).2.2.2.2.2.2.1 f hbdd
    refine ⟨hb.1, hb.2, fun U U' h => hdep _ hf.2.2 U U' fun b hb' => h b ?_⟩
    obtain ⟨b₀, hb₀, rfl⟩ := hb'
    intro x hx
    have hi := (SlabCopy.mapsOrbits_and_descends S hD (hiso k).1).2
    obtain ⟨y, hy, rfl⟩ := SlabCopy.linkEndpoints_linkImage_subset hi b₀ hx
    have hon : S.period.descendPoint (S.inducingSymmetry (S.slabTransporter j k)) =
        (S.slabTransporter j k).pointMap := congrArg (·.pointMap) (hiso k).2
    have himg := (hspec j k).2
    rw [hon]
    change _ ∈ S.slabOfClass k
    rw [← himg]
    exact ⟨y, hb₀ hy, rfl⟩
  have hconj : ∀ (k : ZMod (2 * S.count)) (G : S.period.QuotientField → ℂ),
      G ∈ S.slabAlgebraOfClass k → (fun U => conj (G U)) ∈ S.slabAlgebraOfClass k := by
    rintro k G ⟨hm, ⟨C, hC⟩, hd⟩
    refine ⟨Complex.continuous_conj.measurable.comp hm, ⟨C, fun U => ?_⟩, fun U U' h => ?_⟩
    · simpa using hC U
    · simp only [hd U U' h]
  refine ⟨fun k => ?_, ?_, fun k => ?_, fun hre k => ?_, fun s i => ?_⟩
  · rcases SlabCopy.slabCopy_cases S j k f with h | h
    · rw [h]; exact hact k
    · rw [h]; exact hconj k _ (hact k)
  · have hid : S.MapsSlabTo j j (PeriodSublattice.TorusMap.identity S.period) :=
      ⟨hidmem, Set.image_id _⟩
    have hg : S.slabTransporter j j = PeriodSublattice.TorusMap.identity S.period :=
      (huniq j j).unique (hspec j j) hid
    have ht : S.IsGroupTranslation (S.slabTransporter j j) := by
      rw [hg]; exact ⟨_, hone.symm⟩
    rw [SlabCopy.slabCopy_of_translation S f ht]
    funext U
    have hb : S.period.descendOrientedLink
        (S.inducingSymmetry (S.slabTransporter j j)) = id := by
      have := congrArg (·.linkMap) (hiso j).2
      rw [hg] at this
      rw [hg]
      exact this
    rw [PeriodSublattice.compPullback, SlabCopy.pullbackField_eq_self S hD (hiso j).1 hb]
  · have hn : ∀ U, ‖S.slabCopy j k f U‖ = ‖f (S.period.pullbackField
        (S.inducingSymmetry (S.slabTransporter j k)) U)‖ := by
      intro U
      rcases SlabCopy.slabCopy_cases S j k f with h | h <;> rw [h]
      · rfl
      · simp [PeriodSublattice.compPullback]
    simp only [PeriodSublattice.supNorm, hn]
    exact (hsurj k).iSup_comp fun U => ‖f U‖
  · have hre' : ∀ U, (S.slabCopy j k f U).re = (f (S.period.pullbackField
        (S.inducingSymmetry (S.slabTransporter j k)) U)).re := by
      intro U
      rcases SlabCopy.slabCopy_cases S j k f with h | h <;> rw [h]
      · rfl
      · simp [PeriodSublattice.compPullback]
    refine ⟨fun U => ?_, ?_⟩
    · rcases SlabCopy.slabCopy_cases S j k f with h | h <;> rw [h]
      · exact hre _
      · simp [PeriodSublattice.compPullback, hre]
    · simp only [hre']
      exact (hsurj k).iInf_comp fun U => (f U).re
  · have hρ : IsClassIsometry S.normal (S.reflectSym (s.val : ℤ)).toFun :=
      isClassIsometry_reflectAcross (S.level_allowed _)
    have hc₁ := hspec j (s + i)
    have hr := hiso (s + i)
    obtain ⟨R, hR, hRf, hRi⟩ := SlabCopy.exists_comp_symmetry S hD hρ hr.1
    rw [hr.2] at hRi
    have hg' : S.slabTransporter j (s - 1 - i) =
        PeriodSublattice.TorusMap.compose (S.torusReflectionOfClass s)
          (S.slabTransporter j (s + i)) := by
      refine (huniq j (s - 1 - i)).unique (hspec j _) ⟨hcompmem _ (hθmem _) _ hc₁.1, ?_⟩
      change (S.torusReflectionOfClass s).pointMap ∘ (S.slabTransporter j (s + i)).pointMap ''
        S.slabOfClass j = _
      rw [Set.image_comp, hc₁.2, hθ]
    have hr' := hiso (s - 1 - i)
    have hind : S.period.descendedTorusMap (S.inducingSymmetry (S.slabTransporter j (s - 1 - i))) =
        S.period.descendedTorusMap R := by
      rw [hr'.2, hRi, hg']
      rfl
    have hpull : S.period.pullbackField
        (S.inducingSymmetry (S.slabTransporter j (s - 1 - i))) =
        S.period.pullbackField R :=
      (hall _ hr'.1).2.2.2.1 R hRf (congrArg (·.linkMap) hind)
    have hcomp : S.period.compPullback
        (S.inducingSymmetry (S.slabTransporter j (s - 1 - i))) f =
        S.period.compPullback (S.reflectSym (s.val : ℤ))
          (S.period.compPullback (S.inducingSymmetry (S.slabTransporter j (s + i))) f) := by
      rw [(hall _ hρ).2.2.2.2.2.2.2.2.1 _ R hr.1 hR f hbdd]
      funext U
      simp only [PeriodSublattice.compPullback, hpull]
    by_cases ht : S.IsGroupTranslation (S.slabTransporter j (s + i))
    · have hcong : S.ValModEqTwo (s + i) j := by
        by_contra h
        exact hnot _ ⟨ht, (hclass _ _ _ hc₁).2 h⟩
      have hnc := (SlabCopy.valModEqTwo_iff_not S s i j).1 hcong
      have hnt : ¬ S.IsGroupTranslation (S.slabTransporter j (s - 1 - i)) := fun h =>
        hnot _ ⟨h, (hclass _ _ _ (hspec j _)).2 hnc⟩
      rw [SlabCopy.slabCopy_of_translation S f ht,
        SlabCopy.slabCopy_of_not_translation S f hnt, hcomp]
      rfl
    · have hnc : ¬ S.ValModEqTwo (s + i) j := fun h => ht ((hclass _ _ _ hc₁).1 h)
      have hcong : S.ValModEqTwo (s - 1 - i) j := by
        by_contra h
        exact hnc ((SlabCopy.valModEqTwo_iff_not S s i j).2 h)
      have ht' := (hclass _ _ _ (hspec j _)).1 hcong
      rw [SlabCopy.slabCopy_of_not_translation S f ht,
        SlabCopy.slabCopy_of_translation S f ht', hcomp]
      funext U
      change conj (conj _) = _
      rw [Complex.conj_conj]
      rfl
end YangMills.Construction.InfiniteLattice

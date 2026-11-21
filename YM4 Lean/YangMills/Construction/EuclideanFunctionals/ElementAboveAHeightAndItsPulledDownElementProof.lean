import YangMills.Construction.EuclideanFunctionals.ElementAboveAHeightAndItsPulledDownElement
import YangMills.Construction.EuclideanFunctionals.TuplesAboveAHeightTheRestrictionsAgreeProof
import YangMills.Construction.SpectralTheory.EverySelfAdjointOperatorIsResolved
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror YangMills.Construction.MetricNotions
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.AboveHeight
open MulTensor (MulComponents)
open TensorCompRules (splitTerm)
theorem finCombIn_mono {U V : Set R4} (hUV : U ⊆ V) :
    finCombIn U ≤ finCombIn V := by apply _root_.YangMills.Construction.EuclideanFunctionals.HeightTuples.finCombIn_mono <;> assumption
theorem actFree_one (F : FreeSep) : (1 : EuclidMotion).actFree F = F := by apply _root_.YangMills.Construction.EuclideanFunctionals.one_actFree <;> assumption
theorem timeVec_three : timeVec 3 = 1 := by
  simp [YangMills.Construction.PeriodicLattice.coordVec]
theorem transl_mul_transl_neg (t : ℝ) :
    EuclidMotion.transl (t • timeVec) * EuclidMotion.transl ((-t) • timeVec) = 1 :=
  EuclidMotion.ext_of_apply fun x => by
    rw [EuclidMotion.mul_apply, EuclidMotion.transl_apply, EuclidMotion.transl_apply,
      EuclidMotion.one_apply]
    simp
theorem isOpen_setOf_lt_coord (t : ℝ) : IsOpen {x : R4 | t < x 3} :=
  isOpen_lt continuous_const (continuous_apply 3)
theorem isOpen_setOf_coord_lt_neg (t : ℝ) : IsOpen {x : R4 | x 3 < -t} :=
  isOpen_lt (continuous_apply 3) continuous_const
theorem isOpen_setOf_abs_coord_lt (t : ℝ) : IsOpen {x : R4 | |x 3| < t} :=
  isOpen_lt (continuous_abs.comp (continuous_apply 3)) continuous_const
theorem image_transl_neg_eq_upperHalf (t : ℝ) :
    (fun x => EuclidMotion.transl ((-t) • timeVec) x) '' {x : R4 | t < x 3} = upperHalf := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : t < x 3 := hx
    show 0 < (EuclidMotion.transl ((-t) • timeVec) x) 3
    rw [EuclidMotion.transl_apply, Pi.add_apply, Pi.smul_apply, timeVec_three]
    simp only [smul_eq_mul, mul_one]
    linarith
  · intro hy
    have hy' : 0 < y 3 := hy
    refine ⟨y + t • timeVec, ?_, ?_⟩
    · show t < (y + t • timeVec) 3
      rw [Pi.add_apply, Pi.smul_apply, timeVec_three]
      simp only [smul_eq_mul, mul_one]
      linarith
    · show EuclidMotion.transl ((-t) • timeVec) (y + t • timeVec) = y
      rw [EuclidMotion.transl_apply]
      simp
section
variable {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
theorem reconClass_of_mem {F : FreeSep} (hF : F ∈ finCombIn upperHalf) :
    reconClass σ F = σ.recon.cls ⟨F, hF⟩ :=
  dif_pos hF
theorem norm_expComplex_ham_le
    (hDiag : YangMills.Construction.SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hFacts : YangMills.Construction.ResolvedFacts.DiagonalizedFacts) {t : ℝ} (ht : 0 < t)
    (ψ : σ.space) :
    ‖YangMills.Construction.ResolvedOps.expComplex σ.recon.ham (t : ℂ) ψ‖ ≤ ‖ψ‖ := by
  have hDiagonal : YangMills.Construction.ResolvedOps.IsDiagonalized σ.recon.ham :=
    (hDiag.1 σ.space).2.2.2.1 _ σ.recon.ham_selfAdjoint
  have hContr := ((hFacts σ.space).2.2.2.1 _ hDiagonal
    σ.recon.ham_nonneg).1 (t : ℂ)
    (by show 0 ≤ ((t : ℂ)).re; simpa using ht.le)
  have hNorm : ‖YangMills.Construction.ResolvedOps.expComplex σ.recon.ham (t : ℂ)‖ ≤ 1 :=
    hContr
  calc ‖YangMills.Construction.ResolvedOps.expComplex σ.recon.ham (t : ℂ) ψ‖
      ≤ ‖YangMills.Construction.ResolvedOps.expComplex σ.recon.ham (t : ℂ)‖ * ‖ψ‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖ψ‖ := mul_le_mul_of_nonneg_right hNorm (norm_nonneg _)
    _ = ‖ψ‖ := one_mul _
theorem classPullDown_holds
    (hDiag : YangMills.Construction.SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hFacts : YangMills.Construction.ResolvedFacts.DiagonalizedFacts)
    (hRules : TupleRules.TupleSpanActionRules) {t : ℝ} (ht : 0 < t) :
    ClassPullDown σ t := by
  obtain ⟨-, hImages, hAction, -⟩ := hRules
  intro F hF
  have hUpper : F ∈ finCombIn upperHalf :=
    finCombIn_mono (fun x (hx : t < x 3) => show 0 < x 3 from ht.trans hx) hF
  have hDown : pullDown t F ∈ finCombIn upperHalf := by
    have hIm : pullDown t F ∈ finCombIn
        ((fun x => EuclidMotion.transl ((-t) • timeVec) x) '' {x : R4 | t < x 3}) :=
      (hImages (EuclidMotion.transl ((-t) • timeVec)) {x | t < x 3}
        (isOpen_setOf_lt_coord t)).2.2.mapsTo hF
    rwa [image_transl_neg_eq_upperHalf] at hIm
  have hRaise : (EuclidMotion.transl (t • timeVec)).actFree (pullDown t F) = F := by
    rw [pullDown, (hAction _ _ F).1, transl_mul_transl_neg, actFree_one]
  have hExp : YangMills.Construction.ResolvedOps.expComplex σ.recon.ham (t : ℂ)
      (σ.recon.cls ⟨pullDown t F, hDown⟩) =
        readClass σ.recon.cls
          ((EuclidMotion.transl (t • timeVec)).actFree (pullDown t F)) :=
    σ.recon.expHam_cls t ht.le ⟨pullDown t F, hDown⟩
  rw [hRaise] at hExp
  have hCls : reconClass σ F = YangMills.Construction.ResolvedOps.expComplex σ.recon.ham (t : ℂ)
      (reconClass σ (pullDown t F)) := by
    rw [reconClass_of_mem σ hDown]
    exact hExp.symm
  refine ⟨hUpper, hCls, ?_⟩
  rw [hCls]
  exact norm_expComplex_ham_le σ hDiag hFacts ht _
end
theorem freeConj_linComb (a b : ℂ) (F F' : FreeSep) :
    freeConj (a • F + b • F') = conj a • freeConj F + conj b • freeConj F' := by
  ext X
  simp [freeConj, Finsupp.mapRange_apply]
theorem flipConj_linComb (a b : ℂ) (F F' : FreeSep) :
    flipConj (a • F + b • F') =
      conj a • flipConj F + conj b • flipConj F' := by
  simp only [flipConj, freeConj_linComb, map_add, map_smul]
theorem conjLinearLeft_holds (S : ConnFamily) (t : ℝ) :
    ConjLinearLeft S t := by
  intro F _ F' _ A _ g _ a b
  simp only [insertion, freeMul3, flipConj_linComb, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
theorem linearRight_holds (S : ConnFamily) (t : ℝ) : LinearRight S t := by
  intro F _ A _ A' _ g _ a b
  simp only [insertion, freeMul3, map_add, map_smul, smul_eq_mul]
theorem sameTensors_freeMul (hC : MulComponents) {F F' A A' : FreeSep}
    (hd : MulDefined F A) (hd' : MulDefined F' A')
    (hF : SameTensors F F') (hA : SameTensors A A') :
    SameTensors (freeMul F A) (freeMul F' A') := by apply _root_.YangMills.Construction.EuclideanFunctionals.HeightTuples.sameTensors_freeMul <;> assumption
theorem sameTensors_rfl (F : FreeSep) : SameTensors F F :=
  ⟨rfl, fun _ _ => rfl⟩
theorem supp_eq_tsupport (f : R4 → ℂ) : supp f = tsupport f :=
  YangMills.Construction.SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
theorem mem_C1c_iff (f : R4 → ℂ) :
    f ∈ C1c ℂ ↔ ContDiff ℝ 1 f ∧ HasCompactSupport f := by
  have h₀ : IsCompactWrt (Ambient.metric defaultMirrorData Ambient.euclidean) (supp f) ↔
      IsCompact (supp f) :=
    YangMills.Construction.SeparatedTuplesR4.isCompactWrt_euclid_iff (fun _ _ => rfl) _
  have hiff : IsCompactWrt (Ambient.metric defaultMirrorData Ambient.euclidean) (supp f) ↔
      HasCompactSupport f := h₀.trans (by rw [supp_eq_tsupport]; rfl)
  exact and_congr Iff.rfl hiff
theorem isThinInsert_linComb {t : ℝ} {g g' : R4 → ℂ} (hg : IsThinInsert t g)
    (hg' : IsThinInsert t g') (a b : ℂ) :
    IsThinInsert t (fun x => a * g x + b * g' x) := by
  obtain ⟨g1, g2⟩ := (mem_C1c_iff g).1 hg.1
  obtain ⟨g1', g2'⟩ := (mem_C1c_iff g').1 hg'.1
  refine ⟨(mem_C1c_iff _).2 ⟨(contDiff_const.mul g1).add (contDiff_const.mul g1'), ?_⟩, ?_⟩
  · exact (g2.mul_left (f := fun _ => a)).add (g2'.mul_left (f := fun _ => b))
  · have hSub : tsupport (fun x => a * g x + b * g' x) ⊆ tsupport g ∪ tsupport g' := by
      refine closure_minimal ?_ ((isClosed_tsupport g).union (isClosed_tsupport g'))
      intro x hx
      by_contra hNot
      have hx1 : g x = 0 := by
        by_contra hne
        exact hNot (Or.inl (subset_tsupport _ hne))
      have hx2 : g' x = 0 := by
        by_contra hne
        exact hNot (Or.inr (subset_tsupport _ hne))
      exact hx (by simp [hx1, hx2])
    rw [supp_eq_tsupport]
    have k1 := hg.2
    have k2 := hg'.2
    rw [supp_eq_tsupport] at k1 k2
    exact hSub.trans (Set.union_subset k1 k2)
theorem linearInsert_holds (hRules : TupleRules.TupleSpanActionRules)
    (hTensor : TensorComponents.CenteredSeesTensorComps)
    (hC : MulComponents) (S : ConnFamily) {t : ℝ} (ht : 0 < t) :
    LinearInsert S t := by
  obtain ⟨-, -, -, -, hOpen, -, -, hEntries, -, hReflected, -⟩ := hRules
  intro F hF A hA g hg g' hg' a b
  have hG := ((hReflected.1 t ht.le F hF A hA).1)
  set G := flipConj F with hGdef
  have hBelowGap : Disjoint {x : R4 | x 3 < -t} {x : R4 | |x 3| < t} := by
    refine Set.disjoint_left.2 fun x (h1 : x 3 < -t) (h2 : |x 3| < t) => ?_
    have := (abs_lt.1 h2).1
    linarith
  have hGapAbove : Disjoint ({x : R4 | x 3 < -t} ∪ {x : R4 | |x 3| < t})
      {x : R4 | t < x 3} := by
    refine Set.disjoint_left.2 fun x hx (h2 : t < x 3) => ?_
    rcases hx with (h1 : x 3 < -t) | (h1 : |x 3| < t)
    · linarith
    · have := (abs_lt.1 h1).2
      linarith
  have hO₁ := (hOpen _ _ (isOpen_setOf_coord_lt_neg t) (isOpen_setOf_abs_coord_lt t) hBelowGap).1
  have hO₂ := (hOpen _ _ ((isOpen_setOf_coord_lt_neg t).union (isOpen_setOf_abs_coord_lt t))
    (isOpen_setOf_lt_coord t) hGapAbove).1
  have single : ∀ u : R4 → ℂ, IsThinInsert t u →
      singleComponent u ∈ finCombIn {x : R4 | |x 3| < t} ∧
      tensorComp 1 (singleComponent u) = tensorOfFns (fun _ : Fin 1 => u) ∧
      tensorCompZero (singleComponent u) = 0 ∧
      ∀ q, 1 ≤ q → q ≠ 1 → tensorComp q (singleComponent u) = 0 := by
    intro u hu
    have hCx : ComplexComponents (fun _ : Fin 1 => u) :=
      ⟨le_rfl, fun _ => hu.1, fun k l hkl => absurd (Subsingleton.elim k l) hkl⟩
    obtain ⟨e1, -, e3, e4, e5, -⟩ :=
      hEntries _ (isOpen_setOf_abs_coord_lt t) 1 1 (fun _ : Fin 1 => u) hCx (fun _ => hu.2)
    exact ⟨e1, e3, e4, e5⟩
  have hComb := isThinInsert_linComb hg hg' a b
  obtain ⟨m₁, t₁, z₁, o₁⟩ := single _ hComb
  obtain ⟨m₂, t₂, z₂, o₂⟩ := single _ hg
  obtain ⟨m₃, t₃, z₃, o₃⟩ := single _ hg'
  set E₁ := singleComponent (fun x => a * g x + b * g' x) with hE₁
  set e := singleComponent g with he
  set e' := singleComponent g' with he'
  have mE₂ : a • e + b • e' ∈ finCombIn {x : R4 | |x 3| < t} :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ m₂) (Submodule.smul_mem _ _ m₃)
  have hSame : SameTensors E₁ (a • e + b • e') := by
    refine ⟨by simp [z₁, z₂, z₃], fun q hq => ?_⟩
    by_cases hq1 : q = 1
    · subst hq1
      rw [map_add, map_smul, map_smul, t₁, t₂, t₃]
      funext x
      simp [tensorOfFns_apply]
    · rw [map_add, map_smul, map_smul, o₁ q hq hq1, o₂ q hq hq1, o₃ q hq hq1]
      simp
  obtain ⟨d₁, c₁⟩ := hO₁ G hG E₁ m₁
  obtain ⟨d₂, c₂⟩ := hO₁ G hG _ mE₂
  have d₃ := (hO₂ _ c₁ A hA).1
  have d₄ := (hO₂ _ c₂ A hA).1
  have hSame₂ := sameTensors_freeMul hC d₃ d₄
    (sameTensors_freeMul hC d₁ d₂ (sameTensors_rfl G) hSame) (sameTensors_rfl A)
  have hValue := (hTensor S).2.1 _ _ hSame₂
  simp only [insertion, freeMul3, ← hGdef]
  rw [hValue]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl
theorem holds_of_inputs (hMul : MulTensor.Holds)
    (hDiag : YangMills.Construction.SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hFacts : YangMills.Construction.ResolvedFacts.DiagonalizedFacts)
    (hTensor : TensorComponents.CenteredSeesTensorComps)
    (hRules : TupleRules.TupleSpanActionRules) : Holds := by
  intro m S σ t ht
  exact ⟨classPullDown_holds σ hDiag hFacts hRules ht,
    conjLinearLeft_holds S t,
    linearInsert_holds hRules hTensor (hMul m S σ).1 S ht,
    linearRight_holds S t⟩
end YangMills.Construction.EuclideanFunctionals.AboveHeight

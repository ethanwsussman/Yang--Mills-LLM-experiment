import YangMills.Construction.Continuum.FormOfAReflectionPositiveFunctional
import YangMills.Construction.Continuum.ModulusOfStrongContinuityOnOneTuple
import YangMills.Construction.Continuum.RotationLeavingAFunctionalInvariantActsUnitarily
import YangMills.Construction.Continuum.RulesOfTheOrthogonalActionProof
import YangMills.Construction.Continuum.TelescopingOverRotatedEntries
import YangMills.Construction.LimitTheorem.OsterwalderSchrader
import Mathlib
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.Continuum.RotationModulus
open YangMills.Construction.ReflectionPositivity.TupleForm
open YangMills.Construction.OrthogonalAction YangMills.Construction.Orthogonal
open YangMills.Construction.TestFunctions YangMills.Construction.SeparatedTuples
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem euclidNormVec_pos_of_ne_zero {u : AmbientSpace} (hu : u ≠ 0) : 0 < euclidNormVec u := by apply _root_.YangMills.Construction.LimitTheorem.ComponentConditions.euclidNormVec_pos_of_ne_zero <;> assumption
theorem euclidNormVec_timeReflection (x : AmbientSpace) :
    euclidNormVec (TimeAxis.timeReflection x) = euclidNormVec x := by
  simp [euclidNormVec, TimeAxis.timeReflection, Fin.sum_univ_four]
theorem setDistR4_ne_top {A B : Set AmbientSpace} (hA : A.Nonempty) (hB : B.Nonempty) :
    setDistR4 A B ≠ ⊤ := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have h : setDistR4 A B ≤ ENNReal.ofReal (euclidNormVec (a - b)) :=
    iInf₂_le_of_le a ha (iInf₂_le_of_le b hb le_rfl)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
theorem setDistR4_pos {A B : Set AmbientSpace} (hA : IsCompact A) (hB : IsCompact B)
    (hAn : A.Nonempty) (hBn : B.Nonempty) (hd : Disjoint A B) : 0 < setDistR4 A B := by
  have hc : ContinuousOn (fun p : AmbientSpace × AmbientSpace => euclidNormVec (p.1 - p.2)) (A ×ˢ B) :=
    (continuous_euclidNormVec.comp (continuous_fst.sub continuous_snd)).continuousOn
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hmin⟩ := (hA.prod hB).exists_isMinOn (hAn.prod hBn) hc
  have hab : a - b ≠ 0 := fun h => Set.disjoint_left.1 hd ha (by rwa [sub_eq_zero.1 h])
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.2 (euclidNormVec_pos_of_ne_zero hab)) ?_
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal ?_
  exact isMinOn_iff.1 hmin (x, y) ⟨hx, hy⟩
def timeReflectionMatrix : orthogonalGroupFour :=
  ⟨Matrix.diagonal ![1, 1, 1, -1], (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).2 (by
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp)⟩
theorem matMap_timeReflectionMatrix : matMap timeReflectionMatrix = TimeAxis.timeReflection := by
  funext x μ
  fin_cases μ <;> simp [matMap, timeReflectionMatrix, Matrix.mulVec_diagonal, TimeAxis.timeReflection]
theorem matMap_inv_matMap (Q : orthogonalGroupFour) (x : AmbientSpace) : matMap Q⁻¹ (matMap Q x) = x := by apply _root_.YangMills.Construction.OrthogonalAction.Laws.matMap_inv_matMap <;> assumption
theorem matMap_matMap_inv (Q : orthogonalGroupFour) (x : AmbientSpace) : matMap Q (matMap Q⁻¹ x) = x := by apply _root_.YangMills.Construction.OrthogonalAction.Laws.matMap_matMap_inv <;> assumption
theorem matMap_injective (Q : orthogonalGroupFour) : Function.Injective (matMap Q) :=
  Function.LeftInverse.injective (matMap_inv_matMap Q)
theorem timeReflection_injective : Function.Injective TimeAxis.timeReflection :=
  matMap_timeReflectionMatrix ▸ matMap_injective timeReflectionMatrix
theorem invMap_matMap (Q : orthogonalGroupFour) : invMap (matMap Q) = matMap Q⁻¹ :=
  funext fun x => by
    have h := Function.leftInverse_invFun (matMap_injective Q) (matMap Q⁻¹ x)
    rw [matMap_matMap_inv] at h
    exact h
theorem pushList_matMap (Q : orthogonalGroupFour) (l : List RealValued) :
    pushList (matMap Q) l = l.map (orthogonalAct Q) := by
  unfold pushList
  rw [invMap_matMap]
  rfl
section Laws
variable (hr : Laws.Statement)
include hr
theorem isC1c_orthogonalAct (Q : orthogonalGroupFour) {f : RealValued} (hf : IsC1c f) :
    IsC1c (orthogonalAct Q f) :=
  ((hr.1 Q Q).1 f hf).1
theorem tsupport_orthogonalAct (Q : orthogonalGroupFour) {f : RealValued} (hf : IsC1c f) :
    tsupport (orthogonalAct Q f) = matMap Q '' tsupport f :=
  ((hr.1 Q Q).1 f hf).2.2.1
theorem sharpNormR4_orthogonalAct (Q : orthogonalGroupFour) {f : RealValued} (hf : IsC1c f) {M : ℝ}
    (hM : 1 ≤ M) : sharpNormR4 M (orthogonalAct Q f) = sharpNormR4 M f :=
  ((hr.1 Q Q).1 f hf).2.2.2.1 M hM
theorem push_matMap_val (Q : orthogonalGroupFour) (X : SepTuple) :
    (push (matMap Q) X).1 = X.1.map (orthogonalAct Q) := by
  have hs : IsDisjointlySupported (pushList (matMap Q) X.1) := by
    rw [pushList_matMap]
    refine ⟨fun g hg => ?_, ?_⟩
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
      exact isC1c_orthogonalAct hr Q (X.2.1 f hf)
    · refine List.pairwise_map.2 (X.2.2.imp_of_mem fun hf hg hd => ?_)
      rw [tsupport_orthogonalAct hr Q (X.2.1 _ hf), tsupport_orthogonalAct hr Q (X.2.1 _ hg)]
      exact (Set.disjoint_image_iff (matMap_injective Q)).2 hd
  unfold push
  rw [dif_pos hs]
  exact pushList_matMap Q X.1
theorem push_timeReflection_val (X : SepTuple) :
    (push TimeAxis.timeReflection X).1 = X.1.map (orthogonalAct timeReflectionMatrix) := by
  rw [← matMap_timeReflectionMatrix]
  exact push_matMap_val hr timeReflectionMatrix X
theorem push_embed_mem (R : orthogonalGroupThree) {X : SepTuple}
    (hX : X ∈ supportedIn TimeAxis.upperHalfSpace) :
    push (matMap (embedOrthogonal R)) X ∈ supportedIn TimeAxis.upperHalfSpace := by
  intro g hg
  rw [push_matMap_val hr] at hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  rw [tsupport_orthogonalAct hr _ (X.2.1 f hf)]
  have himage := (hr.2.1 R R).2.2.2.2.2.2.2.1
  rw [← himage]
  exact Set.image_mono (hX f hf)
end Laws
theorem disjoint_tsupport_get (X : SepTuple) {a b : Fin X.1.length} (hab : a ≠ b) :
    Disjoint (tsupport (X.1.get a)) (tsupport (X.1.get b)) := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact List.pairwise_iff_get.1 X.2.2 a b h
  · exact (List.pairwise_iff_get.1 X.2.2 b a h).symm
theorem reflectedAndSupports_inl (hr : Laws.Statement) (X : SepTuple) (l : Fin X.1.length) :
    reflectedAndSupports X (Sum.inl l) =
      tsupport (orthogonalAct timeReflectionMatrix (X.1.get l)) := by
  rw [tsupport_orthogonalAct hr _ (X.2.1 _ (List.get_mem _ _)), matMap_timeReflectionMatrix]
  rfl
theorem isCompact_reflectedAndSupports (hr : Laws.Statement) (X : SepTuple)
    (i : Fin X.1.length ⊕ Fin X.1.length) : IsCompact (reflectedAndSupports X i) := by
  rcases i with l | l
  · rw [reflectedAndSupports_inl hr]
    exact (isC1c_orthogonalAct hr _ (X.2.1 _ (List.get_mem _ _))).2
  · exact (X.2.1 _ (List.get_mem _ _)).2
theorem tsupport_nonempty_of_fn_ne_zero {f : RealValued} (hf : f ≠ 0) : (tsupport f).Nonempty := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hf
  exact ⟨x, subset_tsupport f (Function.mem_support.2 hx)⟩
theorem reflectedAndSupports_nonempty (X : SepTuple) (h0 : ∀ f ∈ X.1, f ≠ 0)
    (i : Fin X.1.length ⊕ Fin X.1.length) : (reflectedAndSupports X i).Nonempty := by
  rcases i with l | l
  · exact (tsupport_nonempty_of_fn_ne_zero (h0 _ (List.get_mem _ _))).image _
  · exact tsupport_nonempty_of_fn_ne_zero (h0 _ (List.get_mem _ _))
theorem reflectedAndSupports_disjoint {X : SepTuple} (hX : X ∈ supportedIn TimeAxis.upperHalfSpace)
    {i j : Fin X.1.length ⊕ Fin X.1.length} (hij : i ≠ j) :
    Disjoint (reflectedAndSupports X i) (reflectedAndSupports X j) := by
  have hcross : ∀ a b : Fin X.1.length,
      Disjoint (TimeAxis.timeReflection '' tsupport (X.1.get a)) (tsupport (X.1.get b)) := by
    intro a b
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ hy
    have h₁ : TimeAxis.timeComponent x > 0 := hX _ (List.get_mem _ _) hx
    have h₂ : TimeAxis.timeComponent (TimeAxis.timeReflection x) > 0 := hX _ (List.get_mem _ _) hy
    have h₃ : TimeAxis.timeComponent (TimeAxis.timeReflection x) = -TimeAxis.timeComponent x := by
      simp [TimeAxis.timeComponent, TimeAxis.timeReflection, TimeAxis.timeIdx]
    linarith
  rcases i with a | a <;> rcases j with b | b
  · exact (Set.disjoint_image_iff timeReflection_injective).2
      (disjoint_tsupport_get X fun h => hij (by rw [h]))
  · exact hcross a b
  · exact (hcross b a).symm
  · exact disjoint_tsupport_get X fun h => hij (by rw [h])
theorem sInf_mem_pairwiseSupportDists (X : SepTuple) (hk : 1 ≤ X.size) :
    sInf (pairwiseSupportDists X) ∈ pairwiseSupportDists X := by
  have hfin : (pairwiseSupportDists X).Finite := by
    refine (Set.finite_range fun p : (Fin X.1.length ⊕ Fin X.1.length) ×
      (Fin X.1.length ⊕ Fin X.1.length) => setDistR4 (reflectedAndSupports X p.1)
        (reflectedAndSupports X p.2)).subset ?_
    rintro t ⟨i, j, -, rfl⟩
    exact ⟨(i, j), rfl⟩
  have hne : (pairwiseSupportDists X).Nonempty :=
    ⟨_, Sum.inl ⟨0, hk⟩, Sum.inr ⟨0, hk⟩, by simp, rfl⟩
  exact hne.csInf_mem hfin
theorem sInf_pairwiseSupportDists_ne_top (X : SepTuple) (hk : 1 ≤ X.size) (h0 : ∀ f ∈ X.1, f ≠ 0) :
    sInf (pairwiseSupportDists X) ≠ ⊤ := by
  obtain ⟨i, j, -, h⟩ := sInf_mem_pairwiseSupportDists X hk
  rw [h]
  exact setDistR4_ne_top (reflectedAndSupports_nonempty X h0 i) (reflectedAndSupports_nonempty X h0 j)
theorem minSupportDist_pos (hr : Laws.Statement) {X : SepTuple}
    (hX : X ∈ supportedIn TimeAxis.upperHalfSpace) (hk : 1 ≤ X.size) (h0 : ∀ f ∈ X.1, f ≠ 0) :
    0 < minSupportDist X := by
  refine ENNReal.toReal_pos ?_ (sInf_pairwiseSupportDists_ne_top X hk h0)
  obtain ⟨i, j, hij, h⟩ := sInf_mem_pairwiseSupportDists X hk
  rw [h]
  exact (setDistR4_pos (isCompact_reflectedAndSupports hr X i) (isCompact_reflectedAndSupports hr X j)
    (reflectedAndSupports_nonempty X h0 i) (reflectedAndSupports_nonempty X h0 j)
    (reflectedAndSupports_disjoint hX hij)).ne'
theorem ofReal_minSupportDist_le (X : SepTuple) (hk : 1 ≤ X.size) (h0 : ∀ f ∈ X.1, f ≠ 0)
    {i j : Fin X.1.length ⊕ Fin X.1.length} (hij : i ≠ j) :
    ENNReal.ofReal (minSupportDist X) ≤
      setDistR4 (reflectedAndSupports X i) (reflectedAndSupports X j) := by
  rw [minSupportDist, ENNReal.ofReal_toReal (sInf_pairwiseSupportDists_ne_top X hk h0)]
  exact sInf_le ⟨i, j, hij, rfl⟩
theorem bddAbove_supportNorms (X : SepTuple) :
    BddAbove {r | ∃ x ∈ ⋃ l, tsupport (X.1.get l), r = euclidNormVec x} := by
  have hU : IsCompact (⋃ l, tsupport (X.1.get l)) :=
    isCompact_iUnion fun l => (X.2.1 _ (List.get_mem _ _)).2
  refine ((hU.image continuous_euclidNormVec).bddAbove).mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx, rfl⟩
theorem euclidNormVec_le_maxSupportRadius (X : SepTuple) {f : RealValued} (hf : f ∈ X.1)
    {x : AmbientSpace} (hx : x ∈ tsupport f) : euclidNormVec x ≤ maxSupportRadius X := by
  obtain ⟨l, rfl⟩ := List.get_of_mem hf
  exact le_csSup (bddAbove_supportNorms X) ⟨x, Set.mem_iUnion.2 ⟨l, hx⟩, rfl⟩
theorem maxSupportRadius_pos {X : SepTuple} (hX : X ∈ supportedIn TimeAxis.upperHalfSpace)
    (hk : 1 ≤ X.size) (h0 : ∀ f ∈ X.1, f ≠ 0) : 0 < maxSupportRadius X := by
  have hf : X.1.get ⟨0, hk⟩ ∈ X.1 := List.get_mem _ _
  obtain ⟨x, hx⟩ := tsupport_nonempty_of_fn_ne_zero (h0 _ hf)
  have ht : TimeAxis.timeComponent x > 0 := hX _ hf hx
  have hne : x ≠ 0 := by
    rintro rfl
    simp [TimeAxis.timeComponent] at ht
  exact (euclidNormVec_pos_of_ne_zero hne).trans_le (euclidNormVec_le_maxSupportRadius X hf hx)
theorem rotateEntriesOn_append (Q : orthogonalGroupFour) (k : ℕ) {A B : List RealValued}
    (hA : A.length = k) (hB : B.length = k) :
    Rotations.OrthogonalSetting.rotateEntriesOn Q (Finset.Icc (k + 1) (2 * k)) (A ++ B) =
      A ++ B.map (orthogonalAct Q) := by
  unfold Rotations.OrthogonalSetting.rotateEntriesOn
  rw [List.zipIdx_append, List.map_append]
  congr 1
  · conv_rhs => rw [← List.zipIdx_map_fst 1 A]
    refine List.map_congr_left ?_
    rintro ⟨f, n⟩ hp
    have h := List.mem_zipIdx hp
    have hn : n ∉ Finset.Icc (k + 1) (2 * k) := by
      rw [Finset.mem_Icc]
      omega
    simp [hn]
  · conv_rhs => rw [← List.zipIdx_map_fst (1 + A.length) B, List.map_map]
    refine List.map_congr_left ?_
    rintro ⟨f, n⟩ hp
    have h := List.mem_zipIdx hp
    have hn : n ∈ Finset.Icc (k + 1) (2 * k) := by
      rw [Finset.mem_Icc]
      omega
    simp [hn]
theorem sum_Icc_upper_half_mul_prod (k : ℕ) (a v s u : ℕ → ℝ) (ha₁ : ∀ n < k, a n = s n)
    (ha₂ : ∀ n < k, a (k + n) = s n) (hv : ∀ n < k, v (k + n) = u n) :
    ∑ l ∈ Finset.Icc (k + 1) (2 * k), v (l - 1) *
        ∏ l' ∈ (Finset.Icc 1 (2 * k)).erase l, a (l' - 1) =
      (∏ j ∈ Finset.range k, s j) *
        ∑ i ∈ Finset.range k, u i * ∏ j ∈ (Finset.range k).erase i, s j := by
  have hI : Finset.Icc (k + 1) (2 * k) = (Finset.range k).image fun i => k + 1 + i := by
    ext l
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨l - (k + 1), by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [hI, Finset.sum_image (by intro x _ y _ h; dsimp only at h; omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have hE : (Finset.Icc 1 (2 * k)).erase (k + 1 + i) =
      (Finset.range k).image (fun j => j + 1) ∪
        ((Finset.range k).erase i).image fun j => k + 1 + j := by
    ext l
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union, Finset.mem_image,
      Finset.mem_range]
    constructor
    · rintro ⟨hne, h₁, h₂⟩
      by_cases hl : l ≤ k
      · exact Or.inl ⟨l - 1, by omega, by omega⟩
      · exact Or.inr ⟨l - (k + 1), ⟨by omega, by omega⟩, by omega⟩
    · rintro (⟨j, hj, rfl⟩ | ⟨j, ⟨hj, hj'⟩, rfl⟩)
      · omega
      · omega
  have hdisj : Disjoint ((Finset.range k).image (fun j => j + 1))
      (((Finset.range k).erase i).image fun j => k + 1 + j) := by
    refine Finset.disjoint_left.2 ?_
    intro l h₁ h₂
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h₁
    obtain ⟨j', hj', h⟩ := Finset.mem_image.1 h₂
    have := Finset.mem_range.1 hj
    omega
  rw [hE, Finset.prod_union hdisj, Finset.prod_image (by intro x _ y _ h; dsimp only at h; omega),
    Finset.prod_image (by intro x _ y _ h; dsimp only at h; omega)]
  have h₁ : ∏ x ∈ Finset.range k, a (x + 1 - 1) = ∏ j ∈ Finset.range k, s j :=
    Finset.prod_congr rfl fun x hx => by
      rw [Nat.add_sub_cancel]
      exact ha₁ x (Finset.mem_range.1 hx)
  have h₂ : ∏ x ∈ (Finset.range k).erase i, a (k + 1 + x - 1) =
      ∏ j ∈ (Finset.range k).erase i, s j :=
    Finset.prod_congr rfl fun x hx => by
      have hx' := Finset.mem_range.1 (Finset.mem_of_mem_erase hx)
      rw [show k + 1 + x - 1 = k + x by omega]
      exact ha₂ x hx'
  rw [h₁, h₂, show k + 1 + i - 1 = k + i by omega, hv i hi']
  ring
theorem componentAt_eq_get (X : SepTuple) (l : Fin X.1.length) : X.componentAt l = X.1.get l := by
  simp [SepTuple.componentAt]
theorem continuityBound_eq (M : ℝ) (X : SepTuple) (R : orthogonalGroupThree) (b : ℝ) :
    continuityBound M X R b = 2 * b * ((∏ j ∈ Finset.range X.1.length, sharpNormR4 M (X.componentAt j)) *
      ∑ i ∈ Finset.range X.1.length,
        sharpNormR4 M (orthogonalAct (embedOrthogonal R) (X.componentAt i) - X.componentAt i) *
          ∏ j ∈ (Finset.range X.1.length).erase i, sharpNormR4 M (X.componentAt j)) := by
  have hP : ∏ j ∈ Finset.range X.1.length, sharpNormR4 M (X.componentAt j) =
      ∏ l, sharpNormR4 M (X.1.get l) := by
    rw [← Fin.prod_univ_eq_prod_range (fun j => sharpNormR4 M (X.componentAt j))]
    exact Finset.prod_congr rfl fun l _ => by rw [componentAt_eq_get]
  have hE : ∀ l : Fin X.1.length,
      ∏ j ∈ (Finset.range X.1.length).erase l, sharpNormR4 M (X.componentAt j) =
        ∏ l' ∈ Finset.univ.erase l, sharpNormR4 M (X.1.get l') := by
    intro l
    symm
    refine Finset.prod_bij (fun j _ => (j : ℕ)) ?_ ?_ ?_ ?_
    · intro j hj
      have hj' : j ≠ l := (Finset.mem_erase.1 hj).1
      exact Finset.mem_erase.2 ⟨fun h => hj' (Fin.ext h), Finset.mem_range.2 j.2⟩
    · intro a _ b _ h
      exact Fin.ext h
    · intro n hn
      obtain ⟨h₁, h₂⟩ := Finset.mem_erase.1 hn
      refine ⟨⟨n, Finset.mem_range.1 h₂⟩, Finset.mem_erase.2 ⟨fun h => h₁ ?_, Finset.mem_univ _⟩, rfl⟩
      exact congrArg Fin.val h
    · intro j _
      rw [componentAt_eq_get]
  have hS : ∑ i ∈ Finset.range X.1.length,
        sharpNormR4 M (orthogonalAct (embedOrthogonal R) (X.componentAt i) - X.componentAt i) *
          ∏ j ∈ (Finset.range X.1.length).erase i, sharpNormR4 M (X.componentAt j) =
      ∑ l, sharpNormR4 M (orthogonalAct (embedOrthogonal R) (X.1.get l) - X.1.get l) *
        ∏ l' ∈ Finset.univ.erase l, sharpNormR4 M (X.1.get l') := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => sharpNormR4 M (orthogonalAct (embedOrthogonal R)
      (X.componentAt i) - X.componentAt i) *
        ∏ j ∈ (Finset.range X.1.length).erase i, sharpNormR4 M (X.componentAt j))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hE l, componentAt_eq_get]
  rw [hP, hS, continuityBound]
  ring
theorem two_mul_sub_le_continuityBound (hr : Laws.Statement)
    (ht : Rotations.OrthogonalSetting.RotatedEntriesTelescoping)
    {M : ℝ} {σ : TupleFunctional} {B : ℕ → ℝ → ℝ → ℝ} (hM : 1 ≤ M)
    (hP : RotationHypotheses M σ B) {X : SepTuple}
    (hX : X ∈ supportedIn TimeAxis.upperHalfSpace) (hk : 1 ≤ X.size) (h0 : ∀ f ∈ X.1, f ≠ 0)
    (R : orthogonalGroupThree)
    (hR : matrixOperatorNorm (R.1 - 1) * maxSupportRadius X ≤ minSupportDist X / 4) :
    2 * (σ (SepTuple.juxt (push TimeAxis.timeReflection X) X) -
        σ (SepTuple.juxt (push TimeAxis.timeReflection X) (push (matMap (embedOrthogonal R)) X))) ≤
      continuityBound M X R
        (B (2 * X.size) (minSupportDist X / 2) (maxSupportRadius X + minSupportDist X)) := by
  have hd := minSupportDist_pos hr hX hk h0
  have hR0 := maxSupportRadius_pos hX hk h0
  have hdef : SepTuple.Composable (push TimeAxis.timeReflection X) X := (hr.2.2.1 1).1 X hX X hX
  have hdefR : SepTuple.Composable (push TimeAxis.timeReflection X)
      (push (matMap (embedOrthogonal R)) X) :=
    (hr.2.2.1 1).1 X hX _ (push_embed_mem hr R hX)
  have hlist : (SepTuple.juxt (push TimeAxis.timeReflection X) X).1 =
      X.1.map (orthogonalAct timeReflectionMatrix) ++ X.1 := by
    rw [SepTuple.juxt_val hdef, push_timeReflection_val hr]
  have hlistR : (SepTuple.juxt (push TimeAxis.timeReflection X)
      (push (matMap (embedOrthogonal R)) X)).1 =
      X.1.map (orthogonalAct timeReflectionMatrix) ++ X.1.map (orthogonalAct (embedOrthogonal R)) := by
    rw [SepTuple.juxt_val hdefR, push_timeReflection_val hr, push_matMap_val hr]
  generalize hh : SepTuple.juxt (push TimeAxis.timeReflection X) X = h at hlist ⊢
  have hlen : h.size = 2 * X.1.length := by
    simp only [SepTuple.size, hlist, List.length_append, List.length_map]
    omega
  have hball : ∀ f ∈ h.1, tsupport f ⊆ closedBallR4 0 (maxSupportRadius X) := by
    intro f hf x hx
    rw [hlist] at hf
    show euclidNormVec (x - 0) ≤ _
    rw [sub_zero]
    rcases List.mem_append.1 hf with hf | hf
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
      rw [tsupport_orthogonalAct hr _ (X.2.1 g hg), matMap_timeReflectionMatrix] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [euclidNormVec_timeReflection]
      exact euclidNormVec_le_maxSupportRadius X hg hy
    · exact euclidNormVec_le_maxSupportRadius X hf hx
  have hpair : h.1.Pairwise (fun f g => ENNReal.ofReal (minSupportDist X) ≤
      setDistR4 (tsupport f) (tsupport g)) := by
    rw [hlist]
    refine List.pairwise_append.2 ⟨List.pairwise_map.2 ?_, ?_, ?_⟩
    · refine List.pairwise_iff_get.2 fun a b hab => ?_
      have := ofReal_minSupportDist_le X hk h0 (i := Sum.inl a) (j := Sum.inl b)
        (by simpa using hab.ne)
      rwa [reflectedAndSupports_inl hr, reflectedAndSupports_inl hr] at this
    · refine List.pairwise_iff_get.2 fun a b hab => ?_
      exact ofReal_minSupportDist_le X hk h0 (i := Sum.inr a) (j := Sum.inr b)
        (by simpa using hab.ne)
    · intro f hf g hg
      obtain ⟨f', hf', rfl⟩ := List.mem_map.1 hf
      obtain ⟨a, rfl⟩ := List.get_of_mem hf'
      obtain ⟨b, rfl⟩ := List.get_of_mem hg
      have := ofReal_minSupportDist_le X hk h0 (i := Sum.inl a) (j := Sum.inr b) (by simp)
      rwa [reflectedAndSupports_inl hr] at this
  have hnorm : matrixOperatorNorm ((embedOrthogonal R).1 - 1) * maxSupportRadius X ≤
      minSupportDist X / 4 := by
    rw [(hr.2.1 R R).2.2.2.2.2.2.1]
    exact hR
  have hIsub : Finset.Icc (X.1.length + 1) (2 * X.1.length) ⊆ Finset.Icc 1 (2 * X.1.length) :=
    Finset.Icc_subset_Icc (by omega) le_rfl
  obtain ⟨hI, hle⟩ := ht M σ B hM hP.entrywiseLinear
    (fun k' hk' d r hd' hr' => ⟨hP.bound_nonneg k' hk' d r hd' hr', hP.bound_spec k' hk' d r hd' hr'⟩)
    (2 * X.1.length) (minSupportDist X) (maxSupportRadius X) h
    (by have : 1 ≤ X.1.length := hk
        omega) hd hR0 hlen hball hpair (embedOrthogonal R)
    (Finset.Icc (X.1.length + 1) (2 * X.1.length)) hnorm hIsub
  have hrot : (⟨Rotations.OrthogonalSetting.rotateEntriesOn (embedOrthogonal R)
        (Finset.Icc (X.1.length + 1) (2 * X.1.length)) h.1, hI⟩ : SepTuple) =
      SepTuple.juxt (push TimeAxis.timeReflection X) (push (matMap (embedOrthogonal R)) X) := by
    refine Subtype.ext ?_
    rw [hlistR]
    show Rotations.OrthogonalSetting.rotateEntriesOn _ _ h.1 = _
    rw [hlist]
    exact rotateEntriesOn_append _ _ (by simp) rfl
  rw [hrot] at hle
  have hc1 : ∀ n, n < X.1.length → IsC1c (X.componentAt n) := by
    intro n hn
    have : X.componentAt n = X.1[n] := List.getD_eq_getElem _ _ hn
    rw [this]
    exact X.2.1 _ (List.getElem_mem hn)
  have e₁ : ∀ n, n < X.1.length → h.componentAt n = orthogonalAct timeReflectionMatrix (X.componentAt n) := by
    intro n hn
    have hn' : n < (X.1.map (orthogonalAct timeReflectionMatrix)).length := by simpa using hn
    simp only [SepTuple.componentAt, hlist]
    rw [List.getD_append _ _ _ _ hn', List.getD_eq_getElem _ _ hn', List.getElem_map,
      List.getD_eq_getElem _ _ hn]
  have e₂ : ∀ n, n < X.1.length → h.componentAt (X.1.length + n) = X.componentAt n := by
    intro n hn
    have hn' : (X.1.map (orthogonalAct timeReflectionMatrix)).length ≤ X.1.length + n := by simp
    simp only [SepTuple.componentAt, hlist]
    rw [List.getD_append_right _ _ _ _ hn']
    simp
  have hsum := sum_Icc_upper_half_mul_prod X.1.length (fun n => sharpNormR4 M (h.componentAt n))
    (fun n => sharpNormR4 M (orthogonalAct (embedOrthogonal R) (h.componentAt n) - h.componentAt n))
    (fun n => sharpNormR4 M (X.componentAt n))
    (fun n => sharpNormR4 M (orthogonalAct (embedOrthogonal R) (X.componentAt n) - X.componentAt n))
    (fun n hn => by
      show sharpNormR4 M (h.componentAt n) = sharpNormR4 M (X.componentAt n)
      rw [e₁ n hn]
      exact sharpNormR4_orthogonalAct hr _ (hc1 n hn) hM)
    (fun n hn => by
      show sharpNormR4 M (h.componentAt (X.1.length + n)) = sharpNormR4 M (X.componentAt n)
      rw [e₂ n hn])
    (fun n hn => by
      show sharpNormR4 M (orthogonalAct (embedOrthogonal R) (h.componentAt (X.1.length + n)) -
        h.componentAt (X.1.length + n)) = _
      rw [e₂ n hn])
  beta_reduce at hsum
  rw [hsum] at hle
  rw [continuityBound_eq]
  change 2 * (σ h - σ (SepTuple.juxt (push TimeAxis.timeReflection X)
      (push (matMap (embedOrthogonal R)) X))) ≤
    2 * B (2 * X.1.length) (minSupportDist X / 2) (maxSupportRadius X + minSupportDist X) * _
  have h₁ : σ h - σ (SepTuple.juxt (push TimeAxis.timeReflection X)
      (push (matMap (embedOrthogonal R)) X)) ≤
      |σ (SepTuple.juxt (push TimeAxis.timeReflection X) (push (matMap (embedOrthogonal R)) X)) -
        σ h| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  linarith
theorem basisVec_mem_spanIn {X : SepTuple} (hX : X ∈ supportedIn TimeAxis.upperHalfSpace) :
    basisVec X ∈ spanIn TimeAxis.upperHalfSpace :=
  Submodule.subset_span ⟨⟨X, hX⟩, rfl⟩
theorem reflectionForm_basisVec (σ : TupleFunctional) {X Y : SepTuple}
    (hX : X ∈ supportedIn TimeAxis.upperHalfSpace) (hY : Y ∈ supportedIn TimeAxis.upperHalfSpace) :
    reflectionForm σ ⟨basisVec X, basisVec_mem_spanIn hX⟩ ⟨basisVec Y, basisVec_mem_spanIn hY⟩ =
      (σ (SepTuple.juxt (push TimeAxis.timeReflection X) Y) : ℂ) := by
  simp only [reflectionForm, reflectConj, conjugation_basisVec, pushSpan, linearExtend_basisVec,
    formalMul_basisVec, TupleFunctional.spanExtension]
theorem isPosSemidefHermitianForm_reflectionForm
    (hf : ReflectionPositiveForm.FormPropertiesStatement) {σ : TupleFunctional}
    (hp : ForwardCone.IsRPTimeZero σ) :
    FormCompletion.IsPosSemidefHermitianForm (reflectionForm σ) := by
  obtain ⟨⟨hF, hpos⟩, ⟨hh, -⟩, -⟩ := hf σ hp
  exact ⟨hF.add_left, hF.smul_left, hF.add_right, hF.smul_right, hh,
    fun F => (Complex.nonneg_iff.1 (hpos F)).1⟩
theorem norm_sq_tupleState_sub (hf : ReflectionPositiveForm.FormPropertiesStatement)
    (hc : FormCompletion.FormCompletionIsHilbertSpace)
    (hu : RotationInvariance.InvariantRotationIsUnitary) {σ : TupleFunctional}
    {R : orthogonalGroupThree} (hp : ForwardCone.IsRPTimeZero σ)
    (hinv : σ.IsInvariant (matMap (embedOrthogonal R))) {X : SepTuple}
    (hX : X ∈ supportedIn TimeAxis.upperHalfSpace)
    (hR : push (matMap (embedOrthogonal R)) X ∈ supportedIn TimeAxis.upperHalfSpace) :
    ‖tupleState σ _ hR - tupleState σ X hX‖ ^ 2 =
      2 * (σ (SepTuple.juxt (push TimeAxis.timeReflection X) X) -
        σ (SepTuple.juxt (push TimeAxis.timeReflection X) (push (matMap (embedOrthogonal R)) X))) := by
  have hq := isPosSemidefHermitianForm_reflectionForm hf hp
  have hin := (hc _ (reflectionForm σ) hq).2.1.2.2.2.2.2.2.1
  let F : PositiveSpan := ⟨basisVec X, basisVec_mem_spanIn hX⟩
  let G : PositiveSpan := ⟨basisVec (push (matMap (embedOrthogonal R)) X), basisVec_mem_spanIn hR⟩
  have hGF : (G : FormalSpan) = pushSpan (matMap (embedOrthogonal R)) (F : FormalSpan) := by
    simp only [G, F, pushSpan, linearExtend_basisVec]
  have hkeep : reflectionForm σ G G = reflectionForm σ F F := (hu σ R hp hinv).1 F F G G hGF hGF
  have e₁ : tupleState σ _ hR = FormCompletion.classVec (reflectionForm σ) G := rfl
  have e₂ : tupleState σ X hX = FormCompletion.classVec (reflectionForm σ) F := rfl
  have hFF : reflectionForm σ F F = (σ (SepTuple.juxt (push TimeAxis.timeReflection X) X) : ℂ) :=
    reflectionForm_basisVec σ hX hX
  have hFG : reflectionForm σ F G =
      (σ (SepTuple.juxt (push TimeAxis.timeReflection X) (push (matMap (embedOrthogonal R)) X)) : ℂ) :=
    reflectionForm_basisVec σ hX hR
  rw [e₁, e₂, norm_sub_sq (𝕜 := ℂ),
    @norm_sq_eq_re_inner ℂ _ _ _ _ (FormCompletion.classVec (reflectionForm σ) G),
    @norm_sq_eq_re_inner ℂ _ _ _ _ (FormCompletion.classVec (reflectionForm σ) F), hin, hin, hin,
    hkeep, hq.hermitian F G, hFF, hFG]
  simp only [Complex.conj_ofReal, RCLike.re_to_complex, Complex.ofReal_re]
  ring
theorem modulusEstimate_holds (hr : Laws.Statement)
    (hu : RotationInvariance.InvariantRotationIsUnitary)
    (ht : Rotations.OrthogonalSetting.RotatedEntriesTelescoping)
    (hf : ReflectionPositiveForm.FormPropertiesStatement)
    (hc : FormCompletion.FormCompletionIsHilbertSpace) : ModulusEstimate := by
  intro M σ B hM hP X hX hk h0
  refine ⟨minSupportDist_pos hr hX hk h0, maxSupportRadius_pos hX hk h0, fun R hR => ?_⟩
  have hRX := push_embed_mem hr R hX
  exact ⟨hRX, norm_sq_tupleState_sub hf hc hu hP.reflectionPositive (hP.orthogonal_invariant R) hX hRX,
    two_mul_sub_le_continuityBound hr ht hM hP hX hk h0 R hR⟩
end YangMills.Construction.Continuum.RotationModulus
end

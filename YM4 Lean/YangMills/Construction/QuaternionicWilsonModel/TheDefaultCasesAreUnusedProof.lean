import YangMills.Construction.Torus.HypercubicGroupTranslationsAndInvarianceOnTorusOrFourSpace
import YangMills.Construction.Continuum.CompactSupportAndTensorsOfSeparatedTuples
import YangMills.Construction.QuaternionicWilsonModel.TheArgumentsLieInTheirDomains
import YangMills.Construction.QuaternionicWilsonModel.TheDefaultCasesAreUnused
import YangMills.Construction.QuaternionicWilsonModel.WhatTheTopGivesAtEveryCouplingProof
import YangMills.Construction.ReflectionPositivity.FactsOnSeparatedTuplesOfFourSpace
import YangMills.Construction.ReflectionPositivity.LatticeFormulaForTheScalarProductProof
import YangMills.Construction.ReflectionPositivity.UnitNormalReflectionAndLatticeMirrors
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotions
import Mathlib
set_option autoImplicit false
open Filter
open scoped NNReal ComplexOrder ComplexConjugate ContDiff Topology
noncomputable section
namespace YangMills.Construction.ConditionDefaults
open YangMills.Construction.SeparatedTuples YangMills.Construction.ReflectionPositivity.TupleForm
open YangMills.Construction.LimitTheorem YangMills.Construction.SystemsWithFiveBounds
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Mirrors (ReflectingHyperplane)
open YangMills.Construction.HilbertSpaceBasics (IsPosSemidef)
open YangMills.Construction.ReflectionPositivity.Reconstruction (spanClass posClass timeBasisVec embedSpatial)
open YangMills.Construction.TorusTransport (hyperoctahedral)
open YangMills.Construction.TestSpaces (SepTupleOfCard)
open YangMills.Construction.TorusMetric (euclidNormVec)
open Matrix
theorem isometry_inverse_spec
    (hm : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine)
    {r : AmbientSpace → AmbientSpace} (hr : IsEuclidIsometry r) :
    (∀ y, r (invMap r y) = y) ∧ ∀ x, invMap r (r x) = x := by
  obtain ⟨R, hR, v, hv⟩ := hm r hr
  have h1 : R * Rᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hR
  have h2 : Rᵀ * R = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).1 hR
  let s : AmbientSpace → AmbientSpace := fun y => Rᵀ *ᵥ (y - v)
  have hrs : ∀ y, r (s y) = y := fun y => by
    simp [s, hv, Matrix.mulVec_mulVec, h1]
  have hsr : ∀ x, s (r x) = x := fun x => by
    simp [s, hv, Matrix.mulVec_mulVec, h2]
  have hinj : Function.Injective r := Function.LeftInverse.injective hsr
  have hl : ∀ x, invMap r (r x) = x := Function.leftInverse_invFun hinj
  refine ⟨fun y => ?_, hl⟩
  have : invMap r y = s y := by
    conv_lhs => rw [← hrs y]
    exact hl _
  rw [this, hrs]
theorem push_val (hI : BasicFacts.IsometryActionOnTuples) {r : AmbientSpace → AmbientSpace}
    (hr : IsEuclidIsometry r) (X : SepTuple) :
    (push r X).1 = pushList r X.1 := by
  have hs := (hI r hr X X).1
  simp [push, hs]
theorem isEuclidIsometry_invMap {r : AmbientSpace → AmbientSpace} (hr : IsEuclidIsometry r)
    (hright : ∀ y, r (invMap r y) = y) : IsEuclidIsometry (invMap r) := fun x y => by
  have h := hr (invMap r x) (invMap r y)
  rw [hright, hright] at h
  exact h.symm
theorem actsWithoutFallback_of_isometry
    (hm : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine)
    (hI : BasicFacts.IsometryActionOnTuples) {r : AmbientSpace → AmbientSpace}
    (hr : IsEuclidIsometry r) :
    ActsWithoutFallback r :=
  ⟨(isometry_inverse_spec hm hr).1, (isometry_inverse_spec hm hr).2, push_val hI hr⟩
theorem isEuclidIsometry_rigidMotion (r : Motions.RigidMotion) : IsEuclidIsometry r.toFun :=
    fun x y => by
  simp only [Motions.RigidMotion.toFun]
  rw [add_sub_add_right_eq_sub, ← Matrix.mulVec_sub]
  exact ConfigSpace.euclidNormVec_orth_mulVec r.mat_mem _
theorem isEuclidIsometry_hyperoctahedral (w : hyperoctahedral) : IsEuclidIsometry w.1 := by apply _root_.YangMills.Construction.TorusSymmetries.euclidNormVec_sub_apply <;> assumption
theorem isEuclidIsometry_reflect (hmf : Mirrors.UnitNormalAndLattice.Statement)
    (M : ReflectingHyperplane) : IsEuclidIsometry M.reflect := by
  have hI := (hmf M 1 one_pos).2.2.2.1.2.2.1
  intro x y
  have h := hI.dist_eq (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  simp only [ReflectingHyperplane.reflectL2, EuclideanSpace.dist_eq, Real.dist_eq, sq_abs] at h
  simpa [TorusMetric.euclidNormVec] using h
theorem actionsWellDefined (hm : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine)
    (hI : BasicFacts.IsometryActionOnTuples)
    (hmf : Mirrors.UnitNormalAndLattice.Statement) :
    ActionsWellDefined where
  isometry_and_inverse r hr :=
    have hi := isEuclidIsometry_invMap hr (isometry_inverse_spec hm hr).1
    ⟨actsWithoutFallback_of_isometry hm hI hr, hi, actsWithoutFallback_of_isometry hm hI hi⟩
  translate_isometry := isEuclidIsometry_translate
  hyperoctahedral_isometry := isEuclidIsometry_hyperoctahedral
  rigidMotion_isometry := isEuclidIsometry_rigidMotion
  rotation_isometry R := isEuclidIsometry_rigidMotion (ofOrthogonal R)
  mirror_isometry := isEuclidIsometry_reflect hmf
  timeReflection_isometry := by
    rw [Mirrors.timeReflection_eq_axialReflection]
    exact isEuclidIsometry_reflect hmf _
theorem exists_sepTuple_in_open (n : ℕ) : ∀ O : Set AmbientSpace, IsOpen O → O.Nonempty →
    ∃ X ∈ supportedIn O, X.1.length = n ∧ ∀ f ∈ X.1, f ≠ 0 := by
  induction n with
  | zero =>
    intro O _ _
    exact ⟨SepTuple.nil, nil_mem_supportedIn O, rfl, by simp [SepTuple.nil]⟩
  | succ n ih =>
    intro O hO ⟨x, hx⟩
    obtain ⟨y, hy, hne⟩ := (infinite_of_mem_nhds x (hO.mem_nhds hx)).nontrivial.exists_ne x
    obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation hne.symm
    obtain ⟨f, hfs, hfc, hfd, -, hf1⟩ := exists_contDiff_tsupport_subset (n := ⊤)
      (s := O ∩ u) ((hO.inter hu).mem_nhds ⟨hx, hxu⟩)
    obtain ⟨X, hX, hlen, hne0⟩ := ih (O ∩ v) (hO.inter hv) ⟨y, hy, hyv⟩
    have hf0 : f ≠ 0 := fun h => by
      rw [h] at hf1
      simp at hf1
    refine ⟨⟨f :: X.1, ?_, ?_⟩, ?_, by simp [hlen], ?_⟩
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact ⟨hfd.of_le (by exact_mod_cast le_top), hfc⟩
      · exact X.2.1 g hg
    · refine List.pairwise_cons.2 ⟨fun g hg => ?_, X.2.2⟩
      exact (huv.mono Set.inter_subset_right Set.inter_subset_right).mono hfs (hX g hg)
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact hfs.trans Set.inter_subset_left
      · exact (hX g hg).trans Set.inter_subset_left
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact hf0
      · exact hne0 g hg
theorem isOpen_positiveSide (M : ReflectingHyperplane) : IsOpen M.positiveSide :=
  isOpen_lt continuous_const (by unfold dotProduct; fun_prop)
theorem positiveSide_nonempty (M : ReflectingHyperplane) : M.positiveSide.Nonempty := by
  have hn : M.normalVec ⬝ᵥ M.normalVec ≠ 0 :=
    Mirrors.dotProduct_self_ne_zero_of_mem M.normalVec_mem
  refine ⟨((M.offset + 1) / (M.normalVec ⬝ᵥ M.normalVec)) • M.normalVec, ?_⟩
  show M.normalVec ⬝ᵥ (((M.offset + 1) / (M.normalVec ⬝ᵥ M.normalVec)) • M.normalVec) > M.offset
  rw [dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hn]
  linarith
theorem exists_functional_eq_neg_one {Z : SepTuple} (hZ : Z ≠ SepTuple.nil) :
    ∃ σ : TupleFunctional, σ Z = -1 := by
  classical
  refine ⟨⟨fun T => if T = SepTuple.nil then 1 else if T = Z then -1 else 0, by simp⟩, ?_⟩
  show (if Z = SepTuple.nil then (1 : ℝ) else if Z = Z then -1 else 0) = -1
  simp [hZ]
theorem ne_nil_of_size_ne_zero {Z : SepTuple} (h : Z.1.length ≠ 0) : Z ≠ SepTuple.nil :=
    fun e => by
  rw [e] at h
  exact h rfl
theorem juxt_at_mirror (hF : BasicFacts.MainFacts) (hmf : Mirrors.UnitNormalAndLattice.Statement)
    (M : ReflectingHyperplane) (X Y : SepTuple) (hX : X ∈ supportedIn M.positiveSide)
    (hY : Y ∈ supportedIn M.positiveSide) :
    SepTuple.Composable (push M.reflect X) Y ∧
      (SepTuple.juxt (push M.reflect X) Y).1 = pushList M.reflect X.1 ++ Y.1 := by
  have hp := (hF.2.2.1 M X Y hX hY).2
  refine ⟨hp, ?_⟩
  rw [SepTuple.juxt_val hp, push_val hF.1 (isEuclidIsometry_reflect hmf M)]
theorem juxt_reflect_ne_nil (hF : BasicFacts.MainFacts)
    (hmf : Mirrors.UnitNormalAndLattice.Statement) (M : ReflectingHyperplane) {X : SepTuple}
    (hX : X ∈ supportedIn M.positiveSide) (hl : X.1.length = 1) :
    SepTuple.juxt (push M.reflect X) X ≠ SepTuple.nil := by
  refine ne_nil_of_size_ne_zero ?_
  rw [(juxt_at_mirror hF hmf M X X hX hX).2]
  simp [pushList, hl]
theorem exists_not_reflectionPositive_at (hF : BasicFacts.MainFacts)
    (hmf : Mirrors.UnitNormalAndLattice.Statement) (M : ReflectingHyperplane) :
    ∃ σ : TupleFunctional, ¬ σ.IsReflectionPositive M := by
  obtain ⟨X, hX, hl, -⟩ :=
    exists_sepTuple_in_open 1 _ (isOpen_positiveSide M) (positiveSide_nonempty M)
  obtain ⟨σ, hσ⟩ := exists_functional_eq_neg_one (juxt_reflect_ne_nil hF hmf M hX hl)
  refine ⟨σ, fun h => ?_⟩
  have h1 := h 1 le_rfl (fun _ => X) (fun _ => hX) (fun _ => 1)
  simp only [Finset.univ_unique, Finset.sum_singleton, hσ] at h1
  have h2 : (0 : ℂ) ≤ -1 := by simpa using h1
  have h3 := (Complex.le_def.1 h2).1
  norm_num at h3
theorem spanExtension_formalMul_eq (σ : TupleFunctional) (G G' : FormalSpan) :
    σ.spanExtension (formalMul G G') =
      ∑ Z ∈ G.support, ∑ Y ∈ G'.support, G Z * G' Y * (σ (SepTuple.juxt Z Y) : ℂ) := by
  have hexp : ∀ H : FormalSpan, ∑ Z ∈ H.support, H Z • basisVec Z = H := fun H => by
    conv_rhs => rw [← Finsupp.sum_single H]
    refine Finset.sum_congr rfl fun Z _ => ?_
    simp [basisVec]
  have h := formalMul_sum G.support G'.support (fun Z => G Z) (fun Y => G' Y)
    (fun Z => Z) (fun Y => Y)
  rw [hexp G, hexp G'] at h
  rw [h]
  simp only [map_sum, map_smul, TupleFunctional.spanExtension, linearExtend_basisVec, smul_eq_mul]
theorem mem_supportedIn_of_mem_support {O : Set AmbientSpace} {G : FormalSpan}
    (hG : G ∈ spanIn O) : ∀ Y ∈ G.support, Y ∈ supportedIn O := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.mem_supportedIn_of_mem_support <;> assumption
theorem exists_of_mem_support_pushSpan (r : AmbientSpace → AmbientSpace) (G : FormalSpan)
    {Z : SepTuple} (hZ : Z ∈ (pushSpan r G).support) : ∃ Y ∈ G.support, Z = push r Y := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.exists_of_mem_support_pushSpan <;> assumption
theorem mem_support_of_mem_support_conjugation (G : FormalSpan) {Z : SepTuple}
    (hZ : Z ∈ (conjugation G).support) : Z ∈ G.support := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.mem_support_of_mem_support_conjugation <;> assumption
theorem isEuclidIsometry_timeReflection
    (hmf : Mirrors.UnitNormalAndLattice.Statement) :
    IsEuclidIsometry TimeAxis.timeReflection := by
  rw [Mirrors.timeReflection_eq_axialReflection]
  exact isEuclidIsometry_reflect hmf _
theorem reflectConj_support_eq (hF : BasicFacts.MainFacts)
    (hmf : Mirrors.UnitNormalAndLattice.Statement) (F : PositiveSpan)
    (Z : SepTuple) (hZ : Z ∈ (reflectConj F).support) :
    ∃ X ∈ supportedIn TimeAxis.upperHalfSpace, Z.1 = pushList TimeAxis.timeReflection X.1 := by
  obtain ⟨Y, hY, rfl⟩ := exists_of_mem_support_pushSpan _ _ hZ
  exact ⟨Y, mem_supportedIn_of_mem_support F.2 Y (mem_support_of_mem_support_conjugation _ hY),
    push_val hF.1 (isEuclidIsometry_timeReflection hmf) Y⟩
theorem timeComponent_nonneg (t : ℝ≥0) (a : Fin 3 → ℝ) :
    0 ≤ ((t : ℝ) • timeBasisVec + embedSpatial a) TimeAxis.timeIdx := by
  have h : ((t : ℝ) • timeBasisVec + embedSpatial a) TimeAxis.timeIdx = (t : ℝ) := by
    simp [timeBasisVec, PeriodicLattice.coordVec, embedSpatial, TimeAxis.timeIdx]
  rw [h]
  exact t.2
theorem exists_far_vector (ρ : ℝ) : ∃ v : AmbientSpace, ρ ≤ euclidNormVec v := by
  obtain ⟨m, hm⟩ := exists_nat_ge ρ
  refine ⟨fun _ => (m : ℝ), hm.trans (Real.le_sqrt_of_sq_le ?_)⟩
  have h : 0 ≤ (m : ℝ) ^ 2 := by positivity
  simp
  linarith
theorem exists_reflectionForm_not_posSemidef (hF : BasicFacts.MainFacts)
    (hmf : Mirrors.UnitNormalAndLattice.Statement) :
    ∃ σ : TupleFunctional, ¬ IsPosSemidef (reflectionForm σ) := by
  let M : ReflectingHyperplane := Mirrors.axialHyperplane TimeAxis.timeIdx 0
  have hr : M.reflect = TimeAxis.timeReflection := Mirrors.timeReflection_eq_axialReflection.symm
  obtain ⟨X, hX, hl, -⟩ :=
    exists_sepTuple_in_open 1 _ (isOpen_positiveSide M) (positiveSide_nonempty M)
  have hX' : X ∈ supportedIn TimeAxis.upperHalfSpace := by
    rw [Mirrors.upperHalfSpace_eq_positiveSide]
    exact hX
  have hZ := juxt_reflect_ne_nil hF hmf M hX hl
  rw [hr] at hZ
  obtain ⟨σ, hσ⟩ := exists_functional_eq_neg_one hZ
  refine ⟨σ, fun h => ?_⟩
  let F : PositiveSpan := ⟨basisVec X, Submodule.subset_span ⟨⟨X, hX'⟩, rfl⟩⟩
  have hform : reflectionForm σ F F =
      ((σ (SepTuple.juxt (push TimeAxis.timeReflection X) X) : ℝ) : ℂ) := by
    have hrefl : reflectConj F = basisVec (push TimeAxis.timeReflection X) := by
      show pushSpan TimeAxis.timeReflection (conjugation (basisVec X)) = _
      rw [conjugation_basisVec]
      exact linearExtend_basisVec _ X
    show σ.spanExtension (formalMul (reflectConj F) (basisVec X)) = _
    rw [hrefl, formalMul_basisVec]
    exact linearExtend_basisVec _ _
  have h1 := h.nonneg F
  rw [hform, hσ] at h1
  have h2 := (Complex.le_def.1 h1).1
  norm_num at h2
theorem productsWellDefined (hF : BasicFacts.MainFacts)
    (hmf : Mirrors.UnitNormalAndLattice.Statement)
    (hT : PositiveTranslates.Statement) : ProductsWellDefined where
  at_mirror := juxt_at_mirror hF hmf
  exists_tuple_at_mirror M n :=
    exists_sepTuple_in_open n _ (isOpen_positiveSide M) (positiveSide_nonempty M)
  exists_not_reflectionPositive := exists_not_reflectionPositive_at hF hmf
  spanExtension_formalMul := spanExtension_formalMul_eq
  reflectConj_support F Z hZ := reflectConj_support_eq hF hmf F Z hZ
  at_form F F' Z hZ Y hY :=
    have hd := (hT F F' 0 (by simp)).2.1 Z hZ Y hY
    ⟨hd, SepTuple.juxt_val hd⟩
  at_matrixElement F F' t a Z hZ Y hY :=
    have hd := (hT F F' _ (timeComponent_nonneg t a)).2.2 Z hZ Y hY
    ⟨hd, SepTuple.juxt_val hd⟩
  exists_form_not_posSemidef := exists_reflectionForm_not_posSemidef hF hmf
  at_cluster X Y v hd := by
    rw [SepTuple.juxt_val hd, push_translate_val]
  exists_far := exists_far_vector
theorem preservesPositiveSpan_of_mem {r : AmbientSpace → AmbientSpace}
    (h : ∀ F : PositiveSpan, pushSpan r F.1 ∈ spanIn TimeAxis.upperHalfSpace) :
    PreservesPositiveSpan r := fun F => ⟨h F, fun σ hσ => by
  unfold spanClass
  exact dif_pos (h F)⟩
theorem isOpen_upperHalfSpace : IsOpen TimeAxis.upperHalfSpace :=
  isOpen_lt continuous_const (continuous_apply _)
theorem pushSpan_mem_of_preserves_time (hA : BasicFacts.PushSpanProperties)
    {r : AmbientSpace → AmbientSpace} (hr : IsEuclidIsometry r)
    (hs : Function.Surjective r) (ht : ∀ x, r x 3 = x 3) (F : PositiveSpan) :
    pushSpan r F.1 ∈ spanIn TimeAxis.upperHalfSpace := by
  have h := ((hA r r hr hr 0 0 F.1).2.2.2.2.1 TimeAxis.upperHalfSpace isOpen_upperHalfSpace).2
  have hi : r '' TimeAxis.upperHalfSpace = TimeAxis.upperHalfSpace := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show r x 3 > 0
      rw [ht]
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := hs y
      refine ⟨x, ?_, rfl⟩
      show x 3 > 0
      have h1 : r x 3 > 0 := hy
      rw [ht] at h1
      exact h1
  rw [hi] at h
  have hm := Submodule.mem_map_of_mem (f := pushSpan r) F.2
  rwa [h] at hm
theorem stabilizer_preserves_time (w : TorusSymmetries.timeVecStabilizer) (x : AmbientSpace) :
    w.1.1 x 3 = x 3 := by
  obtain ⟨π, ε, hε, h⟩ := (TorusTransport.mem_hyperoctahedral_iff w.1.1).1 w.1.2
  have hw : w.1.1 TimeAxisSymbols.timeAxisVec = TimeAxisSymbols.timeAxisVec := w.2
  have h3 := h TimeAxisSymbols.timeAxisVec 3
  rw [hw] at h3
  have e3 : TimeAxisSymbols.timeAxisVec 3 = 1 := by
    show (Pi.single (3 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 3 = 1
    simp
  have hπ : π 3 = 3 := by
    by_contra hne
    have h0 : TimeAxisSymbols.timeAxisVec (π 3) = 0 := by
      show (Pi.single (3 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) (π 3) = 0
      exact Pi.single_eq_of_ne hne _
    rw [h0, e3] at h3
    rcases hε 3 with e | e <;> rw [e] at h3 <;> norm_num at h3
  rw [hπ, e3] at h3
  have hε1 : ε 3 = 1 := by linarith
  have := h x 3
  rw [hπ, hε1, one_mul] at this
  exact this
theorem rotation_preserves_time (R : Orthogonal.orthogonalGroupThree) (x : AmbientSpace) :
    rotationMap (Orthogonal.embedOrthogonal R) x 3 = x 3 := by
  have hx : x = Orthogonal.spacetimePoint (fun i : Fin 3 => x i.castSucc) (x (Fin.last 3)) := by
    funext μ
    refine Fin.lastCases ?_ (fun i => ?_) μ
    · rw [Orthogonal.spacetimePoint_last]
    · rw [Orthogonal.spacetimePoint_castSucc]
  have h := Orthogonal.embedOrthogonal_mulVec R (fun i : Fin 3 => x i.castSucc) (x (Fin.last 3))
  rw [← hx] at h
  have h3 : rotationMap (Orthogonal.embedOrthogonal R) x =
      (Orthogonal.embedOrthogonal R).1.mulVec x := by
    funext μ
    simp [rotationMap, LimitTheorem.ofOrthogonal, Motions.RigidMotion.toFun]
  rw [h3, h]
  show Orthogonal.spacetimePoint _ _ (Fin.last 3) = x (Fin.last 3)
  rw [Orthogonal.spacetimePoint_last]
theorem classesWellDefined (hm : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine)
    (hF : BasicFacts.MainFacts) (hT : PositiveTranslates.Statement) :
    ClassesWellDefined where
  timeShift t := preservesPositiveSpan_of_mem fun F => (hT F F _ (by
    have h := timeComponent_nonneg t 0
    have h0 : embedSpatial 0 = 0 := by
      funext μ
      fin_cases μ <;> simp [embedSpatial]
    rwa [h0, add_zero] at h)).1
  spatialShift a := preservesPositiveSpan_of_mem fun F => (hT F F _ (by
    simp [embedSpatial, TimeAxis.timeIdx])).1
  timeVecStabilizer w := preservesPositiveSpan_of_mem fun F =>
    pushSpan_mem_of_preserves_time hF.2.2.2.2.1 (isEuclidIsometry_hyperoctahedral w.1)
      w.1.1.surjective (stabilizer_preserves_time w) F
  spatialRotation R := preservesPositiveSpan_of_mem fun F =>
    have hr := isEuclidIsometry_rigidMotion (ofOrthogonal (Orthogonal.embedOrthogonal R))
    pushSpan_mem_of_preserves_time hF.2.2.2.2.1 hr
      (fun y => ⟨_, (isometry_inverse_spec hm hr).1 y⟩) (rotation_preserves_time R) F
theorem shiftedComponents_eq (X : SepTuple) (P : List (SepTuple × AmbientSpace)) :
    shiftedComponents X P =
      X.1 ++ P.flatMap fun p : SepTuple × AmbientSpace => pushList (SeparatedTuples.translate p.2) p.1.1 := by
  simp only [shiftedComponents, push_translate_val]
theorem farProductsWellDefined : FarProductsWellDefined where
  shiftedJuxt_eq X P h := by
    rw [shiftedJuxt_val h, shiftedComponents_eq]
  iterLimitValue_eq s X Y vs h := by
    have hs : IsDisjointlySupported (shiftedComponents X (Y.zip vs)) := by
      simpa using h.2.2
    refine ⟨shiftedJuxt X (Y.zip vs), ?_, rfl⟩
    rw [shiftedJuxt_val hs, shiftedComponents_eq]
  eventually_mem_domain X Y k hk vs hvs :=
    eventually_cons_mem_iterLimitDomain X Y Set.univ hk hvs
  neBot := IsShiftRange.neBot (L := 1) le_rfl (Or.inl rfl)
  domain_last X Y := iterLimitDomain_length X Y Set.univ
theorem dyadicRescale_mem {n : ℕ} (i : ℕ) (X : SepTupleOfCard n) :
    TotalDensities.dyadicRescale i X.1 ∈
      TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) n := by apply _root_.YangMills.Construction.NonGaussianLimits.dyadicRescale_mem <;> assumption
theorem exists_nonzero_smooth_distinct (hS : ConfigSpace.CompactSupportTensorFacts)
    (hA : ConditionDomains.ArgumentsNotAllZero) (m : ℕ) :
    ∃ φ : TestSpaces.PointTuple (m + 1) → ℂ,
      φ ∈ TestSpaces.smoothCompactSupp (TestSpaces.distinctLocus (m + 1)) ∧ φ ≠ 0 := by
  obtain ⟨X, hX, -, hne⟩ := hA.exists_family (m + 1) (by omega)
  obtain ⟨-, h₁, h₂, h₃⟩ := ((hS (m + 1) (by omega)).2.2.2.2.1 X.1 X.2 hX).1
  exact ⟨_, ⟨h₁, h₂, h₃⟩, hne⟩
theorem premisesSatisfiable (hF : BasicFacts.MainFacts)
    (hS : ConfigSpace.CompactSupportTensorFacts)
    (hA : ConditionDomains.ArgumentsNotAllZero) : PremisesSatisfiable where
  exists_linear_combination A B f f' α α' X X' hX hX' :=
    ⟨⟨_, hF.2.1 A B f f' α α' (hX ▸ X.2) (hX' ▸ X'.2)⟩, rfl⟩
  exists_slot_combination n i b b' X X' h :=
    ⟨⟨_, TestSpaces.update_linComb_mem_disjointSupportTuples i b b' X X' h⟩, by simp,
      fun j hj => by simp [Function.update_of_ne hj]⟩
  exists_permuted n X ς :=
    ⟨⟨fun i => X.1 (ς i), fun i => X.2.1 (ς i), fun _ _ h => X.2.2 (ς.injective.ne h)⟩, rfl⟩
  exists_dilates n X := ⟨fun i => ⟨_, dyadicRescale_mem i X⟩, fun _ => rfl⟩
  exists_nonzero_smooth := exists_nonzero_smooth_distinct hS hA
  exists_nonzero_testFn m := by
    obtain ⟨φ, hφ, hne⟩ := exists_nonzero_smooth_distinct hS hA m
    have he : offDiagonal (m + 1) = TestSpaces.distinctLocus (m + 1) := by
      simp [offDiagonal, TestSpaces.diagonalLocus, TestSpaces.distinctLocus]
    exact ⟨⟨φ, he ▸ hφ⟩, hne⟩
  posSemidef_of_reconstruction σ h := by
    obtain ⟨-, -, h, -⟩ := h
    exact h
theorem nonvacuityStatement_holds (hF : BasicFacts.MainFacts)
    (hmf : Mirrors.UnitNormalAndLattice.Statement)
    (hT : PositiveTranslates.Statement)
    (hM : Tower.OrthogonalMotions.Classification)
    (hS : ConfigSpace.CompactSupportTensorFacts)
    (hA : ConditionDomains.ArgumentsNotAllZero) : NonvacuityStatement :=
  ⟨actionsWellDefined hM.2.1 hF.1 hmf, productsWellDefined hF hmf hT,
    classesWellDefined hM.2.1 hF hT, farProductsWellDefined,
    premisesSatisfiable hF hS hA, hT⟩
end YangMills.Construction.ConditionDefaults
end

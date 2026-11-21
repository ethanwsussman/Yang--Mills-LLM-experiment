import YangMills.Construction.Continuum.FreeSlabInsertionFormAndPulledDownNorm
import YangMills.Construction.ReflectionPositivity.ComplementsToTheReconstructionProof
import YangMills.Construction.SystemsWithFiveBounds.ConditionsAtFixedConstantsProof
import YangMills.Construction.SystemsWithFiveBounds.ListOfTheReconstructionOfALimit
import Mathlib
set_option autoImplicit false
section
noncomputable section
open Filter MeasureTheory Topology
open scoped ComplexOrder ENNReal InnerProductSpace NNReal
namespace YangMills.Construction.WindowLimits
section ClassesOfTuples
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass posTupleVec)
open SeparatedTuples ReflectionPositivity.TupleForm HilbertSpaceBasics
variable (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
private theorem reflectionForm_posTupleVec (X Y : supportedIn TimeAxis.upperHalfSpace) :
    reflectionForm σ (posTupleVec X) (posTupleVec Y) =
      (σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) Y.1) : ℂ) := by apply _root_.YangMills.SharedProofs.p11521 <;> assumption
private theorem inner_posClass (F G : PositiveSpan) :
    ⟪posClass σ h F, posClass σ h G⟫_ℂ = reflectionForm σ F G :=
  UniformSpace.Completion.inner_coe (𝕜 := ℂ) (E := FormSpace (reflectionForm σ) h) F G
private theorem norm_sub_posClass_sq (X Y : supportedIn TimeAxis.upperHalfSpace) :
    ‖posClass σ h (posTupleVec X) - posClass σ h (posTupleVec Y)‖ ^ 2 =
      (σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) X.1) -
          σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) Y.1)) +
        (σ (SepTuple.juxt (push TimeAxis.timeReflection Y.1) Y.1) -
          σ (SepTuple.juxt (push TimeAxis.timeReflection Y.1) X.1)) := by
  have e : ((‖posClass σ h (posTupleVec X) - posClass σ h (posTupleVec Y)‖ ^ 2 : ℝ) : ℂ) =
      (((σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) X.1) -
          σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) Y.1)) +
        (σ (SepTuple.juxt (push TimeAxis.timeReflection Y.1) Y.1) -
          σ (SepTuple.juxt (push TimeAxis.timeReflection Y.1) X.1)) : ℝ) : ℂ) := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
      (posClass σ h (posTupleVec X) - posClass σ h (posTupleVec Y))
    push_cast at this ⊢
    refine Eq.trans this.symm ?_
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    simp only [inner_posClass, reflectionForm_posTupleVec]
    ring
  exact_mod_cast e
private theorem separableSpace_of_countable_dense_classes (T : Set (supportedIn TimeAxis.upperHalfSpace))
    (hT : T.Countable)
    (hd : ∀ X : supportedIn TimeAxis.upperHalfSpace, posClass σ h (posTupleVec X) ∈
      closure ((fun Y => posClass σ h (posTupleVec Y)) '' T)) :
    TopologicalSpace.SeparableSpace (PhysicalSpace σ h) := by
  set S : Set (PhysicalSpace σ h) := (fun Y => posClass σ h (posTupleVec Y)) '' T with hS
  have hSc : S.Countable := hT.image _
  have hsep : TopologicalSpace.IsSeparable (Submodule.span ℂ S : Set (PhysicalSpace σ h)) :=
    hSc.isSeparable.span
  set P : Submodule ℂ (PhysicalSpace σ h) := (Submodule.span ℂ S).topologicalClosure with hP
  have hPsep : TopologicalSpace.IsSeparable (P : Set (PhysicalSpace σ h)) := hsep.closure
  have hmem : ∀ F : PositiveSpan, posClass σ h F ∈ P := by
    rintro ⟨G, hG⟩
    induction hG using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨X, rfl⟩ := hx
      exact closure_mono Submodule.subset_span (hd X)
    | zero =>
      change posClass σ h (0 : PositiveSpan) ∈ P
      rw [map_zero]
      exact P.zero_mem
    | add x y hx hy ihx ihy =>
      have := P.add_mem ihx ihy
      rwa [← map_add] at this
    | smul a x hx ih =>
      have := P.smul_mem a ih
      rwa [← map_smul] at this
  have hdense : (P : Set (PhysicalSpace σ h)) = Set.univ := by
    have hcl : IsClosed (P : Set (PhysicalSpace σ h)) := Submodule.isClosed_topologicalClosure _
    have hr : DenseRange (posClass σ h : PositiveSpan → PhysicalSpace σ h) :=
      UniformSpace.Completion.denseRange_coe (α := FormSpace (reflectionForm σ) h)
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hr.closure_range]
    exact closure_minimal (Set.range_subset_iff.2 hmem) hcl
  rw [hdense] at hPsep
  exact TopologicalSpace.isSeparable_univ_iff.1 hPsep
end ClassesOfTuples
section Neighbourhoods
open Metric
open InfiniteLattice (AmbientSpace)
open TorusMetric TimeAxis
private theorem exists_separated_open_nhds {k : ℕ} (K : Fin k → Set AmbientSpace) (hc : ∀ i, IsCompact (K i))
    (hd : ∀ i l, i ≠ l → Disjoint (K i) (K l)) (hp : ∀ i, K i ⊆ upperHalfSpace) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∃ O : Fin k → Set AmbientSpace, (∀ i, IsOpen (O i)) ∧ (∀ i, K i ⊆ O i) ∧
      (∀ i, ∀ x ∈ O i, δ ≤ x 3) ∧
      (∀ i l, i ≠ l → ∀ x ∈ O i, ∀ y ∈ O l, δ ≤ euclidNormVec (x - y)) ∧
      ∀ i, ∀ x ∈ O i, euclidNormVec x ≤ R := by
  have hopen : IsOpen (upperHalfSpace : Set AmbientSpace) :=
    isOpen_lt continuous_const (continuous_apply timeIdx)
  have e₁ : ∀ i l, ∀ᶠ ε in 𝓝[>] (0 : ℝ), i ≠ l → Disjoint (thickening ε (K i)) (thickening ε (K l)) := by
    intro i l
    by_cases hil : i = l
    · exact Eventually.of_forall fun _ h => absurd hil h
    · obtain ⟨δ, hδ, hdis⟩ := (hd i l hil).exists_thickenings (hc i) (hc l).isClosed
      filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε _
      exact hdis.mono (thickening_mono hε.2.le _) (thickening_mono hε.2.le _)
  have e₂ : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ), thickening ε (K i) ⊆ upperHalfSpace := by
    intro i
    obtain ⟨δ, hδ, hsub⟩ := (hc i).exists_thickening_subset_open hopen (hp i)
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    exact (thickening_mono hε.2.le _).trans hsub
  have e₃ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, h₁, h₂, hε⟩ := ((eventually_all.2 fun i => eventually_all.2 (e₁ i)).and
    ((eventually_all.2 e₂).and e₃)).exists
  have hδ : 0 < ε / 2 := half_pos hε
  have hb : Bornology.IsBounded (⋃ i, thickening (ε / 2) (K i)) :=
    Bornology.isBounded_iUnion.2 fun i => (hc i).isBounded.thickening
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  have hC' : ∀ i, ∀ x ∈ thickening (ε / 2) (K i), euclidNormVec x ≤ 2 * |C| + 1 := by
    intro i x hx
    have hn := hC x (Set.mem_iUnion.2 ⟨i, hx⟩)
    have hcoord : ∀ μ, x μ ^ 2 ≤ |C| ^ 2 := fun μ => by
      rw [← sq_abs (x μ)]
      have : |x μ| ≤ |C| := ((norm_le_pi_norm x μ).trans hn).trans (le_abs_self C)
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [Fin.sum_univ_four]
    nlinarith [hcoord 0, hcoord 1, hcoord 2, hcoord 3, abs_nonneg C]
  refine ⟨ε / 2, 2 * |C| + 1, hδ, by positivity, fun i => thickening (ε / 2) (K i),
    fun i => isOpen_thickening, fun i => self_subset_thickening hδ _, ?_, ?_, hC'⟩
  · intro i x hx
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.1 hx
    set y : AmbientSpace := Function.update x 3 (x 3 - ε / 2) with hy
    have hyx : dist y x ≤ ε / 2 := by
      refine (dist_pi_le_iff hδ.le).2 fun μ => ?_
      by_cases hμ : μ = 3
      · subst hμ
        simp [hy, abs_of_pos hε]
      · simp [hy, Function.update_of_ne hμ, hδ.le]
    have hyt : y ∈ thickening ε (K i) :=
      mem_thickening_iff.2 ⟨z, hz, by linarith [dist_triangle y x z]⟩
    have hpos : 0 < y 3 := h₂ i hyt
    simp [hy] at hpos
    linarith
  · intro i l hil x hx y hy
    by_contra hlt
    rw [not_le] at hlt
    have hxy : dist x y < ε / 2 := (dist_pi_lt_iff hδ).2 fun μ => by
      rw [Real.dist_eq]
      exact (abs_apply_le_euclidNormVec (x - y) μ).trans_lt hlt
    obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.1 hy
    obtain ⟨w, hw, hxw⟩ := mem_thickening_iff.1 hx
    have a₁ : x ∈ thickening ε (K i) := mem_thickening_iff.2 ⟨w, hw, by linarith⟩
    have a₂ : x ∈ thickening ε (K l) := mem_thickening_iff.2 ⟨z, hz, by linarith [dist_triangle x y z]⟩
    exact Set.disjoint_left.1 (h₁ i l hil) a₁ a₂
end Neighbourhoods
section SeparabilityOfThePhysicalSpace
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass posTupleVec)
open TestFunctions TorusMetric
open SeparatedTuples ReflectionPositivity.TupleForm HilbertSpaceBasics
open TimeAxis (timeReflection upperHalfSpace)
open InfiniteLattice (AmbientSpace)
private theorem involutive_timeReflection : Function.Involutive timeReflection := by apply _root_.YangMills.Construction.ReflectionPositivity.LimitContraction.timeReflection_involutive <;> assumption
private theorem continuous_timeReflection_map : Continuous timeReflection := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.continuous_timeReflection <;> assumption
private def timeReflectionHomeomorph : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toFun := timeReflection
  invFun := timeReflection
  left_inv := involutive_timeReflection
  right_inv := involutive_timeReflection
  continuous_toFun := continuous_timeReflection_map
  continuous_invFun := continuous_timeReflection_map
private theorem tsupport_comp_timeReflection (f : RealValued) :
    tsupport (f ∘ timeReflection) = timeReflection ⁻¹' tsupport f :=
  tsupport_comp_eq_preimage f timeReflectionHomeomorph
private theorem sharpNormR4_comp_timeReflection (M : ℝ) (f : RealValued) :
    sharpNormR4 M (f ∘ timeReflection) = sharpNormR4 M f := by
  have e₁ : uniformNorm (f ∘ timeReflection) = uniformNorm f :=
    involutive_timeReflection.surjective.iSup_comp fun x => ‖f x‖
  have hd : ∀ x y, euclidDistR4 (timeReflection x) (timeReflection y) = euclidDistR4 x y := fun x y => by
    simp only [euclidDistR4, euclidNormVec, Fin.sum_univ_four, timeReflection, Pi.sub_apply]
    congr 1
    simp
    ring
  have e₂ : lipConstR4 (f ∘ timeReflection) = lipConstR4 f := by
    unfold lipConstR4 bestLipschitzConstant
    congr 1
    ext C
    refine and_congr_right fun _ => ⟨fun h x y => ?_, fun h x y => ?_⟩
    · have := h (timeReflection x) (timeReflection y)
      simpa [involutive_timeReflection x, involutive_timeReflection y, hd] using this
    · simpa [hd] using h (timeReflection x) (timeReflection y)
  simp only [sharpNormR4, e₁, e₂]
private theorem sharpNormR4_zero (M : ℝ) : sharpNormR4 M (0 : RealValued) = 0 := by
  have h₁ : uniformNorm (0 : RealValued) = 0 := by simp [uniformNorm]
  have h₂ : lipConstR4 (0 : RealValued) = 0 := by
    unfold lipConstR4 bestLipschitzConstant
    refine le_antisymm (csInf_le ⟨0, fun _ h => h.1⟩ ⟨le_rfl, fun x y => by simp⟩)
      (le_csInf ⟨0, le_rfl, fun x y => by simp⟩ fun _ h => h.1)
  simp [sharpNormR4, h₁, h₂]
abbrev _root_.YangMills.DeltaSharedProofs.p501833 := @sharpNormR4_zero
private theorem componentAt_of_ofFn {W : SepTuple} {m : ℕ} {f : Fin m → RealValued} (hW : W.1 = List.ofFn f)
    (i : Fin m) : W.componentAt i = f i := by
  have hi : (i : ℕ) < (List.ofFn f).length := by simp
  simp only [SepTuple.componentAt, hW]
  rw [List.getD_eq_getElem _ _ hi]
  simp
private theorem juxt_push_timeReflection_val {A B : SepTuple} {k : ℕ} (a b : Fin k → RealValued)
    (hA : A.1 = List.ofFn a) (hB : B.1 = List.ofFn b) (hA' : A ∈ supportedIn upperHalfSpace)
    (hB' : B ∈ supportedIn upperHalfSpace) :
    (SepTuple.juxt (push timeReflection A) B).1 =
      List.ofFn (Fin.append (fun i => a i ∘ timeReflection) b) := by apply _root_.YangMills.SharedProofs.p44178 <;> assumption
private theorem isCompact_preimage_timeReflection {C : Set AmbientSpace} (hC : IsCompact C) :
    IsCompact (timeReflection ⁻¹' C) :=
  timeReflectionHomeomorph.isCompact_preimage.2 hC
private theorem tendsto_juxt_push_timeReflection {σ : TupleFunctional} (hc : σ.IsAdmissiblyContinuous)
    (hS : ∀ f : RealValued, IsC1c f → c1NormR4 f ≤ sharpNormR4 1 f)
    {k : ℕ} {C : Fin k → Set AmbientSpace} (hC : ∀ i, IsCompact (C i))
    (hd : ∀ i l, i ≠ l → Disjoint (C i) (C l)) (hp : ∀ i, C i ⊆ upperHalfSpace)
    {X : SepTuple} {g : Fin k → RealValued} (hX : X.1 = List.ofFn g) (hX' : X ∈ supportedIn upperHalfSpace)
    (sg : ∀ i, tsupport (g i) ⊆ C i)
    {A B : ℕ → SepTuple} {a b : ℕ → Fin k → RealValued} (hA : ∀ n, (A n).1 = List.ofFn (a n))
    (hB : ∀ n, (B n).1 = List.ofFn (b n)) (hA' : ∀ n, A n ∈ supportedIn upperHalfSpace)
    (hB' : ∀ n, B n ∈ supportedIn upperHalfSpace) (sa : ∀ n i, tsupport (a n i) ⊆ C i)
    (sb : ∀ n i, tsupport (b n i) ⊆ C i)
    (ha : ∀ i, Tendsto (fun n => sharpNormR4 1 (a n i - g i)) atTop (𝓝 0))
    (hb : ∀ i, Tendsto (fun n => sharpNormR4 1 (b n i - g i)) atTop (𝓝 0)) :
    Tendsto (fun n => σ (SepTuple.juxt (push timeReflection (A n)) (B n))) atTop
      (𝓝 (σ (SepTuple.juxt (push timeReflection X) X))) := by
  set F : ℕ → Fin (k + k) → RealValued := fun n => Fin.append (fun i => a n i ∘ timeReflection) (b n) with hF
  set G : Fin (k + k) → RealValued := Fin.append (fun i => g i ∘ timeReflection) g with hG
  have hZn : ∀ n, (SepTuple.juxt (push timeReflection (A n)) (B n)).1 = List.ofFn (F n) := fun n =>
    juxt_push_timeReflection_val _ _ (hA n) (hB n) (hA' n) (hB' n)
  have hZ : (SepTuple.juxt (push timeReflection X) X).1 = List.ofFn G :=
    juxt_push_timeReflection_val _ _ hX hX hX' hX'
  have hlen : (SepTuple.juxt (push timeReflection X) X).size = k + k := by
    simp [SepTuple.size, hZ]
  set E : Fin (k + k) → Set AmbientSpace := Fin.append (fun i => timeReflection ⁻¹' C i) C with hE
  have hEc : ∀ j, IsCompact (E j) := by
    intro j
    induction j using Fin.addCases with
    | left i =>
      simp only [hE, Fin.append_left]
      exact isCompact_preimage_timeReflection (hC i)
    | right i =>
      simp only [hE, Fin.append_right]
      exact hC i
  have hEd : ∀ j l, j ≠ l → Disjoint (E j) (E l) := by
    have hmix : ∀ i l, Disjoint (timeReflection ⁻¹' C i) (C l) := fun i l => by
      refine Set.disjoint_left.2 fun x hx hx' => ?_
      have h₁ : 0 < timeReflection x 3 := hp i hx
      have h₂ : 0 < x 3 := hp l hx'
      simp [timeReflection] at h₁
      linarith
    intro j l hjl
    induction j using Fin.addCases with
    | left i =>
      induction l using Fin.addCases with
      | left i' =>
        simp only [hE, Fin.append_left]
        exact (hd i i' fun e => hjl (by rw [e])).preimage _
      | right i' =>
        simp only [hE, Fin.append_left, Fin.append_right]
        exact hmix i i'
    | right i =>
      induction l using Fin.addCases with
      | left i' =>
        simp only [hE, Fin.append_left, Fin.append_right]
        exact (hmix i' i).symm
      | right i' =>
        simp only [hE, Fin.append_right]
        exact hd i i' fun e => hjl (by rw [e])
  have hsF : ∀ n j, tsupport (F n j) ⊆ E j := by
    intro n j
    induction j using Fin.addCases with
    | left i =>
      simp only [hF, hE, Fin.append_left]
      rw [tsupport_comp_timeReflection]
      exact Set.preimage_mono (sa n i)
    | right i =>
      simp only [hF, hE, Fin.append_right]
      exact sb n i
  have hsG : ∀ j, tsupport (G j) ⊆ E j := by
    intro j
    induction j using Fin.addCases with
    | left i =>
      simp only [hG, hE, Fin.append_left]
      rw [tsupport_comp_timeReflection]
      exact Set.preimage_mono (sg i)
    | right i =>
      simp only [hG, hE, Fin.append_right]
      exact sg i
  have hFmem : ∀ n j, IsC1c (F n j) := fun n j =>
    (SepTuple.juxt (push timeReflection (A n)) (B n)).2.1 _
      (by rw [hZn]; exact (List.mem_ofFn' _ _).2 ⟨j, rfl⟩)
  have hGmem : ∀ j, IsC1c (G j) := fun j =>
    (SepTuple.juxt (push timeReflection X) X).2.1 _ (by rw [hZ]; exact (List.mem_ofFn' _ _).2 ⟨j, rfl⟩)
  have hdiff : ∀ j, Tendsto (fun n => c1NormR4 (F n j - G j)) atTop (𝓝 0) := by
    intro j
    have hnn : ∀ n, 0 ≤ c1NormR4 (F n j - G j) := fun n =>
      le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
    have hmemd : ∀ n, IsC1c (F n j - G j) := fun n =>
      ⟨(hFmem n j).1.sub (hGmem j).1, (hFmem n j).2.sub (hGmem j).2⟩
    refine squeeze_zero hnn (fun n => hS _ (hmemd n)) ?_
    induction j using Fin.addCases with
    | left i =>
      simp only [hF, hG, Fin.append_left]
      refine (ha i).congr fun n => ?_
      have e : (a n i ∘ timeReflection) - (g i ∘ timeReflection) = (a n i - g i) ∘ timeReflection := rfl
      rw [e, sharpNormR4_comp_timeReflection]
    | right i =>
      simp only [hF, hG, Fin.append_right]
      exact hb i
  refine hc 1 _ _ ⟨le_rfl, fun r _ => ?_, fun i => E (Fin.cast hlen i), fun i => hEc _, ?_, ?_, ?_⟩
  · simp [SepTuple.size, hZ, hZn]
  · intro i l hil
    exact hEd _ _ fun e => hil (Fin.cast_injective _ e)
  · intro r _ i
    have e₁ := componentAt_of_ofFn (hZn r) (Fin.cast hlen i)
    have e₂ := componentAt_of_ofFn hZ (Fin.cast hlen i)
    simp only [Fin.val_cast] at e₁ e₂
    rw [e₁, e₂]
    exact Set.union_subset (hsF r _) (hsG _)
  · intro i
    have e₂ := componentAt_of_ofFn hZ (Fin.cast hlen i)
    simp only [Fin.val_cast] at e₂
    refine (hdiff (Fin.cast hlen i)).congr fun n => ?_
    have e₁ := componentAt_of_ofFn (hZn n) (Fin.cast hlen i)
    simp only [Fin.val_cast] at e₁
    rw [e₁, e₂]
private theorem separableSpace_physicalSpace {σ : TupleFunctional} (hc : σ.IsAdmissiblyContinuous)
    (hfam : CanonicalDecomposition.SeparatingTuplesProperties.Claim)
    (hS : ∀ f : RealValued, IsC1c f → c1NormR4 f ≤ sharpNormR4 1 f)
    (s : Conventions.StandingParameters) (h : IsPosSemidef (reflectionForm σ)) :
    TopologicalSpace.SeparableSpace (PhysicalSpace σ h) := by
  have hM : (1 : ℝ) ≤ 1 := le_rfl
  set T : Set (supportedIn upperHalfSpace) :=
    {Y | (R4TupleForms.finTupleEquiv s).symm Y.1 ∈ CanonicalDecomposition.separatingTuples s} with hTdef
  have hT : T.Countable := (hfam s 1 hM).countable.preimage
    (f := fun Y : supportedIn upperHalfSpace => (R4TupleForms.finTupleEquiv s).symm Y.1)
    fun Y Y' e => Subtype.ext ((R4TupleForms.finTupleEquiv s).symm.injective e)
  have hTmem : ∀ Y : supportedIn upperHalfSpace, (R4TupleForms.finTupleEquiv s).symm Y.1 ∈
      CanonicalDecomposition.separatingTuples s → Y ∈ T := fun _ h => h
  refine separableSpace_of_countable_dense_classes _ h T hT fun X => ?_
  by_cases hk : X.1.1.length = 0
  · have hX : X.1 = SepTuple.nil := Subtype.ext (List.length_eq_zero_iff.1 hk)
    refine subset_closure ⟨X, hTmem X ?_, rfl⟩
    rw [hX]
    refine Or.inl ((Equiv.symm_apply_eq _).2 ?_)
    exact R4TupleForms.listOf_nilTuple.symm
  have hk1 : 1 ≤ X.1.1.length := Nat.pos_of_ne_zero hk
  set g : Fin X.1.1.length → RealValued := X.1.1.get with hgdef
  have hXg : X.1.1 = List.ofFn g := (List.ofFn_get _).symm
  have hg : ∀ i, g i ∈ X.1.1 := fun i => List.get_mem _ _
  have hdisj : ∀ i l, i ≠ l → Disjoint (tsupport (g i)) (tsupport (g l)) := by
    intro i l hil
    rcases lt_or_gt_of_ne hil with hlt | hlt
    · exact List.pairwise_iff_get.1 X.1.2.2 i l hlt
    · exact (List.pairwise_iff_get.1 X.1.2.2 l i hlt).symm
  obtain ⟨δ, R, hδ, hR, O, hOo, hKO, h₁, h₂, h₃⟩ := exists_separated_open_nhds (fun i => tsupport (g i))
    (fun i => (X.1.2.1 _ (hg i)).2) hdisj (fun i => X.2 _ (hg i))
  have hOo' : ∀ i, @IsOpen (Continuum.SeparatedFourTuples.EuclideanFour s) _ (O i) := fun i => by
    let P' : Set (Continuum.SeparatedFourTuples.EuclideanFour s) := O i
    have hcl : closure (P'ᶜ) = P'ᶜ :=
      (R4TupleForms.closure_pt_euclidean (s := s) ((O i)ᶜ)).trans (hOo i).isClosed_compl.closure_eq
    exact isClosed_compl_iff.1 (closure_eq_iff_isClosed.1 hcl)
  obtain ⟨Y, hYT, hYs, hYt⟩ := (hfam s 1 hM).approx ((R4TupleForms.finTupleEquiv s).symm X.1) hk1
    O hOo' (fun i => (R4TupleForms.tsupport_pt_euclidean (s := s) (g i)).le.trans (hKO i))
  set b : ℕ → Fin X.1.1.length → RealValued := fun n => (Y n).1 with hbdef
  have sY : ∀ n i, tsupport (b n i) ⊆ O i := fun n i =>
    (R4TupleForms.tsupport_pt_euclidean (s := s) (b n i)).ge.trans (hYs n i)
  set Yt : ℕ → SepTuple := fun n =>
    R4TupleForms.finTupleEquiv s (Continuum.SeparatedFourTuples.ofFixedLength (Y n)) with hYtdef
  have hYt1 : ∀ n, (Yt n).1 = List.ofFn (b n) := fun n => rfl
  have hpos : ∀ n, Yt n ∈ supportedIn upperHalfSpace := by
    intro n f hf
    rw [hYt1] at hf
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    intro x hx
    have := h₁ i x (sY n i hx)
    exact lt_of_lt_of_le hδ this
  set Yp : ℕ → supportedIn upperHalfSpace := fun n => ⟨Yt n, hpos n⟩ with hYpdef
  have hmemT : ∀ n, Yp n ∈ T := fun n => hTmem (Yp n) (by
    rw [show (Yp n).1 =
        R4TupleForms.finTupleEquiv s (Continuum.SeparatedFourTuples.ofFixedLength (Y n)) from rfl,
      Equiv.symm_apply_apply]
    exact hYT n)
  set C : Fin X.1.1.length → Set AmbientSpace := fun i => closure (O i) with hCdef
  have hcont_ve : Continuous (euclidNormVec : AmbientSpace → ℝ) := by
    unfold euclidNormVec
    fun_prop
  have hC3 : ∀ i, ∀ x ∈ C i, δ ≤ x 3 := fun i x hx =>
    closure_minimal (s := O i) (t := {x : AmbientSpace | δ ≤ x 3}) (h₁ i)
      (isClosed_le continuous_const (continuous_apply 3)) hx
  have hCb : ∀ i, ∀ x ∈ C i, euclidNormVec x ≤ R := fun i x hx =>
    closure_minimal (s := O i) (t := {x : AmbientSpace | euclidNormVec x ≤ R}) (h₃ i)
      (isClosed_le hcont_ve continuous_const) hx
  have hCc : ∀ i, IsCompact (C i) := fun i => by
    refine Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_
    refine (Metric.isBounded_iff_subset_closedBall (0 : AmbientSpace)).2 ⟨R, fun x hx => ?_⟩
    have hn : ‖x‖ ≤ euclidNormVec x := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun μ => ?_
      rw [Real.norm_eq_abs]
      exact abs_apply_le_euclidNormVec x μ
    simpa using hn.trans (hCb i x hx)
  have hCd : ∀ i l, i ≠ l → Disjoint (C i) (C l) := by
    intro i l hil
    have hsep : ∀ x ∈ C i, ∀ y ∈ C l, δ ≤ euclidNormVec (x - y) := by
      intro x hx y hy
      have step₁ : ∀ y' ∈ O l, δ ≤ euclidNormVec (x - y') := fun y' hy' =>
        closure_minimal (s := O i) (t := {x' : AmbientSpace | δ ≤ euclidNormVec (x' - y')})
          (fun x' hx' => h₂ i l hil x' hx' y' hy')
          (isClosed_le continuous_const (hcont_ve.comp (continuous_id.sub continuous_const))) hx
      exact closure_minimal (s := O l) (t := {y' : AmbientSpace | δ ≤ euclidNormVec (x - y')}) step₁
        (isClosed_le continuous_const (hcont_ve.comp (continuous_const.sub continuous_id))) hy
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    have := hsep x hx x hx'
    have e : euclidNormVec (x - x) = 0 := by simp [euclidNormVec]
    linarith
  have hCp : ∀ i, C i ⊆ upperHalfSpace := fun i x hx => lt_of_lt_of_le hδ (hC3 i x hx)
  have sYC : ∀ n i, tsupport (b n i) ⊆ C i := fun n i => (sY n i).trans subset_closure
  have sgC : ∀ i, tsupport (g i) ⊆ C i := fun i => (hKO i).trans subset_closure
  have hb0 : ∀ i, Tendsto (fun n => sharpNormR4 1 (b n i - g i)) atTop (𝓝 0) := hYt
  have hg0 : ∀ i, Tendsto (fun n : ℕ => sharpNormR4 1 (g i - g i)) atTop (𝓝 0) := fun i => by
    have e : sharpNormR4 1 (g i - g i) = 0 := by
      rw [sub_self]
      exact sharpNormR4_zero 1
    rw [e]
    exact tendsto_const_nhds
  have t₁ : Tendsto (fun n => σ (SepTuple.juxt (push timeReflection X.1) (Yt n))) atTop
      (𝓝 (σ (SepTuple.juxt (push timeReflection X.1) X.1))) :=
    tendsto_juxt_push_timeReflection hc hS hCc hCd hCp hXg X.2 sgC (A := fun _ => X.1) (B := Yt)
      (a := fun _ => g) (b := b) (fun _ => hXg) hYt1 (fun _ => X.2) hpos (fun _ => sgC) sYC hg0 hb0
  have t₂ : Tendsto (fun n => σ (SepTuple.juxt (push timeReflection (Yt n)) (Yt n))) atTop
      (𝓝 (σ (SepTuple.juxt (push timeReflection X.1) X.1))) :=
    tendsto_juxt_push_timeReflection hc hS hCc hCd hCp hXg X.2 sgC (A := Yt) (B := Yt)
      (a := b) (b := b) hYt1 hYt1 hpos hpos sYC sYC hb0 hb0
  have t₃ : Tendsto (fun n => σ (SepTuple.juxt (push timeReflection (Yt n)) X.1)) atTop
      (𝓝 (σ (SepTuple.juxt (push timeReflection X.1) X.1))) :=
    tendsto_juxt_push_timeReflection hc hS hCc hCd hCp hXg X.2 sgC (A := Yt) (B := fun _ => X.1)
      (a := b) (b := fun _ => g) hYt1 (fun _ => hXg) hpos (fun _ => X.2) sYC (fun _ => sgC) hb0 hg0
  have hsq : Tendsto (fun n => ‖posClass σ h (posTupleVec X) -
      posClass σ h (posTupleVec (Yp n))‖ ^ 2) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := σ (SepTuple.juxt (push timeReflection X.1) X.1))).sub t₁).add
      (t₂.sub t₃)
    simp only [sub_self, add_zero] at this
    exact this.congr fun n => (norm_sub_posClass_sq σ h X (Yp n)).symm
  refine mem_closure_of_tendsto (b := atTop)
    (f := fun n => posClass σ h (posTupleVec (Yp n))) ?_
    (Eventually.of_forall fun n => ⟨Yp n, hmemT n, rfl⟩)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs := hsq.sqrt
  simp only [Real.sqrt_zero] at hs
  refine hs.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _), norm_sub_rev]
abbrev _root_.YangMills.SharedProofs.p25811 := @separableSpace_physicalSpace
end SeparabilityOfThePhysicalSpace
section ReconstructionProperties
open Filter MeasureTheory InfiniteLattice
open SeparatedTuples hiding conjugation
open ReflectionPositivity.TupleForm SpectralTheory
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass spanClass spaceShift
  timeShift timeBasisVec vacuum)
open ReflectionPositivity.PairMeasureOperators (pairHamiltonian pairMomentum energyMomentumPair)
open ReflectionPositivity.ReconstructionComplements
open LimitConventions (SpaceVec octahedralGroup3 timeExtension)
open HilbertSpaceBasics (IsPosSemidef)
private def linearEquivOfHyperoctahedral (w : TorusTransport.hyperoctahedral) : AmbientSpace ≃ₗ[ℝ] AmbientSpace :=
  { TorusTransport.hyperoctahedralLinear w with
    invFun := w.1.symm
    left_inv := w.1.left_inv
    right_inv := w.1.right_inv }
private theorem exists_octahedral_of_stabilizer (hc : OctahedralFixesTime)
    (w : TorusSymmetries.timeVecStabilizer) :
    ∃ v ∈ octahedralGroup3, ⇑(timeExtension v) = ⇑w.1.1 := by
  have hmem : linearEquivOfHyperoctahedral w.1 ∈ InfiniteLattice.hyperoctahedralLinearGroup :=
    (LimitConventions.mem_hyperoctahedralLinearGroup_iff_toEquiv _).2 w.1.2
  have htime : linearEquivOfHyperoctahedral w.1 Continuum.AxisPreservingSymmetries.timeBasisVector =
      Continuum.AxisPreservingSymmetries.timeBasisVector := w.2
  obtain ⟨v, hv, e⟩ := (hc _).1 ⟨hmem, htime⟩
  exact ⟨v, hv, by rw [← e]; rfl⟩
abbrev _root_.YangMills.SharedProofs.p12663 := @exists_octahedral_of_stabilizer
private def octahedralOf (hc : OctahedralFixesTime) (w : TorusSymmetries.timeVecStabilizer) :
    SpaceVec ≃ₗ[ℝ] SpaceVec :=
  (exists_octahedral_of_stabilizer hc w).choose
private theorem octahedralOf_mem (hc : OctahedralFixesTime) (w : TorusSymmetries.timeVecStabilizer) :
    octahedralOf hc w ∈ octahedralGroup3 :=
  (exists_octahedral_of_stabilizer hc w).choose_spec.1
private theorem coe_timeExtension_octahedralOf (hc : OctahedralFixesTime)
    (w : TorusSymmetries.timeVecStabilizer) :
    ⇑(timeExtension (octahedralOf hc w)) = ⇑w.1.1 :=
  (exists_octahedral_of_stabilizer hc w).choose_spec.2
private theorem isEuclidIsometry_of_hyperoctahedral (w : TorusTransport.hyperoctahedral) :
    IsEuclidIsometry ⇑w.1 := by apply _root_.YangMills.Construction.ConditionDefaults.isEuclidIsometry_hyperoctahedral <;> assumption
private theorem invMap_eq_symm (g : AmbientSpace ≃ AmbientSpace) : invMap ⇑g = ⇑g.symm := by
  funext x
  have hx : g (g.symm x) = x := g.apply_symm_apply x
  calc invMap g x = invMap g (g (g.symm x)) := by rw [hx]
    _ = g.symm x := Function.leftInverse_invFun g.injective _
private theorem timeComponent_timeExtension_symm (v : SpaceVec ≃ₗ[ℝ] SpaceVec) (x : AmbientSpace) :
    TimeAxis.timeComponent ((timeExtension v).symm x) = TimeAxis.timeComponent x := by
  have e : (timeExtension v).symm x =
      LimitConventions.mkPoint (v.symm (LimitConventions.spacePart x))
        (TimeAxis.timeComponent x) := rfl
  rw [e]
  simp
private theorem pushSpan_timeExtension_mem (v : SpaceVec ≃ₗ[ℝ] SpaceVec) {G : FormalSpan}
    (hG : G ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan ⇑(timeExtension v) G ∈ spanIn TimeAxis.upperHalfSpace := by
  refine SlabInsertion.pushSpan_mem_spanIn (ρ := ⇑(timeExtension v).symm)
    (invMap_eq_symm (timeExtension v).toEquiv)
    ((timeExtension v).symm.toLinearMap.continuous_of_finiteDimensional)
    (fun x hx => ?_) hG
  change TimeAxis.timeComponent ((timeExtension v).symm x) > 0 at hx
  rw [timeComponent_timeExtension_symm] at hx
  exact hx
abbrev _root_.YangMills.SharedProofs.p61114 := @pushSpan_timeExtension_mem
private theorem pushSpan_translate_mem {v : AmbientSpace} (hv : 0 ≤ v TimeAxis.timeIdx) {G : FormalSpan}
    (hG : G ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan (translate v) G ∈ spanIn TimeAxis.upperHalfSpace := by
  have hr : invMap (translate v) = fun x => x - v := by
    have := invMap_eq_symm (Equiv.addRight v)
    exact this
  refine SlabInsertion.pushSpan_mem_spanIn hr (continuous_id.sub continuous_const)
    (fun x hx => ?_) hG
  change TimeAxis.timeComponent (x - v) > 0 at hx
  change TimeAxis.timeComponent x > 0
  have e : TimeAxis.timeComponent (x - v) = TimeAxis.timeComponent x - v TimeAxis.timeIdx := rfl
  rw [e] at hx
  linarith
abbrev _root_.YangMills.SharedProofs.p76588 := @pushSpan_translate_mem
section Stabilizer
variable {σ : TupleFunctional} {h : IsPosSemidef (reflectionForm σ)}
private theorem clm_ext_on_posClass (hC : HilbertSpaceFacts.CompletionProperties)
    {A B : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
    (hAB : ∀ F, A (posClass σ h F) = B (posClass σ h F)) : A = B := by
  have hd : Dense (Set.range (posClass σ h)) := by
    have := (hC _ (reflectionForm σ) h).2.2.2.1
    rwa [LinearMap.coe_range] at this
  refine ContinuousLinearMap.ext fun ψ => ?_
  refine congrFun (Continuous.ext_on hd A.continuous B.continuous ?_) ψ
  rintro _ ⟨F, rfl⟩
  exact hAB F
abbrev _root_.YangMills.SharedProofs.p22624 := @clm_ext_on_posClass
private theorem spanClass_of_mem {G : FormalSpan}
    (hG : G ∈ spanIn TimeAxis.upperHalfSpace) :
    spanClass σ h G = posClass σ h ⟨G, hG⟩ := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.spanClass_of_mem <;> assumption
variable (hc : OctahedralFixesTime)
  (hpart : ∀ w ∈ octahedralGroup3, UnitaryClaim σ h w ∧ IntertwiningClaim σ h w)
private def stabilizerOp (w : TorusSymmetries.timeVecStabilizer) :
    PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h :=
  octahedralUnitaryCLM σ h (octahedralOf hc w)
include hpart in
private theorem stabilizerOp_acts (w : TorusSymmetries.timeVecStabilizer) :
    LimitTheorem.ActsOnClasses σ h w.1.1 (stabilizerOp (σ := σ) (h := h) hc w) := by
  intro F
  have h₁ := (hpart _ (octahedralOf_mem hc w)).1.2 F
  rw [coe_timeExtension_octahedralOf hc w] at h₁
  exact h₁
include hc in
private theorem pushSpan_stabilizer_mem (w : TorusSymmetries.timeVecStabilizer)
    {G : FormalSpan} (hG : G ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan ⇑w.1.1 G ∈ spanIn TimeAxis.upperHalfSpace := by
  rw [← coe_timeExtension_octahedralOf hc w]
  exact pushSpan_timeExtension_mem _ hG
include hpart in
private theorem stabilizerOp_posClass (w : TorusSymmetries.timeVecStabilizer)
    (F : PositiveSpan) :
    stabilizerOp (σ := σ) (h := h) hc w (posClass σ h F) =
      posClass σ h ⟨_, pushSpan_stabilizer_mem hc w F.2⟩ := by
  rw [stabilizerOp_acts hc hpart w F]
  exact spanClass_of_mem _
private theorem stabilizer_comp_translate (w : TorusSymmetries.timeVecStabilizer) (t : ℝ) :
    ⇑w.1.1 ∘ SeparatedTuples.translate (t • timeBasisVec) =
      SeparatedTuples.translate (t • timeBasisVec) ∘ ⇑w.1.1 := by
  have hw : w.1.1 timeBasisVec = timeBasisVec := w.2
  funext x
  change w.1.1 (x + t • timeBasisVec) = w.1.1 x + t • timeBasisVec
  have h₁ := (TorusTransport.hyperoctahedralLinear w.1).map_add x (t • timeBasisVec)
  have h₂ := (TorusTransport.hyperoctahedralLinear w.1).map_smul t timeBasisVec
  have h₃ : w.1.1 (x + t • timeBasisVec) = w.1.1 x + w.1.1 (t • timeBasisVec) := h₁
  have h₄ : w.1.1 (t • timeBasisVec) = t • w.1.1 timeBasisVec := h₂
  rw [h₃, h₄, hw]
abbrev _root_.YangMills.SharedProofs.p62730 := @stabilizer_comp_translate
include hpart in
private theorem stabilizerOp_isStabilizerRep
    (hC : HilbertSpaceFacts.CompletionProperties)
    (hA : BasicFacts.PushSpanProperties)
    (hTime : ReflectionPositivity.Reconstruction.IsTimeShiftFamily σ h (timeShift σ h)) :
    LimitTheorem.IsStabilizerRep σ h (stabilizerOp (σ := σ) (h := h) hc) := by
  refine ⟨fun w => ⟨stabilizerOp_acts hc hpart w, fun U' hU' => ?_⟩,
    ⟨fun w => ⟨fun ψ => ?_, ?_⟩, fun w w' => ?_⟩,
    fun w => (hpart _ (octahedralOf_mem hc w)).2.1, fun w t => ?_⟩
  · exact clm_ext_on_posClass hC fun F => by rw [hU' F, stabilizerOp_acts hc hpart w F]
  · exact (octahedralUnitary σ h (octahedralOf hc w)).norm_map ψ
  · exact (octahedralUnitary σ h (octahedralOf hc w)).surjective
  · refine clm_ext_on_posClass hC fun F => ?_
    change stabilizerOp hc w (stabilizerOp hc w' (posClass σ h F)) = _
    rw [stabilizerOp_posClass hc hpart w' F, stabilizerOp_posClass hc hpart w,
      stabilizerOp_posClass hc hpart (w * w') F]
    refine congrArg _ (Subtype.ext ?_)
    exact ((hA _ _ (isEuclidIsometry_of_hyperoctahedral w.1) (isEuclidIsometry_of_hyperoctahedral w'.1)
      0 0 F.1).1).symm
  · have ht : 0 ≤ ((t : ℝ) • timeBasisVec) TimeAxis.timeIdx := by
      have : ((t : ℝ) • timeBasisVec) TimeAxis.timeIdx = (t : ℝ) := by
        simp [timeBasisVec, PeriodicLattice.coordVec]
      rw [this]
      exact t.2
    have hτ := isEuclidIsometry_translate ((t : ℝ) • timeBasisVec)
    refine clm_ext_on_posClass hC fun F => ?_
    change stabilizerOp hc w (timeShift σ h t (posClass σ h F)) =
      timeShift σ h t (stabilizerOp hc w (posClass σ h F))
    rw [hTime t F, spanClass_of_mem (pushSpan_translate_mem ht F.2),
      stabilizerOp_posClass hc hpart w, stabilizerOp_posClass hc hpart w F, hTime t,
      spanClass_of_mem (pushSpan_translate_mem ht (pushSpan_stabilizer_mem hc w F.2))]
    refine congrArg _ (Subtype.ext ?_)
    change pushSpan ⇑w.1.1 (pushSpan (translate ((t : ℝ) • timeBasisVec)) F.1) =
      pushSpan (translate ((t : ℝ) • timeBasisVec)) (pushSpan ⇑w.1.1 F.1)
    rw [← (hA _ _ (isEuclidIsometry_of_hyperoctahedral w.1) hτ 0 0 F.1).1,
      ← (hA _ _ hτ (isEuclidIsometry_of_hyperoctahedral w.1) 0 0 F.1).1, stabilizer_comp_translate]
end Stabilizer
private theorem stronglyCommute_energyMomentumPair {σ : TupleFunctional} {h : IsPosSemidef (reflectionForm σ)}
    (hfour : StronglyCommute (energyMomentumOps σ h)) (i : Fin 3) :
    StronglyCommute (energyMomentumPair σ h i) := by
  let φ : Fin 2 → Fin 4 := ![0, i.succ]
  have e : ∀ j, energyMomentumPair σ h i j = energyMomentumOps σ h (φ j) := by
    intro j
    fin_cases j
    · rfl
    · simp [energyMomentumPair, energyMomentumOps, φ]
  have hφ : Function.Injective φ := by
    intro j k hjk
    fin_cases j <;> fin_cases k <;> simp_all [φ, Fin.succ_ne_zero, (Fin.succ_ne_zero i).symm]
  refine ⟨fun j => ?_, fun j k hjk P Q hP hQ => ?_⟩
  · rw [e]
    exact hfour.1 _
  · rw [e] at hP hQ
    exact hfour.2 _ _ (fun c => hjk (hφ c)) P Q hP hQ
abbrev _root_.YangMills.SharedProofs.p86973 := @stronglyCommute_energyMomentumPair
private theorem jointSpectrumSubset_nonnegEnergy {σ : TupleFunctional} {h : IsPosSemidef (reflectionForm σ)}
    (supp : SpectralSupport.ConcentratedOnSupportTheorem)
    (hO : OperatorClaim σ h) (hCar : SupportClaim σ h) :
    LimitTheorem.JointSpectrumSubset σ h {y | 0 ≤ y 0} := by
  have hclosed : IsClosed {y : Fin 4 → ℝ | 0 ≤ y 0} :=
    isClosed_le continuous_const (continuous_apply 0)
  refine ⟨(jointMeasure σ h).support, ⟨_, fun r => ?_, rfl⟩, ?_⟩
  · fin_cases r
    · exact hO.1
    · exact hO.2.1 0
    · exact hO.2.1 1
    · exact hO.2.1 2
  · exact ((supp 4 _ (jointMeasure σ h)).support_subset_iff _ hclosed).2 hCar.1
abbrev _root_.YangMills.SharedProofs.p1597 := @jointSpectrumSubset_nonnegEnergy
private theorem reconstructionProperties_of_limit
    (recon : ReflectionPositivity.LimitReconstruction.LimitReconstructionTheorem)
    (compl : ComplementsTheorem)
    (firstHalf : ReflectionPositivity.LimitSymmetries.LimitHasSymmetries)
    (bdd : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (supp : SpectralSupport.ConcentratedOnSupportTheorem)
    (hilbert : HilbertSpaceFacts.Facts)
    (facts : BasicFacts.MainFacts)
    (fam : CanonicalDecomposition.SeparatingTuplesProperties.Claim)
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (s : Conventions.StandingParameters)
    (T : LimitConventions.ApproxTriple L) (σ : TupleFunctional)
    (hb : ReflectionPositivity.ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM
      (unitAxisMirrorData hL) T)
    (hrp : LimitConventions.ApproxTriple.IsReflPos T)
    (hlim : LimitConventions.ApproxTriple.ConvergesTo T σ) :
    LimitTheorem.ReconstructionProperties σ := by
  have hC : HilbertSpaceFacts.CompletionProperties := hilbert.2.2.2.2.2.1
  have hA : BasicFacts.PushSpanProperties := facts.2.2.2.2.1
  obtain ⟨hH, -, h, hV, hS, hTr, hM⟩ := recon (unitAxisMirrorData hL) T σ hb hrp hlim
  obtain ⟨hcub, hc⟩ := compl
  obtain ⟨h₃, -, hOps, hCar, -, hUnit⟩ := hc (unitAxisMirrorData hL) T σ hb hrp hlim
  obtain ⟨hσ₀, hsym⟩ := firstHalf (unitAxisMirrorData hL) T σ hb hrp hlim
  have hcont : σ.IsAdmissiblyContinuous := hsym.1.2.2
  have hSn : ∀ f : RealValued, IsC1c f →
      TestFunctions.c1NormR4 f ≤ TestFunctions.sharpNormR4 1 f := fun f hf =>
    (bdd.2.1 1 le_rfl f hf).1
  have hsepH := separableSpace_physicalSpace hcont fam hSn s h
  have hrep := stabilizerOp_isStabilizerRep hcub hUnit hC hA hS.2.1
  obtain ⟨D₀, hD₀⟩ := hH.contraction
  exact ⟨hH.permInvariant, hD₀.translateInvariant, h, ⟨hV, hS, hTr, hM⟩, hsepH,
    stronglyCommute_energyMomentumPair hOps.2.2.1, jointSpectrumSubset_nonnegEnergy supp hOps hCar, _, hrep⟩
end ReconstructionProperties
end YangMills.Construction.WindowLimits
end
end
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
theorem limitReconstructionProperties_of_inputs
    (h1 : ReflectionPositivity.LimitReconstruction.LimitReconstructionTheorem)
    (h2 : ReflectionPositivity.ReconstructionComplements.ComplementsTheorem)
    (h3 : ReflectionPositivity.LimitSymmetries.LimitHasSymmetries)
    (h4 : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (h5 : SpectralSupport.ConcentratedOnSupportTheorem)
    (h6 : HilbertSpaceFacts.Facts)
    (h7 : SeparatedTuples.BasicFacts.MainFacts)
    (h8 : CanonicalDecomposition.SeparatingTuplesProperties.Claim) :
    LimitReconstructionProperties :=
  fun hL s T σ hb hrp hl =>
    WindowLimits.reconstructionProperties_of_limit h1 h2 h3 h4 h5 h6 h7 h8 hL s T σ hb hrp hl
end YangMills.Construction.SystemsWithFiveBounds
end

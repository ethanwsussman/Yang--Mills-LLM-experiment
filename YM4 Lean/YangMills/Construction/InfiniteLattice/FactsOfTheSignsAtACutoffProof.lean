import YangMills.Construction.InfiniteLattice.GroupOfLatticeIsometriesProof
import YangMills.Construction.ReflectionPositivity.ModulusOfAFunctionOfClassC1TendsToZeroProof
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.Cumulants.MultilinearityShiftsAndMomentsOfJointCumulants
import YangMills.Construction.InfiniteLattice.FactsOfTheSignsAtACutoff
import YangMills.Construction.SourcesAndGluing.CumulantsOfBoundedVariables
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNormProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.AtCutoff.SignFacts
open YangMills.Construction.MetricNotions YangMills.Construction.TorusMetric
open YangMills.Construction.ReflectionPositivity.AxisMirror
section Distances
variable {X : Type*} {d : X → X → ℝ}
theorem exists_of_notMem_closureWrt {Z : Set X} {x : X} (h : x ∉ closureWrt d Z) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Z, r ≤ d x y := by apply _root_.YangMills.SharedProofs.p12075 <;> assumption
theorem closureWrt_mono {A B : Set X} (h : A ⊆ B) : closureWrt d A ⊆ closureWrt d B :=
  fun _ hx r hr => let ⟨y, hy, hd⟩ := hx r hr; ⟨y, h hy, hd⟩
theorem closureWrt_union_subset (A B : Set X) :
    closureWrt d (A ∪ B) ⊆ closureWrt d A ∪ closureWrt d B := by
  intro x hx
  by_contra hn
  rw [Set.mem_union, not_or] at hn
  obtain ⟨r, hr, h₁⟩ := exists_of_notMem_closureWrt hn.1
  obtain ⟨r', hr', h₂⟩ := exists_of_notMem_closureWrt hn.2
  obtain ⟨y, hy | hy, hd⟩ := hx (min r r') (lt_min hr hr')
  · exact absurd (lt_of_lt_of_le hd (min_le_left _ _)) (not_lt.2 (h₁ y hy))
  · exact absurd (lt_of_lt_of_le hd (min_le_right _ _)) (not_lt.2 (h₂ y hy))
theorem closureWrt_empty : closureWrt d (∅ : Set X) = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨y, hy, -⟩ := hx 1 one_pos
  exact hy
theorem isClosedWrt_closureWrt (tri : ∀ x y z, d x z ≤ d x y + d y z) (Z : Set X) :
    IsClosedWrt d (closureWrt d Z) := by apply _root_.YangMills.SharedProofs.p11892 <;> assumption
theorem IsCompactWrt.of_isClosedWrt_subset {Z C : Set X} (hZ : IsCompactWrt d Z)
    (hC : IsClosedWrt d C) (hs : C ⊆ Z) : IsCompactWrt d C := by apply _root_.YangMills.SharedProofs.p5019 <;> assumption
theorem IsCompactWrt.union {A B : Set X} (hA : IsCompactWrt d A) (hB : IsCompactWrt d B) :
    IsCompactWrt d (A ∪ B) := by apply _root_.YangMills.SharedProofs.p57694 <;> assumption
theorem closureWrt_image {e : X ≃ X} (he : ∀ x y, d (e x) (e y) = d x y) (Z : Set X) :
    closureWrt d (e '' Z) = e '' closureWrt d Z := by
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x, fun r hr => ?_, e.apply_symm_apply x⟩
    obtain ⟨_, ⟨z, hz, rfl⟩, hd⟩ := hx r hr
    refine ⟨z, hz, ?_⟩
    rw [← he, e.apply_symm_apply]
    exact hd
  · rintro ⟨z, hz, rfl⟩ r hr
    obtain ⟨y, hy, hd⟩ := hz r hr
    exact ⟨e y, ⟨y, hy, rfl⟩, by rw [he]; exact hd⟩
theorem IsCompactWrt.image {e : X ≃ X} (he : ∀ x y, d (e x) (e y) = d x y) {Z : Set X}
    (hZ : IsCompactWrt d Z) : IsCompactWrt d (e '' Z) := by
  intro 𝒰 hU hcov
  have hopen : ∀ V ∈ (fun U : Set X => e ⁻¹' U) '' 𝒰, IsOpenWrt d V := by
    rintro _ ⟨U, hUm, rfl⟩ x hx
    obtain ⟨r, hr, h⟩ := hU U hUm (e x) hx
    exact ⟨r, hr, fun y hy => h (e y) (by rw [he]; exact hy)⟩
  have hsub : Z ⊆ ⋃₀ ((fun U : Set X => e ⁻¹' U) '' 𝒰) := by
    intro x hx
    obtain ⟨U, hUm, hxU⟩ := hcov (Set.mem_image_of_mem e hx)
    exact ⟨e ⁻¹' U, ⟨U, hUm, rfl⟩, hxU⟩
  obtain ⟨𝒰', h₁, h₂, h₃⟩ := Set.exists_subset_image_finite_and.1 (hZ _ hopen hsub)
  refine ⟨𝒰', h₁, h₂, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨_, ⟨U, hUm, rfl⟩, hxU⟩ := h₃ hx
  exact ⟨U, hUm, hxU⟩
end Distances
section Euclid
theorem euclidNormVec_sub_le (x y z : Fin 4 → ℝ) :
    euclidNormVec (x - z) ≤ euclidNormVec (x - y) + euclidNormVec (y - z) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_le <;> assumption
theorem norm_le_euclidNormVec (v : Fin 4 → ℝ) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul_norm (v : Fin 4 → ℝ) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
def euclidDist (x y : Fin 4 → ℝ) : ℝ := euclidNormVec (x - y)
theorem isCompact_of_isCompactWrt {S : Set (Fin 4 → ℝ)} (h : IsCompactWrt euclidDist S) :
    IsCompact S := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.SmoothModulusVanishes.isCompact_of_isCompactWrt <;> assumption
theorem closure_subset_closureWrt (Z : Set (Fin 4 → ℝ)) :
    closure Z ⊆ closureWrt euclidDist Z := by
  intro x hx r hr
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.1 hx (r / 2) (half_pos hr)
  refine ⟨y, hy, ?_⟩
  have h : euclidNormVec (x - y) ≤ 2 * ‖x - y‖ := euclidNormVec_le_two_mul_norm _
  rw [dist_eq_norm] at hd
  show euclidNormVec (x - y) < r
  linarith
theorem hasCompactSupport_of_isCompactWrt {f : (Fin 4 → ℝ) → ℝ}
    (h : IsCompactWrt euclidDist (closureWrt euclidDist {x | f x ≠ 0})) : HasCompactSupport f :=
  (isCompact_of_isCompactWrt h).of_isClosed_subset isClosed_closure
    (closure_subset_closureWrt _)
end Euclid
section Bounds
theorem partialDerivR4_eq_fderiv (μ : Fin 4) {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (x : Fin 4 → ℝ) :
    TestFunctions.partialDerivR4 μ f x = fderiv ℝ f x (Pi.single μ 1) := by
  have hd : DifferentiableAt ℝ f x := (hf.differentiable one_ne_zero) x
  have h₁ : HasDerivAt (fun t : ℝ => x + t • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ))
      (Pi.single μ 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)).const_add x
  have h₂ := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hd.hasFDerivAt h₁ (by simp)
  exact h₂.deriv
theorem hasFiniteC1NormR4_of_hasCompactSupport {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : SourcesAndGluing.HasFiniteC1NormR4 f := by
  refine ⟨hc.exists_bound_of_continuous hf.continuous, fun μ => ?_⟩
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv one_ne_zero)
  refine ⟨C * ‖(Pi.single μ (1 : ℝ) : Fin 4 → ℝ)‖, fun x => ?_⟩
  rw [partialDerivR4_eq_fderiv μ hf x]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
def gluingSetupOf (D : MirrorData) : SourcesAndGluing.GluingSetup where
  toStandingParameters := D.toStandingParameters
  β := D.β
  beta_pos := D.β_pos
  cubeExp := 0
theorem hasFiniteC1NormTorus_of_contDiff (hc : ProjectionFacts) (D : MirrorData) {f : D.Torus → ℝ}
    (hf : ContDiff ℝ 1 (f ∘ D.projection)) : (gluingSetupOf D).HasFiniteC1NormTorus f := by
  obtain ⟨-, hlift, -⟩ : D.ProjectionAdditive := (hc D).1
  have hQ : IsCompact (Set.Icc (0 : Fin 4 → ℝ) (fun _ => D.side)) := isCompact_Icc
  have hmem : ∀ x : D.Torus, ∃ y ∈ Set.Icc (0 : Fin 4 → ℝ) (fun _ => D.side),
      D.projection y = x := by
    intro x
    obtain ⟨y, hy, hI⟩ := hlift x
    exact ⟨y, ⟨fun μ => (hI μ).1, fun μ => (hI μ).2.le⟩, hy⟩
  obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨C', hC'⟩ := hQ.exists_bound_of_continuousOn
    (hf.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨⟨C, fun x => ?_⟩, fun μ => ⟨C' * ‖(Pi.single μ (1 : ℝ) : Fin 4 → ℝ)‖, fun x => ?_⟩⟩
  · obtain ⟨y, hy, rfl⟩ := hmem x
    exact hC y hy
  · obtain ⟨y, hy, rfl⟩ := hmem x
    have h : (gluingSetupOf D).partialDeriv μ f (D.projection y) =
        TestFunctions.partialDerivR4 μ (f ∘ D.projection) y :=
      congrFun ((gluingSetupOf D).partialDeriv_comp_proj μ f) y
    rw [h, partialDerivR4_eq_fderiv μ hf y]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hC' y hy) (norm_nonneg _))
end Bounds
section Parts
variable (D : MirrorData)
theorem metric_triangle (hc : ProjectionFacts) (E : Ambient) (x y z : E.Point D) :
    Ambient.metric D E x z ≤ Ambient.metric D E x y + Ambient.metric D E y z := by
  cases E with
  | torus =>
    obtain ⟨-, -, -, -, -, h⟩ : D.ProjectionMetric := (hc D).2.1
    exact h x y z
  | euclidean => exact euclidNormVec_sub_le x y z
variable {D} in
theorem metric_isometryEquiv (r : Ambient.IsometryEquiv D .euclidean)
    (x y : Ambient.euclidean.Point D) :
    Ambient.metric D .euclidean (r.toEquiv x) (r.toEquiv y) = Ambient.metric D .euclidean x y :=
  r.isometric x y
variable {D} in
theorem closedSupport_mapFn (r : Ambient.IsometryEquiv D .euclidean) {𝕜 : Type} [RCLike 𝕜]
    (f : Ambient.euclidean.Point D → 𝕜) :
    Ambient.closedSupport D .euclidean (r.mapFn f) =
      r.toEquiv '' Ambient.closedSupport D .euclidean f := by
  have hset : {x | r.mapFn f x ≠ 0} = r.toEquiv '' {x | f x ≠ 0} := by
    ext x
    constructor
    · intro hx
      exact ⟨r.toEquiv.symm x, hx, r.toEquiv.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      show f (r.toEquiv.symm (r.toEquiv y)) ≠ 0
      rwa [Equiv.symm_apply_apply]
  unfold Ambient.closedSupport
  rw [hset, closureWrt_image (metric_isometryEquiv r)]
theorem isometryFacts : IsometryFacts D := by
  intro r
  have he := metric_isometryEquiv r
  have he' : ∀ x y, Ambient.metric D .euclidean (r.toEquiv.symm x) (r.toEquiv.symm y) =
      Ambient.metric D .euclidean x y := fun x y => by
    rw [← he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  refine ⟨fun x ε hε => ⟨ε, hε, fun y hy => by rw [he]; exact hy⟩,
    fun x ε hε => ⟨ε, hε, fun y hy => by rw [he']; exact hy⟩, fun 𝕜 _ f => ?_⟩
  exact ⟨closedSupport_mapFn r f, fun h => IsCompactWrt.image he h⟩
theorem euclidNormVec_hyperoctahedral
    {w : InfiniteLattice.AmbientSpace ≃ₗ[ℝ] InfiniteLattice.AmbientSpace}
    (hw : w ∈ InfiniteLattice.hyperoctahedralLinearGroup) (x : Fin 4 → ℝ) :
    euclidNormVec (w x) = euclidNormVec x := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeSymmetryGroup.euclidNormVec_hyperoctahedral <;> assumption
def affineIsometryEquiv (w : InfiniteLattice.AmbientSpace ≃ₗ[ℝ] InfiniteLattice.AmbientSpace)
    (hw : w ∈ InfiniteLattice.hyperoctahedralLinearGroup) (v : Fin 4 → ℝ) :
    Ambient.IsometryEquiv D .euclidean where
  toEquiv :=
    { toFun := fun x : Fin 4 → ℝ => w x + v
      invFun := fun y : Fin 4 → ℝ => w.symm (y - v)
      left_inv := fun x : Fin 4 → ℝ => by
        show w.symm (w x + v - v) = x
        simp
      right_inv := fun y : Fin 4 → ℝ => by
        show w (w.symm (y - v)) + v = y
        simp }
  isometric := fun x y : Fin 4 → ℝ => by
    change euclidNormVec (w x + v - (w y + v)) = euclidNormVec (x - y)
    rw [add_sub_add_right_eq_sub, ← map_sub, euclidNormVec_hyperoctahedral hw]
variable {D} in
theorem mapFn_eq_of_affine {r : Ambient.IsometryEquiv D .euclidean}
    {w : InfiniteLattice.AmbientSpace ≃ₗ[ℝ] InfiniteLattice.AmbientSpace} {v : Fin 4 → ℝ}
    (h : IsAffineRealization D r w v) (f : (Fin 4 → ℝ) → ℝ) :
    r.mapFn f = fun y : Fin 4 → ℝ => f (w.symm (y - v)) := by
  refine funext fun (y : Fin 4 → ℝ) => ?_
  have h₁ : @Eq (Fin 4 → ℝ) (r.toEquiv (r.toEquiv.symm y)) (w (r.toEquiv.symm y) + v) := h _
  have h₀ : @Eq (Fin 4 → ℝ) (r.toEquiv (r.toEquiv.symm y)) y := r.toEquiv.apply_symm_apply y
  have h₃ : y - v = w (r.toEquiv.symm y) := sub_eq_of_eq_add (h₀.symm.trans h₁)
  have h₄ : @Eq (Fin 4 → ℝ) (w.symm (y - v)) (r.toEquiv.symm y) := by
    rw [h₃]
    exact w.symm_apply_apply _
  exact congrArg f h₄.symm
variable {D} in
theorem isC1_mapFn {r : Ambient.IsometryEquiv D .euclidean}
    {w : InfiniteLattice.AmbientSpace ≃ₗ[ℝ] InfiniteLattice.AmbientSpace} {v : Fin 4 → ℝ}
    (h : IsAffineRealization D r w v) {f : (Fin 4 → ℝ) → ℝ} (hf : Ambient.IsC1 D .euclidean f) :
    Ambient.IsC1 D .euclidean (r.mapFn f) := by
  rw [mapFn_eq_of_affine h f]
  have hw : ContDiff ℝ 1 (fun y : Fin 4 → ℝ => w.symm y) :=
    (LinearMap.toContinuousLinearMap
      (w.symm : InfiniteLattice.AmbientSpace →ₗ[ℝ] InfiniteLattice.AmbientSpace)).contDiff
  have hf' : ContDiff ℝ 1 f := hf
  exact hf'.comp (hw.comp (contDiff_id.sub contDiff_const))
theorem affineMapFacts : AffineMapFacts D := by
  intro w hw v
  refine ⟨⟨affineIsometryEquiv D w hw v, fun x => rfl⟩, fun r hr =>
    ⟨fun f hf => isC1_mapFn hr hf, fun n X hX => ?_⟩⟩
  obtain ⟨hn, hsep, hpair⟩ := hX
  refine ⟨by simpa [Ambient.IsometryEquiv.mapList] using hn, ?_, ?_⟩
  · intro g hg
    obtain ⟨f, hfX, rfl⟩ := List.mem_map.1 hg
    obtain ⟨h₁, h₂⟩ := hsep f hfX
    refine ⟨isC1_mapFn hr h₁, ?_⟩
    show IsCompactWrt _ (Ambient.closedSupport D .euclidean (r.mapFn f))
    rw [closedSupport_mapFn]
    exact IsCompactWrt.image (metric_isometryEquiv r) h₂
  · refine List.pairwise_map.2 (hpair.imp fun {f g} h => ?_)
    rw [closedSupport_mapFn, closedSupport_mapFn]
    exact (Set.disjoint_image_iff r.toEquiv.injective).2 h
theorem contDiff_linComb {f g : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (s t : ℝ) : ContDiff ℝ 1 (s • f + t • g) :=
  (hf.const_smul s).add (hg.const_smul t)
theorem isC1_linComb (E : Ambient) {f g : E.Point D → ℝ}
    (hf : Ambient.IsC1 D E f) (hg : Ambient.IsC1 D E g) (s t : ℝ) :
    Ambient.IsC1 D E (s • f + t • g) := by
  cases E with
  | torus =>
    exact contDiff_linComb (f := f ∘ D.projection) (g := g ∘ D.projection) hf hg s t
  | euclidean => exact contDiff_linComb hf hg s t
theorem closedSupport_linComb_subset (E : Ambient) (f g : E.Point D → ℝ) (s t : ℝ) :
    Ambient.closedSupport D E (s • f + t • g) ⊆
      Ambient.closedSupport D E f ∪ Ambient.closedSupport D E g := by
  refine (closureWrt_mono ?_).trans (closureWrt_union_subset _ _)
  intro x hx
  by_contra hn
  rw [Set.mem_union, not_or] at hn
  have h₁ : f x = 0 := not_not.1 hn.1
  have h₂ : g x = 0 := not_not.1 hn.2
  apply hx
  simp [h₁, h₂]
theorem linComb_mem_cOneIn (hc : ProjectionFacts) (E : Ambient)
    (A : Set (E.Point D)) {f g : E.Point D → ℝ} (hf : f ∈ cOneIn D E A)
    (hg : g ∈ cOneIn D E A) (s t : ℝ) : s • f + t • g ∈ cOneIn D E A := by
  have hsub := closedSupport_linComb_subset D E f g s t
  refine ⟨⟨isC1_linComb D E hf.1.1 hg.1.1 s t, ?_⟩,
    hsub.trans (Set.union_subset hf.2 hg.2)⟩
  exact IsCompactWrt.of_isClosedWrt_subset (IsCompactWrt.union hf.1.2 hg.1.2)
    (isClosedWrt_closureWrt (metric_triangle D hc E) _) hsub
theorem closedSupport_zero (E : Ambient) :
    Ambient.closedSupport D E (0 : E.Point D → ℝ) = ∅ := by
  have h : {x : E.Point D | (0 : E.Point D → ℝ) x ≠ 0} = ∅ := by
    ext x
    simp
  unfold Ambient.closedSupport
  rw [h, closureWrt_empty]
theorem zero_mem_cOneIn (E : Ambient) (A : Set (E.Point D)) :
    (0 : E.Point D → ℝ) ∈ cOneIn D E A := by
  have h₀ : ContDiff ℝ 1 (fun _ : Fin 4 → ℝ => (0 : ℝ)) := contDiff_const
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · cases E with
    | torus => exact h₀
    | euclidean => exact h₀
  · rw [closedSupport_zero]
    exact fun 𝒰 _ _ => ⟨∅, Set.empty_subset _, Set.finite_empty, Set.empty_subset _⟩
  · rw [closedSupport_zero]
    exact Set.empty_subset _
theorem c1ClassFacts (hc : ProjectionFacts) (E : Ambient) : C1ClassFacts D E := by
  refine ⟨fun A => ?_, fun n _ A hA f hf => Ambient.ofFn_mem_separatedN D E
    ((pairwisePosSeparated_iff D E A).1 hA) hf⟩
  refine ⟨{ carrier := cOneIn D E A
            add_mem' := fun {f g} hf hg => ?_
            zero_mem' := zero_mem_cOneIn D E A
            smul_mem' := fun c f hf => ?_ }, rfl⟩
  · simpa using linComb_mem_cOneIn D hc E A hf hg 1 1
  · simpa using linComb_mem_cOneIn D hc E A hf (zero_mem_cOneIn D E A) c 0
variable {D} in
theorem contDiff_of_mem_cOneIn {A : Set (Fin 4 → ℝ)} {f : (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ cOneIn D .euclidean A) : ContDiff ℝ 1 f ∧ HasCompactSupport f :=
  ⟨hf.1.1, hasCompactSupport_of_isCompactWrt hf.1.2⟩
theorem boundedLipschitz (hs : SourcesAndGluing.SharpNormBound.Statement)
    (hc : ProjectionFacts) (E : Ambient) : BoundedLipschitz D E := by
  intro f hf
  cases E with
  | torus =>
    have hC : ContDiff ℝ 1 (f ∘ D.projection) := hf.1.1
    have hfin := hasFiniteC1NormTorus_of_contDiff hc D hC
    exact ⟨hfin.1, ((hs (gluingSetupOf D) ℝ).1 f hC hfin).1⟩
  | euclidean =>
    obtain ⟨hC, hcs⟩ := contDiff_of_mem_cOneIn hf
    have hfin := hasFiniteC1NormR4_of_hasCompactSupport hC hcs
    exact ⟨hfin.1, ((hs (gluingSetupOf D) ℝ).2 f hC hfin).1⟩
theorem normBoundsR4 (hs : SourcesAndGluing.SharpNormBound.Statement) :
    NormBoundsR4 D := by
  intro f hf
  obtain ⟨hC, hcs⟩ := contDiff_of_mem_cOneIn hf
  have hfin := hasFiniteC1NormR4_of_hasCompactSupport hC hcs
  obtain ⟨-, hLip, -⟩ := (hs (gluingSetupOf D) ℝ).2 f hC hfin
  refine ⟨hfin, hLip, fun M hM => ?_⟩
  have h₁ : TestFunctions.uniformNorm f ≤ TestFunctions.c1NormR4 f := le_max_left _ _
  have h₀ : 0 ≤ TestFunctions.uniformNorm f := Real.iSup_nonneg fun _ => norm_nonneg _
  refine max_le ?_ ?_
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left hLip (by positivity : 0 ≤ 40 * M)]
theorem smearedObservableFacts (hcum : SourcesAndGluing.BoundedCumulants.Corollary) :
    SmearedObservableFacts D := by
  obtain ⟨-, -, hO⟩ := hcum
  obtain ⟨-, h₂, -, h₄, -⟩ := hO (gluingSetupOf D)
  refine ⟨⟨SourcesAndGluing.compactBorelSubspace, rfl⟩, fun A f hf => ?_, h₂,
    fun f hf g hg s t => h₄ f hf g hg s t⟩
  obtain ⟨hC, hcs⟩ := contDiff_of_mem_cOneIn hf
  exact ⟨hC.continuous.measurable, hcs.exists_bound_of_continuous hC.continuous, hcs⟩
end Parts
section Real
open YangMills.Construction.Probability (IsBoundedRealRV)
theorem mixedCumulant_orderEmbOfFin_univ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
    {q n : ℕ} (hn : (Finset.univ : Finset (Fin q)).card = n) (X : Fin q → Ω → ℝ)
    (Y : Fin n → Ω → ℝ) (hY : ∀ k, Y k = X (Finset.univ.orderEmbOfFin hn k)) :
    Cumulants.mixedCumulant ν Y = Cumulants.mixedCumulant ν X := by
  have hq : n = q := by simpa using hn.symm
  subst hq
  congr 1
  funext k
  rw [hY k]
  congr 1
  exact (congrFun (Finset.orderEmbOfFin_unique hn (f := id) (fun _ => Finset.mem_univ _)
    strictMono_id) k).symm
theorem mixedCumulant_mem_range (hmom : Cumulants.MomentCumulantRelations.Holds)
    {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (q : ℕ) :
    1 ≤ q → ∀ X : Fin q → Ω → ℝ, (∀ l, IsBoundedRealRV (X l)) →
      Cumulants.mixedCumulant ν X ∈ Complex.ofRealHom.range := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq X hX
    have hm := ((hmom Ω ν).2.2.2 q X hq hX).1
    have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
    let π₀ : SourcesAndGluing.IndexPartition q :=
      Finpartition.indiscrete (Finset.univ_nonempty (α := Fin q)).ne_empty
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ π₀)] at hm
    have h₀ : ∏ B ∈ π₀.parts, Cumulants.mixedCumulant ν
        (fun k : Fin B.card => X (B.orderEmbOfFin rfl k)) = Cumulants.mixedCumulant ν X := by
      show ∏ B ∈ ({Finset.univ} : Finset (Finset (Fin q))), Cumulants.mixedCumulant ν
        (fun k : Fin B.card => X (B.orderEmbOfFin rfl k)) = _
      rw [Finset.prod_singleton]
      exact mixedCumulant_orderEmbOfFin_univ ν rfl X _ fun _ => rfl
    rw [h₀] at hm
    rw [eq_sub_of_add_eq hm.symm]
    refine sub_mem ⟨_, rfl⟩ (sum_mem fun π hπ => prod_mem fun B hB => ?_)
    have hne : π ≠ π₀ := (Finset.mem_erase.1 hπ).1
    have hpos : 1 ≤ B.card := Finset.card_pos.2 (π.nonempty_of_mem_parts hB)
    have hlt : B.card < q := by
      by_contra hge
      have hle : B.card ≤ q := by simpa using Finset.card_le_univ B
      have hB' : B = Finset.univ :=
        Finset.eq_univ_of_card B (by simpa using le_antisymm hle (not_lt.1 hge))
      apply hne
      apply Finpartition.ext
      ext C
      constructor
      · intro hC
        obtain ⟨a, ha⟩ := π.nonempty_of_mem_parts hC
        have : C = B := π.eq_of_mem_parts hC hB ha (hB' ▸ Finset.mem_univ a)
        show C ∈ ({Finset.univ} : Finset (Finset (Fin q)))
        rw [this, hB']
        exact Finset.mem_singleton_self _
      · intro hC
        have : C = Finset.univ := Finset.mem_singleton.1 hC
        rw [this, ← hB']
        exact hB
    exact ih _ hlt hpos _ fun k => hX _
end Real
section State
open YangMills.Construction.Probability (IsBoundedRealRV)
variable (D : MirrorData)
theorem connectedPartitionSum_zero (ν : Measure (FieldSpace D))
    (h : Fin 0 → InfiniteLattice.AmbientSpace → ℝ) : connectedPartitionSum ν h = 1 := by
  have hu : ∀ π : Finpartition (Finset.univ : Finset (Fin 0)), π.parts = ∅ := fun π => by
    refine Finset.eq_empty_of_forall_notMem fun B hB => ?_
    obtain ⟨a, -⟩ := π.nonempty_of_mem_parts hB
    exact a.elim0
  have hb : SetPartition.nonSingletonPartitions 0 = {⊥} := by
    ext π
    simp only [SetPartition.nonSingletonPartitions, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, hu]
    exact ⟨fun _ => Finpartition.ext ((hu π).trans (hu ⊥).symm), fun _ J hJ => by simp at hJ⟩
  unfold connectedPartitionSum
  rw [hb, Finset.sum_singleton, hu, Finset.prod_empty]
theorem stateConnectedFunctions (hmom : Cumulants.MomentCumulantRelations.Holds)
    (hobs : ∀ f ∈ boundedBorelCompactSupport,
      IsBoundedRealRV fun U : FieldSpace D => InfiniteLattice.smearedEnergy f U) :
    StateConnectedFunctions D := by
  intro ν hν
  have : IsProbabilityMeasure ν := hν
  refine ⟨fun n hn f hf => ?_, fun q h hh => ?_⟩
  · obtain ⟨r, hr⟩ := mixedCumulant_mem_range hmom ν n (by omega)
      (fun i U => InfiniteLattice.smearedEnergy (f i) U) fun i => hobs _ (hf i)
    change (Cumulants.mixedCumulant ν _).im = 0
    rw [← hr]
    simp
  · cases q with
    | zero =>
      rw [connectedPartitionSum_zero]
      simp [InfiniteLattice.PeriodicTorusMeasures.measureCentredMoment]
    | succ q =>
      have hm := ((hmom _ ν).2.2.2 (q + 1) (fun l U => InfiniteLattice.smearedEnergy (h l) U)
        (by omega) fun l => hobs _ (hh l)).2
      have key : ∀ U : FieldSpace D, ((h 0 :: List.ofFn fun i : Fin q => h i.succ).map
          fun k => InfiniteLattice.smearedEnergy k U -
            ∫ V, InfiniteLattice.smearedEnergy k V ∂ν).prod =
          ∏ l, (InfiniteLattice.smearedEnergy (h l) U -
            ∫ V, InfiniteLattice.smearedEnergy (h l) V ∂ν) := fun U => by
        rw [← List.ofFn_succ, List.map_ofFn, List.prod_ofFn]
        rfl
      have hL : InfiniteLattice.PeriodicTorusMeasures.measureCentredMoment ν (List.ofFn h) =
          ∫ U, ∏ l, (InfiniteLattice.smearedEnergy (h l) U -
            ∫ V, InfiniteLattice.smearedEnergy (h l) V ∂ν) ∂ν := by
        rw [List.ofFn_succ]
        exact integral_congr_ae (Filter.Eventually.of_forall key)
      rw [hL]
      exact hm
end State
theorem signFactsHold_of (hcum : SourcesAndGluing.BoundedCumulants.Corollary)
    (hs : SourcesAndGluing.SharpNormBound.Statement)
    (hc : ProjectionFacts)
    (hmom : Cumulants.MomentCumulantRelations.Holds) : SignFactsHold := fun D =>
  ⟨isometryFacts D, affineMapFacts D, c1ClassFacts D hc, boundedLipschitz D hs hc,
    normBoundsR4 D hs, smearedObservableFacts D hcum,
    stateConnectedFunctions D hmom (smearedObservableFacts D hcum).2.2.1⟩
end YangMills.Construction.AtCutoff.SignFacts
end

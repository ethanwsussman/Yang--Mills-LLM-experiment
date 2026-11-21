import YangMills.Construction.Lattice.IsometryInvarianceOfWilsonMeasure
import YangMills.Construction.ReflectionPositivity.BondsAndPlaquettesAreNotDegenerate
import YangMills.Construction.ReflectionPositivity.ReflectionInALinkMirror
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkReflection
variable {D : MirrorData}
def axisFlip (w : D.Torus) : D.Torus := Function.update w D.dir (-(w D.dir))
def axisFlipVec (D : MirrorData) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  Function.update v D.dir (-(v D.dir))
theorem axisFlip_axisFlip (w : D.Torus) : axisFlip (axisFlip w) = w := by
  funext i
  by_cases hi : i = D.dir
  · subst hi
    simp [axisFlip]
  · simp [axisFlip, Function.update_of_ne hi]
theorem torusProj_axisFlipVec (v : Fin 4 → ℝ) :
    TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) (axisFlipVec D v) =
      axisFlip (TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) v : D.Torus) := by
  funext i
  by_cases hi : i = D.dir
  · subst hi
    simp [axisFlip, axisFlipVec, TorusMetric.torusProj]
  · simp [axisFlip, axisFlipVec, TorusMetric.torusProj, Function.update_of_ne hi]
theorem euclidNormVec_axisFlipVec (v : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (axisFlipVec D v) = TorusMetric.euclidNormVec v := by
  simp only [TorusMetric.euclidNormVec]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = D.dir
  · subst hi
    simp [axisFlipVec]
  · simp [axisFlipVec, Function.update_of_ne hi]
theorem torusEuclidNorm_axisFlip (w : D.Torus) :
    TorusMetric.torusEuclidNorm (axisFlip w) = TorusMetric.torusEuclidNorm w := by
  have hsub : ∀ z : D.Torus,
      TorusMetric.euclidNormVec '' (TorusMetric.torusProj _ ⁻¹' {z}) ⊆
        TorusMetric.euclidNormVec '' (TorusMetric.torusProj _ ⁻¹' {axisFlip z}) := by
    rintro z _ ⟨v, hv, rfl⟩
    refine ⟨axisFlipVec D v, ?_, euclidNormVec_axisFlipVec v⟩
    have hv' : TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) v = z := hv
    change TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) (axisFlipVec D v) = axisFlip z
    rw [torusProj_axisFlipVec, hv']
  have hset : TorusMetric.euclidNormVec '' (TorusMetric.torusProj _ ⁻¹' {axisFlip w}) =
      TorusMetric.euclidNormVec '' (TorusMetric.torusProj _ ⁻¹' {w}) := by
    refine Subset.antisymm ?_ (hsub w)
    have := hsub (axisFlip w)
    rwa [axisFlip_axisFlip] at this
  simp only [TorusMetric.torusEuclidNorm]
  rw [hset]
variable (C : LinkLevel D)
theorem refl_apply_eq_update (y : D.Torus) :
    C.refl y = Function.update y D.dir (((2 * C.pos : ℝ) : D.CircleCoord) - y D.dir) := by
  have hind : D.Induces C.pos
      (fun z => Function.update z D.dir (((2 * C.pos : ℝ) : D.CircleCoord) - z D.dir)) := by
    funext v
    funext i
    simp only [Function.comp_apply, MirrorData.reflectVec_eq_sub]
    by_cases hi : i = D.dir
    · subst hi
      simp only [Function.update_self, MirrorData.proj, TorusMetric.torusProj, Pi.sub_apply,
        Pi.smul_apply, PeriodicLattice.coordVec, Pi.single_eq_same, smul_eq_mul, mul_one]
      rw [← AddCircle.coe_sub]
      congr 1
      ring
    · simp [Function.update_of_ne hi, MirrorData.proj, TorusMetric.torusProj,
        PeriodicLattice.coordVec, Pi.single_eq_of_ne hi]
  have heq := (D.existsUnique_induces C.pos).unique (D.induces_reflect C.pos) hind
  exact congrFun heq y
theorem refl_apply_dir (y : D.Torus) :
    C.refl y D.dir = ((2 * C.pos : ℝ) : D.CircleCoord) - y D.dir := by
  rw [refl_apply_eq_update]
  simp
theorem refl_apply_of_ne (y : D.Torus) {i : Fin 4} (hi : i ≠ D.dir) : C.refl y i = y i := by
  rw [refl_apply_eq_update]
  simp [Function.update_of_ne hi]
theorem refl_involutive : Function.Involutive C.refl := by
  intro y
  funext i
  by_cases hi : i = D.dir
  · subst hi
    rw [refl_apply_dir, refl_apply_dir]
    abel
  · rw [refl_apply_of_ne C _ hi, refl_apply_of_ne C _ hi]
theorem refl_add (x w : D.Torus) : C.refl (x + w) = C.refl x + axisFlip w := by
  funext i
  by_cases hi : i = D.dir
  · subst hi
    simp only [Pi.add_apply, refl_apply_dir, axisFlip, Function.update_self]
    abel
  · simp only [Pi.add_apply, refl_apply_of_ne C _ hi, axisFlip, Function.update_of_ne hi]
theorem refl_sub_refl (x y : D.Torus) : C.refl x - C.refl y = axisFlip (x - y) := by
  have h := refl_add C y (x - y)
  rw [add_sub_cancel] at h
  rw [h]
  abel
theorem refl_isDistPreserving : D.IsDistPreserving C.refl := by
  intro x y
  simp only [MirrorData.torusDist, PeriodicLattice.torusEuclidDist]
  rw [refl_sub_refl]
  exact torusEuclidNorm_axisFlip _
theorem two_mul_pos_eq_int_mul_spacing (C : LinkLevel D) :
    ∃ k : ℤ, 2 * C.pos = (k : ℝ) * D.spacing := by
  obtain ⟨n, hn⟩ := C.isLinkLevel
  refine ⟨2 * n + 1, ?_⟩
  rw [hn]
  push_cast
  ring
theorem refl_mem_latticeSubgroup {x : D.Torus} (hx : x ∈ D.latticeSubgroup) :
    C.refl x ∈ D.latticeSubgroup := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨k, hk⟩ := two_mul_pos_eq_int_mul_spacing C
  refine ⟨Function.update n D.dir (k - n D.dir), fun i => ?_⟩
  by_cases hi : i = D.dir
  · subst hi
    rw [refl_apply_dir, hn, hk, ← AddCircle.coe_sub]
    simp only [Function.update_self]
    congr 1
    simp only [MirrorData.spacing]
    push_cast
    ring
  · rw [refl_apply_of_ne C _ hi, hn, Function.update_of_ne hi]
theorem refl_image_latticeSubgroup :
    C.refl '' (D.latticeSubgroup : Set D.Torus) = D.latticeSubgroup := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact refl_mem_latticeSubgroup C hx
  · intro x hx
    exact ⟨C.refl x, refl_mem_latticeSubgroup C hx, refl_involutive C x⟩
theorem centeredRep_refl (y : D.Torus) (hy : C.centeredRep y ≠ C.pos - D.side / 2) :
    C.centeredRep (C.refl y) = 2 * C.pos - C.centeredRep y := by
  obtain ⟨hrep, hlo, hhi⟩ := C.isCenteredRep_centeredRep y
  have hlo' : C.pos - D.side / 2 < C.centeredRep y := lt_of_le_of_ne hlo (Ne.symm hy)
  refine (C.existsUnique_isCenteredRep (C.refl y)).unique (C.isCenteredRep_centeredRep _)
    ⟨?_, ?_, ?_⟩
  · have hrep' : ((C.centeredRep y : ℝ) : D.CircleCoord) = y D.dir := hrep
    change ((2 * C.pos - C.centeredRep y : ℝ) : D.CircleCoord) = C.refl y D.dir
    rw [refl_apply_dir, AddCircle.coe_sub, hrep']
  · linarith
  · linarith
theorem refl_proj (y : Fin 4 → ℝ) : C.refl (D.proj y) = D.proj (C.reflVec y) :=
  congrFun (D.induces_reflect C.pos) y
theorem reflVec_apply_dir (y : Fin 4 → ℝ) : C.reflVec y D.dir = 2 * C.pos - y D.dir := by
  simp only [LinkLevel.reflVec, MirrorData.reflectVec_eq_sub, Pi.sub_apply, Pi.smul_apply,
    PeriodicLattice.coordVec, Pi.single_eq_same, smul_eq_mul, mul_one]
  ring
theorem refl_image_openSlab_subset (σ τ : SlabSide) (hστ : τ.toReal = -σ.toReal) :
    C.refl '' C.openSlab σ ⊆ C.openSlab τ := by
  rintro _ ⟨_, ⟨y, ⟨h₁, h₂⟩, rfl⟩, rfl⟩
  refine ⟨C.reflVec y, ⟨?_, ?_⟩, (refl_proj C y).symm⟩
  · rw [reflVec_apply_dir, hστ]
    have : -σ.toReal * (2 * C.pos - y D.dir - C.pos) = σ.toReal * (y D.dir - C.pos) := by ring
    rw [this]
    exact h₁
  · rw [reflVec_apply_dir, hστ]
    have : -σ.toReal * (2 * C.pos - y D.dir - C.pos) = σ.toReal * (y D.dir - C.pos) := by ring
    rw [this]
    exact h₂
theorem refl_image_openSlab (σ τ : SlabSide) (hστ : τ.toReal = -σ.toReal) :
    C.refl '' C.openSlab σ = C.openSlab τ := by
  refine Subset.antisymm (refl_image_openSlab_subset C σ τ hστ) ?_
  intro x hx
  exact ⟨C.refl x, refl_image_openSlab_subset C τ σ (by rw [hστ, neg_neg]) ⟨x, hx, rfl⟩,
    refl_involutive C x⟩
theorem actsOnTorus : ActsOnTorus C :=
  ⟨refl_involutive C, refl_isDistPreserving C, refl_image_latticeSubgroup C, centeredRep_refl C,
    refl_image_openSlab C .pos .neg (by simp [SlabSide.toReal]),
    refl_image_openSlab C .neg .pos (by simp [SlabSide.toReal])⟩
def reflSymmetry : D.Symmetry where
  toFun := C.refl
  dist_eq := refl_isDistPreserving C
  image_eq := refl_image_latticeSubgroup C
open PeriodicLattice in
abbrev reflSite (x : Site D.L D.m ((D.K : ℕ) : ℤ)) : Site D.L D.m ((D.K : ℕ) : ℤ) :=
  PeriodicLattice.TorusLatticeSymmetry.pointMap (reflSymmetry C) x
abbrev axisUnit (D : MirrorData) (i : Fin 4) : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ) :=
  PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) i
theorem axisFlip_axisUnit_of_ne {i : Fin 4} (hi : i ≠ D.dir) :
    axisFlip ((axisUnit D i : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)) : D.Torus) =
      (axisUnit D i) := by
  funext j
  by_cases hj : j = D.dir
  · subst hj
    simp [axisFlip, axisUnit, PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis,
      Pi.single_eq_of_ne (Ne.symm hi)]
  · simp [axisFlip, Function.update_of_ne hj]
theorem axisFlip_axisUnit_dir :
    axisFlip ((axisUnit D D.dir : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)) : D.Torus) =
      -(axisUnit D D.dir : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)) := by
  funext j
  by_cases hj : j = D.dir
  · subst hj
    simp [axisFlip]
  · simp [axisFlip, Function.update_of_ne hj, PeriodicLattice.unitStep,
      PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hj]
theorem reflSite_add_axisUnit (x : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)) {i : Fin 4}
    (hi : i ≠ D.dir) : reflSite C (x + axisUnit D i) = reflSite C x + axisUnit D i :=
  Subtype.ext (by
    change C.refl ((x : D.Torus) + (axisUnit D i : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ))) =
      C.refl x + (axisUnit D i : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ))
    rw [refl_add, axisFlip_axisUnit_of_ne hi])
theorem reflSite_add_axisUnit_dir (x : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)) :
    reflSite C (x + axisUnit D D.dir) = reflSite C x - axisUnit D D.dir :=
  Subtype.ext (by
    change C.refl ((x : D.Torus) +
        (axisUnit D D.dir : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ))) =
      C.refl x - (axisUnit D D.dir : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ))
    rw [refl_add, axisFlip_axisUnit_dir, sub_eq_add_neg])
theorem reflSite_reflSite (x : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)) :
    reflSite C (reflSite C x) = x :=
  Subtype.ext (refl_involutive C x)
theorem reflSite_sub_of_ne {x x' : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)} {i : Fin 4}
    (hi : i ≠ D.dir) (hx : x' - x = axisUnit D i) :
    reflSite C x' - reflSite C x = axisUnit D i := by
  have hx' : x' = x + axisUnit D i := by rw [← hx]; abel
  rw [hx', reflSite_add_axisUnit C x hi]
  abel
theorem reflSite_sub_dir {x x' : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)}
    (hx : x' - x = axisUnit D D.dir) : reflSite C x' - reflSite C x = -axisUnit D D.dir := by
  have hx' : x' = x + axisUnit D D.dir := by rw [← hx]; abel
  rw [hx', reflSite_add_axisUnit_dir C x]
  abel
theorem reflSite_sub_eq_or_eq_neg {x x' : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)}
    {i : Fin 4} (hx : x' - x = axisUnit D i) :
    reflSite C x' - reflSite C x = axisUnit D i ∨ reflSite C x' - reflSite C x = -axisUnit D i := by
  by_cases hi : i = D.dir
  · subst hi
    exact Or.inr (reflSite_sub_dir C hx)
  · exact Or.inl (reflSite_sub_of_ne C hi hx)
theorem exists_isBondImage (b : D.DirectedBond) :
    ∃ b', PeriodicLattice.TorusLatticeSymmetry.IsBondImage (reflSymmetry C) b b' := by
  obtain ⟨i, h | h⟩ := b.isNeighbour
  · exact ⟨⟨reflSite C b.source, reflSite C b.target, i, reflSite_sub_eq_or_eq_neg C h⟩, rfl⟩
  · have h' : b.source - b.target = axisUnit D i := by
      rw [← neg_sub, h, neg_neg]
    refine ⟨⟨reflSite C b.source, reflSite C b.target, i, ?_⟩, rfl⟩
    rcases reflSite_sub_eq_or_eq_neg C h' with e | e
    · right
      rw [← neg_sub, e]
    · left
      rw [← neg_sub, e, neg_neg]
theorem isBondImage_bondImage (b : D.DirectedBond) :
    PeriodicLattice.TorusLatticeSymmetry.IsBondImage (reflSymmetry C) b
      (MirrorData.Symmetry.bondImage (reflSymmetry C) b) := by
  obtain ⟨b', h⟩ := exists_isBondImage C b
  rwa [MirrorData.Symmetry.bondImage_eq _ h]
theorem bondImage_source (b : D.DirectedBond) :
    (MirrorData.Symmetry.bondImage (reflSymmetry C) b).source = reflSite C b.source :=
  congrArg Prod.fst (isBondImage_bondImage C b)
theorem bondImage_target (b : D.DirectedBond) :
    (MirrorData.Symmetry.bondImage (reflSymmetry C) b).target = reflSite C b.target :=
  congrArg Prod.snd (isBondImage_bondImage C b)
theorem bondImage_involutive :
    Function.Involutive (MirrorData.Symmetry.bondImage (reflSymmetry C)) := by
  intro b
  refine PeriodicLattice.Bond.ext ?_ ?_
  · rw [bondImage_source, bondImage_source, reflSite_reflSite]
  · rw [bondImage_target, bondImage_target, reflSite_reflSite]
theorem bondImage_opposite (b : D.DirectedBond) :
    MirrorData.Symmetry.bondImage (reflSymmetry C) b.opposite =
      (MirrorData.Symmetry.bondImage (reflSymmetry C) b).opposite :=
  PeriodicLattice.TorusLatticeSymmetry.bondMap_opposite _ b
theorem coe_axisUnit_eq_proj (i : Fin 4) :
    ((axisUnit D i : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)) : D.Torus) =
      D.proj (PlaquetteNondegeneracy.signedAxisStep D (i, 1)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [MirrorData.proj, TorusMetric.torusProj, PlaquetteNondegeneracy.signedAxisStep,
      PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, PeriodicLattice.coordVec,
      MirrorData.spacing]
  · simp [MirrorData.proj, TorusMetric.torusProj, PlaquetteNondegeneracy.signedAxisStep,
      PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, PeriodicLattice.coordVec,
      Pi.single_eq_of_ne hj]
theorem coe_neg_axisUnit_eq_proj (i : Fin 4) :
    (-(axisUnit D i : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)) : D.Torus) =
      D.proj (PlaquetteNondegeneracy.signedAxisStep D (i, -1)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [MirrorData.proj, TorusMetric.torusProj, PlaquetteNondegeneracy.signedAxisStep,
      PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, PeriodicLattice.coordVec,
      MirrorData.spacing]
  · simp [MirrorData.proj, TorusMetric.torusProj, PlaquetteNondegeneracy.signedAxisStep,
      PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, PeriodicLattice.coordVec,
      Pi.single_eq_of_ne hj]
theorem target_sub_source_of_positive (hD : PlaquetteNondegeneracy.BondAxisAndSign D)
    {b : D.DirectedBond} {i : Fin 4} (hp : b.IsPositivelyOriented) (hi : b.IsParallelToAxis i) :
    b.target - b.source = axisUnit D i := by
  obtain ⟨k, hk⟩ := hp
  have inj := hD.1
  have hcoe : ∀ d : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ), b.target - b.source = d →
      ((d : D.Torus)) = (b.target : D.Torus) - b.source := by
    intro d hd
    rw [← hd]
    rfl
  rcases hi with h | h
  · exact h
  · exfalso
    have e₁ := hcoe _ hk
    have e₂ := hcoe _ h
    have e : D.proj (PlaquetteNondegeneracy.signedAxisStep D (k, 1)) =
        D.proj (PlaquetteNondegeneracy.signedAxisStep D (i, -1)) := by
      rw [← coe_axisUnit_eq_proj, ← coe_neg_axisUnit_eq_proj]
      refine e₁.trans (e₂.symm.trans ?_)
      rfl
    have := inj e
    have hsign : (1 : ℤˣ) = -1 := congrArg Prod.snd this
    exact absurd hsign (by decide)
theorem actsOnBonds (hD : PlaquetteNondegeneracy.BondAxisAndSign D) :
    ActsOnBonds C (reflSymmetry C) := by
  refine ⟨fun b => ⟨congrArg Subtype.val (bondImage_source C b),
    congrArg Subtype.val (bondImage_target C b)⟩, bondImage_involutive C, bondImage_opposite C, ?_⟩
  intro b i hp hi
  have hd := target_sub_source_of_positive hD hp hi
  have hs := bondImage_source C b
  have ht := bondImage_target C b
  by_cases hdir : i = D.dir
  · subst hdir
    have e : (MirrorData.Symmetry.bondImage (reflSymmetry C) b).target -
        (MirrorData.Symmetry.bondImage (reflSymmetry C) b).source = -axisUnit D D.dir := by
      rw [hs, ht]
      exact reflSite_sub_dir C hd
    refine ⟨Or.inr e, fun hne => absurd rfl hne, fun _ => ?_⟩
    intro hpos
    have hopp : (MirrorData.Symmetry.bondImage (reflSymmetry C) b).opposite.IsPositivelyOriented := by
      refine ⟨D.dir, ?_⟩
      change (MirrorData.Symmetry.bondImage (reflSymmetry C) b).source -
        (MirrorData.Symmetry.bondImage (reflSymmetry C) b).target = _
      rw [← neg_sub, e, neg_neg]
    rcases (hD.2 (MirrorData.Symmetry.bondImage (reflSymmetry C) b)).2 with h₁ | h₁
    · exact h₁.2 hopp
    · exact h₁.2 hpos
  · have e : (MirrorData.Symmetry.bondImage (reflSymmetry C) b).target -
        (MirrorData.Symmetry.bondImage (reflSymmetry C) b).source = axisUnit D i := by
      rw [hs, ht]
      exact reflSite_sub_of_ne C hdir hd
    exact ⟨Or.inl e, fun _ => ⟨i, e⟩, fun hne => absurd hne hdir⟩
theorem pullback_pullback (U : D.BondField) :
    MirrorData.Symmetry.pullback (reflSymmetry C) (MirrorData.Symmetry.pullback (reflSymmetry C) U) =
      U := by
  funext b
  change U (MirrorData.Symmetry.bondImage (reflSymmetry C)
    (MirrorData.Symmetry.bondImage (reflSymmetry C) b)) = U b
  rw [bondImage_involutive C b]
theorem pullback_mem_gaugeFieldSpace {U : D.BondField} (hU : U ∈ gaugeFieldSpace D) :
    MirrorData.Symmetry.pullback (reflSymmetry C) U ∈ gaugeFieldSpace D := by
  refine ⟨fun b _ => hU.1 _ (mem_univ _), fun b _ => ?_⟩
  change U (MirrorData.Symmetry.bondImage (reflSymmetry C) b.opposite) =
    (U (MirrorData.Symmetry.bondImage (reflSymmetry C) b))⁻¹
  rw [bondImage_opposite]
  exact hU.2 _ (mem_univ _)
theorem continuous_pullback_restrict :
    Continuous fun U : gaugeFieldSpace D =>
      (⟨MirrorData.Symmetry.pullback (reflSymmetry C) U.1, pullback_mem_gaugeFieldSpace C U.2⟩ :
        gaugeFieldSpace D) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun b => ?_
  exact (continuous_apply (MirrorData.Symmetry.bondImage (reflSymmetry C) b)).comp
    continuous_subtype_val
theorem actsOnGaugeFields : ActsOnGaugeFields (reflSymmetry C) := by
  refine ⟨fun U hU => ⟨pullback_mem_gaugeFieldSpace C hU, fun b => rfl, pullback_pullback C U⟩, ?_⟩
  exact ⟨{ toFun := fun U => ⟨_, pullback_mem_gaugeFieldSpace C U.2⟩
           invFun := fun U => ⟨_, pullback_mem_gaugeFieldSpace C U.2⟩
           left_inv := fun U => Subtype.ext (pullback_pullback C U.1)
           right_inv := fun U => Subtype.ext (pullback_pullback C U.1)
           continuous_toFun := continuous_pullback_restrict C
           continuous_invFun := continuous_pullback_restrict C }, fun U => rfl⟩
theorem quad_eq_of_first_reversed {G : Type*} [AddCommGroup G] (w e f : G) :
    ({w - e, w - e + e, w - e + e + f, w - e + f} : Set G) = {w, w - e, w - e + f, w + f} := by
  have h₁ : w - e + e = w := by abel
  rw [h₁]
  ext y
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto
theorem quad_eq_of_second_reversed {G : Type*} [AddCommGroup G] (w e f : G) :
    ({w - f, w - f + e, w - f + e + f, w - f + f} : Set G) = {w, w + e, w + e - f, w - f} := by
  have h₁ : w - f + f = w := by abel
  have h₂ : w - f + e + f = w + e := by abel
  have h₃ : w - f + e = w + e - f := by abel
  rw [h₁, h₂, h₃]
  ext y
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto
def reflFace (p : D.Face) : D.Face :=
  if D.dir = p.firstAxis ∨ D.dir = p.secondAxis then
    ⟨reflSite C p.origin - axisUnit D D.dir, p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩
  else ⟨reflSite C p.origin, p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩
theorem reflFace_vertices (p : D.Face) :
    (reflFace C p).vertices = reflSite C '' p.vertices := by
  obtain ⟨x, i, j, hij⟩ := p
  by_cases h₁ : D.dir = i
  · subst h₁
    have hj : j ≠ D.dir := hij.ne'
    have a₁ : reflSite C (x + axisUnit D D.dir) = reflSite C x - axisUnit D D.dir :=
      reflSite_add_axisUnit_dir C x
    have a₂ : reflSite C (x + axisUnit D D.dir + axisUnit D j) =
        reflSite C x - axisUnit D D.dir + axisUnit D j := by
      rw [reflSite_add_axisUnit C _ hj, a₁]
    have a₃ : reflSite C (x + axisUnit D j) = reflSite C x + axisUnit D j :=
      reflSite_add_axisUnit C x hj
    have img : reflSite C '' ({x, x + axisUnit D D.dir, x + axisUnit D D.dir + axisUnit D j,
        x + axisUnit D j} : Set (PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ))) =
        {reflSite C x, reflSite C x - axisUnit D D.dir,
          reflSite C x - axisUnit D D.dir + axisUnit D j, reflSite C x + axisUnit D j} := by
      rw [image_insert_eq, image_insert_eq, image_insert_eq, image_singleton, a₁, a₂, a₃]
    rw [reflFace, if_pos (Or.inl rfl)]
    exact (quad_eq_of_first_reversed _ _ _).trans img.symm
  · by_cases h₂ : D.dir = j
    · subst h₂
      have hi : i ≠ D.dir := hij.ne
      have a₁ : reflSite C (x + axisUnit D i) = reflSite C x + axisUnit D i :=
        reflSite_add_axisUnit C x hi
      have a₂ : reflSite C (x + axisUnit D i + axisUnit D D.dir) =
          reflSite C x + axisUnit D i - axisUnit D D.dir := by
        rw [reflSite_add_axisUnit_dir, a₁]
      have a₃ : reflSite C (x + axisUnit D D.dir) = reflSite C x - axisUnit D D.dir :=
        reflSite_add_axisUnit_dir C x
      have img : reflSite C '' ({x, x + axisUnit D i, x + axisUnit D i + axisUnit D D.dir,
          x + axisUnit D D.dir} : Set (PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ))) =
          {reflSite C x, reflSite C x + axisUnit D i,
            reflSite C x + axisUnit D i - axisUnit D D.dir, reflSite C x - axisUnit D D.dir} := by
        rw [image_insert_eq, image_insert_eq, image_insert_eq, image_singleton, a₁, a₂, a₃]
      rw [reflFace, if_pos (Or.inr rfl)]
      exact (quad_eq_of_second_reversed _ _ _).trans img.symm
    · have hi : i ≠ D.dir := Ne.symm h₁
      have hj : j ≠ D.dir := Ne.symm h₂
      have a₁ : reflSite C (x + axisUnit D i) = reflSite C x + axisUnit D i :=
        reflSite_add_axisUnit C x hi
      have a₂ : reflSite C (x + axisUnit D i + axisUnit D j) =
          reflSite C x + axisUnit D i + axisUnit D j := by
        rw [reflSite_add_axisUnit C _ hj, a₁]
      have a₃ : reflSite C (x + axisUnit D j) = reflSite C x + axisUnit D j :=
        reflSite_add_axisUnit C x hj
      have img : reflSite C '' ({x, x + axisUnit D i, x + axisUnit D i + axisUnit D j,
          x + axisUnit D j} : Set (PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ))) =
          {reflSite C x, reflSite C x + axisUnit D i, reflSite C x + axisUnit D i + axisUnit D j,
            reflSite C x + axisUnit D j} := by
        rw [image_insert_eq, image_insert_eq, image_insert_eq, image_singleton, a₁, a₂, a₃]
      rw [reflFace, if_neg (by simpa using ⟨h₁, h₂⟩)]
      exact img.symm
theorem isFaceImage_reflSymmetry (p : D.Face) :
    MirrorData.Symmetry.IsFaceImage (reflSymmetry C) p
      (MirrorData.Symmetry.faceImage (reflSymmetry C) p) :=
  MirrorData.Symmetry.isFaceImage_faceImage _ ⟨reflFace C p, reflFace_vertices C p⟩
theorem faceImage_eq_reflFace (hC : PlaquetteNondegeneracy.PlaquetteVerticesDistinct D)
    (p : D.Face) : MirrorData.Symmetry.faceImage (reflSymmetry C) p = reflFace C p :=
  (hC _).2 _ ((isFaceImage_reflSymmetry C p).trans (reflFace_vertices C p).symm)
theorem faceImage_involutive (hC : PlaquetteNondegeneracy.PlaquetteVerticesDistinct D) :
    Function.Involutive (MirrorData.Symmetry.faceImage (reflSymmetry C)) := by
  intro p
  refine (hC _).2 _ ?_
  have e₁ := isFaceImage_reflSymmetry C p
  have e₂ := isFaceImage_reflSymmetry C (MirrorData.Symmetry.faceImage (reflSymmetry C) p)
  have e₁' : (MirrorData.Symmetry.faceImage (reflSymmetry C) p).vertices =
      reflSite C '' p.vertices := e₁
  have e₂' : (MirrorData.Symmetry.faceImage (reflSymmetry C)
      (MirrorData.Symmetry.faceImage (reflSymmetry C) p)).vertices =
      reflSite C '' (MirrorData.Symmetry.faceImage (reflSymmetry C) p).vertices := e₂
  rw [e₂', e₁', image_image]
  simp only [reflSite_reflSite, image_id']
theorem axisFlip_pointOnAxis_of_ne {i : Fin 4} (hi : i ≠ D.dir) (t : ℝ) :
    axisFlip (PeriodicLattice.pointOnAxis D.L D.m i t : D.Torus) =
      PeriodicLattice.pointOnAxis D.L D.m i t := by
  funext j
  by_cases hj : j = D.dir
  · subst hj
    simp [axisFlip, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne (Ne.symm hi)]
  · simp [axisFlip, Function.update_of_ne hj]
theorem axisFlip_pointOnAxis_dir (t : ℝ) :
    axisFlip (PeriodicLattice.pointOnAxis D.L D.m D.dir t : D.Torus) =
      -PeriodicLattice.pointOnAxis D.L D.m D.dir t := by
  funext j
  by_cases hj : j = D.dir
  · subst hj
    simp [axisFlip]
  · simp [axisFlip, Function.update_of_ne hj, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hj]
theorem pointOnAxis_eq_half_add_half (i : Fin 4) (t : ℝ) :
    (PeriodicLattice.pointOnAxis D.L D.m i t : D.Torus) =
      PeriodicLattice.pointOnAxis D.L D.m i (t / 2) +
        PeriodicLattice.pointOnAxis D.L D.m i (t / 2) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [PeriodicLattice.pointOnAxis, Pi.add_apply, Pi.single_eq_same, ← AddCircle.coe_add]
    congr 1
    ring
  · simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hj]
theorem reflFace_barycenter (p : D.Face) :
    (reflFace C p).barycenter = C.refl p.barycenter := by
  obtain ⟨x, i, j, hij⟩ := p
  simp only [PeriodicLattice.Plaquette.barycenter]
  rw [refl_add, refl_add]
  by_cases h₁ : D.dir = i
  · subst h₁
    have hj : j ≠ D.dir := hij.ne'
    rw [reflFace, if_pos (Or.inl rfl), axisFlip_pointOnAxis_dir, axisFlip_pointOnAxis_of_ne hj]
    change (C.refl x - PeriodicLattice.pointOnAxis D.L D.m D.dir
      (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ))) + _ + _ = _
    rw [pointOnAxis_eq_half_add_half D.dir (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ))]
    abel
  · by_cases h₂ : D.dir = j
    · subst h₂
      have hi : i ≠ D.dir := hij.ne
      rw [reflFace, if_pos (Or.inr rfl), axisFlip_pointOnAxis_dir, axisFlip_pointOnAxis_of_ne hi]
      change (C.refl x - PeriodicLattice.pointOnAxis D.L D.m D.dir
        (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ))) + _ + _ = _
      rw [pointOnAxis_eq_half_add_half D.dir (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ))]
      abel
    · rw [reflFace, if_neg (by simpa using ⟨h₁, h₂⟩), axisFlip_pointOnAxis_of_ne (Ne.symm h₁),
        axisFlip_pointOnAxis_of_ne (Ne.symm h₂)]
      rfl
theorem plaquetteEnergy_pullback
    (hE : PlaquetteNondegeneracy.TraceIndependentOfTraversal D)
    {U : D.BondField} (hU : U ∈ gaugeFieldSpace D) (p : D.Face) :
    PeriodicLattice.plaquetteCost (MirrorData.Symmetry.pullback (reflSymmetry C) U) p =
      PeriodicLattice.plaquetteCost U (MirrorData.Symmetry.faceImage (reflSymmetry C) p) := by
  obtain ⟨x, i, j, hij⟩ := p
  have hvert : ({reflSite C x, reflSite C (x + axisUnit D i),
      reflSite C (x + axisUnit D i + axisUnit D j), reflSite C (x + axisUnit D j)} :
        Set (PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ))) =
      (MirrorData.Symmetry.faceImage (reflSymmetry C) ⟨x, i, j, hij⟩).vertices := by
    have e : (MirrorData.Symmetry.faceImage (reflSymmetry C) ⟨x, i, j, hij⟩).vertices =
        reflSite C '' ({x, x + axisUnit D i, x + axisUnit D i + axisUnit D j, x + axisUnit D j} :
          Set (PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ))) :=
      isFaceImage_reflSymmetry C ⟨x, i, j, hij⟩
    rw [e, image_insert_eq, image_insert_eq, image_insert_eq, image_singleton]
  have key := hE (MirrorData.Symmetry.faceImage (reflSymmetry C) ⟨x, i, j, hij⟩)
    (reflSite C x) (reflSite C (x + axisUnit D i)) (reflSite C (x + axisUnit D i + axisUnit D j))
    (reflSite C (x + axisUnit D j))
    (MirrorData.Symmetry.bondImage (reflSymmetry C) (PeriodicLattice.Bond.forwardFrom x i))
    (MirrorData.Symmetry.bondImage (reflSymmetry C)
      (PeriodicLattice.Bond.forwardFrom (x + axisUnit D i) j))
    (MirrorData.Symmetry.bondImage (reflSymmetry C)
      (PeriodicLattice.Bond.forwardFrom (x + axisUnit D j) i).opposite)
    (MirrorData.Symmetry.bondImage (reflSymmetry C) (PeriodicLattice.Bond.forwardFrom x j).opposite)
    hvert (bondImage_source C _) (bondImage_target C _) (bondImage_source C _)
    (bondImage_target C _)
    (by
      rw [bondImage_source]
      exact congrArg (reflSite C)
        (show x + axisUnit D j + axisUnit D i = x + axisUnit D i + axisUnit D j by abel))
    (bondImage_target C _) (bondImage_source C _) (bondImage_target C _) U hU
  have hhol : PeriodicLattice.plaquetteHolonomy (MirrorData.Symmetry.pullback (reflSymmetry C) U)
      ⟨x, i, j, hij⟩ =
      U (MirrorData.Symmetry.bondImage (reflSymmetry C) (PeriodicLattice.Bond.forwardFrom x i)) *
        U (MirrorData.Symmetry.bondImage (reflSymmetry C)
          (PeriodicLattice.Bond.forwardFrom (x + axisUnit D i) j)) *
        U (MirrorData.Symmetry.bondImage (reflSymmetry C)
          (PeriodicLattice.Bond.forwardFrom (x + axisUnit D j) i).opposite) *
        U (MirrorData.Symmetry.bondImage (reflSymmetry C)
          (PeriodicLattice.Bond.forwardFrom x j).opposite) := by
    simp [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
      PeriodicLattice.Plaquette.boundaryBonds, MirrorData.Symmetry.pullback, mul_assoc]
  rw [PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteCost, hhol, key]
theorem actsOnPlaquettes (hC : PlaquetteNondegeneracy.PlaquetteVerticesDistinct D)
    (hE : PlaquetteNondegeneracy.TraceIndependentOfTraversal D) :
    ActsOnPlaquettes C (reflSymmetry C) := by
  have hbar : ∀ p : D.Face,
      (MirrorData.Symmetry.faceImage (reflSymmetry C) p).barycenter = C.refl p.barycenter :=
    fun p => by rw [faceImage_eq_reflFace C hC, reflFace_barycenter]
  refine ⟨isFaceImage_reflSymmetry C, faceImage_involutive C hC, hbar,
    fun U hU p => plaquetteEnergy_pullback C hE hU p, ?_⟩
  intro E _ _ f _ U hU
  simp only [PeriodicLattice.smearedObservable]
  rw [← finsum_comp_equiv (faceImage_involutive C hC).toPerm]
  refine finsum_congr fun p => ?_
  simp only [Function.Involutive.coe_toPerm, Function.comp_apply]
  rw [plaquetteEnergy_pullback C hE hU, faceImage_involutive C hC p, hbar p]
abbrev reflPerm : D.Torus ≃ D.Torus := (refl_involutive C).toPerm
theorem reflPerm_isSublatticeIsometry :
    PeriodicLattice.IsSublatticeIsometry ((D.K : ℕ) : ℤ) (reflPerm C) :=
  ⟨fun x y => refl_isDistPreserving C x y, refl_image_latticeSubgroup C⟩
theorem pullback_eq_transport :
    MirrorData.Symmetry.pullback (reflSymmetry C) =
      PeriodicLattice.transportGaugeField (reflPerm C) := by
  funext U
  have h := MirrorData.Symmetry.pullback_eq_transportGaugeField (reflSymmetry C) (reflPerm C)
    (fun _ => rfl) (exists_isBondImage C) U
  rwa [Function.Involutive.toPerm_symm] at h
def pullbackMeasurableEquiv : D.BondField ≃ᵐ D.BondField where
  toFun := MirrorData.Symmetry.pullback (reflSymmetry C)
  invFun := MirrorData.Symmetry.pullback (reflSymmetry C)
  left_inv := pullback_pullback C
  right_inv := pullback_pullback C
  measurable_toFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
theorem gibbsExpectation_comp_pullback (hI : PeriodicLattice.WilsonMeasureIsometryInvariant)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : D.BondField → E) :
    PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
        (F ∘ MirrorData.Symmetry.pullback (reflSymmetry C)) =
      PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling F := by
  have hL : 1 < D.L := lt_of_lt_of_le (by norm_num) D.isAdmissible.2
  have hmap := ((hI D.L D.m D.K D.coupling hL D.m.pos D.K.pos).2.2 (reflPerm C)
    (reflPerm_isSublatticeIsometry C)).2.2
  rw [← pullback_eq_transport] at hmap
  have e := (pullbackMeasurableEquiv C).measurableEmbedding.integral_map
    (μ := PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling) F
  have e' : Measure.map (⇑(pullbackMeasurableEquiv C))
      (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling) =
      PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling := hmap
  rw [e'] at e
  exact e.symm
theorem preservesExpectations (hI : PeriodicLattice.WilsonMeasureIsometryInvariant) :
    PreservesExpectations (reflSymmetry C) :=
  ⟨fun F _ => gibbsExpectation_comp_pullback C hI F,
    fun F _ => gibbsExpectation_comp_pullback C hI F⟩
theorem linkReflectionProperties_of_nondegeneracy
    (hN : PlaquetteNondegeneracy.NondegeneracyStatement)
    (hI : PeriodicLattice.WilsonMeasureIsometryInvariant) : LinkReflectionProperties := by
  intro D C
  obtain ⟨-, hB, hC, -, hE⟩ := hN D
  exact ⟨actsOnTorus C, reflSymmetry C, rfl, actsOnBonds C hB, actsOnGaugeFields C,
    actsOnPlaquettes C hC hE, preservesExpectations C hI⟩
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkReflection
end

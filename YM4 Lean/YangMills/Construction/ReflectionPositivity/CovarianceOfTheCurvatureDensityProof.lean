import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfASpacingAndTheirActions
import YangMills.Construction.Lattice.IsometryInvarianceOfWilsonMeasure
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.ReflectionPositivity.BondsAndPlaquettesAreNotDegenerate
import YangMills.Construction.ReflectionPositivity.CovarianceOfTheCurvatureDensity
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance
open MirrorData.Symmetry
variable {D : MirrorData}
abbrev LatticeSite (D : MirrorData) : Type := PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)
abbrev latticeStep (D : MirrorData) (ν : Fin 4) : LatticeSite D :=
  PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) ν
abbrev frameAction (D : MirrorData) (R : PeriodicLattice.SignedFrame) : D.Torus ≃ D.Torus :=
  PeriodicLattice.SignedFrame.torusEquiv D.L D.m R
theorem frameAction_apply (R : PeriodicLattice.SignedFrame) (y : D.Torus) (μ : Fin 4) :
    frameAction D R y μ = ((R.2 μ : ℤˣ) : ℤ) • y (R.1 μ) := rfl
theorem frameAction_add (R : PeriodicLattice.SignedFrame) (x y : D.Torus) :
    frameAction D R (x + y) = frameAction D R x + frameAction D R y := by
  funext μ
  simp [frameAction_apply, smul_add]
theorem proj_add (x y : Fin 4 → ℝ) : D.proj (x + y) = D.proj x + D.proj y := by
  funext μ
  simp [MirrorData.proj, TorusMetric.torusProj]
theorem proj_surjective : Function.Surjective D.proj := by
  intro y
  have hs : ∀ κ, ∃ t : ℝ, (t : D.CircleCoord) = y κ := fun κ =>
    QuotientAddGroup.mk_surjective (y κ)
  choose t ht using hs
  exact ⟨t, funext ht⟩
theorem frameAction_proj (R : PeriodicLattice.SignedFrame) (x : Fin 4 → ℝ) :
    frameAction D R (D.proj x) = D.proj (R.actOnVector x) := by
  funext μ
  rw [frameAction_apply]
  simp only [MirrorData.proj, TorusMetric.torusProj, PeriodicLattice.SignedFrame.actOnVector]
  rcases Int.units_eq_one_or (R.2 μ) with h | h <;> simp [h]
theorem frameAction_pointOnAxis (R : PeriodicLattice.SignedFrame) (ν : Fin 4) (t : ℝ) :
    frameAction D R (PeriodicLattice.pointOnAxis D.L D.m ν t) =
      ((R.2 (R.1.symm ν) : ℤˣ) : ℤ) • PeriodicLattice.pointOnAxis D.L D.m (R.1.symm ν) t := by
  funext μ
  rw [frameAction_apply]
  by_cases h : μ = R.1.symm ν
  · subst h
    simp [PeriodicLattice.pointOnAxis]
  · have h' : R.1 μ ≠ ν := fun e => h (by rw [← e]; simp)
    simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
theorem isSublatticeIsometry_symm {σ : D.Torus ≃ D.Torus}
    (h : PeriodicLattice.IsSublatticeIsometry ((D.K : ℕ) : ℤ) σ) :
    PeriodicLattice.IsSublatticeIsometry ((D.K : ℕ) : ℤ) σ.symm := by
  refine ⟨fun x y => ?_, ?_⟩
  · have := h.1 (σ.symm x) (σ.symm y)
    simpa using this.symm
  · conv_lhs => rw [← h.2]
    rw [← image_comp]
    simp
theorem isSublatticeIsometry_trans {σ τ : D.Torus ≃ D.Torus}
    (h : PeriodicLattice.IsSublatticeIsometry ((D.K : ℕ) : ℤ) σ)
    (h' : PeriodicLattice.IsSublatticeIsometry ((D.K : ℕ) : ℤ) τ) :
    PeriodicLattice.IsSublatticeIsometry ((D.K : ℕ) : ℤ) (σ.trans τ) := by
  refine ⟨fun x y => ?_, ?_⟩
  · simpa using (h'.1 (σ x) (σ y)).trans (h.1 x y)
  · rw [Equiv.coe_trans, image_comp, h.2, h'.2]
def symmetryOfEquiv (σ : D.Torus ≃ D.Torus)
    (h : PeriodicLattice.IsSublatticeIsometry ((D.K : ℕ) : ℤ) σ) : D.Symmetry where
  toFun := σ
  dist_eq := h.1
  image_eq := h.2
def frameAffine (D : MirrorData) (R : PeriodicLattice.SignedFrame) (c : D.Torus) :
    D.Torus ≃ D.Torus :=
  (frameAction D R).trans (Equiv.addRight c)
theorem frameAffine_apply (R : PeriodicLattice.SignedFrame) (c y : D.Torus) :
    frameAffine D R c y = frameAction D R y + c := rfl
theorem one_lt_blockFactor (D : MirrorData) : 1 < D.L :=
  lt_of_lt_of_le (by norm_num) D.isAdmissible.2
theorem frameAffine_isSublatticeIsometry (hI : PeriodicLattice.WilsonMeasureIsometryInvariant)
    (R : PeriodicLattice.SignedFrame) {c : D.Torus} (hc : c ∈ D.latticeSubgroup) :
    PeriodicLattice.IsSublatticeIsometry ((D.K : ℕ) : ℤ) (frameAffine D R c) := by
  obtain ⟨h₁, h₂, -⟩ := hI D.L D.m D.K D.coupling (one_lt_blockFactor D) D.m.pos D.K.pos
  exact isSublatticeIsometry_trans (h₂ _ ⟨R.1, R.2, rfl⟩) (h₁ ⟨c, hc⟩)
theorem proj_mem_latticeSubgroup {v : Fin 4 → ℝ}
    (hv : v ∈ PeriodicLattice.meshVectors D.L ((D.K : ℕ) : ℤ)) : D.proj v ∈ D.latticeSubgroup := by
  obtain ⟨n, hn⟩ := hv
  refine ⟨n, fun μ => ?_⟩
  simp only [MirrorData.proj, TorusMetric.torusProj]
  rw [hn μ]
theorem isAffine_of_symmetry (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (s : D.Symmetry) : IsAffine s := by
  have hL : 0 < D.L := lt_trans Nat.zero_lt_one (one_lt_blockFactor D)
  obtain ⟨-, -, -, h, -⟩ := hT D.L hL D.isAdmissible (D.K : ℕ)
  have hs : Tower.MapsSublatticeOnto (D.K : ℕ) 0 s.toFun := by
    simpa [Tower.MapsSublatticeOnto, PeriodicLattice.levelDepth] using s.image_eq
  obtain ⟨w, hw, v, hv, e⟩ := (h (D.m : ℕ) D.m.pos 0 (Nat.zero_le _) s.toFun s.dist_eq hs).1
  obtain ⟨r, hr⟩ := InfiniteLattice.exists_frameLinearMap_eq_of_mem_hypercubicGroup
    ((InfiniteLattice.linearMap_mem_hypercubicGroup_iff w).mpr hw)
  refine ⟨r, v, ?_, fun x => ?_⟩
  · obtain ⟨n, hn⟩ := hv
    refine ⟨n, fun μ => ?_⟩
    rw [hn μ]
    simp [Tower.meshAt, PeriodicLattice.meshSize]
  · have e' := e x
    have hw' : w x = r.actOnVector x := LinearMap.congr_fun hr x
    rw [hw'] at e'
    exact e'
theorem exists_frameAffine_eq (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (s : D.Symmetry) :
    ∃ R : PeriodicLattice.SignedFrame, ∃ v ∈ PeriodicLattice.meshVectors D.L ((D.K : ℕ) : ℤ),
      ∀ y, s.toFun y = frameAffine D R (D.proj v) y := by
  obtain ⟨R, v, hv, h⟩ := isAffine_of_symmetry hT s
  refine ⟨R, v, hv, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := proj_surjective y
  rw [h x, frameAffine_apply, frameAction_proj, proj_add]
theorem affineMapsExhaustSymmetries
    (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hI : PeriodicLattice.WilsonMeasureIsometryInvariant) (D : MirrorData) :
    AffineMapsExhaustSymmetries D := by
  have mk : ∀ (R : PeriodicLattice.SignedFrame) (v : Fin 4 → ℝ)
      (_ : v ∈ PeriodicLattice.meshVectors D.L ((D.K : ℕ) : ℤ)), ∀ x : Fin 4 → ℝ,
      frameAffine D R (D.proj v) (D.proj x) = D.proj (R.actOnVector x + v) := by
    intro R v _ x
    rw [frameAffine_apply, frameAction_proj, proj_add]
  refine ⟨fun R v hv =>
    ⟨symmetryOfEquiv _ (frameAffine_isSublatticeIsometry hI R (proj_mem_latticeSubgroup hv)),
      fun x => mk R v hv x⟩, ?_⟩
  apply Subset.antisymm
  · rintro _ ⟨s, rfl⟩
    obtain ⟨R, v, hv, h⟩ := exists_frameAffine_eq hT s
    refine ⟨frameAffine D R (D.proj v), ⟨R, v, hv, fun x => mk R v hv x⟩, ?_⟩
    exact (funext h).symm
  · rintro _ ⟨σ, ⟨R, v, hv, h⟩, rfl⟩
    refine ⟨symmetryOfEquiv _ (frameAffine_isSublatticeIsometry hI R (proj_mem_latticeSubgroup hv)), ?_⟩
    funext y
    obtain ⟨x, rfl⟩ := proj_surjective y
    exact (mk R v hv x).trans (h x).symm
structure SymmetryPair (D : MirrorData) where
  fwd : D.Symmetry
  bwd : D.Symmetry
  bwd_fwd : ∀ x, bwd.toFun (fwd.toFun x) = x
  fwd_bwd : ∀ x, fwd.toFun (bwd.toFun x) = x
  exists_bondImage_fwd : ∀ b : D.DirectedBond,
    ∃ b', PeriodicLattice.TorusLatticeSymmetry.IsBondImage fwd b b'
  exists_bondImage_bwd : ∀ b : D.DirectedBond,
    ∃ b', PeriodicLattice.TorusLatticeSymmetry.IsBondImage bwd b b'
  affine_fwd : ∃ (R : PeriodicLattice.SignedFrame) (c : D.Torus),
    ∀ y, fwd.toFun y = frameAffine D R c y
  affine_bwd : ∃ (R : PeriodicLattice.SignedFrame) (c : D.Torus),
    ∀ y, bwd.toFun y = frameAffine D R c y
theorem exists_isBondImage (hI : PeriodicLattice.WilsonMeasureIsometryInvariant)
    {τ : D.Torus ≃ D.Torus} (hτ : PeriodicLattice.IsSublatticeIsometry ((D.K : ℕ) : ℤ) τ)
    (u : D.Symmetry) (hu : ∀ y, u.toFun y = τ y) (b : D.DirectedBond) :
    ∃ b', PeriodicLattice.TorusLatticeSymmetry.IsBondImage u b b' := by
  obtain ⟨-, -, h⟩ := hI D.L D.m D.K D.coupling (one_lt_blockFactor D) D.m.pos D.K.pos
  obtain ⟨h₁, h₂⟩ := (h τ.symm (isSublatticeIsometry_symm hτ)).1 b
  refine ⟨PeriodicLattice.bondPreimage τ.symm b, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · exact h₁.trans (hu _).symm
  · exact h₂.trans (hu _).symm
theorem exists_symmetryPair
    (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hI : PeriodicLattice.WilsonMeasureIsometryInvariant) (s : D.Symmetry) :
    ∃ P : SymmetryPair D, P.fwd = s := by
  obtain ⟨R, v, hv, h⟩ := exists_frameAffine_eq hT s
  have hσ := frameAffine_isSublatticeIsometry hI R (proj_mem_latticeSubgroup hv)
  set σ := frameAffine D R (D.proj v) with hσd
  let t : D.Symmetry := symmetryOfEquiv σ.symm (isSublatticeIsometry_symm hσ)
  have ht : ∀ y, t.toFun y = σ.symm y := fun _ => rfl
  obtain ⟨R', v', -, h'⟩ := exists_frameAffine_eq hT t
  exact ⟨⟨s, t, fun x => by rw [h, ht]; simp, fun x => by rw [h, ht]; simp,
    exists_isBondImage hI hσ s h, exists_isBondImage hI (isSublatticeIsometry_symm hσ) t ht,
    ⟨R, _, h⟩, ⟨R', _, h'⟩⟩, rfl⟩
namespace SymmetryPair
variable (P : SymmetryPair D)
def symm : SymmetryPair D :=
  ⟨P.bwd, P.fwd, P.fwd_bwd, P.bwd_fwd, P.exists_bondImage_bwd, P.exists_bondImage_fwd,
    P.affine_bwd, P.affine_fwd⟩
def toEquiv : D.Torus ≃ D.Torus := ⟨P.fwd.toFun, P.bwd.toFun, P.bwd_fwd, P.fwd_bwd⟩
theorem isSublatticeIsometry : PeriodicLattice.IsSublatticeIsometry ((D.K : ℕ) : ℤ) P.toEquiv :=
  ⟨P.fwd.dist_eq, P.fwd.image_eq⟩
abbrev vertexMap (x : LatticeSite D) : LatticeSite D :=
  PeriodicLattice.TorusLatticeSymmetry.pointMap P.fwd x
theorem symm_vertexMap_vertexMap (x : LatticeSite D) : P.symm.vertexMap (P.vertexMap x) = x :=
  Subtype.ext (P.bwd_fwd x)
theorem isBondImage_bondImage (b : D.DirectedBond) :
    PeriodicLattice.TorusLatticeSymmetry.IsBondImage P.fwd b (bondImage P.fwd b) := by
  obtain ⟨b', h⟩ := P.exists_bondImage_fwd b
  rwa [bondImage_eq _ h]
theorem bondImage_source (b : D.DirectedBond) :
    (bondImage P.fwd b).source = P.vertexMap b.source :=
  congrArg Prod.fst (P.isBondImage_bondImage b)
theorem bondImage_target (b : D.DirectedBond) :
    (bondImage P.fwd b).target = P.vertexMap b.target :=
  congrArg Prod.snd (P.isBondImage_bondImage b)
theorem bondImage_bwd_fwd (b : D.DirectedBond) : bondImage P.bwd (bondImage P.fwd b) = b := by
  refine PeriodicLattice.Bond.ext ?_ ?_
  · exact (P.symm.bondImage_source (bondImage P.fwd b)).trans
      ((congrArg P.symm.vertexMap (P.bondImage_source b)).trans (P.symm_vertexMap_vertexMap _))
  · exact (P.symm.bondImage_target (bondImage P.fwd b)).trans
      ((congrArg P.symm.vertexMap (P.bondImage_target b)).trans (P.symm_vertexMap_vertexMap _))
theorem bondImage_fwd_bwd (b : D.DirectedBond) : bondImage P.fwd (bondImage P.bwd b) = b :=
  P.symm.bondImage_bwd_fwd b
theorem bondImage_opposite (b : D.DirectedBond) :
    bondImage P.fwd b.opposite = (bondImage P.fwd b).opposite :=
  PeriodicLattice.TorusLatticeSymmetry.bondMap_opposite _ b
theorem actsOnBonds : ActsOnBonds P.fwd :=
  ⟨Function.bijective_iff_has_inverse.mpr
      ⟨bondImage P.bwd, P.bondImage_bwd_fwd, P.bondImage_fwd_bwd⟩,
    P.bondImage_opposite⟩
theorem pullback_bwd_fwd (U : D.BondField) : pullback P.bwd (pullback P.fwd U) = U := by
  funext b
  change U (bondImage P.fwd (bondImage P.bwd b)) = U b
  rw [P.bondImage_fwd_bwd]
theorem pullback_fwd_bwd (U : D.BondField) : pullback P.fwd (pullback P.bwd U) = U :=
  P.symm.pullback_bwd_fwd U
theorem pullback_mem_gaugeFieldSet {U : D.BondField} (hU : U ∈ gaugeFieldSet D) :
    pullback P.fwd U ∈ gaugeFieldSet D := by
  refine ⟨fun b _ => hU.1 _ (mem_univ _), fun b _ => ?_⟩
  change U (bondImage P.fwd b.opposite) = (U (bondImage P.fwd b))⁻¹
  rw [P.bondImage_opposite]
  exact hU.2 _ (mem_univ _)
theorem continuous_pullback :
    Continuous fun U : gaugeFieldSet D =>
      (⟨pullback P.fwd U.1, P.pullback_mem_gaugeFieldSet U.2⟩ : gaugeFieldSet D) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun b => ?_
  exact (continuous_apply (bondImage P.fwd b)).comp continuous_subtype_val
theorem pullback_eq_transport :
    pullback P.fwd = PeriodicLattice.transportGaugeField P.symm.toEquiv :=
  funext fun U =>
    pullback_eq_transportGaugeField P.fwd P.toEquiv (fun _ => rfl) P.exists_bondImage_fwd U
theorem actsOnGaugeFields : ActsOnGaugeFields P.fwd P.bwd := by
  refine ⟨fun U hU =>
    ⟨P.pullback_mem_gaugeFieldSet hU, P.pullback_bwd_fwd U, P.pullback_fwd_bwd U⟩, ?_, ?_⟩
  · exact ⟨{ toFun := fun U => ⟨_, P.pullback_mem_gaugeFieldSet U.2⟩
             invFun := fun U => ⟨_, P.symm.pullback_mem_gaugeFieldSet U.2⟩
             left_inv := fun U => Subtype.ext (P.pullback_bwd_fwd U.1)
             right_inv := fun U => Subtype.ext (P.pullback_fwd_bwd U.1)
             continuous_toFun := P.continuous_pullback
             continuous_invFun := P.symm.continuous_pullback }, fun U => rfl⟩
  · exact ⟨P.symm.toEquiv, rfl, fun U _ => congrFun P.pullback_eq_transport U⟩
end SymmetryPair
abbrev halfStep (D : MirrorData) (α : Fin 4) : D.Torus :=
  PeriodicLattice.pointOnAxis D.L D.m α (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ) / 2)
theorem coe_latticeStep (α : Fin 4) :
    ((latticeStep D α : LatticeSite D) : D.Torus) = halfStep D α + halfStep D α := by
  funext κ
  by_cases h : κ = α
  · subst h
    simp only [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.add_apply,
      Pi.single_eq_same, ← AddCircle.coe_add]
    congr 1
    ring
  · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
section Corners
variable {G : Type*} [AddCommGroup G] (y e f : G)
theorem quad_neg_first :
    ({y - e, y - e + e, y - e + e + f, y - e + f} : Set G) = {y, y + -e, y + -e + f, y + f} := by
  have h₁ : y - e + e = y := by abel
  have h₂ : y - e = y + -e := by abel
  rw [h₁, h₂]
  ext w
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto
theorem quad_neg_second :
    ({y - f, y - f + e, y - f + e + f, y - f + f} : Set G) = {y, y + e, y + e + -f, y + -f} := by
  have h₁ : y - f + f = y := by abel
  have h₂ : y - f + e + f = y + e := by abel
  have h₃ : y - f + e = y + e + -f := by abel
  have h₄ : y - f = y + -f := by abel
  rw [h₁, h₂, h₃, h₄]
  ext w
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto
theorem quad_neg_both :
    ({y - e - f, y - e - f + e, y - e - f + e + f, y - e - f + f} : Set G) =
      {y, y + -e, y + -e + -f, y + -f} := by
  have h₁ : y - e - f + e + f = y := by abel
  have h₂ : y - e - f + e = y + -f := by abel
  have h₃ : y - e - f + f = y + -e := by abel
  have h₄ : y - e - f = y + -e + -f := by abel
  rw [h₁, h₂, h₃, h₄]
  ext w
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto
theorem quad_swap :
    ({y, y + f, y + f + e, y + e} : Set G) = {y, y + e, y + e + f, y + f} := by
  have h₁ : y + f + e = y + e + f := by abel
  rw [h₁]
  ext w
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto
end Corners
theorem exists_face_of_lt (y : LatticeSite D) {α β : Fin 4} (h : α < β) (ε ε' : ℤˣ) :
    ∃ p : D.Face,
      p.vertices = {y, y + (ε : ℤ) • latticeStep D α,
        y + (ε : ℤ) • latticeStep D α + (ε' : ℤ) • latticeStep D β,
        y + (ε' : ℤ) • latticeStep D β} ∧
      p.barycenter = (y : D.Torus) + (ε : ℤ) • halfStep D α + (ε' : ℤ) • halfStep D β := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl
  · refine ⟨⟨y, α, β, h⟩, ?_, ?_⟩
    · simp only [Units.val_one, one_smul]
      rfl
    · simp only [Units.val_one, one_smul]
      rfl
  · refine ⟨⟨y - latticeStep D β, α, β, h⟩, ?_, ?_⟩
    · simp only [Units.val_one, one_smul, Units.val_neg, neg_smul]
      exact quad_neg_second y (latticeStep D α) (latticeStep D β)
    · simp only [Units.val_one, one_smul, Units.val_neg, neg_smul,
        PeriodicLattice.Plaquette.barycenter, AddSubgroup.coe_sub, coe_latticeStep]
      abel
  · refine ⟨⟨y - latticeStep D α, α, β, h⟩, ?_, ?_⟩
    · simp only [Units.val_one, one_smul, Units.val_neg, neg_smul]
      exact quad_neg_first y (latticeStep D α) (latticeStep D β)
    · simp only [Units.val_one, one_smul, Units.val_neg, neg_smul,
        PeriodicLattice.Plaquette.barycenter, AddSubgroup.coe_sub, coe_latticeStep]
      abel
  · refine ⟨⟨y - latticeStep D α - latticeStep D β, α, β, h⟩, ?_, ?_⟩
    · simp only [Units.val_one, one_smul, Units.val_neg, neg_smul]
      exact quad_neg_both y (latticeStep D α) (latticeStep D β)
    · simp only [Units.val_one, one_smul, Units.val_neg, neg_smul,
        PeriodicLattice.Plaquette.barycenter, AddSubgroup.coe_sub, coe_latticeStep]
      abel
theorem exists_face (y : LatticeSite D) {α β : Fin 4} (h : α ≠ β) (ε ε' : ℤˣ) :
    ∃ p : D.Face,
      p.vertices = {y, y + (ε : ℤ) • latticeStep D α,
        y + (ε : ℤ) • latticeStep D α + (ε' : ℤ) • latticeStep D β,
        y + (ε' : ℤ) • latticeStep D β} ∧
      p.barycenter = (y : D.Torus) + (ε : ℤ) • halfStep D α + (ε' : ℤ) • halfStep D β := by
  rcases lt_or_gt_of_ne h with h | h
  · exact exists_face_of_lt y h ε ε'
  · obtain ⟨p, h₁, h₂⟩ := exists_face_of_lt y h ε' ε
    refine ⟨p, h₁.trans (quad_swap _ _ _), ?_⟩
    rw [h₂]
    abel
namespace SymmetryPair
variable (P : SymmetryPair D)
theorem exists_faceImage_with_barycenter (p : D.Face) :
    ∃ p' : D.Face, p'.vertices = P.vertexMap '' p.vertices ∧
      p'.barycenter = P.fwd.toFun p.barycenter := by
  obtain ⟨R, c, h⟩ := P.affine_fwd
  obtain ⟨x, ν, l, hνl⟩ := p
  have hαβ : R.1.symm ν ≠ R.1.symm l := fun e => hνl.ne (R.1.symm.injective e)
  have hstep : ∀ (w : LatticeSite D) (κ : Fin 4), P.vertexMap (w + latticeStep D κ) =
      P.vertexMap w + ((R.2 (R.1.symm κ) : ℤˣ) : ℤ) • latticeStep D (R.1.symm κ) := by
    intro w κ
    refine Subtype.ext ?_
    change P.fwd.toFun ((w : D.Torus) + (latticeStep D κ : LatticeSite D)) =
      P.fwd.toFun w +
        ((R.2 (R.1.symm κ) : ℤˣ) : ℤ) • ((latticeStep D (R.1.symm κ) : LatticeSite D) : D.Torus)
    rw [h, h, frameAffine_apply, frameAffine_apply, frameAction_add]
    have e : frameAction D R ((latticeStep D κ : LatticeSite D) : D.Torus) =
        ((R.2 (R.1.symm κ) : ℤˣ) : ℤ) • ((latticeStep D (R.1.symm κ) : LatticeSite D) : D.Torus) :=
      frameAction_pointOnAxis R κ _
    rw [e]
    abel
  obtain ⟨p', h₁, h₂⟩ :=
    exists_face (P.vertexMap x) hαβ (R.2 (R.1.symm ν)) (R.2 (R.1.symm l))
  refine ⟨p', h₁.trans ?_, h₂.trans ?_⟩
  · change _ = P.vertexMap '' ({x, x + latticeStep D ν, x + latticeStep D ν + latticeStep D l,
      x + latticeStep D l} : Set (LatticeSite D))
    rw [image_insert_eq, image_insert_eq, image_insert_eq, image_singleton,
      hstep (x + latticeStep D ν) l, hstep x ν, hstep x l]
  · change P.fwd.toFun x + _ + _ = P.fwd.toFun ((x : D.Torus) + halfStep D ν + halfStep D l)
    rw [h, h, frameAffine_apply, frameAffine_apply, frameAction_add, frameAction_add,
      frameAction_pointOnAxis, frameAction_pointOnAxis]
    abel
theorem isFaceImage (p : D.Face) : IsFaceImage P.fwd p (faceImage P.fwd p) :=
  isFaceImage_faceImage _ (by
    obtain ⟨p', h, -⟩ := P.exists_faceImage_with_barycenter p
    exact ⟨p', h⟩)
theorem faceImage_vertices (p : D.Face) :
    (faceImage P.fwd p).vertices = P.vertexMap '' p.vertices := P.isFaceImage p
theorem faceImage_barycenter (hC : PlaquetteNondegeneracy.PlaquetteVerticesDistinct D)
    (p : D.Face) : (faceImage P.fwd p).barycenter = P.fwd.toFun p.barycenter := by
  obtain ⟨p', h₁, h₂⟩ := P.exists_faceImage_with_barycenter p
  have e : faceImage P.fwd p = p' := (hC _).2 _ ((P.faceImage_vertices p).trans h₁.symm)
  rw [e, h₂]
theorem faceImage_bwd_fwd (hC : PlaquetteNondegeneracy.PlaquetteVerticesDistinct D)
    (p : D.Face) : faceImage P.bwd (faceImage P.fwd p) = p := by
  refine (hC _).2 _ ?_
  have e₁ := P.symm.faceImage_vertices (faceImage P.fwd p)
  have e₂ := P.faceImage_vertices p
  refine e₁.trans ?_
  rw [e₂, image_image]
  simp only [P.symm_vertexMap_vertexMap, image_id']
def faceEquiv (hC : PlaquetteNondegeneracy.PlaquetteVerticesDistinct D) : D.Face ≃ D.Face :=
  ⟨faceImage P.fwd, faceImage P.bwd, P.faceImage_bwd_fwd hC, P.symm.faceImage_bwd_fwd hC⟩
theorem plaquetteEnergy_pullback
    (hE : PlaquetteNondegeneracy.TraceIndependentOfTraversal D)
    {U : D.BondField} (hU : U ∈ gaugeFieldSet D) (p : D.Face) :
    PeriodicLattice.plaquetteCost (pullback P.fwd U) p =
      PeriodicLattice.plaquetteCost U (faceImage P.fwd p) := by
  obtain ⟨x, ν, l, hνl⟩ := p
  have hcorn : ({P.vertexMap x, P.vertexMap (x + latticeStep D ν),
      P.vertexMap (x + latticeStep D ν + latticeStep D l),
      P.vertexMap (x + latticeStep D l)} : Set (LatticeSite D)) =
      (faceImage P.fwd ⟨x, ν, l, hνl⟩).vertices := by
    have e : (faceImage P.fwd ⟨x, ν, l, hνl⟩).vertices =
        P.vertexMap '' ({x, x + latticeStep D ν, x + latticeStep D ν + latticeStep D l,
          x + latticeStep D l} : Set (LatticeSite D)) := P.isFaceImage ⟨x, ν, l, hνl⟩
    rw [e, image_insert_eq, image_insert_eq, image_insert_eq, image_singleton]
  have key := hE (faceImage P.fwd ⟨x, ν, l, hνl⟩)
    (P.vertexMap x) (P.vertexMap (x + latticeStep D ν))
    (P.vertexMap (x + latticeStep D ν + latticeStep D l))
    (P.vertexMap (x + latticeStep D l))
    (bondImage P.fwd (PeriodicLattice.Bond.forwardFrom x ν))
    (bondImage P.fwd (PeriodicLattice.Bond.forwardFrom (x + latticeStep D ν) l))
    (bondImage P.fwd (PeriodicLattice.Bond.forwardFrom (x + latticeStep D l) ν).opposite)
    (bondImage P.fwd (PeriodicLattice.Bond.forwardFrom x l).opposite)
    hcorn (P.bondImage_source _) (P.bondImage_target _) (P.bondImage_source _)
    (P.bondImage_target _)
    (by
      rw [P.bondImage_source]
      exact congrArg P.vertexMap
        (show x + latticeStep D l + latticeStep D ν = x + latticeStep D ν + latticeStep D l by
          abel))
    (P.bondImage_target _) (P.bondImage_source _) (P.bondImage_target _) U hU
  have hv : PeriodicLattice.plaquetteHolonomy (pullback P.fwd U) ⟨x, ν, l, hνl⟩ =
      U (bondImage P.fwd (PeriodicLattice.Bond.forwardFrom x ν)) *
        U (bondImage P.fwd (PeriodicLattice.Bond.forwardFrom (x + latticeStep D ν) l)) *
        U (bondImage P.fwd (PeriodicLattice.Bond.forwardFrom (x + latticeStep D l) ν).opposite) *
        U (bondImage P.fwd (PeriodicLattice.Bond.forwardFrom x l).opposite) := by
    simp [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
      PeriodicLattice.Plaquette.boundaryBonds, pullback, mul_assoc]
  rw [PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteCost, hv, key]
theorem actsOnFaces (hC : PlaquetteNondegeneracy.PlaquetteVerticesDistinct D)
    (hE : PlaquetteNondegeneracy.TraceIndependentOfTraversal D) :
    ActsOnFaces P.fwd P.bwd :=
  ⟨P.isFaceImage, (P.faceEquiv hC).bijective, P.faceImage_bwd_fwd hC,
    P.symm.faceImage_bwd_fwd hC, fun p =>
      ⟨fun _ hU => P.plaquetteEnergy_pullback hE hU p, P.faceImage_barycenter hC p⟩⟩
theorem smearedObservable_pullback (hC : PlaquetteNondegeneracy.PlaquetteVerticesDistinct D)
    (hE : PlaquetteNondegeneracy.TraceIndependentOfTraversal D)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : D.Torus → E)
    {U : D.BondField} (hU : U ∈ gaugeFieldSet D) :
    PeriodicLattice.smearedObservable f (pullback P.fwd U) =
      PeriodicLattice.smearedObservable (f ∘ P.bwd.toFun) U := by
  simp only [PeriodicLattice.smearedObservable]
  refine Eq.trans ?_ (finsum_comp_equiv (P.faceEquiv hC))
  refine finsum_congr fun p => ?_
  change _ = PeriodicLattice.plaquetteCost U (faceImage P.fwd p) •
    f (P.bwd.toFun (faceImage P.fwd p).barycenter)
  rw [P.plaquetteEnergy_pullback hE hU, P.faceImage_barycenter hC, P.bwd_fwd]
end SymmetryPair
theorem ae_mem_gaugeFieldSet (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    ∀ᵐ U ∂(PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling), U ∈ gaugeFieldSet D := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ :=
    hW D.L D.m D.K D.coupling (one_lt_blockFactor D) D.m.pos D.K.pos
  exact mem_ae_iff.mpr h
namespace SymmetryPair
variable (P : SymmetryPair D)
def pullbackMeasurableEquiv : D.BondField ≃ᵐ D.BondField where
  toFun := pullback P.fwd
  invFun := pullback P.bwd
  left_inv := P.pullback_bwd_fwd
  right_inv := P.pullback_fwd_bwd
  measurable_toFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
theorem gibbsExpectation_comp_pullback (hI : PeriodicLattice.WilsonMeasureIsometryInvariant)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Υ : D.BondField → E) :
    PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling (Υ ∘ pullback P.fwd) =
      PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling Υ := by
  have hm := ((hI D.L D.m D.K D.coupling (one_lt_blockFactor D) D.m.pos D.K.pos).2.2
    P.symm.toEquiv P.symm.isSublatticeIsometry).2.2
  rw [← P.pullback_eq_transport] at hm
  have e := P.pullbackMeasurableEquiv.measurableEmbedding.integral_map
    (μ := PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling) Υ
  have e' : Measure.map (⇑P.pullbackMeasurableEquiv)
      (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling) =
      PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling := hm
  rw [e'] at e
  exact e.symm
theorem preservesExpectations (hI : PeriodicLattice.WilsonMeasureIsometryInvariant) :
    PreservesExpectations P.fwd :=
  ⟨fun Υ _ _ => P.gibbsExpectation_comp_pullback hI Υ,
    fun Υ _ _ => P.gibbsExpectation_comp_pullback hI Υ⟩
theorem gibbsExpectation_smearedObservable_comp
    (hI : PeriodicLattice.WilsonMeasureIsometryInvariant)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hC : PlaquetteNondegeneracy.PlaquetteVerticesDistinct D)
    (hE : PlaquetteNondegeneracy.TraceIndependentOfTraversal D)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : D.Torus → E) :
    PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
        (PeriodicLattice.smearedObservable (f ∘ P.fwd.toFun)) =
      PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
        (PeriodicLattice.smearedObservable f) := by
  refine Eq.trans ?_
    (P.symm.gibbsExpectation_comp_pullback hI (PeriodicLattice.smearedObservable f))
  refine integral_congr_ae ((ae_mem_gaugeFieldSet hW).mono fun U hU => ?_)
  exact (P.symm.smearedObservable_pullback hC hE f hU).symm
theorem centredObservable_pullback (hI : PeriodicLattice.WilsonMeasureIsometryInvariant)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hC : PlaquetteNondegeneracy.PlaquetteVerticesDistinct D)
    (hE : PlaquetteNondegeneracy.TraceIndependentOfTraversal D)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : D.Torus → E)
    {U : D.BondField} (hU : U ∈ gaugeFieldSet D) :
    D.centredObservable f (pullback P.fwd U) = D.centredObservable (f ∘ P.bwd.toFun) U := by
  have e : PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
      (PeriodicLattice.smearedObservable (f ∘ P.bwd.toFun)) =
      PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
        (PeriodicLattice.smearedObservable f) :=
    P.symm.gibbsExpectation_smearedObservable_comp hI hW hC hE f
  simp only [MirrorData.centredObservable]
  rw [P.smearedObservable_pullback hC hE f hU, e]
theorem actsOnCentredObservables (hI : PeriodicLattice.WilsonMeasureIsometryInvariant)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hC : PlaquetteNondegeneracy.PlaquetteVerticesDistinct D)
    (hE : PlaquetteNondegeneracy.TraceIndependentOfTraversal D) :
    ActsOnCentredObservables P.fwd P.bwd := fun _ _ _ f _ =>
  ⟨P.gibbsExpectation_smearedObservable_comp hI hW hC hE f,
    fun _ hU => P.centredObservable_pullback hI hW hC hE f hU⟩
theorem connectedSchwinger_comp (hI : PeriodicLattice.WilsonMeasureIsometryInvariant)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hC : PlaquetteNondegeneracy.PlaquetteVerticesDistinct D)
    (hE : PlaquetteNondegeneracy.TraceIndependentOfTraversal D)
    {n : ℕ} (f : Fin n → D.Torus → ℝ) :
    SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling (fun i => f i ∘ P.fwd.toFun) =
      SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling f := by
  have gen : ∀ z : Fin n → ℂ,
      Cumulants.momentGeneratingFunction
        (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling)
        (fun i U => PeriodicLattice.smearedObservable (f i ∘ P.fwd.toFun) U) z =
      Cumulants.momentGeneratingFunction
        (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling)
        (fun i U => PeriodicLattice.smearedObservable (f i) U) z := by
    intro z
    refine Eq.trans ?_ (P.symm.gibbsExpectation_comp_pullback hI
      (fun U => Complex.exp (∑ i, z i * ((PeriodicLattice.smearedObservable (f i) U : ℝ) : ℂ))))
    refine integral_congr_ae ((ae_mem_gaugeFieldSet hW).mono fun U hU => ?_)
    have e : ∀ i, PeriodicLattice.smearedObservable (f i) (pullback P.bwd U) =
        PeriodicLattice.smearedObservable (f i ∘ P.fwd.toFun) U :=
      fun i => P.symm.smearedObservable_pullback hC hE (f i) hU
    simp only [Function.comp_apply]
    change Complex.exp
        (∑ i, z i * ((PeriodicLattice.smearedObservable (f i ∘ P.fwd.toFun) U : ℝ) : ℂ)) =
      Complex.exp
        (∑ i, z i * ((PeriodicLattice.smearedObservable (f i) (pullback P.bwd U) : ℝ) : ℂ))
    simp only [e]
  have h : (fun z => Complex.log (Cumulants.momentGeneratingFunction
      (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling)
        (fun i U => PeriodicLattice.smearedObservable (f i ∘ P.fwd.toFun) U) z)) =
      fun z => Complex.log (Cumulants.momentGeneratingFunction
        (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling)
          (fun i U => PeriodicLattice.smearedObservable (f i) U) z) :=
    funext fun z => by rw [gen z]
  simp only [SchwingerFunctions.connectedSchwinger, PeriodicLattice.gibbsCumulant,
    Cumulants.mixedCumulant]
  rw [h]
theorem measurable_fwd : Measurable P.fwd.toFun := by
  obtain ⟨R, c, h⟩ := P.affine_fwd
  have e : P.fwd.toFun = fun y => frameAction D R y + c := funext h
  rw [e]
  have hc : Continuous fun y : D.Torus => frameAction D R y := by
    refine continuous_pi fun μ => ?_
    exact (continuous_apply (R.1 μ)).zsmul _
  exact (hc.add continuous_const).measurable
theorem bijective_fwd : Function.Bijective P.fwd.toFun :=
  Function.bijective_iff_has_inverse.mpr ⟨P.bwd.toFun, P.bwd_fwd, P.fwd_bwd⟩
theorem preservesConnectedSchwinger (hI : PeriodicLattice.WilsonMeasureIsometryInvariant)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hCl : TorusMetricSpace.IsometryActionOnFunctions D)
    (hC : PlaquetteNondegeneracy.PlaquetteVerticesDistinct D)
    (hE : PlaquetteNondegeneracy.TraceIndependentOfTraversal D) :
    PreservesConnectedSchwinger P.fwd := by
  intro n _ f d hb hm hsep
  have B := hCl P.fwd.toFun P.bijective_fwd P.fwd.isDistPreserving
  refine ⟨fun i => ?_, fun i => (hm i).comp P.measurable_fwd, (B.2.2.2 ℝ n f).2 d hsep,
    P.connectedSchwinger_comp hI hW hC hE f⟩
  obtain ⟨C, hC'⟩ := hb i
  exact ⟨C, fun x => hC' _⟩
theorem preservesGibbsFunctional (hI : PeriodicLattice.WilsonMeasureIsometryInvariant)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hCl : TorusMetricSpace.IsometryActionOnFunctions D)
    (hC : PlaquetteNondegeneracy.PlaquetteVerticesDistinct D)
    (hE : PlaquetteNondegeneracy.TraceIndependentOfTraversal D) :
    PreservesGibbsFunctional P.fwd := by
  intro q h hh
  have B := hCl P.fwd.toFun P.bijective_fwd P.fwd.isDistPreserving
  refine ⟨⟨fun l => ((B.2.1 ℝ (h l)).2.2.2) (hh.1 l), (B.2.2.2 ℝ q h).1 hh.2⟩, ?_⟩
  refine Eq.trans ?_ (P.symm.gibbsExpectation_comp_pullback hI
    (fun U => ∏ l, D.centredObservable (h l) U))
  refine integral_congr_ae ((ae_mem_gaugeFieldSet hW).mono fun U hU => ?_)
  have e : ∀ l, D.centredObservable (h l) (pullback P.bwd U) =
      D.centredObservable (h l ∘ P.fwd.toFun) U :=
    fun l => P.symm.centredObservable_pullback hI hW hC hE (h l) hU
  change ∏ l, D.centredObservable (h l ∘ P.fwd.toFun) U =
    ∏ l, D.centredObservable (h l) (pullback P.bwd U)
  simp only [e]
end SymmetryPair
theorem symmetryCovariance (hN : PlaquetteNondegeneracy.NondegeneracyStatement)
    (hI : PeriodicLattice.WilsonMeasureIsometryInvariant)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hCl : TorusMetricSpace.MetricTorusFacts)
    (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement) :
    SymmetryCovariance := by
  intro D
  refine ⟨affineMapsExhaustSymmetries hT hI D, fun s => ?_⟩
  obtain ⟨-, -, hC, -, hE⟩ := hN D
  obtain ⟨-, -, -, hB⟩ := hCl D
  obtain ⟨P, rfl⟩ := exists_symmetryPair hT hI s
  exact ⟨isAffine_of_symmetry hT P.fwd, P.bijective_fwd, P.bwd, ⟨P.bwd_fwd, P.fwd_bwd⟩,
    P.actsOnBonds, P.actsOnGaugeFields, P.actsOnFaces hC hE,
    fun _ _ _ f _ _ hU => P.smearedObservable_pullback hC hE f hU,
    P.preservesExpectations hI, P.actsOnCentredObservables hI hW hC hE,
    P.preservesConnectedSchwinger hI hW hB hC hE, P.preservesGibbsFunctional hI hW hB hC hE⟩
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance
end

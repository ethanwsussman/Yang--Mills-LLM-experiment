import YangMills.Construction.InfiniteLattice.LatticeAtOneSpacingWithItsTorusAndCovering
import YangMills.Construction.InfiniteLattice.PeriodicExtensionsAndTheirWeakLimitPoints
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import Mathlib
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.InfiniteLattice
open YangMills.Construction.InfiniteLattice.PeriodicExtensions YangMills.Construction.FixedSpacing
namespace TorusCovering
variable (D : Setup)
def SitesUnderProjection : Prop :=
  (∀ x y : AmbientSpace, D.proj x = D.proj y ↔ x - y ∈ latticeSubgroup D.side) ∧
    (∀ x v : AmbientSpace, D.proj (x + v) = D.addVec (D.proj x) v) ∧
    latticeSubgroup D.side ≤ D.latticeSites ∧
    D.proj '' (D.latticeSites : Set AmbientSpace) = (D.torusSites : Set D.Torus)
def LinksUnderProjection : Prop :=
  (∀ b : Link D.mesh,
      ((D.projLink b).source : D.Torus) = D.proj b.initial ∧
        ((D.projLink b).target : D.Torus) = D.proj b.terminal ∧
        (b ∈ D.links → D.projLink b ∈ D.positiveTorusLinks) ∧
        D.projLink b.opposite = (D.projLink b).opposite) ∧
    (∀ c ∈ D.positiveTorusLinks, ∃ b ∈ D.links, D.projLink b = c) ∧
    ∀ (x y : LatticePoint D.mesh) (i j : Fin 4),
      (D.projLink (Link.forwardFrom x i) = D.projLink (Link.forwardFrom y j) ↔
          i = j ∧ (y : AmbientSpace) - (x : AmbientSpace) ∈ latticeSubgroup D.side) ∧
        (D.projLink (Link.forwardFrom x i) = D.projLink (Link.forwardFrom y j) ↔
          ∃ v : LatticePoint D.mesh, (v : AmbientSpace) ∈ latticeSubgroup D.side ∧
            Link.forwardFrom y j = CutoffLattice.translateLink (Link.forwardFrom x i) v)
def PlaquettesUnderProjection : Prop :=
  Function.Surjective D.projFace ∧
    (∀ p q : ElementaryPlaquette D.mesh,
      (D.projFace p = D.projFace q ↔
          ∃ v : LatticePoint D.mesh, (v : AmbientSpace) ∈ latticeSubgroup D.side ∧
            q = CutoffLattice.translateFace p v) ∧
        ∀ v w : LatticePoint D.mesh, (v : AmbientSpace) ∈ latticeSubgroup D.side →
          (w : AmbientSpace) ∈ latticeSubgroup D.side →
          q = CutoffLattice.translateFace p v →
          q = CutoffLattice.translateFace p w → v = w) ∧
    ∀ p : ElementaryPlaquette D.mesh,
      (D.projFace p).vertices = projectPoint D.L D.m (D.level : ℤ) '' p.cornerSet ∧
        [torusFirstEdge (D.projFace p), torusSecondEdge (D.projFace p),
            torusThirdEdge (D.projFace p), torusFourthEdge (D.projFace p)] =
          [firstEdge p, secondEdge p, thirdEdge p, fourthEdge p].map D.projLink ∧
        (D.projFace p).barycenter = D.proj p.center
def FieldsUnderProjection : Prop :=
  (∀ (U : D.TorusFields) (b : Link D.mesh),
      liftCompactField U b = U.linkValue (D.projLink b)) ∧
    (∀ (U : D.TorusFields) (b : Link D.mesh) (v : LatticePoint D.mesh),
      (v : AmbientSpace) ∈ latticeSubgroup D.side →
      liftCompactField U (CutoffLattice.translateLink b v) = liftCompactField U b) ∧
    (∀ (U : D.TorusFields) (p : ElementaryPlaquette D.mesh),
      faceEnergy (liftCompactField U) p = D.faceEnergy (D.projFace p) U) ∧
    Continuous (liftCompactField : D.TorusFields → D.Fields)
def Statement : Prop :=
  ∀ D : Setup, SitesUnderProjection D ∧ LinksUnderProjection D ∧ PlaquettesUnderProjection D ∧
    FieldsUnderProjection D
end TorusCovering
end YangMills.Construction.InfiniteLattice
end

open Set
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice.TorusCovering
section Points
variable {L m : ℕ}
theorem torusProj_add (x y : InfiniteLattice.AmbientSpace) :
    TorusMetric.torusProj (PeriodicLattice.torusSide L m) (x + y) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L m) x +
        TorusMetric.torusProj (PeriodicLattice.torusSide L m) y :=
  funext fun μ => by simp [TorusMetric.torusProj]
theorem torusProj_single (ν : Fin 4) (t : ℝ) :
    TorusMetric.torusProj (PeriodicLattice.torusSide L m) (Pi.single ν t : InfiniteLattice.AmbientSpace) =
      PeriodicLattice.pointOnAxis L m ν t := by
  funext μ
  by_cases hμ : μ = ν
  · subst hμ
    simp [TorusMetric.torusProj, PeriodicLattice.pointOnAxis]
  · simp [TorusMetric.torusProj, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hμ]
theorem torusProj_eq_iff (x x' : InfiniteLattice.AmbientSpace) :
    TorusMetric.torusProj (PeriodicLattice.torusSide L m) x =
        TorusMetric.torusProj (PeriodicLattice.torusSide L m) x' ↔
      x - x' ∈ InfiniteLattice.latticeSubgroup (PeriodicLattice.torusSide L m) := by
  constructor
  · intro hx
    have hcoord : ∀ μ, ∃ k : ℤ, k • PeriodicLattice.torusSide L m = x μ - x' μ := by
      intro μ
      refine (AddCircle.coe_eq_zero_iff _).mp ?_
      have hμ : ((x μ : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) =
          ((x' μ : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) := congrFun hx μ
      rw [AddCircle.coe_sub, hμ, sub_self]
    choose k hk using hcoord
    refine ⟨k, fun μ => ?_⟩
    have hkμ := hk μ
    rw [zsmul_eq_mul] at hkμ
    simpa using hkμ.symm
  · rintro ⟨k, hk⟩
    funext μ
    show ((x μ : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) =
      ((x' μ : ℝ) : AddCircle (PeriodicLattice.torusSide L m))
    rw [← sub_eq_zero, ← AddCircle.coe_sub]
    refine (AddCircle.coe_eq_zero_iff _).mpr ⟨k μ, ?_⟩
    rw [zsmul_eq_mul]
    simpa using (hk μ).symm
theorem isLevelLift_self_iff (K : ℕ) (u : PeriodicLattice.FourTorus L m) (w : InfiniteLattice.AmbientSpace) :
    PeriodicLattice.IsLevelLift L m K K u w ↔
      TorusMetric.torusProj (PeriodicLattice.torusSide L m) w = u := by
  have hunits : ∀ r : ℝ, PeriodicLattice.toLevelUnits L K K r = r := fun r => by
    simp [PeriodicLattice.toLevelUnits, PeriodicLattice.levelDepth]
  constructor
  · rintro ⟨v, hv, hw⟩
    funext μ
    show ((w μ : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) = u μ
    rw [hw μ, hunits, hv μ]
  · rintro rfl
    exact ⟨w, fun _ => rfl, fun μ => (hunits _).symm⟩
theorem torusCover_add_eq_addVec (K : ℕ) (x v : InfiniteLattice.AmbientSpace) :
    CutoffLattice.torusCover L m (x + v) =
      CutoffLattice.addVec L m K (CutoffLattice.torusCover L m x) v := by
  have hy := (isLevelLift_self_iff K _ _).mp
    (Classical.epsilon_spec
      (p := PeriodicLattice.IsLevelLift L m K K (CutoffLattice.torusCover L m x))
      ⟨x, (isLevelLift_self_iff K _ x).mpr rfl⟩)
  unfold CutoffLattice.addVec PeriodicLattice.shiftBy
  set y := Classical.epsilon (PeriodicLattice.IsLevelLift L m K K (CutoffLattice.torusCover L m x))
  have hz := (isLevelLift_self_iff K _ _).mp (Classical.epsilon_spec
    (p := fun u => PeriodicLattice.IsLevelLift L m K K u (y + v))
    ⟨_, (isLevelLift_self_iff K _ (y + v)).mpr rfl⟩)
  show _ = Classical.epsilon fun u => PeriodicLattice.IsLevelLift L m K K u (y + v)
  rw [← hz, torusProj_add, hy]
  exact torusProj_add x v
end Points
section Sites
variable {L m : ℕ} {j : ℤ}
theorem projectPoint_add (x y : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L j)) :
    InfiniteLattice.projectPoint L m j (x + y) =
      InfiniteLattice.projectPoint L m j x + InfiniteLattice.projectPoint L m j y :=
  Subtype.ext (torusProj_add _ _)
theorem projectPoint_eq_iff (x x' : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L j)) :
    InfiniteLattice.projectPoint L m j x = InfiniteLattice.projectPoint L m j x' ↔
      (x : InfiniteLattice.AmbientSpace) - (x' : InfiniteLattice.AmbientSpace) ∈
        InfiniteLattice.latticeSubgroup (PeriodicLattice.torusSide L m) :=
  Subtype.ext_iff.trans (torusProj_eq_iff _ _)
theorem exists_projectPoint_eq (y : PeriodicLattice.Site L m j) :
    ∃ x : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L j),
      InfiniteLattice.projectPoint L m j x = y := by
  obtain ⟨k, hk⟩ := y.2
  refine ⟨⟨fun μ => (k μ : ℝ) * PeriodicLattice.meshSize L j, k, fun _ => rfl⟩, Subtype.ext ?_⟩
  funext μ
  exact (hk μ).symm
theorem projectLink_forwardFrom (x : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L j))
    (κ : Fin 4) :
    InfiniteLattice.projectLink L m j (InfiniteLattice.Link.forwardFrom x κ) =
      PeriodicLattice.Bond.forwardFrom (InfiniteLattice.projectPoint L m j x) κ :=
  PeriodicLattice.Bond.ext rfl (by
    show InfiniteLattice.projectPoint L m j (x + InfiniteLattice.axisStep _ κ) =
      InfiniteLattice.projectPoint L m j x + PeriodicLattice.unitStep L m j κ
    rw [projectPoint_add, InfiniteLattice.projectPoint_axisStep])
theorem projectLink_translateLink (b : InfiniteLattice.Link (PeriodicLattice.meshSize L j))
    (v : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L j))
    (hv : (v : InfiniteLattice.AmbientSpace) ∈
      InfiniteLattice.latticeSubgroup (PeriodicLattice.torusSide L m)) :
    InfiniteLattice.projectLink L m j (CutoffLattice.translateLink b v) =
      InfiniteLattice.projectLink L m j b := by
  have hshift : ∀ x : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L j),
      InfiniteLattice.projectPoint L m j (x + v) = InfiniteLattice.projectPoint L m j x :=
    fun x => (projectPoint_eq_iff _ _).mpr (by simpa using hv)
  exact PeriodicLattice.Bond.ext (hshift _) (hshift _)
end Sites
section Numbers
variable (D : FixedSpacing.Setup)
theorem one_lt_L : (1 : ℝ) < D.L := by
  have hL : 1 < D.L := by
    have := D.admissible.2
    omega
  exact_mod_cast hL
theorem mesh_pos : 0 < D.mesh :=
  zpow_pos (lt_trans one_pos (one_lt_L D)) _
theorem mesh_le_one : D.mesh ≤ 1 := by
  have hpow : (1 : ℝ) ≤ (D.L : ℝ) ^ D.level := one_le_pow₀ (one_lt_L D).le
  simp only [FixedSpacing.Setup.mesh, PeriodicLattice.meshSize, zpow_neg, zpow_natCast]
  exact inv_le_one_of_one_le₀ hpow
theorem two_le_side : 2 ≤ D.side := by
  have hpow : (1 : ℝ) ≤ (D.L : ℝ) ^ (D.m : ℕ) := one_le_pow₀ (one_lt_L D).le
  simp only [FixedSpacing.Setup.side, PeriodicLattice.torusSide]
  linarith
theorem unitStep_injective {κ κ' : Fin 4}
    (hstep : PeriodicLattice.unitStep D.L D.m (D.level : ℤ) κ =
      PeriodicLattice.unitStep D.L D.m (D.level : ℤ) κ') :
    κ = κ' := by
  by_contra hne
  have hzero : ((D.mesh : ℝ) : AddCircle D.side) = 0 := by
    have hκ := congrFun (congrArg Subtype.val hstep) κ
    simp only [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_same] at hκ
    rw [Pi.single_eq_of_ne hne] at hκ
    exact hκ
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).mp hzero
  rw [zsmul_eq_mul] at hk
  have ha := mesh_pos D
  have ha' := mesh_le_one D
  have hs := two_le_side D
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk0
    nlinarith
  · simp [hk0] at hk
    linarith
  · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    nlinarith
end Numbers
section Requirements
variable (D : FixedSpacing.Setup)
theorem sitesUnderProjection_holds : SitesUnderProjection D := by
  refine ⟨torusProj_eq_iff, fun x v => torusCover_add_eq_addVec _ x v, ?_, ?_⟩
  · rintro x ⟨k, hk⟩
    have hL : (D.L : ℝ) ≠ 0 := (lt_trans one_pos (one_lt_L D)).ne'
    refine ⟨fun μ => k μ * (2 * (D.L : ℤ) ^ ((D.m : ℕ) + D.level)), fun μ => ?_⟩
    rw [hk μ]
    simp only [FixedSpacing.Setup.mesh, FixedSpacing.Setup.side, PeriodicLattice.torusSide,
      PeriodicLattice.meshSize, zpow_neg, zpow_natCast]
    push_cast
    rw [pow_add]
    field_simp
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (InfiniteLattice.projectPoint D.L D.m (D.level : ℤ) ⟨x, hx⟩).2
    · intro hy
      obtain ⟨x, hx⟩ :=
        exists_projectPoint_eq (L := D.L) (m := D.m) (j := (D.level : ℤ)) ⟨y, hy⟩
      exact ⟨x, x.2, congrArg Subtype.val hx⟩
theorem linksUnderProjection_holds : LinksUnderProjection D := by
  refine ⟨fun b => ⟨rfl, rfl, ?_, InfiniteLattice.projectLink_opposite b⟩, ?_, fun x x' κ κ' => ?_⟩
  · rintro ⟨x, κ, rfl⟩
    refine ⟨κ, ?_⟩
    show (D.projLink (InfiniteLattice.Link.forwardFrom x κ)).target -
      (D.projLink (InfiniteLattice.Link.forwardFrom x κ)).source = _
    simp only [FixedSpacing.Setup.projLink, projectLink_forwardFrom,
      PeriodicLattice.Bond.forwardFrom]
    abel
  · rintro c ⟨μ, hμ⟩
    obtain ⟨x, hx⟩ := exists_projectPoint_eq c.source
    refine ⟨InfiniteLattice.Link.forwardFrom x μ, ⟨x, μ, rfl⟩, ?_⟩
    refine (projectLink_forwardFrom x μ).trans (PeriodicLattice.Bond.ext hx ?_)
    show InfiniteLattice.projectPoint D.L D.m (D.level : ℤ) x +
      PeriodicLattice.unitStep D.L D.m (D.level : ℤ) μ = c.target
    rw [hx, ← hμ]
    abel
  · have hforward : D.projLink (InfiniteLattice.Link.forwardFrom x κ) =
          D.projLink (InfiniteLattice.Link.forwardFrom x' κ') ↔
        κ = κ' ∧ (x' : InfiniteLattice.AmbientSpace) - (x : InfiniteLattice.AmbientSpace) ∈
          InfiniteLattice.latticeSubgroup D.side := by
      constructor
      · intro hlink
        have hlink' : PeriodicLattice.Bond.forwardFrom
              (InfiniteLattice.projectPoint D.L D.m (D.level : ℤ) x) κ =
            PeriodicLattice.Bond.forwardFrom
              (InfiniteLattice.projectPoint D.L D.m (D.level : ℤ) x') κ' := by
          rw [← projectLink_forwardFrom, ← projectLink_forwardFrom]
          exact hlink
        have hsrc : InfiniteLattice.projectPoint D.L D.m (D.level : ℤ) x =
            InfiniteLattice.projectPoint D.L D.m (D.level : ℤ) x' :=
          congrArg PeriodicLattice.Bond.source hlink'
        have htgt : InfiniteLattice.projectPoint D.L D.m (D.level : ℤ) x +
              PeriodicLattice.unitStep D.L D.m (D.level : ℤ) κ =
            InfiniteLattice.projectPoint D.L D.m (D.level : ℤ) x' +
              PeriodicLattice.unitStep D.L D.m (D.level : ℤ) κ' :=
          congrArg PeriodicLattice.Bond.target hlink'
        rw [hsrc] at htgt
        exact ⟨unitStep_injective D (add_left_cancel htgt),
          (projectPoint_eq_iff x' x).mp hsrc.symm⟩
      · rintro ⟨rfl, hs⟩
        have hsrc := (projectPoint_eq_iff x x').mpr
          (by rw [← neg_sub]; exact neg_mem hs)
        show InfiniteLattice.projectLink D.L D.m (D.level : ℤ) _ =
          InfiniteLattice.projectLink D.L D.m (D.level : ℤ) _
        rw [projectLink_forwardFrom, projectLink_forwardFrom, hsrc]
    refine ⟨hforward, ?_⟩
    constructor
    · intro hlink
      obtain ⟨rfl, hs⟩ := hforward.mp hlink
      refine ⟨x' - x, hs, InfiniteLattice.Link.ext ?_ ?_⟩
      · show x' = x + (x' - x)
        abel
      · show x' + InfiniteLattice.axisStep _ κ = x + InfiniteLattice.axisStep _ κ + (x' - x)
        abel
    · rintro ⟨v, hv, hb⟩
      show InfiniteLattice.projectLink D.L D.m (D.level : ℤ) _ =
        InfiniteLattice.projectLink D.L D.m (D.level : ℤ) _
      rw [hb, projectLink_translateLink _ _ hv]
theorem plaquettesUnderProjection_holds : PlaquettesUnderProjection D := by
  refine ⟨?_, fun p p' => ⟨?_, ?_⟩, fun p => ⟨?_, ?_, ?_⟩⟩
  · intro P
    obtain ⟨x, hx⟩ := exists_projectPoint_eq P.origin
    refine ⟨⟨x, P.firstAxis, P.secondAxis, P.firstAxis_lt_secondAxis⟩, ?_⟩
    cases P
    simp only [FixedSpacing.Setup.projFace, CutoffLattice.projectFace]
    simp_all
  · constructor
    · intro hface
      have horigin : InfiniteLattice.projectPoint D.L D.m (D.level : ℤ) p.corner =
          InfiniteLattice.projectPoint D.L D.m (D.level : ℤ) p'.corner :=
        congrArg PeriodicLattice.Plaquette.origin hface
      have h₁ : p.lowAxis = p'.lowAxis := congrArg PeriodicLattice.Plaquette.firstAxis hface
      have h₂ : p.highAxis = p'.highAxis := congrArg PeriodicLattice.Plaquette.secondAxis hface
      refine ⟨p'.corner - p.corner, (projectPoint_eq_iff _ _).mp horigin.symm, ?_⟩
      cases p
      cases p'
      simp_all [CutoffLattice.translateFace, CutoffLattice.face]
    · rintro ⟨v, hv, rfl⟩
      have hshift : InfiniteLattice.projectPoint D.L D.m (D.level : ℤ) (p.corner + v) =
          InfiniteLattice.projectPoint D.L D.m (D.level : ℤ) p.corner :=
        (projectPoint_eq_iff _ _).mpr (by simpa using hv)
      cases p
      simp_all [FixedSpacing.Setup.projFace, CutoffLattice.projectFace,
        CutoffLattice.translateFace, CutoffLattice.face]
  · intro v w _ _ hv hw
    have := congrArg InfiniteLattice.ElementaryPlaquette.corner (hv.symm.trans hw)
    exact add_left_cancel this
  · simp only [InfiniteLattice.ElementaryPlaquette.cornerSet, PeriodicLattice.Plaquette.vertices,
      image_insert_eq, image_singleton, projectPoint_add, InfiniteLattice.projectPoint_axisStep]
    rfl
  · simp only [List.map_cons, List.map_nil, FixedSpacing.Setup.projLink,
      PeriodicExtensions.firstEdge, PeriodicExtensions.secondEdge, PeriodicExtensions.thirdEdge,
      PeriodicExtensions.fourthEdge, projectLink_forwardFrom, projectPoint_add,
      InfiniteLattice.projectPoint_axisStep]
    rfl
  · show _ = TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) _
    simp only [InfiniteLattice.ElementaryPlaquette.center, torusProj_add, torusProj_single]
    rfl
theorem fieldsUnderProjection_holds : FieldsUnderProjection D := by
  refine ⟨fun U b => InfiniteLattice.liftCompactField_apply U b, fun U b v hv => ?_, fun U p => ?_,
    InfiniteLattice.continuous_liftCompactField⟩
  · rw [InfiniteLattice.liftCompactField_apply, InfiniteLattice.liftCompactField_apply,
      projectLink_translateLink _ _ hv]
  · have hedge : ∀ (x : InfiniteLattice.LatticePoint D.mesh) (κ : Fin 4),
        InfiniteLattice.liftCompactField U (InfiniteLattice.Link.forwardFrom x κ) =
          U.linkValue (PeriodicLattice.Bond.forwardFrom
            (InfiniteLattice.projectPoint D.L D.m (D.level : ℤ) x) κ) := fun x κ => by
      rw [InfiniteLattice.liftCompactField_apply, projectLink_forwardFrom]
    have hhol : ((InfiniteLattice.faceHolonomy (InfiniteLattice.liftCompactField U) p :
          Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
        PeriodicLattice.plaquetteHolonomy U.1 (D.projFace p) := by
      have hinv : ∀ b : PeriodicLattice.Bond D.L D.m (D.level : ℤ),
          (((U.linkValue b)⁻¹ : Matrices.ComplexMatrix2.specialUnitary) :
            Matrices.ComplexMatrix2) = U.1 b.opposite := fun b => by
        rw [← U.linkValue_opposite b]
        rfl
      simp only [InfiniteLattice.faceHolonomy, hedge, projectPoint_add,
        InfiniteLattice.projectPoint_axisStep, PeriodicLattice.plaquetteHolonomy,
        PeriodicLattice.pathHolonomy, PeriodicLattice.Plaquette.boundaryBonds,
        FixedSpacing.Setup.projFace, CutoffLattice.projectFace, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one, Submonoid.coe_mul, hinv]
      simp only [mul_assoc]
      rfl
    simp only [InfiniteLattice.faceEnergy, FixedSpacing.Setup.faceEnergy,
      PeriodicLattice.plaquetteCost, hhol]
end Requirements
theorem statement_holds : TorusCovering.Statement := fun D =>
  ⟨sitesUnderProjection_holds D, linksUnderProjection_holds D, plaquettesUnderProjection_holds D,
    fieldsUnderProjection_holds D⟩
end InfiniteLattice.TorusCovering
end YangMills.Construction

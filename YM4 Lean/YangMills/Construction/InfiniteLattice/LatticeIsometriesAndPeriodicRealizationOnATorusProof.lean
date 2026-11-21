import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLatticeProof
import YangMills.Construction.InfiniteLattice.FunctionsOfASetOfBonds
import YangMills.Construction.InfiniteLattice.LatticeIsometriesAndPeriodicRealizationOnATorus
import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
open Set
noncomputable section
namespace YangMills.Construction.MultipleReflections
open InfiniteLattice (IsBoundedObservable ElementaryPlaquette LatticePoint AmbientSpace
  observableSupNorm faceEnergy smearedEnergy)
namespace TorusPullback
variable (D : Setup)
theorem blockFactor_pos : 0 < D.L := by
  have h := D.isAdmissible.2
  omega
theorem mesh_pos : 0 < D.mesh := by apply _root_.YangMills.Construction.InfiniteLattice.LinkSetFunctions.mesh_pos <;> assumption
theorem side_pos : 0 < D.side := by apply _root_.YangMills.Construction.LatticeCovering.period_pos <;> assumption
theorem meshAt_zero_eq : Tower.meshAt D.L D.K 0 = D.mesh := by
  simp [Tower.meshAt, ReflectionPositivity.AxisMirror.MirrorData.mesh, PeriodicLattice.meshSize]
theorem latticeTranslate_mem (n : Fin 4 → ℤ) :
    TestFunctions.latticeTranslate D.side n ∈ InfiniteLattice.latticeSubgroup D.mesh := by
  have h : D.side = 2 * (D.halfSideCount : ℝ) * D.mesh := by
    have := D.side_div_mesh
    rw [div_eq_iff (mesh_pos D).ne'] at this
    exact this
  refine ⟨fun μ => 2 * (D.halfSideCount : ℤ) * n μ, fun μ => ?_⟩
  simp only [TestFunctions.latticeTranslate, h]
  push_cast
  ring
theorem eq_zero_of_norm_latticeTranslate_le {ℓ : ℝ} (hℓ : 0 < ℓ) (n : Fin 4 → ℤ)
    (h : TorusMetric.euclidNormVec (TestFunctions.latticeTranslate ℓ n) ≤ ℓ / 2) : n = 0 := by
  by_contra hn
  obtain ⟨μ, hμ⟩ : ∃ μ, n μ ≠ 0 := by
    by_contra hc
    exact hn (funext fun μ => by
      by_contra hν
      exact hc ⟨μ, hν⟩)
  have h1 : (1 : ℝ) ≤ (n μ : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ n μ ^ 2 := by
      have := sq_pos_of_ne_zero hμ
      omega
    exact_mod_cast this
  have h2 : ℓ ^ 2 ≤ ∑ ν, TestFunctions.latticeTranslate ℓ n ν ^ 2 := by
    calc ℓ ^ 2 ≤ (ℓ * (n μ : ℝ)) ^ 2 := by
          rw [mul_pow]
          nlinarith [sq_nonneg ℓ]
      _ = TestFunctions.latticeTranslate ℓ n μ ^ 2 := rfl
      _ ≤ ∑ ν, TestFunctions.latticeTranslate ℓ n ν ^ 2 :=
          Finset.single_le_sum (f := fun ν => TestFunctions.latticeTranslate ℓ n ν ^ 2)
            (fun ν _ => sq_nonneg _) (Finset.mem_univ μ)
  have h3 : ℓ ≤ TorusMetric.euclidNormVec (TestFunctions.latticeTranslate ℓ n) :=
    Real.le_sqrt_of_sq_le h2
  linarith
abbrev linkProj (b : InfiniteLattice.Link D.mesh) : PeriodicLattice.Bond D.L D.m ((D.K : ℕ) : ℤ) :=
  InfiniteLattice.projectLink D.L D.m ((D.K : ℕ) : ℤ) b
abbrev pointProj (x : LatticePoint D.mesh) : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ) :=
  InfiniteLattice.projectPoint D.L D.m ((D.K : ℕ) : ℤ) x
theorem pointProj_add (x y : LatticePoint D.mesh) :
    pointProj D (x + y) = pointProj D x + pointProj D y :=
  Subtype.ext ((PeriodicLattice.torusProjHom D.L D.m).map_add x y)
theorem pointProj_axisStep (μ : Fin 4) :
    pointProj D (InfiniteLattice.axisStep D.mesh μ) =
      PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) μ :=
  InfiniteLattice.projectPoint_axisStep D.L D.m ((D.K : ℕ) : ℤ) μ
theorem linkProj_forwardFrom (x : LatticePoint D.mesh) (μ : Fin 4) :
    linkProj D (InfiniteLattice.Link.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom (pointProj D x) μ :=
  PeriodicLattice.Bond.ext rfl (by
    change pointProj D (x + InfiniteLattice.axisStep D.mesh μ) = _
    rw [pointProj_add, pointProj_axisStep]
    rfl)
theorem lift_apply_coe (U : D.TorusField) (b : InfiniteLattice.Link D.mesh) :
    ((D.lift U).1 b : Matrices.ComplexMatrix2) = U.1 (linkProj D b) :=
  congrArg Subtype.val (InfiniteLattice.liftCompactField_apply U b)
theorem lift_forwardFrom_coe (U : D.TorusField) (x : LatticePoint D.mesh) (μ : Fin 4) :
    ((D.lift U).1 (InfiniteLattice.Link.forwardFrom x μ) : Matrices.ComplexMatrix2) =
      U.1 (PeriodicLattice.Bond.forwardFrom (pointProj D x) μ) := by
  rw [lift_apply_coe, linkProj_forwardFrom]
theorem faceHolonomy_lift (U : D.TorusField) (p : ElementaryPlaquette D.mesh) :
    ((InfiniteLattice.faceHolonomy (D.lift U).1 p : Matrices.ComplexMatrix2.specialUnitary) :
        Matrices.ComplexMatrix2) =
      PeriodicLattice.plaquetteHolonomy U.1 (D.projectPlaquette p) := by
  have hrev : ∀ b : PeriodicLattice.Bond D.L D.m ((D.K : ℕ) : ℤ), U.1 b.opposite = (U.1 b)⁻¹ :=
    fun b => U.2.2 b (mem_univ _)
  have hc : (D.projectPlaquette p).origin = pointProj D p.corner := rfl
  have h1 : (D.projectPlaquette p).firstAxis = p.lowAxis := rfl
  have h2 : (D.projectPlaquette p).secondAxis = p.highAxis := rfl
  simp only [InfiniteLattice.faceHolonomy, PeriodicLattice.plaquetteHolonomy,
    PeriodicLattice.pathHolonomy, PeriodicLattice.Plaquette.boundaryBonds, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, hrev, hc, h1, h2]
  simp only [MulMemClass.coe_mul, InfiniteLattice.specialUnitary_coe_inv, lift_forwardFrom_coe,
    pointProj_add, pointProj_axisStep, mul_assoc]
theorem faceEnergy_lift (U : D.TorusField) (p : ElementaryPlaquette D.mesh) :
    faceEnergy (D.lift U).1 p = PeriodicLattice.plaquetteCost U.1 (D.projectPlaquette p) := by
  simp only [faceEnergy, PeriodicLattice.plaquetteCost, faceHolonomy_lift]
theorem barycenter_projectPlaquette (p : ElementaryPlaquette D.mesh) :
    (D.projectPlaquette p).barycenter = D.projection p.center := by
  funext μ
  have h : ∀ (ν : Fin 4) (t : ℝ), PeriodicLattice.pointOnAxis D.L D.m ν t μ =
      (((Pi.single ν t : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) := by
    intro ν t
    by_cases hν : μ = ν
    · subst hν
      simp [PeriodicLattice.pointOnAxis]
    · simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hν]
  change ((D.projectPlaquette p).origin : PeriodicLattice.FourTorus D.L D.m) μ +
      PeriodicLattice.pointOnAxis D.L D.m p.lowAxis
        (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ) / 2) μ +
      PeriodicLattice.pointOnAxis D.L D.m p.highAxis
        (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ) / 2) μ =
    ((((p.corner : AmbientSpace) + (Pi.single p.lowAxis (D.mesh / 2) : AmbientSpace) +
      (Pi.single p.highAxis (D.mesh / 2) : AmbientSpace) : AmbientSpace) μ : ℝ) :
      AddCircle (PeriodicLattice.torusSide D.L D.m))
  rw [h, h]
  simp only [Pi.add_apply, AddCircle.coe_add]
  rfl
theorem symmetry_facts (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (r : D.LatticeSymmetry) :
    (∃ R ∈ InfiniteLattice.hyperoctahedralLinearGroup, ∃ v ∈ InfiniteLattice.latticeSubgroup D.mesh,
      ∀ x : AmbientSpace, r.toFun x = R x + v) ∧
    Tower.FullSpace.MapsLinksOnto D.mesh r.toFun ∧
    Tower.FullSpace.MapsFacesOnto D.mesh r.toFun ∧
    ∃ g : PeriodicLattice.FourTorus D.L D.m → PeriodicLattice.FourTorus D.L D.m,
      (∀ x : AmbientSpace, g (TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) x) =
        TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) (r.toFun x)) ∧
      Tower.IsDistancePreserving g ∧ Tower.MapsSublatticeOnto (D.K : ℕ) 0 g := by
  have hW := (hT D.L (blockFactor_pos D) D.isAdmissible (D.K : ℕ)).2.2.2.2.1 0 (Nat.zero_le _)
    r.toFun r.preservesDist (by
      rw [Tower.FullSpace.MapsSublatticeOnto, meshAt_zero_eq]
      exact r.image_eq)
  rw [meshAt_zero_eq] at hW
  obtain ⟨h1, h2, h3⟩ := hW
  obtain ⟨-, hb, hp⟩ := h2 0 le_rfl
  rw [meshAt_zero_eq] at hb hp
  obtain ⟨g, hg⟩ := h3 D.m D.m.pos
  exact ⟨h1, hb, hp, g, fun x => hg.1 x, hg.2⟩
theorem symmetries_hyperoctahedral
    (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement) :
    D.SymmetriesAreHyperoctahedralMotions := by
  intro r
  obtain ⟨h1, hb, hp, -⟩ := symmetry_facts D hT r
  have hcorners : ∀ p q : ElementaryPlaquette D.mesh,
      (Subtype.val '' Tower.FullSpace.faceCorners q : Set AmbientSpace) =
        r.toFun '' (Subtype.val '' Tower.FullSpace.faceCorners p) →
      q.cornerSet = r.pointMap '' p.cornerSet := by
    intro p q h
    apply Set.image_injective.2
      (Subtype.val_injective (p := (· ∈ InfiniteLattice.latticeSubgroup D.mesh)))
    rw [Set.image_image]
    exact h.trans (Set.image_image _ _ _)
  refine ⟨h1, fun b' => ?_, fun p => ?_, fun q => ?_⟩
  · obtain ⟨b, hi, ht⟩ := hb.2 b'
    exact ⟨b, InfiniteLattice.Link.ext (Subtype.ext hi.symm) (Subtype.ext ht.symm)⟩
  · obtain ⟨q, hq⟩ := hp.1 p
    exact ⟨q, hcorners p q hq⟩
  · obtain ⟨p, hq⟩ := hp.2 q
    exact ⟨p, hcorners p q hq⟩
theorem symmetries_closed (hA : InfiniteLattice.SymmetryActionOnObservables) :
    D.SymmetriesClosedUnderInvMul := by
  obtain ⟨-, -, -, hc, -, -, -, -, -, hi, -⟩ := hA ⟨D.mesh, mesh_pos D⟩
  exact ⟨fun r => (hi r).2.1, fun r t => ⟨r.comp t, (hc r t).1⟩⟩
theorem actOn_respects_algebra (hA : InfiniteLattice.SymmetryActionOnObservables) :
    D.ActOnRespectsAlgebra := by
  obtain ⟨-, hh, -, -, -, hl, -⟩ := hA ⟨D.mesh, mesh_pos D⟩
  intro r
  refine ⟨(hh r).2.bijective, fun A A' hO _ c => ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩⟩
  exact ((hl r).2 A hO).2.2.2
theorem bondMap_linkProj {s : D.TorusSymmetry} {r : D.LatticeSymmetry} (h : D.IsDescentOf s r)
    (b : InfiniteLattice.Link D.mesh) : s.bondMap (linkProj D b) = linkProj D (r.linkMap b) := by
  have hi : s.IsBondImage (linkProj D b) (linkProj D (r.linkMap b)) :=
    Prod.ext (Subtype.ext (h b.initial)) (Subtype.ext (h b.terminal))
  have hex : ∃ b', s.IsBondImage (linkProj D b) b' := ⟨_, hi⟩
  have e : s.bondMap (linkProj D b) = hex.choose := dif_pos hex
  rw [e]
  exact s.isBondImage_unique hex.choose_spec hi
theorem pullbackField_lift {s : D.TorusSymmetry} {r : D.LatticeSymmetry}
    (h : D.IsDescentOf s r) (U : D.TorusField) :
    r.pullbackField (D.lift U) = D.lift (s.pullback U) := by
  refine Subtype.ext (funext fun b => Subtype.ext ?_)
  change ((D.lift U).1 (r.linkMap b) : Matrices.ComplexMatrix2) =
    ((D.lift (s.pullback U)).1 b : Matrices.ComplexMatrix2)
  refine (lift_apply_coe D U _).trans (Eq.trans ?_ (lift_apply_coe D (s.pullback U) b).symm)
  change U.1 (linkProj D (r.linkMap b)) = U.1 (s.bondMap (linkProj D b))
  rw [bondMap_linkProj D h]
theorem symmetries_descend (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement) :
    D.SymmetriesDescendToTorus := by
  intro r
  refine ⟨?_, fun s hs => ⟨pullbackField_lift D hs, fun A _ => ?_⟩⟩
  · obtain ⟨-, -, -, g, hg, hi, ho⟩ := symmetry_facts D hT r
    have hd : PeriodicLattice.levelDepth (D.K : ℕ) 0 = ((D.K : ℕ) : ℤ) := by
      simp [PeriodicLattice.levelDepth]
    rw [Tower.MapsSublatticeOnto, hd] at ho
    refine ⟨⟨g, hi, ho⟩, fun x => (hg x).symm⟩
  · funext U
    change A (r.pullbackField (D.lift U)) = A (D.lift (s.pullback U))
    rw [pullbackField_lift D hs]
theorem periodShifts_invisible : D.PeriodShiftsInvisible := by
  refine ⟨latticeTranslate_mem D, fun v n hv A _ => ?_⟩
  funext U
  change A ((InfiniteLattice.shift v).pullbackField (D.lift U)) = A (D.lift U)
  congr 1
  refine Subtype.ext (funext fun b => Subtype.ext ?_)
  change ((D.lift U).1 ((InfiniteLattice.shift v).linkMap b) : Matrices.ComplexMatrix2) =
    ((D.lift U).1 b : Matrices.ComplexMatrix2)
  refine (lift_apply_coe D U _).trans (Eq.trans ?_ (lift_apply_coe D U b).symm)
  have hs : ∀ x : LatticePoint D.mesh,
      pointProj D ((InfiniteLattice.shift v).pointMap x) = pointProj D x := by
    intro x
    refine Subtype.ext ?_
    change TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m)
        ((x : AmbientSpace) + (v : AmbientSpace)) =
      TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) (x : AmbientSpace)
    rw [hv]
    exact TestFunctions.torusProj_add_latticeTranslate _ _ _
  have hb : linkProj D ((InfiniteLattice.shift v).linkMap b) = linkProj D b :=
    PeriodicLattice.Bond.ext (hs b.initial) (hs b.terminal)
  rw [hb]
theorem pullback_respects_algebra : D.PullbackRespectsAlgebra := by
  have hc : Continuous D.lift := InfiniteLattice.continuous_liftCompactField
  refine ⟨hc, fun A A' hO _ c => ⟨hO.1.comp hc.measurable, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩⟩
  · obtain ⟨C, hC⟩ := hO.2
    exact ⟨C, fun U => hC _⟩
  · obtain ⟨C, hC⟩ := hO.2
    have : Nonempty D.TorusField := ⟨PeriodicLattice.CompactGaugeField.identity _ _ _⟩
    refine ciSup_le fun U => ?_
    exact le_ciSup (f := fun V => ‖A V‖) ⟨C, by rintro _ ⟨V, rfl⟩; exact hC V⟩ _
theorem exists_projectPlaquette_eq (q : PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ)) :
    ∃ p : ElementaryPlaquette D.mesh, D.projectPlaquette p = q := by
  obtain ⟨x, hx, hxq⟩ :=
    (PeriodicLattice.sublattice_eq_map_latticeSubgroup D.L D.m ((D.K : ℕ) : ℤ)).le q.origin.2
  exact ⟨⟨⟨x, hx⟩, q.firstAxis, q.secondAxis, q.firstAxis_lt_secondAxis⟩,
    PeriodicLattice.Plaquette.ext (Subtype.ext hxq) rfl rfl⟩
def translatePlaquette (p : ElementaryPlaquette D.mesh) (n : Fin 4 → ℤ) :
    ElementaryPlaquette D.mesh :=
  ⟨p.corner + ⟨TestFunctions.latticeTranslate D.side n, latticeTranslate_mem D n⟩, p.lowAxis,
    p.highAxis, p.lowAxis_lt_highAxis⟩
theorem center_translatePlaquette (p : ElementaryPlaquette D.mesh) (n : Fin 4 → ℤ) :
    (translatePlaquette D p n).center = p.center + TestFunctions.latticeTranslate D.side n := by
  change (p.corner : AmbientSpace) + TestFunctions.latticeTranslate D.side n +
      Pi.single p.lowAxis (D.mesh / 2) + Pi.single p.highAxis (D.mesh / 2) =
    (p.corner : AmbientSpace) + Pi.single p.lowAxis (D.mesh / 2) +
      Pi.single p.highAxis (D.mesh / 2) + TestFunctions.latticeTranslate D.side n
  abel
theorem projectPlaquette_translatePlaquette (p : ElementaryPlaquette D.mesh) (n : Fin 4 → ℤ) :
    D.projectPlaquette (translatePlaquette D p n) = D.projectPlaquette p :=
  PeriodicLattice.Plaquette.ext
    (Subtype.ext (TestFunctions.torusProj_add_latticeTranslate _ _ _)) rfl rfl
theorem eq_translatePlaquette_of_projectPlaquette_eq {p p' : ElementaryPlaquette D.mesh}
    (h : D.projectPlaquette p = D.projectPlaquette p') : ∃ n, p = translatePlaquette D p' n := by
  have hb : TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) (p.corner : AmbientSpace) =
      TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) (p'.corner : AmbientSpace) :=
    congrArg (fun q : PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ) =>
      (q.origin : PeriodicLattice.FourTorus D.L D.m)) h
  obtain ⟨n, hn⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq hb
  exact ⟨n, InfiniteLattice.ElementaryPlaquette.ext (Subtype.ext hn)
    (congrArg PeriodicLattice.Plaquette.firstAxis h)
    (congrArg PeriodicLattice.Plaquette.secondAxis h)⟩
section Periodization
variable {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E]
omit [Module ℝ E] [TopologicalSpace E] in
theorem eq_zero_at_translate {S : Set AmbientSpace} {f : AmbientSpace → E}
    (hf : TestFunctions.IsPeriodizable D.side S f) {x : AmbientSpace} (hx : f x ≠ 0)
    {n : Fin 4 → ℤ} (hn : n ≠ 0) : f (x + TestFunctions.latticeTranslate D.side n) = 0 := by
  by_contra hne
  refine hn (eq_zero_of_norm_latticeTranslate_le (side_pos D) n ?_)
  have h := hf.1 _ (hf.2 hne) _ (hf.2 hx)
  simpa using h
theorem smearedEnergy_lift {S : Set AmbientSpace} {f : AmbientSpace → E}
    (hf : TestFunctions.IsPeriodizable D.side S f) (U : D.TorusField) :
    smearedEnergy f (D.lift U) =
      PeriodicLattice.smearedObservable (TestFunctions.periodize D.side f) U.1 := by
  set T : Set (ElementaryPlaquette D.mesh) := {p | f p.center ≠ 0} with hT
  set H : PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ) → E := fun q =>
    PeriodicLattice.plaquetteCost U.1 q • TestFunctions.periodize D.side f q.barycenter with hH
  have hinj : InjOn D.projectPlaquette T := by
    intro p hp p' hp' h
    obtain ⟨n, rfl⟩ := eq_translatePlaquette_of_projectPlaquette_eq D h
    by_cases hn : n = 0
    · subst hn
      refine InfiniteLattice.ElementaryPlaquette.ext (Subtype.ext ?_) rfl rfl
      change (p'.corner : AmbientSpace) + TestFunctions.latticeTranslate D.side 0 = _
      have : TestFunctions.latticeTranslate D.side 0 = 0 := by
        funext μ
        simp [TestFunctions.latticeTranslate]
      rw [this, add_zero]
    · exact absurd (by rw [center_translatePlaquette]; exact eq_zero_at_translate D hf hp' hn) hp
  have hval : ∀ p ∈ T, H (D.projectPlaquette p) = faceEnergy (D.lift U).1 p • f p.center := by
    intro p hp
    simp only [hH]
    rw [barycenter_projectPlaquette, ← faceEnergy_lift]
    congr 1
    change TestFunctions.periodize D.side f (TorusMetric.torusProj D.side p.center) = _
    rw [TestFunctions.periodize_torusProj, TestFunctions.periodicSum,
      tsum_eq_single (0 : Fin 4 → ℤ) fun n hn => eq_zero_at_translate D hf hp hn]
    have : TestFunctions.latticeTranslate D.side 0 = 0 := by
      funext μ
      simp [TestFunctions.latticeTranslate]
    rw [this, add_zero]
  have hsupp : Function.support H ⊆ D.projectPlaquette '' T := by
    intro q hq
    obtain ⟨p, rfl⟩ := exists_projectPlaquette_eq D q
    by_contra hno
    refine hq ?_
    simp only [hH]
    have h0 : TestFunctions.periodize D.side f (D.projectPlaquette p).barycenter = 0 := by
      rw [barycenter_projectPlaquette]
      change TestFunctions.periodize D.side f (TorusMetric.torusProj D.side p.center) = _
      rw [TestFunctions.periodize_torusProj, TestFunctions.periodicSum]
      have hz : ∀ n : Fin 4 → ℤ, f (p.center + TestFunctions.latticeTranslate D.side n) = 0 := by
        intro n
        by_contra hne
        refine hno ⟨translatePlaquette D p n, ?_, projectPlaquette_translatePlaquette D p n⟩
        change f (translatePlaquette D p n).center ≠ 0
        rw [center_translatePlaquette]
        exact hne
      simp only [hz, tsum_zero]
    rw [h0, smul_zero]
  have hG : Function.support (fun p : ElementaryPlaquette D.mesh =>
      faceEnergy (D.lift U).1 p • f p.center) ⊆ T := by
    intro p hp h0
    exact hp (by simp only [h0, smul_zero])
  calc smearedEnergy f (D.lift U)
      = ∑ᶠ p ∈ T, faceEnergy (D.lift U).1 p • f p.center := by
        rw [finsum_mem_def, Set.indicator_eq_self.2 hG]
        rfl
    _ = ∑ᶠ p ∈ T, H (D.projectPlaquette p) := finsum_mem_congr rfl fun p hp => (hval p hp).symm
    _ = ∑ᶠ q ∈ D.projectPlaquette '' T, H q := (finsum_mem_image hinj).symm
    _ = PeriodicLattice.smearedObservable (TestFunctions.periodize D.side f) U.1 := by
        rw [finsum_mem_def, Set.indicator_eq_self.2 hsupp]
        rfl
end Periodization
theorem projection_matches_faces : D.ProjectionMatchesFaces :=
  fun p U => ⟨barycenter_projectPlaquette D p, faceEnergy_lift D U p⟩
theorem pullback_smeared_eq_periodized : D.PullbackSmearedEqPeriodized := by
  intro S
  refine ⟨fun f _ _ hf U => smearedEnergy_lift D hf U, fun f _ _ hf U => ?_⟩
  exact congrArg (fun t : ℝ => (t : ℂ)) (smearedEnergy_lift D hf U)
end TorusPullback
open TorusPullback in
theorem symmetriesAndTorusPullback_holds
    (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hA : InfiniteLattice.SymmetryActionOnObservables) :
    SymmetriesAndTorusPullback := fun D =>
  ⟨pullback_respects_algebra D, symmetries_hyperoctahedral D hT, symmetries_closed D hA,
    actOn_respects_algebra D hA, symmetries_descend D hT, periodShifts_invisible D,
    projection_matches_faces D, pullback_smeared_eq_periodized D⟩
end YangMills.Construction.MultipleReflections
end

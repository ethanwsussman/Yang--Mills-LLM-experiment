import YangMills.Construction.RunningCouplingSlope.TheOrbitMapReadsNearCellsProof
import YangMills.Construction.Towers.DifferencesAndRestrictionsOfATowerAreMapsOfPeriodicFunctions
import YangMills.Construction.Towers.LatticesOfSideInfinityOverAFiniteSideProof
import YangMills.Construction.Towers.NormOfTheColourCoefficients
import YangMills.Construction.Towers.QuotientOfATowerCarriesSetsProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (torusProj)
noncomputable section
namespace YangMills.Construction.Tower.UnitScale.CoboundaryRestrictionPeriodicity
open OneStepChart
section Weights
variable {P : Type}
open Classical in
def indicatorWeight (c : P) (r : ℝ) : P → ℝ := fun p => if p = c then r else 0
theorem indicatorWeight_support_finite (c : P) (r : ℝ) : {p | indicatorWeight c r p ≠ 0}.Finite :=
  (finite_singleton c).subset fun p hp => by
    by_contra hc
    exact hp (if_neg hc)
theorem finsum_indicatorWeight_smul (c : P) (r : ℝ) (v : P → Matrices.ComplexMatrix2) :
    ∑ᶠ p, indicatorWeight c r p • v p = r • v c := by
  rw [finsum_eq_single _ c fun p hp => by simp [indicatorWeight, hp]]
  simp [indicatorWeight]
theorem support_weight_smul_subset (K : P → ℝ) (v : P → Matrices.ComplexMatrix2) :
    Function.support (fun p => K p • v p) ⊆ {p | K p ≠ 0} := fun p hp h => hp (by simp [h])
theorem finsum_add_weights_smul {K K' : P → ℝ} (hK : {p | K p ≠ 0}.Finite)
    (hK' : {p | K' p ≠ 0}.Finite) (v : P → Matrices.ComplexMatrix2) :
    ∑ᶠ p, (K p + K' p) • v p = ∑ᶠ p, K p • v p + ∑ᶠ p, K' p • v p := by
  rw [← finsum_add_distrib (hK.subset (support_weight_smul_subset K _))
    (hK'.subset (support_weight_smul_subset K' _))]
  exact finsum_congr fun p => add_smul _ _ _
theorem add_weights_support_finite {K K' : P → ℝ} (hK : {p | K p ≠ 0}.Finite)
    (hK' : {p | K' p ≠ 0}.Finite) : {p | K p + K' p ≠ 0}.Finite :=
  (hK.union hK').subset fun p hp => by
    by_contra hc
    simp only [mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
    exact hp (by simp [hc.1, hc.2])
theorem apply_mem_traceless {σ : Type} {f : σ → Matrices.ComplexMatrix2}
    (h : f ∈ Matrices.GroupLieProduct.tracelessFunctions σ) (x : σ) :
    f x ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.PauliCoefficientNorm.apply_mem_traceless <;> assumption
theorem mem_tracelessFunctions_of_apply {σ : Type} {f : σ → Matrices.ComplexMatrix2}
    (h : ∀ x, f x ∈ Matrices.ComplexMatrix2.traceless) :
    f ∈ Matrices.GroupLieProduct.tracelessFunctions σ :=
  Submodule.mem_pi.2 fun x _ => h x
end Weights
section Points
variable {a a' : ℝ}
theorem coe_toFiner (y : InfiniteLattice.LatticePoint a)
    (h : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a') :
    ((FullSpace.toFiner a' y : InfiniteLattice.LatticePoint a') : AmbientSpace) = y := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.coe_toFiner <;> assumption
theorem latticeSubgroup_le_of_eq_mul (N : ℤ) (h : a' = N * a) :
    InfiniteLattice.latticeSubgroup a' ≤ InfiniteLattice.latticeSubgroup a := by apply _root_.YangMills.Construction.FullLatticeOverTorus.latticeSubgroup_le_of_eq_zmul <;> assumption
theorem latticeSubgroup_meshAt_antitone {L : ℕ} (hL : L ≠ 0) (k : ℕ) {i j : ℕ} (h : i ≤ j) :
    InfiniteLattice.latticeSubgroup (meshAt L k j) ≤ InfiniteLattice.latticeSubgroup (meshAt L k i) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  refine latticeSubgroup_le_of_eq_mul ((L : ℤ) ^ d) ?_
  have e : (((i + d : ℕ) : ℤ) - (k : ℤ)) = (d : ℤ) + ((i : ℤ) - (k : ℤ)) := by
    push_cast
    ring
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  simp only [meshAt]
  rw [e, zpow_add₀ hL', zpow_natCast]
  push_cast
  ring
theorem intCast_mem_latticeSubgroup {L : ℕ} (hL : L ≠ 0) {k i : ℕ} (h : i ≤ k) (z : Fin 4 → ℤ) :
    (fun μ => (z μ : ℝ)) ∈ InfiniteLattice.latticeSubgroup (meshAt L k i) := by
  refine latticeSubgroup_meshAt_antitone hL k h ⟨z, fun μ => ?_⟩
  simp [meshAt]
theorem coe_integerPoint {L : ℕ} (hL : L ≠ 0) {k i : ℕ} (h : i ≤ k) (z : Fin 4 → ℤ) :
    ((integerPoint (meshAt L k i) z : InfiniteLattice.LatticePoint (meshAt L k i)) : AmbientSpace) =
      fun μ => (z μ : ℝ) :=
  coe_toFiner _ (intCast_mem_latticeSubgroup hL h z)
end Points
section Links
variable {L m k j : ℕ}
theorem link_ext {a : ℝ} {b c : InfiniteLattice.Link a} (h : b.initial = c.initial)
    (h' : b.terminal = c.terminal) : b = c := by
  obtain ⟨t, s, _⟩ := b
  obtain ⟨t', s', _⟩ := c
  simp only at h h'
  subst h h'
  rfl
theorem bond_ext {l : ℤ} {b c : PeriodicLattice.Bond L m l} (h : b.source = c.source)
    (h' : b.target = c.target) : b = c := by apply _root_.YangMills.SharedProofs.p29034 <;> assumption
theorem linkTranslate_forwardFrom {a : ℝ} (x v : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    linkTranslate (InfiniteLattice.Link.forwardFrom x μ) v =
      InfiniteLattice.Link.forwardFrom (x + v) μ :=
  link_ext rfl (add_right_comm _ _ _)
theorem projVertex_add (x y : FullSpace.Vertex L k j) :
    FullSpace.projVertex L m k j (x + y) =
      FullSpace.projVertex L m k j x + FullSpace.projVertex L m k j y := by apply _root_.YangMills.Construction.Tower.FullSpace.ProjectionSets.projVertex_add <;> assumption
theorem projVertex_axisStep (μ : Fin 4) :
    FullSpace.projVertex L m k j (InfiniteLattice.axisStep (meshAt L k j) μ) =
      PeriodicLattice.unitStep L m (PeriodicLattice.levelDepth k j) μ := by apply _root_.YangMills.Construction.Tower.EdgeProjection.projVertex_axisStep <;> assumption
theorem projEdge_forwardFrom (hq : EdgeProjectionProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hj : j ≤ k) (x : FullSpace.Vertex L k j) (μ : Fin 4) :
    FullSpace.projEdge L m k j (InfiniteLattice.Link.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom (FullSpace.projVertex L m k j x) μ := by
  obtain ⟨ht, hh, -, -⟩ := (hq L m k j hL hm hj).1 (InfiniteLattice.Link.forwardFrom x μ)
  refine bond_ext ht (hh.trans ?_)
  show FullSpace.projVertex L m k j (x + InfiniteLattice.axisStep (meshAt L k j) μ) = _
  rw [projVertex_add, projVertex_axisStep]
  rfl
def positiveForwardFrom {a : ℝ} (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    FullSpace.PositiveEdge a :=
  ⟨InfiniteLattice.Link.forwardFrom x μ, μ, add_sub_cancel_left _ _⟩
end Links
section Operators
variable {L m k : ℕ}
theorem vertexCoboundary_eq_finsum {a : ℝ} (q : FullSpace.PositiveEdge a)
    (f : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) :
    FullSpace.restrictToPositiveEdges (FullSpace.vertexCoboundary f) q =
      ∑ᶠ p : InfiniteLattice.LatticePoint a,
        (indicatorWeight q.1.terminal 1 p + indicatorWeight q.1.initial (-1) p) • f p := by
  rw [finsum_add_weights_smul (indicatorWeight_support_finite _ _)
      (indicatorWeight_support_finite _ _), finsum_indicatorWeight_smul,
    finsum_indicatorWeight_smul, one_smul, neg_one_smul, ← sub_eq_add_neg]
  rfl
theorem vertexCoboundary_periodicOperator (hq : EdgeProjectionProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) {j : ℕ} (hj : j ≤ k) :
    PeriodicOperator (vertexFunctions L m k j) (edgeForms L m k j)
      FullSpace.vertexCoboundary Tower.vertexCoboundary where
  full_mem f hf :=
    ⟨fun _ _ => Matrices.ComplexMatrix2.traceless.sub_mem (apply_mem_traceless hf _)
      (apply_mem_traceless hf _), fun _ => (neg_sub _ _).symm⟩
  torus_mem f hf :=
    ⟨fun _ _ => Matrices.ComplexMatrix2.traceless.sub_mem (apply_mem_traceless hf _)
      (apply_mem_traceless hf _), fun _ => (neg_sub _ _).symm⟩
  map_extend f _ := by
    funext b
    obtain ⟨ht, hh, -, -⟩ := (hq L m k j hL hm hj).1 b
    show f (FullSpace.projVertex L m k j b.terminal) - f (FullSpace.projVertex L m k j b.initial) =
      f (FullSpace.projEdge L m k j b).target - f (FullSpace.projEdge L m k j b).source
    rw [ht, hh]
  commutes z f _ := by
    funext b
    rfl
  realKernel := by
    refine ⟨fun (q : FullSpace.PositiveEdge (meshAt L k j)) (p : FullSpace.Vertex L k j) =>
        indicatorWeight q.1.terminal 1 p + indicatorWeight q.1.initial (-1) p,
      fun q => add_weights_support_finite (indicatorWeight_support_finite _ _)
        (indicatorWeight_support_finite _ _),
      fun f _ q => ?_⟩
    exact vertexCoboundary_eq_finsum q f
theorem edgeCoboundary_projEdge (hq : EdgeProjectionProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {j : ℕ} (hj : j ≤ k)
    (B : Tower.Edge L m k j → Matrices.ComplexMatrix2) (p : FullSpace.Face L k j) :
    FullSpace.edgeCoboundary (fun b => B (FullSpace.projEdge L m k j b)) p =
      Tower.edgeCoboundary B (FullSpace.projFace L m k j p) := by
  simp only [FullSpace.edgeCoboundary, Tower.edgeCoboundary, FullSpace.projFace,
    projEdge_forwardFrom hq hL hm hj, projVertex_add, projVertex_axisStep]
theorem edgeCoboundary_linkTranslate {a : ℝ} (B : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (v : InfiniteLattice.LatticePoint a) (p : InfiniteLattice.ElementaryPlaquette a) :
    FullSpace.edgeCoboundary (fun b => B (linkTranslate b v)) p =
      FullSpace.edgeCoboundary B ⟨p.corner + v, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩ := by
  simp only [FullSpace.edgeCoboundary, linkTranslate_forwardFrom]
  rw [add_right_comm p.corner (InfiniteLattice.axisStep a p.lowAxis) v,
    add_right_comm p.corner (InfiniteLattice.axisStep a p.highAxis) v]
theorem edgeCoboundary_eq_finsum {a : ℝ} (q : InfiniteLattice.ElementaryPlaquette a)
    (B : InfiniteLattice.Link a → Matrices.ComplexMatrix2) :
    FullSpace.edgeCoboundary B q =
      ∑ᶠ p : FullSpace.PositiveEdge a,
        (indicatorWeight (positiveForwardFrom q.corner q.lowAxis) 1 p +
          indicatorWeight (positiveForwardFrom (q.corner + InfiniteLattice.axisStep a q.lowAxis)
            q.highAxis) 1 p +
          indicatorWeight (positiveForwardFrom (q.corner + InfiniteLattice.axisStep a q.highAxis)
            q.lowAxis) (-1) p +
          indicatorWeight (positiveForwardFrom q.corner q.highAxis) (-1) p) •
            FullSpace.restrictToPositiveEdges B p := by
  have h₁ := add_weights_support_finite
    (indicatorWeight_support_finite (positiveForwardFrom q.corner q.lowAxis) 1)
    (indicatorWeight_support_finite
      (positiveForwardFrom (q.corner + InfiniteLattice.axisStep a q.lowAxis) q.highAxis) 1)
  have h₂ := add_weights_support_finite h₁
    (indicatorWeight_support_finite
      (positiveForwardFrom (q.corner + InfiniteLattice.axisStep a q.highAxis) q.lowAxis) (-1))
  rw [finsum_add_weights_smul h₂ (indicatorWeight_support_finite _ _),
    finsum_add_weights_smul h₁ (indicatorWeight_support_finite _ _),
    finsum_add_weights_smul (indicatorWeight_support_finite _ _)
      (indicatorWeight_support_finite _ _),
    finsum_indicatorWeight_smul, finsum_indicatorWeight_smul, finsum_indicatorWeight_smul,
    finsum_indicatorWeight_smul]
  simp only [one_smul, neg_one_smul, FullSpace.edgeCoboundary, FullSpace.restrictToPositiveEdges,
    positiveForwardFrom, sub_eq_add_neg]
theorem edgeCoboundary_periodicOperator (hq : EdgeProjectionProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {j : ℕ} (hj : j ≤ k) :
    PeriodicOperator (edgeForms L m k j) (faceFunctions L m k j)
      FullSpace.edgeCoboundary Tower.edgeCoboundary where
  full_mem B hB := by
    have h : ∀ (x : FullSpace.Vertex L k j) (μ : Fin 4),
        B (InfiniteLattice.Link.forwardFrom x μ) ∈ Matrices.ComplexMatrix2.traceless :=
      fun x μ => hB.1 _ ⟨μ, add_sub_cancel_left _ _⟩
    exact mem_tracelessFunctions_of_apply fun p =>
      Matrices.ComplexMatrix2.traceless.sub_mem (Matrices.ComplexMatrix2.traceless.sub_mem
        (Matrices.ComplexMatrix2.traceless.add_mem (h _ _) (h _ _)) (h _ _)) (h _ _)
  torus_mem B hB := by
    have h : ∀ (x : Tower.Vertex L m k j) (μ : Fin 4),
        B (PeriodicLattice.Bond.forwardFrom x μ) ∈ Matrices.ComplexMatrix2.traceless :=
      fun x μ => hB.1 _ ⟨μ, add_sub_cancel_left _ _⟩
    exact mem_tracelessFunctions_of_apply fun p =>
      Matrices.ComplexMatrix2.traceless.sub_mem (Matrices.ComplexMatrix2.traceless.sub_mem
        (Matrices.ComplexMatrix2.traceless.add_mem (h _ _) (h _ _)) (h _ _)) (h _ _)
  map_extend B _ := by
    funext p
    exact edgeCoboundary_projEdge hq hL hm hj B p
  commutes z B _ := by
    funext p
    exact edgeCoboundary_linkTranslate B _ p
  realKernel :=
    ⟨fun (q : FullSpace.Face L k j) (p : FullSpace.PositiveEdge (meshAt L k j)) =>
        indicatorWeight (positiveForwardFrom q.corner q.lowAxis) 1 p +
          indicatorWeight (positiveForwardFrom
            (q.corner + InfiniteLattice.axisStep (meshAt L k j) q.lowAxis) q.highAxis) 1 p +
          indicatorWeight (positiveForwardFrom
            (q.corner + InfiniteLattice.axisStep (meshAt L k j) q.highAxis) q.lowAxis) (-1) p +
          indicatorWeight (positiveForwardFrom q.corner q.highAxis) (-1) p,
      fun q => add_weights_support_finite (add_weights_support_finite (add_weights_support_finite
        (indicatorWeight_support_finite _ _) (indicatorWeight_support_finite _ _))
        (indicatorWeight_support_finite _ _)) (indicatorWeight_support_finite _ _),
      fun B _ q => edgeCoboundary_eq_finsum q B⟩
theorem restrict_periodicOperator (hL : L ≠ 0) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ k) :
    PeriodicOperator (vertexFunctions L m k i) (vertexFunctions L m k j)
      (FullSpace.restrictVertexFunction (meshAt L k j)) (Tower.restrictVertexFunction j) where
  full_mem f hf := mem_tracelessFunctions_of_apply fun _ => apply_mem_traceless hf _
  torus_mem f hf := mem_tracelessFunctions_of_apply fun _ => apply_mem_traceless hf _
  map_extend f _ := by
    funext x
    have hx := coe_toFiner (a' := meshAt L k i) x (latticeSubgroup_meshAt_antitone hL k hij x.2)
    have hw : ((FullSpace.projVertex L m k i (FullSpace.toFiner (meshAt L k i) x) :
          Tower.Vertex L m k i) : PeriodicLattice.FourTorus L m) =
        (FullSpace.projVertex L m k j x : Tower.Vertex L m k j) := by
      show torusProj (PeriodicLattice.torusSide L m)
          ((FullSpace.toFiner (meshAt L k i) x : InfiniteLattice.LatticePoint (meshAt L k i)) :
            AmbientSpace) = torusProj (PeriodicLattice.torusSide L m) (x : AmbientSpace)
      rw [hx]
    have hs := Classical.epsilon_spec
      (p := fun u : Tower.Vertex L m k i => (u : PeriodicLattice.FourTorus L m) =
        (FullSpace.projVertex L m k j x : Tower.Vertex L m k j)) ⟨_, hw⟩
    exact congrArg f (Subtype.ext (hw.trans hs.symm))
  commutes z f _ := by
    funext y
    have hi : i ≤ k := hij.trans hj
    have hs := latticeSubgroup_meshAt_antitone hL k hij
    have e : FullSpace.toFiner (meshAt L k i) y + integerPoint (meshAt L k i) (-z) =
        FullSpace.toFiner (meshAt L k i) (y + integerPoint (meshAt L k j) (-z)) := by
      refine Subtype.ext ?_
      rw [coe_toFiner _ (hs (y + integerPoint (meshAt L k j) (-z)).2)]
      show ((FullSpace.toFiner (meshAt L k i) y : InfiniteLattice.LatticePoint (meshAt L k i)) :
          AmbientSpace) + (integerPoint (meshAt L k i) (-z) :
            InfiniteLattice.LatticePoint (meshAt L k i)) =
        (y : AmbientSpace) + (integerPoint (meshAt L k j) (-z) :
          InfiniteLattice.LatticePoint (meshAt L k j))
      rw [coe_toFiner y (hs y.2), coe_integerPoint hL hi, coe_integerPoint hL hj]
    exact congrArg f e
  realKernel :=
    ⟨fun (q : FullSpace.Vertex L k j) (p : FullSpace.Vertex L k i) =>
        indicatorWeight (FullSpace.toFiner (meshAt L k i) q) 1 p,
      fun q => indicatorWeight_support_finite _ _,
      fun f _ q => by
        refine Eq.trans ?_
          (finsum_indicatorWeight_smul (FullSpace.toFiner (meshAt L k i) q) 1 f).symm
        exact (one_smul ℝ _).symm⟩
end Operators
theorem holds (hq : EdgeProjectionProperties) : Statement :=
  fun _ hL _ _ hm =>
    ⟨fun _ hj => vertexCoboundary_periodicOperator hq hL hm hj,
      fun _ hj => edgeCoboundary_periodicOperator hq hL hm hj,
      fun _ _ hij hj => restrict_periodicOperator (by have := hL.2; omega) hij hj⟩
end YangMills.Construction.Tower.UnitScale.CoboundaryRestrictionPeriodicity
end

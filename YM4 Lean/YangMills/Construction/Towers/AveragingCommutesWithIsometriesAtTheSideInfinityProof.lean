import YangMills.Construction.Towers.AverageIsDifferentiableOnThePolydiscProof
import YangMills.Construction.Towers.AveragesAtTheSideInfinityNearTheTrivialConfigurationProof
import YangMills.Construction.Towers.AveragingCommutesWithIsometriesAtTheSideInfinity
import YangMills.Construction.Towers.AveragingCommutesWithIsometriesOnTheSides
import YangMills.Construction.Towers.GaugeAndIsometricImagesAreConfigurations
import YangMills.Construction.Towers.WhatTheDilationKeepsProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.EquivariantSmoothing
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Matrices (ComplexMatrix2)
section Space
variable {a : ℝ} {f : AmbientSpace → AmbientSpace}
theorem coe_vertexImage (hM : MapsSublatticeOnto a f) (x : InfiniteLattice.LatticePoint a) :
    ((vertexImage f x : InfiniteLattice.LatticePoint a) : AmbientSpace) = f x := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.coe_space_vertexImage <;> assumption
theorem apply_vertexPreimage (hM : MapsSublatticeOnto a f) (x : InfiniteLattice.LatticePoint a) :
    f (vertexPreimage f x : InfiniteLattice.LatticePoint a) = x := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingInvariance.vertexPreimage_spec <;> assumption
theorem edgeImage_endpoints (hM : MapsSublatticeOnto a f) (hB : MapsLinksOnto a f)
    (b : InfiniteLattice.Link a) :
    (edgeImage f b).initial = vertexImage f b.initial ∧
      (edgeImage f b).terminal = vertexImage f b.terminal := by
  obtain ⟨b', h₁, h₂⟩ := hB.1 b
  exact Classical.epsilon_spec
    (p := fun b' : InfiniteLattice.Link a =>
      b'.initial = vertexImage f b.initial ∧ b'.terminal = vertexImage f b.terminal)
    ⟨b', Subtype.ext (h₁.trans (coe_vertexImage hM _).symm),
      Subtype.ext (h₂.trans (coe_vertexImage hM _).symm)⟩
theorem edgePreimage_endpoints (hM : MapsSublatticeOnto a f) (hB : MapsLinksOnto a f)
    (hi : Function.Injective f) (b : InfiniteLattice.Link a) :
    (edgePreimage f b).initial = vertexPreimage f b.initial ∧
      (edgePreimage f b).terminal = vertexPreimage f b.terminal := by
  obtain ⟨b₀, h₁, h₂⟩ := hB.2 b
  exact Classical.epsilon_spec
    (p := fun b' : InfiniteLattice.Link a =>
      b'.initial = vertexPreimage f b.initial ∧ b'.terminal = vertexPreimage f b.terminal)
    ⟨b₀, Subtype.ext (hi (h₁.symm.trans (apply_vertexPreimage hM _).symm)),
      Subtype.ext (hi (h₂.symm.trans (apply_vertexPreimage hM _).symm))⟩
theorem edgeImage_edgePreimage (hM : MapsSublatticeOnto a f) (hB : MapsLinksOnto a f)
    (hi : Function.Injective f) (b : InfiniteLattice.Link a) :
    edgeImage f (edgePreimage f b) = b := by
  obtain ⟨t, h⟩ := edgeImage_endpoints hM hB (edgePreimage f b)
  obtain ⟨t', h'⟩ := edgePreimage_endpoints hM hB hi b
  refine InfiniteLattice.Link.ext ?_ ?_
  · rw [t, t']
    exact Subtype.ext ((coe_vertexImage hM _).trans (apply_vertexPreimage hM _))
  · rw [h, h']
    exact Subtype.ext ((coe_vertexImage hM _).trans (apply_vertexPreimage hM _))
theorem edgeImage_opposite (hM : MapsSublatticeOnto a f) (hB : MapsLinksOnto a f)
    (b : InfiniteLattice.Link a) : edgeImage f b.opposite = (edgeImage f b).opposite := by
  obtain ⟨t, h⟩ := edgeImage_endpoints hM hB b
  obtain ⟨t', h'⟩ := edgeImage_endpoints hM hB b.opposite
  refine InfiniteLattice.Link.ext ?_ ?_
  · rw [t']; exact h.symm
  · rw [h']; exact t.symm
theorem not_isPositivelyOriented_opposite (ha : a ≠ 0) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.PolydiscSmoothing.not_opposite_isPositivelyOriented <;> assumption
theorem isPositivelyOriented_opposite {b : InfiniteLattice.Link a}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
end Space
section Torus
variable {L n k j : ℕ} {g : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
theorem coe_torusVertexImage (hM : Tower.MapsSublatticeOnto k j g) (x : Tower.Vertex L n k j) :
    ((Tower.vertexImage (k := k) (j := j) g x : Tower.Vertex L n k j) :
      PeriodicLattice.FourTorus L n) = g x := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.coe_torus_vertexImage <;> assumption
theorem apply_torusVertexPreimage (hM : Tower.MapsSublatticeOnto k j g)
    (x : Tower.Vertex L n k j) :
    g (Tower.vertexPreimage (k := k) (j := j) g x : Tower.Vertex L n k j) = x := by apply _root_.YangMills.Construction.Tower.ScalingInvariance.vertexPreimage_spec <;> assumption
theorem eq_of_torus_apply_eq [Finite (Tower.Vertex L n k j)] (hM : Tower.MapsSublatticeOnto k j g)
    (x y : Tower.Vertex L n k j) (h : g x = g y) : x = y := by
  have hs : Function.Surjective
      (fun x : Tower.Vertex L n k j =>
        (Tower.vertexImage (k := k) (j := j) g x : Tower.Vertex L n k j)) := by
    intro z
    refine ⟨Tower.vertexPreimage (k := k) (j := j) g z, Subtype.ext ?_⟩
    exact (coe_torusVertexImage hM _).trans (apply_torusVertexPreimage hM z)
  refine (Finite.injective_iff_surjective.2 hs) (Subtype.ext ?_)
  exact (coe_torusVertexImage hM x).trans (h.trans (coe_torusVertexImage hM y).symm)
theorem torusEdgeImage_endpoints (hM : Tower.MapsSublatticeOnto k j g)
    (hB : Tower.MapsEdgesOnto k j g) (b : Tower.Edge L n k j) :
    (Tower.edgeImage (k := k) (j := j) g b).source =
        Tower.vertexImage (k := k) (j := j) g b.source ∧
      (Tower.edgeImage (k := k) (j := j) g b).target =
        Tower.vertexImage (k := k) (j := j) g b.target := by
  obtain ⟨b', h₁, h₂⟩ := hB.1 b
  exact Classical.epsilon_spec
    (p := fun b' : Tower.Edge L n k j =>
      b'.source = Tower.vertexImage (k := k) (j := j) g b.source ∧
        b'.target = Tower.vertexImage (k := k) (j := j) g b.target)
    ⟨b', Subtype.ext (h₁.trans (coe_torusVertexImage hM _).symm),
      Subtype.ext (h₂.trans (coe_torusVertexImage hM _).symm)⟩
theorem torusEdgePreimage_endpoints [Finite (Tower.Vertex L n k j)]
    (hM : Tower.MapsSublatticeOnto k j g)
    (hB : Tower.MapsEdgesOnto k j g) (b : Tower.Edge L n k j) :
    (Tower.edgePreimage (k := k) (j := j) g b).source =
        Tower.vertexPreimage (k := k) (j := j) g b.source ∧
      (Tower.edgePreimage (k := k) (j := j) g b).target =
        Tower.vertexPreimage (k := k) (j := j) g b.target := by
  obtain ⟨b₀, h₁, h₂⟩ := hB.2 b
  exact Classical.epsilon_spec
    (p := fun b' : Tower.Edge L n k j =>
      b'.source = Tower.vertexPreimage (k := k) (j := j) g b.source ∧
        b'.target = Tower.vertexPreimage (k := k) (j := j) g b.target)
    ⟨b₀, eq_of_torus_apply_eq hM _ _ (h₁.symm.trans (apply_torusVertexPreimage hM _).symm),
      eq_of_torus_apply_eq hM _ _ (h₂.symm.trans (apply_torusVertexPreimage hM _).symm)⟩
theorem torusEdgeImage_torusEdgePreimage [Finite (Tower.Vertex L n k j)]
    (hM : Tower.MapsSublatticeOnto k j g)
    (hB : Tower.MapsEdgesOnto k j g) (b : Tower.Edge L n k j) :
    Tower.edgeImage (k := k) (j := j) g (Tower.edgePreimage (k := k) (j := j) g b) = b := by
  obtain ⟨t, h⟩ := torusEdgeImage_endpoints hM hB (Tower.edgePreimage (k := k) (j := j) g b)
  obtain ⟨t', h'⟩ := torusEdgePreimage_endpoints hM hB b
  refine PeriodicLattice.Bond.ext ?_ ?_
  · rw [t, t']
    exact Subtype.ext ((coe_torusVertexImage hM _).trans (apply_torusVertexPreimage hM _))
  · rw [h, h']
    exact Subtype.ext ((coe_torusVertexImage hM _).trans (apply_torusVertexPreimage hM _))
theorem torusEdgePreimage_torusEdgeImage [Finite (Tower.Vertex L n k j)]
    (hM : Tower.MapsSublatticeOnto k j g)
    (hB : Tower.MapsEdgesOnto k j g) (b : Tower.Edge L n k j) :
    Tower.edgePreimage (k := k) (j := j) g (Tower.edgeImage (k := k) (j := j) g b) = b := by
  obtain ⟨t, h⟩ := torusEdgePreimage_endpoints hM hB (Tower.edgeImage (k := k) (j := j) g b)
  obtain ⟨t', h'⟩ := torusEdgeImage_endpoints hM hB b
  refine PeriodicLattice.Bond.ext ?_ ?_
  · rw [t, t']
    exact eq_of_torus_apply_eq hM _ _
      ((apply_torusVertexPreimage hM _).trans (coe_torusVertexImage hM _))
  · rw [h, h']
    exact eq_of_torus_apply_eq hM _ _
      ((apply_torusVertexPreimage hM _).trans (coe_torusVertexImage hM _))
theorem torusEdgeImage_opposite (hM : Tower.MapsSublatticeOnto k j g)
    (hB : Tower.MapsEdgesOnto k j g) (b : Tower.Edge L n k j) :
    Tower.edgeImage (k := k) (j := j) g b.opposite =
      (Tower.edgeImage (k := k) (j := j) g b).opposite := by
  obtain ⟨t, h⟩ := torusEdgeImage_endpoints hM hB b
  obtain ⟨t', h'⟩ := torusEdgeImage_endpoints hM hB b.opposite
  refine PeriodicLattice.Bond.ext ?_ ?_
  · rw [t']; exact h.symm
  · rw [h']; exact t.symm
end Torus
theorem exists_ball_of_eventuallyNearIdentity {ι : Type*} [Finite ι]
    {D : Set (ι → ComplexMatrix2)} {P : (ι → ComplexMatrix2) → Prop}
    (h : Tower.EventuallyNearIdentity D P) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ W ∈ D, (∀ b, ComplexMatrix2.operatorNorm (W b - 1) < ε) → P W := by
  obtain ⟨u, hu, hs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 h
  have := Fintype.ofFinite ι
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 hu
  refine ⟨ε, hε, fun W hW hn => hs ⟨hb ?_, hW⟩⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro b
  rw [dist_eq_norm]
  exact hn b
theorem operatorNorm_mul_four_sub_one_lt (hG : ComplexMatrix2.SpecialUnitaryAngleBounds)
    {A B C D : ComplexMatrix2} {r : ℝ}
    (hA : A ∈ ComplexMatrix2.specialUnitary) (hB : B ∈ ComplexMatrix2.specialUnitary)
    (hC : C ∈ ComplexMatrix2.specialUnitary) (hD : D ∈ ComplexMatrix2.specialUnitary)
    (a : ComplexMatrix2.operatorNorm (A - 1) < r) (b : ComplexMatrix2.operatorNorm (B - 1) < r)
    (c : ComplexMatrix2.operatorNorm (C - 1) < r) (d : ComplexMatrix2.operatorNorm (D - 1) < r) :
    ComplexMatrix2.operatorNorm (A * (B * (C * D)) - 1) < 4 * r := by apply _root_.YangMills.Construction.Tower.FullSpace.NearIdentitySmoothing.operatorNorm_mul_four_sub_one_lt <;> assumption
theorem doubleBlockCurvature_lt (hG : ComplexMatrix2.SpecialUnitaryAngleBounds) {L m : ℕ}
    {j j' : ℤ} [Finite (PeriodicLattice.Plaquette L m j')]
    (c : PeriodicLattice.Bond L m j) (W : PeriodicLattice.Bond L m j' → ComplexMatrix2) {ω : ℝ}
    (hω : 0 < ω)
    (hW : ∀ b, W b ∈ PeriodicLattice.compactGaugeGroup ∧
      ComplexMatrix2.operatorNorm (W b - 1) < ω / 4) :
    PeriodicLattice.doubleBlockCurvature W c < ω := by
  unfold PeriodicLattice.doubleBlockCurvature
  rcases isEmpty_or_nonempty ↥(PeriodicLattice.doubleBlockPlaquettes c :
      Set (PeriodicLattice.Plaquette L m j')) with he | he
  · rw [Real.iSup_of_isEmpty]
    exact hω
  · obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite
      (f := fun p : ↥(PeriodicLattice.doubleBlockPlaquettes c :
        Set (PeriodicLattice.Plaquette L m j')) =>
          ComplexMatrix2.operatorNorm (PeriodicLattice.plaquetteHolonomy W p.1 - 1))
    rw [← hp]
    obtain ⟨a₁, a₂⟩ := hW (PeriodicLattice.Bond.forwardFrom p.1.origin p.1.firstAxis)
    obtain ⟨b₁, b₂⟩ := hW (PeriodicLattice.Bond.forwardFrom
      (p.1.origin + PeriodicLattice.unitStep L m j' p.1.firstAxis) p.1.secondAxis)
    obtain ⟨d₁, d₂⟩ := hW (PeriodicLattice.Bond.forwardFrom
      (p.1.origin + PeriodicLattice.unitStep L m j' p.1.secondAxis) p.1.firstAxis).opposite
    obtain ⟨e₁, e₂⟩ := hW (PeriodicLattice.Bond.forwardFrom p.1.origin p.1.secondAxis).opposite
    have key := operatorNorm_mul_four_sub_one_lt hG a₁ b₁ d₁ e₁ a₂ b₂ d₂ e₂
    have h4 : 4 * (ω / 4) = ω := by ring
    rw [h4] at key
    simpa [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
      PeriodicLattice.Plaquette.boundaryBonds] using key
theorem projField_properties (hQ : Tower.EdgeProjectionProperties) {L k i : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hi : i ≤ k)
    {c : FullSpace.Edge L k (i + 1)}
    (Q : ProjPreservesStructures L 1 k i c) {V : FullSpace.Edge L k i → ComplexMatrix2}
    (hV : V ∈ fieldSpace L k i) {r : ℝ} (hr : 0 < r)
    (hVb : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r) :
    projField L 1 k i (doubleCubeLinks L (Tower.meshAt L k i) c) V ∈
        Tower.fieldSpace L 1 k i ∧
      (∀ β, ComplexMatrix2.operatorNorm
        (projField L 1 k i (doubleCubeLinks L (Tower.meshAt L k i) c) V β - 1) < r) ∧
      (∀ b ∈ doubleCubeLinks L (Tower.meshAt L k i) c,
        projField L 1 k i (doubleCubeLinks L (Tower.meshAt L k i) c) V
          (projEdge L 1 k i b) = V b) ∧
      ∀ β, (∀ b ∈ doubleCubeLinks L (Tower.meshAt L k i) c, projEdge L 1 k i b ≠ β) →
        projField L 1 k i (doubleCubeLinks L (Tower.meshAt L k i) c) V β = 1 := by
  have hcV : IsFieldOn PeriodicLattice.complexGaugeGroup
      (doubleCubeLinks L (Tower.meshAt L k i) c) V :=
    ⟨fun b _ => (Matrix.mem_specialUnitaryGroup_iff.mp (hV.1 b)).2, fun b _ => hV.2 b⟩
  have hon := (Q.projField_spec V hcV).1
  have hoff : ∀ β, (∀ b ∈ doubleCubeLinks L (Tower.meshAt L k i) c, projEdge L 1 k i b ≠ β) →
      projField L 1 k i (doubleCubeLinks L (Tower.meshAt L k i) c) V β = 1 := by
    intro β hβ
    unfold projField
    rw [dif_neg]
    rintro ⟨b, hb, e⟩
    exact hβ b hb e
  have hrev := (hQ L 1 k i hL one_pos hi).1
  have hPrev : ∀ b ∈ doubleCubeLinks L (Tower.meshAt L k i) c,
      b.opposite ∈ doubleCubeLinks L (Tower.meshAt L k i) c := fun b hb => ⟨hb.2, hb.1⟩
  refine ⟨⟨fun β _ => ?_, fun β _ => ?_⟩, fun β => ?_, hon, hoff⟩
  · by_cases h : ∃ b ∈ doubleCubeLinks L (Tower.meshAt L k i) c, projEdge L 1 k i b = β
    · obtain ⟨b, hb, rfl⟩ := h
      rw [hon b hb]
      exact hV.1 b
    · rw [hoff β fun b hb e => h ⟨b, hb, e⟩]
      exact one_mem ComplexMatrix2.specialUnitary
  · by_cases h : ∃ b ∈ doubleCubeLinks L (Tower.meshAt L k i) c, projEdge L 1 k i b = β
    · obtain ⟨b, hb, rfl⟩ := h
      rw [(hrev b).2.2.2, hon _ (hPrev b hb), hon b hb]
      exact hV.2 b
    · rw [hoff β fun b hb e => h ⟨b, hb, e⟩, hoff β.opposite, inv_one]
      intro b hb e
      refine h ⟨b.opposite, hPrev b hb, ?_⟩
      rw [← (hrev b).2.2.2, e]
      rfl
  · by_cases h : ∃ b ∈ doubleCubeLinks L (Tower.meshAt L k i) c, projEdge L 1 k i b = β
    · obtain ⟨b, hb, rfl⟩ := h
      rw [hon b hb]
      exact hVb b
    · rw [hoff β fun b hb e => h ⟨b, hb, e⟩]
      simpa using hr
theorem complexBlockAverage_eq_near_identity (hS : PeriodicLattice.AveragingSchemeProperties)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hG : ComplexMatrix2.SpecialUnitaryAngleBounds)
    {L k i : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hik : i < k)
    {W : Tower.Edge L 1 k i → ComplexMatrix2} (hW : W ∈ Tower.fieldSpace L 1 k i)
    (hWb : ∀ β, ComplexMatrix2.operatorNorm (W β - 1) < Averaging.smoothingRadius L / 4)
    {d : Tower.Edge L 1 k (i + 1)} (hd : d.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverage W d = Tower.smoothingStep L 1 k i W d ∧
      ∀ y ∈ ({d.source, d.target} : Set (Tower.Vertex L 1 k (i + 1))),
        ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
          PeriodicLattice.complexMeanContourHolonomy W y x =
            PeriodicLattice.meanContourHolonomy W y x := by
  have hω : 0 < Averaging.smoothingRadius L :=
    (Averaging.isSmoothingRadius_smoothingRadius hL.1 hL.2).1
  have hplaq : Finite (PeriodicLattice.Plaquette L 1 (PeriodicLattice.levelDepth k i)) := by
    have := (hA L hL 1 i k (by norm_num) hik.le).2.1
    exact this.2.2.2.2.2.2.2.2.2.2.2.2
  have hsize : PeriodicLattice.doubleBlockCurvature W d < Averaging.smoothingRadius L :=
    doubleBlockCurvature_lt hG d W hω fun b => ⟨hW.1 b (mem_univ b), hWb b⟩
  have hreal : PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup
      (PeriodicLattice.bondsInDoubleBlock d) W :=
    ⟨fun b _ => hW.1 b (mem_univ b), fun b _ => hW.2 b (mem_univ b)⟩
  have hsch := (hS L hL 1 k i one_pos hik .centred).2.1 d hd
  have hmean := hsch.2.2.2.2.1 W hreal hsize
  refine ⟨?_, fun y hy x hx => hmean.contour_eq y hy x hx⟩
  rw [← hsch.2.2.1.average_eq W hmean.mem_domain, hmean.average_eq]
  rfl
theorem smoothingStep_opposite {L k i : ℕ} {W : Tower.Edge L 1 k i → ComplexMatrix2}
    {d : Tower.Edge L 1 k (i + 1)} (hd : d.IsPositivelyOriented)
    (hr : ¬ d.opposite.IsPositivelyOriented) :
    Tower.smoothingStep L 1 k i W d.opposite = (Tower.smoothingStep L 1 k i W d)⁻¹ := by
  simp only [Tower.smoothingStep, PeriodicLattice.blockAverageStep, PeriodicLattice.blockAverage,
    if_pos hd, if_neg hr]
  rfl
theorem pushField_eq_of_extensions {L k i : ℕ} {f : AmbientSpace → AmbientSpace}
    {g : PeriodicLattice.FourTorus L 1 → PeriodicLattice.FourTorus L 1}
    {P P' : Set (FullSpace.Edge L k i)} {V V' : FullSpace.Edge L k i → ComplexMatrix2}
    {W W' : Tower.Edge L 1 k i → ComplexMatrix2}
    (hW : ∀ b ∈ P, W (projEdge L 1 k i b) = V b)
    (hWo : ∀ β, (∀ b ∈ P, projEdge L 1 k i b ≠ β) → W β = 1)
    (hW' : ∀ b ∈ P', W' (projEdge L 1 k i b) = V' b)
    (hWo' : ∀ β, (∀ b ∈ P', projEdge L 1 k i b ≠ β) → W' β = 1)
    (hm : ∀ b ∈ P, edgeImage f b ∈ P') (hm' : ∀ b ∈ P', edgePreimage f b ∈ P)
    (hV : ∀ b, V' b = V (edgePreimage f b))
    (hq : ∀ b : FullSpace.Edge L k i, projEdge L 1 k i (edgeImage f b) =
      Tower.edgeImage (k := k) (j := i) g (projEdge L 1 k i b))
    (hf : ∀ b : FullSpace.Edge L k i, edgeImage f (edgePreimage f b) = b)
    (hg : ∀ β : Tower.Edge L 1 k i,
      Tower.edgeImage (k := k) (j := i) g (Tower.edgePreimage (k := k) (j := i) g β) = β)
    (hg' : ∀ β : Tower.Edge L 1 k i,
      Tower.edgePreimage (k := k) (j := i) g (Tower.edgeImage (k := k) (j := i) g β) = β) :
    W' = Tower.pushField (k := k) (j := i) g W := by
  funext β
  by_cases h : ∃ b ∈ P', projEdge L 1 k i b = β
  · obtain ⟨b', hb', rfl⟩ := h
    have hb := hm' b' hb'
    have e : Tower.edgePreimage (k := k) (j := i) g (projEdge L 1 k i b') =
        projEdge L 1 k i (edgePreimage f b') := by
      conv_lhs => rw [← hf b', hq, hg']
    show W' _ = W (Tower.edgePreimage (k := k) (j := i) g _)
    rw [hW' b' hb', hV, e, hW _ hb]
  · rw [hWo' β fun b hb e => h ⟨b, hb, e⟩]
    show 1 = W (Tower.edgePreimage (k := k) (j := i) g β)
    rw [hWo]
    intro b hb e
    refine h ⟨edgeImage f b, hm b hb, ?_⟩
    rw [hq, e, hg]
theorem complexSmoothing_opposite {a a' : ℝ} (ha : a ≠ 0) {L : ℕ}
    {U : InfiniteLattice.Link a' → ComplexMatrix2}
    (hU : ∀ c : InfiniteLattice.Link a, c.IsPositivelyOriented →
      complexSmoothingPositive L U c ∈ PeriodicLattice.compactGaugeGroup)
    (c : InfiniteLattice.Link a) :
    complexSmoothing L U c.opposite = (complexSmoothing L U c)⁻¹ := by
  by_cases hc : c.IsPositivelyOriented
  · have hr := not_isPositivelyOriented_opposite ha hc
    simp only [complexSmoothing, if_pos hc, if_neg hr]
    rfl
  · have hr := isPositivelyOriented_opposite hc
    simp only [complexSmoothing, if_pos hr, if_neg hc]
    have h1 : (complexSmoothingPositive L U c.opposite).det = 1 :=
      (Matrix.mem_specialUnitaryGroup_iff.mp (hU _ hr)).2
    rw [Matrix.nonsing_inv_nonsing_inv _ (by rw [h1]; exact isUnit_one)]
theorem torus_not_isPositivelyOriented_opposite
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties) {L k i : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hik : i ≤ k) {d : Tower.Edge L 1 k i}
    (hd : d.IsPositivelyOriented) : ¬ d.opposite.IsPositivelyOriented := by
  have N := (hA L hL 1 i k le_rfl hik).2.2.2.2.2.1
  obtain ⟨μ, h⟩ := hd
  have hs : QuotientLattices.IsSignedAxisStep
      (QuotientLattices.torusAxisSteps L 1 k i)
      (d.source : PeriodicLattice.FourTorus L 1) (d.target : PeriodicLattice.FourTorus L 1) 1 μ := by
    have := congrArg Subtype.val h
    simpa [QuotientLattices.IsSignedAxisStep, QuotientLattices.torusAxisSteps] using this
  have X := ((N.2.2 _ d.source.2 _ d.target.2).2 1 μ hs).2
  rintro ⟨ν, h'⟩
  have hs' : QuotientLattices.IsSignedAxisStep
      (QuotientLattices.torusAxisSteps L 1 k i)
      (d.target : PeriodicLattice.FourTorus L 1) (d.source : PeriodicLattice.FourTorus L 1) 1 ν := by
    have := congrArg Subtype.val h'
    simpa [QuotientLattices.IsSignedAxisStep, QuotientLattices.torusAxisSteps,
      PeriodicLattice.Bond.opposite] using this
  rcases X with ⟨-, h₂⟩ | ⟨-, h₂⟩
  · exact h₂ ⟨ν, hs'⟩
  · exact h₂ ⟨μ, hs⟩
abbrev extendByOne (L k j : ℕ) (c : FullSpace.Edge L k (j + 1))
    (U : FullSpace.Edge L k j → ComplexMatrix2) : Tower.Edge L 1 k j → ComplexMatrix2 :=
  projField L 1 k j (doubleCubeLinks L (Tower.meshAt L k j) c) U
theorem equivariant_at_symmetry (hS : PeriodicLattice.AveragingSchemeProperties)
    (hF : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hQ : Tower.EdgeProjectionProperties)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hG : ComplexMatrix2.SpecialUnitaryAngleBounds)
    (hI : Tower.SmoothingEquivariantOnSides)
    (hZ : Tower.BlockStructure)
    (hC : Tower.GaugeAndSymmetryImages.statement)
    (hM : SmoothingNearIdentity)
    {L k j : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hjk : j < k)
    {f : AmbientSpace → AmbientSpace}
    (hf : IsDistancePreserving f) (hMf : MapsSublatticeOnto (Tower.meshAt L k (j + 1)) f) :
    EventuallyNearIdentity (smoothingDomain L k j) fun V =>
      pushField f V ∈ smoothingDomain L k j ∧
        (∀ (y : FullSpace.Vertex L k (j + 1)), ∀ x ∈ cubeVertices L (Tower.meshAt L k j) y,
          complexContourMean L (pushField f V) (vertexImage f y) (vertexImage f x) =
            complexContourMean L V y x) ∧
        smoothingMap L k j (pushField f V) = pushField f (smoothingMap L k j V) := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hω : 0 < Averaging.smoothingRadius L :=
    (Averaging.isSmoothingRadius_smoothingRadius hL.1 hL.2).1
  have hk : 1 ≤ k := by omega
  have hs : ∀ i, Tower.meshAt L k i ≠ 0 := fun i =>
    zpow_ne_zero _ (by exact_mod_cast hL0.ne')
  have hF' := hF L hL0 hL k
  obtain ⟨⟨w, -, v, -, hwv⟩, hi, hgx⟩ := hF'.2.2.2.2.1 (j + 1) (by omega) f hf hMf
  obtain ⟨hMj, hBj, -⟩ := hi j (by omega)
  obtain ⟨-, hB1, -⟩ := hi (j + 1) le_rfl
  obtain ⟨g, hgπ, hgI, hgM⟩ := hgx 1 one_pos
  obtain ⟨-, hi'⟩ := hF'.2.2.2.1 1 one_pos (j + 1) (by omega) g hgI hgM
  obtain ⟨hMgj, hBgj, -⟩ := hi' j (by omega)
  obtain ⟨hMg1, hBg1, -⟩ := hi' (j + 1) le_rfl
  have hfi : Function.Injective f := by
    intro x y h
    rw [hwv x, hwv y] at h
    exact w.injective (add_right_cancel h)
  have hsiteFin : Finite (Tower.Vertex L 1 k j) :=
    (hA L hL 1 j k (by norm_num) hjk.le).2.1.2.2.2.2.2.2.2.2.2.2.1
  have hbondFin : Finite (Tower.Edge L 1 k j) :=
    (hA L hL 1 j k (by norm_num) hjk.le).2.1.2.2.2.2.2.2.2.2.2.2.2.1
  have hsiteFin1 : Finite (Tower.Vertex L 1 k (j + 1)) :=
    (hA L hL 1 (j + 1) k (by norm_num) hjk).2.1.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨ε₀, hε₀, hnear⟩ :=
    exists_ball_of_eventuallyNearIdentity (hI L hL 1 k j one_pos hjk g hgI hgM)
  have hr : 0 < min ε₀ (Averaging.smoothingRadius L / 4) := lt_min hε₀ (by positivity)
  refine ⟨min ε₀ (Averaging.smoothingRadius L / 4), hr, fun V hVD hd => ?_⟩
  have hVb : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) <
      min ε₀ (Averaging.smoothingRadius L / 4) := fun b => by
    have h : ENNReal.ofReal (ComplexMatrix2.operatorNorm (V b - 1)) <
        ENNReal.ofReal (min ε₀ (Averaging.smoothingRadius L / 4)) :=
      lt_of_le_of_lt
        (le_iSup (fun b => ENNReal.ofReal (ComplexMatrix2.operatorNorm (V b - 1))) b) hd
    exact (ENNReal.ofReal_lt_ofReal_iff hr).1 h
  have hcV : IsFieldIn PeriodicLattice.complexGaugeGroup V :=
    ⟨fun b => (Matrix.mem_specialUnitaryGroup_iff.mp (hVD.1.1 b)).2, hVD.1.2⟩
  have hsV : pushField f V ∈ fieldSpace L k j :=
    ((hC L k j hL hjk.le).2 V (fun _ => 1) f hcV
      (fun _ => (Matrix.mem_specialUnitaryGroup_iff.mp
        (one_mem ComplexMatrix2.specialUnitary)).2) hf hMj).2.2.2 hVD.1
  have hsVb : ∀ b, ComplexMatrix2.operatorNorm (pushField f V b - 1) <
      min ε₀ (Averaging.smoothingRadius L / 4) :=
    fun b => hVb _
  have hsd : supDistOne (pushField f V) < ENNReal.ofReal (Averaging.smoothingRadius L / 4) := by
    refine lt_of_le_of_lt (iSup_le fun b => ?_)
      (lt_of_lt_of_le hd (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
    exact le_iSup (fun b => ENNReal.ofReal (ComplexMatrix2.operatorNorm (V b - 1)))
      (edgePreimage f b)
  have hsD : pushField f V ∈ smoothingDomain L k j := by
    refine ⟨hsV, fun c hc => ?_⟩
    have h := hM L k (j + 1) hL hk (by omega) (by omega) (pushField f V) hsV hsd c hc
    refine ⟨h.1, ?_⟩
    have e : complexSmoothing L (pushField f V) c =
        complexSmoothingPositive L (pushField f V) c := by
      simp only [complexSmoothing, if_pos hc]
    exact e ▸ h.2.1
  have hZ' : ∀ y : FullSpace.Vertex L k (j + 1), f '' cube L (Tower.meshAt L k j) y =
      cube L (Tower.meshAt L k j) (vertexImage f y) :=
    (hZ L k (j + 1) hL hk (by omega) (by omega)).2.2.2.2 f hf hMf
  have himg : ∀ c : FullSpace.Edge L k (j + 1), f '' doubleCube L (Tower.meshAt L k j) c =
      doubleCube L (Tower.meshAt L k j) (edgeImage f c) := by
    intro c
    obtain ⟨t, h⟩ := edgeImage_endpoints hMf hB1 c
    unfold doubleCube
    rw [image_union, hZ', hZ', t, h]
  have hPrev : ∀ c : FullSpace.Edge L k (j + 1),
      doubleCubeLinks L (Tower.meshAt L k j) c.opposite =
        doubleCubeLinks L (Tower.meshAt L k j) c := by
    intro c
    have hD : doubleCube L (Tower.meshAt L k j) c.opposite =
        doubleCube L (Tower.meshAt L k j) c := union_comm _ _
    unfold doubleCubeLinks
    rw [hD]
  have hmem : ∀ (c : FullSpace.Edge L k (j + 1)) (b : FullSpace.Edge L k j),
      b ∈ doubleCubeLinks L (Tower.meshAt L k j) c →
        edgeImage f b ∈ doubleCubeLinks L (Tower.meshAt L k j) (edgeImage f c) := by
    intro c b hb
    obtain ⟨t, h⟩ := edgeImage_endpoints hMj hBj b
    refine ⟨?_, ?_⟩
    · rw [t, coe_vertexImage hMj, ← himg]
      exact ⟨_, hb.1, rfl⟩
    · rw [h, coe_vertexImage hMj, ← himg]
      exact ⟨_, hb.2, rfl⟩
  have hmem' : ∀ (c : FullSpace.Edge L k (j + 1)) (b : FullSpace.Edge L k j),
      b ∈ doubleCubeLinks L (Tower.meshAt L k j) (edgeImage f c) →
        edgePreimage f b ∈ doubleCubeLinks L (Tower.meshAt L k j) c := by
    intro c b hb
    obtain ⟨t, h⟩ := edgePreimage_endpoints hMj hBj hfi b
    have key : ∀ x : FullSpace.Vertex L k j, (x : AmbientSpace) ∈
        doubleCube L (Tower.meshAt L k j) (edgeImage f c) →
        ((vertexPreimage f x : FullSpace.Vertex L k j) : AmbientSpace) ∈
          doubleCube L (Tower.meshAt L k j) c := by
      intro x hx
      rw [← himg] at hx
      obtain ⟨z, hz, e⟩ := hx
      have e' : ((vertexPreimage f x : FullSpace.Vertex L k j) : AmbientSpace) = z :=
        hfi ((apply_vertexPreimage hMj x).trans e.symm)
      rw [e']
      exact hz
    exact ⟨by rw [t]; exact key _ hb.1, by rw [h]; exact key _ hb.2⟩
  have hqS : ∀ i (_ : MapsSublatticeOnto (Tower.meshAt L k i) f)
      (_ : Tower.MapsSublatticeOnto k i g) (x : FullSpace.Vertex L k i),
      projVertex L 1 k i (vertexImage f x) =
        Tower.vertexImage (k := k) (j := i) g (projVertex L 1 k i x) := by
    intro i hMi hMgi x
    apply Subtype.ext
    rw [coe_torusVertexImage hMgi]
    show TorusMetric.torusProj (PeriodicLattice.torusSide L 1)
        ((vertexImage f x : FullSpace.Vertex L k i) : AmbientSpace) =
      g (TorusMetric.torusProj (PeriodicLattice.torusSide L 1) (x : AmbientSpace))
    rw [coe_vertexImage hMi, hgπ]
  have hqB : ∀ i (_ : i ≤ k) (_ : MapsSublatticeOnto (Tower.meshAt L k i) f)
      (_ : MapsLinksOnto (Tower.meshAt L k i) f)
      (_ : Tower.MapsSublatticeOnto k i g) (_ : Tower.MapsEdgesOnto k i g)
      (b : FullSpace.Edge L k i),
      projEdge L 1 k i (edgeImage f b) =
        Tower.edgeImage (k := k) (j := i) g (projEdge L 1 k i b) := by
    intro i hik hMi hBi hMgi hBgi b
    have q := (hQ L 1 k i hL one_pos hik).1
    refine PeriodicLattice.Bond.ext ?_ ?_
    · rw [(q _).1, (edgeImage_endpoints hMi hBi b).1, hqS i hMi hMgi,
        (torusEdgeImage_endpoints hMgi hBgi _).1, (q b).1]
    · rw [(q _).2.1, (edgeImage_endpoints hMi hBi b).2, hqS i hMi hMgi,
        (torusEdgeImage_endpoints hMgi hBgi _).2, (q b).2.1]
  have Qof : ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
      ProjPreservesStructures L 1 k j c :=
    fun c hc => (hF'.2.2.2.2.2.2 hk 1 one_pos).2 j hjk c hc
  have hlift := fun (c : FullSpace.Edge L k (j + 1)) (hc : c.IsPositivelyOriented) =>
    projField_properties hQ hL hjk.le (Qof c hc) hVD.1 hr hVb
  have hlift' := fun (c : FullSpace.Edge L k (j + 1)) (hc : c.IsPositivelyOriented) =>
    projField_properties hQ hL hjk.le (Qof c hc) hsV hr hsVb
  have hq1 := (hQ L 1 k (j + 1) hL one_pos (by omega)).1
  have dpos : ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
      (projEdge L 1 k (j + 1) c).IsPositivelyOriented := fun c hc => (hq1 c).2.2.1 hc
  have htr : ∀ c c' : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
      c'.IsPositivelyOriented →
      (c' = edgeImage f c ∨ c' = (edgeImage f c).opposite) →
      extendByOne L k j c' (pushField f V) =
        Tower.pushField (k := k) (j := j) g (extendByOne L k j c V) := by
    intro c c' hc hc' hrel
    have hP : doubleCubeLinks L (Tower.meshAt L k j) c' =
        doubleCubeLinks L (Tower.meshAt L k j) (edgeImage f c) := by
      rcases hrel with rfl | rfl
      · rfl
      · exact hPrev _
    obtain ⟨-, -, w₁, w₂⟩ := hlift c hc
    obtain ⟨-, -, w₁', w₂'⟩ := hlift' c' hc'
    exact pushField_eq_of_extensions w₁ w₂ w₁' w₂' (fun b hb => hP ▸ hmem c b hb)
      (fun b hb => hmem' c b (hP ▸ hb)) (fun _ => rfl)
      (hqB j hjk.le hMj hBj hMgj hBgj) (edgeImage_edgePreimage hMj hBj hfi)
      (torusEdgeImage_torusEdgePreimage hMgj hBgj) (torusEdgePreimage_torusEdgeImage hMgj hBgj)
  have hsmall : min ε₀ (Averaging.smoothingRadius L / 4) ≤ Averaging.smoothingRadius L / 4 :=
    min_le_right _ _
  have hmean := fun (c : FullSpace.Edge L k (j + 1)) (hc : c.IsPositivelyOriented) =>
    complexBlockAverage_eq_near_identity hS hA hG hL hjk (hlift c hc).1
      (fun β => lt_of_lt_of_le ((hlift c hc).2.1 β) hsmall) (dpos c hc)
  have hmean' := fun (c : FullSpace.Edge L k (j + 1)) (hc : c.IsPositivelyOriented) =>
    complexBlockAverage_eq_near_identity hS hA hG hL hjk (hlift' c hc).1
      (fun β => lt_of_lt_of_le ((hlift' c hc).2.1 β) hsmall) (dpos c hc)
  have hfin := fun (c : FullSpace.Edge L k (j + 1)) (hc : c.IsPositivelyOriented) =>
    hnear _ (hlift c hc).1 (fun β => lt_of_lt_of_le ((hlift c hc).2.1 β) (min_le_left _ _))
  have hchoice : ∀ c : FullSpace.Edge L k (j + 1), ∃ c' : FullSpace.Edge L k (j + 1),
      c'.IsPositivelyOriented ∧ (c' = edgeImage f c ∨ c' = (edgeImage f c).opposite) := by
    intro c
    by_cases h : (edgeImage f c).IsPositivelyOriented
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, isPositivelyOriented_opposite h, Or.inr rfl⟩
  have hblk : ∀ (c : FullSpace.Edge L k (j + 1)), c.IsPositivelyOriented →
      ∀ y : FullSpace.Vertex L k (j + 1),
      (y = c.initial ∨ y = c.terminal) → ∀ x ∈ cubeVertices L (Tower.meshAt L k j) y,
      projVertex L 1 k (j + 1) y ∈ ({(projEdge L 1 k (j + 1) c).source,
          (projEdge L 1 k (j + 1) c).target} : Set (Tower.Vertex L 1 k (j + 1))) ∧
        projVertex L 1 k j x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
          (projVertex L 1 k (j + 1) y) := by
    intro c hc y hy x hx
    have Q := Qof c hc
    rcases hy with rfl | rfl
    · refine ⟨Or.inl (hq1 c).1.symm, ?_⟩
      rw [← (hq1 c).1]
      show ((projVertex L 1 k j x : Tower.Vertex L 1 k j) : PeriodicLattice.FourTorus L 1) ∈
        PeriodicLattice.unitBlock (projEdge L 1 k (j + 1) c).source
      rw [← Q.cube_initial]
      exact ⟨_, hx, rfl⟩
    · refine ⟨Or.inr (hq1 c).2.1.symm, ?_⟩
      rw [← (hq1 c).2.1]
      show ((projVertex L 1 k j x : Tower.Vertex L 1 k j) : PeriodicLattice.FourTorus L 1) ∈
        PeriodicLattice.unitBlock (projEdge L 1 k (j + 1) c).target
      rw [← Q.cube_terminal]
      exact ⟨_, hx, rfl⟩
  refine ⟨hsD, ?_, ?_⟩
  · intro y x hx
    have hc : (InfiniteLattice.Link.forwardFrom y 0 :
        FullSpace.Edge L k (j + 1)).IsPositivelyOriented :=
      ⟨0, by simp [InfiniteLattice.Link.forwardFrom]⟩
    obtain ⟨c', hc', hrel⟩ := hchoice (InfiniteLattice.Link.forwardFrom y 0)
    have hty : (edgeImage f (InfiniteLattice.Link.forwardFrom y 0 :
        FullSpace.Edge L k (j + 1))).initial = vertexImage f y :=
      (edgeImage_endpoints hMf hB1 _).1
    have hy' : vertexImage f y = c'.initial ∨ vertexImage f y = c'.terminal := by
      rcases hrel with rfl | rfl
      · exact Or.inl hty.symm
      · exact Or.inr hty.symm
    have hx' : vertexImage f x ∈ cubeVertices L (Tower.meshAt L k j) (vertexImage f y) := by
      show ((vertexImage f x : FullSpace.Vertex L k j) : AmbientSpace) ∈
        cube L (Tower.meshAt L k j) (vertexImage f y)
      rw [coe_vertexImage hMj, ← hZ']
      exact ⟨_, hx, rfl⟩
    have e₁ := (Qof _ hc).complexContourMean_eq V (hVD.2 _ hc).1 y (Or.inl rfl) x hx
    have e₂ := (Qof c' hc').complexContourMean_eq _ (hsD.2 c' hc').1 _ hy' _ hx'
    obtain ⟨hyd, hxd⟩ := hblk _ hc y (Or.inl rfl) x hx
    obtain ⟨hyd', hxd'⟩ := hblk c' hc' _ hy' _ hx'
    rw [e₁, e₂, (hmean _ hc).2 _ hyd _ hxd, (hmean' c' hc').2 _ hyd' _ hxd']
    have e₃ := htr _ c' hc hc' hrel
    simp only [extendByOne] at e₃
    rw [e₃, hqS (j + 1) hMf hMg1, hqS j hMj hMgj]
    exact (hfin _ hc).1 _ _ hxd
  · have hpos : ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
        complexSmoothing L (pushField f V) (edgeImage f c) =
          complexSmoothing L V c := by
      intro c hc
      obtain ⟨c', hc', hrel⟩ := hchoice c
      have hVc := (Qof c hc).complexSmoothing_eq V (hVD.2 c hc).1
      have hsc := (Qof c' hc').complexSmoothing_eq _ (hsD.2 c' hc').1
      have m₁ := (hmean c hc).1
      have m₂ := (hmean' c' hc').1
      have val : Tower.smoothingStep L 1 k j (extendByOne L k j c' (pushField f V))
            (projEdge L 1 k (j + 1) c') =
          Tower.smoothingStep L 1 k j (extendByOne L k j c V)
            (Tower.edgePreimage (k := k) (j := j + 1) g
              (projEdge L 1 k (j + 1) c')) := by
        rw [htr c c' hc hc' hrel]
        exact congrFun (hfin c hc).2 _
      rcases hrel with rfl | e
      · rw [hsc, m₂, val, hqB (j + 1) (by omega) hMf hB1 hMg1 hBg1,
          torusEdgePreimage_torusEdgeImage hMg1 hBg1, ← m₁, ← hVc]
      · have es : edgeImage f c = c'.opposite := by rw [e]; rfl
        have hinv : Tower.edgePreimage (k := k) (j := j + 1) g
            (projEdge L 1 k (j + 1) c') = (projEdge L 1 k (j + 1) c).opposite := by
          rw [e, ← (hq1 _).2.2.2, hqB (j + 1) (by omega) hMf hB1 hMg1 hBg1,
            ← torusEdgeImage_opposite hMg1 hBg1, torusEdgePreimage_torusEdgeImage hMg1 hBg1]
        have hnp := torus_not_isPositivelyOriented_opposite hA hL (by omega : j + 1 ≤ k)
          (dpos c hc)
        rw [es, complexSmoothing_opposite (hs (j + 1)) (fun c hc => (hsD.2 c hc).2) c', hsc,
          m₂, val, hinv, smoothingStep_opposite (dpos c hc) hnp, ← m₁, ← hVc]
        have h1 : (complexSmoothing L V c).det = 1 := by
          have e' : complexSmoothing L V c = complexSmoothingPositive L V c := by
            simp only [complexSmoothing, if_pos hc]
          rw [e']
          exact (Matrix.mem_specialUnitaryGroup_iff.mp (hVD.2 c hc).2).2
        rw [Matrix.nonsing_inv_nonsing_inv _ (by rw [h1]; exact isUnit_one)]
    funext b
    show complexSmoothing L (pushField f V) b = complexSmoothing L V (edgePreimage f b)
    by_cases hc : (edgePreimage f b).IsPositivelyOriented
    · conv_lhs => rw [← edgeImage_edgePreimage hMf hB1 hfi b]
      exact hpos _ hc
    · have hr' := isPositivelyOriented_opposite hc
      have e : b = (edgeImage f (edgePreimage f b).opposite).opposite := by
        rw [edgeImage_opposite hMf hB1, edgeImage_edgePreimage hMf hB1 hfi]
        rfl
      conv_lhs => rw [e]
      rw [complexSmoothing_opposite (hs (j + 1)) (fun c hc => (hsD.2 c hc).2), hpos _ hr']
      exact (complexSmoothing_opposite (hs (j + 1)) (fun c hc => (hVD.2 c hc).2)
        (edgePreimage f b).opposite).symm
theorem smoothingEquivariantAllSteps_holds
    (hS : PeriodicLattice.AveragingSchemeProperties)
    (hF : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hQ : Tower.EdgeProjectionProperties)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hG : ComplexMatrix2.SpecialUnitaryAngleBounds)
    (hI : Tower.SmoothingEquivariantOnSides)
    (hZ : Tower.BlockStructure)
    (hC : Tower.GaugeAndSymmetryImages.statement)
    (hM : SmoothingNearIdentity) :
    SmoothingEquivariantAllSteps := by
  intro L hL k j hjk f hf hMf
  exact equivariant_at_symmetry hS hF hQ hA hG hI hZ hC hM hL hjk hf hMf
end YangMills.Construction.Tower.FullSpace.EquivariantSmoothing
end

import YangMills.Construction.Lattice.CovarianceOfComplexHolonomiesAndAverages
import YangMills.Construction.Towers.AveragingCommutesWithIsometriesAtTheSideInfinityProof
import YangMills.Construction.Towers.AveragingCommutesWithIsometriesOnTheSidesProof
import YangMills.Construction.Towers.ComplexAverageLiesInTheComplexGroup
import YangMills.Construction.Towers.ComplexAveragesCommuteWithIsometriesOnThePolydiscs
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction
noncomputable section
namespace Tower.PeriodicDoubleSide
variable {L n k i : ℕ}
theorem exists_mem_latticeIsometries
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    {w : InfiniteLattice.AmbientSpace ≃ₗ[ℝ] InfiniteLattice.AmbientSpace}
    (hw : w ∈ InfiniteLattice.hyperoctahedralLinearGroup) {v : InfiniteLattice.AmbientSpace}
    (hv : v ∈ InfiniteLattice.latticeSubgroup (meshAt L k i))
    (hwv : ∀ x : InfiniteLattice.AmbientSpace,
      f (TorusMetric.torusProj (PeriodicLattice.torusSide L n) x) =
        TorusMetric.torusProj (PeriodicLattice.torusSide L n) (w x + v)) :
    ∃ σ : PeriodicLattice.FourTorus L n ≃ PeriodicLattice.FourTorus L n, (∀ x, σ x = f x) ∧
      σ ∈ PeriodicLattice.latticeIsometries L n (PeriodicLattice.levelDepth k i) := by apply _root_.YangMills.Construction.Tower.EquivariantOnSides.exists_mem_latticeIsometries <;> assumption
theorem vertexImage_eq_sitePreimage
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    {σ : PeriodicLattice.FourTorus L n ≃ PeriodicLattice.FourTorus L n} (hσf : ∀ x, σ x = f x)
    (x : Vertex L n k i) : vertexImage f x = PeriodicLattice.sitePreimage σ.symm x := by apply _root_.YangMills.Construction.Tower.EquivariantOnSides.vertexImage_eq_sitePreimage <;> assumption
theorem pushField_eq_transportGaugeField
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    {σ : PeriodicLattice.FourTorus L n ≃ PeriodicLattice.FourTorus L n} (hσf : ∀ x, σ x = f x)
    (hedges : MapsEdgesOnto k i f) (U : Edge L n k i → Matrices.ComplexMatrix2) :
    pushField f U = PeriodicLattice.transportGaugeField σ U := by apply _root_.YangMills.Construction.Tower.EquivariantOnSides.pushField_eq_transportGaugeField <;> assumption
variable {g : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
theorem coe_vertexImage (hM : MapsSublatticeOnto k i g) (x : Vertex L n k i) :
    ((vertexImage (k := k) (j := i) g x : Vertex L n k i) : PeriodicLattice.FourTorus L n) =
      g x := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.coe_torus_vertexImage <;> assumption
theorem apply_vertexPreimage (hM : MapsSublatticeOnto k i g) (x : Vertex L n k i) :
    g (vertexPreimage (k := k) (j := i) g x : Vertex L n k i) = x := by apply _root_.YangMills.Construction.Tower.ScalingInvariance.vertexPreimage_spec <;> assumption
theorem edgeImage_spec (hM : MapsSublatticeOnto k i g) (hB : MapsEdgesOnto k i g)
    (b : Edge L n k i) :
    (edgeImage (k := k) (j := i) g b).source = vertexImage (k := k) (j := i) g b.source ∧
      (edgeImage (k := k) (j := i) g b).target = vertexImage (k := k) (j := i) g b.target := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.torusEdgeImage_endpoints <;> assumption
theorem edgePreimage_spec (hM : MapsSublatticeOnto k i g) (hB : MapsEdgesOnto k i g)
    (hi : Function.Injective g) (b : Edge L n k i) :
    (edgePreimage (k := k) (j := i) g b).source = vertexPreimage (k := k) (j := i) g b.source ∧
      (edgePreimage (k := k) (j := i) g b).target =
        vertexPreimage (k := k) (j := i) g b.target := by
  obtain ⟨b₀, h₁, h₂⟩ := hB.2 b
  exact Classical.epsilon_spec
    (p := fun b' : Edge L n k i =>
      b'.source = vertexPreimage (k := k) (j := i) g b.source ∧
        b'.target = vertexPreimage (k := k) (j := i) g b.target)
    ⟨b₀, Subtype.ext (hi (h₁.symm.trans (apply_vertexPreimage hM _).symm)),
      Subtype.ext (hi (h₂.symm.trans (apply_vertexPreimage hM _).symm))⟩
theorem edgeImage_edgePreimage (hM : MapsSublatticeOnto k i g) (hB : MapsEdgesOnto k i g)
    (hi : Function.Injective g) (b : Edge L n k i) :
    edgeImage (k := k) (j := i) g (edgePreimage (k := k) (j := i) g b) = b := by
  obtain ⟨t, h⟩ := edgeImage_spec hM hB (edgePreimage (k := k) (j := i) g b)
  obtain ⟨t', h'⟩ := edgePreimage_spec hM hB hi b
  refine PeriodicLattice.Bond.ext ?_ ?_
  · rw [t, t']
    exact Subtype.ext ((coe_vertexImage hM _).trans (apply_vertexPreimage hM _))
  · rw [h, h']
    exact Subtype.ext ((coe_vertexImage hM _).trans (apply_vertexPreimage hM _))
theorem edgePreimage_edgeImage (hM : MapsSublatticeOnto k i g) (hB : MapsEdgesOnto k i g)
    (hi : Function.Injective g) (b : Edge L n k i) :
    edgePreimage (k := k) (j := i) g (edgeImage (k := k) (j := i) g b) = b := by
  obtain ⟨t, h⟩ := edgePreimage_spec hM hB hi (edgeImage (k := k) (j := i) g b)
  obtain ⟨t', h'⟩ := edgeImage_spec hM hB b
  refine PeriodicLattice.Bond.ext ?_ ?_
  · rw [t, t']
    exact Subtype.ext (hi ((apply_vertexPreimage hM _).trans (coe_vertexImage hM _)))
  · rw [h, h']
    exact Subtype.ext (hi ((apply_vertexPreimage hM _).trans (coe_vertexImage hM _)))
theorem bondImage_eq_edgeImage
    {σ : PeriodicLattice.FourTorus L n ≃ PeriodicLattice.FourTorus L n} (hσf : ∀ x, σ x = g x)
    (hM : MapsSublatticeOnto k i g) (hB : MapsEdgesOnto k i g) (b : Edge L n k i) :
    PeriodicLattice.bondImage σ b = edgeImage (k := k) (j := i) g b := by
  obtain ⟨t, h⟩ := edgeImage_spec hM hB b
  have hex : ∃ b' : Edge L n k i,
      (b'.source : PeriodicLattice.FourTorus L n) = σ.symm.symm b.source ∧
      (b'.target : PeriodicLattice.FourTorus L n) = σ.symm.symm b.target :=
    ⟨edgeImage (k := k) (j := i) g b, by rw [t, coe_vertexImage hM, Equiv.symm_symm, hσf],
      by rw [h, coe_vertexImage hM, Equiv.symm_symm, hσf]⟩
  simp only [PeriodicLattice.bondImage, PeriodicLattice.bondPreimage, dif_pos hex]
  have hc := hex.choose_spec
  refine PeriodicLattice.Bond.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [hc.1, t, coe_vertexImage hM, Equiv.symm_symm, hσf]
  · rw [hc.2, h, coe_vertexImage hM, Equiv.symm_symm, hσf]
end Tower.PeriodicDoubleSide
namespace Tower.FullSpace.ComplexSmoothingEquivarianceProof
open InfiniteLattice (AmbientSpace)
open Tower.PeriodicDoubleSide (exists_mem_latticeIsometries)
open Tower.PeriodicDoubleSide renaming coe_vertexImage → torus_coe_vertexImage,
  edgeImage_spec → torus_edgeImage_spec, edgeImage_edgePreimage → torus_edgeImage_edgePreimage,
  edgePreimage_edgeImage → torus_edgePreimage_edgeImage,
  bondImage_eq_edgeImage → torus_bondImage_eq_edgeImage,
  pushField_eq_transportGaugeField → torus_pushField_eq_transportGaugeField,
  vertexImage_eq_sitePreimage → torus_vertexImage_eq_sitePreimage
section Ambient
variable {a : ℝ} {f : AmbientSpace → AmbientSpace}
theorem coe_vertexImage (hM : MapsSublatticeOnto a f) (x : InfiniteLattice.LatticePoint a) :
    ((vertexImage f x : InfiniteLattice.LatticePoint a) : AmbientSpace) = f x := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.coe_space_vertexImage <;> assumption
theorem apply_vertexPreimage (hM : MapsSublatticeOnto a f) (x : InfiniteLattice.LatticePoint a) :
    f (vertexPreimage f x : InfiniteLattice.LatticePoint a) = x := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingInvariance.vertexPreimage_spec <;> assumption
theorem edgeImage_spec (hM : MapsSublatticeOnto a f) (hB : MapsLinksOnto a f)
    (b : InfiniteLattice.Link a) :
    (edgeImage f b).initial = vertexImage f b.initial ∧
      (edgeImage f b).terminal = vertexImage f b.terminal := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.edgeImage_endpoints <;> assumption
theorem edgePreimage_spec (hM : MapsSublatticeOnto a f) (hB : MapsLinksOnto a f)
    (hi : Function.Injective f) (b : InfiniteLattice.Link a) :
    (edgePreimage f b).initial = vertexPreimage f b.initial ∧
      (edgePreimage f b).terminal = vertexPreimage f b.terminal := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.edgePreimage_endpoints <;> assumption
theorem edgeImage_edgePreimage (hM : MapsSublatticeOnto a f) (hB : MapsLinksOnto a f)
    (hi : Function.Injective f) (b : InfiniteLattice.Link a) :
    edgeImage f (edgePreimage f b) = b := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.edgeImage_edgePreimage <;> assumption
theorem edgePreimage_edgeImage (hM : MapsSublatticeOnto a f) (hB : MapsLinksOnto a f)
    (hi : Function.Injective f) (b : InfiniteLattice.Link a) :
    edgePreimage f (edgeImage f b) = b := by
  obtain ⟨t, h⟩ := edgePreimage_spec hM hB hi (edgeImage f b)
  obtain ⟨t', h'⟩ := edgeImage_spec hM hB b
  refine InfiniteLattice.Link.ext ?_ ?_
  · rw [t, t']
    exact Subtype.ext (hi ((apply_vertexPreimage hM _).trans (coe_vertexImage hM _)))
  · rw [h, h']
    exact Subtype.ext (hi ((apply_vertexPreimage hM _).trans (coe_vertexImage hM _)))
theorem edgeImage_opposite (hM : MapsSublatticeOnto a f) (hB : MapsLinksOnto a f)
    (b : InfiniteLattice.Link a) : edgeImage f b.opposite = (edgeImage f b).opposite := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.edgeImage_opposite <;> assumption
theorem not_isPositivelyOriented_opposite (ha : a ≠ 0) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.PolydiscSmoothing.not_opposite_isPositivelyOriented <;> assumption
theorem isPositivelyOriented_opposite {b : InfiniteLattice.Link a}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
end Ambient
theorem pushField_eq_of_agree {L k i : ℕ} {f : AmbientSpace → AmbientSpace}
    {g : PeriodicLattice.FourTorus L 1 → PeriodicLattice.FourTorus L 1}
    {P P' : Set (Edge L k i)} {V V' : Edge L k i → Matrices.ComplexMatrix2}
    {W W' : Tower.Edge L 1 k i → Matrices.ComplexMatrix2}
    (hW : ∀ b ∈ P, W (projEdge L 1 k i b) = V b)
    (hWo : ∀ β, (∀ b ∈ P, projEdge L 1 k i b ≠ β) → W β = 1)
    (hW' : ∀ b ∈ P', W' (projEdge L 1 k i b) = V' b)
    (hWo' : ∀ β, (∀ b ∈ P', projEdge L 1 k i b ≠ β) → W' β = 1)
    (hm : ∀ b ∈ P, edgeImage f b ∈ P') (hm' : ∀ b ∈ P', edgePreimage f b ∈ P)
    (hV : ∀ b, V' b = V (edgePreimage f b))
    (hq : ∀ b : Edge L k i, projEdge L 1 k i (edgeImage f b) =
      Tower.edgeImage (k := k) (j := i) g (projEdge L 1 k i b))
    (hf : ∀ b : Edge L k i, edgeImage f (edgePreimage f b) = b)
    (hg : ∀ β : Tower.Edge L 1 k i,
      Tower.edgeImage (k := k) (j := i) g (Tower.edgePreimage (k := k) (j := i) g β) = β)
    (hg' : ∀ β : Tower.Edge L 1 k i,
      Tower.edgePreimage (k := k) (j := i) g (Tower.edgeImage (k := k) (j := i) g β) = β) :
    W' = Tower.pushField (k := k) (j := i) g W := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.pushField_eq_of_extensions <;> assumption
abbrev extendByOne (L k j : ℕ) (c : Edge L k (j + 1)) (U : Edge L k j → Matrices.ComplexMatrix2) :
    Tower.Edge L 1 k j → Matrices.ComplexMatrix2 :=
  projField L 1 k j (doubleCubeLinks L (meshAt L k j) c) U
theorem extendByOne_spec {L k i : ℕ} {c : Edge L k (i + 1)}
    (Q : ProjPreservesStructures L 1 k i c) {V : Edge L k i → Matrices.ComplexMatrix2}
    (hV : IsFieldOn PeriodicLattice.complexGaugeGroup
      (doubleCubeLinks L (meshAt L k i) c) V) :
    (∀ b ∈ doubleCubeLinks L (meshAt L k i) c,
      extendByOne L k i c V (projEdge L 1 k i b) = V b) ∧
    ∀ β, (∀ b ∈ doubleCubeLinks L (meshAt L k i) c, projEdge L 1 k i b ≠ β) →
      extendByOne L k i c V β = 1 := by
  refine ⟨(Q.projField_spec V hV).1, fun β hβ => ?_⟩
  unfold extendByOne projField
  rw [dif_neg]
  rintro ⟨b, hb, e⟩
  exact hβ b hb e
theorem complexSmoothing_opposite_of_positive {L k j : ℕ} {c : Edge L k (j + 1)}
    (ha : meshAt L k (j + 1) ≠ 0) (hc : c.IsPositivelyOriented)
    (U : Edge L k j → Matrices.ComplexMatrix2) :
    complexSmoothing L U c.opposite = (complexSmoothing L U c)⁻¹ := by
  have hn := not_isPositivelyOriented_opposite ha hc
  simp only [complexSmoothing, if_neg hn, if_pos hc]
  rfl
theorem holds_at (hF : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hQ : Tower.EdgeProjectionProperties)
    (hZ : Tower.BlockStructure)
    (hT : PeriodicLattice.ComplexAverageEquivariance)
    (hH : PeriodicLattice.ComplexHolonomiesAndAveragesCovariance.Statement)
    (hR : Tower.SmoothingNearIdentity)
    (hD : Tower.ComplexMeanLiesInComplexGaugeGroup)
    {L k j : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hjk : j < k)
    {f : AmbientSpace → AmbientSpace}
    (hf : IsDistancePreserving f) (hMf : MapsSublatticeOnto (meshAt L k (j + 1)) f)
    (c : Edge L k (j + 1)) (hc : c.IsPositivelyOriented) (V : Edge L k j → Matrices.ComplexMatrix2)
    (hV : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c) :
    (∀ y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))),
      ∀ x ∈ cubeVertices L (meshAt L k j) y,
        complexContourMean L (pushField f V) (vertexImage f y) (vertexImage f x) =
          complexContourMean L V y x) ∧
      complexSmoothing L (pushField f V) (edgeImage f c) = complexSmoothing L V c := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hk : 1 ≤ k := by omega
  have hs : ∀ i, meshAt L k i ≠ 0 := fun i =>
    zpow_ne_zero _ (by exact_mod_cast hL0.ne')
  have hF' := hF L hL0 hL k
  obtain ⟨⟨w, -, v, -, hwv⟩, hi, hgx⟩ := hF'.2.2.2.2.1 (j + 1) (by omega) f hf hMf
  obtain ⟨hMj, hBj, -⟩ := hi j (by omega)
  obtain ⟨-, hB1, -⟩ := hi (j + 1) le_rfl
  obtain ⟨g, hgπ, hgI, hgM⟩ := hgx 1 one_pos
  obtain ⟨⟨w', hw', v', hv', hwv'⟩, hi'⟩ := hF'.2.2.2.1 1 one_pos (j + 1) (by omega) g hgI hgM
  obtain ⟨hMgj, hBgj, -⟩ := hi' j (by omega)
  obtain ⟨hMg1, hBg1, -⟩ := hi' (j + 1) le_rfl
  obtain ⟨σ, hσg, hσ⟩ := exists_mem_latticeIsometries (k := k) (i := j + 1) hw' hv' hwv'
  have hgi : Function.Injective g := by
    have : g = σ := funext fun x => (hσg x).symm
    rw [this]
    exact σ.injective
  have hfi : Function.Injective f := by
    intro x y h
    rw [hwv x, hwv y] at h
    exact w.injective (add_right_cancel h)
  have hserve := (hR.1 L hL).2.2
  have hZ' : ∀ y : Vertex L k (j + 1), f '' cube L (meshAt L k j) y =
      cube L (meshAt L k j) (vertexImage f y) :=
    (hZ L k (j + 1) hL hk (by omega) (by omega)).2.2.2.2 f hf hMf
  have himg : ∀ c : Edge L k (j + 1), f '' doubleCube L (meshAt L k j) c =
      doubleCube L (meshAt L k j) (edgeImage f c) := by
    intro c
    obtain ⟨t, h⟩ := edgeImage_spec hMf hB1 c
    unfold doubleCube
    rw [image_union, hZ', hZ', t, h]
  have hPrev : ∀ c : Edge L k (j + 1), doubleCubeLinks L (meshAt L k j) c.opposite =
      doubleCubeLinks L (meshAt L k j) c := by
    intro c
    have hD : doubleCube L (meshAt L k j) c.opposite =
        doubleCube L (meshAt L k j) c := union_comm _ _
    unfold doubleCubeLinks
    rw [hD]
  have hmem : ∀ (c : Edge L k (j + 1)) (b : Edge L k j),
      b ∈ doubleCubeLinks L (meshAt L k j) c →
        edgeImage f b ∈ doubleCubeLinks L (meshAt L k j) (edgeImage f c) := by
    intro c b hb
    obtain ⟨t, h⟩ := edgeImage_spec hMj hBj b
    refine ⟨?_, ?_⟩
    · rw [t, coe_vertexImage hMj, ← himg]
      exact ⟨_, hb.1, rfl⟩
    · rw [h, coe_vertexImage hMj, ← himg]
      exact ⟨_, hb.2, rfl⟩
  have hmem' : ∀ (c : Edge L k (j + 1)) (b : Edge L k j),
      b ∈ doubleCubeLinks L (meshAt L k j) (edgeImage f c) →
        edgePreimage f b ∈ doubleCubeLinks L (meshAt L k j) c := by
    intro c b hb
    obtain ⟨t, h⟩ := edgePreimage_spec hMj hBj hfi b
    have key : ∀ x : Vertex L k j, (x : AmbientSpace) ∈
        doubleCube L (meshAt L k j) (edgeImage f c) →
        ((vertexPreimage f x : Vertex L k j) : AmbientSpace) ∈
          doubleCube L (meshAt L k j) c := by
      intro x hx
      rw [← himg] at hx
      obtain ⟨z, hz, e⟩ := hx
      have e' : ((vertexPreimage f x : Vertex L k j) : AmbientSpace) = z :=
        hfi ((apply_vertexPreimage hMj x).trans e.symm)
      rw [e']
      exact hz
    exact ⟨by rw [t]; exact key _ hb.1, by rw [h]; exact key _ hb.2⟩
  have hinvrev : ∀ b : Edge L k j, edgePreimage f b.opposite = (edgePreimage f b).opposite := by
    intro b
    have e := edgeImage_opposite hMj hBj (edgePreimage f b)
    rw [edgeImage_edgePreimage hMj hBj hfi] at e
    rw [← e, edgePreimage_edgeImage hMj hBj hfi]
  have hqS : ∀ i (_ : MapsSublatticeOnto (meshAt L k i) f)
      (_ : Tower.MapsSublatticeOnto k i g) (x : Vertex L k i),
      projVertex L 1 k i (vertexImage f x) =
        Tower.vertexImage (k := k) (j := i) g (projVertex L 1 k i x) := by
    intro i hMi hMgi x
    apply Subtype.ext
    rw [torus_coe_vertexImage hMgi]
    show TorusMetric.torusProj (PeriodicLattice.torusSide L 1)
        ((vertexImage f x : Vertex L k i) : AmbientSpace) =
      g (TorusMetric.torusProj (PeriodicLattice.torusSide L 1) (x : AmbientSpace))
    rw [coe_vertexImage hMi, hgπ]
  have hqB : ∀ i (_ : i ≤ k) (_ : MapsSublatticeOnto (meshAt L k i) f)
      (_ : MapsLinksOnto (meshAt L k i) f)
      (_ : Tower.MapsSublatticeOnto k i g) (_ : Tower.MapsEdgesOnto k i g)
      (b : Edge L k i),
      projEdge L 1 k i (edgeImage f b) =
        Tower.edgeImage (k := k) (j := i) g (projEdge L 1 k i b) := by
    intro i hik hMi hBi hMgi hBgi b
    have q := (hQ L 1 k i hL one_pos hik).1
    refine PeriodicLattice.Bond.ext ?_ ?_
    · rw [(q _).1, (edgeImage_spec hMi hBi b).1, hqS i hMi hMgi,
        (torus_edgeImage_spec hMgi hBgi _).1, (q b).1]
    · rw [(q _).2.1, (edgeImage_spec hMi hBi b).2, hqS i hMi hMgi,
        (torus_edgeImage_spec hMgi hBgi _).2, (q b).2.1]
  have Qof : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
      ProjPreservesStructures L 1 k j c :=
    fun c hc => (hF'.2.2.2.2.2.2 hk 1 one_pos).2 j hjk c hc
  have hq1 := (hQ L 1 k (j + 1) hL one_pos (by omega)).1
  have dpos : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
      (projEdge L 1 k (j + 1) c).IsPositivelyOriented := fun c hc => (hq1 c).2.2.1 hc
  obtain ⟨c', hc', hrel⟩ : ∃ c' : Edge L k (j + 1), c'.IsPositivelyOriented ∧
      (c' = edgeImage f c ∨ c' = (edgeImage f c).opposite) := by
    by_cases h : (edgeImage f c).IsPositivelyOriented
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, isPositivelyOriented_opposite h, Or.inr rfl⟩
  have hP : doubleCubeLinks L (meshAt L k j) c' =
      doubleCubeLinks L (meshAt L k j) (edgeImage f c) := by
    rcases hrel with rfl | rfl
    · rfl
    · exact hPrev _
  have hV' : pushField f V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c' := by
    refine ⟨⟨fun b hb => hV.1.1 _ (hmem' c b (hP ▸ hb)), fun b hb => ?_⟩, fun b hb => ?_⟩
    · show V (edgePreimage f b.opposite) = (V (edgePreimage f b))⁻¹
      rw [hinvrev]
      exact hV.1.2 _ (hmem' c b (hP ▸ hb))
    · exact hV.2 _ (hmem' c b (hP ▸ hb))
  have hO := (hserve.fullSpace k j hjk c hc).subset_complexDomain hV
  have hO' := (hserve.fullSpace k j hjk c' hc').subset_complexDomain hV'
  have Q := Qof c hc
  have Q' := Qof c' hc'
  obtain ⟨w₁, w₂⟩ := extendByOne_spec Q hV.1
  obtain ⟨w₁', w₂'⟩ := extendByOne_spec Q' hV'.1
  have htr : extendByOne L k j c' (pushField f V) =
      PeriodicLattice.transportGaugeField σ (extendByOne L k j c V) := by
    rw [← torus_pushField_eq_transportGaugeField hσg hBgj]
    exact pushField_eq_of_agree w₁ w₂ w₁' w₂' (fun b hb => hP ▸ hmem c b hb)
      (fun b hb => hmem' c b (hP ▸ hb)) (fun _ => rfl)
      (hqB j hjk.le hMj hBj hMgj hBgj) (edgeImage_edgePreimage hMj hBj hfi)
      (torus_edgeImage_edgePreimage hMgj hBgj hgi) (torus_edgePreimage_edgeImage hMgj hBgj hgi)
  have e₃ := htr
  simp only [extendByOne] at e₃
  have hW := (Q.mem_complexDomain_iff V hV.1).1 hO
  have hW' := (Q'.mem_complexDomain_iff _ hV'.1).1 hO'
  have himgB : PeriodicLattice.bondImage σ (projEdge L 1 k (j + 1) c) =
      projEdge L 1 k (j + 1) (edgeImage f c) := by
    rw [torus_bondImage_eq_edgeImage hσg hMg1 hBg1, hqB (j + 1) (by omega) hMf hB1 hMg1 hBg1]
  have hi₀ : -((1 : ℕ) : ℤ) ≤ PeriodicLattice.levelDepth k (j + 1) := by
    simp only [PeriodicLattice.levelDepth]
    omega
  have hrelπ : projEdge L 1 k (j + 1) c' =
        PeriodicLattice.bondImage σ (projEdge L 1 k (j + 1) c) ∨
      projEdge L 1 k (j + 1) c' =
        (PeriodicLattice.bondImage σ (projEdge L 1 k (j + 1) c)).opposite := by
    rcases hrel with e | e
    · exact Or.inl (by rw [himgB, e])
    · exact Or.inr (by rw [himgB, e, ← (hq1 _).2.2.2])
  have hCA := hT L 1 k j _ σ hL one_pos hi₀ hσ hjk le_rfl (extendByOne L k j c V)
    (projEdge L 1 k (j + 1) c) (projEdge L 1 k (j + 1) c') (dpos c hc) (dpos c' hc')
    hrelπ (Q.projField_spec V hV.1).2
  refine ⟨fun y hy x hx => ?_, ?_⟩
  · have hy₁ : y = c.initial ∨ y = c.terminal := by simpa using hy
    have hyc' : vertexImage f y = c'.initial ∨ vertexImage f y = c'.terminal := by
      obtain ⟨t, h⟩ := edgeImage_spec hMf hB1 c
      rcases hrel with e | e <;> rcases hy₁ with e' | e' <;> rw [e, e']
      · exact Or.inl t.symm
      · exact Or.inr h.symm
      · exact Or.inr t.symm
      · exact Or.inl h.symm
    have hx' : vertexImage f x ∈ cubeVertices L (meshAt L k j) (vertexImage f y) := by
      show ((vertexImage f x : Vertex L k j) : AmbientSpace) ∈
        cube L (meshAt L k j) (vertexImage f y)
      rw [coe_vertexImage hMj, ← hZ']
      exact ⟨_, hx, rfl⟩
    have e₁ := Q.complexContourMean_eq V hO y hy₁ x hx
    have e₂ := Q'.complexContourMean_eq _ hO' _ hyc' _ hx'
    have hπy : projVertex L 1 k (j + 1) y = (projEdge L 1 k (j + 1) c).source ∨
        projVertex L 1 k (j + 1) y = (projEdge L 1 k (j + 1) c).target := by
      rcases hy₁ with rfl | rfl
      · exact Or.inl (hq1 c).1.symm
      · exact Or.inr (hq1 c).2.1.symm
    have hπx : projVertex L 1 k j x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (projVertex L 1 k (j + 1) y) := by
      rcases hy₁ with rfl | rfl
      · rw [← (hq1 c).1]
        show ((projVertex L 1 k j x : Tower.Vertex L 1 k j) : PeriodicLattice.FourTorus L 1) ∈
          PeriodicLattice.unitBlock (projEdge L 1 k (j + 1) c).source
        rw [← Q.cube_initial]
        exact ⟨_, hx, rfl⟩
      · rw [← (hq1 c).2.1]
        show ((projVertex L 1 k j x : Tower.Vertex L 1 k j) : PeriodicLattice.FourTorus L 1) ∈
          PeriodicLattice.unitBlock (projEdge L 1 k (j + 1) c).target
        rw [← Q.cube_terminal]
        exact ⟨_, hx, rfl⟩
    have hdiam : Matrices.ComplexMatrix2.familyDiameter
        (PeriodicLattice.contourHolonomies (extendByOne L k j c V)
          (projVertex L 1 k (j + 1) y) (projVertex L 1 k j x)) <
        Averaging.centreOfMassDiameter := by
      rcases hπy with e | e
      · rw [e] at hπx ⊢
        exact hW.1.2.1 _ hπx
      · rw [e] at hπx ⊢
        exact hW.1.2.2 _ hπx
    have hin : extendByOne L k j c V ∈ PeriodicLattice.complexGaugeFields
        (PeriodicLattice.bondsInside (PeriodicLattice.unitBlock (projVertex L 1 k (j + 1) y)) :
          Set (PeriodicLattice.BondAtLevel L 1 k j)) := by
      have hsub : ∀ b ∈ (PeriodicLattice.bondsInside
          (PeriodicLattice.unitBlock (projVertex L 1 k (j + 1) y)) :
            Set (PeriodicLattice.BondAtLevel L 1 k j)),
          b ∈ (PeriodicLattice.bondsInDoubleBlock (projEdge L 1 k (j + 1) c) :
            Set (PeriodicLattice.BondAtLevel L 1 k j)) := by
        intro b hb
        rcases hπy with e | e
        · rw [e] at hb
          exact ⟨Or.inl hb.1, Or.inl hb.2⟩
        · rw [e] at hb
          exact ⟨Or.inr hb.1, Or.inr hb.2⟩
      have hcfg := (Q.projField_spec V hV.1).2
      exact ⟨fun b hb => hcfg.1 b (hsub b hb), fun b hb => hcfg.2 b (hsub b hb)⟩
    obtain ⟨ε, hε⟩ := hH
    have hcc := (hε L 1 _ σ hL one_pos hi₀ hσ).2.2.2.1 k j hjk le_rfl
      (projVertex L 1 k (j + 1) y) (projVertex L 1 k j x) hπx
    have hcarried := hcc.2.2.2.1 (extendByOne L k j c V)
      ⟨⟨hin, by rw [hcc.1 _ hin]; exact hdiam⟩, ⟨hin, hdiam⟩⟩
    rw [e₁, e₂, e₃, hqS (j + 1) hMf hMg1, hqS j hMj hMgj, torus_vertexImage_eq_sitePreimage hσg,
      torus_vertexImage_eq_sitePreimage hσg]
    exact hcarried
  · have m₁ := Q.complexSmoothing_eq V hO
    have m₂ := Q'.complexSmoothing_eq _ hO'
    rcases hrel with e | e
    · rw [← e, m₂, e₃, hCA.average_image (by rw [himgB, e]) hW, ← m₁]
    · have es : edgeImage f c = c'.opposite := by rw [e]; rfl
      have hdet : (complexSmoothing L V c).det = 1 :=
        ((hD.2 L k (j + 1) hL (by omega) (by omega)).2 c V hc hO).2
      have hWσ : PeriodicLattice.transportGaugeField σ (extendByOne L k j c V) ∈
          (PeriodicLattice.complexAveragingDomainNearOne (projEdge L 1 k (j + 1) c') :
            Set (PeriodicLattice.BondAtLevel L 1 k j → Matrices.ComplexMatrix2)) := htr ▸ hW'
      rw [es, complexSmoothing_opposite_of_positive (hs (j + 1)) hc', m₂, e₃,
        hCA.average_opposite (by rw [himgB, e, ← (hq1 _).2.2.2]) hW hWσ, ← m₁,
        Matrix.nonsing_inv_nonsing_inv _ (by rw [hdet]; exact isUnit_one)]
theorem statement_holds (hF : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hQ : Tower.EdgeProjectionProperties)
    (hZ : Tower.BlockStructure)
    (hT : PeriodicLattice.ComplexAverageEquivariance)
    (hH : PeriodicLattice.ComplexHolonomiesAndAveragesCovariance.Statement)
    (hR : Tower.SmoothingNearIdentity)
    (hD : Tower.ComplexMeanLiesInComplexGaugeGroup) :
    Tower.FullSpace.ComplexSmoothingEquivariance.Statement := by
  intro L hL k j hjk f hf hMf c hc V hV
  exact holds_at hF hQ hZ hT hH hR hD hL hjk hf hMf c hc V hV
end Tower.FullSpace.ComplexSmoothingEquivarianceProof
end
end YangMills.Construction

import YangMills.Construction.Lattice.ElementarySquareCorners
import YangMills.Construction.Lattice.ImagesOfBondsAndPlaquettesUnderLatticeIsometries
import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.SymmetryImages
open YangMills.Construction.InfiniteLattice (AmbientSpace)
private theorem val_image_vertices {L m : ℕ} {j : ℤ} (p : Plaquette L m j) :
    Subtype.val '' p.vertices =
      {c | c ∈ ElementarySquare.vertexList (pointOnAxis L m) (meshSize L j) p.origin p.firstAxis
        p.secondAxis} := by
  have hstep : ∀ μ, ((unitStep L m j μ : Site L m j) : FourTorus L m) =
      pointOnAxis L m μ (meshSize L j) :=
    fun _ => rfl
  ext c
  simp [Plaquette.vertices, ElementarySquare.vertexList, hstep]
  simp only [eq_comm (a := c)]
private theorem val_image_cornerSet {a : ℝ} (p : InfiniteLattice.ElementaryPlaquette a) :
    Subtype.val '' p.cornerSet =
      {c | c ∈ ElementarySquare.vertexList (fun μ t => (Pi.single μ t : AmbientSpace)) a p.corner
        p.lowAxis p.highAxis} := by
  have hstep : ∀ μ, ((InfiniteLattice.axisStep a μ : InfiniteLattice.LatticePoint a) :
      AmbientSpace) = Pi.single μ a :=
    fun _ => rfl
  ext c
  simp [InfiniteLattice.ElementaryPlaquette.cornerSet, ElementarySquare.vertexList, hstep]
  simp only [eq_comm (a := c)]
private theorem onTorus {L m K : ℕ} (hsym : Tower.TorusSymmetries L m K)
    (hsq : ElementarySquare.SquareFacts (sublattice L m (levelDepth K 0)) (pointOnAxis L m)
      (meshSize L (levelDepth K 0)))
    (g : TorusLatticeSymmetry L m K) :
    (∀ b : Bond L m (K : ℤ), ∃ b' : Bond L m (K : ℤ),
      (b'.source, b'.target) = g.pairMap (b.source, b.target)) ∧
    (∀ b : Bond L m (K : ℤ), g.bondMap b.opposite = (g.bondMap b).opposite) ∧
    (∀ p : Plaquette L m (K : ℤ), ∃! p' : Plaquette L m (K : ℤ),
      p'.vertices = g.pointMap '' p.vertices) := by
  have hlev : levelDepth K 0 = (K : ℤ) := rfl
  rw [hlev] at hsq
  obtain ⟨-, hevery⟩ := hsym 0 (Nat.zero_le K) g.toFun g.dist_eq g.image_eq
  obtain ⟨-, hbond, hplaq⟩ := hevery 0 le_rfl
  have hbond₁ : ∀ b : Bond L m (K : ℤ), ∃ b' : Bond L m (K : ℤ),
      (b'.source : FourTorus L m) = g.toFun b.source ∧
        (b'.target : FourTorus L m) = g.toFun b.target := hbond.1
  have hplaq₁ : ∀ p : Plaquette L m (K : ℤ), ∃ p' : Plaquette L m (K : ℤ),
      Subtype.val '' p'.vertices = g.toFun '' (Subtype.val '' p.vertices) := hplaq.1
  refine ⟨fun b => ?_, g.bondMap_opposite, fun p => ?_⟩
  · obtain ⟨b', hsrc, htgt⟩ := hbond₁ b
    exact ⟨b', Prod.ext (Subtype.ext hsrc) (Subtype.ext htgt)⟩
  · obtain ⟨p', hp'⟩ := hplaq₁ p
    have himg : Subtype.val '' (g.pointMap '' p.vertices) =
        g.toFun '' (Subtype.val '' p.vertices) := by
      rw [image_image, image_image]
      rfl
    have hexist : p'.vertices = g.pointMap '' p.vertices :=
      Subtype.val_injective.image_injective (hp'.trans himg.symm)
    refine ⟨p', hexist, fun q hq => ?_⟩
    have hagree : Subtype.val '' q.vertices = Subtype.val '' p'.vertices := by
      rw [hq, hexist]
    rw [val_image_vertices, val_image_vertices] at hagree
    obtain ⟨e₁, e₂, e₃⟩ := (hsq q.origin q.origin.2 p'.origin p'.origin.2 q.firstAxis
      q.secondAxis p'.firstAxis p'.secondAxis q.firstAxis_lt_secondAxis
      p'.firstAxis_lt_secondAxis).2.1 hagree
    exact Plaquette.ext (Subtype.ext e₁) e₂ e₃
private theorem onSpace {L K : ℕ} (hsym : Tower.FullSpace.SpaceSymmetries L K)
    (hsq : ElementarySquare.SquareFacts
      (InfiniteLattice.latticeSubgroup (meshSize L (levelDepth K 0)))
      (fun μ t => (Pi.single μ t : AmbientSpace)) (meshSize L (levelDepth K 0)))
    {a : ℝ} (ha : a = Tower.meshAt L K 0) (g : InfiniteLattice.LatticeSymmetry a) :
    (∀ b : InfiniteLattice.Link a, ∃ b' : InfiniteLattice.Link a,
      (b'.initial, b'.terminal) = g.pairMap (b.initial, b.terminal)) ∧
    (∀ b : InfiniteLattice.Link a, g.linkMap b.opposite = (g.linkMap b).opposite) ∧
    (∀ p : InfiniteLattice.ElementaryPlaquette a, ∃! p' : InfiniteLattice.ElementaryPlaquette a,
      p'.cornerSet = g.pointMap '' p.cornerSet) := by
  subst ha
  rw [Tower.meshSize_levelDepth] at hsq
  obtain ⟨-, hevery, -⟩ := hsym 0 (Nat.zero_le K) g.toFun g.preservesDist g.image_eq
  obtain ⟨-, -, hplaq⟩ := hevery 0 le_rfl
  have hplaq₁ : ∀ p : InfiniteLattice.ElementaryPlaquette (Tower.meshAt L K 0),
      ∃ p' : InfiniteLattice.ElementaryPlaquette (Tower.meshAt L K 0),
        Subtype.val '' p'.cornerSet = g.toFun '' (Subtype.val '' p.cornerSet) := hplaq.1
  refine ⟨fun b => ⟨g.linkMap b, rfl⟩, fun b => rfl, fun p => ?_⟩
  obtain ⟨p', hp'⟩ := hplaq₁ p
  have himg : Subtype.val '' (g.pointMap '' p.cornerSet) =
      g.toFun '' (Subtype.val '' p.cornerSet) := by
    rw [image_image, image_image]
    rfl
  have hexist : p'.cornerSet = g.pointMap '' p.cornerSet :=
    Subtype.val_injective.image_injective (hp'.trans himg.symm)
  refine ⟨p', hexist, fun q hq => ?_⟩
  have hagree : Subtype.val '' q.cornerSet = Subtype.val '' p'.cornerSet := by
    rw [hq, hexist]
  rw [val_image_cornerSet, val_image_cornerSet] at hagree
  obtain ⟨e₁, e₂, e₃⟩ := (hsq q.corner q.corner.2 p'.corner p'.corner.2 q.lowAxis q.highAxis
    p'.lowAxis p'.highAxis q.lowAxis_lt_highAxis p'.lowAxis_lt_highAxis).2.1 hagree
  exact InfiniteLattice.ElementaryPlaquette.ext (Subtype.ext e₁) e₂ e₃
theorem symmetriesPreserveBondsAndPlaquettes_holds
    (hTower : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hSquare : ElementarySquare.ElementarySquareStatement) :
    SymmetriesPreserveBondsAndPlaquettes := by
  intro D
  have hLpos : 0 < D.L := by
    have := D.isAdmissible.2
    omega
  obtain ⟨-, -, -, hTorus, hSpace, -⟩ := hTower D.L hLpos D.isAdmissible (D.K : ℕ)
  obtain ⟨hsq₁, hsq₂⟩ := hSquare D.L D.isAdmissible (D.m : ℕ) 0 (D.K : ℕ) D.m.pos
    (Nat.zero_le _)
  have hmesh : meshSize D.L ((D.K : ℕ) : ℤ) = Tower.meshAt D.L (D.K : ℕ) 0 := by
    simp [meshSize, Tower.meshAt]
  exact ⟨fun g => onTorus (hTorus (D.m : ℕ) D.m.pos) hsq₁ g,
    fun g => onSpace hSpace hsq₂ hmesh g⟩
end YangMills.Construction.PeriodicLattice.SymmetryImages
end

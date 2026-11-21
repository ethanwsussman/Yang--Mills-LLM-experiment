import YangMills.Construction.Lattice.ComplexAverageAtAnImageBondProof
import YangMills.Construction.Towers.BlocksOfATower
import YangMills.Construction.Towers.ReverseOfAStraightPathAtTheSideInfinity
import YangMills.Construction.Towers.ReverseOfAStraightPathOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.AxisPathReversal
theorem finsum_mem_eq_neg_of_inverse {S M : Type*} [AddCommGroup M] {s t : Set S}
    {f g : S → S} (hf : MapsTo f s t) (hg : MapsTo g t s) (hgf : ∀ x ∈ s, g (f x) = x)
    (hfg : ∀ z ∈ t, f (g z) = z) (F G : S → M) (hFG : ∀ x ∈ s, G (f x) = -F x) :
    ∑ᶠ z ∈ t, G z = -∑ᶠ x ∈ s, F x := by
  have hbij : BijOn f s t :=
    ⟨hf, fun a ha b hb hab => by rw [← hgf a ha, ← hgf b hb, hab],
      fun z hz => ⟨g z, hg hz, hfg z hz⟩⟩
  have hsum : ∑ᶠ x ∈ s, -F x = ∑ᶠ z ∈ t, G z :=
    finsum_mem_eq_of_bijOn f hbij fun x hx => (hFG x hx).symm
  rw [← hsum]
  simp only [finsum_neg_distrib]
theorem blockingFactor_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < L := by
  have := hL.2
  omega
theorem mem_complexLieAlgebra_of_mem {X : Matrices.ComplexMatrix2}
    (hX : X ∈ PeriodicLattice.compactLieAlgebra) :
    X ∈ PeriodicLattice.complexLieAlgebra := by
  obtain ⟨_, ht⟩ := hX
  exact ht
section PeriodicSide
variable {L m : ℕ} {j j' : ℤ}
theorem coe_shiftAcross (hL : 0 < L) (hjj : j ≤ j') (c : PeriodicLattice.Bond L m j)
    (x : PeriodicLattice.Site L m j') :
    ((PeriodicLattice.shiftAcross c x : PeriodicLattice.Site L m j') :
        PeriodicLattice.FourTorus L m) =
      (x : PeriodicLattice.FourTorus L m) +
        ((c.target : PeriodicLattice.FourTorus L m) -
          (c.source : PeriodicLattice.FourTorus L m)) := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.coe_shiftAcross <;> assumption
theorem shiftAcross_opposite_shiftAcross (hL : 0 < L) (hjj : j ≤ j')
    (c : PeriodicLattice.Bond L m j) (x : PeriodicLattice.Site L m j') :
    PeriodicLattice.shiftAcross c.opposite (PeriodicLattice.shiftAcross c x) = x := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.shiftAcross_opposite_shiftAcross <;> assumption
theorem shiftAcross_shiftAcross_opposite (hL : 0 < L) (hjj : j ≤ j')
    (c : PeriodicLattice.Bond L m j) (x : PeriodicLattice.Site L m j') :
    PeriodicLattice.shiftAcross c (PeriodicLattice.shiftAcross c.opposite x) = x := by
  apply Subtype.ext
  rw [coe_shiftAcross hL hjj, coe_shiftAcross hL hjj]
  change (x : PeriodicLattice.FourTorus L m) +
    ((c.source : PeriodicLattice.FourTorus L m) - (c.target : PeriodicLattice.FourTorus L m)) +
      ((c.target : PeriodicLattice.FourTorus L m) -
        (c.source : PeriodicLattice.FourTorus L m)) = x
  abel
theorem bondFormSumAlong_crossingPath_opposite (hrev : PeriodicLattice.AxialPathReversal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj' : -(m : ℤ) ≤ j')
    (hjj : j ≤ j') (c : PeriodicLattice.Bond L m j) (x : PeriodicLattice.Site L m j')
    (μ : Fin 4) (t : ℤ)
    (hd : PeriodicLattice.IsAxialDisplacement x (PeriodicLattice.shiftAcross c x) μ t)
    (A : PeriodicLattice.Bond L m j' → Matrices.ComplexMatrix2)
    (hA : PeriodicLattice.IsBondForm PeriodicLattice.complexLieAlgebra A) :
    PeriodicLattice.bondFormSumAlong A
        (PeriodicLattice.crossingPath c.opposite (PeriodicLattice.shiftAcross c x)) =
      -PeriodicLattice.bondFormSumAlong A (PeriodicLattice.crossingPath c x) := by
  have hr := (hrev L m hL hm j' hj' x _ μ t hd).2.2.2 A hA
  rw [PeriodicLattice.crossingPath, shiftAcross_opposite_shiftAcross (blockingFactor_pos hL) hjj, hr]
  rfl
theorem blockSums_opposite (hrev : PeriodicLattice.AxialPathReversal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj' : -(m : ℤ) ≤ j')
    (hjj : j ≤ j') (c : PeriodicLattice.Bond L m j)
    (hbij : BijOn (fun x : PeriodicLattice.FourTorus L m =>
        x + ((c.target : PeriodicLattice.FourTorus L m) -
          (c.source : PeriodicLattice.FourTorus L m)))
      (PeriodicLattice.unitBlock c.source) (PeriodicLattice.unitBlock c.target))
    (hst : ∀ x : PeriodicLattice.Site L m j',
      (x : PeriodicLattice.FourTorus L m) ∈ PeriodicLattice.unitBlock c.source →
      ∃ (μ : Fin 4) (t : ℤ),
        PeriodicLattice.IsAxialDisplacement x (PeriodicLattice.shiftAcross c x) μ t)
    (A : PeriodicLattice.Bond L m j' → Matrices.ComplexMatrix2)
    (hA : PeriodicLattice.IsBondForm PeriodicLattice.complexLieAlgebra A) :
    (∑ᶠ z ∈ PeriodicLattice.sitesInBlock j' c.opposite.source,
        PeriodicLattice.bondFormSumAlong A (PeriodicLattice.crossingPath c.opposite z)) =
      -(∑ᶠ x ∈ PeriodicLattice.sitesInBlock j' c.source,
        PeriodicLattice.bondFormSumAlong A (PeriodicLattice.crossingPath c x)) ∧
      PeriodicLattice.scaledLinearBlockAverage A c.opposite =
        -PeriodicLattice.scaledLinearBlockAverage A c := by
  have hpos := blockingFactor_pos hL
  have hs : MapsTo (PeriodicLattice.shiftAcross c) (PeriodicLattice.sitesInBlock j' c.source)
      (PeriodicLattice.sitesInBlock j' c.opposite.source) := by
    intro x hx
    change ((PeriodicLattice.shiftAcross c x : PeriodicLattice.Site L m j') :
      PeriodicLattice.FourTorus L m) ∈ PeriodicLattice.unitBlock c.target
    rw [coe_shiftAcross hpos hjj]
    exact hbij.mapsTo hx
  have ht : MapsTo (PeriodicLattice.shiftAcross c.opposite)
      (PeriodicLattice.sitesInBlock j' c.opposite.source)
      (PeriodicLattice.sitesInBlock j' c.source) := by
    intro z hz
    have hz' : (z : PeriodicLattice.FourTorus L m) ∈ PeriodicLattice.unitBlock c.target := hz
    obtain ⟨p, hp, hpz⟩ := hbij.surjOn hz'
    have hpz' : p + ((c.target : PeriodicLattice.FourTorus L m) -
        (c.source : PeriodicLattice.FourTorus L m)) = z :=
      hpz
    have hcoe : ((PeriodicLattice.shiftAcross c.opposite z : PeriodicLattice.Site L m j') :
        PeriodicLattice.FourTorus L m) = p := by
      rw [coe_shiftAcross hpos hjj]
      change (z : PeriodicLattice.FourTorus L m) +
        ((c.source : PeriodicLattice.FourTorus L m) -
          (c.target : PeriodicLattice.FourTorus L m)) = p
      rw [← hpz']
      abel
    change ((PeriodicLattice.shiftAcross c.opposite z : PeriodicLattice.Site L m j') :
      PeriodicLattice.FourTorus L m) ∈ PeriodicLattice.unitBlock c.source
    rw [hcoe]
    exact hp
  have hl : ∀ x ∈ PeriodicLattice.sitesInBlock j' c.source,
      PeriodicLattice.shiftAcross c.opposite (PeriodicLattice.shiftAcross c x) = x :=
    fun x _ => shiftAcross_opposite_shiftAcross hpos hjj c x
  have hr : ∀ z ∈ PeriodicLattice.sitesInBlock j' c.opposite.source,
      PeriodicLattice.shiftAcross c (PeriodicLattice.shiftAcross c.opposite z) = z :=
    fun z _ => shiftAcross_shiftAcross_opposite hpos hjj c z
  have hcross : ∀ x ∈ PeriodicLattice.sitesInBlock j' c.source,
      PeriodicLattice.bondFormSumAlong A
          (PeriodicLattice.crossingPath c.opposite (PeriodicLattice.shiftAcross c x)) =
        -PeriodicLattice.bondFormSumAlong A (PeriodicLattice.crossingPath c x) := by
    intro x hx
    obtain ⟨μ, t, hd⟩ := hst x hx
    exact bondFormSumAlong_crossingPath_opposite hrev hL hm hj' hjj c x μ t hd A hA
  refine ⟨finsum_mem_eq_neg_of_inverse hs ht hl hr _ _ hcross, ?_⟩
  unfold PeriodicLattice.scaledLinearBlockAverage PeriodicLattice.linearBlockSum
  rw [← smul_neg]
  congr 1
  refine finsum_mem_eq_neg_of_inverse hs ht hl hr _ _ fun x hx => ?_
  change PeriodicLattice.contourFormAverage A c.target (PeriodicLattice.shiftAcross c x) +
      PeriodicLattice.bondFormSumAlong A
        (PeriodicLattice.crossingPath c.opposite (PeriodicLattice.shiftAcross c x)) -
      PeriodicLattice.contourFormAverage A c.source
        (PeriodicLattice.shiftAcross c.opposite (PeriodicLattice.shiftAcross c x)) =
    -(PeriodicLattice.contourFormAverage A c.source x +
        PeriodicLattice.bondFormSumAlong A (PeriodicLattice.crossingPath c x) -
      PeriodicLattice.contourFormAverage A c.target (PeriodicLattice.shiftAcross c x))
  rw [hcross x hx, hl x hx]
  abel
theorem abs_lt_pow_of_mul_meshAt_lt {L m k i : ℕ} (hL : 0 < L) {n : ℤ}
    (hn : ((|n| : ℤ) : ℝ) * meshAt L k i < PeriodicLattice.torusSide L m / 2) :
    ((|n| : ℤ) : ℝ) < (L : ℝ) ^ ((m : ℤ) + PeriodicLattice.levelDepth k i) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hexp : (m : ℤ) + PeriodicLattice.levelDepth k i + ((i : ℤ) - (k : ℤ)) = m := by
    simp only [PeriodicLattice.levelDepth]
    ring
  have he : (L : ℝ) ^ ((m : ℤ) + PeriodicLattice.levelDepth k i) * meshAt L k i =
      PeriodicLattice.torusSide L m / 2 := by
    rw [meshAt, ← zpow_add₀ hLr.ne', hexp, PeriodicLattice.torusSide, zpow_natCast]
    ring
  rw [← he] at hn
  exact lt_of_mul_lt_mul_right hn (zpow_pos hLr _).le
theorem holdsOnPeriodicSide (hblocks : BlockStructure)
    (hrev : PeriodicLattice.AxialPathReversal) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (k m : ℕ) (hm : 0 < m) :
    HoldsOnPeriodicSide L m k := by
  have hpos := blockingFactor_pos hL
  refine ⟨fun i hi => ⟨?_, ?_⟩, ?_⟩
  · rintro B ⟨hB, hB'⟩
    exact ⟨fun b hb => mem_complexLieAlgebra_of_mem (hB b hb), hB'⟩
  · intro x x' μ n hx hn
    have hj : -(m : ℤ) ≤ PeriodicLattice.levelDepth k i := by
      simp only [PeriodicLattice.levelDepth]
      omega
    have hd : PeriodicLattice.IsAxialDisplacement x x' μ n :=
      ⟨hx, abs_lt_pow_of_mul_meshAt_lt hpos hn⟩
    obtain ⟨hb, hp, -, hf⟩ := hrev L m hL hm _ hj x x' μ n hd
    exact ⟨⟨(μ, n), hd⟩, hb, hp, fun B hB => hf B hB⟩
  · intro j hj c B hB
    obtain ⟨μ, hμ⟩ := c.isNeighbour
    have htr : BlockShiftAlongBond L m k (j + 1) c μ :=
      ((hblocks L k (j + 1) hL (by omega) (by omega) hj).1 m hm).2.2.1 c μ hμ
    have hle : PeriodicLattice.levelDepth k (j + 1) ≤ PeriodicLattice.levelDepth k j := by
      simp only [PeriodicLattice.levelDepth]
      omega
    have hj' : -(m : ℤ) ≤ PeriodicLattice.levelDepth k j := by
      simp only [PeriodicLattice.levelDepth]
      omega
    have hst : ∀ x : PeriodicLattice.Site L m (PeriodicLattice.levelDepth k j),
        (x : PeriodicLattice.FourTorus L m) ∈ PeriodicLattice.unitBlock c.source →
        ∃ (ν : Fin 4) (t : ℤ),
          PeriodicLattice.IsAxialDisplacement x (PeriodicLattice.shiftAcross c x) ν t := by
      intro x hx
      obtain ⟨-, ⟨t, -, hd⟩, -⟩ :=
        htr.2 x (PeriodicLattice.shiftAcross c x) hx (coe_shiftAcross hpos hle c x)
      exact ⟨μ, t, hd⟩
    exact blockSums_opposite hrev hL hm hj' hle c htr.1 hst B hB
end PeriodicSide
section FullSpaceSide
open InfiniteLattice (AmbientSpace)
theorem meshAt_succ {L : ℕ} (hL : 0 < L) (k j : ℕ) :
    meshAt L k (j + 1) = (L : ℝ) * meshAt L k j := by
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [meshAt, meshAt,
    show ((j + 1 : ℕ) : ℤ) - (k : ℤ) = ((j : ℤ) - (k : ℤ)) + 1 by push_cast; ring,
    zpow_add_one₀ hLr]
  ring
theorem coe_toFiner {L : ℕ} (hL : 0 < L) (k j : ℕ) (y : FullSpace.Vertex L k (j + 1)) :
    ((FullSpace.toFiner (meshAt L k j) y : FullSpace.Vertex L k j) : AmbientSpace) = y := by
  obtain ⟨n, hn⟩ := y.2
  have hex : ∃ x : FullSpace.Vertex L k j, (x : AmbientSpace) = y := by
    refine ⟨⟨y, fun μ => n μ * (L : ℤ), fun μ => ?_⟩, rfl⟩
    rw [hn μ, meshAt_succ hL]
    push_cast
    ring
  exact Classical.epsilon_spec hex
theorem coe_shifted {L : ℕ} (hL : 0 < L) (k j : ℕ) (c : FullSpace.Edge L k (j + 1))
    (x : FullSpace.Vertex L k j) :
    ((FullSpace.shifted c x : FullSpace.Vertex L k j) : AmbientSpace) =
      (x : AmbientSpace) + ((c.terminal : AmbientSpace) - (c.initial : AmbientSpace)) := by
  rw [FullSpace.shifted, AddSubgroup.coe_add, coe_toFiner hL, AddSubgroup.coe_sub]
theorem shifted_opposite_shifted {L : ℕ} (hL : 0 < L) (k j : ℕ)
    (c : FullSpace.Edge L k (j + 1)) (x : FullSpace.Vertex L k j) :
    FullSpace.shifted c.opposite (FullSpace.shifted c x) = x := by
  apply Subtype.ext
  rw [coe_shifted hL, coe_shifted hL]
  change (x : AmbientSpace) + ((c.terminal : AmbientSpace) - (c.initial : AmbientSpace)) +
    ((c.initial : AmbientSpace) - (c.terminal : AmbientSpace)) = x
  abel
theorem shifted_shifted_opposite {L : ℕ} (hL : 0 < L) (k j : ℕ)
    (c : FullSpace.Edge L k (j + 1)) (x : FullSpace.Vertex L k j) :
    FullSpace.shifted c (FullSpace.shifted c.opposite x) = x := by
  apply Subtype.ext
  rw [coe_shifted hL, coe_shifted hL]
  change (x : AmbientSpace) + ((c.initial : AmbientSpace) - (c.terminal : AmbientSpace)) +
    ((c.terminal : AmbientSpace) - (c.initial : AmbientSpace)) = x
  abel
theorem holdsOnFullSpace (hblocks : BlockStructure)
    (hrev : FullSpace.AxisPathReversal.statement) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) : HoldsOnFullSpace L k := by
  have hpos := blockingFactor_pos hL
  refine ⟨fun i hi => ⟨?_, ?_⟩, ?_⟩
  · rintro B ⟨hB, hB'⟩
    exact ⟨fun b hb => mem_complexLieAlgebra_of_mem (hB b hb), hB'⟩
  · intro x x' μ n hx
    have hd : FullSpace.IsAxisDisplacement x x' μ n := hx
    obtain ⟨hb, hp, hf⟩ := hrev L k i hL hi x x' μ n hd
    exact ⟨⟨(μ, n), hd⟩, hb, hp, fun B hB => hf ℂ Matrices.ComplexMatrix2 B hB.2⟩
  · intro j hj c B hB
    obtain ⟨μ, hμ⟩ := c.isAdjacent
    have htr : FullSpace.BlockTranslateAlongBond L k (j + 1) c μ :=
      (hblocks L k (j + 1) hL (by omega) (by omega) hj).2.2.2.1 c μ hμ
    have hbij : BijOn (fun x : AmbientSpace =>
        x + ((c.terminal : AmbientSpace) - (c.initial : AmbientSpace)))
        (FullSpace.cube L (meshAt L k j) c.initial)
        (FullSpace.cube L (meshAt L k j) c.terminal) :=
      htr.1
    have hs : MapsTo (FullSpace.shifted c) (FullSpace.cubeVertices L (meshAt L k j) c.initial)
        (FullSpace.cubeVertices L (meshAt L k j) c.opposite.initial) := by
      intro x hx
      change ((FullSpace.shifted c x : FullSpace.Vertex L k j) : AmbientSpace) ∈
        FullSpace.cube L (meshAt L k j) c.terminal
      rw [coe_shifted hpos]
      exact hbij.mapsTo hx
    have ht : MapsTo (FullSpace.shifted c.opposite)
        (FullSpace.cubeVertices L (meshAt L k j) c.opposite.initial)
        (FullSpace.cubeVertices L (meshAt L k j) c.initial) := by
      intro z hz
      have hz' : (z : AmbientSpace) ∈ FullSpace.cube L (meshAt L k j) c.terminal := hz
      obtain ⟨p, hp, hpz⟩ := hbij.surjOn hz'
      have hpz' : p + ((c.terminal : AmbientSpace) - (c.initial : AmbientSpace)) = z := hpz
      have hcoe : ((FullSpace.shifted c.opposite z : FullSpace.Vertex L k j) : AmbientSpace) =
          p := by
        rw [coe_shifted hpos]
        change (z : AmbientSpace) + ((c.initial : AmbientSpace) - (c.terminal : AmbientSpace)) = p
        rw [← hpz']
        abel
      change ((FullSpace.shifted c.opposite z : FullSpace.Vertex L k j) : AmbientSpace) ∈
        FullSpace.cube L (meshAt L k j) c.initial
      rw [hcoe]
      exact hp
    have hl : ∀ x ∈ FullSpace.cubeVertices L (meshAt L k j) c.initial,
        FullSpace.shifted c.opposite (FullSpace.shifted c x) = x :=
      fun x _ => shifted_opposite_shifted hpos k j c x
    have hr : ∀ z ∈ FullSpace.cubeVertices L (meshAt L k j) c.opposite.initial,
        FullSpace.shifted c (FullSpace.shifted c.opposite z) = z :=
      fun z _ => shifted_shifted_opposite hpos k j c z
    have hcross : ∀ x ∈ FullSpace.cubeVertices L (meshAt L k j) c.initial,
        FullSpace.edgeFormPathSum B
            (FullSpace.crossingPath c.opposite (FullSpace.shifted c x)) =
          -FullSpace.edgeFormPathSum B (FullSpace.crossingPath c x) := by
      intro x hx
      obtain ⟨-, ⟨t, -, hd⟩, -⟩ :=
        htr.2 x (FullSpace.shifted c x) hx (coe_shifted hpos k j c x)
      have hf := (hrev L k j hL (by omega) x _ μ t hd).2.2 ℂ Matrices.ComplexMatrix2 B hB.2
      rw [FullSpace.crossingPath, shifted_opposite_shifted hpos]
      exact hf
    refine ⟨finsum_mem_eq_neg_of_inverse hs ht hl hr _ _ hcross, ?_⟩
    unfold FullSpace.linearSmoothing
    rw [← smul_neg]
    congr 1
    refine finsum_mem_eq_neg_of_inverse hs ht hl hr _ _ fun x hx => ?_
    change FullSpace.contourAverage L B c.terminal (FullSpace.shifted c x) +
        FullSpace.edgeFormPathSum B (FullSpace.crossingPath c.opposite (FullSpace.shifted c x)) -
        FullSpace.contourAverage L B c.initial
          (FullSpace.shifted c.opposite (FullSpace.shifted c x)) =
      -(FullSpace.contourAverage L B c.initial x +
          FullSpace.edgeFormPathSum B (FullSpace.crossingPath c x) -
        FullSpace.contourAverage L B c.terminal (FullSpace.shifted c x))
    rw [hcross x hx, hl x hx]
    abel
end FullSpaceSide
theorem mainStatement_holds (hblocks : BlockStructure)
    (hrev : PeriodicLattice.AxialPathReversal)
    (hrev' : FullSpace.AxisPathReversal.statement) : MainStatement :=
  fun _ hL k => ⟨fun m hm => holdsOnPeriodicSide hblocks hrev hL k m hm,
    holdsOnFullSpace hblocks hrev' hL k⟩
end YangMills.Construction.Tower.AxisPathReversal
end

import YangMills.Construction.Towers.GaugeAndIsometricImagesAreConfigurations
import YangMills.Construction.Towers.WhatTheDilationKeepsProof
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction
open QuotientLattices
namespace Tower.GaugeAndSymmetryImages
def IsUnimodularMatrixGroup (G : Set Matrices.ComplexMatrix2) : Prop :=
  (∀ A ∈ G, A.det = 1) ∧ (∀ A ∈ G, ∀ B ∈ G, A * B ∈ G) ∧ ∀ A ∈ G, A⁻¹ ∈ G
theorem complexGaugeGroup_isUnimodular :
    IsUnimodularMatrixGroup PeriodicLattice.complexGaugeGroup := by
  refine ⟨fun A hA => hA, fun A hA B hB => ?_, fun A hA => ?_⟩
  · have hdetA : A.det = 1 := hA
    have hdetB : B.det = 1 := hB
    show (A * B).det = 1
    rw [Matrix.det_mul, hdetA, hdetB, one_mul]
  · have hdetA : A.det = 1 := hA
    show (A⁻¹).det = 1
    rw [Matrix.det_nonsing_inv, hdetA]
    simp
theorem compactGaugeGroup_isUnimodular :
    IsUnimodularMatrixGroup PeriodicLattice.compactGaugeGroup := by
  refine ⟨fun A hA => (Matrix.mem_specialUnitaryGroup_iff.mp hA).2, fun A hA B hB => ?_,
    fun A hA => ?_⟩
  · exact (Matrix.specialUnitaryGroup (Fin 2) ℂ).mul_mem hA hB
  · obtain ⟨hunit, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hA
    have hinv : A⁻¹ = star A := Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hunit)
    rw [hinv]
    refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Unitary.star_mem hunit, ?_⟩
    rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hdet, star_one]
theorem sandwich_mem {G : Set Matrices.ComplexMatrix2} (hG : IsUnimodularMatrixGroup G)
    {g V h : Matrices.ComplexMatrix2} (hg : g ∈ G) (hV : V ∈ G) (hh : h ∈ G) :
    g * V * h⁻¹ ∈ G :=
  hG.2.1 _ (hG.2.1 _ hg _ hV) _ (hG.2.2 _ hh)
theorem sandwich_inv {g V h : Matrices.ComplexMatrix2} (hh : h.det = 1) :
    h * V⁻¹ * g⁻¹ = (g * V * h⁻¹)⁻¹ := by
  have hh' : h⁻¹⁻¹ = h := Matrix.nonsing_inv_nonsing_inv h (by rw [hh]; exact isUnit_one)
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hh', mul_assoc]
section Neighbours
variable {X : Type} [AddCommGroup X]
theorem areNeighbours_iff_exists_axis {e : Fin 4 → X} {x y : X} :
    AreNeighbours e x y ↔ ∃ μ, y - x = e μ ∨ y - x = -e μ := by
  constructor
  · rintro ⟨σ, μ, h⟩
    rcases Int.units_eq_one_or σ with rfl | rfl
    · exact ⟨μ, Or.inl (by simpa [IsSignedAxisStep] using h)⟩
    · exact ⟨μ, Or.inr (by simpa [IsSignedAxisStep] using h)⟩
  · rintro ⟨μ, h | h⟩
    · exact ⟨1, μ, by simpa [IsSignedAxisStep] using h⟩
    · exact ⟨-1, μ, by simpa [IsSignedAxisStep] using h⟩
theorem areNeighbours_of_map_areNeighbours [Nonempty X] {d : X → X → ℝ} {Λ : AddSubgroup X}
    {a : ℝ} {e : Fin 4 → X} (hN : NeighboursAtSpacing d Λ a e) {s : X → X}
    (hs : ∀ p q, d (s p) (s q) = d p q) (hsurj : s '' (Λ : Set X) = Λ) {y y' x x' : X}
    (hy : y ∈ Λ) (hy' : y' ∈ Λ) (hx : s y = x) (hx' : s y' = x')
    (hxx : ∃ μ, x' - x = e μ ∨ x' - x = -e μ) :
    ∃ μ, y' - y = e μ ∨ y' - y = -e μ := by
  obtain ⟨hinj, -, hpre⟩ := hN.2 s hs hsurj
  have hxΛ : x ∈ Λ := by
    have hmem : x ∈ s '' (Λ : Set X) := ⟨y, hy, hx⟩
    rw [hsurj] at hmem
    exact hmem
  have hx'Λ : x' ∈ Λ := by
    have hmem : x' ∈ s '' (Λ : Set X) := ⟨y', hy', hx'⟩
    rw [hsurj] at hmem
    exact hmem
  have hback : ∀ {z w : X}, z ∈ Λ → s z = w → Function.invFunOn s (Λ : Set X) w = z := by
    intro z w hz hw
    have hex : ∃ t ∈ (Λ : Set X), s t = w := ⟨z, hz, hw⟩
    exact hinj (Function.invFunOn_mem hex) hz ((Function.invFunOn_eq hex).trans hw.symm)
  have hnb := hpre x hxΛ x' hx'Λ (areNeighbours_iff_exists_axis.mpr hxx)
  rw [hback hy hx, hback hy' hx'] at hnb
  exact areNeighbours_iff_exists_axis.mp hnb
end Neighbours
theorem torus_neighboursAtSpacing (hQ : TorusAndSpaceLatticeProperties) {L n k j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    NeighboursAtSpacing (torusDist L n) (PeriodicLattice.sublattice L n (refinementIndex k j))
      (PeriodicLattice.meshSize L (refinementIndex k j)) (torusAxisSteps L n k j) :=
  (hQ L hL n j k hn hj).2.2.2.2.2.2.2.1
theorem space_neighboursAtSpacing (hQ : TorusAndSpaceLatticeProperties) {L k j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) :
    NeighboursAtSpacing spaceDist (InfiniteLattice.latticeSubgroup (meshAt L k j))
      (meshAt L k j) (spaceAxisSteps (meshAt L k j)) := by
  have hsp := (hQ L hL 1 j k le_rfl hj).2.2.2.2.2.2.2.2
  have hmesh : PeriodicLattice.meshSize L (refinementIndex k j) = meshAt L k j :=
    meshSize_levelDepth L k j
  rwa [hmesh] at hsp
section Periodic
variable {L n k j : ℕ} {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
theorem gaugeTransform_isGaugeField {m : ℕ} {i : ℤ} {G : Set Matrices.ComplexMatrix2}
    (hG : IsUnimodularMatrixGroup G) {U : PeriodicLattice.Bond L m i → Matrices.ComplexMatrix2}
    {g : PeriodicLattice.Site L m i → Matrices.ComplexMatrix2}
    (hU : PeriodicLattice.IsGaugeField G univ U) (hg : PeriodicLattice.IsGaugeMap G g) :
    PeriodicLattice.IsGaugeField G univ (PeriodicLattice.gaugeTransform g U) := by
  refine ⟨fun b _ => sandwich_mem hG (hg _) (hU.1 b (mem_univ b)) (hg _), fun b _ => ?_⟩
  show g b.target * U b.opposite * (g b.source)⁻¹ = (g b.source * U b * (g b.target)⁻¹)⁻¹
  rw [hU.2 b (mem_univ b)]
  exact sandwich_inv (hG.1 _ (hg _))
theorem apply_vertexPreimage (hsurj : MapsSublatticeOnto k j f) (x : Vertex L n k j) :
    f (vertexPreimage (k := k) (j := j) f x) = x := by apply _root_.YangMills.Construction.Tower.ScalingInvariance.vertexPreimage_spec <;> assumption
theorem exists_edge_between_vertexPreimages
    (hN : NeighboursAtSpacing (torusDist L n) (PeriodicLattice.sublattice L n (refinementIndex k j))
      (PeriodicLattice.meshSize L (refinementIndex k j)) (torusAxisSteps L n k j))
    (hf : IsDistancePreserving f) (hsurj : MapsSublatticeOnto k j f) (b : Edge L n k j) :
    ∃ c : Edge L n k j, c.source = vertexPreimage (k := k) (j := j) f b.source ∧
      c.target = vertexPreimage (k := k) (j := j) f b.target := by
  have hxx : ∃ μ, (b.target : PeriodicLattice.FourTorus L n) - b.source =
        torusAxisSteps L n k j μ ∨
      (b.target : PeriodicLattice.FourTorus L n) - b.source = -torusAxisSteps L n k j μ := by
    obtain ⟨μ, h | h⟩ := b.isNeighbour
    · exact ⟨μ, Or.inl (congrArg Subtype.val h)⟩
    · exact ⟨μ, Or.inr (congrArg Subtype.val h)⟩
  obtain ⟨μ, h⟩ := areNeighbours_of_map_areNeighbours hN (s := f) hf hsurj
    (vertexPreimage (k := k) (j := j) f b.source).2 (vertexPreimage (k := k) (j := j) f b.target).2
    (apply_vertexPreimage hsurj b.source) (apply_vertexPreimage hsurj b.target) hxx
  refine ⟨⟨_, _, μ, ?_⟩, rfl, rfl⟩
  rcases h with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)
theorem edgePreimage_endpoints
    (hN : NeighboursAtSpacing (torusDist L n) (PeriodicLattice.sublattice L n (refinementIndex k j))
      (PeriodicLattice.meshSize L (refinementIndex k j)) (torusAxisSteps L n k j))
    (hf : IsDistancePreserving f) (hsurj : MapsSublatticeOnto k j f) (b : Edge L n k j) :
    (edgePreimage (k := k) (j := j) f b).source = vertexPreimage (k := k) (j := j) f b.source ∧
      (edgePreimage (k := k) (j := j) f b).target = vertexPreimage (k := k) (j := j) f b.target :=
  Classical.epsilon_spec (p := fun c : Edge L n k j =>
    c.source = vertexPreimage (k := k) (j := j) f b.source ∧
      c.target = vertexPreimage (k := k) (j := j) f b.target)
    (exists_edge_between_vertexPreimages hN hf hsurj b)
theorem pushField_isGaugeField {G : Set Matrices.ComplexMatrix2}
    (hN : NeighboursAtSpacing (torusDist L n) (PeriodicLattice.sublattice L n (refinementIndex k j))
      (PeriodicLattice.meshSize L (refinementIndex k j)) (torusAxisSteps L n k j))
    (hf : IsDistancePreserving f) (hsurj : MapsSublatticeOnto k j f)
    {U : Edge L n k j → Matrices.ComplexMatrix2}
    (hU : PeriodicLattice.IsGaugeField G univ U) :
    PeriodicLattice.IsGaugeField G univ (pushField (k := k) (j := j) f U) := by
  refine ⟨fun b _ => hU.1 _ (mem_univ _), fun b _ => ?_⟩
  have hopp : edgePreimage (k := k) (j := j) f b.opposite =
      (edgePreimage (k := k) (j := j) f b).opposite := by
    apply PeriodicLattice.Bond.ext
    · exact (edgePreimage_endpoints hN hf hsurj b.opposite).1.trans
        (edgePreimage_endpoints hN hf hsurj b).2.symm
    · exact (edgePreimage_endpoints hN hf hsurj b.opposite).2.trans
        (edgePreimage_endpoints hN hf hsurj b).1.symm
  show U (edgePreimage (k := k) (j := j) f b.opposite) =
    (U (edgePreimage (k := k) (j := j) f b))⁻¹
  rw [hopp]
  exact hU.2 _ (mem_univ _)
end Periodic
section Unbounded
open InfiniteLattice (AmbientSpace)
variable {a : ℝ} {f : AmbientSpace → AmbientSpace}
theorem fullSpace_gaugeAct_isFieldIn {G : Set Matrices.ComplexMatrix2}
    (hG : IsUnimodularMatrixGroup G)
    {U : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    {g : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2}
    (hU : FullSpace.IsFieldIn G U) (hg : ∀ x, g x ∈ G) :
    FullSpace.IsFieldIn G (FullSpace.gaugeAct g U) := by
  refine ⟨fun b => sandwich_mem hG (hg _) (hU.1 b) (hg _), fun b => ?_⟩
  show g b.terminal * U b.opposite * (g b.initial)⁻¹ = (g b.initial * U b * (g b.terminal)⁻¹)⁻¹
  rw [hU.2 b]
  exact sandwich_inv (hG.1 _ (hg _))
theorem fullSpace_apply_vertexPreimage (hsurj : FullSpace.MapsSublatticeOnto a f)
    (x : InfiniteLattice.LatticePoint a) :
    f (FullSpace.vertexPreimage f x) = x := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingInvariance.vertexPreimage_spec <;> assumption
theorem fullSpace_exists_link_between_vertexPreimages
    (hN : NeighboursAtSpacing spaceDist (InfiniteLattice.latticeSubgroup a) a (spaceAxisSteps a))
    (hf : FullSpace.IsDistancePreserving f) (hsurj : FullSpace.MapsSublatticeOnto a f)
    (b : InfiniteLattice.Link a) :
    ∃ c : InfiniteLattice.Link a, c.initial = FullSpace.vertexPreimage f b.initial ∧
      c.terminal = FullSpace.vertexPreimage f b.terminal := by
  have hxx : ∃ μ, (b.terminal : AmbientSpace) - b.initial = spaceAxisSteps a μ ∨
      (b.terminal : AmbientSpace) - b.initial = -spaceAxisSteps a μ := by
    obtain ⟨μ, h | h⟩ := b.isAdjacent
    · exact ⟨μ, Or.inl (congrArg Subtype.val h)⟩
    · exact ⟨μ, Or.inr (congrArg Subtype.val h)⟩
  obtain ⟨μ, h⟩ := areNeighbours_of_map_areNeighbours hN (s := f) hf hsurj
    (FullSpace.vertexPreimage f b.initial).2 (FullSpace.vertexPreimage f b.terminal).2
    (fullSpace_apply_vertexPreimage hsurj b.initial)
    (fullSpace_apply_vertexPreimage hsurj b.terminal) hxx
  refine ⟨⟨_, _, μ, ?_⟩, rfl, rfl⟩
  rcases h with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)
theorem fullSpace_edgePreimage_endpoints
    (hN : NeighboursAtSpacing spaceDist (InfiniteLattice.latticeSubgroup a) a (spaceAxisSteps a))
    (hf : FullSpace.IsDistancePreserving f) (hsurj : FullSpace.MapsSublatticeOnto a f)
    (b : InfiniteLattice.Link a) :
    (FullSpace.edgePreimage f b).initial = FullSpace.vertexPreimage f b.initial ∧
      (FullSpace.edgePreimage f b).terminal = FullSpace.vertexPreimage f b.terminal :=
  Classical.epsilon_spec (p := fun c : InfiniteLattice.Link a =>
    c.initial = FullSpace.vertexPreimage f b.initial ∧
      c.terminal = FullSpace.vertexPreimage f b.terminal)
    (fullSpace_exists_link_between_vertexPreimages hN hf hsurj b)
theorem fullSpace_pushField_isFieldIn {G : Set Matrices.ComplexMatrix2}
    (hN : NeighboursAtSpacing spaceDist (InfiniteLattice.latticeSubgroup a) a (spaceAxisSteps a))
    (hf : FullSpace.IsDistancePreserving f) (hsurj : FullSpace.MapsSublatticeOnto a f)
    {U : InfiniteLattice.Link a → Matrices.ComplexMatrix2} (hU : FullSpace.IsFieldIn G U) :
    FullSpace.IsFieldIn G (FullSpace.pushField f U) := by
  refine ⟨fun b => hU.1 _, fun b => ?_⟩
  have hopp : FullSpace.edgePreimage f b.opposite = (FullSpace.edgePreimage f b).opposite := by
    apply InfiniteLattice.Link.ext
    · exact (fullSpace_edgePreimage_endpoints hN hf hsurj b.opposite).1.trans
        (fullSpace_edgePreimage_endpoints hN hf hsurj b).2.symm
    · exact (fullSpace_edgePreimage_endpoints hN hf hsurj b.opposite).2.trans
        (fullSpace_edgePreimage_endpoints hN hf hsurj b).1.symm
  show U (FullSpace.edgePreimage f b.opposite) = (U (FullSpace.edgePreimage f b))⁻¹
  rw [hopp]
  exact hU.2 _
end Unbounded
theorem statement_holds (hQ : TorusAndSpaceLatticeProperties) : statement := by
  intro L k j hL hj
  refine ⟨fun n hn => ?_, ?_⟩
  · intro U g f hU hg hf hsurj
    have hN := torus_neighboursAtSpacing hQ hL hn hj
    exact ⟨gaugeTransform_isGaugeField complexGaugeGroup_isUnimodular hU hg,
      pushField_isGaugeField hN hf hsurj hU,
      fun hr hv => gaugeTransform_isGaugeField compactGaugeGroup_isUnimodular hr hv,
      fun hr => pushField_isGaugeField hN hf hsurj hr⟩
  · intro U g f hU hg hf hsurj
    have hN := space_neighboursAtSpacing hQ hL hj
    exact ⟨fullSpace_gaugeAct_isFieldIn complexGaugeGroup_isUnimodular hU hg,
      fullSpace_pushField_isFieldIn hN hf hsurj hU,
      fun hr hv => fullSpace_gaugeAct_isFieldIn compactGaugeGroup_isUnimodular hr hv,
      fun hr => fullSpace_pushField_isFieldIn hN hf hsurj hr⟩
end Tower.GaugeAndSymmetryImages
end YangMills.Construction

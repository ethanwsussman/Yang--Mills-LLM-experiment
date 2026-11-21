import YangMills.Construction.Towers.HessianOfTheWilsonActionProof
import YangMills.Construction.Towers.TranslatedConfigurationOfAField
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ShiftedFieldGauge
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.BackgroundJets (gaugeFieldOfForm)
variable {L k : ℕ}
theorem castVec_mem (hL : 0 < L) (m : Fin 4 → ℤ) :
    castVec m ∈ InfiniteLattice.latticeSubgroup (meshAt L k 0) := by
  refine ⟨fun μ => m μ * (L : ℤ) ^ k, fun μ => ?_⟩
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [castVec, meshAt, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [Nat.cast_zero, zero_sub, zpow_neg, zpow_natCast, mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero k hL'), mul_one]
theorem coe_vertexImage (hL : 0 < L) (m : Fin 4 → ℤ) (x : Vertex L k 0) :
    ((vertexImage (intShift m) x : Vertex L k 0) : AmbientSpace) = (x : AmbientSpace) + castVec m := by
  have hex : ∃ x' : Vertex L k 0, (x' : AmbientSpace) = intShift m x :=
    ⟨⟨(x : AmbientSpace) + castVec m, add_mem x.2 (castVec_mem hL m)⟩, rfl⟩
  exact Classical.epsilon_spec hex
theorem vertexImage_sub (hL : 0 < L) (m : Fin 4 → ℤ) (x y : Vertex L k 0) :
    (vertexImage (intShift m) x - vertexImage (intShift m) y : Vertex L k 0) = x - y := by
  apply Subtype.ext
  simp only [AddSubgroup.coe_sub, coe_vertexImage hL]
  abel
theorem edgeImage_ends (hL : 0 < L) (m : Fin 4 → ℤ) (b : Edge L k 0) :
    (edgeImage (intShift m) b).initial = vertexImage (intShift m) b.initial ∧
      (edgeImage (intShift m) b).terminal = vertexImage (intShift m) b.terminal := by
  have hex : ∃ b' : Edge L k 0, b'.initial = vertexImage (intShift m) b.initial ∧
      b'.terminal = vertexImage (intShift m) b.terminal :=
    ⟨⟨vertexImage (intShift m) b.initial, vertexImage (intShift m) b.terminal, by
      rw [vertexImage_sub hL]
      exact b.isAdjacent⟩, rfl, rfl⟩
  exact Classical.epsilon_spec hex
theorem edgeImage_sub (hL : 0 < L) (m : Fin 4 → ℤ) (b : Edge L k 0) :
    (edgeImage (intShift m) b).terminal - (edgeImage (intShift m) b).initial =
      b.terminal - b.initial := by
  rw [(edgeImage_ends hL m b).1, (edgeImage_ends hL m b).2, vertexImage_sub hL]
theorem edgeImage_isPositivelyOriented_iff (hL : 0 < L) (m : Fin 4 → ℤ) (b : Edge L k 0) :
    (edgeImage (intShift m) b).IsPositivelyOriented ↔ b.IsPositivelyOriented := by
  simp only [InfiniteLattice.Link.IsPositivelyOriented, edgeImage_sub hL]
theorem edgeImage_opposite (hL : 0 < L) (m : Fin 4 → ℤ) (b : Edge L k 0) :
    (edgeImage (intShift m) b).opposite = edgeImage (intShift m) b.opposite :=
  InfiniteLattice.Link.ext
    (by
      show (edgeImage (intShift m) b).terminal = (edgeImage (intShift m) b.opposite).initial
      rw [(edgeImage_ends hL m b).2, (edgeImage_ends hL m b.opposite).1]
      rfl)
    (by
      show (edgeImage (intShift m) b).initial = (edgeImage (intShift m) b.opposite).terminal
      rw [(edgeImage_ends hL m b).1, (edgeImage_ends hL m b.opposite).2]
      rfl)
theorem opposite_isPositivelyOriented {b : Edge L k 0} (hb : ¬b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.WilsonHessianProof.opposite_isPositivelyOriented_of_not <;> assumption
theorem shiftEdge_val (hL : 0 < L) (m : Fin 4 → ℤ) (p : PeriodicOperators.PosEdge L k 0) :
    (shiftEdge m p).1 = edgeImage (intShift m) p.1 :=
  Classical.epsilon_spec (p := fun b' : PeriodicOperators.PosEdge L k 0 =>
    b'.1 = edgeImage (intShift m) p.1)
    ⟨⟨_, (edgeImage_isPositivelyOriented_iff hL m p.1).2 p.2⟩, rfl⟩
theorem vertexImage_neg_cancel (hL : 0 < L) (m : Fin 4 → ℤ) (x : Vertex L k 0) :
    (vertexImage (intShift (-m)) (vertexImage (intShift m) x) : Vertex L k 0) = x := by
  apply Subtype.ext
  rw [coe_vertexImage hL, coe_vertexImage hL]
  funext μ
  simp [castVec]
theorem shiftEdge_neg_image (hL : 0 < L) (m : Fin 4 → ℤ) {b : Edge L k 0}
    (hb : b.IsPositivelyOriented) (hb' : (edgeImage (intShift m) b).IsPositivelyOriented) :
    shiftEdge (-m) (⟨edgeImage (intShift m) b, hb'⟩ : PeriodicOperators.PosEdge L k 0) =
      ⟨b, hb⟩ := by
  apply Subtype.ext
  rw [shiftEdge_val hL]
  refine InfiniteLattice.Link.ext ?_ ?_
  · rw [(edgeImage_ends hL _ _).1]
    show vertexImage _ (edgeImage (intShift m) b).initial = _
    rw [(edgeImage_ends hL _ _).1, vertexImage_neg_cancel hL]
  · rw [(edgeImage_ends hL _ _).2]
    show vertexImage _ (edgeImage (intShift m) b).terminal = _
    rw [(edgeImage_ends hL _ _).2, vertexImage_neg_cancel hL]
theorem ofCoeffs_positive (f : (remainderIndex L k).Carrier → ℂ) (p : PeriodicOperators.PosEdge L k 0) :
    (edgePauliCoordinates L k 0).ofCoeffs f p.1 = ofPauliCoeffs f p := by
  unfold edgePauliCoordinates
  dsimp only
  rw [extendOddly, if_pos p.2]
  exact dif_pos p.2
theorem ofCoeffs_at_image (hL : 0 < L) (m : Fin 4 → ℤ) (ζ : (remainderIndex L k).Carrier → ℂ)
    {b : Edge L k 0} (hb : b.IsPositivelyOriented) :
    (edgePauliCoordinates L k 0).ofCoeffs (shiftField (remainderIndex L k) m ζ)
        (edgeImage (intShift m) b) = (edgePauliCoordinates L k 0).ofCoeffs ζ b := by
  have hb' := (edgeImage_isPositivelyOriented_iff hL m b).2 hb
  rw [ofCoeffs_positive _ ⟨_, hb'⟩, ofCoeffs_positive _ ⟨b, hb⟩]
  refine Finset.sum_congr rfl fun a _ => ?_
  show ζ (a, shiftEdge (-m) ⟨edgeImage (intShift m) b, hb'⟩) • _ = ζ (a, ⟨b, hb⟩) • _
  rw [shiftEdge_neg_image hL m hb hb']
theorem shiftCommutes_holds : ShiftCommutes := by
  intro L hL k m ζ b
  have hL₀ : 0 < L := by have := hL.2; omega
  show expTwist _ 1 _ = expTwist _ 1 _
  by_cases hb : b.IsPositivelyOriented
  · have hb' := (edgeImage_isPositivelyOriented_iff hL₀ m b).2 hb
    simp only [expTwist, if_pos hb, if_pos hb', ofCoeffs_at_image hL₀ m ζ hb, Pi.one_apply]
  · have hb' : ¬(edgeImage (intShift m) b).IsPositivelyOriented :=
      fun h => hb ((edgeImage_isPositivelyOriented_iff hL₀ m b).1 h)
    simp only [expTwist, if_neg hb, if_neg hb', edgeImage_opposite hL₀ m b,
      ofCoeffs_at_image hL₀ m ζ (opposite_isPositivelyOriented hb)]
    rfl
end YangMills.Construction.Tower.FullSpace.ShiftedFieldGauge
end

import YangMills.Construction.Lattice.EndPointsAndOrientationOfABond
import YangMills.Construction.Lattice.TwoCasesOfTheLiftOfOrder
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.OrderLift
variable {L m K : ℕ}
private theorem isLevelLift_unique {j : ℕ} (hL : (L : ℝ) ≠ 0) {x y : FourTorus L m}
    {w : Fin 4 → ℝ} (hx : IsLevelLift L m K j x w) (hy : IsLevelLift L m K j y w) : x = y := by
  obtain ⟨v, hv, hw⟩ := hx
  obtain ⟨v', hv', hw'⟩ := hy
  funext μ
  have h : (L : ℝ) ^ levelDepth K j * v μ = (L : ℝ) ^ levelDepth K j * v' μ :=
    (hw μ).symm.trans (hw' μ)
  have hne : (L : ℝ) ^ levelDepth K j ≠ 0 := zpow_ne_zero _ hL
  rw [← hv μ, ← hv' μ, mul_left_cancel₀ hne h]
private theorem shiftBy_zero {j : ℕ} (hL : (L : ℝ) ≠ 0) (x : FourTorus L m) :
    shiftBy L m K j x 0 = x := by
  have hc : ∀ μ, ∃ t : ℝ, (t : AddCircle (torusSide L m)) = x μ :=
    fun μ => QuotientAddGroup.mk_surjective (x μ)
  choose v hv using hc
  have hex : ∃ w, IsLevelLift L m K j x w :=
    ⟨fun μ => toLevelUnits L K j (v μ), v, hv, fun _ => rfl⟩
  have hw := Classical.epsilon_spec hex
  unfold shiftBy torusClassOf
  rw [add_zero]
  exact isLevelLift_unique hL
    (Classical.epsilon_spec
      (p := fun y => IsLevelLift L m K j y (Classical.epsilon (IsLevelLift L m K j x)))
      ⟨x, hw⟩) hw
section Centres
variable (hB : CoarseCentreProperties) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hm : 0 < m) (hK : 0 < K)
include hB hL hm hK
private theorem mem_blockAtLevel_iff {j k : ℕ} (hjk : j ≤ k) (hkK : k ≤ K)
    (x : SiteAtLevel L m K j) (y : SiteAtLevel L m K k) :
    (x : FourTorus L m) ∈ blockAtLevel j y ↔ coarseCentre j k x = y := by
  rw [((hB L m K hL hm hK j k hjk hkK).2.1 y).1]
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨x', hx', hc⟩
    rwa [Subtype.ext hx'] at hc
  · intro hc
    exact ⟨x, rfl, hc⟩
private theorem ends_of_covers {j k : ℕ} (hjk : j ≤ k) (hkK : k ≤ K) {b : BondAtLevel L m K j}
    {c : BondAtLevel L m K k} (h : CoversBond c b) :
    c.source = coarseCentre j k b.source ∧ c.target = coarseCentre j k b.target :=
  ⟨((mem_blockAtLevel_iff hB hL hm hK hjk hkK _ _).mp h.1).symm,
    ((mem_blockAtLevel_iff hB hL hm hK hjk hkK _ _).mp h.2).symm⟩
private theorem covered_unique {j k : ℕ} (hjk : j ≤ k) (hkK : k ≤ K) {b : BondAtLevel L m K j}
    {c c' : BondAtLevel L m K k} (h : CoversBond c b) (h' : CoversBond c' b) : c = c' := by
  obtain ⟨e₁, e₂⟩ := ends_of_covers hB hL hm hK hjk hkK h
  obtain ⟨e₁', e₂'⟩ := ends_of_covers hB hL hm hK hjk hkK h'
  exact Bond.ext (e₁.trans e₁'.symm) (e₂.trans e₂'.symm)
private theorem coarseCentre_same_level {k : ℕ} (hkK : k ≤ K) (x : SiteAtLevel L m K k) :
    coarseCentre k k x = x := by
  have hL' : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hL.2; omega)
  have hu := ((hB L m K hL hm hK k k le_rfl hkK).1 x).1
  have hz : (fun μ => (((0 : Fin 4 → ℤ) μ : ℤ) : ℝ)) = 0 := by
    funext μ
    simp
  have h0 : IsBlockDisplacement k k x x 0 := by
    constructor
    · rw [hz]
      simp [supNormVec, halfWidth]
    · rw [hz, shiftBy_zero hL']
  obtain ⟨r, hr⟩ : ∃ r, IsBlockDisplacement k k x (coarseCentre k k x) r :=
    Classical.epsilon_spec (p := fun y => ∃ r, IsBlockDisplacement k k x y r) ⟨x, 0, h0⟩
  exact congrArg Prod.fst (hu.unique (y₁ := (coarseCentre k k x, r)) (y₂ := (x, 0)) hr h0)
private theorem blockAtLevel_same_level {k : ℕ} (hkK : k ≤ K) (x : SiteAtLevel L m K k) :
    blockAtLevel k x = {(x : FourTorus L m)} := by
  ext z
  rw [((hB L m K hL hm hK k k le_rfl hkK).2.1 x).1]
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨x', rfl, hc⟩
    rw [coarseCentre_same_level hB hL hm hK hkK] at hc
    rw [hc]
  · rintro rfl
    exact ⟨x, rfl, coarseCentre_same_level hB hL hm hK hkK x⟩
end Centres
private theorem source_ne_target (hE : BondEndpointsOrientation.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K) {k : ℕ}
    (hkK : k ≤ K) (c : BondAtLevel L m K k) : c.source ≠ c.target :=
  ((hE ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩ k hkK).2.2.2 c).2.1
section TwoCases
variable (hB : CoarseCentreProperties) (hE : BondEndpointsOrientation.Statement)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K)
include hB hE hL hm hK
private theorem not_covers_of_inside {j k : ℕ} (hjk : j ≤ k) (hkK : k ≤ K)
    {b : BondAtLevel L m K j} (h : IsInsideSomeBlock k b) (c : BondAtLevel L m K k) :
    ¬CoversBond c b := by
  intro hc
  obtain ⟨y, ht, hh⟩ := h
  obtain ⟨e₁, e₂⟩ := ends_of_covers hB hL hm hK hjk hkK hc
  apply source_ne_target hE hL hm hK hkK c
  rw [e₁, e₂, (mem_blockAtLevel_iff hB hL hm hK hjk hkK _ _).mp ht,
    (mem_blockAtLevel_iff hB hL hm hK hjk hkK _ _).mp hh]
private theorem orderLift_of_covers {j k : ℕ} (hjk : j ≤ k) (hkK : k ≤ K)
    {b : BondAtLevel L m K j} {c : BondAtLevel L m K k} (hc : CoversBond c b)
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) : orderLift j V b = V c := by
  have hnot : ¬EndsInOneBlock k b := fun h => not_covers_of_inside hB hE hL hm hK hjk hkK h c hc
  have hu : CoversBond (coveredBond k b) b :=
    Classical.epsilon_spec (p := fun c' => CoversBond c' b) ⟨c, hc⟩
  have he : coveredBond k b = c := covered_unique hB hL hm hK hjk hkK hu hc
  show liftToFinerLevel j V b = V c
  unfold liftToFinerLevel
  rw [if_neg hnot, he]
end TwoCases
private theorem orderLift_of_inside {j k : ℕ} {b : BondAtLevel L m K j}
    (h : IsInsideSomeBlock k b) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    orderLift j V b = 1 := by
  have h' : EndsInOneBlock k b := h
  show liftToFinerLevel j V b = 1
  unfold liftToFinerLevel
  rw [if_pos h']
theorem orderLiftCases_of_centres (hB : CoarseCentreProperties)
    (hE : BondEndpointsOrientation.Statement) : OrderLiftCases := by
  intro L m K hL hm hK
  refine ⟨fun j k hjk hkK => ?_, fun k hkK => ?_⟩
  · refine ⟨fun b c h => ends_of_covers hB hL hm hK hjk hkK h,
      fun b c c' h h' => covered_unique hB hL hm hK hjk hkK h h',
      fun b h c => not_covers_of_inside hB hE hL hm hK hjk hkK h c,
      fun 𝒞 V hC hV b hb => ?_⟩
    have hor : IsInsideSomeBlock k b ∨ ∃ c ∈ 𝒞, CoversBond c b := hb
    refine ⟨fun ⟨h, c, _, hc⟩ => not_covers_of_inside hB hE hL hm hK hjk hkK h c hc, hor, ?_,
      fun h => orderLift_of_inside h V,
      fun c _ hc => orderLift_of_covers hB hE hL hm hK hjk hkK hc V, ?_⟩
    · rintro ⟨c, hc, hl⟩
      exact ⟨c, ⟨hc, hl⟩, fun c' h' => covered_unique hB hL hm hK hjk hkK h'.2 hl⟩
    · rcases hor with h | ⟨c, hc, hl⟩
      · rw [orderLift_of_inside h V]
        exact Matrix.det_one
      · rw [orderLift_of_covers hB hE hL hm hK hjk hkK hl V]
        exact hV.1 c hc
  · have hblock := blockAtLevel_same_level (L := L) (m := m) (K := K) hB hL hm hK hkK
    have hnot : ∀ b : BondAtLevel L m K k, ¬IsInsideSomeBlock k b := by
      rintro b ⟨y, ht, hh⟩
      rw [hblock] at ht hh
      exact source_ne_target hE hL hm hK hkK b
        (Subtype.ext ((mem_singleton_iff.mp ht).trans (mem_singleton_iff.mp hh).symm))
    have hover : ∀ b c : BondAtLevel L m K k, CoversBond c b ↔ c = b := by
      intro b c
      constructor
      · rintro ⟨ht, hh⟩
        rw [hblock] at ht hh
        exact Bond.ext (Subtype.ext (mem_singleton_iff.mp ht)).symm
          (Subtype.ext (mem_singleton_iff.mp hh)).symm
      · rintro rfl
        exact ⟨by rw [hblock]; rfl, by rw [hblock]; rfl⟩
    refine ⟨fun x => ⟨coarseCentre_same_level hB hL hm hK hkK x, hblock x⟩, hnot, hover,
      fun 𝒞 V _ _ => ⟨?_, fun b _ =>
        orderLift_of_covers hB hE hL hm hK le_rfl hkK ((hover b b).mpr rfl) V⟩⟩
    ext b
    constructor
    · rintro (h | ⟨c, hc, hl⟩)
      · exact (hnot b h).elim
      · rwa [(hover b c).mp hl] at hc
    · intro hb
      exact Or.inr ⟨b, hb, (hover b b).mpr rfl⟩
end YangMills.Construction.PeriodicLattice.OrderLift

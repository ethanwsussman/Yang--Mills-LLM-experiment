import YangMills.Construction.TorusOrFourSpace.InducedMapsOfAdicIsometries
import YangMills.Construction.TorusOrFourSpace.ThreeKindsOfMapsOfSeveralPointsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.AdicInducedMaps
open PeriodicLattice (SignedFrame)
open WellPosedness (QuotMapSurjectiveHomWithKernel)
variable (D : Params) (E : Kind)
private theorem mem_latticeSubgroup_iff {a : ℝ} {x : Fin 4 → ℝ} :
    x ∈ InfiniteLattice.latticeSubgroup a ↔ ∃ n : Fin 4 → ℤ, ∀ μ, x μ = (n μ : ℝ) * a := Iff.rfl
private theorem meshSize_eq_pow_mul {j j' : ℕ} (h : j ≤ j') :
    PeriodicLattice.meshSize D.L (j : ℤ) =
      ((D.L ^ (j' - j) : ℕ) : ℝ) * PeriodicLattice.meshSize D.L (j' : ℤ) := by
  have hL : (D.L : ℝ) ≠ 0 := by
    have hadm := D.isAdmissible.2
    exact Nat.cast_ne_zero.2 (by omega)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [PeriodicLattice.meshSize, Nat.add_sub_cancel_left, Nat.cast_pow]
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_add]
  field_simp
private theorem adicLat_mono : AdicLatMono D := by
  rintro j j' h x ⟨n, hn⟩
  refine mem_latticeSubgroup_iff.2 ⟨fun μ => n μ * ((D.L ^ (j' - j) : ℕ) : ℤ), fun μ => ?_⟩
  rw [hn μ, meshSize_eq_pow_mul D h]
  push_cast
  ring
private theorem exists_mem_adicLat {a : Fin 4 → ℝ} (ha : a ∈ adicPoints4 D.L) :
    ∃ j₀ : ℕ, a ∈ adicLat D j₀ := by
  have h : ∀ μ, ∃ k : ℕ, ∃ n : ℤ, a μ = (n : ℝ) * PeriodicLattice.meshSize D.L (k : ℤ) :=
    fun μ => (PeriodicLattice.mem_adicGridPoints_iff D.L (a μ)).1 (ha μ)
  choose k n hkn using h
  refine ⟨Finset.univ.sup k, mem_latticeSubgroup_iff.2
    ⟨fun μ => n μ * ((D.L ^ (Finset.univ.sup k - k μ) : ℕ) : ℤ), fun μ => ?_⟩⟩
  rw [hkn μ, meshSize_eq_pow_mul D (Finset.le_sup (f := k) (Finset.mem_univ μ))]
  push_cast
  ring
private theorem adicPoints_eq_iUnion : AdicPointsEqIUnion D := by
  ext a
  simp only [Set.mem_iUnion]
  constructor
  · intro ha
    obtain ⟨j, hj⟩ := exists_mem_adicLat D ha
    exact ⟨j, hj⟩
  · rintro ⟨j, n, hn⟩ μ
    exact (PeriodicLattice.mem_adicGridPoints_iff D.L (a μ)).2 ⟨j, n μ, hn μ⟩
private theorem eventually_mem_adicLat : EventuallyMemAdicLat D := by
  intro a ha
  obtain ⟨j₀, hj₀⟩ := exists_mem_adicLat D ha
  exact ⟨j₀, fun j hj => adicLat_mono D j₀ j hj hj₀⟩
private theorem actOnVector_add (w : SignedFrame) (x k : Fin 4 → ℝ) :
    w.actOnVector (x + k) = w.actOnVector x + w.actOnVector k := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.actOnVector_add <;> assumption
private theorem actOnVector_mem_periodGroup (w : SignedFrame) {k : Fin 4 → ℝ}
    (hk : k ∈ E.periodGroup D) : w.actOnVector k ∈ E.periodGroup D := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.TupleMapFacts.actOnVector_mem_periodGroup <;> assumption
private theorem frame_moves_periods : FrameMovesPeriods D E := by
  intro a _ w x k hk
  refine ⟨?_, actOnVector_mem_periodGroup D E w hk⟩
  simp only [shiftedFrameMap, Function.comp, translateR4, actOnVector_add]
  exact add_right_comm _ _ _
private theorem quot_const_on_cosets (hQ : QuotMapSurjectiveHomWithKernel D E) :
    QuotConstOnCosets D E := by
  intro a ha w x k hk
  obtain ⟨hmove, hwk⟩ := frame_moves_periods D E a ha w x k hk
  rw [hmove, hQ.1, (hQ.2.2 _).2 hwk, add_zero]
private theorem quotMap_shiftedFrameMap_eq (hQ : QuotMapSurjectiveHomWithKernel D E)
    {a : Fin 4 → ℝ} (ha : a ∈ adicPoints4 D.L) (w : SignedFrame) {x x' : Fin 4 → ℝ}
    (hx : E.quotMap D x' = E.quotMap D x) :
    E.quotMap D (shiftedFrameMap a w x') = E.quotMap D (shiftedFrameMap a w x) := by
  have hk : x' - x ∈ E.periodGroup D := by
    refine (hQ.2.2 _).1 ?_
    have hsum : E.quotMap D x' = E.quotMap D x + E.quotMap D (x' - x) := by
      rw [← hQ.1, add_sub_cancel]
    rw [hx] at hsum
    exact left_eq_add.1 hsum
  have hc := quot_const_on_cosets D E hQ a ha w x (x' - x) hk
  rwa [add_sub_cancel] at hc
private theorem existsUnique_descended (hQ : QuotMapSurjectiveHomWithKernel D E) :
    ExistsUniqueDescended D E := by
  intro a ha w
  have hsurj := hQ.2.1
  refine ⟨fun y => E.quotMap D (shiftedFrameMap a w (Function.surjInv hsurj y)), ?_, ?_⟩
  · funext x
    exact quotMap_shiftedFrameMap_eq D E hQ ha w (Function.surjInv_eq hsurj _)
  · intro r hr
    funext y
    obtain ⟨x, rfl⟩ := hsurj y
    have hr₁ : r (E.quotMap D x) = E.quotMap D (shiftedFrameMap a w x) := congrFun hr x
    rw [hr₁]
    exact (quotMap_shiftedFrameMap_eq D E hQ ha w (Function.surjInv_eq hsurj _)).symm
private theorem zero_mem_adicPoints4 : (0 : Fin 4 → ℝ) ∈ adicPoints4 D.L :=
  fun _ => (PeriodicLattice.mem_adicGridPoints_iff D.L 0).2 ⟨0, 0, by simp⟩
private theorem descendedMap_inducedBy (hQ : QuotMapSurjectiveHomWithKernel D E)
    {a : Fin 4 → ℝ} (ha : a ∈ adicPoints4 D.L) (w : SignedFrame) :
    Kind.InducedBy D E (shiftedFrameMap a w)
      (Kind.descendedMap D E (shiftedFrameMap a w)) := by
  unfold Kind.descendedMap
  exact Classical.epsilon_spec (existsUnique_descended D E hQ a ha w).exists
private theorem signedFrameMap_inducedBy (hQ : QuotMapSurjectiveHomWithKernel D E)
    (w : SignedFrame) : Kind.InducedBy D E w.actOnVector (Kind.signedFrameMap D E w) := by
  have h0 : shiftedFrameMap 0 w = w.actOnVector := by
    funext x
    simp [translateR4]
  have h := descendedMap_inducedBy D E hQ (zero_mem_adicPoints4 D) w
  rw [h0] at h
  exact h
private theorem eq_of_inducedBy (hQ : QuotMapSurjectiveHomWithKernel D E)
    {a : Fin 4 → ℝ} {w : SignedFrame} {r : E.Pt D → E.Pt D}
    (hr : Kind.InducedBy D E (shiftedFrameMap a w) r) :
    r = fun y => Kind.signedFrameMap D E w y + E.quotMap D a := by
  funext y
  obtain ⟨x, rfl⟩ := hQ.2.1 y
  have h₁ : r (E.quotMap D x) = E.quotMap D (w.actOnVector x + a) := congrFun hr x
  have h₂ : Kind.signedFrameMap D E w (E.quotMap D x) = E.quotMap D (w.actOnVector x) :=
    congrFun (signedFrameMap_inducedBy D E hQ w) x
  rw [h₁, h₂, hQ.1]
theorem adicLatticesAndInducedMaps_of_wellPosed (hWell : WellPosedness.WellPosed) :
    AdicLatticesAndInducedMaps := by
  intro D E
  have hQ : ∀ E : Kind, QuotMapSurjectiveHomWithKernel D E :=
    fun E => (hWell D E).1
  refine ⟨adicPoints_eq_iUnion D, adicLat_mono D, eventually_mem_adicLat D,
    frame_moves_periods D E, quot_const_on_cosets D E (hQ E), existsUnique_descended D E (hQ E),
    ?_, ?_⟩
  · intro a ha w
    exact eq_of_inducedBy D Kind.torus (hQ _) (descendedMap_inducedBy D Kind.torus (hQ _) ha w)
  · rintro r ⟨s, ⟨a, ha, w, rfl⟩, hr⟩
    exact ⟨w, E.quotMap D a, ⟨a, ha, rfl⟩, eq_of_inducedBy D E (hQ E) hr⟩
end YangMills.Construction.PeriodicSpace.AdicInducedMaps

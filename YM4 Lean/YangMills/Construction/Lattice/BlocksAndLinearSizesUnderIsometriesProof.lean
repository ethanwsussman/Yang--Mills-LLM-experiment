import YangMills.Construction.Lattice.AxialPathUniquenessProof
import YangMills.Construction.Lattice.BlocksAndLinearSizesUnderIsometries
import YangMills.Construction.Lattice.BoxesOfSitesFromACornerProof
import YangMills.Construction.Lattice.ComplexAverageAtAnImageBondProof
import YangMills.Construction.Lattice.PivotOfBond
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.IsometryInvariance
variable {L m : ℕ} {j : ℤ}
theorem isInducedByAffine_apply {σ : FourTorus L m ≃ FourTorus L m} {r : SignedFrame}
    {v : Fin 4 → ℝ} (h : IsInducedByAffine σ r v) (x : FourTorus L m) (μ : Fin 4) :
    σ x μ = ((r.2 μ : ℤˣ) : ℤ) • x (r.1 μ) + (v μ : AddCircle (torusSide L m)) := by
  choose l hl using fun ν => QuotientAddGroup.mk_surjective (x ν)
  have hx : x = toFourTorus L m l := funext fun ν => (hl ν).symm
  rw [hx, h l]
  simp only [toFourTorus, Pi.add_apply, SignedFrame.actOnVector, AddCircle.coe_add]
  congr 1
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
theorem torusSide_eq_mul_meshSize (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    ∃ N : ℕ, (N : ℝ) = (L : ℝ) ^ ((m : ℤ) + j) ∧ torusSide L m = 2 * (N : ℝ) * meshSize L j := by
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ (m : ℤ) + j)
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  refine ⟨L ^ d, ?_, ?_⟩
  · rw [hd]; simp
  · have h₁ : (((L ^ d : ℕ) : ℝ)) = (L : ℝ) ^ ((m : ℤ) + j) := by rw [hd]; simp
    rw [h₁, torusSide, meshSize, mul_assoc, ← zpow_add₀ hL']
    simp
theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem int_eq_zero_of_coe_mul_meshSize (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {a : ℤ}
    (ha : ((|a| : ℤ) : ℝ) < 2 * (L : ℝ) ^ ((m : ℤ) + j))
    (h : (((a : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0) : a = 0 := by
  obtain ⟨N, hN, hs⟩ := torusSide_eq_mul_meshSize (m := m) hL hj
  obtain ⟨c, hc⟩ := (AddCircle.coe_eq_zero_iff (torusSide L m)).1 h
  have hsp := (meshSize_pos hL j).ne'
  have hc' : (c : ℝ) * (2 * (N : ℝ)) = (a : ℝ) := by
    rw [zsmul_eq_mul, hs, ← mul_assoc] at hc
    exact mul_right_cancel₀ hsp hc
  have hc'' : c * (2 * (N : ℤ)) = a := by exact_mod_cast hc'
  rw [← hN] at ha
  have ha' : |a| < 2 * (N : ℤ) := by exact_mod_cast ha
  by_contra hne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hc''.symm)
  have h1 : 1 ≤ |c| := Int.one_le_abs hc0
  have hN0 : (0 : ℤ) ≤ 2 * (N : ℤ) := by positivity
  have : |a| = |c| * (2 * (N : ℤ)) := by
    rw [← hc'', abs_mul, abs_of_nonneg hN0]
  nlinarith
theorem zsmul_unitStep_apply (n : ℤ) (μ ν : Fin 4) :
    ((n • unitStep L m j μ : Site L m j) : FourTorus L m) ν =
      if ν = μ then (((n : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) else 0 := by apply _root_.YangMills.Construction.PeriodicLattice.AxialUniqueness.zsmul_unitStep_apply <;> assumption
theorem isAxialDisplacement_unique (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {x x' : Site L m j}
    {μ μ' : Fin 4} {n n' : ℤ} (h : IsAxialDisplacement x x' μ n)
    (h' : IsAxialDisplacement x x' μ' n') :
    (n = 0 ∧ n' = 0) ∨ (μ = μ' ∧ n = n') := by
  have heq : n • unitStep L m j μ = n' • unitStep L m j μ' := h.1.symm.trans h'.1
  have hc : ∀ ν, ((n • unitStep L m j μ : Site L m j) : FourTorus L m) ν =
      ((n' • unitStep L m j μ' : Site L m j) : FourTorus L m) ν := fun ν => by rw [heq]
  have hpos : (0 : ℝ) ≤ (L : ℝ) ^ ((m : ℤ) + j) := by positivity
  have h1 := h.2
  have h2 := h'.2
  by_cases hμ : μ = μ'
  · subst hμ
    right
    refine ⟨rfl, ?_⟩
    have h3 := hc μ
    simp only [zsmul_unitStep_apply, if_true] at h3
    have h4 : ((((n - n' : ℤ) : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
      push_cast
      rw [sub_mul, AddCircle.coe_sub, h3, sub_self]
    have h5 : ((|n - n'| : ℤ) : ℝ) < 2 * (L : ℝ) ^ ((m : ℤ) + j) := by
      have : |n - n'| ≤ |n| + |n'| := abs_sub _ _
      have : ((|n - n'| : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) + ((|n'| : ℤ) : ℝ) := by exact_mod_cast this
      linarith
    have := int_eq_zero_of_coe_mul_meshSize hL hj h5 h4
    omega
  · left
    have h3 := hc μ
    have h4 := hc μ'
    simp only [zsmul_unitStep_apply, if_true, if_neg hμ, if_neg (Ne.symm hμ)] at h3 h4
    exact ⟨int_eq_zero_of_coe_mul_meshSize hL hj (by linarith) h3,
      int_eq_zero_of_coe_mul_meshSize hL hj (by linarith) h4.symm⟩
theorem flowAlong_zero (x : Site L m j) (μ : Fin 4) : flowAlong x μ 0 = [] := by
  simp [flowAlong, forwardAxisPath]
theorem axialPath_eq_flowAlong (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {x x' : Site L m j} {μ : Fin 4}
    {n : ℤ} (h : IsAxialDisplacement x x' μ n) : axialPath x x' = flowAlong x μ n := by
  have hex : ∃ q : Fin 4 × ℤ, IsAxialDisplacement x x' q.1 q.2 := ⟨(μ, n), h⟩
  rw [axialPath, dif_pos hex]
  rcases isAxialDisplacement_unique hL hj hex.choose_spec h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1, flowAlong_zero, flowAlong_zero]
  · rw [h0, h1]
section Images
variable {σ : FourTorus L m ≃ FourTorus L m}
theorem coe_sitePreimage_symm (hc : MapsCellsAndCubes σ j) (y : Site L m j) :
    ((sitePreimage σ.symm y : Site L m j) : FourTorus L m) = σ y := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.coe_sitePreimage_of_maps <;> assumption
theorem bondImage_eq_of_endpoints (hc : MapsCellsAndCubes σ j) {b b' : Bond L m j}
    (h₁ : (b'.source : FourTorus L m) = σ b.source) (h₂ : (b'.target : FourTorus L m) = σ b.target) :
    bondImage σ b = b' := by
  have h := hc.2.2.2.1 b
  exact Bond.ext (Subtype.ext (h.1.trans h₁.symm)) (Subtype.ext (h.2.trans h₂.symm))
theorem sitePreimage_add_zsmul {r : SignedFrame} {v : Fin 4 → ℝ} (h : IsInducedByAffine σ r v)
    (hc : MapsCellsAndCubes σ j) (z : Site L m j) (μ : Fin 4) (n : ℤ) :
    sitePreimage σ.symm (z + n • unitStep L m j μ) =
      sitePreimage σ.symm z +
        (((r.2 (r.1.symm μ) : ℤˣ) : ℤ) * n) • unitStep L m j (r.1.symm μ) := by
  apply Subtype.ext
  funext ν
  have e₁ : ∀ a b : Site L m j, ((a + b : Site L m j) : FourTorus L m) =
      (a : FourTorus L m) + (b : FourTorus L m) := fun _ _ => rfl
  rw [coe_sitePreimage_symm hc, e₁, e₁, coe_sitePreimage_symm hc, Pi.add_apply,
    isInducedByAffine_apply h, isInducedByAffine_apply h, Pi.add_apply, zsmul_unitStep_apply,
    zsmul_unitStep_apply, smul_add]
  by_cases hν : ν = r.1.symm μ
  · subst hν
    simp only [Equiv.apply_symm_apply, if_true]
    have : (((r.2 (r.1.symm μ) : ℤˣ) : ℤ) •
        (((n : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m))) =
        ((((((r.2 (r.1.symm μ) : ℤˣ) : ℤ) * n : ℤ) : ℝ) * meshSize L j : ℝ) :
          AddCircle (torusSide L m)) := by
      rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
      push_cast
      ring_nf
    rw [this]
    abel
  · have hne : r.1 ν ≠ μ := fun e => hν (by rw [← e]; simp)
    simp only [if_neg hne, if_neg hν, smul_zero, add_zero]
section Paths
variable {r : SignedFrame} {v : Fin 4 → ℝ}
theorem sitePreimage_add_unitStep_of_pos (h : IsInducedByAffine σ r v)
    (hc : MapsCellsAndCubes σ j) {μ : Fin 4}
    (ht : ((r.2 (r.1.symm μ) : ℤˣ) : ℤ) = 1) (z : Site L m j) :
    sitePreimage σ.symm (z + unitStep L m j μ) =
      sitePreimage σ.symm z + unitStep L m j (r.1.symm μ) := by
  simpa [ht] using sitePreimage_add_zsmul h hc z μ 1
theorem sitePreimage_add_unitStep_of_neg (h : IsInducedByAffine σ r v)
    (hc : MapsCellsAndCubes σ j) {μ : Fin 4}
    (ht : ((r.2 (r.1.symm μ) : ℤˣ) : ℤ) = -1) (z : Site L m j) :
    sitePreimage σ.symm (z + unitStep L m j μ) =
      sitePreimage σ.symm z - unitStep L m j (r.1.symm μ) := by
  simpa [ht, sub_eq_add_neg] using sitePreimage_add_zsmul h hc z μ 1
theorem sitePreimage_sub_unitStep_of_pos (h : IsInducedByAffine σ r v)
    (hc : MapsCellsAndCubes σ j) {μ : Fin 4}
    (ht : ((r.2 (r.1.symm μ) : ℤˣ) : ℤ) = 1) (z : Site L m j) :
    sitePreimage σ.symm (z - unitStep L m j μ) =
      sitePreimage σ.symm z - unitStep L m j (r.1.symm μ) := by
  simpa [ht, sub_eq_add_neg] using sitePreimage_add_zsmul h hc z μ (-1)
theorem sitePreimage_sub_unitStep_of_neg (h : IsInducedByAffine σ r v)
    (hc : MapsCellsAndCubes σ j) {μ : Fin 4}
    (ht : ((r.2 (r.1.symm μ) : ℤˣ) : ℤ) = -1) (z : Site L m j) :
    sitePreimage σ.symm (z - unitStep L m j μ) =
      sitePreimage σ.symm z + unitStep L m j (r.1.symm μ) := by
  simpa [ht, sub_eq_add_neg] using sitePreimage_add_zsmul h hc z μ (-1)
theorem pathImage_forwardFlow_of_pos (h : IsInducedByAffine σ r v)
    (hc : MapsCellsAndCubes σ j) {μ : Fin 4}
    (ht : ((r.2 (r.1.symm μ) : ℤˣ) : ℤ) = 1) (n : ℕ) (z : Site L m j) :
    pathImage σ (forwardAxisPath z μ n) =
      forwardAxisPath (sitePreimage σ.symm z) (r.1.symm μ) n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    have hb : bondImage σ (Bond.forwardFrom z μ) =
        Bond.forwardFrom (sitePreimage σ.symm z) (r.1.symm μ) :=
      bondImage_eq_of_endpoints hc (coe_sitePreimage_symm hc z).symm.symm
        (by
          have e := coe_sitePreimage_symm hc (z + unitStep L m j μ)
          rw [sitePreimage_add_unitStep_of_pos h hc ht] at e
          exact e)
    show bondImage σ (Bond.forwardFrom z μ) ::
      pathImage σ (forwardAxisPath (z + unitStep L m j μ) μ n) = _
    rw [hb, ih, sitePreimage_add_unitStep_of_pos h hc ht]
    rfl
theorem pathImage_forwardFlow_of_neg (h : IsInducedByAffine σ r v)
    (hc : MapsCellsAndCubes σ j) {μ : Fin 4}
    (ht : ((r.2 (r.1.symm μ) : ℤˣ) : ℤ) = -1) (n : ℕ) (z : Site L m j) :
    pathImage σ (forwardAxisPath z μ n) =
      backwardAxisPath (sitePreimage σ.symm z) (r.1.symm μ) n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    have hb : bondImage σ (Bond.forwardFrom z μ) =
        Bond.backwardFrom (sitePreimage σ.symm z) (r.1.symm μ) :=
      bondImage_eq_of_endpoints hc (coe_sitePreimage_symm hc z)
        (by
          have e := coe_sitePreimage_symm hc (z + unitStep L m j μ)
          rw [sitePreimage_add_unitStep_of_neg h hc ht] at e
          exact e)
    show bondImage σ (Bond.forwardFrom z μ) ::
      pathImage σ (forwardAxisPath (z + unitStep L m j μ) μ n) = _
    rw [hb, ih, sitePreimage_add_unitStep_of_neg h hc ht]
    rfl
theorem pathImage_backwardFlow_of_pos (h : IsInducedByAffine σ r v)
    (hc : MapsCellsAndCubes σ j) {μ : Fin 4}
    (ht : ((r.2 (r.1.symm μ) : ℤˣ) : ℤ) = 1) (n : ℕ) (z : Site L m j) :
    pathImage σ (backwardAxisPath z μ n) =
      backwardAxisPath (sitePreimage σ.symm z) (r.1.symm μ) n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    have hb : bondImage σ (Bond.backwardFrom z μ) =
        Bond.backwardFrom (sitePreimage σ.symm z) (r.1.symm μ) :=
      bondImage_eq_of_endpoints hc (coe_sitePreimage_symm hc z)
        (by
          have e := coe_sitePreimage_symm hc (z - unitStep L m j μ)
          rw [sitePreimage_sub_unitStep_of_pos h hc ht] at e
          exact e)
    show bondImage σ (Bond.backwardFrom z μ) ::
      pathImage σ (backwardAxisPath (z - unitStep L m j μ) μ n) = _
    rw [hb, ih, sitePreimage_sub_unitStep_of_pos h hc ht]
    rfl
theorem pathImage_backwardFlow_of_neg (h : IsInducedByAffine σ r v)
    (hc : MapsCellsAndCubes σ j) {μ : Fin 4}
    (ht : ((r.2 (r.1.symm μ) : ℤˣ) : ℤ) = -1) (n : ℕ) (z : Site L m j) :
    pathImage σ (backwardAxisPath z μ n) =
      forwardAxisPath (sitePreimage σ.symm z) (r.1.symm μ) n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    have hb : bondImage σ (Bond.backwardFrom z μ) =
        Bond.forwardFrom (sitePreimage σ.symm z) (r.1.symm μ) :=
      bondImage_eq_of_endpoints hc (coe_sitePreimage_symm hc z)
        (by
          have e := coe_sitePreimage_symm hc (z - unitStep L m j μ)
          rw [sitePreimage_sub_unitStep_of_neg h hc ht] at e
          exact e)
    show bondImage σ (Bond.backwardFrom z μ) ::
      pathImage σ (backwardAxisPath (z - unitStep L m j μ) μ n) = _
    rw [hb, ih, sitePreimage_sub_unitStep_of_neg h hc ht]
    rfl
theorem int_unit_eq_one_or_neg_one (u : ℤˣ) : (u : ℤ) = 1 ∨ (u : ℤ) = -1 := by
  rcases Int.units_eq_one_or u with e | e <;> simp [e]
theorem pathImage_flowAlong (h : IsInducedByAffine σ r v)
    (hc : MapsCellsAndCubes σ j) (z : Site L m j) (μ : Fin 4) (n : ℤ) :
    pathImage σ (flowAlong z μ n) =
      flowAlong (sitePreimage σ.symm z) (r.1.symm μ) (((r.2 (r.1.symm μ) : ℤˣ) : ℤ) * n) := by
  rcases int_unit_eq_one_or_neg_one (r.2 (r.1.symm μ)) with ht | ht
  · rw [ht, one_mul]
    unfold flowAlong
    split_ifs with hn
    · exact pathImage_forwardFlow_of_pos h hc ht _ z
    · exact pathImage_backwardFlow_of_pos h hc ht _ z
  · rw [ht]
    rcases lt_trichotomy n 0 with hn | hn | hn
    · have e₁ : ¬0 ≤ n := by omega
      have e₂ : 0 ≤ -1 * n := by omega
      have e₃ : (-n).toNat = (-1 * n).toNat := by congr 1; ring
      unfold flowAlong
      rw [if_neg e₁, if_pos e₂, e₃]
      exact pathImage_backwardFlow_of_neg h hc ht _ z
    · subst hn
      simp [flowAlong_zero, pathImage]
    · have e₁ : 0 ≤ n := by omega
      have e₂ : ¬0 ≤ -1 * n := by omega
      have e₃ : n.toNat = (-(-1 * n)).toNat := by congr 1; ring
      unfold flowAlong
      rw [if_pos e₁, if_neg e₂, ← e₃]
      exact pathImage_forwardFlow_of_neg h hc ht _ z
theorem abs_unit_mul_eq (u : ℤˣ) (n : ℤ) : |(u : ℤ) * n| = |n| := by
  rcases int_unit_eq_one_or_neg_one u with e | e <;> simp [e]
theorem mapsAxialPaths_of_affine (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    (h : IsInducedByAffine σ r v) (hc : MapsCellsAndCubes σ j) :
    MapsAxialPaths σ j := by
  rintro x x' ⟨μ, n, hd⟩
  have hx' : x' = x + n • unitStep L m j μ := by rw [← hd.1]; abel
  have hd' : IsAxialDisplacement (sitePreimage σ.symm x) (sitePreimage σ.symm x')
      (r.1.symm μ) (((r.2 (r.1.symm μ) : ℤˣ) : ℤ) * n) := by
    refine ⟨?_, ?_⟩
    · rw [hx', sitePreimage_add_zsmul h hc]; abel
    · rw [abs_unit_mul_eq]; exact hd.2
  refine ⟨⟨_, _, hd'⟩, ?_⟩
  rw [axialPath_eq_flowAlong hL hj hd, axialPath_eq_flowAlong hL hj hd', pathImage_flowAlong h hc]
def signedPermuteCoords (r : SignedFrame) (n : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun ν => ((r.2 ν : ℤˣ) : ℤ) * n (r.1 ν)
theorem pathImage_stepsThroughAxes (h : IsInducedByAffine σ r v)
    (hc : MapsCellsAndCubes σ j) (n : Fin 4 → ℤ) (l : List (Fin 4))
    (z : Site L m j) :
    pathImage σ (stepsThroughAxes n z l) =
      stepsThroughAxes (signedPermuteCoords r n) (sitePreimage σ.symm z) (l.map r.1.symm) := by
  induction l generalizing z with
  | nil => rfl
  | cons μ l ih =>
    have e : signedPermuteCoords r n (r.1.symm μ) = ((r.2 (r.1.symm μ) : ℤˣ) : ℤ) * n μ := by
      simp [signedPermuteCoords]
    show pathImage σ (flowAlong z μ (n μ) ++ stepsThroughAxes n (z + n μ • unitStep L m j μ) l) =
      flowAlong (sitePreimage σ.symm z) (r.1.symm μ) (signedPermuteCoords r n (r.1.symm μ)) ++
        stepsThroughAxes (signedPermuteCoords r n)
          (sitePreimage σ.symm z +
            signedPermuteCoords r n (r.1.symm μ) • unitStep L m j (r.1.symm μ)) (l.map r.1.symm)
    rw [e, ← sitePreimage_add_zsmul h hc, ← ih, ← pathImage_flowAlong h hc]
    simp [pathImage]
end Paths
theorem range_orderings_eq_nodup_lists (S : Finset (Fin 4)) :
    range (fun τ : Fin S.card ≃ S => (List.finRange S.card).map fun i => ((τ i : S) : Fin 4)) =
      {l | l.Nodup ∧ ∀ μ, μ ∈ l ↔ μ ∈ S} := by
  ext l
  constructor
  · rintro ⟨τ, rfl⟩
    refine ⟨(List.nodup_finRange _).map fun a b e => τ.injective (Subtype.ext e), fun μ => ?_⟩
    simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (τ i).2
    · intro hμ
      exact ⟨τ.symm ⟨μ, hμ⟩, by simp⟩
  · rintro ⟨hn, hm⟩
    have hset : l.toFinset = S := by
      ext μ
      simp [hm]
    have hlen : S.card = l.length := by
      rw [← hset, List.toFinset_card_of_nodup hn]
    let f : Fin S.card → S := fun i =>
      ⟨l.get (i.cast hlen), (hm _).1 (List.get_mem _ _)⟩
    have hf : Function.Injective f := by
      intro a b e
      have e' : l.get (a.cast hlen) = l.get (b.cast hlen) := congrArg Subtype.val e
      have := hn.injective_get e'
      simpa [Fin.ext_iff] using this
    have hb : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by simp⟩
    refine ⟨Equiv.ofBijective f hb, ?_⟩
    apply List.ext_getElem
    · simp [hlen]
    · intro i h₁ h₂
      simp [f]
theorem contourSet_eq_image {j' : ℤ} (y : Site L m j) (x : Site L m j') :
    contourSet y x = stepsThroughAxes (blockOffset y x) (y.toSublattice j') ''
      {l | l.Nodup ∧ ∀ μ, μ ∈ l ↔ blockOffset y x μ ≠ 0} := by
  have hmem : {l : List (Fin 4) | l.Nodup ∧ ∀ μ, μ ∈ l ↔ blockOffset y x μ ≠ 0} =
      {l | l.Nodup ∧ ∀ μ, μ ∈ l ↔ μ ∈ offsetAxes y x} := by
    ext l
    simp [offsetAxes]
  rw [hmem, ← range_orderings_eq_nodup_lists, ← range_comp]
  rfl
theorem coe_toSublattice (hL : 0 < L) {j' : ℤ} (hj : j ≤ j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y := by apply _root_.YangMills.Construction.PeriodicLattice.CornerBoxes.coe_toSublattice <;> assumption
theorem sum_pointOnAxis_apply (f : Fin 4 → ℝ) (ν : Fin 4) :
    (∑ μ, pointOnAxis L m μ (f μ)) ν = (f ν : AddCircle (torusSide L m)) := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.sum_pointOnAxis_apply <;> assumption
theorem isBlockOffset_unique (hLs : Conventions.IsAdmissibleBlockingFactor L) {j' : ℤ}
    (hj : -(m : ℤ) + 1 ≤ j') {y : Site L m j} {x : Site L m j'} {p q : Fin 4 → ℤ}
    (hp : IsBlockOffset y x p) (hq : IsBlockOffset y x q) : p = q := by
  have hL : 0 < L := by have := hLs.2; omega
  funext ν
  have e := congrFun (hp.1.symm.trans hq.1) ν
  rw [sum_pointOnAxis_apply, sum_pointOnAxis_apply] at e
  have h0 : (((((p ν - q ν : ℤ) : ℝ) * meshSize L j' : ℝ)) : AddCircle (torusSide L m)) = 0 := by
    push_cast
    rw [sub_mul, AddCircle.coe_sub, e, sub_self]
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ (m : ℤ) + j' - 1)
  have hpow : (L : ℝ) ≤ (L : ℝ) ^ ((m : ℤ) + j') := by
    have e₁ : (m : ℤ) + j' = ((d + 1 : ℕ) : ℤ) := by push_cast; omega
    rw [e₁, zpow_natCast]
    exact le_self_pow₀ (by exact_mod_cast hL) (by omega)
  have hb : ((|p ν - q ν| : ℤ) : ℝ) < 2 * (L : ℝ) ^ ((m : ℤ) + j') := by
    have h₁ := hp.2 ν
    have h₂ := hq.2 ν
    have h₃ : |p ν - q ν| ≤ |p ν| + |q ν| := abs_sub _ _
    have h₄ : |p ν - q ν| < 2 * (L : ℤ) := by
      have : (0 : ℤ) < L := by exact_mod_cast hL
      omega
    have h₅ : ((|p ν - q ν| : ℤ) : ℝ) < 2 * (L : ℝ) := by exact_mod_cast h₄
    linarith
  have := int_eq_zero_of_coe_mul_meshSize hL (by omega) hb h0
  omega
end Images
theorem isBlockOffset_blockOffset (hB : BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : -(m : ℤ) ≤ j)
    {y : Site L m j} {x : Site L m (j + 1)} (hx : (x : FourTorus L m) ∈ unitBlock y) :
    IsBlockOffset y x (blockOffset y x) := by
  have hL : 0 < L := by have := hLs.2; omega
  have hb := ((hB L m hLs hm j 1 0 hj).1 y).1
  have hx' : (x : FourTorus L m) ∈ refinedBlock 1 y := hx
  rw [hb] at hx'
  obtain ⟨p, hp, hpx⟩ := hx'
  refine Classical.epsilon_spec (p := IsBlockOffset y x) ⟨p, ?_, fun μ => ?_⟩
  · funext ν
    rw [sum_pointOnAxis_apply, Pi.sub_apply, ← hpx]
    have e₁ : ∀ (a b : Site L m (j + ((1 : ℕ) : ℤ))), ((a + b : Site L m (j + ((1 : ℕ) : ℤ))) :
        FourTorus L m) = (a : FourTorus L m) + (b : FourTorus L m) := fun _ _ => rfl
    have e₂ : ((∑ μ, p μ • unitStep L m (j + ((1 : ℕ) : ℤ)) μ : Site L m (j + ((1 : ℕ) : ℤ))) :
        FourTorus L m) ν =
        (((p ν : ℝ) * meshSize L (j + ((1 : ℕ) : ℤ)) : ℝ) : AddCircle (torusSide L m)) := by
      rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
      simp only [zsmul_unitStep_apply]
      simp
    have e₃ := coe_toSublattice (m := m) hL (j' := j + ((1 : ℕ) : ℤ)) (by omega) y
    simp only [refinedOffsetSite, offsetSite]
    rw [e₁, Pi.add_apply, e₂, e₃, add_sub_cancel_left]
    simp
  · have := hp μ
    simpa using this
theorem isBlockOffset_sitePreimage {σ : FourTorus L m ≃ FourTorus L m} {r : SignedFrame}
    {v : Fin 4 → ℝ} {j' : ℤ} (h : IsInducedByAffine σ r v) (hc : MapsCellsAndCubes σ j)
    (hc' : MapsCellsAndCubes σ j') {y : Site L m j} {x : Site L m j'}
    {n : Fin 4 → ℤ} (hn : IsBlockOffset y x n) :
    IsBlockOffset (sitePreimage σ.symm y) (sitePreimage σ.symm x)
      (signedPermuteCoords r n) := by
  refine ⟨?_, fun μ => ?_⟩
  · funext ν
    have e := congrFun hn.1 (r.1 ν)
    rw [sum_pointOnAxis_apply, Pi.sub_apply] at e
    rw [coe_sitePreimage_symm hc', coe_sitePreimage_symm hc, sum_pointOnAxis_apply, Pi.sub_apply,
      isInducedByAffine_apply h, isInducedByAffine_apply h, add_sub_add_right_eq_sub, ← smul_sub,
      e, ← AddCircle.coe_zsmul, zsmul_eq_mul]
    simp only [signedPermuteCoords]
    push_cast
    ring_nf
  · simp only [signedPermuteCoords, abs_unit_mul_eq]
    exact hn.2 _
theorem mem_map_perm_symm (π : Equiv.Perm (Fin 4)) (l : List (Fin 4)) (μ : Fin 4) :
    μ ∈ l.map π.symm ↔ π μ ∈ l := by
  constructor
  · intro hμ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hμ
    simpa using ha
  · intro hμ
    exact List.mem_map.2 ⟨_, hμ, by simp⟩
theorem mapsContourSets_of_affine {σ : FourTorus L m ≃ FourTorus L m} {r : SignedFrame}
    {v : Fin 4 → ℝ} (hB : BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hj : -(m : ℤ) ≤ j) (h : IsInducedByAffine σ r v)
    (hc : MapsCellsAndCubes σ j) (hc' : MapsCellsAndCubes σ (j + 1)) :
    MapsContourSets σ j := by
  intro y x hx
  have hL : 0 < L := by have := hLs.2; omega
  have hj1 : j ≤ j + 1 := by omega
  have hn := isBlockOffset_blockOffset hB hLs hm hj hx
  have hn' := isBlockOffset_sitePreimage h hc hc' hn
  have hd : blockOffset (sitePreimage σ.symm y) (sitePreimage σ.symm x) =
      signedPermuteCoords r (blockOffset y x) :=
    isBlockOffset_unique hLs (by omega)
      (Classical.epsilon_spec (p := IsBlockOffset _ _) ⟨_, hn'⟩) hn'
  have hy : (sitePreimage σ.symm y).toSublattice (j + 1) =
      sitePreimage σ.symm (y.toSublattice (j + 1)) :=
    Subtype.ext (by
      rw [coe_toSublattice hL hj1, coe_sitePreimage_symm hc, coe_sitePreimage_symm hc',
        coe_toSublattice hL hj1])
  have hne : ∀ μ, signedPermuteCoords r (blockOffset y x) μ ≠ 0 ↔
      blockOffset y x (r.1 μ) ≠ 0 := by
    intro μ
    simp only [signedPermuteCoords]
    rcases int_unit_eq_one_or_neg_one (r.2 μ) with e | e <;> simp [e]
  rw [contourSet_eq_image, contourSet_eq_image, hd, hy]
  ext P
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨l.map r.1.symm, ⟨hl.1.map r.1.symm.injective, fun μ => ?_⟩,
      (pathImage_stepsThroughAxes h hc' _ _ _).symm⟩
    rw [mem_map_perm_symm, hl.2, hne]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨_, ⟨l.map r.1, ⟨hl.1.map r.1.injective, fun μ => ?_⟩, rfl⟩, ?_⟩
    · have := mem_map_perm_symm r.1.symm l μ
      rw [Equiv.symm_symm] at this
      rw [this, hl.2, hne]
      simp
    · rw [pathImage_stepsThroughAxes h hc', List.map_map]
      simp
section Bonds
variable {σ : FourTorus L m ≃ FourTorus L m} {j' : ℤ}
theorem mem_image_equiv_iff {X : Set (FourTorus L m)} {x : FourTorus L m} :
    x ∈ σ '' X ↔ σ.symm x ∈ X := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro hx
    exact ⟨_, hx, by simp⟩
theorem image_cubeAround (hc : MapsCellsAndCubes σ j) (y : Site L m j) :
    σ '' cubeAround y = cubeAround (sitePreimage σ.symm y) :=
  hc.2.2.2.2.2.2.2.2.1 y _ (coe_sitePreimage_symm hc y)
theorem mapsBlocks_of_mapsCells (hc : ∀ j', j ≤ j' → MapsCellsAndCubes σ j') :
    MapsBlocks σ j := by
  intro n y
  rw [refinedBlock, image_inter σ.injective, image_cubeAround (hc j le_rfl),
    (hc (j + n) (by omega)).1]
  rfl
theorem bondImage_source (hc : MapsCellsAndCubes σ j) (b : Bond L m j) :
    (bondImage σ b).source = sitePreimage σ.symm b.source :=
  Subtype.ext (by rw [(hc.2.2.2.1 b).1, coe_sitePreimage_symm hc])
theorem bondImage_target (hc : MapsCellsAndCubes σ j) (b : Bond L m j) :
    (bondImage σ b).target = sitePreimage σ.symm b.target :=
  Subtype.ext (by rw [(hc.2.2.2.1 b).2, coe_sitePreimage_symm hc])
theorem bondImage_bondImage_symm (hc : MapsCellsAndCubes σ j)
    (hs : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    bondImage σ (bondImage σ.symm b) = b :=
  bondImage_eq_of_endpoints hc (by rw [(hs.2.2.2.1 b).1]; simp) (by rw [(hs.2.2.2.1 b).2]; simp)
theorem bondImage_symm_bondImage (hc : MapsCellsAndCubes σ j)
    (hs : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    bondImage σ.symm (bondImage σ b) = b :=
  bondImage_eq_of_endpoints hs (by rw [(hc.2.2.2.1 b).1]; simp) (by rw [(hc.2.2.2.1 b).2]; simp)
theorem bondImage_injective (hc : MapsCellsAndCubes σ j)
    (hs : MapsCellsAndCubes σ.symm j) :
    Function.Injective (bondImage σ : Bond L m j → Bond L m j) :=
  Function.LeftInverse.injective (bondImage_symm_bondImage hc hs)
theorem image_bondsInside (hc : MapsCellsAndCubes σ j)
    (hs : MapsCellsAndCubes σ.symm j) (X : Set (FourTorus L m)) :
    bondImage σ '' (bondsInside X : Set (Bond L m j)) = bondsInside (σ '' X) := by
  ext b
  constructor
  · rintro ⟨b₀, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨by rw [(hc.2.2.2.1 b₀).1]; exact mem_image_of_mem σ h₁,
      by rw [(hc.2.2.2.1 b₀).2]; exact mem_image_of_mem σ h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨bondImage σ.symm b, ⟨by rw [(hs.2.2.2.1 b).1]; exact mem_image_equiv_iff.1 h₁,
      by rw [(hs.2.2.2.1 b).2]; exact mem_image_equiv_iff.1 h₂⟩, bondImage_bondImage_symm hc hs b⟩
theorem image_bondsMeeting (hc : MapsCellsAndCubes σ j)
    (hs : MapsCellsAndCubes σ.symm j) (X : Set (FourTorus L m)) :
    bondImage σ '' (bondsMeeting X : Set (Bond L m j)) = bondsMeeting (σ '' X) := by
  ext b
  constructor
  · rintro ⟨b₀, h₁ | h₁, rfl⟩
    · exact Or.inl (by rw [(hc.2.2.2.1 b₀).1]; exact mem_image_of_mem σ h₁)
    · exact Or.inr (by rw [(hc.2.2.2.1 b₀).2]; exact mem_image_of_mem σ h₁)
  · rintro (h₁ | h₁)
    · exact ⟨bondImage σ.symm b,
        Or.inl (by rw [(hs.2.2.2.1 b).1]; exact mem_image_equiv_iff.1 h₁),
        bondImage_bondImage_symm hc hs b⟩
    · exact ⟨bondImage σ.symm b,
        Or.inr (by rw [(hs.2.2.2.1 b).2]; exact mem_image_equiv_iff.1 h₁),
        bondImage_bondImage_symm hc hs b⟩
theorem image_bondDoubleBlock (hb : MapsBlocks σ j) (hc : MapsCellsAndCubes σ j)
    (c : Bond L m j) : σ '' bondDoubleBlock c = bondDoubleBlock (bondImage σ c) := by
  rw [bondDoubleBlock, bondDoubleBlock, image_union, bondImage_source hc, bondImage_target hc]
  exact congrArg₂ (· ∪ ·) (hb 1 c.source) (hb 1 c.target)
theorem bondDoubleBlock_positivelyOriented (c : Bond L m j) :
    bondDoubleBlock c.positivelyOriented = bondDoubleBlock c := by
  unfold Bond.positivelyOriented
  split_ifs
  · rfl
  · exact union_comm _ _
theorem image_bondCorridor (hb : MapsBlocks σ j) (hcj : MapsCellsAndCubes σ j)
    (hc : MapsCellsAndCubes σ j') (hs : MapsCellsAndCubes σ.symm j')
    (c : Bond L m j) :
    bondImage σ '' (bondCorridor c : Set (Bond L m j')) = bondCorridor (bondImage σ c) := by
  have ht : σ '' unitBlock c.source = unitBlock (bondImage σ c).source := by
    rw [bondImage_source hcj]; exact hb 1 c.source
  have hh : σ '' unitBlock c.target = unitBlock (bondImage σ c).target := by
    rw [bondImage_target hcj]; exact hb 1 c.target
  ext b
  constructor
  · rintro ⟨b₀, ⟨h₁, h₂⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [(hc.2.2.2.1 b₀).1, ← ht]; exact mem_image_of_mem σ h₁
    · rw [(hc.2.2.2.1 b₀).2, ← hh]; exact mem_image_of_mem σ h₂
  · rintro ⟨h₁, h₂⟩
    rw [← ht] at h₁
    rw [← hh] at h₂
    exact ⟨bondImage σ.symm b, ⟨by rw [(hs.2.2.2.1 b).1]; exact mem_image_equiv_iff.1 h₁,
      by rw [(hs.2.2.2.1 b).2]; exact mem_image_equiv_iff.1 h₂⟩, bondImage_bondImage_symm hc hs b⟩
theorem isAxialDisplacement_of_mem_axialPath {x x' : Site L m j} {b : Bond L m j}
    (hb : b ∈ axialPath x x') : ∃ μ n, IsAxialDisplacement x x' μ n := by
  unfold axialPath at hb
  split_ifs at hb with h
  · exact ⟨_, _, h.choose_spec⟩
  · simp at hb
theorem bondImage_pivot (hL : 0 < L) {K k : ℕ} (hb : MapsBlocks σ (levelDepth K (k + 1)))
    (hcj : MapsCellsAndCubes σ (levelDepth K (k + 1)))
    (hc : MapsCellsAndCubes σ (levelDepth K k))
    (hs : MapsCellsAndCubes σ.symm (levelDepth K k))
    (hp : MapsAxialPaths σ (levelDepth K k)) (hle : levelDepth K (k + 1) ≤ levelDepth K k)
    (c : BondAtLevel L m K (k + 1)) (hF : PivotProperties c)
    (hF' : PivotProperties (bondImage σ c)) :
    bondImage σ (pivot c : BondAtLevel L m K k) = pivot (bondImage σ c) := by
  have h₀ := hF.isPivot
  have hcor : bondImage σ (pivot c : BondAtLevel L m K k) ∈
      (bondCorridor (bondImage σ c) : Set (BondAtLevel L m K k)) := by
    rw [← image_bondCorridor hb hcj hc hs]
    exact mem_image_of_mem _ h₀.1
  have hsites : ∀ y : SiteAtLevel L m K (k + 1),
      sitePreimage σ.symm (y.toSublattice (levelDepth K k)) =
        (sitePreimage σ.symm y).toSublattice (levelDepth K k) := fun y =>
    Subtype.ext (by
      rw [coe_toSublattice hL hle, coe_sitePreimage_symm hc, coe_toSublattice hL hle,
        coe_sitePreimage_symm hcj])
  have hpath : bondImage σ (pivot c : BondAtLevel L m K k) ∈
      axialPath ((bondImage σ c).source.toSublattice (levelDepth K k))
        ((bondImage σ c).target.toSublattice (levelDepth K k)) := by
    have e := (hp _ _ (isAxialDisplacement_of_mem_axialPath h₀.2)).2
    rw [bondImage_source hcj, bondImage_target hcj, ← hsites, ← hsites, ← e]
    exact List.mem_map_of_mem h₀.2
  have h₁ := hF'.isPivot
  exact hF'.existsUnique_onAxialPath.unique ⟨hpath, hcor⟩ ⟨h₁.2, h₁.1⟩
theorem image_nonPivotBonds_subset {K k : ℕ}
    (hc : MapsCellsAndCubes σ (levelDepth K k))
    (hs : MapsCellsAndCubes σ.symm (levelDepth K k))
    (hc₁ : MapsCellsAndCubes σ (levelDepth K (k + 1)))
    (hs₁ : MapsCellsAndCubes σ.symm (levelDepth K (k + 1)))
    (hpiv : ∀ c : BondAtLevel L m K (k + 1),
      bondImage σ (pivot c : BondAtLevel L m K k) = pivot (bondImage σ c))
    (X : Set (FourTorus L m)) :
    bondImage σ '' nonPivotBonds K k X ⊆ nonPivotBonds K k (σ '' X) := by
  rintro _ ⟨b, ⟨hb, hn⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [← image_bondsMeeting hc hs]
    exact mem_image_of_mem _ hb
  · rintro ⟨c, hcX, e⟩
    rw [← image_bondsMeeting hc₁ hs₁] at hcX
    obtain ⟨c₀, h₀, rfl⟩ := hcX
    refine hn ⟨c₀, h₀, bondImage_injective hc hs ?_⟩
    rw [e, hpiv]
end Bonds
section Edges
variable {σ : FourTorus L m ≃ FourTorus L m} {I : ℤ}
def ActsAffinelyOnCubes (σ : FourTorus L m ≃ FourTorus L m) (I : ℤ) : Prop :=
  (∃ (r : SignedFrame) (v : Fin 4 → ℝ), IsInducedByAffine σ r v) ∧
    MapsCellsAndCubes σ I
theorem zsmul_coe_half (s : ℤ) (e t : ℝ) :
    s • (((e * t / 2 : ℝ)) : AddCircle (torusSide L m)) =
      ((((s : ℝ) * e) * t / 2 : ℝ) : AddCircle (torusSide L m)) := by
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  congr 1
  ring
theorem unit_zsmul_cancel (u : ℤˣ) {a b : AddCircle (torusSide L m)}
    (h : (u : ℤ) • a = (u : ℤ) • b) : a = b := by
  rcases int_unit_eq_one_or_neg_one u with e | e
  · simpa [e] using h
  · simpa [e] using h
theorem signedPermute_sign (r : SignedFrame) {ε : Fin 4 → ℝ} (hε : ∀ ν, ε ν = 1 ∨ ε ν = -1)
    (ν : Fin 4) :
    (((r.2 ν : ℤˣ) : ℤ) : ℝ) * ε (r.1 ν) = 1 ∨ (((r.2 ν : ℤˣ) : ℤ) : ℝ) * ε (r.1 ν) = -1 := by
  rcases int_unit_eq_one_or_neg_one (r.2 ν) with e | e <;> rcases hε (r.1 ν) with f | f <;>
    simp [e, f]
theorem isCubeVertex_image (a : ActsAffinelyOnCubes σ I) {c : FourTorus L m}
    {Q : Set (FourTorus L m)} (hq : IsCubeVertex I c Q) : IsCubeVertex I (σ c) (σ '' Q) := by
  obtain ⟨⟨r, v, h⟩, hc⟩ := a
  obtain ⟨y, rfl, ε, hε, he⟩ := hq
  refine ⟨sitePreimage σ.symm y, image_cubeAround hc y,
    fun ν => (((r.2 ν : ℤˣ) : ℤ) : ℝ) * ε (r.1 ν), signedPermute_sign r hε, fun ν => ?_⟩
  rw [coe_sitePreimage_symm hc, isInducedByAffine_apply h, isInducedByAffine_apply h, he,
    smul_add, zsmul_coe_half]
  abel
theorem isCubeEdge_image (a : ActsAffinelyOnCubes σ I) {e Q : Set (FourTorus L m)}
    (he : IsCubeEdge I e Q) : IsCubeEdge I (σ '' e) (σ '' Q) := by
  obtain ⟨⟨r, v, h⟩, hc⟩ := a
  obtain ⟨y, rfl, μ, ε, hε, rfl⟩ := he
  refine ⟨sitePreimage σ.symm y, image_cubeAround hc y, r.1.symm μ,
    fun ν => (((r.2 ν : ℤˣ) : ℤ) : ℝ) * ε (r.1 ν), signedPermute_sign r hε, ?_⟩
  ext x'
  constructor
  · rintro ⟨x, ⟨hx, hxe⟩, rfl⟩
    refine ⟨mem_image_of_mem σ hx, fun ν hν => ?_⟩
    have hne : r.1 ν ≠ μ := fun e => hν (by rw [← e]; simp)
    rw [coe_sitePreimage_symm hc, isInducedByAffine_apply h, isInducedByAffine_apply h,
      hxe _ hne, smul_add, zsmul_coe_half]
    abel
  · rintro ⟨⟨x, hx, rfl⟩, hxe⟩
    refine ⟨x, ⟨hx, fun ν hν => ?_⟩, rfl⟩
    have hne : r.1.symm ν ≠ r.1.symm μ := fun e => hν (r.1.symm.injective e)
    have e₀ := hxe _ hne
    rw [coe_sitePreimage_symm hc, isInducedByAffine_apply h, isInducedByAffine_apply h,
      Equiv.apply_symm_apply, ← zsmul_coe_half, add_right_comm, ← smul_add] at e₀
    simp only [Equiv.apply_symm_apply] at e₀
    exact unit_zsmul_cancel _ (add_right_cancel e₀)
theorem ActsAffinelyOnCubes.continuous (a : ActsAffinelyOnCubes σ I) : Continuous σ := by
  obtain ⟨⟨r, v, h⟩, -⟩ := a
  refine continuous_pi fun μ => ?_
  simp only [isInducedByAffine_apply h]
  exact ((continuous_zsmul _).comp (continuous_apply _)).add continuous_const
theorem partitionCubesIn_image (hc : MapsCellsAndCubes σ I) (X : Set (FourTorus L m)) :
    partitionCubesIn I (σ '' X) = (fun Q => σ '' Q) '' partitionCubesIn I X := by
  have hp := hc.2.2.2.2.2.2.2.2.2
  ext Q
  constructor
  · rintro ⟨hq, hs⟩
    rw [← hp] at hq
    obtain ⟨Q₀, h₀, rfl⟩ := hq
    exact ⟨Q₀, ⟨h₀, (image_subset_image_iff σ.injective).1 hs⟩, rfl⟩
  · rintro ⟨Q₀, ⟨h₀, hs⟩, rfl⟩
    exact ⟨hp ▸ mem_image_of_mem _ h₀, image_mono hs⟩
theorem image_mem_standardCubePartition (hc : MapsCellsAndCubes σ I) {Q : Set (FourTorus L m)}
    (hq : Q ∈ standardCubePartition L m I) : σ '' Q ∈ standardCubePartition L m I := by
  rw [← hc.2.2.2.2.2.2.2.2.2]
  exact mem_image_of_mem _ hq
theorem image_mem_partitionCubesIn (hc : MapsCellsAndCubes σ I) {X Q : Set (FourTorus L m)}
    (hq : Q ∈ partitionCubesIn I X) : σ '' Q ∈ partitionCubesIn I (σ '' X) := by
  rw [partitionCubesIn_image hc]
  exact mem_image_of_mem _ hq
theorem isEdgeGraph_image (a : ActsAffinelyOnCubes σ I) {X Γ : Set (FourTorus L m)}
    (hΓ : IsEdgeGraph I X Γ) : IsEdgeGraph I (σ '' X) (σ '' Γ) := by
  rcases hΓ with ⟨Q, hQ, c, hcn, rfl⟩ | ⟨E, hE, rfl⟩
  · exact Or.inl ⟨σ '' Q, image_mem_partitionCubesIn a.2 hQ, σ c, isCubeVertex_image a hcn,
      image_singleton⟩
  · refine Or.inr ⟨(fun e => σ '' e) '' E, ?_, image_sUnion⟩
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨Q, hQ, heq⟩ := hE e he
    exact ⟨σ '' Q, image_mem_partitionCubesIn a.2 hQ, isCubeEdge_image a heq⟩
theorem equiv_symm_image_image (Γ : Set (FourTorus L m)) : σ.symm '' (σ '' Γ) = Γ := by
  simp [image_image]
theorem equiv_image_symm_image (Γ : Set (FourTorus L m)) : σ '' (σ.symm '' Γ) = Γ := by
  simp [image_image]
theorem equiv_image_injective :
    Function.Injective (fun S : Set (FourTorus L m) => σ '' S) :=
  image_injective.2 σ.injective
theorem image_setOf_isEdgeGraph (a : ActsAffinelyOnCubes σ I) (b : ActsAffinelyOnCubes σ.symm I)
    (X : Set (FourTorus L m)) :
    (fun Γ => σ '' Γ) '' {Γ | IsEdgeGraph I X Γ} = {Γ | IsEdgeGraph I (σ '' X) Γ} := by
  ext Γ
  constructor
  · rintro ⟨Γ₀, h₀, rfl⟩
    exact isEdgeGraph_image a h₀
  · intro h₀
    refine ⟨σ.symm '' Γ, ?_, equiv_image_symm_image Γ⟩
    have := isEdgeGraph_image b h₀
    rwa [equiv_symm_image_image] at this
theorem image_mem_cubeEdges (a : ActsAffinelyOnCubes σ I) {Γ e : Set (FourTorus L m)}
    (he : (∃ Q ∈ standardCubePartition L m I, IsCubeEdge I e Q) ∧ e ⊆ Γ) :
    (∃ Q ∈ standardCubePartition L m I, IsCubeEdge I (σ '' e) Q) ∧ σ '' e ⊆ σ '' Γ := by
  obtain ⟨⟨Q, hQ, heq⟩, hs⟩ := he
  exact ⟨⟨σ '' Q, image_mem_standardCubePartition a.2 hQ, isCubeEdge_image a heq⟩, image_mono hs⟩
theorem edgeCount_image (a : ActsAffinelyOnCubes σ I) (b : ActsAffinelyOnCubes σ.symm I)
    (Γ : Set (FourTorus L m)) : edgeCount I (σ '' Γ) = edgeCount I Γ := by
  have hset : {e | (∃ Q ∈ standardCubePartition L m I, IsCubeEdge I e Q) ∧ e ⊆ σ '' Γ} =
      (fun e => σ '' e) ''
        {e | (∃ Q ∈ standardCubePartition L m I, IsCubeEdge I e Q) ∧ e ⊆ Γ} := by
    ext e
    constructor
    · intro he
      refine ⟨σ.symm '' e, ?_, equiv_image_symm_image e⟩
      have := image_mem_cubeEdges b he
      rwa [equiv_symm_image_image] at this
    · rintro ⟨e₀, h₀, rfl⟩
      exact image_mem_cubeEdges a h₀
  unfold edgeCount
  rw [hset, ncard_image_of_injective _ equiv_image_injective]
theorem graphLength_image (a : ActsAffinelyOnCubes σ I) (b : ActsAffinelyOnCubes σ.symm I)
    (M : ℕ) (Γ : Set (FourTorus L m)) : graphLength M I (σ '' Γ) = graphLength M I Γ := by
  unfold graphLength
  rw [edgeCount_image a b]
theorem isSpanningEdgeTree_image (a : ActsAffinelyOnCubes σ I) {X Γ : Set (FourTorus L m)}
    {G : Set (Set (FourTorus L m))} (h : IsSpanningEdgeTree I X G Γ) :
    IsSpanningEdgeTree I (σ '' X) ((fun A => σ '' A) '' G) (σ '' Γ) := by
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
  refine ⟨⟨isEdgeGraph_image a h₁, h₂.image _ (ActsAffinelyOnCubes.continuous a).continuousOn⟩, ?_⟩
  rintro _ ⟨A, hA, rfl⟩
  obtain ⟨x, hx, hx'⟩ := h₃ A hA
  exact ⟨σ x, mem_image_of_mem σ hx, mem_image_of_mem σ hx'⟩
theorem minTreeLength_image (a : ActsAffinelyOnCubes σ I) (b : ActsAffinelyOnCubes σ.symm I)
    (M : ℕ) (X : Set (FourTorus L m)) (G : Set (Set (FourTorus L m))) :
    minTreeLength M I (σ '' X) ((fun A => σ '' A) '' G) = minTreeLength M I X G := by
  unfold minTreeLength
  congr 1
  ext n
  constructor
  · rintro ⟨Γ, hΓ, rfl⟩
    refine ⟨σ.symm '' Γ, ?_, graphLength_image b a M Γ⟩
    have := isSpanningEdgeTree_image b hΓ
    rw [equiv_symm_image_image, image_image] at this
    simpa [equiv_symm_image_image] using this
  · rintro ⟨Γ, hΓ, rfl⟩
    exact ⟨σ '' Γ, isSpanningEdgeTree_image a hΓ, graphLength_image a b M Γ⟩
theorem cubesNotIn_image (hc : MapsCellsAndCubes σ I) (X Z : Set (FourTorus L m)) :
    cubesNotIn I (σ '' X) (σ '' Z) = (fun Q => σ '' Q) '' cubesNotIn I X Z := by
  unfold cubesNotIn
  rw [partitionCubesIn_image hc, partitionCubesIn_image hc, image_sdiff equiv_image_injective]
theorem sUnion_image_image (F : Set (Set (FourTorus L m))) :
    ⋃₀ ((fun B => σ '' B) '' F) = σ '' ⋃₀ F := image_sUnion.symm
theorem islandTreeTargets_image (hc : MapsCellsAndCubes σ I)
    (F : Set (Set (FourTorus L m))) (X : Set (FourTorus L m)) :
    islandTreeTargets I ((fun B => σ '' B) '' F) (σ '' X) =
      (fun A => σ '' A) '' islandTreeTargets I F X := by
  unfold islandTreeTargets
  rw [sUnion_image_image, cubesNotIn_image hc, image_union]
  congr 1
  ext B
  constructor
  · rintro ⟨⟨B₀, h₀, rfl⟩, hs⟩
    exact ⟨B₀, ⟨h₀, (image_subset_image_iff σ.injective).1 hs⟩, rfl⟩
  · rintro ⟨B₀, ⟨h₀, hs⟩, rfl⟩
    exact ⟨mem_image_of_mem _ h₀, image_mono hs⟩
theorem linearExtent_image {K m' j₀ : ℕ} (a : ActsAffinelyOnCubes σ (coarseCubeIndex K m' j₀))
    (b : ActsAffinelyOnCubes σ.symm (coarseCubeIndex K m' j₀)) (X : Set (FourTorus L m)) :
    linearExtent K m' j₀ (σ '' X) = linearExtent K m' j₀ X := by
  unfold linearExtent
  rw [partitionCubesIn_image a.2, minTreeLength_image a b]
theorem relativeLinearExtent_image {K m' j₀ : ℕ}
    (a : ActsAffinelyOnCubes σ (coarseCubeIndex K m' j₀))
    (b : ActsAffinelyOnCubes σ.symm (coarseCubeIndex K m' j₀)) (Z X : Set (FourTorus L m)) :
    relativeLinearExtent K m' j₀ (σ '' Z) (σ '' X) = relativeLinearExtent K m' j₀ Z X := by
  have hiff : (∀ Q ∈ partitionCubesIn (coarseCubeIndex K m' j₀) (σ '' X), Q ⊆ σ '' Z) ↔
      ∀ Q ∈ partitionCubesIn (coarseCubeIndex K m' j₀) X, Q ⊆ Z := by
    rw [partitionCubesIn_image a.2]
    constructor
    · intro h Q hQ
      exact (image_subset_image_iff σ.injective).1 (h _ (mem_image_of_mem _ hQ))
    · rintro h _ ⟨Q, hQ, rfl⟩
      exact image_mono (h Q hQ)
  unfold relativeLinearExtent
  by_cases hZ : ∀ Q ∈ partitionCubesIn (coarseCubeIndex K m' j₀) X, Q ⊆ Z
  · rw [if_pos hZ, if_pos (hiff.2 hZ)]
  · rw [if_neg hZ, if_neg (fun h => hZ (hiff.1 h)), cubesNotIn_image a.2,
      minTreeLength_image a b]
theorem islandLinearExtent_image {K m' j₀ : ℕ}
    (a : ActsAffinelyOnCubes σ (coarseCubeIndex K m' j₀))
    (b : ActsAffinelyOnCubes σ.symm (coarseCubeIndex K m' j₀)) (F : Set (Set (FourTorus L m)))
    (X : Set (FourTorus L m)) :
    islandLinearExtent K m' j₀ ((fun B => σ '' B) '' F) (σ '' X) =
      islandLinearExtent K m' j₀ F X := by
  unfold islandLinearExtent
  rw [islandTreeTargets_image a.2, minTreeLength_image a b]
theorem isIslandCollection_image (hr : MapsRegions σ I) {F : Set (Set (FourTorus L m))}
    (hF : IsIslandCollection I F) : IsIslandCollection I ((fun B => σ '' B) '' F) := by
  obtain ⟨h₁, h₂, h₃⟩ := hF
  refine ⟨h₁.image _, ?_, ?_⟩
  · rintro _ ⟨B, hB, rfl⟩
    exact ((hr.2.2.2.2.1 B (h₂ B hB).1).2.2.2.1).2 (h₂ B hB)
  · rintro _ ⟨B, hB, rfl⟩ _ ⟨B', hB', rfl⟩ hne ht
    refine h₃ hB hB' (fun e => hne (by rw [e])) ?_
    exact (hr.2.2.1 B B' (h₂ B hB).1 (h₂ B' hB').1).1 ht
theorem image_mem_connectedRegions (hc : MapsCellsAndCubes σ I)
    (hr : MapsRegions σ I) {X : Set (FourTorus L m)} (hX : X ∈ connectedRegions L m I) :
    σ '' X ∈ connectedRegions L m I := by
  obtain ⟨hreg, hne, hw⟩ := hX
  refine ⟨(hr.1 X).2 hreg, hne.image _, ?_⟩
  rw [partitionCubesIn_image hc]
  rintro _ ⟨Q, hQ, rfl⟩ _ ⟨Q', hQ', rfl⟩
  obtain ⟨c, hc₁, hc₂, hc₃⟩ := hw Q hQ Q' hQ'
  refine ⟨c.map fun P => σ '' P, ((hr.2.2.2.1 X hreg c).2).2 hc₁, ?_, ?_⟩
  · simp [List.head?_map, hc₂]
  · simp [List.getLast?_map, hc₃]
theorem image_connectedRegions (hc : MapsCellsAndCubes σ I)
    (hr : MapsRegions σ I) (hs : MapsCellsAndCubes σ.symm I)
    (hrs : MapsRegions σ.symm I) :
    (fun X => σ '' X) '' connectedRegions L m I = connectedRegions L m I := by
  ext X
  constructor
  · rintro ⟨X₀, h₀, rfl⟩
    exact image_mem_connectedRegions hc hr h₀
  · intro h₀
    exact ⟨σ.symm '' X, image_mem_connectedRegions hs hrs h₀, equiv_image_symm_image X⟩
theorem image_mem_islandRegions (hc : MapsCellsAndCubes σ I)
    (hr : MapsRegions σ I) {F : Set (Set (FourTorus L m))} {X : Set (FourTorus L m)}
    (hX : X ∈ islandRegions I F) : σ '' X ∈ islandRegions I ((fun B => σ '' B) '' F) := by
  obtain ⟨h₁, ⟨J, hJ, hJe⟩, h₃⟩ := hX
  refine ⟨image_mem_connectedRegions hc hr h₁, ⟨(fun B => σ '' B) '' J, image_mono hJ, ?_⟩, ?_⟩
  · rw [sUnion_image_image, sUnion_image_image, ← image_inter σ.injective, hJe]
  · rw [sUnion_image_image]
    exact fun h => h₃ ((image_subset_image_iff σ.injective).1 h)
theorem image_islandRegions (hc : MapsCellsAndCubes σ I)
    (hr : MapsRegions σ I) (hs : MapsCellsAndCubes σ.symm I)
    (hrs : MapsRegions σ.symm I) (F : Set (Set (FourTorus L m))) :
    (fun X => σ '' X) '' islandRegions I F = islandRegions I ((fun B => σ '' B) '' F) := by
  ext X
  constructor
  · rintro ⟨X₀, h₀, rfl⟩
    exact image_mem_islandRegions hc hr h₀
  · intro h₀
    refine ⟨σ.symm '' X, ?_, equiv_image_symm_image X⟩
    have := image_mem_islandRegions hs hrs h₀
    rw [image_image] at this
    simpa [equiv_symm_image_image] using this
end Edges
theorem symm_mem_latticeIsometries {i : ℤ} (hg : LatticeIsometriesFormFiniteGroup L m i)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i) :
    σ.symm ∈ latticeIsometries L m i := by
  obtain ⟨⟨H, hH⟩, -⟩ := hg
  have h₁ : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := by rw [hH]; exact hσ
  have h₂ : σ⁻¹ ∈ H := H.inv_mem h₁
  have h₃ : σ⁻¹ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := h₂
  rw [hH] at h₃
  exact h₃
theorem exists_isInducedByAffine_of_mem {i : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : σ ∈ latticeIsometries L m i) :
    ∃ (r : SignedFrame) (v : Fin 4 → ℝ), IsInducedByAffine σ r v := by
  obtain ⟨r, v, -, h⟩ := hσ
  exact ⟨r, v, h⟩
theorem mapsBondObjects_of_affine {σ : FourTorus L m ≃ FourTorus L m} (hF : PivotOfEveryBond)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    (hσ : ∃ (r : SignedFrame) (v : Fin 4 → ℝ), IsInducedByAffine σ r v)
    (hc : ∀ j', i ≤ j' → MapsCellsAndCubes σ j')
    (hs : ∀ j', i ≤ j' → MapsCellsAndCubes σ.symm j')
    {K k : ℕ} (hk : k < K) (hd : i ≤ levelDepth K (k + 1)) :
    MapsBondObjects σ K k := by
  have hL : 0 < L := by have := hLs.2; omega
  have hd' : i ≤ levelDepth K k := by simp only [levelDepth] at hd ⊢; omega
  obtain ⟨r, v, h⟩ := hσ
  have hb : MapsBlocks σ (levelDepth K (k + 1)) :=
    mapsBlocks_of_mapsCells fun j' hj' => hc j' (hd.trans hj')
  have hcj := hc _ hd
  have hck := hc _ hd'
  have hsk := hs _ hd'
  have hp : MapsAxialPaths σ (levelDepth K k) :=
    mapsAxialPaths_of_affine hL (hi.trans hd') h hck
  have hpiv := fun c : BondAtLevel L m K (k + 1) =>
    hF ⟨L, hLs, ⟨K, by omega⟩, ⟨m, hm⟩⟩ k hk c
  intro c
  refine ⟨image_bondDoubleBlock hb hcj c, image_bondCorridor hb hcj hck hsk c,
    bondImage_pivot hL hb hcj hck hsk hp (by simp only [levelDepth]; omega) c (hpiv c)
      (hpiv (bondImage σ c)), ?_⟩
  unfold bondsInDoubleBlock
  rw [bondDoubleBlock_positivelyOriented, bondDoubleBlock_positivelyOriented,
    image_bondsInside hck hsk, image_bondDoubleBlock hb hcj]
theorem invariantUnderIsometries_holds (hG : LatticeIsometryGroupActionStatement)
    (hB : BlockPartition.Properties) (hF : PivotOfEveryBond) : InvariantUnderIsometries := by
  intro L m hLs hm i hi σ hσ
  have hL : 0 < L := by have := hLs.2; omega
  obtain ⟨hgroup, -, -, -, hall⟩ := hG L m i hLs hm hi
  have hτ := symm_mem_latticeIsometries hgroup hσ
  have hc : ∀ j', i ≤ j' → MapsCellsAndCubes σ j' := fun j' h => (hall σ hσ j' h).1
  have hs : ∀ j', i ≤ j' → MapsCellsAndCubes σ.symm j' :=
    fun j' h => (hall σ.symm hτ j' h).1
  have hr : ∀ j', i ≤ j' → MapsRegions σ j' := fun j' h => (hall σ hσ j' h).2
  have hrs : ∀ j', i ≤ j' → MapsRegions σ.symm j' := fun j' h => (hall σ.symm hτ j' h).2
  have ha : ∀ j', i ≤ j' → ActsAffinelyOnCubes σ j' :=
    fun j' h => ⟨exists_isInducedByAffine_of_mem hσ, hc j' h⟩
  have hb : ∀ j', i ≤ j' → ActsAffinelyOnCubes σ.symm j' :=
    fun j' h => ⟨exists_isInducedByAffine_of_mem hτ, hs j' h⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨r, v, h⟩ := exists_isInducedByAffine_of_mem hσ
    exact ⟨mapsBlocks_of_mapsCells fun j' hj' => hc j' (hj.trans hj'),
      mapsAxialPaths_of_affine hL (hi.trans hj) h (hc j hj),
      mapsContourSets_of_affine hB hLs hm (hi.trans hj) h (hc j hj) (hc _ (by omega))⟩
  · intro K k hk hd
    exact mapsBondObjects_of_affine hF hLs hm hi (exists_isInducedByAffine_of_mem hσ) hc hs hk hd
  · intro K k hk i' hi' hi'' X _
    have hck := hc _ (hi'.trans hi'')
    have hsk := hs _ (hi'.trans hi'')
    ext x
    constructor
    · rintro ⟨x₀, h₀, rfl⟩
      show ((sitePreimage σ.symm x₀ : SiteAtLevel L m K k) : FourTorus L m) ∈ σ '' X
      rw [coe_sitePreimage_symm hck]
      exact mem_image_of_mem σ h₀
    · intro h₀
      have h₁ : (x : FourTorus L m) ∈ σ '' X := h₀
      refine ⟨sitePreimage σ.symm.symm x, ?_, ?_⟩
      · show ((sitePreimage σ.symm.symm x : SiteAtLevel L m K k) : FourTorus L m) ∈ X
        rw [coe_sitePreimage_symm hsk]
        exact mem_image_equiv_iff.1 h₁
      · apply Subtype.ext
        rw [coe_sitePreimage_symm hck, coe_sitePreimage_symm hsk]
        simp
  · intro K k hk hd i' hi' hi'' X _
    have hd' : i ≤ levelDepth K k := hi'.trans hi''
    have hpσ : ∀ c : BondAtLevel L m K (k + 1),
        bondImage σ (pivot c : BondAtLevel L m K k) = pivot (bondImage σ c) :=
      fun c => (mapsBondObjects_of_affine hF hLs hm hi (exists_isInducedByAffine_of_mem hσ) hc hs
        hk hd c).2.2.1
    have hpτ : ∀ c : BondAtLevel L m K (k + 1),
        bondImage σ.symm (pivot c : BondAtLevel L m K k) = pivot (bondImage σ.symm c) :=
      fun c => (mapsBondObjects_of_affine hF hLs hm hi (exists_isInducedByAffine_of_mem hτ) hs hc
        hk hd c).2.2.1
    apply Subset.antisymm
    · exact image_nonPivotBonds_subset (hc _ hd') (hs _ hd') (hc _ hd) (hs _ hd) hpσ X
    · intro b hb'
      refine ⟨bondImage σ.symm b, ?_, bondImage_bondImage_symm (hc _ hd') (hs _ hd') b⟩
      have := image_nonPivotBonds_subset (hs _ hd') (hc _ hd') (hs _ hd) (hc _ hd) hpτ (σ '' X)
        (mem_image_of_mem _ hb')
      rwa [equiv_symm_image_image] at this
  · intro K m' j _ hI
    have a := ha _ hI
    have b := hb _ hI
    refine ⟨fun X _ => ⟨image_setOf_isEdgeGraph a b X, fun Γ _ => graphLength_image a b _ Γ⟩,
      ⟨image_connectedRegions (hc _ hI) (hr _ hI) (hs _ hI) (hrs _ hI), fun X _ =>
        ⟨linearExtent_image a b X, fun Z _ => relativeLinearExtent_image a b Z X⟩⟩, fun F hF' =>
        ⟨isIslandCollection_image (hr _ hI) hF', image_islandRegions (hc _ hI) (hr _ hI) (hs _ hI)
          (hrs _ hI) F, fun X _ => islandLinearExtent_image a b F X⟩⟩
end YangMills.Construction.PeriodicLattice.IsometryInvariance

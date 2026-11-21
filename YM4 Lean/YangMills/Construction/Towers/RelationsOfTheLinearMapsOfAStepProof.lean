import YangMills.Construction.Towers.BlocksOfATower
import YangMills.Construction.Towers.EndPointsOfTheContours
import YangMills.Construction.Towers.RelationsOfTheLinearMapsOfAStep
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.PeriodicLattice (FourTorus unitBlock sitesInBlock inverseFourthPowerWeight
  contourSet contourFormAverage orderedContour crossingPath levelDepth sublattice bondFormSumAlong
  unitStep shiftAcross)
noncomputable section
namespace YangMills.Construction.Tower.TrivialLinearization
section GradientSums
variable {L m : ℕ} {i i' : ℤ}
theorem sumAlong_forwardFlow_of_gradient (f : PeriodicLattice.Site L m i → Matrices.ComplexMatrix2)
    (μ : Fin 4) (N : ℕ) :
    ∀ x : PeriodicLattice.Site L m i,
      bondFormSumAlong (fun b => f b.target - f b.source) (PeriodicLattice.forwardAxisPath x μ N) =
        f (x + N • unitStep L m i μ) - f x := by
  induction N with
  | zero => intro x; simp [PeriodicLattice.forwardAxisPath, bondFormSumAlong]
  | succ N ih =>
    intro x
    have h := ih (x + unitStep L m i μ)
    have e : x + unitStep L m i μ + N • unitStep L m i μ = x + (N + 1) • unitStep L m i μ := by
      rw [succ_nsmul]; abel
    rw [e] at h
    unfold bondFormSumAlong at h ⊢
    simp only [PeriodicLattice.forwardAxisPath, List.map_cons, List.sum_cons, h]
    show f (x + unitStep L m i μ) - f x + _ = _
    abel
theorem sumAlong_backwardFlow_of_gradient (f : PeriodicLattice.Site L m i → Matrices.ComplexMatrix2)
    (μ : Fin 4) (N : ℕ) :
    ∀ x : PeriodicLattice.Site L m i,
      bondFormSumAlong (fun b => f b.target - f b.source) (PeriodicLattice.backwardAxisPath x μ N) =
        f (x - N • unitStep L m i μ) - f x := by
  induction N with
  | zero => intro x; simp [PeriodicLattice.backwardAxisPath, bondFormSumAlong]
  | succ N ih =>
    intro x
    have h := ih (x - unitStep L m i μ)
    have e : x - unitStep L m i μ - N • unitStep L m i μ = x - (N + 1) • unitStep L m i μ := by
      rw [succ_nsmul]; abel
    rw [e] at h
    unfold bondFormSumAlong at h ⊢
    simp only [PeriodicLattice.backwardAxisPath, List.map_cons, List.sum_cons, h]
    show f (x - unitStep L m i μ) - f x + _ = _
    abel
theorem sumAlong_flow_of_gradient (f : PeriodicLattice.Site L m i → Matrices.ComplexMatrix2)
    (μ : Fin 4) (t : ℤ) (x : PeriodicLattice.Site L m i) :
    bondFormSumAlong (fun b => f b.target - f b.source) (PeriodicLattice.flowAlong x μ t) =
      f (x + t • unitStep L m i μ) - f x := by
  unfold PeriodicLattice.flowAlong
  split_ifs with h
  · have ht : (t.toNat : ℤ) = t := Int.toNat_of_nonneg h
    have e : t.toNat • unitStep L m i μ = t • unitStep L m i μ := by
      rw [← natCast_zsmul, ht]
    rw [sumAlong_forwardFlow_of_gradient, e]
  · have ht : ((-t).toNat : ℤ) = -t := Int.toNat_of_nonneg (by omega)
    have e : x - (-t).toNat • unitStep L m i μ = x + t • unitStep L m i μ := by
      rw [← natCast_zsmul, ht, neg_smul, sub_neg_eq_add]
    rw [sumAlong_backwardFlow_of_gradient, e]
theorem sumAlong_axialPath_of_gradient (f : PeriodicLattice.Site L m i → Matrices.ComplexMatrix2)
    {x x' : PeriodicLattice.Site L m i} {μ : Fin 4} {t : ℤ}
    (h : PeriodicLattice.IsAxialDisplacement x x' μ t) :
    bondFormSumAlong (fun b => f b.target - f b.source) (PeriodicLattice.axialPath x x') =
      f x' - f x := by
  have hex : ∃ q : Fin 4 × ℤ, PeriodicLattice.IsAxialDisplacement x x' q.1 q.2 := ⟨(μ, t), h⟩
  unfold PeriodicLattice.axialPath
  rw [dif_pos hex, sumAlong_flow_of_gradient]
  have e : x + hex.choose.2 • unitStep L m i hex.choose.1 = x' := by
    rw [← hex.choose_spec.1]; abel
  rw [e]
theorem sumAlong_path_of_gradient (f : PeriodicLattice.Site L m i → Matrices.ComplexMatrix2)
    (Γ : List (PeriodicLattice.Bond L m i)) :
    ∀ x x' : PeriodicLattice.Site L m i, PeriodicLattice.IsBondPathFromTo Γ x x' →
      bondFormSumAlong (fun b => f b.target - f b.source) Γ = f x' - f x := by
  induction Γ with
  | nil =>
    intro x x' h
    have e : x = x' := h.2.1 rfl
    subst e
    simp [bondFormSumAlong]
  | cons b Γ ih =>
    intro x x' h
    have hb : b.source = x := h.2.2.1 b (by simp)
    subst hb
    have hrest : bondFormSumAlong (fun b => f b.target - f b.source) Γ = f x' - f b.target := by
      cases Γ with
      | nil =>
        have e : b.target = x' := h.2.2.2 b (by simp)
        subst e
        simp [bondFormSumAlong]
      | cons b' Γ' =>
        have hc := List.isChain_cons_cons.mp h.1
        refine ih _ _ ⟨hc.2, by simp, fun c hc' => ?_, fun c hc' => ?_⟩
        · have e : b' = c := by simpa using hc'
          subst e
          exact hc.1.symm
        · exact h.2.2.2 c (by simpa [List.getLast?_cons_cons] using hc')
    unfold bondFormSumAlong at hrest ⊢
    simp only [List.map_cons, List.sum_cons, hrest]
    abel
theorem contourFormAverage_of_gradient (f : PeriodicLattice.Site L m i' → Matrices.ComplexMatrix2)
    {y : PeriodicLattice.Site L m i} {x : PeriodicLattice.Site L m i'}
    (h : ∀ Γ ∈ contourSet y x, PeriodicLattice.IsBondPathFromTo Γ (y.toSublattice i') x) :
    contourFormAverage (fun b => f b.target - f b.source) y x = f x - f (y.toSublattice i') := by
  have hv : ∀ σ, bondFormSumAlong (fun b => f b.target - f b.source) (orderedContour y x σ) =
      f x - f (y.toSublattice i') := fun σ => sumAlong_path_of_gradient f _ _ _ (h _ ⟨σ, rfl⟩)
  have hc : Fintype.card (PeriodicLattice.AxisOrdering y x) ≠ 0 := by
    have : Nonempty (PeriodicLattice.AxisOrdering y x) := ⟨(Finset.equivFin _).symm⟩
    exact Fintype.card_ne_zero
  unfold contourFormAverage
  simp only [hv, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have e : (((Fintype.card (PeriodicLattice.AxisOrdering y x) : ℝ)⁻¹ : ℝ) : ℂ) *
      (Fintype.card (PeriodicLattice.AxisOrdering y x) : ℂ) = 1 := by
    push_cast
    exact inv_mul_cancel₀ (by exact_mod_cast hc)
  rw [e, one_smul]
theorem coe_shiftAcross (hle : sublattice L m i ≤ sublattice L m i')
    (c : PeriodicLattice.Bond L m i) (x : PeriodicLattice.Site L m i') :
    ((shiftAcross c x : PeriodicLattice.Site L m i') : FourTorus L m) =
      (x : FourTorus L m) + ((c.target : FourTorus L m) - (c.source : FourTorus L m)) := by
  have h : (((c.target - c.source).toSublattice i' : PeriodicLattice.Site L m i') : FourTorus L m) =
      ((c.target - c.source : PeriodicLattice.Site L m i) : FourTorus L m) :=
    Classical.epsilon_spec
      (p := fun z : PeriodicLattice.Site L m i' =>
        (z : FourTorus L m) = ((c.target - c.source : PeriodicLattice.Site L m i) : FourTorus L m))
      ⟨⟨_, hle (c.target - c.source).2⟩, rfl⟩
  show (x : FourTorus L m) +
      (((c.target - c.source).toSublattice i' : PeriodicLattice.Site L m i') : FourTorus L m) = _
  rw [h]
  rfl
theorem sitesInBlock_finite {y : PeriodicLattice.Site L m i} (h : (unitBlock y).Finite) :
    (sitesInBlock i' y).Finite :=
  h.preimage Subtype.val_injective.injOn
theorem weight_smul_finsum_const (hL : L ≠ 0) {y : PeriodicLattice.Site L m i}
    (hsub : unitBlock y ⊆ (sublattice L m i' : Set (FourTorus L m)))
    (hcard : (unitBlock y).ncard = L ^ 4) (v : Matrices.ComplexMatrix2) :
    inverseFourthPowerWeight L • ∑ᶠ _x ∈ sitesInBlock i' y, v = v := by
  have hpos : 0 < (unitBlock y).ncard := by
    rw [hcard]
    exact pow_pos (Nat.pos_of_ne_zero hL) 4
  have hfin : (sitesInBlock i' y).Finite := sitesInBlock_finite (Set.finite_of_ncard_pos hpos)
  have himage : Subtype.val '' (sitesInBlock i' y) = unitBlock y := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      exact ⟨⟨p, hsub hp⟩, hp, rfl⟩
  have hN : (sitesInBlock i' y).ncard = L ^ 4 := by
    rw [← hcard, ← himage, Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const,
    ← Set.ncard_eq_toFinset_card _ hfin, hN, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have e : inverseFourthPowerWeight L * ((L ^ 4 : ℕ) : ℂ) = 1 := by
    have e' : (L : ℝ) ^ (-4 : ℤ) * ((L ^ 4 : ℕ) : ℝ) = 1 := by
      rw [zpow_neg]
      push_cast
      rw [show ((4 : ℤ)) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
      exact inv_mul_cancel₀ (pow_ne_zero 4 hL')
    unfold inverseFourthPowerWeight
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) e'
  rw [e, one_smul]
end GradientSums
theorem oneStepIdentities_of_blocks {L n k j : ℕ} (hL : L ≠ 0)
    (hsites : ∀ y : Vertex L n k (j + 1), BlockEqOffsetImage L n k (j + 1) y)
    (hsort : BlocksPartitionFiner L n k (j + 1))
    (htrans : ∀ (c : Edge L n k (j + 1)) (μ : Fin 4), BondAlongAxis c μ →
      BlockShiftAlongBond L n k (j + 1) c μ)
    (hends : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j), (x : FourTorus L n) ∈ unitBlock y →
      ∀ Γ ∈ contourSet y x, PeriodicLattice.IsBondPathFromTo Γ (y.toSublattice (levelDepth k j)) x) :
    OneStepIdentities L n k j := by
  have hle : sublattice L n (levelDepth k (j + 1)) ≤ sublattice L n (levelDepth k j) :=
    PeriodicLattice.sublattice_mono (Nat.pos_of_ne_zero hL) n
      (by simp only [levelDepth]; push_cast; omega)
  have hsub : ∀ y : Vertex L n k (j + 1),
      unitBlock y ⊆ (sublattice L n (levelDepth k j) : Set (FourTorus L n)) :=
    fun y => (hsites y).2.2.2
  have hcard : ∀ y : Vertex L n k (j + 1), (unitBlock y).ncard = L ^ 4 := fun y => (hsites y).2.2.1
  have hfin : ∀ y : Vertex L n k (j + 1), (sitesInBlock (levelDepth k j) y).Finite := fun y =>
    sitesInBlock_finite (Set.finite_of_ncard_pos (by
      rw [hcard]; exact pow_pos (Nat.pos_of_ne_zero hL) 4))
  have hw : ∀ (y : Vertex L n k (j + 1)) (v : Matrices.ComplexMatrix2),
      inverseFourthPowerWeight L • ∑ᶠ _x ∈ sitesInBlock (levelDepth k j) y, v = v := fun y v =>
    weight_smul_finsum_const hL (hsub y) (hcard y) v
  have hbij : ∀ c : Edge L n k (j + 1),
      BijOn (shiftAcross c : Vertex L n k j → Vertex L n k j)
        (sitesInBlock (levelDepth k j) c.source) (sitesInBlock (levelDepth k j) c.target) := by
    intro c
    obtain ⟨μ, hμ⟩ := c.isNeighbour
    have hb := (htrans c μ hμ).1
    refine ⟨fun x hx => ?_, fun x _ x' _ h => ?_, fun x' hx' => ?_⟩
    · show ((shiftAcross c x : Vertex L n k j) : FourTorus L n) ∈ unitBlock c.target
      rw [coe_shiftAcross hle]
      exact hb.mapsTo hx
    · exact add_right_cancel (b := (c.target - c.source).toSublattice (levelDepth k j)) h
    · obtain ⟨z, hz, e⟩ := hb.surjOn hx'
      refine ⟨⟨z, hsub _ hz⟩, hz, Subtype.ext ?_⟩
      rw [coe_shiftAcross hle]
      exact e
  have hpath : ∀ (f : Vertex L n k j → Matrices.ComplexMatrix2) (c : Edge L n k (j + 1))
      (x : Vertex L n k j), x ∈ sitesInBlock (levelDepth k j) c.source →
      edgeFormPathSum (vertexCoboundary f) (crossingPath c x) = f (shiftAcross c x) - f x := by
    intro f c x hx
    obtain ⟨μ, hμ⟩ := c.isNeighbour
    obtain ⟨-, ⟨t, -, ht⟩, -⟩ :=
      (htrans c μ hμ).2 x (shiftAcross c x) hx (coe_shiftAcross hle c x)
    exact sumAlong_axialPath_of_gradient f ht
  have hmean : ∀ (f : Vertex L n k j → Matrices.ComplexMatrix2) (y : Vertex L n k (j + 1))
      (x : Vertex L n k j), x ∈ sitesInBlock (levelDepth k j) y →
      contourFormAverage (vertexCoboundary f) y x = f x - f (y.toSublattice (levelDepth k j)) :=
    fun f y x hx => contourFormAverage_of_gradient f (hends y x hx)
  refine ⟨fun B _ => ?_, fun f _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · funext c
    have hs := hfin c.source
    have e : ∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.source,
        contourFormAverage B c.target (shiftAcross c x : Vertex L n k j) =
        ∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.target, contourFormAverage B c.target x :=
      finsum_mem_eq_of_bijOn _ (hbij c) fun _ _ => rfl
    show inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.source,
        (contourFormAverage B c.source x + bondFormSumAlong B (crossingPath c x) -
          contourFormAverage B c.target (shiftAcross c x : Vertex L n k j)) =
      inverseFourthPowerWeight L •
          (∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.source, bondFormSumAlong B (crossingPath c x)) -
        (inverseFourthPowerWeight L •
            (∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.target, contourFormAverage B c.target x) -
          inverseFourthPowerWeight L •
            ∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.source, contourFormAverage B c.source x)
    rw [finsum_mem_sub_distrib _ _ hs, finsum_mem_add_distrib hs, e]
    simp only [smul_sub, smul_add]
    abel
  · funext c
    have e : ∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.source,
        (contourFormAverage (vertexCoboundary f) c.source x +
            bondFormSumAlong (vertexCoboundary f) (crossingPath c x) -
          contourFormAverage (vertexCoboundary f) c.target (shiftAcross c x : Vertex L n k j)) =
        ∑ᶠ _x ∈ sitesInBlock (levelDepth k j) c.source,
          (f (c.target.toSublattice (levelDepth k j)) - f (c.source.toSublattice (levelDepth k j))) := by
      refine finsum_mem_congr rfl fun x hx => ?_
      have h1 := hmean f c.source x hx
      have h2 : bondFormSumAlong (vertexCoboundary f) (crossingPath c x) = _ := hpath f c x hx
      have h3 := hmean f c.target _ ((hbij c).mapsTo hx)
      rw [h1, h2, h3]
      abel
    show inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.source,
        (contourFormAverage (vertexCoboundary f) c.source x +
            bondFormSumAlong (vertexCoboundary f) (crossingPath c x) -
          contourFormAverage (vertexCoboundary f) c.target (shiftAcross c x : Vertex L n k j)) =
      f (c.target.toSublattice (levelDepth k j)) - f (c.source.toSublattice (levelDepth k j))
    rw [e, hw]
  · funext c
    have hs := hfin c.source
    have e : ∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.source,
        edgeFormPathSum (vertexCoboundary f) (crossingPath c x) =
        ∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.source,
          (f (shiftAcross c x : Vertex L n k j) - f x) :=
      finsum_mem_congr rfl fun x hx => hpath f c x hx
    have e' : ∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.source, f (shiftAcross c x : Vertex L n k j) =
        ∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.target, f x :=
      finsum_mem_eq_of_bijOn _ (hbij c) fun _ _ => rfl
    show inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.source,
        edgeFormPathSum (vertexCoboundary f) (crossingPath c x) =
      inverseFourthPowerWeight L • (∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.target, f x) -
        inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.source, f x
    rw [e, finsum_mem_sub_distrib _ _ hs, e', smul_sub]
  · funext y
    have hs := hfin y
    have e : ∑ᶠ x ∈ sitesInBlock (levelDepth k j) y, contourFormAverage (vertexCoboundary f) y x =
        ∑ᶠ x ∈ sitesInBlock (levelDepth k j) y, (f x - f (y.toSublattice (levelDepth k j))) :=
      finsum_mem_congr rfl fun x hx => hmean f y x hx
    show inverseFourthPowerWeight L •
        ∑ᶠ x ∈ sitesInBlock (levelDepth k j) y, contourFormAverage (vertexCoboundary f) y x =
      inverseFourthPowerWeight L • (∑ᶠ x ∈ sitesInBlock (levelDepth k j) y, f x) -
        f (y.toSublattice (levelDepth k j))
    rw [e, finsum_mem_sub_distrib _ _ hs, smul_sub, hw]
  · intro y x hx hne
    have hspec : x.1 ∈ sitesInBlock (levelDepth k j) (cubeCentre x) ∧
        (x.1 : FourTorus L n) ≠ (cubeCentre x : Vertex L n k (j + 1)) :=
      Classical.epsilon_spec
        (p := fun y : Vertex L n k (j + 1) =>
          x.1 ∈ sitesInBlock (levelDepth k j) y ∧ (x.1 : FourTorus L n) ≠ y) ⟨y, hx, hne⟩
    have hy : cubeCentre x = y := (hsort.2.1 x.1).unique hspec.1 hx
    show contourFormAverage (vertexCoboundary f) (cubeCentre x) x.1 = _
    rw [hy]
    exact hmean f y x.1 hx
theorem oneStepIdentitiesHold_of_blockStructure (h₁ : BlockStructure) (h₂ : ContourEndpoints) :
    OneStepIdentitiesHold := by
  intro L hL n k j hn hj
  have hL0 : L ≠ 0 := by
    have := hL.2
    omega
  obtain ⟨hs, hb, ht, -⟩ := (h₁ L k (j + 1) hL (by omega) (by omega) (by omega)).1 n hn
  exact oneStepIdentities_of_blocks hL0 hs hb ht
    ((h₂ L k (j + 1) hL (by omega) (by omega) (by omega)).1 n hn)
end YangMills.Construction.Tower.TrivialLinearization
end

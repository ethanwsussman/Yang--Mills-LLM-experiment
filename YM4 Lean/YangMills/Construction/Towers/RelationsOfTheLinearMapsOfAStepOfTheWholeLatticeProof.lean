import YangMills.Construction.Towers.BlocksCorridorsPivotBondsAndPathsProof
import YangMills.Construction.Towers.BlocksOfATower
import YangMills.Construction.Towers.EndPointsOfTheContours
import YangMills.Construction.Towers.RelationsOfTheLinearMapsOfAStepOfTheWholeLattice
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.OneStepProof
open InfiniteLattice (AmbientSpace)
section Paths
variable {a a' : ℝ}
theorem sumAlong_forwardSteps (f : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2)
    (μ : Fin 4) (N : ℕ) :
    ∀ p : InfiniteLattice.LatticePoint a,
      sumAlong (fun e => f e.terminal - f e.initial) (forwardSteps p μ N) =
        f (p + N • InfiniteLattice.axisStep a μ) - f p := by
  induction N with
  | zero => intro p; simp [forwardSteps, sumAlong]
  | succ N ih =>
    intro p
    have hrec := ih (p + InfiniteLattice.axisStep a μ)
    have hshift : p + InfiniteLattice.axisStep a μ + N • InfiniteLattice.axisStep a μ =
        p + (N + 1) • InfiniteLattice.axisStep a μ := by
      rw [succ_nsmul]; abel
    rw [hshift] at hrec
    unfold sumAlong at hrec ⊢
    simp only [forwardSteps, List.map_cons, List.sum_cons, hrec]
    show f (p + InfiniteLattice.axisStep a μ) - f p + _ = _
    abel
theorem sumAlong_backwardSteps (f : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2)
    (μ : Fin 4) (N : ℕ) :
    ∀ p : InfiniteLattice.LatticePoint a,
      sumAlong (fun e => f e.terminal - f e.initial) (backwardSteps p μ N) =
        f (p - N • InfiniteLattice.axisStep a μ) - f p := by
  induction N with
  | zero => intro p; simp [backwardSteps, sumAlong]
  | succ N ih =>
    intro p
    have hrec := ih (p - InfiniteLattice.axisStep a μ)
    have hshift : p - InfiniteLattice.axisStep a μ - N • InfiniteLattice.axisStep a μ =
        p - (N + 1) • InfiniteLattice.axisStep a μ := by
      rw [succ_nsmul]; abel
    rw [hshift] at hrec
    unfold sumAlong at hrec ⊢
    simp only [backwardSteps, List.map_cons, List.sum_cons, hrec]
    show f (p - InfiniteLattice.axisStep a μ) - f p + _ = _
    abel
theorem sumAlong_signedSteps (f : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2)
    (μ : Fin 4) (m : ℤ) (p : InfiniteLattice.LatticePoint a) :
    sumAlong (fun e => f e.terminal - f e.initial) (signedSteps p μ m) =
      f (p + m • InfiniteLattice.axisStep a μ) - f p := by
  unfold signedSteps
  split_ifs with hm
  · have hcast : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
    have hsmul : m.toNat • InfiniteLattice.axisStep a μ = m • InfiniteLattice.axisStep a μ := by
      rw [← natCast_zsmul, hcast]
    rw [sumAlong_forwardSteps, hsmul]
  · have hcast : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (by omega)
    have hsmul : p - (-m).toNat • InfiniteLattice.axisStep a μ =
        p + m • InfiniteLattice.axisStep a μ := by
      rw [← natCast_zsmul, hcast, neg_smul, sub_neg_eq_add]
    rw [sumAlong_backwardSteps, hsmul]
theorem sumAlong_axisPath (f : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2)
    {p q : InfiniteLattice.LatticePoint a} {μ : Fin 4} {t : ℤ} (hpq : IsAxisDisplacement p q μ t) :
    sumAlong (fun e => f e.terminal - f e.initial) (axisPath p q) = f q - f p := by
  have hex : ∃ r : Fin 4 × ℤ, IsAxisDisplacement p q r.1 r.2 := ⟨(μ, t), hpq⟩
  unfold axisPath
  rw [dif_pos hex, sumAlong_signedSteps]
  have hdiff : q - p = hex.choose.2 • InfiniteLattice.axisStep a hex.choose.1 := hex.choose_spec
  have hend : p + hex.choose.2 • InfiniteLattice.axisStep a hex.choose.1 = q := by
    rw [← hdiff]; abel
  rw [hend]
theorem sumAlong_of_linksJoin (f : InfiniteLattice.LatticePoint a' → Matrices.ComplexMatrix2)
    (Γ : List (InfiniteLattice.Link a')) :
    ∀ p q : InfiniteLattice.LatticePoint a', LinksJoin (p : AmbientSpace) (q : AmbientSpace) Γ →
      sumAlong (fun e => f e.terminal - f e.initial) Γ = f q - f p := by
  induction Γ with
  | nil =>
    intro p q hjoin
    have hpq : p = q := Subtype.ext hjoin
    subst hpq
    simp [sumAlong]
  | cons e Γ ih =>
    intro p q hjoin
    have hsplit : (e.initial : AmbientSpace) = p ∧
        LinksJoin (e.terminal : AmbientSpace) (q : AmbientSpace) Γ := hjoin
    have hstart : e.initial = p := Subtype.ext hsplit.1
    subst hstart
    have hrest := ih e.terminal q hsplit.2
    unfold sumAlong at hrest ⊢
    simp only [List.map_cons, List.sum_cons, hrest]
    abel
theorem contourAverage_of_coboundary (L : ℕ)
    (f : InfiniteLattice.LatticePoint a' → Matrices.ComplexMatrix2)
    {y : InfiniteLattice.LatticePoint a} {x y' : InfiniteLattice.LatticePoint a'}
    (hy : (y' : AmbientSpace) = y)
    (hjoin : ∀ Γ ∈ contourSet L y x, LinksJoin (y : AmbientSpace) (x : AmbientSpace) Γ) :
    _root_.YangMills.Construction.Tower.FullSpace.contourAverage L (fun e => f e.terminal - f e.initial) y x = f x - f y' := by
  have hval : ∀ σ, sumAlong (fun e => f e.terminal - f e.initial) (contour L y x σ) =
      f x - f y' := fun σ =>
    sumAlong_of_linksJoin f _ _ _ (by rw [hy]; exact hjoin _ ⟨σ, rfl⟩)
  have hcard : Fintype.card (ContourOrder L y x) ≠ 0 := by
    have : Nonempty (ContourOrder L y x) := ⟨(Finset.equivFin _).symm⟩
    exact Fintype.card_ne_zero
  unfold _root_.YangMills.Construction.Tower.FullSpace.contourAverage
  simp only [hval, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hone : (((Fintype.card (ContourOrder L y x) : ℝ)⁻¹ : ℝ) : ℂ) *
      (Fintype.card (ContourOrder L y x) : ℂ) = 1 := by
    push_cast
    exact inv_mul_cancel₀ (by exact_mod_cast hcard)
  rw [hone, one_smul]
theorem coe_toFiner {y : InfiniteLattice.LatticePoint a}
    (hy : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a') :
    ((toFiner a' y : InfiniteLattice.LatticePoint a') : AmbientSpace) = y := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.coe_toFiner <;> assumption
theorem coe_shifted (c : InfiniteLattice.Link a) (x : InfiniteLattice.LatticePoint a')
    (hc : ((c.terminal - c.initial : InfiniteLattice.LatticePoint a) : AmbientSpace) ∈
      InfiniteLattice.latticeSubgroup a') :
    ((shifted c x : InfiniteLattice.LatticePoint a') : AmbientSpace) =
      (x : AmbientSpace) + ((c.terminal : AmbientSpace) - (c.initial : AmbientSpace)) := by
  show (x : AmbientSpace) +
      ((toFiner a' (c.terminal - c.initial) : InfiniteLattice.LatticePoint a') : AmbientSpace) = _
  rw [coe_toFiner hc]
  rfl
theorem cubeVertices_finite {L : ℕ} {y : InfiniteLattice.LatticePoint a}
    (hfin : (cube L a' y).Finite) :
    (cubeVertices L a' y).Finite :=
  hfin.preimage Subtype.val_injective.injOn
theorem weight_smul_finsum_const {L : ℕ} (hL : L ≠ 0) {y : InfiniteLattice.LatticePoint a}
    (hsub : cube L a' y ⊆ (InfiniteLattice.latticeSubgroup a' : Set AmbientSpace))
    (hcard : (cube L a' y).ncard = L ^ 4) (v : Matrices.ComplexMatrix2) :
    PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ _x ∈ cubeVertices L a' y, v = v := by
  have hpos : 0 < (cube L a' y).ncard := by
    rw [hcard]
    exact pow_pos (Nat.pos_of_ne_zero hL) 4
  have hfin : (cubeVertices L a' y).Finite :=
    cubeVertices_finite (Set.finite_of_ncard_pos hpos)
  have himage : Subtype.val '' (cubeVertices L a' y) = cube L a' y := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      exact ⟨⟨p, hsub hp⟩, hp, rfl⟩
  have hm : (cubeVertices L a' y).ncard = L ^ 4 := by
    rw [← hcard, ← himage, Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const,
    ← Set.ncard_eq_toFinset_card _ hfin, hm, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have hone : PeriodicLattice.inverseFourthPowerWeight L * ((L ^ 4 : ℕ) : ℂ) = 1 := by
    have hreal : (L : ℝ) ^ (-4 : ℤ) * ((L ^ 4 : ℕ) : ℝ) = 1 := by
      rw [zpow_neg]
      push_cast
      rw [show ((4 : ℤ)) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
      exact inv_mul_cancel₀ (pow_ne_zero 4 hL')
    unfold PeriodicLattice.inverseFourthPowerWeight
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hreal
  rw [hone, one_smul]
end Paths
open TrivialLinearization
theorem oneStepIdentities_of_cubes {L k j : ℕ} (hL : L ≠ 0)
    (hverts : ∀ y : Vertex L k (j + 1), BlockEqOffsetImage L k (j + 1) y)
    (hpart : BlocksPartitionFiner L k (j + 1))
    (hshift : ∀ (c : Edge L k (j + 1)) (μ : Fin 4), BondAlongAxis c μ →
      BlockTranslateAlongBond L k (j + 1) c μ)
    (hends : ∀ (y : Vertex L k (j + 1)) (x : Vertex L k j),
      (x : AmbientSpace) ∈ cube L (meshAt L k j) y →
      ∀ Γ ∈ contourSet L y x, LinksJoin (y : AmbientSpace) (x : AmbientSpace) Γ) :
    OneStepIdentities L k j := by
  have hsub : ∀ y : Vertex L k (j + 1),
      cube L (meshAt L k j) y ⊆
        (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) :=
    fun y => (hverts y).2.2.2
  have hcard : ∀ y : Vertex L k (j + 1), (cube L (meshAt L k j) y).ncard = L ^ 4 :=
    fun y => (hverts y).2.2.1
  have hL1 : (1 : ℤ) ≤ (L : ℤ) := by omega
  have hcentre : ∀ y : Vertex L k (j + 1), (y : AmbientSpace) ∈ cube L (meshAt L k j) y := by
    intro y
    show ∃ ν : Fin 4 → ℤ, (∀ μ, 2 * |ν μ| ≤ (L : ℤ) ^ 1 - 1) ∧
      (y : AmbientSpace) = (y : AmbientSpace) + ∑ μ, Pi.single μ ((ν μ : ℝ) * meshAt L k j)
    refine ⟨0, fun μ => ?_, ?_⟩
    · simpa using hL1
    · simp
  have hfine : ∀ y : Vertex L k (j + 1),
      (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup (meshAt L k j) :=
    fun y => hsub y (hcentre y)
  have hdiff : ∀ c : Edge L k (j + 1),
      ((c.terminal - c.initial : Vertex L k (j + 1)) : AmbientSpace) ∈
        InfiniteLattice.latticeSubgroup (meshAt L k j) := fun c => by
    rw [AddSubgroup.coe_sub]
    exact (InfiniteLattice.latticeSubgroup _).sub_mem (hfine _) (hfine _)
  have hfin : ∀ y : Vertex L k (j + 1), (cubeVertices L (meshAt L k j) y).Finite := fun y =>
    cubeVertices_finite (Set.finite_of_ncard_pos (by
      rw [hcard]; exact pow_pos (Nat.pos_of_ne_zero hL) 4))
  have hw : ∀ (y : Vertex L k (j + 1)) (v : Matrices.ComplexMatrix2),
      PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ _x ∈ cubeVertices L (meshAt L k j) y, v = v :=
    fun y v => weight_smul_finsum_const hL (hsub y) (hcard y) v
  have hbij : ∀ c : Edge L k (j + 1),
      BijOn (shifted c : Vertex L k j → Vertex L k j)
        (cubeVertices L (meshAt L k j) c.initial) (cubeVertices L (meshAt L k j) c.terminal) := by
    intro c
    obtain ⟨μ, hμ⟩ := c.isAdjacent
    have hb := (hshift c μ hμ).1
    refine ⟨fun x hx => ?_, fun x _ x' _ h => ?_, fun x' hx' => ?_⟩
    · show ((shifted c x : Vertex L k j) : AmbientSpace) ∈ cube L (meshAt L k j) c.terminal
      rw [coe_shifted c x (hdiff c)]
      exact hb.mapsTo hx
    · exact add_right_cancel (b := toFiner (meshAt L k j) (c.terminal - c.initial)) h
    · obtain ⟨z, hz, hzx⟩ := hb.surjOn hx'
      refine ⟨⟨z, hsub _ hz⟩, hz, Subtype.ext ?_⟩
      rw [coe_shifted c _ (hdiff c)]
      exact hzx
  have hpath : ∀ (f : Vertex L k j → Matrices.ComplexMatrix2) (c : Edge L k (j + 1))
      (x : Vertex L k j), x ∈ cubeVertices L (meshAt L k j) c.initial →
      edgeFormPathSum (vertexCoboundary f) (crossingPath c x) = f (shifted c x) - f x := by
    intro f c x hx
    obtain ⟨μ, hμ⟩ := c.isAdjacent
    obtain ⟨-, ⟨t, -, ht⟩, -⟩ :=
      (hshift c μ hμ).2 x (shifted c x) hx (coe_shifted c x (hdiff c))
    exact sumAlong_axisPath f ht
  have hmean : ∀ (f : Vertex L k j → Matrices.ComplexMatrix2) (y : Vertex L k (j + 1))
      (x : Vertex L k j), x ∈ cubeVertices L (meshAt L k j) y →
      _root_.YangMills.Construction.Tower.FullSpace.contourAverage L (vertexCoboundary f) y x = f x - f (toFiner (meshAt L k j) y) :=
    fun f y x hx =>
      contourAverage_of_coboundary L f (coe_toFiner (hfine y)) (hends y x hx)
  refine ⟨fun B _ => ?_, fun f _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · funext c
    have hs := hfin c.initial
    have hre : ∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.initial,
        _root_.YangMills.Construction.Tower.FullSpace.contourAverage L B c.terminal (shifted c x : Vertex L k j) =
        ∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.terminal, _root_.YangMills.Construction.Tower.FullSpace.contourAverage L B c.terminal x :=
      finsum_mem_eq_of_bijOn _ (hbij c) fun _ _ => rfl
    show PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.initial,
        (_root_.YangMills.Construction.Tower.FullSpace.contourAverage L B c.initial x + sumAlong B (crossingPath c x) -
          _root_.YangMills.Construction.Tower.FullSpace.contourAverage L B c.terminal (shifted c x : Vertex L k j)) =
      PeriodicLattice.inverseFourthPowerWeight L •
          (∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.initial, sumAlong B (crossingPath c x)) -
        (PeriodicLattice.inverseFourthPowerWeight L •
            (∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.terminal, _root_.YangMills.Construction.Tower.FullSpace.contourAverage L B c.terminal x) -
          PeriodicLattice.inverseFourthPowerWeight L •
            ∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.initial, _root_.YangMills.Construction.Tower.FullSpace.contourAverage L B c.initial x)
    rw [finsum_mem_sub_distrib _ _ hs, finsum_mem_add_distrib hs, hre]
    simp only [smul_sub, smul_add]
    abel
  · funext c
    have hre : ∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.initial,
        (contourAverage L (vertexCoboundary f) c.initial x +
            sumAlong (vertexCoboundary f) (crossingPath c x) -
          contourAverage L (vertexCoboundary f) c.terminal (shifted c x : Vertex L k j)) =
        ∑ᶠ _x ∈ cubeVertices L (meshAt L k j) c.initial,
          (f (toFiner (meshAt L k j) c.terminal) - f (toFiner (meshAt L k j) c.initial)) := by
      refine finsum_mem_congr rfl fun x hx => ?_
      have h1 := hmean f c.initial x hx
      have h2 : sumAlong (vertexCoboundary f) (crossingPath c x) = _ := hpath f c x hx
      have h3 := hmean f c.terminal _ ((hbij c).mapsTo hx)
      rw [h1, h2, h3]
      abel
    show PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.initial,
        (contourAverage L (vertexCoboundary f) c.initial x +
            sumAlong (vertexCoboundary f) (crossingPath c x) -
          contourAverage L (vertexCoboundary f) c.terminal (shifted c x : Vertex L k j)) =
      f (toFiner (meshAt L k j) c.terminal) - f (toFiner (meshAt L k j) c.initial)
    rw [hre, hw]
  · funext c
    have hs := hfin c.initial
    have hre : ∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.initial,
        edgeFormPathSum (vertexCoboundary f) (crossingPath c x) =
        ∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.initial,
          (f (shifted c x : Vertex L k j) - f x) :=
      finsum_mem_congr rfl fun x hx => hpath f c x hx
    have hre' : ∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.initial,
        f (shifted c x : Vertex L k j) =
        ∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.terminal, f x :=
      finsum_mem_eq_of_bijOn _ (hbij c) fun _ _ => rfl
    show PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.initial,
        edgeFormPathSum (vertexCoboundary f) (crossingPath c x) =
      PeriodicLattice.inverseFourthPowerWeight L •
          (∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.terminal, f x) -
        PeriodicLattice.inverseFourthPowerWeight L •
          ∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.initial, f x
    rw [hre, finsum_mem_sub_distrib _ _ hs, hre', smul_sub]
  · funext y
    have hs := hfin y
    have hre : ∑ᶠ x ∈ cubeVertices L (meshAt L k j) y,
        _root_.YangMills.Construction.Tower.FullSpace.contourAverage L (vertexCoboundary f) y x =
        ∑ᶠ x ∈ cubeVertices L (meshAt L k j) y, (f x - f (toFiner (meshAt L k j) y)) :=
      finsum_mem_congr rfl fun x hx => hmean f y x hx
    show PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ x ∈ cubeVertices L (meshAt L k j) y, _root_.YangMills.Construction.Tower.FullSpace.contourAverage L (vertexCoboundary f) y x =
      PeriodicLattice.inverseFourthPowerWeight L •
          (∑ᶠ x ∈ cubeVertices L (meshAt L k j) y, f x) -
        f (toFiner (meshAt L k j) y)
    rw [hre, finsum_mem_sub_distrib _ _ hs, smul_sub, hw]
  · intro y x hx hne
    have hspec : x.1 ∈ cubeVertices L (meshAt L k j) (cubeCentre L x) ∧
        (x.1 : AmbientSpace) ≠ (cubeCentre L x : Vertex L k (j + 1)) :=
      Classical.epsilon_spec
        (p := fun y : Vertex L k (j + 1) =>
          x.1 ∈ cubeVertices L (meshAt L k j) y ∧ (x.1 : AmbientSpace) ≠ y) ⟨y, hx, hne⟩
    have hy : cubeCentre L x = y := (hpart.2.1 x.1).unique hspec.1 hx
    show _root_.YangMills.Construction.Tower.FullSpace.contourAverage L (vertexCoboundary f) (cubeCentre L x) x.1 = _
    rw [hy]
    exact hmean f y x.1 hx
theorem oneStepIdentitiesHold (hcubes : BlockStructure) (hends : ContourEndpoints) :
    OneStepIdentitiesHold := by
  intro L hL k j hj
  have hL0 : L ≠ 0 := by
    have := hL.2
    omega
  obtain ⟨-, hs, hb, ht, -⟩ := hcubes L k (j + 1) hL (by omega) (by omega) (by omega)
  exact oneStepIdentities_of_cubes hL0 hs hb ht
    ((hends L k (j + 1) hL (by omega) (by omega) (by omega)).2)
end YangMills.Construction.Tower.FullSpace.OneStepProof
end

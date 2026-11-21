import YangMills.Construction.ChessboardTori.FromTheInfiniteLatticeToTheTorusProof
import YangMills.Construction.ChessboardTori.InducedMapsProof
import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLatticeAtOneSpacingProof
import YangMills.Construction.InfiniteLattice.WilsonKernelOfBondsWithOneOrientation
import YangMills.Construction.LawInAState.GridDataAtEveryExponentProofForm
import Mathlib
set_option autoImplicit false
open Set MeasureTheory Function
noncomputable section
namespace YangMills.Construction.ChessboardTori.LiftingRules
open InfiniteLattice (AmbientSpace)
open TestFunctions (latticeTranslate)
open Matrices (ComplexMatrix2)
theorem card_translates_in_cube_le {ℓ : ℝ} (hℓ : 0 < ℓ) (δ : ℝ) :
    ∃ N : ℕ, ∀ x : AmbientSpace, ∃ K : Finset (Fin 4 → ℤ), K.card ≤ N ∧
      ∀ k : Fin 4 → ℤ, (∀ μ, |(x + latticeTranslate ℓ k) μ| ≤ δ) → k ∈ K := by
  refine ⟨(⌈2 * δ / ℓ⌉₊ + 1) ^ 4, fun x => ?_⟩
  refine ⟨Fintype.piFinset fun μ => Finset.Icc ⌈(-δ - x μ) / ℓ⌉ ⌊(δ - x μ) / ℓ⌋, ?_, fun k hk => ?_⟩
  · rw [Fintype.card_piFinset]
    have hb : ∀ μ : Fin 4, (Finset.Icc ⌈(-δ - x μ) / ℓ⌉ ⌊(δ - x μ) / ℓ⌋).card ≤ ⌈2 * δ / ℓ⌉₊ + 1 := by
      intro μ
      rw [Int.card_Icc, Int.toNat_le]
      have h1 : ((⌊(δ - x μ) / ℓ⌋ : ℤ) : ℝ) ≤ (δ - x μ) / ℓ := Int.floor_le _
      have h2 : (-δ - x μ) / ℓ ≤ ((⌈(-δ - x μ) / ℓ⌉ : ℤ) : ℝ) := Int.le_ceil _
      have h3 : 2 * δ / ℓ ≤ (⌈2 * δ / ℓ⌉₊ : ℝ) := Nat.le_ceil _
      have h4 : (δ - x μ) / ℓ - (-δ - x μ) / ℓ = 2 * δ / ℓ := by ring
      have h5 : ((⌊(δ - x μ) / ℓ⌋ - ⌈(-δ - x μ) / ℓ⌉ : ℤ) : ℝ) ≤ ((⌈2 * δ / ℓ⌉₊ : ℤ) : ℝ) := by
        push_cast
        linarith
      have h6 : ⌊(δ - x μ) / ℓ⌋ - ⌈(-δ - x μ) / ℓ⌉ ≤ (⌈2 * δ / ℓ⌉₊ : ℤ) := by exact_mod_cast h5
      push_cast
      omega
    calc ∏ μ : Fin 4, (Finset.Icc ⌈(-δ - x μ) / ℓ⌉ ⌊(δ - x μ) / ℓ⌋).card
        ≤ ∏ _μ : Fin 4, (⌈2 * δ / ℓ⌉₊ + 1) := Finset.prod_le_prod' fun μ _ => hb μ
      _ = (⌈2 * δ / ℓ⌉₊ + 1) ^ 4 := by simp
  · rw [Fintype.mem_piFinset]
    intro μ
    have h := abs_le.mp (hk μ)
    have h1 : -δ ≤ x μ + ℓ * (k μ : ℝ) := h.1
    have h2 : x μ + ℓ * (k μ : ℝ) ≤ δ := h.2
    rw [Finset.mem_Icc]
    constructor
    · apply Int.ceil_le.mpr
      rw [div_le_iff₀ hℓ]
      linarith
    · apply Int.le_floor.mpr
      rw [le_div_iff₀ hℓ]
      linarith
theorem exists_cube_of_hasBoundedSupport {v : AmbientSpace → ℂ}
    (hv : ChessboardSetup.HasBoundedSupport v) :
    ∃ δ : ℝ, ∀ x, v x ≠ 0 → ∀ μ, |x μ| ≤ δ := by
  obtain ⟨S, hS, h⟩ := hv
  obtain ⟨r, hr⟩ := hS.subset_closedBall 0
  refine ⟨r, fun x hx μ => ?_⟩
  have hxS : x ∈ S := by
    by_contra hc
    exact hx (h x hc)
  have h1 : ‖x‖ ≤ r := by simpa using hr hxS
  have h2 : ‖x μ‖ ≤ ‖x‖ := norm_le_pi_norm x μ
  rw [Real.norm_eq_abs] at h2
  exact h2.trans h1
theorem card_support_translates_le {ℓ : ℝ} (hℓ : 0 < ℓ) {v : AmbientSpace → ℂ}
    (hv : ChessboardSetup.HasBoundedSupport v) :
    ∃ N : ℕ, ∀ x : AmbientSpace, ∃ K : Finset (Fin 4 → ℤ), K.card ≤ N ∧
      support (fun k => v (x + latticeTranslate ℓ k)) ⊆ K := by
  obtain ⟨δ, hδ⟩ := exists_cube_of_hasBoundedSupport hv
  obtain ⟨N, hN⟩ := card_translates_in_cube_le hℓ δ
  refine ⟨N, fun x => ?_⟩
  obtain ⟨K, hK, h⟩ := hN x
  exact ⟨K, hK, fun k hk => h k (hδ _ hk)⟩
namespace PlaquetteFibres
variable (D : ChessboardSetup)
theorem torusPeriod_pos : 0 < D.torusPeriod :=
  mul_pos two_pos (pow_pos (by linarith [D.one_lt_factor]) _)
theorem L_pos : 0 < D.L := by apply _root_.YangMills.Construction.ChessboardTori.InducedQuotientMaps.L_pos <;> assumption
theorem periodize_bounded {v : AmbientSpace → ℂ} (hb : ∃ C : ℝ, ∀ x, ‖v x‖ ≤ C)
    (hv : ChessboardSetup.HasBoundedSupport v) : ∃ C : ℝ, ∀ x, ‖D.periodize v x‖ ≤ C := by
  classical
  obtain ⟨C, hC⟩ := hb
  obtain ⟨N, hN⟩ := card_support_translates_le (torusPeriod_pos D) hv
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨N * C, fun x => ?_⟩
  obtain ⟨K, hK, hs⟩ := hN x
  have e : D.periodize v x = ∑ k ∈ K, v (x + latticeTranslate D.torusPeriod k) :=
    finsum_eq_sum_of_support_subset _ hs
  rw [e]
  calc ‖∑ k ∈ K, v (x + latticeTranslate D.torusPeriod k)‖ ≤ ∑ _k ∈ K, C :=
        norm_sum_le_of_le _ fun k _ => hC _
    _ = K.card * C := by simp
    _ ≤ N * C := mul_le_mul_of_nonneg_right (by exact_mod_cast hK) hC0
theorem periodize_add_latticeTranslate (v : AmbientSpace → ℂ) (x : AmbientSpace) (k : Fin 4 → ℤ) :
    D.periodize v (x + latticeTranslate D.torusPeriod k) = D.periodize v x := by
  have h := finsum_comp_equiv (Equiv.addRight k)
    (f := fun c : Fin 4 → ℤ => v (x + latticeTranslate D.torusPeriod c))
  unfold ChessboardSetup.periodize
  rw [← h]
  refine finsum_congr fun c => ?_
  simp only [Equiv.coe_addRight, TestFunctions.latticeTranslate_add]
  congr 1
  abel
def latticeTranslatePoint (k : Fin 4 → ℤ) : InfiniteLattice.LatticePoint D.mesh :=
  ⟨latticeTranslate D.torusPeriod k, fun μ => 2 * (D.L : ℤ) ^ ((D.m : ℕ) + (D.K : ℕ)) * k μ, fun μ => by
    have h := SourcesAndGluing.torusSide_eq_intCast_mul_meshSize (L_pos D) D.m D.K
    have h' : D.torusPeriod = ((2 * (D.L : ℤ) ^ ((D.m : ℕ) + (D.K : ℕ)) : ℤ) : ℝ) * D.mesh := h
    simp only [latticeTranslate]
    rw [h']
    push_cast
    ring⟩
def shiftBy (p : D.Plaquette) (k : Fin 4 → ℤ) : D.Plaquette :=
  D.shiftPlaquette p (latticeTranslatePoint D k)
theorem projPlaquette_shiftBy (p : D.Plaquette) (k : Fin 4 → ℤ) :
    D.projPlaquette (shiftBy D p k) = D.projPlaquette p :=
  PeriodicLattice.Plaquette.ext
    (Subtype.ext (TestFunctions.torusProj_add_latticeTranslate D.torusPeriod (p.corner : AmbientSpace) k))
    rfl rfl
theorem exists_shiftBy_of_projPlaquette_eq {p p' : D.Plaquette}
    (h : D.projPlaquette p' = D.projPlaquette p) : ∃ k, p' = shiftBy D p k := by
  have hb : TorusMetric.torusProj D.torusPeriod (p'.corner : AmbientSpace) =
      TorusMetric.torusProj D.torusPeriod (p.corner : AmbientSpace) :=
    congrArg (fun q : D.PeriodicPlaquette => ((q.origin : PeriodicLattice.Site _ _ _) : D.Torus)) h
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq hb
  exact ⟨k, InfiniteLattice.ElementaryPlaquette.ext (Subtype.ext hk)
    (congrArg PeriodicLattice.Plaquette.firstAxis h) (congrArg PeriodicLattice.Plaquette.secondAxis h)⟩
theorem shiftBy_injective (p : D.Plaquette) : Injective (shiftBy D p) := by
  intro k k' h
  have h1 : (p.corner : AmbientSpace) + latticeTranslate D.torusPeriod k =
      (p.corner : AmbientSpace) + latticeTranslate D.torusPeriod k' :=
    congrArg (fun q : D.Plaquette => (q.corner : AmbientSpace)) h
  have h2 := add_left_cancel h1
  funext μ
  have h3 : D.torusPeriod * (k μ : ℝ) = D.torusPeriod * (k' μ : ℝ) := congrFun h2 μ
  exact_mod_cast mul_left_cancel₀ (torusPeriod_pos D).ne' h3
theorem center_shiftBy (p : D.Plaquette) (k : Fin 4 → ℤ) :
    (shiftBy D p k).center = p.center + latticeTranslate D.torusPeriod k := by
  change (p.corner : AmbientSpace) + latticeTranslate D.torusPeriod k + _ + _ =
    (p.corner : AmbientSpace) + _ + _ + _
  abel
def fibreEquiv (σ : D.PeriodicPlaquette → D.Plaquette) (hσ : ∀ q, D.projPlaquette (σ q) = q) :
    D.PeriodicPlaquette × (Fin 4 → ℤ) ≃ D.Plaquette :=
  Equiv.ofBijective (fun q => shiftBy D (σ q.1) q.2) (by
    constructor
    · rintro ⟨q, k⟩ ⟨q', k'⟩ h
      have h1 : q = q' := by
        have h2 := congrArg D.projPlaquette h
        simpa only [projPlaquette_shiftBy, hσ] using h2
      subst h1
      exact Prod.ext rfl (shiftBy_injective D _ h)
    · intro p
      obtain ⟨k, hk⟩ := exists_shiftBy_of_projPlaquette_eq D (hσ (D.projPlaquette p)).symm
      exact ⟨(D.projPlaquette p, k), hk.symm⟩)
theorem finite_support_center [Finite D.PeriodicPlaquette] (hsurj : Surjective D.projPlaquette)
    {v : AmbientSpace → ℂ} (hv : ChessboardSetup.HasBoundedSupport v) :
    {p : D.Plaquette | v p.center ≠ 0}.Finite := by
  classical
  obtain ⟨N, hN⟩ := card_support_translates_le (torusPeriod_pos D) hv
  have hσ := surjInv_eq hsurj
  have hk : ∀ q : D.PeriodicPlaquette,
      {k : Fin 4 → ℤ | v ((surjInv hsurj q).center + latticeTranslate D.torusPeriod k) ≠ 0}.Finite := by
    intro q
    obtain ⟨K, -, hs⟩ := hN (surjInv hsurj q).center
    exact K.finite_toSet.subset hs
  refine Set.Finite.subset ((finite_iUnion fun q => (hk q).image (fun k => (q, k))).image
    (fibreEquiv D (surjInv hsurj) hσ)) ?_
  intro p hp
  obtain ⟨⟨q, k⟩, rfl⟩ := (fibreEquiv D (surjInv hsurj) hσ).surjective p
  refine ⟨(q, k), mem_iUnion.2 ⟨q, k, ?_, rfl⟩, rfl⟩
  have h : v (shiftBy D (surjInv hsurj q) k).center ≠ 0 := hp
  rwa [center_shiftBy] at h
end PlaquetteFibres
section Covering
variable {L m : ℕ} {j : ℤ}
theorem projectPoint_add (x y : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L j)) :
    InfiniteLattice.projectPoint L m j (x + y) =
      InfiniteLattice.projectPoint L m j x + InfiniteLattice.projectPoint L m j y := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectPoint_add <;> assumption
theorem projectLink_forwardFrom (x : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L j))
    (μ : Fin 4) :
    InfiniteLattice.projectLink L m j (InfiniteLattice.Link.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom (InfiniteLattice.projectPoint L m j x) μ := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectLink_forwardFrom <;> assumption
theorem faceHolonomy_liftField {U : PeriodicLattice.Bond L m j → ComplexMatrix2}
    (hU : U ∈ PeriodicLattice.compactGaugeFields L m j)
    (p : InfiniteLattice.ElementaryPlaquette (PeriodicLattice.meshSize L j)) :
    ((InfiniteLattice.faceHolonomy (InfiniteLattice.liftField L m j U) p :
        ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      PeriodicLattice.plaquetteHolonomy U (TorusLifts.projectPlaquette L m j p) := by
  have hrev : ∀ b : PeriodicLattice.Bond L m j, U b.opposite = (U b)⁻¹ :=
    fun b => hU.2 b (mem_univ _)
  have hval : ∀ b, ((InfiniteLattice.liftField L m j U b : ComplexMatrix2.specialUnitary) :
      ComplexMatrix2) = U (InfiniteLattice.projectLink L m j b) :=
    fun b => InfiniteLattice.liftField_apply_of_mem hU b
  have hs : ∀ μ, InfiniteLattice.projectPoint L m j (p.corner + InfiniteLattice.axisStep _ μ) =
      InfiniteLattice.projectPoint L m j p.corner + PeriodicLattice.unitStep L m j μ := fun μ => by
    rw [projectPoint_add, InfiniteLattice.projectPoint_axisStep]
  change ((_ * _ * _ * _ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
    PeriodicLattice.pathHolonomy U (PeriodicLattice.Plaquette.boundaryBonds _)
  simp only [PeriodicLattice.pathHolonomy, PeriodicLattice.Plaquette.boundaryBonds, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, hrev, Submonoid.coe_mul,
    InfiniteLattice.specialUnitary_coe_inv, hval, projectLink_forwardFrom, hs, mul_assoc]
  rfl
end Covering
section EvaluationMaps
variable (D : ChessboardSetup)
theorem faceEnergy_liftField {U : D.PeriodicLink → ComplexMatrix2} (hU : U ∈ D.compactFields)
    (p : D.Plaquette) :
    InfiniteLattice.faceEnergy (D.liftField U) p =
      PeriodicLattice.plaquetteCost U (D.projPlaquette p) := by
  have h := faceHolonomy_liftField hU p
  unfold InfiniteLattice.faceEnergy PeriodicLattice.plaquetteCost
  exact congrArg (fun A : ComplexMatrix2 => 1 - (1 / 2) * (ComplexMatrix2.fullTrace A).re) h
theorem smeared_liftField [Finite D.PeriodicPlaquette]
    (hsurj : Surjective D.projPlaquette)
    (hbary : ∀ p : D.Plaquette, (D.projPlaquette p).barycenter = D.proj p.center)
    {v : AmbientSpace → ℂ} (hv : ChessboardSetup.HasBoundedSupport v)
    {U : D.PeriodicLink → ComplexMatrix2} (hU : U ∈ D.compactFields) :
    D.smeared v (D.liftField U) =
      PeriodicLattice.smearedObservable (D.descend (D.periodize v)) U := by
  classical
  have hσ := surjInv_eq hsurj
  set σ := surjInv hsurj with hσdef
  set E := PlaquetteFibres.fibreEquiv D σ hσ with hE
  set f : D.Plaquette → ℂ := fun p =>
    InfiniteLattice.faceEnergy (D.liftField U) p • v p.center with hf
  have hs : (support f).Finite := (PlaquetteFibres.finite_support_center D hsurj hv).subset
    fun p hp h0 => hp (by simp [hf, h0])
  have hper := PlaquetteFibres.periodize_add_latticeTranslate D v
  have hread : ∀ x, D.descend (D.periodize v) (D.proj x) = D.periodize v x :=
    fun x => congrFun (D.descend_comp_proj hper) x
  have hinner : ∀ q : D.PeriodicPlaquette, ∑ᶠ k, f (E (q, k)) =
      PeriodicLattice.plaquetteCost U q • D.descend (D.periodize v) q.barycenter := by
    intro q
    have hk : ∀ k, f (E (q, k)) =
        PeriodicLattice.plaquetteCost U q • v ((σ q).center + latticeTranslate D.torusPeriod k) := by
      intro k
      change InfiniteLattice.faceEnergy (D.liftField U) (PlaquetteFibres.shiftBy D (σ q) k) •
        v (PlaquetteFibres.shiftBy D (σ q) k).center = _
      rw [faceEnergy_liftField D hU, PlaquetteFibres.projPlaquette_shiftBy, hσ,
        PlaquetteFibres.center_shiftBy]
    simp only [hk]
    rw [← smul_finsum]
    congr 1
    have hq : q.barycenter = D.proj (σ q).center := by
      rw [← hbary, hσ]
    rw [hq, hread]
    rfl
  calc D.smeared v (D.liftField U) = ∑ᶠ p, f p := rfl
    _ = ∑ᶠ q, f (E q) := (finsum_comp_equiv E).symm
    _ = ∑ᶠ q, ∑ᶠ k, f (E (q, k)) :=
        finsum_curry (fun q => f (E q)) (hs.preimage E.injective.injOn)
    _ = PeriodicLattice.smearedObservable (D.descend (D.periodize v)) U := finsum_congr hinner
theorem descend_periodize {v : AmbientSpace → ℂ} (hv : ChessboardSetup.HasBoundedSupport v) :
    D.descend (D.periodize v) = TestFunctions.periodize D.torusPeriod v := by
  funext u
  obtain ⟨N, hN⟩ := card_support_translates_le (PlaquetteFibres.torusPeriod_pos D) hv
  obtain ⟨K, -, hs⟩ := hN (TestFunctions.liftPoint (ℓ := D.torusPeriod) u)
  exact (tsum_eq_finsum (K.finite_toSet.subset hs)).symm
theorem imageLink_projLink {r : D.LatticeSym} {r' : D.Torus → D.Torus}
    (h : D.proj ∘ r.toFun = r' ∘ D.proj) (b : D.Link) :
    D.imageLink r' (D.projLink b) = D.projLink (r.linkMap b) := by
  have h1 : ((D.projLink (r.linkMap b)).source : D.Torus) = r' (D.projLink b).source :=
    congrFun h (b.initial : AmbientSpace)
  have h2 : ((D.projLink (r.linkMap b)).target : D.Torus) = r' (D.projLink b).target :=
    congrFun h (b.terminal : AmbientSpace)
  have hs := Classical.epsilon_spec
    (p := fun b' : D.PeriodicLink => (b'.source : D.Torus) = r' (D.projLink b).source ∧
      (b'.target : D.Torus) = r' (D.projLink b).target) ⟨_, h1, h2⟩
  exact PeriodicLattice.Bond.ext (Subtype.ext (hs.1.trans h1.symm))
    (Subtype.ext (hs.2.trans h2.symm))
theorem inducedMapRespectsFields (hsurj : Surjective D.projLink)
    (hlat : D.proj '' (D.gridPoints : Set AmbientSpace) = (D.periodicSites : Set D.Torus))
    (r : D.LatticeSym) (r' : D.Torus → D.Torus)
    (h : D.proj ∘ r.toFun = r' ∘ D.proj) : D.InducedMapRespectsFields r r' := by
  refine ⟨?_, fun U hU => ?_⟩
  · rw [← hlat, ← image_comp, ← h, image_comp]
    exact congrArg (D.proj '' ·) r.image_eq
  · have hreal : D.pullbackField r' U ∈ D.compactFields := by
      refine ⟨fun b _ => hU.1 _ (mem_univ _), fun b _ => ?_⟩
      obtain ⟨c, rfl⟩ := hsurj b
      have e₁ : (D.projLink c).opposite = D.projLink c.opposite := rfl
      have e₂ : r.linkMap c.opposite = (r.linkMap c).opposite := rfl
      have e₃ : D.projLink (r.linkMap c).opposite = (D.projLink (r.linkMap c)).opposite := rfl
      change U (D.imageLink r' (D.projLink c).opposite) =
        (U (D.imageLink r' (D.projLink c)))⁻¹
      rw [e₁, imageLink_projLink D h, imageLink_projLink D h, e₂, e₃]
      exact hU.2 _ (mem_univ _)
    refine ⟨?_, fun b => ?_⟩
    · refine Subtype.ext (funext fun c => Subtype.ext ?_)
      have e₁ : ((D.liftField U (r.linkMap c) : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
          U (D.projLink (r.linkMap c)) :=
        InfiniteLattice.liftField_apply_of_mem hU _
      have e₂ : ((D.liftField (D.pullbackField r' U) c : ComplexMatrix2.specialUnitary) :
          ComplexMatrix2) = D.pullbackField r' U (D.projLink c) :=
        InfiniteLattice.liftField_apply_of_mem hreal _
      refine e₁.trans (Eq.trans ?_ e₂.symm)
      change _ = U (D.imageLink r' (D.projLink c))
      rw [imageLink_projLink D h]
    · obtain ⟨c, rfl⟩ := hsurj b
      refine ⟨D.projLink (r.linkMap c), congrFun h (c.initial : AmbientSpace),
        congrFun h (c.terminal : AmbientSpace), ?_⟩
      change U (D.imageLink r' (D.projLink c)) = _
      rw [imageLink_projLink D h]
theorem pullbackField_shift_liftField {U : D.PeriodicLink → ComplexMatrix2}
    (hU : U ∈ D.compactFields) (v : InfiniteLattice.LatticePoint D.mesh)
    (hv : ∃ k : Fin 4 → ℤ, (v : AmbientSpace) = latticeTranslate D.torusPeriod k) :
    (InfiniteLattice.shift v).pullbackField (D.liftField U) = D.liftField U := by
  obtain ⟨k, hk⟩ := hv
  have hc : ∀ x : InfiniteLattice.LatticePoint D.mesh,
      InfiniteLattice.projectPoint D.L D.m ((D.K : ℕ) : ℤ) ((InfiniteLattice.shift v).pointMap x) =
        InfiniteLattice.projectPoint D.L D.m ((D.K : ℕ) : ℤ) x := fun x => Subtype.ext (by
    change TorusMetric.torusProj D.torusPeriod ((x : AmbientSpace) + (v : AmbientSpace)) =
      TorusMetric.torusProj D.torusPeriod x
    rw [hk]
    exact TestFunctions.torusProj_add_latticeTranslate _ _ _)
  refine Subtype.ext (funext fun b => Subtype.ext ?_)
  have e₁ : ((D.liftField U ((InfiniteLattice.shift v).linkMap b) : ComplexMatrix2.specialUnitary) :
      ComplexMatrix2) = U (D.projLink ((InfiniteLattice.shift v).linkMap b)) :=
    InfiniteLattice.liftField_apply_of_mem hU _
  have e₂ : ((D.liftField U b : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      U (D.projLink b) :=
    InfiniteLattice.liftField_apply_of_mem hU _
  have e₃ : D.projLink ((InfiniteLattice.shift v).linkMap b) = D.projLink b :=
    PeriodicLattice.Bond.ext (hc b.initial) (hc b.terminal)
  refine e₁.trans (Eq.trans ?_ e₂.symm)
  rw [e₃]
end EvaluationMaps
section Measures
variable {L m : ℕ} {j : ℤ}
theorem measurable_boltzmannWeight [Finite (PeriodicLattice.Plaquette L m j)] (β : ℝ) :
    Measurable (PeriodicLattice.boltzmannWeight β :
      (PeriodicLattice.Bond L m j → ComplexMatrix2) → ℝ) := by apply _root_.YangMills.Construction.EqualSideGridsAtEveryExponent.boltzmannWeight_measurable <;> assumption
theorem sourcedBoltzmannWeight_eq [Finite (PeriodicLattice.Plaquette L m j)] {β : ℝ}
    (w : PeriodicLattice.FourTorus L m → ℂ) {U : PeriodicLattice.Bond L m j → ComplexMatrix2}
    (hp : ∀ p : PeriodicLattice.Plaquette L m j,
      ((PeriodicLattice.plaquetteCost U p : ℝ) : ℂ) = PeriodicLattice.plaquetteEnergy U p) :
    PeriodicLattice.sourcedBoltzmannWeight β w U =
      (PeriodicLattice.boltzmannWeight β U : ℂ) *
        Complex.exp (PeriodicLattice.smearedObservable w U) := by apply _root_.YangMills.Construction.ChessboardTori.BoxTorusQuotient.sourcedBoltzmannWeight_eq <;> assumption
end Measures
section Expectation
variable (D : ChessboardSetup)
theorem finite_periodicPlaquette (hC : PeriodicLattice.SiteAndPlaquetteCounts) :
    Finite D.PeriodicPlaquette := by
  have hL := PlaquetteFibres.L_pos D
  have hm : -((D.m : ℕ) : ℤ) ≤ ((D.K : ℕ) : ℤ) := by omega
  obtain ⟨-, -, -, hc, -⟩ := hC D.L D.m ((D.K : ℕ) : ℤ) hL hm
  apply Nat.finite_of_card_ne_zero
  rw [hc]
  have : 0 < 6 * (2 * D.L ^ (((D.m : ℕ) : ℤ) + ((D.K : ℕ) : ℤ)).toNat) ^ 4 := by positivity
  omega
theorem ae_mem_compactFields (hC : PeriodicLattice.SiteAndPlaquetteCounts) :
    ∀ᵐ U ∂(PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)),
      U ∈ D.compactFields := by apply _root_.YangMills.Construction.ChessboardTori.TorusReduction.ae_mem_compactGaugeFields_haar <;> assumption
theorem measurable_exp_smeared {v : AmbientSpace → ℂ}
    (hs : {p : D.Plaquette | v p.center ≠ 0}.Finite) :
    Measurable fun U : D.GaugeField => Complex.exp (D.smeared v U) := by
  have he : (fun U : D.GaugeField => D.smeared v U) = fun U : D.GaugeField =>
      ∑ p ∈ hs.toFinset, InfiniteLattice.faceEnergy U p • v p.center := by
    funext U
    refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
    rw [Set.Finite.coe_toFinset]
    intro h0
    exact hp (by simp [h0])
  have hc : Continuous fun U : D.GaugeField => D.smeared v U := by
    rw [he]
    exact continuous_finsetSum _ fun p _ =>
      (InfiniteLattice.continuous_faceEnergy p).smul continuous_const
  exact (Complex.continuous_exp.comp hc).measurable
theorem liftedExpectation_eq (hC : PeriodicLattice.SiteAndPlaquetteCounts)
    (hT : PeriodicLattice.CubeGeometry.ElementaryLatticeFacts) {F : D.GaugeField → ℂ}
    (hF : Measurable F) {w : D.Torus → ℂ}
    (hO : ∀ U ∈ D.compactFields,
      F (D.liftField U) = Complex.exp (PeriodicLattice.smearedObservable w U)) :
    D.liftedExpectation F = D.partitionFunction w / D.partitionFunction 0 := by
  have := finite_periodicPlaquette D hC
  have hae := ae_mem_compactFields D hC
  have hp : ∀ U ∈ D.compactFields, ∀ p : D.PeriodicPlaquette,
      ((PeriodicLattice.plaquetteCost U p : ℝ) : ℂ) = PeriodicLattice.plaquetteEnergy U p :=
    fun U hU => ((hT D.toStandingParameters).2.2 U hU).1
  have hd : Measurable (PeriodicLattice.boltzmannWeight D.β :
      (PeriodicLattice.Bond D.L D.m ((D.K : ℕ) : ℤ) → ComplexMatrix2) → ℝ) :=
    measurable_boltzmannWeight D.β
  have hext : Measurable D.liftField :=
    InfiniteLattice.measurable_liftField D.L D.m ((D.K : ℕ) : ℤ)
  have hZ0 : D.partitionFunction 0 =
      ((PeriodicLattice.partitionFunction D.L D.m D.K D.β : ℝ) : ℂ) := by
    change ∫ U, PeriodicLattice.sourcedBoltzmannWeight D.β 0 U
      ∂(PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)) = _
    rw [PeriodicLattice.partitionFunction, ← integral_complex_ofReal]
    refine integral_congr_ae (hae.mono fun U hU => ?_)
    rw [sourcedBoltzmannWeight_eq 0 (hp U hU)]
    simp [PeriodicLattice.smearedObservable]
  have h1 : D.liftedExpectation F =
      ∫ U, F (D.liftField U) ∂(PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β) :=
    integral_map hext.aemeasurable hF.aestronglyMeasurable
  have h2 : ∫ U, F (D.liftField U) ∂(PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β) =
      ((ENNReal.ofReal (PeriodicLattice.partitionFunction D.L D.m D.K D.β))⁻¹).toReal •
        ∫ U, (ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β U)).toReal • F (D.liftField U)
          ∂(PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)) := by
    have hmd : Measurable fun U => ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β U) :=
      ENNReal.measurable_ofReal.comp hd
    unfold PeriodicLattice.wilsonGibbsMeasure
    rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hmd
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have h3 : ∫ U, (ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β U)).toReal •
      F (D.liftField U) ∂(PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)) =
      D.partitionFunction w := by
    refine integral_congr_ae (hae.mono fun U hU => ?_)
    have hn : 0 ≤ PeriodicLattice.boltzmannWeight D.β U := (Real.exp_pos _).le
    change (ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β U)).toReal • F (D.liftField U) =
      PeriodicLattice.sourcedBoltzmannWeight D.β w U
    rw [sourcedBoltzmannWeight_eq w (hp U hU), ENNReal.toReal_ofReal hn, hO U hU, Complex.real_smul]
  have hZ : 0 ≤ PeriodicLattice.partitionFunction D.L D.m D.K D.β :=
    integral_nonneg fun U => (Real.exp_pos _).le
  rw [h1, h2, h3, hZ0, ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ, Complex.real_smul,
    div_eq_mul_inv]
  push_cast
  ring
end Expectation
section Copies
variable {D : ChessboardSetup} (g : ReflectionGrid D)
theorem cellSide_mul_pow (hside : 2 * g.cellSide ≤ D.torusPeriod) :
    g.cellSide * (D.L : ℝ) ^ (((D.m : ℕ) : ℤ) - g.q).toNat = (D.L : ℝ) ^ (D.m : ℕ) := by
  have hL := D.one_lt_factor
  have hL0 : (D.L : ℝ) ≠ 0 := by linarith
  have h1 : (D.L : ℝ) ^ g.q ≤ (D.L : ℝ) ^ (((D.m : ℕ) : ℤ)) := by
    have h2 : 2 * (D.L : ℝ) ^ g.q ≤ 2 * (D.L : ℝ) ^ (D.m : ℕ) := hside
    rw [zpow_natCast]
    linarith
  have hq : g.q ≤ ((D.m : ℕ) : ℤ) := (zpow_le_zpow_iff_right₀ hL).1 h1
  have hn : ((((D.m : ℕ) : ℤ) - g.q).toNat : ℤ) = ((D.m : ℕ) : ℤ) - g.q :=
    Int.toNat_of_nonneg (by omega)
  rw [ReflectionGrid.cellSide, ← zpow_natCast, hn, ← zpow_add₀ hL0, ← zpow_natCast]
  congr 1
  ring
theorem transportsArePeriodic (hG : GridBasicProperties.Statement)
    (hside : 2 * g.cellSide ≤ D.torusPeriod) : g.TransportsArePeriodic := by
  intro U hU v hv
  refine ⟨pullbackField_shift_liftField D hU v hv, fun S hS F _ S' hS' => ?_⟩
  obtain ⟨-, -, -, hform, -⟩ := hG D g
  obtain ⟨-, -, -, hsgn, -, hcell, hunique, htrans⟩ := hform
  have hτ := pullbackField_shift_liftField D hU v hv
  obtain ⟨k, hk⟩ := hv
  obtain ⟨r, hr, hrv, hrs⟩ := htrans
    fun μ => (D.L : ℤ) ^ (((D.m : ℕ) : ℤ) - g.q).toNat * k μ
  have hrv' : (r : AmbientSpace → AmbientSpace) = translate (v : AmbientSpace) := by
    rw [hrv]
    congr 1
    funext μ
    rw [hk]
    have e := cellSide_mul_pow g hside
    have e' : D.torusPeriod = 2 * (D.L : ℝ) ^ (D.m : ℕ) := rfl
    simp only [latticeTranslate, e', ← e]
    push_cast
    ring
  have hρ : ∃ c : g.reflectionGroup, c.1 '' S = S' := (hunique S hS S' hS').exists
  set ρ := g.mover S S' with hρdef
  have hρS : ρ.1 '' S = S' := Classical.epsilon_spec hρ
  have hS'' : translate (v : AmbientSpace) '' S' ∈ g.cellSet := by
    rw [← hrv']
    exact hcell r hr S' hS'
  have hcar : g.mover S (translate (v : AmbientSpace) '' S') = ⟨r, hr⟩ * ρ := by
    obtain ⟨c, hc, huniq⟩ := hunique S hS _ hS''
    have h1 : (g.mover S (translate (v : AmbientSpace) '' S')).1 '' S =
        translate (v : AmbientSpace) '' S' :=
      Classical.epsilon_spec
        (p := fun r : g.reflectionGroup => r.1 '' S = translate (v : AmbientSpace) '' S') ⟨c, hc⟩
    have h2 : (⟨r, hr⟩ * ρ : g.reflectionGroup).1 '' S = translate (v : AmbientSpace) '' S' := by
      rw [Subgroup.coe_mul, Equiv.Perm.coe_mul, image_comp, hρS]
      change (r : AmbientSpace → AmbientSpace) '' S' = _
      rw [hrv']
    exact (huniq _ h1).trans (huniq _ h2).symm
  have hs : orientationSign ((⟨r, hr⟩ * ρ : g.reflectionGroup).1 : AmbientSpace → AmbientSpace) =
      orientationSign (ρ.1 : AmbientSpace → AmbientSpace) := by
    have h := hsgn r hr ρ.1 ρ.2
    rw [hrs, one_mul] at h
    exact h
  have hconf : ∀ W : D.GaugeField,
      (g.toLatticeSym (⟨r, hr⟩ * ρ)).pullbackField W =
        (g.toLatticeSym ρ).pullbackField ((InfiniteLattice.shift v).pullbackField W) := by
    intro W
    refine Subtype.ext (funext fun b => congrArg W.1 (InfiniteLattice.Link.ext ?_ ?_))
    · exact Subtype.ext (congrFun hrv' _)
    · exact Subtype.ext (congrFun hrv' _)
  refine ⟨?_, ?_⟩
  · simp only [ReflectionGrid.transportTo]
    rw [hcar]
    simp only [ReflectionGrid.transport, Conventions.signedConjFun,
      InfiniteLattice.LatticeSymmetry.actOn]
    rw [hs, hconf]
  · change g.transportTo S S' F ((InfiniteLattice.shift v).pullbackField _) = _
    rw [hτ]
end Copies
theorem holds (hLifts : TorusLifts.LiftsAndDescendedMaps.Statement)
    (hCounts : PeriodicLattice.SiteAndPlaquetteCounts)
    (hTraces : PeriodicLattice.CubeGeometry.ElementaryLatticeFacts)
    (hGrid : GridBasicProperties.Statement) : Statement := by
  intro D
  obtain ⟨-, -, -, -, -, hlat, hbond, hlsurj, -, hpsurj, hbary⟩ := hLifts D.toStandingParameters
  have hfin := finite_periodicPlaquette D hCounts
  have hsurj : Surjective D.projPlaquette := hpsurj
  have hbary' : ∀ p : D.Plaquette, (D.projPlaquette p).barycenter = D.proj p.center := hbary
  refine ⟨⟨hlat, hlsurj, hsurj, hbary', fun p U hU => faceEnergy_liftField D hU p⟩,
    fun v hb hv => ?_, fun g hg => transportsArePeriodic g hGrid hg,
    fun r r' h => inducedMapRespectsFields D hlsurj hlat r r' h⟩
  have hO := fun U (hU : U ∈ D.compactFields) => smeared_liftField D hsurj hbary' hv hU
  obtain ⟨C, hC⟩ := PlaquetteFibres.periodize_bounded D hb hv
  refine ⟨⟨C, hC⟩, fun x k => PlaquetteFibres.periodize_add_latticeTranslate D v x k, hO, ?_,
    fun _ _ => descend_periodize D hv⟩
  exact liftedExpectation_eq D hCounts hTraces
    (measurable_exp_smeared D (PlaquetteFibres.finite_support_center D hsurj hv))
    fun U hU => congrArg Complex.exp (hO U hU)
end YangMills.Construction.ChessboardTori.LiftingRules
end

import YangMills.Construction.InfiniteLattice.DilationToSpacingOneProof
import YangMills.Construction.LawInAState.TheLeastTorusLawUnderLatticeIsometriesProof
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfTheWilsonMeasureIsInvariantUnderMotionsKeepingThePeriodsProof
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAndCopies
import YangMills.Construction.InfiniteLattice.TorusOfAPeriodLatticeIsFaithful
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace QuotientTorusFaithful
variable {a : ℝ}
theorem axisStep_ne_zero (ha : a ≠ 0) (μ : Fin 4) : axisStep a μ ≠ 0 := by
  intro h
  have h' : (Pi.single μ a : AmbientSpace) μ = 0 := congrFun (congrArg Subtype.val h) μ
  rw [Pi.single_eq_same] at h'
  exact ha h'
theorem axisStep_ne (ha : a ≠ 0) {μ ν : Fin 4} (h : μ ≠ ν) : axisStep a μ ≠ axisStep a ν := by
  intro h'
  have h₁ : (Pi.single μ a : AmbientSpace) μ = (Pi.single ν a : AmbientSpace) μ :=
    congrFun (congrArg Subtype.val h') μ
  rw [Pi.single_eq_same, Pi.single_eq_of_ne h] at h₁
  exact ha h₁
theorem axisStep_add_axisStep_ne_zero (ha : a ≠ 0) {μ ν : Fin 4} (h : μ ≠ ν) :
    axisStep a μ + axisStep a ν ≠ 0 := by
  intro h'
  have h₁ : (Pi.single μ a : AmbientSpace) μ + (Pi.single ν a : AmbientSpace) μ = 0 :=
    congrFun (congrArg Subtype.val h') μ
  rw [Pi.single_eq_same, Pi.single_eq_of_ne h, add_zero] at h₁
  exact ha h₁
theorem quotientMap_eq_iff (Γ : PeriodSublattice a) {x y : LatticePoint a} :
    Γ.quotientMap x = Γ.quotientMap y ↔ y - x ∈ Γ.periods := by
  change (QuotientAddGroup.mk x : LatticePoint a ⧸ Γ.periods) = QuotientAddGroup.mk y ↔ _
  rw [QuotientAddGroup.eq, neg_add_eq_sub]
theorem quotientMap_add_period (Γ : PeriodSublattice a) (x : LatticePoint a) {γ : LatticePoint a}
    (hγ : γ ∈ Γ.periods) : Γ.quotientMap (x + γ) = Γ.quotientMap x :=
  (quotientMap_eq_iff Γ).2 (by simpa using neg_mem hγ)
theorem eq_zero_of_abs_le (ha : 0 < a) (Γ : PeriodSublattice a) {γ : LatticePoint a}
    (hγ : γ ∈ Γ.periods) (h : ∀ μ, |(γ : AmbientSpace) μ| ≤ 2 * a) : γ = 0 := by
  by_contra hne
  have h₁ := Γ.le_norm_of_ne_zero γ hγ hne
  have h₂ : ‖(γ : AmbientSpace)‖ ≤ 2 * a := (pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ => by
    simpa [Real.norm_eq_abs] using h μ
  unfold minimalPeriodRatio at h₁
  linarith
theorem injOn_tripleCube (ha : 0 < a) (Γ : PeriodSublattice a) (x : LatticePoint a) :
    InjOn Γ.quotientMap (tripleCube x) := by
  rintro y ⟨w, hw, hy⟩ y' ⟨w', hw', hy'⟩ h
  have hγ : y' - y ∈ Γ.periods := (quotientMap_eq_iff Γ).1 h
  refine (sub_eq_zero.1 (eq_zero_of_abs_le ha Γ hγ fun μ => ?_)).symm
  have hd : ((y' - y : LatticePoint a) : AmbientSpace) μ = ((w' μ - w μ : ℤ) : ℝ) * a := by
    change (y' : AmbientSpace) μ - (y : AmbientSpace) μ = _
    rw [hy, hy']
    push_cast
    ring
  rw [hd, abs_mul, abs_of_pos ha]
  have h₂ : |((w' μ - w μ : ℤ) : ℝ)| ≤ 2 := by
    have h₃ := hw μ
    have h₄ := hw' μ
    rw [abs_le]
    constructor
    · exact_mod_cast (by omega : (-2 : ℤ) ≤ w' μ - w μ)
    · exact_mod_cast (by omega : w' μ - w μ ≤ 2)
  exact mul_le_mul_of_nonneg_right h₂ ha.le
theorem self_mem_tripleCube (x : LatticePoint a) : x ∈ tripleCube x :=
  ⟨0, fun μ => by simp, fun μ => by simp⟩
theorem add_axisStep_mem_tripleCube (x : LatticePoint a) (μ : Fin 4) :
    x + axisStep a μ ∈ tripleCube x := by
  refine ⟨Pi.single μ 1, fun ν => ?_, fun ν => ?_⟩
  · by_cases h : ν = μ
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  · change (x : AmbientSpace) ν + (Pi.single μ a : AmbientSpace) ν = _
    by_cases h : ν = μ
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
theorem add_axisStep_add_axisStep_mem_tripleCube (x : LatticePoint a) {μ ν : Fin 4} (hμν : μ ≠ ν) :
    x + axisStep a μ + axisStep a ν ∈ tripleCube x := by
  refine ⟨Pi.single μ 1 + Pi.single ν 1, fun κ => ?_, fun κ => ?_⟩
  · by_cases h : κ = μ
    · subst h
      simp [Pi.single_eq_of_ne hμν]
    · by_cases h' : κ = ν
      · subst h'
        simp [Pi.single_eq_of_ne h]
      · simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
  · change (x : AmbientSpace) κ + (Pi.single μ a : AmbientSpace) κ +
      (Pi.single ν a : AmbientSpace) κ = _
    by_cases h : κ = μ
    · subst h
      simp [Pi.single_eq_of_ne hμν]
    · by_cases h' : κ = ν
      · subst h'
        simp [Pi.single_eq_of_ne h]
      · simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
theorem cornerSet_subset_tripleCube (p : ElementaryPlaquette a) :
    p.cornerSet ⊆ tripleCube p.corner := by
  intro c hc
  simp only [ElementaryPlaquette.cornerSet, mem_insert_iff, mem_singleton_iff] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact self_mem_tripleCube _
  · exact add_axisStep_mem_tripleCube _ _
  · exact add_axisStep_add_axisStep_mem_tripleCube _ p.lowAxis_lt_highAxis.ne
  · exact add_axisStep_mem_tripleCube _ _
theorem exists_nsmul_mem_periods (Γ : PeriodSublattice a) :
    ∃ κ : ℕ, 0 < κ ∧ ∀ y : LatticePoint a, κ • y ∈ Γ.periods := by
  obtain ⟨v, hv, hli⟩ := Γ.exists_linearIndependent
  have hex : ∀ i, ∃ n : Fin 4 → ℤ, ∀ μ, (v i : AmbientSpace) μ = (n μ : ℝ) * a := fun i => (v i).2
  choose n hn using hex
  let N : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of n
  have hdet : N.det ≠ 0 := by
    intro h0
    let R : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i => (v i : AmbientSpace)
    have hR : R = a • (Int.castRingHom ℝ).mapMatrix N := by
      ext i μ
      simp [R, N, hn, mul_comm]
    have hu : IsUnit R := Matrix.linearIndependent_rows_iff_isUnit.1 hli
    have hd : R.det = 0 := by
      rw [hR, Matrix.det_smul, ← RingHom.map_det, h0]
      simp
    rw [Matrix.isUnit_iff_isUnit_det, hd] at hu
    exact not_isUnit_zero hu
  have hmul : ∀ y : LatticePoint a, N.det • y ∈ Γ.periods := by
    intro y
    obtain ⟨c, hc⟩ := y.2
    have key : Matrix.vecMul (Matrix.vecMul c N.adjugate) N = N.det • c := by
      rw [Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul, Matrix.vecMul_one]
    have hsum : N.det • y = ∑ i, (Matrix.vecMul c N.adjugate) i • v i := by
      apply Subtype.ext
      funext μ
      let φ : LatticePoint a →+ ℝ :=
        (Pi.evalAddMonoidHom (fun _ : Fin 4 => ℝ) μ).comp (latticeSubgroup a).subtype
      change φ (N.det • y) = φ (∑ i, (Matrix.vecMul c N.adjugate) i • v i)
      rw [map_zsmul, map_sum]
      simp only [map_zsmul]
      have hφ : ∀ z : LatticePoint a, φ z = (z : AmbientSpace) μ := fun _ => rfl
      simp only [hφ, hn, hc, zsmul_eq_mul]
      have kμ : ∑ i, (Matrix.vecMul c N.adjugate) i * n i μ = N.det * c μ := by
        have := congrFun key μ
        simpa [Matrix.vecMul, dotProduct, N] using this
      have kμ' : ∑ i, ((Matrix.vecMul c N.adjugate) i : ℝ) * (n i μ : ℝ) =
          (N.det : ℝ) * (c μ : ℝ) := by
        exact_mod_cast kμ
      calc (N.det : ℝ) * ((c μ : ℝ) * a) = ((N.det : ℝ) * (c μ : ℝ)) * a := by ring
        _ = (∑ i, ((Matrix.vecMul c N.adjugate) i : ℝ) * (n i μ : ℝ)) * a := by rw [kμ']
        _ = _ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum]
    exact sum_mem fun i _ => zsmul_mem (hv i) _
  refine ⟨N.det.natAbs, Int.natAbs_pos.2 hdet, fun y => ?_⟩
  have h₁ : ((N.det.natAbs : ℤ)) • y ∈ Γ.periods := by
    rcases Int.natAbs_eq N.det with h | h
    · rw [← h]
      exact hmul y
    · have h' : (N.det.natAbs : ℤ) = -N.det := by omega
      rw [h', neg_smul]
      exact neg_mem (hmul y)
  rwa [natCast_zsmul] at h₁
def pointOfCoords (a : ℝ) (n : Fin 4 → ℤ) : LatticePoint a :=
  ⟨fun μ => (n μ : ℝ) * a, n, fun _ => rfl⟩
theorem finite_quotientTorus (Γ : PeriodSublattice a) : Finite Γ.QuotientTorus := by
  obtain ⟨κ, hκ, h⟩ := exists_nsmul_mem_periods Γ
  have hκ' : (0 : ℤ) < κ := by exact_mod_cast hκ
  let f : (Fin 4 → Fin κ) → Γ.QuotientTorus :=
    fun w => Γ.quotientMap (pointOfCoords a fun μ => ((w μ : ℕ) : ℤ))
  refine Finite.of_surjective f fun ξ => ?_
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective ξ
  obtain ⟨n, hn⟩ := x.2
  have hlt : ∀ μ, (n μ % κ).toNat < κ := fun μ => by
    have h₁ := Int.emod_nonneg (n μ) hκ'.ne'
    have h₂ := Int.emod_lt_of_pos (n μ) hκ'
    omega
  refine ⟨fun μ => ⟨(n μ % κ).toNat, hlt μ⟩, ?_⟩
  refine (quotientMap_eq_iff Γ).2 ?_
  have hq : x - pointOfCoords a (fun μ => (((n μ % κ).toNat : ℕ) : ℤ)) =
      κ • pointOfCoords a (fun μ => n μ / κ) := by
    apply Subtype.ext
    funext μ
    change (x : AmbientSpace) μ - ((((n μ % κ).toNat : ℕ) : ℤ) : ℝ) * a =
      ((κ • pointOfCoords a (fun μ => n μ / κ) : LatticePoint a) : AmbientSpace) μ
    have h₁ : ((κ • pointOfCoords a (fun μ => n μ / κ) : LatticePoint a) : AmbientSpace) μ =
        (κ : ℝ) * (((n μ / κ : ℤ) : ℝ) * a) := by
      simp [pointOfCoords]
    have h₂ : (((n μ % κ).toNat : ℕ) : ℤ) = n μ % κ :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hκ'.ne')
    have h₃ : ((n μ : ℤ) : ℝ) = ((n μ % κ : ℤ) : ℝ) + (κ : ℝ) * ((n μ / κ : ℤ) : ℝ) := by
      exact_mod_cast (Int.emod_add_mul_ediv (n μ) κ).symm
    rw [h₁, h₂, hn μ, h₃]
    ring
  exact hq ▸ h _
theorem translate_zero (b : PositiveLink a) : b.translate 0 = b :=
  Subtype.ext (Link.ext (add_zero _) (add_zero _))
theorem linkClass_translate (Γ : PeriodSublattice a) (b : PositiveLink a) {γ : LatticePoint a}
    (hγ : γ ∈ Γ.periods) : Γ.linkClass (b.translate γ) = Γ.linkClass b := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.linkClass_translate <;> assumption
theorem exists_linkRep_eq_translate (Γ : PeriodSublattice a) (b : PositiveLink a) :
    ∃ γ ∈ Γ.periods, Γ.linkRep (Γ.linkClass b) = b.translate γ :=
  (Γ.quotientLink_nonempty (Γ.linkClass b)).some_mem
theorem exists_eq_forwardAt (b : PositiveLink a) :
    ∃ μ, b = PositiveLink.forwardAt b.1.initial μ := by
  obtain ⟨μ, h⟩ := b.2
  refine ⟨μ, Subtype.ext (Link.ext rfl ?_)⟩
  change b.1.terminal = b.1.initial + axisStep a μ
  rw [← h]
  abel
theorem forwardAt_injective (ha : a ≠ 0) {x y : LatticePoint a} {μ ν : Fin 4}
    (h : PositiveLink.forwardAt x μ = PositiveLink.forwardAt y ν) : x = y ∧ μ = ν := by
  have h₁ : x = y := congrArg (fun b : PositiveLink a => b.1.initial) h
  have h₂ : x + axisStep a μ = y + axisStep a ν :=
    congrArg (fun b : PositiveLink a => b.1.terminal) h
  subst h₁
  refine ⟨rfl, ?_⟩
  by_contra hne
  exact axisStep_ne ha hne (add_left_cancel h₂)
theorem translate_forwardAt (x γ : LatticePoint a) (μ : Fin 4) :
    (PositiveLink.forwardAt x μ).translate γ = PositiveLink.forwardAt (x + γ) μ := by
  refine Subtype.ext (Link.ext rfl ?_)
  change x + axisStep a μ + γ = x + γ + axisStep a μ
  abel
theorem exists_linkClass_eq_forwardAt (Γ : PeriodSublattice a) (c : Γ.QuotientLink) :
    ∃ (x : LatticePoint a) (μ : Fin 4), c = Γ.linkClass (PositiveLink.forwardAt x μ) := by
  obtain ⟨_, b, rfl⟩ := c
  obtain ⟨μ, hμ⟩ := exists_eq_forwardAt b
  exact ⟨b.1.initial, μ, congrArg Γ.linkClass hμ⟩
def linkCoords (Γ : PeriodSublattice a) (c : Γ.QuotientLink) : Γ.QuotientTorus × Fin 4 :=
  (Γ.quotientMap (Γ.linkRep c).1.initial, (exists_eq_forwardAt (Γ.linkRep c)).choose)
theorem linkCoords_forwardAt (Γ : PeriodSublattice a) (x : LatticePoint a) (μ : Fin 4) :
    linkCoords Γ (Γ.linkClass (PositiveLink.forwardAt x μ)) = (Γ.quotientMap x, μ) := by
  obtain ⟨γ, hγ, h⟩ := exists_linkRep_eq_translate Γ (PositiveLink.forwardAt x μ)
  rw [translate_forwardAt] at h
  have hs := (exists_eq_forwardAt (Γ.linkRep
    (Γ.linkClass (PositiveLink.forwardAt x μ)))).choose_spec
  have hi := forwardAt_injective Γ.spacing_ne_zero (h.symm.trans hs)
  refine Prod.ext ?_ hi.2.symm
  change Γ.quotientMap (Γ.linkRep _).1.initial = Γ.quotientMap x
  rw [← hi.1]
  exact quotientMap_add_period Γ x hγ
theorem linkCoords_bijective (Γ : PeriodSublattice a) : Function.Bijective (linkCoords Γ) := by
  constructor
  · intro c c' h
    obtain ⟨x, μ, rfl⟩ := exists_linkClass_eq_forwardAt Γ c
    obtain ⟨y, ν, rfl⟩ := exists_linkClass_eq_forwardAt Γ c'
    rw [linkCoords_forwardAt, linkCoords_forwardAt] at h
    obtain ⟨h₁, rfl⟩ := Prod.mk.inj h
    have hγ := (quotientMap_eq_iff Γ).1 h₁
    have hy : PositiveLink.forwardAt y μ = (PositiveLink.forwardAt x μ).translate (y - x) := by
      rw [translate_forwardAt, add_sub_cancel]
    rw [hy, linkClass_translate Γ _ hγ]
  · rintro ⟨ξ, μ⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective ξ
    exact ⟨_, linkCoords_forwardAt Γ x μ⟩
theorem linkClass_forwardAt_ne (Γ : PeriodSublattice a) {x y : LatticePoint a} {μ ν : Fin 4}
    (h : Γ.quotientMap x ≠ Γ.quotientMap y ∨ μ ≠ ν) :
    Γ.linkClass (PositiveLink.forwardAt x μ) ≠ Γ.linkClass (PositiveLink.forwardAt y ν) := by
  intro h'
  have h₁ := congrArg (linkCoords Γ) h'
  rw [linkCoords_forwardAt, linkCoords_forwardAt] at h₁
  obtain ⟨h₂, h₃⟩ := Prod.mk.inj h₁
  exact h.elim (fun h₄ => h₄ h₂) fun h₄ => h₄ h₃
theorem linkEndpoints_linkClass (Γ : PeriodSublattice a) (b : PositiveLink a) :
    Γ.linkEndpoints (Γ.linkClass b) =
      {Γ.quotientMap b.1.initial, Γ.quotientMap b.1.terminal} := by
  obtain ⟨γ, hγ, h⟩ := exists_linkRep_eq_translate Γ b
  unfold PeriodSublattice.linkEndpoints
  rw [h]
  change ({Γ.quotientMap (b.1.initial + γ), Γ.quotientMap (b.1.terminal + γ)} :
    Set Γ.QuotientTorus) = _
  rw [quotientMap_add_period Γ _ hγ, quotientMap_add_period Γ _ hγ]
theorem ncard_linkEndpoints (ha : 0 < a) (Γ : PeriodSublattice a) (c : Γ.QuotientLink) :
    (Γ.linkEndpoints c).ncard = 2 := by
  obtain ⟨x, μ, rfl⟩ := exists_linkClass_eq_forwardAt Γ c
  rw [linkEndpoints_linkClass]
  refine Set.ncard_pair fun h => ?_
  have h₁ : x = x + axisStep a μ :=
    injOn_tripleCube ha Γ x (self_mem_tripleCube x) (add_axisStep_mem_tripleCube x μ) h
  exact axisStep_ne_zero ha.ne' μ (left_eq_add.1 h₁)
theorem link_eq_of_shared_endpoint (ha : 0 < a) (Γ : PeriodSublattice a) (b b' : PositiveLink a)
    (hb : b' ∈ Γ.linkOrbit b)
    (hc : (({b.1.initial, b.1.terminal} ∩ {b'.1.initial, b'.1.terminal} :
      Set (LatticePoint a))).Nonempty) :
    b' = b := by
  obtain ⟨γ, hγ, rfl⟩ := hb
  obtain ⟨μ, hμ⟩ := exists_eq_forwardAt b
  have hhead : b.1.terminal = b.1.initial + axisStep a μ :=
    congrArg (fun c : PositiveLink a => c.1.terminal) hμ
  have hmem : ∀ z ∈ ({b.1.initial, b.1.terminal} : Set (LatticePoint a)),
      z ∈ tripleCube b.1.initial := by
    rintro z (rfl | hz)
    · exact self_mem_tripleCube _
    · rw [mem_singleton_iff.1 hz, hhead]
      exact add_axisStep_mem_tripleCube _ _
  obtain ⟨z, hz, hz'⟩ := hc
  obtain ⟨y, hy, hyz⟩ : ∃ y ∈ ({b.1.initial, b.1.terminal} : Set (LatticePoint a)),
      z = y + γ := by
    rcases hz' with rfl | hz'
    · exact ⟨b.1.initial, by simp, rfl⟩
    · exact ⟨b.1.terminal, by simp, mem_singleton_iff.1 hz'⟩
  have h₁ : y = z := injOn_tripleCube ha Γ _ (hmem y hy) (hmem z hz)
    (by rw [hyz, quotientMap_add_period Γ y hγ])
  have h₂ : γ = 0 := by
    rw [h₁] at hyz
    exact left_eq_add.1 hyz
  rw [h₂, translate_zero]
def shiftPlaquette (p : ElementaryPlaquette a) (γ : LatticePoint a) : ElementaryPlaquette a :=
  ⟨p.corner + γ, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
theorem cornerSet_shiftPlaquette (p : ElementaryPlaquette a) (γ : LatticePoint a) :
    (shiftPlaquette p γ).cornerSet = (shift γ).pointMap '' p.cornerSet := by apply _root_.YangMills.DeltaSharedProofs.p501596 <;> assumption
theorem plaquetteMap_shift_eq (ha : 0 < a) (p : ElementaryPlaquette a) (γ : LatticePoint a) :
    (shift γ).plaquetteMap p = shiftPlaquette p γ := by apply _root_.YangMills.Construction.UnitSpacing.plaquetteMap_shift <;> assumption
theorem mem_plaquetteOrbit_iff (ha : 0 < a) (Γ : PeriodSublattice a)
    {p q : ElementaryPlaquette a} :
    q ∈ Γ.plaquetteOrbit p ↔ ∃ γ ∈ Γ.periods, q = shiftPlaquette p γ := by
  simp only [PeriodSublattice.plaquetteOrbit, mem_ofPred_eq, plaquetteMap_shift_eq ha]
theorem shiftPlaquette_zero (p : ElementaryPlaquette a) : shiftPlaquette p 0 = p :=
  ElementaryPlaquette.ext (add_zero _) rfl rfl
theorem shiftPlaquette_shiftPlaquette (p : ElementaryPlaquette a) (γ δ : LatticePoint a) :
    shiftPlaquette (shiftPlaquette p γ) δ = shiftPlaquette p (γ + δ) := by apply _root_.YangMills.DeltaSharedProofs.p502013 <;> assumption
theorem faceClass_shiftPlaquette (ha : 0 < a) (Γ : PeriodSublattice a) (p : ElementaryPlaquette a)
    {γ : LatticePoint a} (hγ : γ ∈ Γ.periods) :
    Γ.faceClass (shiftPlaquette p γ) = Γ.faceClass p := by
  refine Subtype.ext ?_
  change Γ.plaquetteOrbit (shiftPlaquette p γ) = Γ.plaquetteOrbit p
  ext q
  rw [mem_plaquetteOrbit_iff ha, mem_plaquetteOrbit_iff ha]
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    exact ⟨γ + δ, add_mem hγ hδ, shiftPlaquette_shiftPlaquette p γ δ⟩
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨-γ + δ, add_mem (neg_mem hγ) hδ, ?_⟩
    rw [shiftPlaquette_shiftPlaquette, add_neg_cancel_left]
theorem exists_plaquetteRep_eq_shift (ha : 0 < a) (Γ : PeriodSublattice a)
    (p : ElementaryPlaquette a) :
    ∃ γ ∈ Γ.periods, Γ.plaquetteRep (Γ.faceClass p) = shiftPlaquette p γ :=
  (mem_plaquetteOrbit_iff ha Γ).1 (Γ.quotientPlaquette_nonempty (Γ.faceClass p)).some_mem
theorem exists_faceClass_eq (Γ : PeriodSublattice a) (P : Γ.QuotientPlaquette) :
    ∃ p : ElementaryPlaquette a, P = Γ.faceClass p := by
  obtain ⟨_, p, rfl⟩ := P
  exact ⟨p, rfl⟩
def faceCoords (Γ : PeriodSublattice a) (P : Γ.QuotientPlaquette) :
    {t : Γ.QuotientTorus × Fin 4 × Fin 4 // t.2.1 < t.2.2} :=
  ⟨(Γ.quotientMap (Γ.plaquetteRep P).corner, (Γ.plaquetteRep P).lowAxis,
    (Γ.plaquetteRep P).highAxis), (Γ.plaquetteRep P).lowAxis_lt_highAxis⟩
theorem faceCoords_faceClass (ha : 0 < a) (Γ : PeriodSublattice a) (p : ElementaryPlaquette a) :
    faceCoords Γ (Γ.faceClass p) =
      ⟨(Γ.quotientMap p.corner, p.lowAxis, p.highAxis), p.lowAxis_lt_highAxis⟩ := by
  obtain ⟨γ, hγ, h⟩ := exists_plaquetteRep_eq_shift ha Γ p
  refine Subtype.ext ?_
  change (Γ.quotientMap (Γ.plaquetteRep (Γ.faceClass p)).corner,
    (Γ.plaquetteRep (Γ.faceClass p)).lowAxis,
    (Γ.plaquetteRep (Γ.faceClass p)).highAxis) =
    (Γ.quotientMap p.corner, p.lowAxis, p.highAxis)
  rw [h]
  exact Prod.ext (quotientMap_add_period Γ p.corner hγ) rfl
theorem faceCoords_bijective (ha : 0 < a) (Γ : PeriodSublattice a) :
    Function.Bijective (faceCoords Γ) := by
  constructor
  · intro P P' h
    obtain ⟨p, rfl⟩ := exists_faceClass_eq Γ P
    obtain ⟨q, rfl⟩ := exists_faceClass_eq Γ P'
    rw [faceCoords_faceClass ha, faceCoords_faceClass ha] at h
    have h₀ := congrArg Subtype.val h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h₀
    obtain ⟨h₃, h₄⟩ := Prod.mk.inj h₂
    have hγ := (quotientMap_eq_iff Γ).1 h₁
    have hq : q = shiftPlaquette p (q.corner - p.corner) :=
      ElementaryPlaquette.ext (add_sub_cancel _ _).symm h₃.symm h₄.symm
    rw [hq, faceClass_shiftPlaquette ha Γ p hγ]
  · rintro ⟨⟨ξ, μ, ν⟩, h⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective ξ
    exact ⟨_, faceCoords_faceClass ha Γ ⟨x, μ, ν, h⟩⟩
theorem plaquetteVertices_faceClass (ha : 0 < a) (Γ : PeriodSublattice a)
    (p : ElementaryPlaquette a) :
    Γ.plaquetteVertices (Γ.faceClass p) = Γ.quotientMap '' p.cornerSet := by
  obtain ⟨γ, hγ, h⟩ := exists_plaquetteRep_eq_shift ha Γ p
  unfold PeriodSublattice.plaquetteVertices
  rw [h, cornerSet_shiftPlaquette, image_image]
  exact image_congr fun x _ => quotientMap_add_period Γ x hγ
theorem ncard_four_of_pairwise_ne {α : Type*} {w x y z : α} (h₁ : w ≠ x) (h₂ : w ≠ y)
    (h₃ : w ≠ z) (h₄ : x ≠ y) (h₅ : x ≠ z) (h₆ : y ≠ z) : ({w, x, y, z} : Set α).ncard = 4 := by
  rw [Set.ncard_insert_of_notMem (by simp [h₁, h₂, h₃]),
    Set.ncard_insert_of_notMem (by simp [h₄, h₅]), Set.ncard_pair h₆]
theorem ncard_cornerSet (ha : a ≠ 0) (p : ElementaryPlaquette a) : p.cornerSet.ncard = 4 := by
  have hs := axisStep_ne_zero ha p.lowAxis
  have hs' := axisStep_ne_zero ha p.highAxis
  have hne := p.lowAxis_lt_highAxis.ne
  refine ncard_four_of_pairwise_ne ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using hs
  · rw [add_assoc]
    simpa using axisStep_add_axisStep_ne_zero ha hne
  · simpa using hs'
  · simpa using hs'
  · simpa using axisStep_ne ha hne
  · simpa using hs
theorem ncard_plaquetteVertices (ha : 0 < a) (Γ : PeriodSublattice a) (P : Γ.QuotientPlaquette) :
    (Γ.plaquetteVertices P).ncard = 4 := by
  obtain ⟨p, rfl⟩ := exists_faceClass_eq Γ P
  rw [plaquetteVertices_faceClass ha,
    Set.InjOn.ncard_image ((injOn_tripleCube ha Γ p.corner).mono (cornerSet_subset_tripleCube p))]
  exact ncard_cornerSet ha.ne' p
theorem plaquette_eq_of_shared_corner (ha : 0 < a) (Γ : PeriodSublattice a)
    (p p' : ElementaryPlaquette a) (hp : p' ∈ Γ.plaquetteOrbit p)
    (hc : (p.cornerSet ∩ p'.cornerSet).Nonempty) : p' = p := by
  obtain ⟨γ, hγ, rfl⟩ := (mem_plaquetteOrbit_iff ha Γ).1 hp
  obtain ⟨z, hz, hz'⟩ := hc
  rw [cornerSet_shiftPlaquette] at hz'
  obtain ⟨y, hy, hyz⟩ := hz'
  have hyz' : y + γ = z := hyz
  have h₁ : y = z := injOn_tripleCube ha Γ p.corner (cornerSet_subset_tripleCube p hy)
    (cornerSet_subset_tripleCube p hz) (by rw [← hyz', quotientMap_add_period Γ y hγ])
  have h₂ : γ = 0 := by
    rw [← h₁] at hyz'
    exact add_eq_left.1 hyz'
  rw [h₂, shiftPlaquette_zero]
theorem mem_linkSet_iff (q : ElementaryPlaquette a) (b : PositiveLink a) :
    b.1 ∈ q.linkSet ↔ b = PositiveLink.forwardAt q.corner q.lowAxis ∨
      b = PositiveLink.forwardAt (q.corner + axisStep a q.lowAxis) q.highAxis ∨
      b = PositiveLink.forwardAt (q.corner + axisStep a q.highAxis) q.lowAxis ∨
      b = PositiveLink.forwardAt q.corner q.highAxis := by
  simp only [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges, mem_ofPred_eq,
    List.mem_cons, List.not_mem_nil, or_false, Subtype.ext_iff]
  rfl
theorem linkClasses_of_plaquette (Γ : PeriodSublattice a) (q : ElementaryPlaquette a) :
    {c | ∃ b : PositiveLink a, b.1 ∈ q.linkSet ∧ c = Γ.linkClass b} =
      {Γ.linkClass (PositiveLink.forwardAt q.corner q.lowAxis),
        Γ.linkClass (PositiveLink.forwardAt (q.corner + axisStep a q.lowAxis) q.highAxis),
        Γ.linkClass (PositiveLink.forwardAt (q.corner + axisStep a q.highAxis) q.lowAxis),
        Γ.linkClass (PositiveLink.forwardAt q.corner q.highAxis)} := by
  ext c
  simp only [mem_ofPred_eq, mem_linkSet_iff, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨b, rfl | rfl | rfl | rfl, rfl⟩ <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
theorem linkClass_forwardAt_add (Γ : PeriodSublattice a) (x : LatticePoint a) (μ : Fin 4)
    {γ : LatticePoint a} (hγ : γ ∈ Γ.periods) :
    Γ.linkClass (PositiveLink.forwardAt (x + γ) μ) =
      Γ.linkClass (PositiveLink.forwardAt x μ) := by
  rw [← translate_forwardAt, linkClass_translate Γ _ hγ]
theorem plaquetteLinks_faceClass (ha : 0 < a) (Γ : PeriodSublattice a)
    (p : ElementaryPlaquette a) :
    Γ.plaquetteLinks (Γ.faceClass p) =
      {c | ∃ b : PositiveLink a, b.1 ∈ p.linkSet ∧ c = Γ.linkClass b} := by
  obtain ⟨γ, hγ, h⟩ := exists_plaquetteRep_eq_shift ha Γ p
  unfold PeriodSublattice.plaquetteLinks
  rw [h, linkClasses_of_plaquette, linkClasses_of_plaquette]
  have h₁ : (shiftPlaquette p γ).corner = p.corner + γ := rfl
  have h₂ : (shiftPlaquette p γ).lowAxis = p.lowAxis := rfl
  have h₃ : (shiftPlaquette p γ).highAxis = p.highAxis := rfl
  have h₄ : ∀ μ, p.corner + γ + axisStep a μ = p.corner + axisStep a μ + γ := fun μ => by abel
  rw [h₁, h₂, h₃, h₄, h₄, linkClass_forwardAt_add Γ _ _ hγ, linkClass_forwardAt_add Γ _ _ hγ,
    linkClass_forwardAt_add Γ _ _ hγ, linkClass_forwardAt_add Γ _ _ hγ]
theorem ncard_plaquetteLinks (ha : 0 < a) (Γ : PeriodSublattice a) (P : Γ.QuotientPlaquette) :
    (Γ.plaquetteLinks P).ncard = 4 := by
  obtain ⟨p, rfl⟩ := exists_faceClass_eq Γ P
  rw [plaquetteLinks_faceClass ha, linkClasses_of_plaquette]
  have hne := p.lowAxis_lt_highAxis.ne
  have h₁ : p.corner ∈ tripleCube p.corner := self_mem_tripleCube _
  have h₂ := add_axisStep_mem_tripleCube p.corner p.lowAxis
  have h₃ := add_axisStep_mem_tripleCube p.corner p.highAxis
  have hinj := injOn_tripleCube ha Γ p.corner
  have hs := axisStep_ne_zero ha.ne' p.lowAxis
  have hs' := axisStep_ne_zero ha.ne' p.highAxis
  refine ncard_four_of_pairwise_ne ?_ ?_ ?_ ?_ ?_ ?_
  · exact linkClass_forwardAt_ne Γ (Or.inr hne)
  · refine linkClass_forwardAt_ne Γ (Or.inl fun h => hs' (left_eq_add.1 (hinj h₁ h₃ h)))
  · exact linkClass_forwardAt_ne Γ (Or.inr hne)
  · exact linkClass_forwardAt_ne Γ (Or.inr hne.symm)
  · exact linkClass_forwardAt_ne Γ (Or.inl fun h => hs (add_eq_left.1 (hinj h₂ h₁ h)))
  · exact linkClass_forwardAt_ne Γ (Or.inr hne)
end QuotientTorusFaithful
open QuotientTorusFaithful in
theorem QuotientTorusFaithful.holds : QuotientTorusFaithful.Statement :=
  fun _ ha Γ =>
    have hfin : Finite Γ.QuotientTorus := finite_quotientTorus Γ
    have hlink : Function.Bijective (linkCoords Γ) := linkCoords_bijective Γ
    have hface : Function.Bijective (faceCoords Γ) := faceCoords_bijective ha Γ
    { periods_finiteIndex := AddSubgroup.finiteIndex_of_finite_quotient
      finite_quotientTorus := hfin
      finite_quotientLink := Finite.of_injective (linkCoords Γ) hlink.1
      finite_quotientPlaquette := Finite.of_injective (faceCoords Γ) hface.1
      link_equiv := ⟨Equiv.ofBijective _ hlink, linkCoords_forwardAt Γ⟩
      plaquette_equiv := ⟨Equiv.ofBijective _ hface, faceCoords_faceClass ha Γ⟩
      injOn_tripleCube := injOn_tripleCube ha Γ
      linkEndpoints_linkClass := linkEndpoints_linkClass Γ
      plaquetteVertices_faceClass := plaquetteVertices_faceClass ha Γ
      plaquetteLinks_faceClass := plaquetteLinks_faceClass ha Γ
      ncard_linkEndpoints := ncard_linkEndpoints ha Γ
      ncard_plaquetteVertices := ncard_plaquetteVertices ha Γ
      ncard_plaquetteLinks := ncard_plaquetteLinks ha Γ
      link_eq_of_shared_endpoint := link_eq_of_shared_endpoint ha Γ
      plaquette_eq_of_shared_corner := plaquette_eq_of_shared_corner ha Γ }
end YangMills.Construction.InfiniteLattice

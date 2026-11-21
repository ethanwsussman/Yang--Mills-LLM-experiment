import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLatticeProof
import YangMills.Construction.TorusOrFourSpace.StandingSignsOfTheSupportAdaptedFamily
import YangMills.Construction.ChessboardTori.CoveringMapOnTheCellsOfAGridProof
import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegionsProof
import YangMills.Construction.Towers.ObjectsOfATowerPickedByTheirPropertiesHaveThosePropertiesProof
import Mathlib
set_option autoImplicit false
open Set Function YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.ProjectionFacts
section Vectors
variable {S : ℝ}
private theorem intCombination_apply (α : ℝ) (w : Fin 4 → ℤ) (μ : Fin 4) :
    intCombination α w μ = α * w μ := by
  simp [intCombination, PeriodicLattice.coordVec, Finset.sum_apply, Pi.single_apply]
private theorem torusProj_add (y y' : Fin 4 → ℝ) :
    torusProj S (y + y') = torusProj S y + torusProj S y' := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
private theorem torusProj_neg (y : Fin 4 → ℝ) : torusProj S (-y) = -torusProj S y := by
  funext μ
  exact AddCircle.coe_neg _
private theorem torusProj_sub (y y' : Fin 4 → ℝ) :
    torusProj S (y - y') = torusProj S y - torusProj S y' := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
private theorem torusProj_surj : Surjective (torusProj S) := by apply _root_.YangMills.Construction.TestFunctions.torusProj_surjective <;> assumption
private theorem torusProj_eq_zero_iff (y : Fin 4 → ℝ) :
    torusProj S y = 0 ↔ ∃ n : Fin 4 → ℤ, y = intCombination S n := by
  constructor
  · intro h
    have h' : ∀ μ, ∃ n : ℤ, n • S = y μ := fun μ =>
      (AddCircle.coe_eq_zero_iff S).1 (congrFun h μ)
    choose n hn using h'
    refine ⟨n, funext fun μ => ?_⟩
    rw [intCombination_apply, ← hn μ, zsmul_eq_mul, mul_comm]
  · rintro ⟨n, rfl⟩
    funext μ
    refine (AddCircle.coe_eq_zero_iff S).2 ⟨n μ, ?_⟩
    rw [intCombination_apply, zsmul_eq_mul, mul_comm]
private theorem torusProj_eq_iff (y y' : Fin 4 → ℝ) :
    torusProj S y = torusProj S y' ↔ ∃ n : Fin 4 → ℤ, y - y' = intCombination S n := by
  rw [← torusProj_eq_zero_iff, torusProj_sub, sub_eq_zero]
private theorem euclidNormVec_mono {b v : Fin 4 → ℝ} (h : ∀ μ, |b μ| ≤ |v μ|) :
    euclidNormVec b ≤ euclidNormVec v := by apply _root_.YangMills.Construction.ChessboardTori.ProjOnGridCellsProof.euclidNormVec_mono <;> assumption
private theorem norm_attained (x : Torus4 S) :
    ∃ b, torusProj S b = x ∧ (∀ μ, |b μ| = ‖x μ‖) ∧ euclidNormVec b = torusEuclidNorm x ∧
      ∀ v, torusProj S v = x → euclidNormVec b ≤ euclidNormVec v := by
  choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm (x μ)
  have hproj : torusProj S b = x := funext hb
  have hmin : ∀ v, torusProj S v = x → euclidNormVec b ≤ euclidNormVec v := by
    intro v hv
    refine euclidNormVec_mono fun μ => ?_
    rw [hb' μ, ← hv]
    exact addCircle_norm_coe_le_abs _
  refine ⟨b, hproj, hb', ?_, hmin⟩
  have hl : IsLeast (euclidNormVec '' (torusProj S ⁻¹' {x})) (euclidNormVec b) :=
    ⟨⟨b, hproj, rfl⟩, by rintro _ ⟨v, hv, rfl⟩; exact hmin v hv⟩
  exact hl.csInf_eq.symm
private theorem torusEuclidNorm_eq_sqrt (x : Torus4 S) :
    torusEuclidNorm x = Real.sqrt (∑ μ, ‖x μ‖ ^ 2) := by apply _root_.YangMills.Construction.AmbientPoints.torusEuclidNorm_eq_sqrt <;> assumption
private theorem euclidNormVec_add_le (v w : Fin 4 → ℝ) :
    euclidNormVec (v + w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
private theorem eq_zero_of_norm_zero (x : Torus4 S) (h : torusEuclidNorm x = 0) : x = 0 := by apply _root_.YangMills.Construction.Tower.SelectedObjects.eq_zero_of_torusEuclidNorm_eq_zero <;> assumption
end Vectors
variable {D : MirrorData}
private theorem proj_add (y y' : Fin 4 → ℝ) :
    D.projection (y + y') = D.projection y + D.projection y' := torusProj_add y y'
private theorem proj_neg (y : Fin 4 → ℝ) : D.projection (-y) = -D.projection y := torusProj_neg y
private theorem proj_sub (y y' : Fin 4 → ℝ) :
    D.projection (y - y') = D.projection y - D.projection y' := torusProj_sub y y'
private theorem proj_surj : Surjective D.projection := torusProj_surj
private theorem proj_eq_iff (y y' : Fin 4 → ℝ) :
    D.projection y = D.projection y' ↔ ∃ n : Fin 4 → ℤ, y - y' = intCombination D.side n :=
  torusProj_eq_iff y y'
private theorem side_pos (D : MirrorData) : 0 < D.side := by apply _root_.YangMills.Construction.LatticeCovering.period_pos <;> assumption
abbrev _root_.YangMills.SharedProofs.p8577 := @side_pos
private theorem shift_eq (x : D.Torus) (v : Fin 4 → ℝ) :
    D.shift x v = x + D.projection v := by
  have hex : ∃ y, PeriodicLattice.IsLevelLift D.L D.m D.K D.K x y := by
    obtain ⟨y, hy⟩ := proj_surj x
    exact ⟨y, (D.isLiftOf_iff x y).2 hy⟩
  have hy := Classical.epsilon_spec hex
  have hy' : D.projection
      (Classical.epsilon (PeriodicLattice.IsLevelLift D.L D.m D.K D.K x)) = x :=
    (D.isLiftOf_iff _ _).1 hy
  have hc : D.IsLiftOf (PeriodicLattice.torusClassOf D.L D.m D.K D.K
      (Classical.epsilon (PeriodicLattice.IsLevelLift D.L D.m D.K D.K x) + v))
      (Classical.epsilon (PeriodicLattice.IsLevelLift D.L D.m D.K D.K x) + v) :=
    Classical.epsilon_spec (p := fun z => PeriodicLattice.IsLevelLift D.L D.m D.K D.K z _)
      ⟨D.projection _, (D.isLiftOf_iff _ _).2 rfl⟩
  have hc' := (D.isLiftOf_iff _ _).1 hc
  show PeriodicLattice.torusClassOf D.L D.m D.K D.K
      (Classical.epsilon (PeriodicLattice.IsLevelLift D.L D.m D.K D.K x) + v) = _
  rw [← hc', proj_add, hy']
private theorem proj_shift (y v : Fin 4 → ℝ) :
    D.shift (D.projection y) v = D.projection (y + v) := by
  rw [shift_eq, proj_add]
private theorem additive (D : MirrorData) : D.ProjectionAdditive := by
  refine ⟨proj_surj, ?_, ?_, proj_shift, ?_, ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := proj_surj x
    have hp := side_pos D
    refine ⟨fun μ => toIcoMod hp 0 (y μ), ?_, fun μ => ?_⟩
    · funext μ
      have hz : ((toIcoDiv hp 0 (y μ) • D.side : ℝ) :
          AddCircle (PeriodicLattice.torusSide D.L D.m)) = 0 :=
        (AddCircle.coe_eq_zero_iff _).2 ⟨_, rfl⟩
      show ((toIcoMod hp 0 (y μ) : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) =
        (y μ : ℝ)
      rw [toIcoMod, AddCircle.coe_sub, hz, sub_zero]
    · simpa using toIcoMod_mem_Ico hp 0 (y μ)
  · intro y y'
    rw [proj_eq_iff]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, hn.symm⟩, fun ⟨n, hn⟩ => ⟨n, hn.symm⟩⟩
  · intro x x' v
    rw [shift_eq, sub_eq_iff_eq_add']
  · intro x v v'
    rw [shift_eq, shift_eq, shift_eq, proj_add, add_assoc]
private theorem norm_proj_le (y : Fin 4 → ℝ) :
    torusEuclidNorm (D.projection y) ≤ euclidNormVec y := by
  obtain ⟨b, -, -, hn, hmin⟩ := norm_attained (D.projection y)
  rw [← hn]
  exact hmin y rfl
private theorem metric (D : MirrorData) : D.ProjectionMetric := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y y'
    rw [← proj_sub]
    obtain ⟨b, hc, -, hn, hmin⟩ := norm_attained (D.projection (y - y'))
    rw [← hn]
    constructor
    · obtain ⟨n, hn'⟩ := (proj_eq_iff b (y - y')).1 hc
      exact ⟨n, by
        show euclidNormVec (y - y' + intCombination D.side n) = _
        rw [← hn']
        simp⟩
    · rintro _ ⟨n, rfl⟩
      refine hmin _ ((proj_eq_iff _ _).2 ⟨n, ?_⟩)
      simp
  · intro y y'
    rw [← proj_sub]
    exact norm_proj_le _
  · intro y x'
    obtain ⟨b, hc, -, hn, -⟩ := norm_attained (D.projection y - x')
    refine ⟨y - b, ?_, ?_⟩
    · have hc' : D.projection b = D.projection y - x' := hc
      rw [proj_sub, hc']
      abel
    · rw [← hn]
      simp
  · intro x x'
    rw [torusEuclidNorm_eq_sqrt, torusEuclidNorm_eq_sqrt]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← neg_sub x' x, Pi.neg_apply, norm_neg]
  · intro x x' h
    exact sub_eq_zero.mp (eq_zero_of_norm_zero _ h)
  · intro x x' x''
    obtain ⟨b, hc, -, hn, -⟩ := norm_attained (x - x')
    obtain ⟨b', hc', -, hn', -⟩ := norm_attained (x' - x'')
    obtain ⟨b'', -, -, hn'', hmin⟩ := norm_attained (x - x'')
    rw [← hn, ← hn', ← hn'']
    refine (hmin (b + b') ?_).trans (euclidNormVec_add_le b b')
    rw [torusProj_add, hc, hc']
    abel
private theorem coe_add_side_mul_int (α : ℝ) (n : ℤ) :
    ((α + D.side * n : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) = α := by
  have hz : ((D.side * n : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) = 0 :=
    (AddCircle.coe_eq_zero_iff _).2 ⟨n, by rw [zsmul_eq_mul, mul_comm]; rfl⟩
  rw [AddCircle.coe_add, hz, add_zero]
private theorem mem_slabImage (μ : Fin 4) (A : Set ℝ) (y : Fin 4 → ℝ) :
    D.projection y ∈ D.slabImage μ A ↔ y μ ∈ D.periodize A := by
  constructor
  · rintro ⟨y', hy', h⟩
    obtain ⟨n, hn⟩ := (proj_eq_iff y y').1 h.symm
    refine ⟨y' μ, hy', n μ, ?_⟩
    have := congrFun hn μ
    rw [Pi.sub_apply, intCombination_apply] at this
    linarith
  · rintro ⟨α, hα, n, hn⟩
    refine ⟨Function.update y μ α, by simpa [coordSet] using hα, funext fun ν => ?_⟩
    by_cases h : ν = μ
    · subst h
      show ((Function.update y ν α ν : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) =
        (y ν : ℝ)
      rw [Function.update_self, hn, coe_add_side_mul_int]
    · show ((Function.update y μ α ν : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) =
        (y ν : ℝ)
      rw [Function.update_of_ne h]
private theorem slabs (D : MirrorData) : D.ProjectionSlabs := by
  intro μ A B
  refine ⟨mem_slabImage μ A, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left, Set.eq_empty_iff_forall_notMem]
    constructor
    · rintro h t ⟨htA, htB⟩
      exact h ((mem_slabImage μ A (fun _ => t)).2 htA) ⟨fun _ => t, htB, rfl⟩
    · rintro h _ hA ⟨y, hy, rfl⟩
      exact h (y μ) ⟨(mem_slabImage μ A y).1 hA, hy⟩
  · intro h
    ext x
    obtain ⟨y, rfl⟩ := proj_surj x
    rw [mem_slabImage, mem_slabImage, h]
  · intro v
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y + v, ⟨y μ, hy, rfl⟩, (proj_shift y v).symm⟩
    · rintro ⟨y, ⟨α, hα, hy⟩, rfl⟩
      refine ⟨D.projection (y - v), ⟨y - v, ?_, rfl⟩, ?_⟩
      · show (y - v) μ ∈ A
        rw [Pi.sub_apply, hy]
        simpa using hα
      · show D.shift (D.projection (y - v)) v = _
        rw [proj_shift]
        simp
private theorem L_cast_ne (D : MirrorData) : (D.L : ℝ) ≠ 0 := by
  have h := D.isAdmissible.2
  exact_mod_cast (by omega : D.L ≠ 0)
private theorem mesh_ne (D : MirrorData) (j : ℤ) : PeriodicLattice.meshSize D.L j ≠ 0 :=
  zpow_ne_zero _ (L_cast_ne D)
private theorem side_eq_cells_mul (D : MirrorData) (j : ℤ) :
    D.side = D.cellsPerSide j * PeriodicLattice.meshSize D.L j := by
  simp only [Conventions.StandingParameters.side, PeriodicLattice.torusSide,
    MirrorData.cellsPerSide, PeriodicLattice.meshSize]
  rw [mul_assoc, ← zpow_add₀ (L_cast_ne D), add_neg_cancel_right, zpow_natCast]
private theorem mem_sublattice_iff (j : ℤ) (x : D.Torus) :
    x ∈ PeriodicLattice.sublattice D.L D.m j ↔
      ∃ w : Fin 4 → ℤ, x = D.projection (intCombination (PeriodicLattice.meshSize D.L j) w) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, funext fun μ => ?_⟩
    rw [hn μ]
    show _ = ((intCombination (PeriodicLattice.meshSize D.L j) n μ : ℝ) :
      AddCircle (PeriodicLattice.torusSide D.L D.m))
    rw [intCombination_apply, mul_comm]
  · rintro ⟨n, rfl⟩
    refine ⟨n, fun μ => ?_⟩
    show ((intCombination (PeriodicLattice.meshSize D.L j) n μ : ℝ) :
      AddCircle (PeriodicLattice.torusSide D.L D.m)) = _
    rw [intCombination_apply, mul_comm]
private theorem unitStep_eq (j : ℤ) (μ : Fin 4) :
    ((PeriodicLattice.unitStep D.L D.m j μ : PeriodicLattice.Site D.L D.m j) : D.Torus) =
      D.projection (PeriodicLattice.meshSize D.L j • PeriodicLattice.coordVec μ) := by
  funext ν
  show PeriodicLattice.pointOnAxis D.L D.m μ (PeriodicLattice.meshSize D.L j) ν =
    (((PeriodicLattice.meshSize D.L j • PeriodicLattice.coordVec μ) ν : ℝ) :
      AddCircle (PeriodicLattice.torusSide D.L D.m))
  by_cases h : ν = μ
  · subst h
    simp [PeriodicLattice.pointOnAxis, PeriodicLattice.coordVec]
  · simp [PeriodicLattice.pointOnAxis, PeriodicLattice.coordVec, Pi.single_eq_of_ne h]
private theorem signed_step (ε : ℝ) (j : ℤ) (ν : Fin 4) (hε : ε = 1 ∨ ε = -1) :
    D.projection ((ε * PeriodicLattice.meshSize D.L j) • PeriodicLattice.coordVec ν) =
      if ε = 1 then
        ((PeriodicLattice.unitStep D.L D.m j ν : PeriodicLattice.Site D.L D.m j) : D.Torus)
      else
        -((PeriodicLattice.unitStep D.L D.m j ν : PeriodicLattice.Site D.L D.m j) : D.Torus) := by
  rcases hε with rfl | rfl
  · rw [if_pos rfl, unitStep_eq, one_mul]
  · rw [if_neg (by norm_num), unitStep_eq, ← proj_neg]
    congr 1
    rw [neg_one_mul, neg_smul]
private theorem projSites (D : MirrorData) (j : ℤ) (hj : -(D.m : ℤ) ≤ j) :
    D.ProjectionSites j := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (D.m : ℤ) + j = k :=
    ⟨((D.m : ℤ) + j).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hN : D.cellsPerSide j = ((2 * D.L ^ k : ℕ) : ℝ) := by
    simp only [MirrorData.cellsPerSide, hk, zpow_natCast]
    push_cast
    rfl
  have hNz : D.cellsPerSide j = ((2 * (D.L : ℤ) ^ k : ℤ) : ℝ) := by
    rw [hN]
    push_cast
    rfl
  have hLpos : 0 < D.L := by
    have h := D.isAdmissible.2
    omega
  have hside := side_eq_cells_mul D j
  have hsp := mesh_ne D j
  refine ⟨⟨2 * D.L ^ k, by positivity, hN.symm, hside⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨2 * (D.L : ℤ) ^ k * n, ?_⟩
    rw [hside, hNz]
    push_cast
    ring
  · ext x
    rw [SetLike.mem_coe, mem_sublattice_iff]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨_, ⟨w, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, rfl⟩
  · intro y
    rw [mem_sublattice_iff]
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨n, hn⟩ := (proj_eq_iff _ _).1 hw
      refine ⟨fun μ => w μ + 2 * (D.L : ℤ) ^ k * n μ, funext fun μ => ?_⟩
      have := congrFun hn μ
      rw [Pi.sub_apply, intCombination_apply, intCombination_apply, hside, hNz] at this
      rw [intCombination_apply]
      push_cast at this ⊢
      linarith
    · rintro ⟨w, rfl⟩
      exact ⟨w, rfl⟩
  · intro x w
    rw [shift_eq]
    exact add_mem x.2 ((mem_sublattice_iff j _).2 ⟨w, rfl⟩)
  · intro x w w'
    rw [shift_eq, shift_eq, add_right_inj, proj_eq_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, fun μ => ?_⟩
      have := congrFun hn μ
      rw [Pi.sub_apply, intCombination_apply, intCombination_apply, intCombination_apply, hside]
        at this
      apply mul_left_cancel₀ hsp
      push_cast
      linarith
    · rintro ⟨n, hn⟩
      refine ⟨n, funext fun μ => ?_⟩
      rw [Pi.sub_apply, intCombination_apply, intCombination_apply, intCombination_apply, hside]
      have := hn μ
      push_cast at this
      linear_combination (PeriodicLattice.meshSize D.L j) * this
  · intro x x'
    constructor
    · rintro ⟨b, rfl, rfl⟩
      obtain ⟨μ, h | h⟩ := b.isNeighbour
      · refine ⟨1, μ, Or.inl rfl, ?_⟩
        rw [shift_eq, signed_step 1 j μ (Or.inl rfl), if_pos rfl]
        have h' := congrArg Subtype.val h
        rw [AddSubgroup.coe_sub] at h'
        rw [← h']
        abel
      · refine ⟨-1, μ, Or.inr rfl, ?_⟩
        rw [shift_eq, signed_step (-1) j μ (Or.inr rfl), if_neg (by norm_num)]
        have h' := congrArg Subtype.val h
        rw [AddSubgroup.coe_sub, AddSubgroup.coe_neg] at h'
        rw [← h']
        abel
    · rintro ⟨ε, ν, hε, h⟩
      rw [shift_eq, signed_step ε j ν hε] at h
      refine ⟨⟨x, x', ν, ?_⟩, rfl, rfl⟩
      rcases hε with rfl | rfl
      · rw [if_pos rfl] at h
        refine Or.inl (Subtype.ext ?_)
        rw [AddSubgroup.coe_sub, h]
        abel
      · rw [if_neg (by norm_num)] at h
        refine Or.inr (Subtype.ext ?_)
        rw [AddSubgroup.coe_sub, AddSubgroup.coe_neg, h]
        abel
  · intro b
    constructor
    · rintro ⟨μ, h⟩
      refine ⟨μ, ?_⟩
      rw [shift_eq, ← unitStep_eq]
      have h' := congrArg Subtype.val h
      rw [AddSubgroup.coe_sub] at h'
      rw [← h']
      abel
    · rintro ⟨μ, h⟩
      refine ⟨μ, Subtype.ext ?_⟩
      rw [shift_eq, ← unitStep_eq] at h
      rw [AddSubgroup.coe_sub, h]
      abel
private theorem projSitesAtFinest (D : MirrorData) : D.ProjectionSitesAtFinest := by
  refine ⟨rfl, rfl, ?_⟩
  simp only [MirrorData.halfSideCount]
  rw [← Nat.cast_add, zpow_natCast]
  push_cast
  rfl
section Frames
private theorem act_add (R : PeriodicLattice.SignedFrame) (v w : Fin 4 → ℝ) :
    R.actOnVector (v + w) = R.actOnVector v + R.actOnVector w := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.actOnVector_add <;> assumption
private theorem act_sub (R : PeriodicLattice.SignedFrame) (v w : Fin 4 → ℝ) :
    R.actOnVector (v - w) = R.actOnVector v - R.actOnVector w := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryAction.actOnVector_sub <;> assumption
private def invFrame (R : PeriodicLattice.SignedFrame) : PeriodicLattice.SignedFrame :=
  (R.1⁻¹, fun μ => R.2 (R.1⁻¹ μ))
private theorem invFrame_act (R : PeriodicLattice.SignedFrame) (v : Fin 4 → ℝ) :
    (invFrame R).actOnVector (R.actOnVector v) = v := by apply _root_.YangMills.Construction.PeriodicSpace.SupportAdapted.actOnVector_frameInv_actOnVector <;> assumption
private theorem act_invFrame (R : PeriodicLattice.SignedFrame) (v : Fin 4 → ℝ) :
    R.actOnVector ((invFrame R).actOnVector v) = v := by apply _root_.YangMills.Construction.PeriodicSpace.SupportAdapted.actOnVector_actOnVector_frameInv <;> assumption
private def compFrame (R R' : PeriodicLattice.SignedFrame) : PeriodicLattice.SignedFrame :=
  (R.1.trans R'.1, fun μ => R.2 μ * R'.2 (R.1 μ))
private theorem compFrame_act (R R' : PeriodicLattice.SignedFrame) (v : Fin 4 → ℝ) :
    (compFrame R R').actOnVector v = R.actOnVector (R'.actOnVector v) := by
  funext μ
  simp [compFrame, PeriodicLattice.SignedFrame.actOnVector, mul_assoc]
private theorem act_intCombination (R : PeriodicLattice.SignedFrame) (α : ℝ) (n : Fin 4 → ℤ) :
    R.actOnVector (intCombination α n) =
      intCombination α fun μ => (R.2 μ : ℤ) * n (R.1 μ) := by
  funext μ
  simp only [PeriodicLattice.SignedFrame.actOnVector, intCombination_apply]
  push_cast
  ring
private theorem euclidNormVec_act (R : PeriodicLattice.SignedFrame) (v : Fin 4 → ℝ) :
    euclidNormVec (R.actOnVector v) = euclidNormVec v := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryAction.euclidNormVec_actOnVector <;> assumption
private theorem torusEuclidNorm_act (R : PeriodicLattice.SignedFrame) (z : Fin 4 → ℝ) :
    torusEuclidNorm (D.projection (R.actOnVector z)) = torusEuclidNorm (D.projection z) := by
  rw [torusEuclidNorm_eq_sqrt, torusEuclidNorm_eq_sqrt]
  congr 1
  rw [← Equiv.sum_comp R.1 fun μ => ‖D.projection z μ‖ ^ 2]
  refine Finset.sum_congr rfl fun μ _ => ?_
  show ‖((((R.2 μ : ℤ) : ℝ) * z (R.1 μ) : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m))‖ ^ 2 =
    ‖((z (R.1 μ) : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m))‖ ^ 2
  rcases Int.units_eq_one_or (R.2 μ) with h | h
  · simp [h]
  · simp [h]
end Frames
private theorem frameAffine_sub (R : PeriodicLattice.SignedFrame) (v y y' : Fin 4 → ℝ) :
    frameAffine R v y - frameAffine R v y' = R.actOnVector (y - y') := by
  simp [frameAffine, act_sub]
private theorem descends_exists (R : PeriodicLattice.SignedFrame) (v : Fin 4 → ℝ) :
    ∃ s, D.Induces (frameAffine R v) s := by
  refine ⟨fun x => D.projection (frameAffine R v (surjInv (proj_surj (D := D)) x)), ?_⟩
  funext y
  show D.projection (frameAffine R v (surjInv (proj_surj (D := D)) (D.projection y))) =
    D.projection (frameAffine R v y)
  obtain ⟨n, hn⟩ := (proj_eq_iff _ _).1 (surjInv_eq (proj_surj (D := D)) (D.projection y))
  rw [proj_eq_iff, frameAffine_sub, hn, act_intCombination]
  exact ⟨_, rfl⟩
private theorem descended_spec {f : (Fin 4 → ℝ) → Fin 4 → ℝ} (h : ∃ s, D.Induces f s) :
    D.Induces f (D.descended f) :=
  Classical.epsilon_spec h
private theorem descends_apply {f : (Fin 4 → ℝ) → Fin 4 → ℝ} {s : D.Torus → D.Torus}
    (h : D.Induces f s) (y : Fin 4 → ℝ) : s (D.projection y) = D.projection (f y) :=
  congrFun h y
private theorem descends_unique {f : (Fin 4 → ℝ) → Fin 4 → ℝ} {s t : D.Torus → D.Torus}
    (hs : D.Induces f s) (ht : D.Induces f t) : s = t := by
  funext x
  obtain ⟨y, rfl⟩ := proj_surj x
  rw [descends_apply hs, descends_apply ht]
private theorem descends (D : MirrorData) (R : PeriodicLattice.SignedFrame) (v : Fin 4 → ℝ) :
    D.ProjectionDescends R v := by
  have hs : D.Induces (frameAffine R v) (D.descended (frameAffine R v)) :=
    descended_spec (descends_exists R v)
  have hgEq : (fun y => (invFrame R).actOnVector y - (invFrame R).actOnVector v) =
      frameAffine (invFrame R) (-(invFrame R).actOnVector v) := by
    funext y
    simp [frameAffine, sub_eq_add_neg]
  have hg : D.Induces (fun y => (invFrame R).actOnVector y - (invFrame R).actOnVector v)
      (D.descended fun y => (invFrame R).actOnVector y - (invFrame R).actOnVector v) :=
    descended_spec (by rw [hgEq]; exact descends_exists _ _)
  have gf : LeftInverse
      (fun y => (invFrame R).actOnVector y - (invFrame R).actOnVector v)
      (frameAffine R v) := by
    intro y
    simp [frameAffine, act_add, invFrame_act]
  have fg : RightInverse
      (fun y => (invFrame R).actOnVector y - (invFrame R).actOnVector v)
      (frameAffine R v) := by
    intro y
    simp [frameAffine, act_sub, act_invFrame]
  have sg : LeftInverse
      (D.descended fun y => (invFrame R).actOnVector y - (invFrame R).actOnVector v)
      (D.descended (frameAffine R v)) := by
    intro x
    obtain ⟨y, rfl⟩ := proj_surj x
    rw [descends_apply hs, descends_apply hg]
    exact congrArg D.projection (gf y)
  have sg' : RightInverse
      (D.descended fun y => (invFrame R).actOnVector y - (invFrame R).actOnVector v)
      (D.descended (frameAffine R v)) := by
    intro x
    obtain ⟨y, rfl⟩ := proj_surj x
    rw [descends_apply hg, descends_apply hs]
    exact congrArg D.projection (fg y)
  refine ⟨⟨R.1⁻¹, fun ν => R.2 (R.1⁻¹ ν), fun ν => ?_⟩,
    bijective_iff_has_inverse.2 ⟨_, gf, fg⟩, ?_,
    ⟨invFrame R, ⟨invFrame_act R, act_invFrame R⟩, gf, fg, sg, sg'⟩,
    ⟨_, hs, fun t ht => descends_unique ht hs⟩, hs,
    bijective_iff_has_inverse.2 ⟨_, sg, sg'⟩, ?_, ?_, ?_, ?_⟩
  · funext μ
    simp only [PeriodicLattice.SignedFrame.actOnVector, PeriodicLattice.coordVec, Pi.smul_apply,
      smul_eq_mul]
    by_cases h : R.1 μ = ν
    · subst h
      simp
    · have h' : μ ≠ R.1.symm ν := fun e => h (by rw [e]; simp)
      simp [h, h']
  · intro y y'
    rw [frameAffine_sub, euclidNormVec_act]
  · intro x x'
    obtain ⟨y, rfl⟩ := proj_surj x
    obtain ⟨y', rfl⟩ := proj_surj x'
    rw [descends_apply hs, descends_apply hs, ← proj_sub, ← proj_sub, frameAffine_sub,
      torusEuclidNorm_act]
  · intro Z
    rw [image_image, image_image]
    exact image_congr fun y _ => descends_apply hs y
  · intro x v'
    obtain ⟨y, rfl⟩ := proj_surj x
    rw [proj_shift, descends_apply hs, descends_apply hs, proj_shift]
    congr 1
    simp only [frameAffine, act_add]
    abel
  · intro R' v'
    refine ⟨⟨compFrame R R', R.actOnVector v' + v, funext fun y => ?_⟩, ?_⟩
    · simp [frameAffine, compFrame_act, act_add, add_assoc]
    · funext y
      have hs' : D.Induces (frameAffine R' v') (D.descended (frameAffine R' v')) :=
        descended_spec (descends_exists R' v')
      simp only [comp_apply]
      rw [descends_apply hs', descends_apply hs]
theorem holds : ProjectionFacts := fun D =>
  ⟨additive D, metric D, slabs D, fun j hj => projSites D j hj, projSitesAtFinest D,
    fun R v => descends D R v⟩
end YangMills.Construction.ReflectionPositivity.AxisMirror.ProjectionFacts

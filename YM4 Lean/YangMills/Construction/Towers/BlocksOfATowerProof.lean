import YangMills.Construction.Lattice.AxialPathReversalProof
import YangMills.Construction.Lattice.BareBaseSitesOfTheSchemesProof
import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlockProof
import YangMills.Construction.Lattice.OneStepObjectsReadInTheChartProof
import YangMills.Construction.Towers.BlocksCorridorsPivotBondsAndPathsProof
import YangMills.Construction.Towers.BlocksOfATower
import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.BlockStructureProof
open InfiniteLattice (AmbientSpace)
open PeriodicLattice (FourTorus pointOnAxis)
theorem meshAt_pos {L : ℕ} (hL : 0 < L) (k j : ℕ) : 0 < meshAt L k j :=
  zpow_pos (by exact_mod_cast hL) _
theorem meshAt_eq_mul_pred {L : ℕ} (hL : 0 < L) (k : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    meshAt L k j = (L : ℝ) * meshAt L k (j - 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [meshAt, Nat.add_sub_cancel]
  rw [show ((i + 1 : ℕ) : ℤ) - (k : ℤ) = 1 + ((i : ℤ) - (k : ℤ)) by push_cast; ring,
    zpow_add₀ hL', zpow_one]
def signedPermute (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) (ν : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun μ => (s μ : ℤ) * ν (π μ)
theorem abs_units_mul (u : ℤˣ) (z : ℤ) : |(u : ℤ) * z| = |z| := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]
theorem units_mul_units_mul (u : ℤˣ) (z : ℤ) : (u : ℤ) * ((u : ℤ) * z) = z := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]
theorem image_signedPermute_blockOffsets (L : ℕ) (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) :
    signedPermute π s '' PeriodicLattice.blockOffsets L 1 =
      PeriodicLattice.blockOffsets L 1 := by
  ext ν'
  constructor
  · rintro ⟨ν, hν, rfl⟩ μ
    simpa only [signedPermute, abs_units_mul] using hν (π μ)
  · intro hν'
    refine ⟨fun κ => (s (π.symm κ) : ℤ) * ν' (π.symm κ), fun κ => ?_, ?_⟩
    · simpa only [abs_units_mul] using hν' (π.symm κ)
    · funext μ
      simp only [signedPermute, Equiv.symm_apply_apply, units_mul_units_mul]
theorem sum_single_apply (c : Fin 4 → ℝ) (ρ : Fin 4) :
    (∑ μ, (Pi.single μ (c μ) : AmbientSpace)) ρ = c ρ := by
  simp [Finset.sum_apply, Pi.single_apply]
theorem apply_sum_single_signedPermute {w : AmbientSpace → AmbientSpace}
    {π : Equiv.Perm (Fin 4)} {s : Fin 4 → ℤˣ}
    (hw : ∀ x μ, w x μ = ((s μ : ℤ) : ℝ) * x (π μ)) (a : ℝ) (ν : Fin 4 → ℤ) :
    w (∑ μ, Pi.single μ ((ν μ : ℝ) * a)) =
      ∑ μ, Pi.single μ ((signedPermute π s ν μ : ℝ) * a) := by
  funext ρ
  rw [hw, sum_single_apply (fun μ => (ν μ : ℝ) * a),
    sum_single_apply (fun μ => (signedPermute π s ν μ : ℝ) * a)]
  simp only [signedPermute, Int.cast_mul]
  ring
section SpacePaths
variable {a : ℝ}
theorem coe_zsmul_axisStep (t : ℤ) (μ : Fin 4) :
    ((t • InfiniteLattice.axisStep a μ : InfiniteLattice.LatticePoint a) : AmbientSpace) =
      Pi.single μ ((t : ℝ) * a) := by
  funext ρ
  by_cases h : ρ = μ
  · subst h
    simp [InfiniteLattice.axisStep]
  · simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne h]
theorem length_forwardSteps (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℕ) :
    (FullSpace.forwardSteps x μ n).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [FullSpace.forwardSteps, ih]
theorem length_backwardSteps (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℕ) :
    (FullSpace.backwardSteps x μ n).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [FullSpace.backwardSteps, ih]
theorem bondAlongAxis_of_mem_forwardSteps (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℕ)
    (b : InfiniteLattice.Link a) (hb : b ∈ FullSpace.forwardSteps x μ n) :
    FullSpace.BondAlongAxis b μ := by
  induction n generalizing x with
  | zero => simp [FullSpace.forwardSteps] at hb
  | succ n ih =>
    rw [FullSpace.forwardSteps, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact Or.inl (by simp [InfiniteLattice.Link.forwardFrom])
    · exact ih _ hb
theorem bondAlongAxis_of_mem_backwardSteps (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℕ)
    (b : InfiniteLattice.Link a) (hb : b ∈ FullSpace.backwardSteps x μ n) :
    FullSpace.BondAlongAxis b μ := by
  induction n generalizing x with
  | zero => simp [FullSpace.backwardSteps] at hb
  | succ n ih =>
    rw [FullSpace.backwardSteps, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact Or.inr (by simp [FullSpace.backwardLink])
    · exact ih _ hb
theorem axisPath_eq_signedSteps (ha : a ≠ 0) {x x' : InfiniteLattice.LatticePoint a} {μ : Fin 4}
    {n : ℤ} (hn : n ≠ 0) (h : FullSpace.IsAxisDisplacement x x' μ n) :
    FullSpace.axisPath x x' = FullSpace.signedSteps x μ n := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.axisPath_eq <;> assumption
theorem axisPath_length_and_axis {L : ℕ} (hL : 0 < L) (ha : a ≠ 0)
    {x x' : InfiniteLattice.LatticePoint a}
    {μ : Fin 4} {t : ℤ} (ht : |t| = (L : ℤ)) (h : FullSpace.IsAxisDisplacement x x' μ t) :
    (FullSpace.axisPath x x').length = L ∧
      ∀ b ∈ FullSpace.axisPath x x', FullSpace.BondAlongAxis b μ := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
    omega
  rw [axisPath_eq_signedSteps ha ht0 h]
  unfold FullSpace.signedSteps
  split_ifs with hs
  · refine ⟨?_, fun b hb => bondAlongAxis_of_mem_forwardSteps _ _ _ b hb⟩
    rw [length_forwardSteps]
    rw [abs_of_nonneg hs] at ht
    omega
  · refine ⟨?_, fun b hb => bondAlongAxis_of_mem_backwardSteps _ _ _ b hb⟩
    rw [length_backwardSteps]
    rw [abs_of_neg (not_le.mp hs)] at ht
    omega
end SpacePaths
section SpaceBlocks
variable {L k j : ℕ}
theorem space_blockEqOffsetImage (P : FullSpace.CubesOfOrderPartition L k j 1)
    (y : FullSpace.Vertex L k j) :
    FullSpace.BlockEqOffsetImage L k j y := by
  have hbox : offsetBox L 1 = PeriodicLattice.blockOffsets L 1 := by
    ext ν
    exact mem_offsetBox_iff
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨ν, hν, rfl⟩
      exact ⟨ν, hν, rfl⟩
    · rintro ⟨ν, hν, rfl⟩
      exact ⟨ν, hν, rfl⟩
  · have h := P.offsetPoint_injOn y
    rw [hbox] at h
    exact h
  · simpa using P.cube_ncard y
  · intro x hx
    have : x ∈ ⋃ y : FullSpace.Vertex L k j,
        FullSpace.cubeOfOrder L (meshAt L k (j - 1)) 1 y := mem_iUnion.mpr ⟨y, hx⟩
    rw [P.iUnion_cube] at this
    exact this
theorem space_center_unique (P : FullSpace.CubesOfOrderPartition L k j 1)
    {y y' : FullSpace.Vertex L k j} {x : AmbientSpace}
    (h : x ∈ FullSpace.cube L (meshAt L k (j - 1)) y)
    (h' : x ∈ FullSpace.cube L (meshAt L k (j - 1)) y') : y = y' := by
  by_contra hne
  have hd : Disjoint (FullSpace.cubeOfOrder L (meshAt L k (j - 1)) 1 y)
      (FullSpace.cubeOfOrder L (meshAt L k (j - 1)) 1 y') := P.pairwise_disjoint_cube hne
  exact Set.disjoint_left.mp hd h h'
theorem space_exists_center (P : FullSpace.CubesOfOrderPartition L k j 1)
    (x : FullSpace.Vertex L k (j - 1)) :
    ∃ y : FullSpace.Vertex L k j, (x : AmbientSpace) ∈ FullSpace.cube L (meshAt L k (j - 1)) y := by
  have hx : (x : AmbientSpace) ∈ ⋃ y : FullSpace.Vertex L k j,
      FullSpace.cubeOfOrder L (meshAt L k (j - 1)) 1 y := by
    rw [P.iUnion_cube]
    exact x.2
  exact mem_iUnion.mp hx
theorem space_blocksPartitionFiner (P : FullSpace.CubesOfOrderPartition L k j 1) :
    FullSpace.BlocksPartitionFiner L k j := by
  refine ⟨fun y => ?_, fun x => ?_, fun x hx => ?_⟩
  · ext z
    constructor
    · rintro ⟨hz, hzl⟩
      have h := space_center_unique P hz (P.center_mem ⟨z, hzl⟩)
      exact (congrArg Subtype.val h).symm
    · rintro rfl
      exact ⟨P.center_mem y, y.2⟩
  · obtain ⟨y, hy⟩ := space_exists_center P x
    exact ⟨y, hy, fun y' hy' => space_center_unique P hy' hy⟩
  · obtain ⟨y, hy⟩ := space_exists_center P x
    refine ⟨y, ⟨hy, fun hxy => hx ?_⟩, fun y' hy' => space_center_unique P hy'.1 hy⟩
    rw [Set.mem_singleton_iff.mp hxy]
    exact y.2
theorem space_blockTranslateAlongBond (hL : 0 < L) (hj : 1 ≤ j)
    (P : FullSpace.CubesOfOrderPartition L k j 1)
    (c : FullSpace.Edge L k j) (μ : Fin 4) (hc : FullSpace.BondAlongAxis c μ) :
    FullSpace.BlockTranslateAlongBond L k j c μ := by
  have ha := (meshAt_pos hL k (j - 1)).ne'
  have hsp := meshAt_eq_mul_pred hL k hj
  refine ⟨?_, fun x x' _ hx' => ?_⟩
  · have h := P.cube_add c.initial (c.terminal - c.initial)
    rw [add_sub_cancel] at h
    have e : ((c.terminal - c.initial : FullSpace.Vertex L k j) : AmbientSpace) =
        (c.terminal : AmbientSpace) - (c.initial : AmbientSpace) := rfl
    rw [e] at h
    rw [show FullSpace.cube L (meshAt L k (j - 1)) c.terminal =
      FullSpace.cubeOfOrder L (meshAt L k (j - 1)) 1 c.terminal from rfl, h]
    exact (add_left_injective _).injOn.bijOn_image
  · have hd : (x' : AmbientSpace) - (x : AmbientSpace) =
        (c.terminal : AmbientSpace) - (c.initial : AmbientSpace) := by
      rw [hx']
      abel
    have key : ∀ t : ℤ, |t| = (L : ℤ) →
        (c.terminal : AmbientSpace) - (c.initial : AmbientSpace) =
          Pi.single μ ((t : ℝ) * meshAt L k (j - 1)) →
        (∃ t : ℤ, |t| = (L : ℤ) ∧ FullSpace.IsAxisDisplacement x x' μ t) ∧
          (FullSpace.axisPath x x').length = L ∧
          ∀ b ∈ FullSpace.axisPath x x', FullSpace.BondAlongAxis b μ := by
      intro t ht he
      have hs : FullSpace.IsAxisDisplacement x x' μ t := by
        apply Subtype.ext
        rw [coe_zsmul_axisStep, ← he, ← hd]
        rfl
      exact ⟨⟨t, ht, hs⟩, axisPath_length_and_axis hL ha ht hs⟩
    rcases hc with hc | hc
    · have he : (c.terminal : AmbientSpace) - (c.initial : AmbientSpace) =
          Pi.single μ ((L : ℝ) * meshAt L k (j - 1)) := by
        rw [← hsp]
        exact congrArg Subtype.val hc
      exact ⟨Or.inl (hd.trans he), key (L : ℤ) (by simp) (by simpa using he)⟩
    · have he : (c.terminal : AmbientSpace) - (c.initial : AmbientSpace) =
          Pi.single μ (-((L : ℝ) * meshAt L k (j - 1))) := by
        rw [← hsp]
        have h := congrArg Subtype.val hc
        funext ρ
        have h' := congrFun h ρ
        by_cases hρ : ρ = μ
        · subst hρ
          simpa [InfiniteLattice.axisStep] using h'
        · simpa [InfiniteLattice.axisStep, Pi.single_eq_of_ne hρ] using h'
      exact ⟨Or.inr (hd.trans he), key (-(L : ℤ)) (by simp) (by simpa using he)⟩
theorem coe_space_vertexImage {a : ℝ} {f : AmbientSpace → AmbientSpace}
    (hf : FullSpace.MapsSublatticeOnto a f)
    (y : InfiniteLattice.LatticePoint a) :
    ((FullSpace.vertexImage f y : InfiniteLattice.LatticePoint a) : AmbientSpace) = f y := by
  have hmem : f y ∈ (InfiniteLattice.latticeSubgroup a : Set AmbientSpace) := by
    rw [← hf]
    exact mem_image_of_mem f y.2
  exact Classical.epsilon_spec
    (p := fun x' : InfiniteLattice.LatticePoint a => (x' : AmbientSpace) = f y) ⟨⟨f y, hmem⟩, rfl⟩
theorem space_symmetryMapsBlocks
    (hdisp : ∀ y : FullSpace.Vertex L k j, FullSpace.BlockEqOffsetImage L k j y)
    (hiso : FullSpace.SpaceSymmetries L k) (hjk : j ≤ k) :
    FullSpace.SymmetryMapsBlocks L k j := by
  intro f hf hl y
  obtain ⟨⟨w, hw, v, -, hfw⟩, -⟩ := hiso j hjk f hf hl
  obtain ⟨π, s, hws⟩ := (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff w).mp hw
  have hmove : ∀ ν, f (FullSpace.offsetPoint (meshAt L k (j - 1)) (y : AmbientSpace) ν) =
      FullSpace.offsetPoint (meshAt L k (j - 1)) (f y) (signedPermute π s ν) := by
    intro ν
    have h := apply_sum_single_signedPermute (w := w) hws (meshAt L k (j - 1)) ν
    unfold FullSpace.offsetPoint
    rw [hfw, hfw, map_add, h]
    abel
  rw [(hdisp y).1, (hdisp (FullSpace.vertexImage f y)).1, coe_space_vertexImage hl y]
  calc f '' (FullSpace.offsetPoint (meshAt L k (j - 1)) (y : AmbientSpace) ''
        PeriodicLattice.blockOffsets L 1)
      = (fun ν => FullSpace.offsetPoint (meshAt L k (j - 1)) (f y) (signedPermute π s ν)) ''
          PeriodicLattice.blockOffsets L 1 := by
        rw [image_image]
        exact image_congr fun ν _ => hmove ν
    _ = FullSpace.offsetPoint (meshAt L k (j - 1)) (f y) ''
          (signedPermute π s '' PeriodicLattice.blockOffsets L 1) := by
        rw [image_image]
    _ = _ := by rw [image_signedPermute_blockOffsets]
end SpaceBlocks
section TorusSteps
variable {L m : ℕ} {d : ℤ}
theorem zsmul_pointOnAxis (μ : Fin 4) (t : ℤ) (c : ℝ) :
    t • pointOnAxis L m μ c = pointOnAxis L m μ ((t : ℝ) * c) := by
  funext ρ
  by_cases h : ρ = μ
  · subst h
    simp only [pointOnAxis, Pi.smul_apply, Pi.single_eq_same]
    rw [← zsmul_eq_mul]
    exact (map_zsmul (QuotientAddGroup.mk' _) t c).symm
  · simp [pointOnAxis, Pi.single_eq_of_ne h]
theorem pointOnAxis_neg (μ : Fin 4) (c : ℝ) : pointOnAxis L m μ (-c) = -pointOnAxis L m μ c := by apply _root_.YangMills.Construction.CellGrid.pointOnAxis_neg <;> assumption
theorem coe_zsmul_unitStep (t : ℤ) (μ : Fin 4) :
    ((t • PeriodicLattice.unitStep L m d μ : PeriodicLattice.Site L m d) : FourTorus L m) =
      pointOnAxis L m μ ((t : ℝ) * PeriodicLattice.meshSize L d) := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.coe_zsmul_unitStep <;> assumption
theorem eq_zero_of_coe_mul_meshSize (hL : 0 < L) (t : ℤ)
    (hN : |(t : ℝ)| < 2 * (L : ℝ) ^ ((m : ℤ) + d))
    (h : (((t : ℝ) * PeriodicLattice.meshSize L d : ℝ) :
      AddCircle (PeriodicLattice.torusSide L m)) = 0) :
    t = 0 := by apply _root_.YangMills.Construction.PeriodicLattice.AxialReversal.int_eq_zero_of_smul_meshSize_coe_eq_zero <;> assumption
theorem zsmul_unitStep_injective (hL : 0 < L) {ν μ : Fin 4} {t n : ℤ} (hn : n ≠ 0)
    (ht : |(t : ℝ)| < (L : ℝ) ^ ((m : ℤ) + d)) (hnb : |(n : ℝ)| < (L : ℝ) ^ ((m : ℤ) + d))
    (e : t • PeriodicLattice.unitStep L m d ν = n • PeriodicLattice.unitStep L m d μ) :
    ν = μ ∧ t = n := by
  have hc : pointOnAxis L m ν ((t : ℝ) * PeriodicLattice.meshSize L d) =
      pointOnAxis L m μ ((n : ℝ) * PeriodicLattice.meshSize L d) := by
    rw [← coe_zsmul_unitStep, ← coe_zsmul_unitStep, e]
  have hμ := congrFun hc μ
  simp only [pointOnAxis, Pi.single_eq_same] at hμ
  have hνμ : ν = μ := by
    by_contra hne
    rw [Pi.single_eq_of_ne (Ne.symm hne)] at hμ
    exact hn (eq_zero_of_coe_mul_meshSize hL n (by linarith [abs_nonneg (n : ℝ)]) hμ.symm)
  subst hνμ
  rw [Pi.single_eq_same] at hμ
  have h0 : ((((t - n : ℤ) : ℝ) * PeriodicLattice.meshSize L d : ℝ) :
      AddCircle (PeriodicLattice.torusSide L m)) = 0 := by
    rw [Int.cast_sub, sub_mul, AddCircle.coe_sub, hμ, sub_self]
  have h1 := eq_zero_of_coe_mul_meshSize hL (t - n) (by
    rw [Int.cast_sub]
    exact (abs_sub _ _).trans_lt (by linarith)) h0
  exact ⟨rfl, by omega⟩
theorem axialPath_eq_flowAlong (hL : 0 < L) {x x' : PeriodicLattice.Site L m d} {μ : Fin 4}
    {n : ℤ} (hn : n ≠ 0) (h : PeriodicLattice.IsAxialDisplacement x x' μ n) :
    PeriodicLattice.axialPath x x' = PeriodicLattice.flowAlong x μ n := by
  have hex : ∃ q : Fin 4 × ℤ, PeriodicLattice.IsAxialDisplacement x x' q.1 q.2 := ⟨(μ, n), h⟩
  have hq := hex.choose_spec
  have hab : ∀ t : ℤ, ((|t| : ℤ) : ℝ) = |(t : ℝ)| := fun t => by simp
  have h1 := hq.2
  have h2 := h.2
  rw [hab] at h1 h2
  obtain ⟨e1, e2⟩ := zsmul_unitStep_injective hL hn h1 h2 (hq.1.symm.trans h.1)
  unfold PeriodicLattice.axialPath
  rw [dif_pos hex, e1, e2]
theorem length_forwardFlow (x : PeriodicLattice.Site L m d) (μ : Fin 4) (n : ℕ) :
    (PeriodicLattice.forwardAxisPath x μ n).length = n := by apply _root_.YangMills.SharedProofs.p1058 <;> assumption
theorem length_backwardFlow (x : PeriodicLattice.Site L m d) (μ : Fin 4) (n : ℕ) :
    (PeriodicLattice.backwardAxisPath x μ n).length = n := by apply _root_.YangMills.SharedProofs.p8383 <;> assumption
theorem bondAlongAxis_of_mem_forwardFlow (x : PeriodicLattice.Site L m d) (μ : Fin 4) (n : ℕ)
    (b : PeriodicLattice.Bond L m d) (hb : b ∈ PeriodicLattice.forwardAxisPath x μ n) :
    BondAlongAxis b μ := by
  induction n generalizing x with
  | zero => simp [PeriodicLattice.forwardAxisPath] at hb
  | succ n ih =>
    rw [PeriodicLattice.forwardAxisPath, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact Or.inl (by simp [PeriodicLattice.Bond.forwardFrom])
    · exact ih _ hb
theorem bondAlongAxis_of_mem_backwardFlow (x : PeriodicLattice.Site L m d) (μ : Fin 4) (n : ℕ)
    (b : PeriodicLattice.Bond L m d) (hb : b ∈ PeriodicLattice.backwardAxisPath x μ n) :
    BondAlongAxis b μ := by
  induction n generalizing x with
  | zero => simp [PeriodicLattice.backwardAxisPath] at hb
  | succ n ih =>
    rw [PeriodicLattice.backwardAxisPath, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact Or.inr (by simp [PeriodicLattice.Bond.backwardFrom])
    · exact ih _ hb
theorem axialPath_length_and_axis (hL : 0 < L) {x x' : PeriodicLattice.Site L m d} {μ : Fin 4}
    {t : ℤ} (ht : |t| = (L : ℤ)) (h : PeriodicLattice.IsAxialDisplacement x x' μ t) :
    (PeriodicLattice.axialPath x x').length = L ∧
      ∀ b ∈ PeriodicLattice.axialPath x x', BondAlongAxis b μ := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
    omega
  rw [axialPath_eq_flowAlong hL ht0 h]
  unfold PeriodicLattice.flowAlong
  split_ifs with hs
  · refine ⟨?_, fun b hb => bondAlongAxis_of_mem_forwardFlow _ _ _ b hb⟩
    rw [length_forwardFlow]
    rw [abs_of_nonneg hs] at ht
    omega
  · refine ⟨?_, fun b hb => bondAlongAxis_of_mem_backwardFlow _ _ _ b hb⟩
    rw [length_backwardFlow]
    rw [abs_of_neg (not_le.mp hs)] at ht
    omega
end TorusSteps
section TorusBlocks
variable {L n k j : ℕ}
theorem levelDepth_pred (hj : 1 ≤ j) :
    PeriodicLattice.levelDepth k (j - 1) = PeriodicLattice.levelDepth k j + ((1 : ℕ) : ℤ) := by
  simp only [PeriodicLattice.levelDepth]
  omega
theorem coe_toSublattice (hL : 0 < L) {d d' : ℤ} (h : d ≤ d') (y : PeriodicLattice.Site L n d) :
    ((y.toSublattice d' : PeriodicLattice.Site L n d') : FourTorus L n) = y := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
theorem coe_refinedOffsetSite (hL : 0 < L) {d : ℤ} (y : PeriodicLattice.Site L n d)
    (p : Fin 4 → ℤ) :
    ((PeriodicLattice.refinedOffsetSite 1 y p :
        PeriodicLattice.Site L n (d + ((1 : ℕ) : ℤ))) : FourTorus L n) =
      offsetPoint (PeriodicLattice.meshSize L (d + ((1 : ℕ) : ℤ))) (y : FourTorus L n) p := by
  unfold PeriodicLattice.refinedOffsetSite PeriodicLattice.offsetSite offsetPoint
  rw [AddSubgroup.coe_add, coe_toSublattice hL (by omega) y]
  congr 1
  exact (map_sum (PeriodicLattice.sublattice L n (d + ((1 : ℕ) : ℤ))).subtype
    (fun μ => p μ • PeriodicLattice.unitStep L n (d + ((1 : ℕ) : ℤ)) μ) Finset.univ).trans
    (Finset.sum_congr rfl fun μ _ => coe_zsmul_unitStep (p μ) μ)
theorem meshSize_levelDepth_succ (hj : 1 ≤ j) :
    PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j + ((1 : ℕ) : ℤ)) =
      meshAt L k (j - 1) := by
  rw [← levelDepth_pred hj, meshSize_levelDepth]
theorem torus_blockEqOffsetImage (hL : 0 < L) (hj : 1 ≤ j) (y : Vertex L n k j)
    (P : PeriodicLattice.RefinedBlockEqOffsetImage L n (PeriodicLattice.levelDepth k j) 1 y) :
    BlockEqOffsetImage L n k j y := by
  have hf : (fun p => ((PeriodicLattice.refinedOffsetSite 1 y p :
      PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j + ((1 : ℕ) : ℤ))) :
        FourTorus L n)) =
      offsetPoint (meshAt L k (j - 1)) (y : FourTorus L n) := by
    funext p
    rw [coe_refinedOffsetSite hL, meshSize_levelDepth_succ hj]
  obtain ⟨h1, h2, h3⟩ := P
  rw [hf] at h1 h2
  refine ⟨h1, h2, by simpa using h3, ?_⟩
  intro x hx
  rw [levelDepth_pred hj]
  have hx' : x ∈ PeriodicLattice.refinedBlock 1 y := hx
  exact hx'.2
theorem torus_blocksPartitionFiner (hj : 1 ≤ j)
    (P : PeriodicLattice.RefinedBlocksPartition L n (PeriodicLattice.levelDepth k j) 1) :
    BlocksPartitionFiner L n k j := by
  obtain ⟨hself, -, hdisj, hcover⟩ := P
  have huniq : ∀ {y y' : Vertex L n k j} {x : FourTorus L n}, x ∈ PeriodicLattice.unitBlock y →
      x ∈ PeriodicLattice.unitBlock y' → y = y' := by
    intro y y' x h h'
    by_contra hne
    have hd : Disjoint (PeriodicLattice.refinedBlock 1 y) (PeriodicLattice.refinedBlock 1 y') :=
      hdisj hne
    exact Set.disjoint_left.mp hd h h'
  have hex : ∀ x : Vertex L n k (j - 1), ∃ y : Vertex L n k j,
      (x : FourTorus L n) ∈ PeriodicLattice.unitBlock y := by
    intro x
    have hx : (x : FourTorus L n) ∈ ⋃ y : Vertex L n k j, PeriodicLattice.refinedBlock 1 y := by
      rw [hcover, ← levelDepth_pred hj]
      exact x.2
    exact mem_iUnion.mp hx
  refine ⟨fun y => ?_, fun x => ?_, fun x hx => ?_⟩
  · ext z
    constructor
    · rintro ⟨hz, hzl⟩
      have h := huniq hz (hself ⟨z, hzl⟩)
      exact (congrArg Subtype.val h).symm
    · rintro rfl
      exact ⟨hself y, y.2⟩
  · obtain ⟨y, hy⟩ := hex x
    exact ⟨y, hy, fun y' hy' => huniq hy' hy⟩
  · obtain ⟨y, hy⟩ := hex x
    refine ⟨y, ⟨hy, fun hxy => hx ?_⟩, fun y' hy' => huniq hy'.1 hy⟩
    rw [Set.mem_singleton_iff.mp hxy]
    exact y.2
theorem torus_blockTranslateAlongBond (hL : 13 ≤ L) (hn : 0 < n) (hj : 1 ≤ j) (hjk : j ≤ k)
    (hdisp : ∀ y : Vertex L n k j, BlockEqOffsetImage L n k j y)
    (c : Edge L n k j) (μ : Fin 4) (hc : BondAlongAxis c μ) :
    BlockShiftAlongBond L n k j c μ := by
  have hL0 : 0 < L := by omega
  have hsp := meshAt_eq_mul_pred hL0 k hj
  refine ⟨?_, fun x x' _ hx' => ?_⟩
  · have himg : (fun x : FourTorus L n =>
        x + ((c.target : FourTorus L n) - (c.source : FourTorus L n))) ''
        PeriodicLattice.unitBlock c.source = PeriodicLattice.unitBlock c.target := by
      rw [(hdisp c.source).1, (hdisp c.target).1, image_image]
      refine image_congr fun ν _ => ?_
      unfold offsetPoint
      abel
    rw [← himg]
    exact (add_left_injective _).injOn.bijOn_image
  · have hd : (x' : FourTorus L n) - (x : FourTorus L n) =
        (c.target : FourTorus L n) - (c.source : FourTorus L n) := by
      rw [hx']
      abel
    have hbound : (L : ℝ) < (L : ℝ) ^ ((n : ℤ) + PeriodicLattice.levelDepth k (j - 1)) := by
      have h1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
      have h2 := zpow_lt_zpow_right₀ h1
        (show (1 : ℤ) < (n : ℤ) + PeriodicLattice.levelDepth k (j - 1) by
          simp only [PeriodicLattice.levelDepth]
          omega)
      simpa using h2
    have key : ∀ t : ℤ, |t| = (L : ℤ) →
        (c.target : FourTorus L n) - (c.source : FourTorus L n) =
          pointOnAxis L n μ ((t : ℝ) * meshAt L k (j - 1)) →
        (∃ t : ℤ, |t| = (L : ℤ) ∧ PeriodicLattice.IsAxialDisplacement x x' μ t) ∧
          (PeriodicLattice.axialPath x x').length = L ∧
          ∀ b ∈ PeriodicLattice.axialPath x x', BondAlongAxis b μ := by
      intro t ht he
      have hs : PeriodicLattice.IsAxialDisplacement x x' μ t := by
        refine ⟨?_, ?_⟩
        · apply Subtype.ext
          rw [coe_zsmul_unitStep, meshSize_levelDepth, ← he, ← hd]
          rfl
        · rw [ht]
          simpa using hbound
      exact ⟨⟨t, ht, hs⟩, axialPath_length_and_axis hL0 ht hs⟩
    have hstep : ((PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ :
        Vertex L n k j) : FourTorus L n) =
        pointOnAxis L n μ ((L : ℝ) * meshAt L k (j - 1)) := by
      rw [← hsp, ← meshSize_levelDepth]
      rfl
    rcases hc with hc | hc
    · have he : (c.target : FourTorus L n) - (c.source : FourTorus L n) =
          pointOnAxis L n μ ((L : ℝ) * meshAt L k (j - 1)) := by
        rw [← hstep]
        exact congrArg Subtype.val hc
      exact ⟨Or.inl (hd.trans he), key (L : ℤ) (by simp) (by simpa using he)⟩
    · have he : (c.target : FourTorus L n) - (c.source : FourTorus L n) =
          pointOnAxis L n μ (-((L : ℝ) * meshAt L k (j - 1))) := by
        rw [pointOnAxis_neg, ← hstep]
        exact congrArg Subtype.val hc
      exact ⟨Or.inr (hd.trans he), key (-(L : ℤ)) (by simp) (by simpa using he)⟩
theorem coe_torus_vertexImage {f : FourTorus L n → FourTorus L n}
    (hf : MapsSublatticeOnto k j f)
    (y : Vertex L n k j) : ((vertexImage f y : Vertex L n k j) : FourTorus L n) = f y := by
  have hmem : f y ∈ (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) :
      Set (FourTorus L n)) := by
    rw [← hf]
    exact mem_image_of_mem f y.2
  exact Classical.epsilon_spec
    (p := fun x' : Vertex L n k j => (x' : FourTorus L n) = f y) ⟨⟨f y, hmem⟩, rfl⟩
theorem offsetPoint_torusProj (a : ℝ) (r : AmbientSpace) (ν : Fin 4 → ℤ) :
    offsetPoint a (TorusMetric.torusProj (PeriodicLattice.torusSide L n) r : FourTorus L n) ν =
      TorusMetric.torusProj (PeriodicLattice.torusSide L n)
        (r + ∑ μ, Pi.single μ ((ν μ : ℝ) * a)) := by
  funext ρ
  simp only [offsetPoint, TorusMetric.torusProj, Pi.add_apply, AddCircle.coe_add]
  rw [sum_single_apply (fun μ => (ν μ : ℝ) * a)]
  simp [Finset.sum_apply, pointOnAxis, Pi.single_apply]
theorem torus_symmetryMapsBlocks (hdisp : ∀ y : Vertex L n k j, BlockEqOffsetImage L n k j y)
    (hiso : TorusSymmetries L n k) (hjk : j ≤ k) : SymmetryMapsBlocks L n k j := by
  intro f hf hl y
  obtain ⟨⟨w, hw, v, -, hfw⟩, -⟩ := hiso j hjk f hf hl
  obtain ⟨π, s, hws⟩ := (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff w).mp hw
  obtain ⟨r, hr⟩ : ∃ r : AmbientSpace,
      TorusMetric.torusProj (PeriodicLattice.torusSide L n) r = (y : FourTorus L n) := by
    have hlift : ∀ μ, ∃ t : ℝ,
        (t : AddCircle (PeriodicLattice.torusSide L n)) = (y : FourTorus L n) μ :=
      fun μ => QuotientAddGroup.mk_surjective _
    choose r hr using hlift
    exact ⟨r, funext hr⟩
  have hmove : ∀ ν, f (offsetPoint (meshAt L k (j - 1)) (y : FourTorus L n) ν) =
      offsetPoint (meshAt L k (j - 1)) (f y) (signedPermute π s ν) := by
    intro ν
    have h := apply_sum_single_signedPermute (w := w) hws (meshAt L k (j - 1)) ν
    rw [← hr, offsetPoint_torusProj, hfw, hfw, offsetPoint_torusProj, map_add, h]
    congr 1
    abel
  rw [(hdisp y).1, (hdisp (vertexImage f y)).1, coe_torus_vertexImage hl y]
  calc f '' (offsetPoint (meshAt L k (j - 1)) (y : FourTorus L n) ''
        PeriodicLattice.blockOffsets L 1)
      = (fun ν => offsetPoint (meshAt L k (j - 1)) (f y) (signedPermute π s ν)) ''
          PeriodicLattice.blockOffsets L 1 := by
        rw [image_image]
        exact image_congr fun ν _ => hmove ν
    _ = offsetPoint (meshAt L k (j - 1)) (f y) ''
          (signedPermute π s '' PeriodicLattice.blockOffsets L 1) := by
        rw [image_image]
    _ = _ := by rw [image_signedPermute_blockOffsets]
end TorusBlocks
theorem blockStructure_holds (h₁ : PeriodicLattice.BlockPartition.Properties)
    (h₂ : FullSpace.CubesCorridorsPivotEdgesAndPaths)
    (h₃ : SublatticesSymmetriesScalingsAndProjections.Statement) :
    BlockStructure := by
  intro L k j hL hk hj hjk
  have hL0 : 0 < L := by
    have := hL.2
    omega
  obtain ⟨-, -, -, hisoS, hisoW, -, -⟩ := h₃ L hL0 hL k
  obtain ⟨P, -, -, -⟩ := h₂ L hL k j 1 hk hj hjk le_rfl hj
  have hW := space_blockEqOffsetImage P
  refine ⟨fun n hn => ?_, hW, space_blocksPartitionFiner P,
    fun c μ hc => space_blockTranslateAlongBond hL0 hj P c μ hc,
    space_symmetryMapsBlocks hW hisoW hjk⟩
  have hneg : -(n : ℤ) ≤ PeriodicLattice.levelDepth k j := by
    simp only [PeriodicLattice.levelDepth]
    omega
  obtain ⟨hd, hp, -, -, -⟩ := h₁ L n hL hn (PeriodicLattice.levelDepth k j) 1 0 hneg
  have hT : ∀ y : Vertex L n k j, BlockEqOffsetImage L n k j y :=
    fun y => torus_blockEqOffsetImage hL0 hj y (hd y)
  exact ⟨hT, torus_blocksPartitionFiner hj hp,
    fun c μ hc => torus_blockTranslateAlongBond hL.2 hn hj hjk hT c μ hc,
    torus_symmetryMapsBlocks hT (hisoS n hn) hjk⟩
end YangMills.Construction.Tower.BlockStructureProof
end

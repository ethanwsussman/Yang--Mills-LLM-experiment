import YangMills.Construction.Lattice.CubesOfTwoStandardPartitionsProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.CubeTorusTransfer
import YangMills.Construction.DirichletOperator.MapsOfACubeOfTheFirstKind
import YangMills.Construction.DirichletOperator.PositionOfTheCubesByKind
import YangMills.Construction.DirichletOperator.PositionOfTheThickenedSetsOfACube
import YangMills.Construction.DirichletOperator.SeparationReadOnTheDistances
import YangMills.Construction.DirichletOperator.SitesAndCubesOfACubeOfTheFirstKind
import YangMills.Construction.RegionSequence.AverageWeights
import YangMills.Construction.RegionSequence.BlockAverageAdjoint
import YangMills.Construction.RegionSequence.ShellDecomposition
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes.CubeTorusAveraging
open YangMills.Construction.PartitionCubes.CubeTorus
section Lengths
variable {S : ℝ}
theorem exists_lift_abs_eq_norm (p : PeriodicTorus 4 S) :
    ∃ v : Fin 4 → ℝ, torusProj 4 S v = p ∧ ∀ μ, |v μ| = ‖p μ‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.exists_torusProj_eq_abs_eq_norm <;> assumption
theorem supNorm_eq_norm (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by
  have hbdd : BddBelow {r | ∃ v : Fin 4 → ℝ, torusProj 4 S v = p ∧ r = ‖v‖} :=
    ⟨0, by rintro _ ⟨v, -, rfl⟩; exact norm_nonneg v⟩
  obtain ⟨b, hb, hb'⟩ := exists_lift_abs_eq_norm p
  apply le_antisymm
  · refine (csInf_le hbdd ⟨b, hb, rfl⟩).trans ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg p)).2 fun μ => ?_
    rw [Real.norm_eq_abs, hb']
    exact norm_le_pi_norm p μ
  · refine le_csInf ⟨_, b, hb, rfl⟩ ?_
    rintro _ ⟨v, rfl, rfl⟩
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun μ => ?_
    exact (TorusMetric.addCircle_norm_coe_le_abs (v μ)).trans (norm_le_pi_norm v μ)
theorem norm_torusProj_le (w : Fin 4 → ℝ) : ‖torusProj 4 S w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun μ => ?_
  exact (TorusMetric.addCircle_norm_coe_le_abs (w μ)).trans (norm_le_pi_norm w μ)
theorem exists_lift_norm_eq_norm (p : PeriodicTorus 4 S) :
    ∃ v : Fin 4 → ℝ, torusProj 4 S v = p ∧ ‖v‖ = ‖p‖ := by
  obtain ⟨v, hv, hv'⟩ := exists_lift_abs_eq_norm p
  refine ⟨v, hv, le_antisymm ?_ (hv ▸ norm_torusProj_le v)⟩
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg p)).2 fun μ => ?_
  rw [Real.norm_eq_abs, hv']
  exact norm_le_pi_norm p μ
theorem torusProj_add (v w : Fin 4 → ℝ) :
    torusProj 4 S (v + w) = torusProj 4 S v + torusProj 4 S w := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
theorem norm_piSingle {a : ℝ} (ha : 0 ≤ a) (ν : Fin 4) : ‖(Pi.single ν a : Fin 4 → ℝ)‖ = a := by
  rw [Pi.norm_single, Real.norm_of_nonneg ha]
theorem norm_sub_le_sub_add_sub (a b c : PeriodicTorus 4 S) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  have h := norm_add_le (a - b) (b - c)
  rwa [sub_add_sub_cancel] at h
theorem torusProj_single_natMul (μ : Fin 4) (a : ℝ) (i : ℕ) :
    torusProj 4 S (Pi.single μ ((i : ℝ) * a)) = i • torusProj 4 S (Pi.single μ a) := by
  induction i with
  | zero => funext ν; simp [torusProj, Pi.single_apply]
  | succ i ih =>
    have e : (Pi.single μ (((i + 1 : ℕ) : ℝ) * a) : Fin 4 → ℝ) =
        Pi.single μ ((i : ℝ) * a) + Pi.single μ a := by
      rw [← Pi.single_add]
      congr 1
      push_cast
      ring
    rw [e, torusProj_add, ih, succ_nsmul]
end Lengths
theorem finsum_mem_eq_zero_of_forall_mem {α : Type*} {s : Set α} {g : α → ℝ}
    (h : ∀ a ∈ s, g a = 0) : ∑ᶠ a ∈ s, g a = 0 := by
  rw [finsum_mem_congr rfl h]
  simp
theorem finsum_eq_finsum_mem_of_support_subset {α : Type*} {F : α → ℝ} {D : Set α}
    (h : Function.support F ⊆ D) : ∑ᶠ a, F a = ∑ᶠ a ∈ D, F a := by
  rw [← finsum_mem_univ]
  refine finsum_mem_inter_support_eq F univ D ?_
  ext a
  simp only [mem_inter_iff, mem_univ, true_and]
  exact ⟨fun ha => ⟨h ha, ha⟩, fun ha => ha.2⟩
theorem finsum_mem_fibre_indicator {α β : Type*} {e : α → β} {X T : Set α} (hXT : X ⊆ T)
    {φ : α → ℝ} (h₀ : ∀ a, a ∉ X → φ a = 0) (h₁ : ∀ a ∈ X, φ a = 1) (hinj : InjOn e X)
    (f : α → ℝ) {a : α} (ha : a ∈ X) :
    ∑ᶠ a' ∈ {a' | a' ∈ T ∧ e a' = e a}, φ a' * f a' = f a := by
  have h : {a' | a' ∈ T ∧ e a' = e a} ∩ Function.support (fun a' => φ a' * f a') =
      {a} ∩ Function.support (fun a' => φ a' * f a') := by
    ext a'
    simp only [mem_inter_iff, mem_setOf_eq, mem_singleton_iff, Function.mem_support]
    constructor
    · rintro ⟨⟨-, h₂⟩, h₃⟩
      have hX : a' ∈ X := by
        by_contra hn
        exact h₃ (by rw [h₀ a' hn, zero_mul])
      exact ⟨hinj hX ha h₂, h₃⟩
    · rintro ⟨rfl, h₃⟩
      exact ⟨⟨hXT ha, rfl⟩, h₃⟩
  refine (finsum_mem_inter_support_eq _ _ _ h).trans ?_
  rw [finsum_mem_singleton, h₁ a ha, one_mul]
theorem sum_range_eq_add_succ_of_vanish (F : ℕ → ℝ) {n N : ℕ} (hn : n < N)
    (h₀ : ∀ j < N, j ≠ n → j ≠ n + 1 → F j = 0) (h₁ : N ≤ n + 1 → F (n + 1) = 0) :
    ∑ j ∈ Finset.range N, F j = F n + F (n + 1) := by
  by_cases hN : n + 1 < N
  · have hs : ({n, n + 1} : Finset ℕ) ⊆ Finset.range N := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> simpa
    rw [← Finset.sum_subset hs, Finset.sum_pair (by omega)]
    intro j hj hj'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj'
    exact h₀ j (Finset.mem_range.1 hj) hj'.1 hj'.2
  · have hs : ({n} : Finset ℕ) ⊆ Finset.range N := by
      intro j hj
      simp only [Finset.mem_singleton] at hj
      subst hj
      simpa
    rw [← Finset.sum_subset hs, Finset.sum_singleton, h₁ (by omega), add_zero]
    intro j hj hj'
    simp only [Finset.mem_singleton] at hj'
    exact h₀ j (Finset.mem_range.1 hj) hj' (by have := Finset.mem_range.1 hj; omega)
theorem scale_pos (𝒯 : NestedRegions) (n : ℕ) : 0 < 𝒯.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem scale_mono (𝒯 : NestedRegions) {j n : ℕ} (h : j ≤ n) :
    𝒯.scale j ≤ 𝒯.scale n := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.scale_mono <;> assumption
theorem scale_zero (𝒯 : NestedRegions) : 𝒯.scale 0 = 𝒯.ξ := by
  simp [𝒯.scale_eq_pow_mul]
theorem mem_fineBlock_iff {𝒯 : NestedRegions} {j : ℕ} {y : 𝒯.Point} {x : 𝒯.FineSite} :
    x ∈ 𝒯.fineBlock j y ↔ ‖(x : 𝒯.Point) - y‖ ≤ 𝒯.scale j / 2 := by
  change supNorm ((x : 𝒯.Point) - y) ≤ _ ↔ _
  rw [supNorm_eq_norm]
theorem norm_sub_le_of_mem_cellOf {𝒯 : NestedRegions} {y p q : 𝒯.Point} (hp : p ∈ 𝒯.cellOf y)
    (hq : q ∈ 𝒯.cellOf y) : ‖p - q‖ ≤ 𝒯.scale (𝒯.level y) := by
  have hp' : supNorm (p - y) ≤ 𝒯.scale (𝒯.level y) / 2 := hp
  have hq' : supNorm (q - y) ≤ 𝒯.scale (𝒯.level y) / 2 := hq
  rw [supNorm_eq_norm] at hp' hq'
  have := norm_sub_le_sub_add_sub p y q
  rw [norm_sub_rev y q] at this
  linarith
theorem centreOfSite_spec {𝒯 : NestedRegions} (HC : ShellCells 𝒯)
    (x : 𝒯.FineSite) (hx : (x : 𝒯.Point) ∈ 𝒯.Ω 0) :
    𝒯.centreOfSite x ∈ 𝒯.allCentres ∧ (x : 𝒯.Point) ∈ 𝒯.cellOf (𝒯.centreOfSite x) ∧
      ∀ y ∈ 𝒯.allCentres, (x : 𝒯.Point) ∈ 𝒯.cellOf y → y = 𝒯.centreOfSite x := by
  obtain ⟨y, hy, hi, hu⟩ := HC.fineSite_mem_unique x hx
  have hex : ∃ y, y ∈ 𝒯.allCentres ∧ (x : 𝒯.Point) ∈ 𝒯.cellOf y := ⟨y, hy, interior_subset hi⟩
  have h : 𝒯.centreOfSite x ∈ 𝒯.allCentres ∧ (x : 𝒯.Point) ∈ 𝒯.cellOf (𝒯.centreOfSite x) :=
    Classical.epsilon_spec hex
  exact ⟨h.1, h.2, fun y' hy' hx' => (hu y' hy' hx').trans (hu _ h.1 h.2).symm⟩
theorem exists_ne_zero_of_blockAvg_ne {𝒯 : NestedRegions} {g : 𝒯.FineSite → ℝ}
    {y : 𝒯.allCentres} (h : blockAvg g y ≠ 0) : ∃ x ∈ 𝒯.fineBlock (𝒯.level y) y, g x ≠ 0 := by
  by_contra hn
  have hn : ∀ x ∈ 𝒯.fineBlock (𝒯.level y) y, g x = 0 :=
    fun x hx => by_contra fun h' => hn ⟨x, hx, h'⟩
  apply h
  have hz : ∑ᶠ x ∈ 𝒯.fineBlock (𝒯.level y) y, g x = 0 := finsum_mem_eq_zero_of_forall_mem hn
  simp only [blockAvg, hz, mul_zero]
def TouchesBlocks (𝒯 : NestedRegions) (j : ℕ) (c : 𝒯.BondAt j) (X : Set 𝒯.Point) : Prop :=
  ∃ x : 𝒯.FineSite, (x ∈ 𝒯.fineBlock j (c.source : 𝒯.Point) ∨
    x ∈ 𝒯.fineBlock j (c.target : 𝒯.Point)) ∧ (x : 𝒯.Point) ∈ X
theorem bondAvg_eq_zero_of_not_touches {𝒯 : NestedRegions}
    (AV : ∀ (n : ℕ) (c : 𝒯.BondAt n) (A : 𝒯.FineBond → ℝ),
      bondAvg n A c = ∑ᶠ b, avgWeight n c b * A b)
    (W : AvgWeightProps 𝒯) {j : ℕ} {c : 𝒯.BondAt j}
    (hc : c ∈ 𝒯.coarseBonds j) {A : 𝒯.FineBond → ℝ} {X : Set 𝒯.Point}
    (hA : ∀ b, A b ≠ 0 → (b.source : 𝒯.Point) ∈ X) (hn : ¬TouchesBlocks 𝒯 j c X) :
    bondAvg j A c = 0 := by
  rw [AV]
  refine finsum_eq_zero_of_forall_eq_zero fun b => ?_
  by_contra hne
  have hw : avgWeight j c b ≠ 0 := left_ne_zero_of_mul hne
  have ha : A b ≠ 0 := right_ne_zero_of_mul hne
  obtain ⟨-, hb⟩ := W.avgWeight_support j c hc b hw
  exact hn ⟨b.source, hb, hA b ha⟩
variable {𝒮 : NestedRegions} {M : ℕ}
theorem norm_target_sub_source_le {S σ : ℝ} (hσ : 0 ≤ σ) (c : LatticeBond 4 S σ) :
    ‖(c.target : PeriodicTorus 4 S) - (c.source : PeriodicTorus 4 S)‖ ≤ σ := by
  have e : (c.target : PeriodicTorus 4 S) - (c.source : PeriodicTorus 4 S) =
      torusProj 4 S (Pi.single c.dir σ) := by
    change ((c.source : PeriodicTorus 4 S) + torusProj 4 S (Pi.single c.dir σ)) -
      (c.source : PeriodicTorus 4 S) = _
    abel
  rw [e]
  exact (norm_torusProj_le _).trans_eq (norm_piSingle hσ _)
theorem exists_centred_rep {S : ℝ} (hS : 0 < S) (θ : AddCircle S) :
    ∃ v : ℝ, v ∈ Ico (-(S / 2)) (S / 2) ∧ (v : AddCircle S) = θ := by
  have : Fact (0 < S) := ⟨hS⟩
  have hθ : θ ∈ ((↑) : ℝ → AddCircle S) '' Ico (-(S / 2)) (-(S / 2) + S) := by
    rw [AddCircle.coe_image_Ico_eq]
    trivial
  obtain ⟨v, hv, rfl⟩ := hθ
  exact ⟨v, ⟨hv.1, by linarith [hv.2]⟩, rfl⟩
theorem torusProj_liftedCentre (Q : LevelCube 𝒮 M) : torusProj 4 𝒮.side Q.liftedCentre = Q.centre := by
  funext μ
  exact (Classical.epsilon_spec (exists_centred_rep 𝒮.side_pos (Q.centre μ))).2
theorem exists_lift_near_centre (Q : LevelCube 𝒮 M) {x : 𝒮.Point} {r : ℝ}
    (h : ‖x - Q.centre‖ < r) :
    ∃ p : Fin 4 → ℝ, torusProj 4 𝒮.side p = x ∧ ∀ μ, |p μ - Q.liftedCentre μ| < r := by
  obtain ⟨v, hv, hv'⟩ := exists_lift_abs_eq_norm (x - Q.centre)
  refine ⟨Q.liftedCentre + v, ?_, fun μ => ?_⟩
  · rw [torusProj_add, hv, torusProj_liftedCentre]
    abel
  · have e : (Q.liftedCentre + v) μ - Q.liftedCentre μ = v μ := by simp
    rw [e, hv']
    exact lt_of_le_of_lt (norm_le_pi_norm _ μ) h
theorem mem_strictPts_of_norm_lt {Q : LevelCube 𝒮 M} {x : 𝒮.Point}
    (h : ‖x - Q.centre‖ < cubeSide 𝒮 M Q.level) : x ∈ Q.strictPts := by
  change supNorm (x - Q.centre) < _
  rwa [supNorm_eq_norm]
def liftedBox (Q : LevelCube 𝒮 M) : Set (Fin 4 → ℝ) :=
  {p | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level}
structure Setup (Q : LevelCube 𝒮 M) : Prop where
  L_eq : Q.system.setting.L = 𝒮.L
  ξ_eq : Q.system.setting.ξ = 𝒮.ξ
  s_eq : Q.system.setting.s = Q.level + 1
  mem_bonds : ∀ b : Q.system.setting.FineBond, b ∈ Q.system.setting.bonds
  Ω_eq_univ : ∀ j ≤ Q.level, Q.system.setting.Ω j = univ
  proj_mem_strictPts : ∀ p ∈ liftedBox Q, torusProj 4 𝒮.side p ∈ Q.strictPts
  embed_injOn : InjOn Q.system.embed Q.strictPts
  embed_mapsTo : MapsTo Q.system.embed Q.strictPts
    ((fun p : Fin 4 → ℝ => (torusProj 4 Q.system.setting.side p : Q.system.setting.Point)) ''
      liftedBox Q)
  embed_add : ∀ p v : Fin 4 → ℝ, p ∈ liftedBox Q → p + v ∈ liftedBox Q →
    Q.system.embed (torusProj 4 𝒮.side p + torusProj 4 𝒮.side v) =
      Q.system.embed (torusProj 4 𝒮.side p) + torusProj 4 Q.system.setting.side v
  embed_lattice_eq : Q.system.embed '' ((spacingLattice 4 𝒮.side (𝒮.scale 0) : Set 𝒮.Point) ∩
      Q.strictPts) =
    (spacingLattice 4 Q.system.setting.side (𝒮.scale 0) : Set Q.system.setting.Point) ∩
      (fun p : Fin 4 → ℝ => (torusProj 4 Q.system.setting.side p : Q.system.setting.Point)) ''
        liftedBox Q
  norm_sub_centre_lt : ∀ x ∈ Q.thicken (5 / 6), ‖x - Q.centre‖ < 5 / 6 * cubeSide 𝒮 M Q.level
  scale_succ_le : 366 * 𝒮.scale (Q.level + 1) ≤ mollifyRadius 𝒮 M Q.level
  mollifyRadius_le : mollifyRadius 𝒮 M Q.level ≤ cubeSide 𝒮 M Q.level / 78
  exists_near_supp : ∀ ς : ℝ, 0 ≤ ς → ∀ x ∈ Q.thicken ς,
    ∃ y ∈ Q.supp, supNorm (x - y) ≤ ς * mollifyRadius 𝒮 M Q.level
  mem_Ω_zero : ∀ (y : 𝒮.FineSite) (x : 𝒮.Point), x ∈ Q.thicken (5 / 6) →
    ‖x - (y : 𝒮.Point)‖ ≤ 𝒮.ξ → (y : 𝒮.Point) ∈ 𝒮.Ω 0
  level_le : Q.level ≤ 𝒮.s
  cell_level : ∀ y ∈ 𝒮.allCentres, (𝒮.cellOf y ∩ Q.thicken (5 / 6)).Nonempty →
    y ∈ 𝒮.centresAt Q.level ∨ y ∈ 𝒮.centresAt (Q.level + 1)
  cell_subset : ∀ y ∈ 𝒮.allCentres, (𝒮.cellOf y ∩ Q.thicken (5 / 6)).Nonempty →
    𝒮.cellOf y ⊆ Q.strictPts
  cell_forward : ∀ y ∈ 𝒮.allCentres, (𝒮.cellOf y ∩ Q.thicken (5 / 6)).Nonempty →
    ∃ y' ∈ Q.system.setting.allCentres,
      (Q.system.setting.cellOf y' ∩ Q.system.embed '' Q.thicken (5 / 6)).Nonempty ∧
        Q.system.embed '' 𝒮.cellOf y = Q.system.setting.cellOf y' ∧
        Q.system.setting.level y' = 𝒮.level y
  cell_backward : ∀ y' ∈ Q.system.setting.allCentres,
    (Q.system.setting.cellOf y' ∩ Q.system.embed '' Q.thicken (5 / 6)).Nonempty →
    ∃ y ∈ 𝒮.allCentres, (𝒮.cellOf y ∩ Q.thicken (5 / 6)).Nonempty ∧
      Q.system.embed '' 𝒮.cellOf y = Q.system.setting.cellOf y' ∧
      Q.system.setting.level y' = 𝒮.level y
  bond_level : ∀ (j : ℕ) (c : 𝒮.BondAt j), c ∈ 𝒮.coarseBonds j →
    TouchesBlocks 𝒮 j c (Q.thicken (2 / 3)) → j = Q.level ∨ j = Q.level + 1
  bond_forward : ∀ (j : ℕ) (c : 𝒮.BondAt j), c ∈ 𝒮.coarseBonds j →
    TouchesBlocks 𝒮 j c (Q.thicken (2 / 3)) →
    ∃ c' ∈ Q.system.setting.coarseBonds j,
      TouchesBlocks Q.system.setting j c' (Q.system.embed '' Q.thicken (2 / 3)) ∧
        (c'.source : Q.system.setting.Point) = Q.system.embed (c.source : 𝒮.Point) ∧
        c'.dir = c.dir
  bond_backward : ∀ j : ℕ, j = Q.level ∨ j = Q.level + 1 → ∀ c' ∈ Q.system.setting.coarseBonds j,
    TouchesBlocks Q.system.setting j c' (Q.system.embed '' Q.thicken (2 / 3)) →
    ∃ c ∈ 𝒮.coarseBonds j, TouchesBlocks 𝒮 j c (Q.thicken (2 / 3)) ∧
      (c'.source : Q.system.setting.Point) = Q.system.embed (c.source : 𝒮.Point) ∧
      c'.dir = c.dir
variable {Q : LevelCube 𝒮 M}
theorem scale_local (H : Setup Q) (j : ℕ) :
    Q.system.setting.scale j = 𝒮.scale j := by
  rw [NestedRegions.scale_eq_pow_mul, NestedRegions.scale_eq_pow_mul, H.L_eq, H.ξ_eq]
theorem twelve_scale_succ_le (H : Setup Q) :
    12 * 𝒮.scale (Q.level + 1) ≤ 1 / 6 * cubeSide 𝒮 M Q.level := by
  have h₁ := H.scale_succ_le
  have h₂ := H.mollifyRadius_le
  have h₃ := scale_pos 𝒮 (Q.level + 1)
  linarith
theorem mem_strictPts_of_mem_thicken (H : Setup Q) {x : 𝒮.Point} (hx : x ∈ Q.thicken (5 / 6)) :
    x ∈ Q.strictPts := by
  have h₁ := H.norm_sub_centre_lt x hx
  have h₂ := twelve_scale_succ_le H
  have h₃ := scale_pos 𝒮 (Q.level + 1)
  exact mem_strictPts_of_norm_lt (by linarith)
theorem embed_translate (H : Setup Q) {x : 𝒮.Point} {w : Fin 4 → ℝ}
    (h : ‖x - Q.centre‖ + ‖w‖ < cubeSide 𝒮 M Q.level) :
    x ∈ Q.strictPts ∧ x + torusProj 4 𝒮.side w ∈ Q.strictPts ∧
      Q.system.embed (x + torusProj 4 𝒮.side w) =
        Q.system.embed x + torusProj 4 Q.system.setting.side w := by
  obtain ⟨p, rfl, hp⟩ := exists_lift_near_centre Q
    (show ‖x - Q.centre‖ < cubeSide 𝒮 M Q.level - ‖w‖ by linarith)
  have hw : 0 ≤ ‖w‖ := norm_nonneg w
  have hp₁ : p ∈ liftedBox Q := fun μ => by linarith [hp μ]
  have hp₂ : p + w ∈ liftedBox Q := fun μ => by
    have e : (p + w) μ - Q.liftedCentre μ = (p μ - Q.liftedCentre μ) + w μ := by
      simp only [Pi.add_apply]
      ring
    have h₁ : |w μ| ≤ ‖w‖ := by simpa using norm_le_pi_norm w μ
    rw [e]
    exact lt_of_le_of_lt (abs_add_le _ _) (by linarith [hp μ])
  refine ⟨H.proj_mem_strictPts p hp₁, ?_, H.embed_add p w hp₁ hp₂⟩
  rw [← torusProj_add]
  exact H.proj_mem_strictPts _ hp₂
theorem embed_mem_lattice (H : Setup Q) {x : 𝒮.Point} (hx : x ∈ spacingLattice 4 𝒮.side 𝒮.ξ)
    (hi : x ∈ Q.strictPts) :
    Q.system.embed x ∈ spacingLattice 4 Q.system.setting.side Q.system.setting.ξ := by
  have h2 : Q.system.embed x ∈ Q.system.embed ''
      ((spacingLattice 4 𝒮.side (𝒮.scale 0) : Set 𝒮.Point) ∩ Q.strictPts) :=
    ⟨x, ⟨by rwa [scale_zero], hi⟩, rfl⟩
  rw [H.embed_lattice_eq] at h2
  have h3 := h2.1
  rwa [scale_zero, ← H.ξ_eq] at h3
theorem mem_lattice_of_embed (H : Setup Q) {x : 𝒮.Point} (hx : x ∈ Q.strictPts)
    (y : Q.system.setting.FineSite) (hy : Q.system.embed x = y) :
    x ∈ spacingLattice 4 𝒮.side 𝒮.ξ := by
  have h : (y : Q.system.setting.Point) ∈ Q.system.embed ''
      ((spacingLattice 4 𝒮.side (𝒮.scale 0) : Set 𝒮.Point) ∩ Q.strictPts) := by
    rw [H.embed_lattice_eq]
    refine ⟨?_, hy ▸ H.embed_mapsTo hx⟩
    rw [scale_zero, ← H.ξ_eq]
    exact y.2
  obtain ⟨u, ⟨hu, hu'⟩, hue⟩ := h
  have e : u = x := H.embed_injOn hu' hx (hue.trans hy.symm)
  rw [scale_zero] at hu
  exact e ▸ hu
theorem coe_mapSite (H : Setup Q) (x : 𝒮.FineSite) (hx : (x : 𝒮.Point) ∈ Q.strictPts) :
    ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) =
      Q.system.embed x :=
  Classical.epsilon_spec
    (p := fun y : Q.system.setting.FineSite => (y : Q.system.setting.Point) = Q.system.embed x)
    ⟨⟨_, embed_mem_lattice H x.2 hx⟩, rfl⟩
theorem mapSite_injective_on (H : Setup Q) {x x' : 𝒮.FineSite} (hx : (x : 𝒮.Point) ∈ Q.strictPts)
    (hx' : (x' : 𝒮.Point) ∈ Q.strictPts) (h : Q.system.mapSite x = Q.system.mapSite x') :
    x = x' := by
  apply Subtype.ext
  apply H.embed_injOn hx hx'
  rw [← coe_mapSite H x hx, ← coe_mapSite H x' hx', h]
theorem mapBond_injective_on (H : Setup Q) {b b' : 𝒮.FineBond}
    (hb : (b.source : 𝒮.Point) ∈ Q.strictPts) (hb' : (b'.source : 𝒮.Point) ∈ Q.strictPts)
    (h : Q.system.mapBond b = Q.system.mapBond b') : b = b' := by
  have h₁ : Q.system.mapSite b.source = Q.system.mapSite b'.source := congrArg LatticeBond.source h
  have h₂ : (Q.system.mapBond b).dir = (Q.system.mapBond b').dir :=
    congrArg LatticeBond.dir h
  change b.dir = b'.dir at h₂
  have h₃ := mapSite_injective_on H hb hb' h₁
  cases b
  cases b'
  simp_all
theorem mapSite_bijOn (H : Setup Q) {C : Set 𝒮.Point} (hC : C ⊆ Q.strictPts)
    {C' : Set Q.system.setting.Point} (hC' : Q.system.embed '' C = C') :
    BijOn Q.system.mapSite {x : 𝒮.FineSite | (x : 𝒮.Point) ∈ C}
      {x' : Q.system.setting.FineSite | (x' : Q.system.setting.Point) ∈ C'} := by
  refine ⟨fun x hx => ?_, fun x hx x' hx' h => mapSite_injective_on H (hC hx) (hC hx') h,
    fun x' hx' => ?_⟩
  · change ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) ∈ C'
    rw [coe_mapSite H x (hC hx), ← hC']
    exact ⟨x, hx, rfl⟩
  · have hx'' : (x' : Q.system.setting.Point) ∈ Q.system.embed '' C := by
      rw [hC']
      exact hx'
    obtain ⟨p, hp, hpe⟩ := hx''
    have hs := mem_lattice_of_embed H (hC hp) x' hpe
    exact ⟨⟨p, hs⟩, hp, Subtype.ext ((coe_mapSite H ⟨p, hs⟩ (hC hp)).trans hpe)⟩
theorem cubeAt_image (H : Setup Q) {p : 𝒮.Point} {σ : ℝ}
    (hp : ‖p - Q.centre‖ + σ / 2 < cubeSide 𝒮 M Q.level) :
    cubeAt p σ ⊆ Q.strictPts ∧ Q.system.embed '' cubeAt p σ =
      cubeAt (Q.system.embed p) σ := by
  have key : ∀ q ∈ cubeAt p σ, q ∈ Q.strictPts ∧
      ‖Q.system.embed q - Q.system.embed p‖ ≤ σ / 2 := by
    intro q hq
    have hq' : supNorm (q - p) ≤ σ / 2 := hq
    rw [supNorm_eq_norm] at hq'
    obtain ⟨u, hu, hu'⟩ := exists_lift_norm_eq_norm (q - p)
    obtain ⟨-, h₂, h₃⟩ := embed_translate H (x := p) (w := u) (by rw [hu']; linarith)
    have e : p + torusProj 4 𝒮.side u = q := by
      rw [hu]
      abel
    rw [e] at h₂ h₃
    refine ⟨h₂, ?_⟩
    rw [h₃, add_sub_cancel_left]
    exact (norm_torusProj_le u).trans (hu' ▸ hq')
  refine ⟨fun q hq => (key q hq).1, subset_antisymm ?_ ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    change supNorm _ ≤ _
    rw [supNorm_eq_norm]
    exact (key q hq).2
  · intro y hy
    have hy' : supNorm (y - Q.system.embed p) ≤ σ / 2 := hy
    rw [supNorm_eq_norm] at hy'
    obtain ⟨u, hu, hu'⟩ := exists_lift_norm_eq_norm (y - Q.system.embed p)
    obtain ⟨-, -, h₃⟩ := embed_translate H (x := p) (w := u) (by rw [hu']; linarith)
    refine ⟨p + torusProj 4 𝒮.side u, ?_, ?_⟩
    · change supNorm _ ≤ _
      rw [supNorm_eq_norm, add_sub_cancel_left]
      exact (norm_torusProj_le u).trans (hu' ▸ hy')
    · rw [h₃, hu]
      abel
theorem fineBlock_bijOn (H : Setup Q) {p : 𝒮.Point} {j : ℕ}
    (hp : ‖p - Q.centre‖ + 𝒮.scale j / 2 < cubeSide 𝒮 M Q.level) :
    BijOn Q.system.mapSite (𝒮.fineBlock j p) (Q.system.setting.fineBlock j (Q.system.embed p)) := by
  have h := cubeAt_image H hp
  have h' := mapSite_bijOn H h.1 h.2
  have e : Q.system.setting.fineBlock j (Q.system.embed p) =
      {x' : Q.system.setting.FineSite | (x' : Q.system.setting.Point) ∈
        cubeAt (Q.system.embed p) (𝒮.scale j)} := by
    rw [← scale_local H j]
    rfl
  rw [e]
  exact h'
theorem mem_thicken_of_near (H : Setup Q) {x p : 𝒮.Point} (hx : x ∈ Q.thicken (2 / 3))
    (hp : ‖p - x‖ ≤ 2 * 𝒮.scale (Q.level + 1)) : p ∈ Q.thicken (5 / 6) := by
  obtain ⟨y, hy, hxy⟩ := H.exists_near_supp (2 / 3) (by norm_num) x hx
  rw [supNorm_eq_norm] at hxy
  have h₁ := norm_sub_le_sub_add_sub p x y
  have h₂ := H.scale_succ_le
  have h₃ := scale_pos 𝒮 (Q.level + 1)
  have h₄ : ‖p - y‖ ≤ 5 / 6 * mollifyRadius 𝒮 M Q.level := by linarith
  change supSetDist {p} Q.supp ≤ _
  refine iInf₂_le_of_le p (mem_singleton p) (iInf₂_le_of_le y hy ?_)
  rw [supNorm_eq_norm]
  exact ENNReal.ofReal_le_ofReal h₄
theorem thicken_mono_two_thirds (H : Setup Q) {x : 𝒮.Point} (hx : x ∈ Q.thicken (2 / 3)) :
    x ∈ Q.thicken (5 / 6) :=
  mem_thicken_of_near H hx (by
    rw [sub_self, norm_zero]
    have := scale_pos 𝒮 (Q.level + 1)
    linarith)
theorem anchor_eq_source (H : Setup Q) {b : 𝒮.FineBond}
    (hb : (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6)) : 𝒮.anchor b = b.source := by
  have h₁ : (b.source : 𝒮.Point) ∈ 𝒮.Ω 0 :=
    H.mem_Ω_zero b.source _ hb (by rw [sub_self, norm_zero]; exact 𝒮.ξ_pos.le)
  have h₂ : ¬((b.source : 𝒮.Point) ∉ 𝒮.Ω 0 ∧ (b.target : 𝒮.Point) ∈ 𝒮.Ω 0) :=
    fun hh => hh.1 h₁
  simp only [anchor, if_neg h₂]
theorem anchor_eq_source_of_anchor (H : Setup Q) {b : 𝒮.FineBond}
    (hb : (𝒮.anchor b : 𝒮.Point) ∈ Q.thicken (5 / 6)) : 𝒮.anchor b = b.source := by
  by_cases h : (b.source : 𝒮.Point) ∉ 𝒮.Ω 0 ∧ (b.target : 𝒮.Point) ∈ 𝒮.Ω 0
  · have e : 𝒮.anchor b = b.target := by simp only [anchor, if_pos h]
    rw [e] at hb
    exact absurd (H.mem_Ω_zero b.source _ hb (norm_target_sub_source_le 𝒮.ξ_pos.le b)) h.1
  · simp only [anchor, if_neg h]
theorem anchor_local (H : Setup Q) (b : Q.system.setting.FineBond) :
    Q.system.setting.anchor b = b.source := by
  have h : ¬((b.source : Q.system.setting.Point) ∉ Q.system.setting.Ω 0 ∧
      (b.target : Q.system.setting.Point) ∈ Q.system.setting.Ω 0) := fun hh =>
    hh.1 (by rw [H.Ω_eq_univ 0 (Nat.zero_le _)]; trivial)
  simp only [anchor, if_neg h]
theorem indicator_one_ne_zero {α : Type*} {X : Set α} {a : α} (ha : a ∈ X) :
    indicator X (1 : α → ℝ) a ≠ 0 := by
  rw [indicator_of_mem ha]
  exact one_ne_zero
theorem restrictSites_mapSite (H : Setup Q) (f : 𝒮.FineSite → ℝ) {x : 𝒮.FineSite}
    (hx : (x : 𝒮.Point) ∈ Q.thicken (5 / 6)) : restrictSites Q f (Q.system.mapSite x) = f x :=
  finsum_mem_fibre_indicator (e := Q.system.mapSite)
    (X := {x' : 𝒮.FineSite | (x' : 𝒮.Point) ∈ Q.thicken (5 / 6)})
    (T := {x' : 𝒮.FineSite | (x' : 𝒮.Point) ∈
      tsupport (indicator (Q.thicken (5 / 6)) (1 : 𝒮.Point → ℝ))})
    (φ := fun x' : 𝒮.FineSite => indicator (Q.thicken (5 / 6)) (1 : 𝒮.Point → ℝ) (x' : 𝒮.Point))
    (fun _ h => subset_tsupport _ (indicator_one_ne_zero h))
    (fun _ h => indicator_of_notMem (show _ ∉ Q.thicken (5 / 6) from h) _)
    (fun _ h => by simp only [indicator_of_mem (show _ ∈ Q.thicken (5 / 6) from h), Pi.one_apply])
    (fun _ h _ h' e => mapSite_injective_on H (mem_strictPts_of_mem_thicken H h)
      (mem_strictPts_of_mem_thicken H h') e) f hx
theorem restrictSites_eq_zero (f : 𝒮.FineSite → ℝ) {y : Q.system.setting.FineSite}
    (h : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ Q.thicken (5 / 6) → Q.system.mapSite x ≠ y) :
    restrictSites Q f y = 0 := by
  refine finsum_mem_eq_zero_of_forall_mem fun x hx => ?_
  have hn : (x : 𝒮.Point) ∉ Q.thicken (5 / 6) := fun hm => h x hm hx.2
  rw [indicator_of_notMem hn, zero_mul]
theorem restrictBonds_mapBond (H : Setup Q) (A : 𝒮.FineBond → ℝ) {b : 𝒮.FineBond}
    (hb : (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6)) :
    restrictBonds Q A (Q.system.mapBond b) = A b :=
  finsum_mem_fibre_indicator (e := Q.system.mapBond)
    (X := {b' : 𝒮.FineBond | (b'.source : 𝒮.Point) ∈ Q.thicken (5 / 6)})
    (T := {b' : 𝒮.FineBond | (b'.source : 𝒮.Point) ∈
      tsupport (indicator (Q.thicken (5 / 6)) (1 : 𝒮.Point → ℝ))})
    (φ := fun b' : 𝒮.FineBond =>
      indicator (Q.thicken (5 / 6)) (1 : 𝒮.Point → ℝ) (b'.source : 𝒮.Point))
    (fun _ h => subset_tsupport _ (indicator_one_ne_zero h))
    (fun _ h => indicator_of_notMem (show _ ∉ Q.thicken (5 / 6) from h) _)
    (fun _ h => by simp only [indicator_of_mem (show _ ∈ Q.thicken (5 / 6) from h), Pi.one_apply])
    (fun _ h _ h' e => mapBond_injective_on H (mem_strictPts_of_mem_thicken H h)
      (mem_strictPts_of_mem_thicken H h') e) A hb
theorem restrictBonds_eq_zero (A : 𝒮.FineBond → ℝ) {c : Q.system.setting.FineBond}
    (h : ∀ b : 𝒮.FineBond, (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6) → Q.system.mapBond b ≠ c) :
    restrictBonds Q A c = 0 := by
  refine finsum_mem_eq_zero_of_forall_mem fun b hb => ?_
  have hn : (b.source : 𝒮.Point) ∉ Q.thicken (5 / 6) := fun hm => h b hm hb.2
  rw [indicator_of_notMem hn, zero_mul]
theorem level_le_succ {y : 𝒮.Point}
    (h : y ∈ 𝒮.centresAt Q.level ∨ y ∈ 𝒮.centresAt (Q.level + 1)) :
    𝒮.level y ≤ Q.level + 1 := by
  rcases h with h | h
  · exact (Nat.sInf_le h).trans (Nat.le_succ _)
  · exact Nat.sInf_le h
theorem scale_le_two_mul {i : ℕ} (hi : i ≤ Q.level + 1) :
    𝒮.scale i ≤ 2 * 𝒮.scale (Q.level + 1) := by
  have h₁ := scale_mono 𝒮 hi
  have h₂ := scale_pos 𝒮 (Q.level + 1)
  linarith
theorem siteFunctionsMatch (H : Setup Q) (C₁ : ShellCells 𝒮)
    (C₂ : ShellCells Q.system.setting)
    (A₁ : BlockAverageAdjointFacts 𝒮)
    (A₂ : BlockAverageAdjointFacts Q.system.setting)
    {f : 𝒮.FineSite → ℝ} (hf : f ∈ 𝒮.siteFns) (hs : VanishesOff (Q.thicken (2 / 3)) f) :
    SiteFunctionsMatch Q (averagingOp f) (averagingOp (restrictSites Q f)) := by
  have hall : ∀ p : Q.system.setting.Point, p ∈ Q.system.setting.Ω 0 := fun p => by
    rw [H.Ω_eq_univ 0 (Nat.zero_le _)]
    trivial
  have hg : restrictSites Q f ∈ Q.system.setting.siteFns := fun x hx => absurd (hall _) hx
  have hsub : ∀ x : 𝒮.FineSite, f x ≠ 0 → (x : 𝒮.Point) ∈ Q.thicken (2 / 3) :=
    fun x hx => by_contra fun hn => hx (hs x hn)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    by_cases hΩ : (x : 𝒮.Point) ∈ 𝒮.Ω 0
    · obtain ⟨hy, hv⟩ := A₁.weighted_apply f hf x hΩ
      change blockAvgAdj (weightMul (blockAvg f)) x = 0
      rw [hv]
      have hz : blockAvg f ⟨𝒮.centreOfSite x, hy⟩ = 0 := by
        by_contra hne
        obtain ⟨x₁, hx₁, hf₁⟩ := exists_ne_zero_of_blockAvg_ne hne
        have h₂ := hsub x₁ hf₁
        have hc₁ : (x₁ : 𝒮.Point) ∈ 𝒮.cellOf (𝒮.centreOfSite x) := hx₁
        have hmeet : (𝒮.cellOf (𝒮.centreOfSite x) ∩ Q.thicken (5 / 6)).Nonempty :=
          ⟨_, hc₁, thicken_mono_two_thirds H h₂⟩
        have hi := level_le_succ (H.cell_level _ hy hmeet)
        have hc := (centreOfSite_spec C₁ x hΩ).2.1
        exact hx (mem_thicken_of_near H h₂
          ((norm_sub_le_of_mem_cellOf hc hc₁).trans (scale_le_two_mul hi)))
      rw [hz, mul_zero]
    · have h : VanishesOff (𝒮.Ω 0) (blockAvgAdj (weightMul (blockAvg f))) :=
        (A₁.blockAvgAdj_apply _).1
      exact h x hΩ
  · intro x' hx'
    have hΩ := hall x'
    obtain ⟨hy', hv⟩ := A₂.weighted_apply _ hg x' hΩ
    change blockAvgAdj (weightMul (blockAvg (restrictSites Q f))) x' = 0
    rw [hv]
    have hz : blockAvg (restrictSites Q f) ⟨Q.system.setting.centreOfSite x', hy'⟩ = 0 := by
      by_contra hne
      obtain ⟨x₁', hx₁', hg₁⟩ := exists_ne_zero_of_blockAvg_ne hne
      have hc₁' : (x₁' : Q.system.setting.Point) ∈
          Q.system.setting.cellOf (Q.system.setting.centreOfSite x') := hx₁'
      have hex : ∃ x₁ : 𝒮.FineSite, (x₁ : 𝒮.Point) ∈ Q.thicken (5 / 6) ∧
          Q.system.mapSite x₁ = x₁' := by
        by_contra hn
        exact hg₁ (restrictSites_eq_zero f fun x₁ h₁ e => hn ⟨x₁, h₁, e⟩)
      obtain ⟨x₁, h₁, rfl⟩ := hex
      rw [restrictSites_mapSite H f h₁] at hg₁
      have h₂ := hsub x₁ hg₁
      have hcoe := coe_mapSite H x₁ (mem_strictPts_of_mem_thicken H h₁)
      have hmeet : (Q.system.setting.cellOf (Q.system.setting.centreOfSite x') ∩
          Q.system.embed '' Q.thicken (5 / 6)).Nonempty := ⟨_, hc₁', ⟨x₁, h₁, hcoe.symm⟩⟩
      obtain ⟨y, hy, hm, him, hidx⟩ := H.cell_backward _ hy' hmeet
      have hin := H.cell_subset y hy hm
      have hc' := (centreOfSite_spec C₂ x' hΩ).2.1
      rw [← him] at hc' hc₁'
      obtain ⟨x₀, hx₀, he₀⟩ := hc'
      obtain ⟨x₂, hx₂, he₂⟩ := hc₁'
      have e₂ : x₂ = x₁ :=
        H.embed_injOn (hin hx₂) (mem_strictPts_of_mem_thicken H h₁) (he₂.trans hcoe)
      rw [e₂] at hx₂
      have hi := level_le_succ (H.cell_level y hy hm)
      exact hx' ⟨x₀, mem_thicken_of_near H h₂
        ((norm_sub_le_of_mem_cellOf hx₀ hx₂).trans (scale_le_two_mul hi)), he₀⟩
    rw [hz, mul_zero]
  · intro x hx
    have hΩ : (x : 𝒮.Point) ∈ 𝒮.Ω 0 :=
      H.mem_Ω_zero x _ hx (by rw [sub_self, norm_zero]; exact 𝒮.ξ_pos.le)
    have hΩ' := hall (Q.system.mapSite x : Q.system.setting.FineSite)
    obtain ⟨hy, hv⟩ := A₁.weighted_apply f hf x hΩ
    obtain ⟨hy', hv'⟩ := A₂.weighted_apply _ hg (Q.system.mapSite x) hΩ'
    change blockAvgAdj (weightMul (blockAvg f)) x =
      blockAvgAdj (weightMul (blockAvg (restrictSites Q f))) (Q.system.mapSite x)
    rw [hv, hv']
    have hcx := (centreOfSite_spec C₁ x hΩ).2.1
    have hmeet : (𝒮.cellOf (𝒮.centreOfSite x) ∩ Q.thicken (5 / 6)).Nonempty := ⟨_, hcx, hx⟩
    obtain ⟨y', hy₁, -, him, hidx⟩ := H.cell_forward _ hy hmeet
    have hin := H.cell_subset _ hy hmeet
    have hxi := mem_strictPts_of_mem_thicken H hx
    have hcx' : ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) ∈
        Q.system.setting.cellOf y' := by
      rw [coe_mapSite H x hxi, ← him]
      exact ⟨x, hcx, rfl⟩
    have hyy : y' = Q.system.setting.centreOfSite (Q.system.mapSite x) :=
      (centreOfSite_spec C₂ _ hΩ').2.2 y' hy₁ hcx'
    rw [hyy] at him hidx
    have hb := mapSite_bijOn H hin him
    have hsum : ∑ᶠ z ∈ 𝒮.fineBlock (𝒮.level (𝒮.centreOfSite x)) (𝒮.centreOfSite x), f z =
        ∑ᶠ z ∈ Q.system.setting.fineBlock
            (Q.system.setting.level (Q.system.setting.centreOfSite (Q.system.mapSite x)))
            (Q.system.setting.centreOfSite (Q.system.mapSite x)), restrictSites Q f z := by
      refine finsum_mem_eq_of_bijOn Q.system.mapSite hb fun z hz => ?_
      by_cases hz5 : (z : 𝒮.Point) ∈ Q.thicken (5 / 6)
      · exact (restrictSites_mapSite H f hz5).symm
      · rw [hs z fun h => hz5 (thicken_mono_two_thirds H h)]
        refine (restrictSites_eq_zero f fun x₁ h₁ e => hz5 ?_).symm
        have e₁ := mapSite_injective_on H (mem_strictPts_of_mem_thicken H h₁) (hin hz) e
        exact e₁ ▸ h₁
    have e₁ : blockAvg f ⟨𝒮.centreOfSite x, hy⟩ =
        ((𝒮.L : ℝ) ^ (𝒮.level (𝒮.centreOfSite x) * 4))⁻¹ *
        ∑ᶠ z ∈ 𝒮.fineBlock (𝒮.level (𝒮.centreOfSite x)) (𝒮.centreOfSite x), f z := rfl
    have e₂ : blockAvg (restrictSites Q f)
          ⟨Q.system.setting.centreOfSite (Q.system.mapSite x), hy'⟩ =
        ((Q.system.setting.L : ℝ) ^
          (Q.system.setting.level (Q.system.setting.centreOfSite (Q.system.mapSite x)) * 4))⁻¹ *
        ∑ᶠ z ∈ Q.system.setting.fineBlock
            (Q.system.setting.level (Q.system.setting.centreOfSite (Q.system.mapSite x)))
            (Q.system.setting.centreOfSite (Q.system.mapSite x)), restrictSites Q f z := rfl
    rw [e₁, e₂, hsum, H.L_eq, scale_local H, hidx]
theorem bond_eq_of_source_dir {S σ : ℝ} {c₁ c₂ : LatticeBond 4 S σ}
    (h₁ : (c₁.source : PeriodicTorus 4 S) = c₂.source) (h₂ : c₁.dir = c₂.dir) : c₁ = c₂ := by
  have h₃ : c₁.source = c₂.source := Subtype.ext h₁
  cases c₁
  cases c₂
  simp_all
theorem touching_bond_near (H : Setup Q) {j : ℕ} (hj : j ≤ Q.level + 1) {c : 𝒮.BondAt j}
    (hc : TouchesBlocks 𝒮 j c (Q.thicken (2 / 3))) :
    (c.source : 𝒮.Point) ∈ Q.thicken (5 / 6) ∧ (c.target : 𝒮.Point) ∈ Q.thicken (5 / 6) ∧
      ∀ x : 𝒮.FineSite, (x ∈ 𝒮.fineBlock j (c.source : 𝒮.Point) ∨
        x ∈ 𝒮.fineBlock j (c.target : 𝒮.Point)) → (x : 𝒮.Point) ∈ Q.thicken (5 / 6) := by
  obtain ⟨x₀, hx₀, hm⟩ := hc
  have hσ := scale_pos 𝒮 j
  have hab := norm_target_sub_source_le hσ.le c
  have hmono := scale_mono 𝒮 hj
  have key : ∀ p : 𝒮.Point, (‖p - (c.source : 𝒮.Point)‖ ≤ 𝒮.scale j / 2 ∨
      ‖p - (c.target : 𝒮.Point)‖ ≤ 𝒮.scale j / 2) → p ∈ Q.thicken (5 / 6) := by
    intro p hp
    refine mem_thicken_of_near H hm ?_
    have t₁ := norm_sub_le_sub_add_sub p (c.source : 𝒮.Point) (x₀ : 𝒮.Point)
    have t₂ := norm_sub_le_sub_add_sub p (c.target : 𝒮.Point) (x₀ : 𝒮.Point)
    have t₃ := norm_sub_le_sub_add_sub (c.source : 𝒮.Point) (c.target : 𝒮.Point) (x₀ : 𝒮.Point)
    have t₄ := norm_sub_le_sub_add_sub (c.target : 𝒮.Point) (c.source : 𝒮.Point) (x₀ : 𝒮.Point)
    have r₁ : ‖(c.source : 𝒮.Point) - (x₀ : 𝒮.Point)‖ =
        ‖(x₀ : 𝒮.Point) - (c.source : 𝒮.Point)‖ := norm_sub_rev _ _
    have r₂ : ‖(c.target : 𝒮.Point) - (x₀ : 𝒮.Point)‖ =
        ‖(x₀ : 𝒮.Point) - (c.target : 𝒮.Point)‖ := norm_sub_rev _ _
    have r₃ : ‖(c.source : 𝒮.Point) - (c.target : 𝒮.Point)‖ =
        ‖(c.target : 𝒮.Point) - (c.source : 𝒮.Point)‖ := norm_sub_rev _ _
    rcases hp with hp | hp <;> rcases hx₀ with hx₀ | hx₀ <;> rw [mem_fineBlock_iff] at hx₀ <;>
      linarith
  have hz : ∀ p : 𝒮.Point, ‖p - p‖ ≤ 𝒮.scale j / 2 := fun p => by
    rw [sub_self, norm_zero]
    linarith
  exact ⟨key _ (Or.inl (hz _)), key _ (Or.inr (hz _)), fun x hx =>
    key _ (hx.imp mem_fineBlock_iff.1 mem_fineBlock_iff.1)⟩
structure MatchedBonds (Q : LevelCube 𝒮 M) (j : ℕ) (c : 𝒮.BondAt j)
    (c' : Q.system.setting.BondAt j) : Prop where
  level_le : j ≤ Q.level + 1
  mem : c ∈ 𝒮.coarseBonds j
  mem' : c' ∈ Q.system.setting.coarseBonds j
  touches : TouchesBlocks 𝒮 j c (Q.thicken (2 / 3))
  source_eq : (c'.source : Q.system.setting.Point) = Q.system.embed (c.source : 𝒮.Point)
  dir_eq : c'.dir = c.dir
theorem norm_add_lt_cubeSide (H : Setup Q) {p : 𝒮.Point} (hp : p ∈ Q.thicken (5 / 6)) {r : ℝ}
    (hr : r ≤ 2 * 𝒮.scale (Q.level + 1)) : ‖p - Q.centre‖ + r < cubeSide 𝒮 M Q.level := by
  have h₁ := H.norm_sub_centre_lt p hp
  have h₂ := twelve_scale_succ_le H
  have h₃ := scale_pos 𝒮 (Q.level + 1)
  linarith
variable {j : ℕ} {c : 𝒮.BondAt j} {c' : Q.system.setting.BondAt j}
theorem half_scale_le (P : MatchedBonds Q j c c') : 𝒮.scale j / 2 ≤ 2 * 𝒮.scale (Q.level + 1) := by
  have h₁ := scale_mono 𝒮 P.level_le
  have h₂ := scale_pos 𝒮 j
  linarith
theorem target_eq (H : Setup Q) (P : MatchedBonds Q j c c') :
    (c'.target : Q.system.setting.Point) = Q.system.embed (c.target : 𝒮.Point) := by
  obtain ⟨ht, -, -⟩ := touching_bond_near H P.level_le P.touches
  have hσ := scale_pos 𝒮 j
  have hw : ‖(c.source : 𝒮.Point) - Q.centre‖ +
      ‖(Pi.single c.dir (𝒮.scale j) : Fin 4 → ℝ)‖ < cubeSide 𝒮 M Q.level := by
    rw [norm_piSingle hσ.le]
    exact norm_add_lt_cubeSide H ht (scale_le_two_mul P.level_le)
  have e₁ : (c.target : 𝒮.Point) = (c.source : 𝒮.Point) +
      torusProj 4 𝒮.side (Pi.single c.dir (𝒮.scale j)) := rfl
  have e₂ : (c'.target : Q.system.setting.Point) = (c'.source : Q.system.setting.Point) +
      torusProj 4 Q.system.setting.side
        (Pi.single c'.dir (Q.system.setting.scale j)) := rfl
  rw [e₁, e₂, P.source_eq, P.dir_eq, scale_local H, (embed_translate H hw).2.2]
theorem source_block_bijOn (H : Setup Q) (P : MatchedBonds Q j c c') :
    BijOn Q.system.mapSite (𝒮.fineBlock j (c.source : 𝒮.Point))
      (Q.system.setting.fineBlock j (c'.source : Q.system.setting.Point)) := by
  obtain ⟨ht, -, -⟩ := touching_bond_near H P.level_le P.touches
  rw [P.source_eq]
  exact fineBlock_bijOn H (norm_add_lt_cubeSide H ht (half_scale_le P))
theorem target_block_bijOn (H : Setup Q) (P : MatchedBonds Q j c c') :
    BijOn Q.system.mapSite (𝒮.fineBlock j (c.target : 𝒮.Point))
      (Q.system.setting.fineBlock j (c'.target : Q.system.setting.Point)) := by
  obtain ⟨-, ht, -⟩ := touching_bond_near H P.level_le P.touches
  rw [target_eq H P]
  exact fineBlock_bijOn H (norm_add_lt_cubeSide H ht (half_scale_le P))
theorem exists_preimage (H : Setup Q) (P : MatchedBonds Q j c c') (x' : Q.system.setting.FineSite)
    (hx' : x' ∈ Q.system.setting.fineBlock j (c'.source : Q.system.setting.Point) ∨
      x' ∈ Q.system.setting.fineBlock j (c'.target : Q.system.setting.Point)) :
    ∃ x : 𝒮.FineSite, (x ∈ 𝒮.fineBlock j (c.source : 𝒮.Point) ∨
      x ∈ 𝒮.fineBlock j (c.target : 𝒮.Point)) ∧ Q.system.mapSite x = x' := by
  rcases hx' with hx' | hx'
  · obtain ⟨x, hx, e⟩ := (source_block_bijOn H P).surjOn hx'
    exact ⟨x, Or.inl hx, e⟩
  · obtain ⟨x, hx, e⟩ := (target_block_bijOn H P).surjOn hx'
    exact ⟨x, Or.inr hx, e⟩
theorem mapSite_path (H : Setup Q) (x : 𝒮.FineSite) (i : ℕ) (μ : Fin 4)
    (h : ‖(x : 𝒮.Point) - Q.centre‖ + (i : ℝ) * 𝒮.ξ < cubeSide 𝒮 M Q.level) :
    ((x + i • unitStep 4 𝒮.side 𝒮.ξ μ : 𝒮.FineSite) : 𝒮.Point) ∈ Q.strictPts ∧
      Q.system.mapSite (x + i • unitStep 4 𝒮.side 𝒮.ξ μ) =
        Q.system.mapSite x + i • unitStep 4 Q.system.setting.side Q.system.setting.ξ μ := by
  have hξ := 𝒮.ξ_pos
  have hi : 0 ≤ (i : ℝ) * 𝒮.ξ := by positivity
  have hw : ‖(x : 𝒮.Point) - Q.centre‖ + ‖(Pi.single μ ((i : ℝ) * 𝒮.ξ) : Fin 4 → ℝ)‖ <
      cubeSide 𝒮 M Q.level := by rwa [norm_piSingle hi]
  obtain ⟨h₁, h₂, h₃⟩ := embed_translate H hw
  rw [torusProj_single_natMul (S := 𝒮.side)] at h₂ h₃
  rw [torusProj_single_natMul (S := Q.system.setting.side)] at h₃
  have ec : ((x + i • unitStep 4 𝒮.side 𝒮.ξ μ : 𝒮.FineSite) : 𝒮.Point) =
      (x : 𝒮.Point) + i • torusProj 4 𝒮.side (Pi.single μ 𝒮.ξ) := rfl
  have hin : ((x + i • unitStep 4 𝒮.side 𝒮.ξ μ : 𝒮.FineSite) : 𝒮.Point) ∈ Q.strictPts := by
    rw [ec]
    exact h₂
  refine ⟨hin, Subtype.ext ?_⟩
  have ec' : ((Q.system.mapSite x + i • unitStep 4 Q.system.setting.side Q.system.setting.ξ μ :
      Q.system.setting.FineSite) : Q.system.setting.Point) =
      ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) +
        i • torusProj 4 Q.system.setting.side (Pi.single μ Q.system.setting.ξ) := rfl
  rw [coe_mapSite H _ hin, ec', coe_mapSite H x h₁, ec, h₃, H.ξ_eq]
theorem path_norm_lt (H : Setup Q) (P : MatchedBonds Q j c c') {x : 𝒮.FineSite}
    (hx : x ∈ 𝒮.fineBlock j (c.source : 𝒮.Point)) {i : ℕ} (hi : i < 𝒮.L ^ j) :
    ‖(x : 𝒮.Point) - Q.centre‖ + (i : ℝ) * 𝒮.ξ < cubeSide 𝒮 M Q.level := by
  obtain ⟨-, -, hbl⟩ := touching_bond_near H P.level_le P.touches
  refine norm_add_lt_cubeSide H (hbl x (Or.inl hx)) ?_
  have h₁ : (i : ℝ) ≤ (𝒮.L : ℝ) ^ j := by exact_mod_cast hi.le
  have h₂ : (i : ℝ) * 𝒮.ξ ≤ 𝒮.scale j := by
    rw [𝒮.scale_eq_pow_mul]
    exact mul_le_mul_of_nonneg_right h₁ 𝒮.ξ_pos.le
  exact h₂.trans (scale_le_two_mul P.level_le)
theorem avgWeight_eq (H : Setup Q) (P : MatchedBonds Q j c c') {b : 𝒮.FineBond}
    (hb : (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6)) :
    avgWeight j c b = avgWeight j c' (Q.system.mapBond b) := by
  have hbij := source_block_bijOn H P
  have hpath : ∀ x ∈ 𝒮.fineBlock j (c.source : 𝒮.Point), ∀ i < 𝒮.L ^ j,
      ((pathBond c.dir x i).source : 𝒮.Point) ∈ Q.strictPts ∧
      Q.system.mapBond (pathBond c.dir x i) =
        pathBond c'.dir (Q.system.mapSite x) i := fun x hx i hi => by
    obtain ⟨h₁, h₂⟩ := mapSite_path H x i c.dir (path_norm_lt H P hx hi)
    refine ⟨h₁, ?_⟩
    change (⟨Q.system.mapSite (x + i • unitStep 4 𝒮.side 𝒮.ξ c.dir), c.dir⟩ :
      LatticeBond _ _ _) = ⟨Q.system.mapSite x + i • unitStep 4 Q.system.setting.side
        Q.system.setting.ξ c'.dir, c'.dir⟩
    rw [h₂, P.dir_eq]
  have himg : {p : Q.system.setting.FineSite × ℕ |
        p.1 ∈ Q.system.setting.fineBlock j (c'.source : Q.system.setting.Point) ∧
        p.2 < Q.system.setting.L ^ j ∧
        pathBond c'.dir p.1 p.2 = Q.system.mapBond b} =
      (fun p : 𝒮.FineSite × ℕ => (Q.system.mapSite p.1, p.2)) ''
        {p : 𝒮.FineSite × ℕ | p.1 ∈ 𝒮.fineBlock j (c.source : 𝒮.Point) ∧ p.2 < 𝒮.L ^ j ∧
          pathBond c.dir p.1 p.2 = b} := by
    ext ⟨x', i⟩
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      obtain ⟨x, hx, rfl⟩ := hbij.surjOn h₁
      change i < Q.system.setting.L ^ j at h₂
      rw [H.L_eq] at h₂
      obtain ⟨hin, hE⟩ := hpath x hx i h₂
      refine ⟨(x, i), ⟨hx, h₂, ?_⟩, rfl⟩
      exact mapBond_injective_on H hin (mem_strictPts_of_mem_thicken H hb) (hE.trans h₃)
    · rintro ⟨⟨x, i₀⟩, ⟨h₁, h₂, h₃⟩, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨hbij.mapsTo h₁, ?_, ?_⟩
      · change i₀ < Q.system.setting.L ^ j
        rw [H.L_eq]
        exact h₂
      · have h₃' : pathBond c.dir x i₀ = b := h₃
        rw [← h₃']
        exact ((hpath x h₁ i₀ h₂).2).symm
  have hinj : InjOn (fun p : 𝒮.FineSite × ℕ => (Q.system.mapSite p.1, p.2))
      {p : 𝒮.FineSite × ℕ | p.1 ∈ 𝒮.fineBlock j (c.source : 𝒮.Point) ∧ p.2 < 𝒮.L ^ j ∧
        pathBond c.dir p.1 p.2 = b} := by
    rintro ⟨x, i⟩ ⟨h₁, -, -⟩ ⟨x₂, i₂⟩ ⟨h₂, -, -⟩ he
    simp only [Prod.mk.injEq] at he
    rw [show x = x₂ from hbij.injOn h₁ h₂ he.1, he.2]
  unfold avgWeight
  rw [himg, hinj.ncard_image, H.L_eq]
def AvgOpFacts (𝒯 : NestedRegions) : Prop :=
  (∀ (n : ℕ) (c : 𝒯.BondAt n) (A : 𝒯.FineBond → ℝ),
      bondAvg n A c = ∑ᶠ b, avgWeight n c b * A b) ∧
    ∀ A : 𝒯.FineBond → ℝ, avgOp A ∈ 𝒯.oneForms ∧
      (∀ A' ∈ 𝒯.oneForms, bondInner (avgOp A) A' = avgForm A A') ∧
      ∀ b ∈ 𝒯.bonds, avgOp A b =
        (𝒯.ξ ^ 4)⁻¹ * ∑ j ∈ Finset.range (𝒯.s + 1), ∑ᶠ c ∈ 𝒯.coarseBonds j,
          gaugeParam * 𝒯.scale j ^ (4 - 2) * avgWeight j c b * bondAvg j A c
def levelSum (𝒯 : NestedRegions) (A : 𝒯.FineBond → ℝ) (b : 𝒯.FineBond) (j : ℕ) : ℝ :=
  ∑ᶠ c ∈ 𝒯.coarseBonds j,
    gaugeParam * 𝒯.scale j ^ (4 - 2) * avgWeight j c b * bondAvg j A c
theorem avgOp_eq_sum {𝒯 : NestedRegions} (V : AvgOpFacts 𝒯) (A : 𝒯.FineBond → ℝ)
    {b : 𝒯.FineBond} (hb : b ∈ 𝒯.bonds) :
    avgOp A b = (𝒯.ξ ^ 4)⁻¹ * ∑ j ∈ Finset.range (𝒯.s + 1), levelSum 𝒯 A b j :=
  (V.2 A).2.2 b hb
theorem bondAvg_eq (H : Setup Q) (V₁ : AvgOpFacts 𝒮) (V₂ : AvgOpFacts Q.system.setting)
    (W₁ : AvgWeightProps 𝒮)
    (W₂ : AvgWeightProps Q.system.setting)
    (P : MatchedBonds Q j c c') (A : 𝒮.FineBond → ℝ) :
    bondAvg j A c = bondAvg j (restrictBonds Q A) c' := by
  obtain ⟨-, -, hbl⟩ := touching_bond_near H P.level_le P.touches
  rw [V₁.1, V₂.1]
  have s₁ : Function.support (fun b => avgWeight j c b * A b) ⊆
      {b : 𝒮.FineBond | (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6)} := by
    intro b hb
    have hw : avgWeight j c b ≠ 0 := left_ne_zero_of_mul (Function.mem_support.1 hb)
    exact hbl _ (W₁.avgWeight_support j c P.mem b hw).2
  have s₂ : Function.support (fun b' => avgWeight j c' b' * restrictBonds Q A b') ⊆
      Q.system.mapBond '' {b : 𝒮.FineBond | (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6)} := by
    intro b' hb'
    have hw : avgWeight j c' b' ≠ 0 := left_ne_zero_of_mul (Function.mem_support.1 hb')
    obtain ⟨x, hx, he⟩ := exists_preimage H P _ (W₂.avgWeight_support j c' P.mem' b' hw).2
    refine ⟨⟨x, b'.dir⟩, hbl x hx, ?_⟩
    change (⟨Q.system.mapSite x, b'.dir⟩ : LatticeBond _ _ _) = b'
    rw [he]
  rw [finsum_eq_finsum_mem_of_support_subset s₁, finsum_eq_finsum_mem_of_support_subset s₂]
  have hinj : InjOn Q.system.mapBond
      {b : 𝒮.FineBond | (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6)} := fun b hb b' hb' e =>
    mapBond_injective_on H (mem_strictPts_of_mem_thicken H hb)
      (mem_strictPts_of_mem_thicken H hb') e
  refine finsum_mem_eq_of_bijOn _ hinj.bijOn_image fun b hb => ?_
  rw [avgWeight_eq H P hb, restrictBonds_mapBond H A hb]
theorem levelSum_eq (H : Setup Q) (V₁ : AvgOpFacts 𝒮) (V₂ : AvgOpFacts Q.system.setting)
    (W₁ : AvgWeightProps 𝒮)
    (W₂ : AvgWeightProps Q.system.setting)
    {A : 𝒮.FineBond → ℝ} (hA : ∀ b, A b ≠ 0 → (b.source : 𝒮.Point) ∈ Q.thicken (2 / 3))
    (hA' : ∀ b', restrictBonds Q A b' ≠ 0 →
      (b'.source : Q.system.setting.Point) ∈ Q.system.embed '' Q.thicken (2 / 3))
    {j : ℕ} (hj : j = Q.level ∨ j = Q.level + 1) {b : 𝒮.FineBond}
    (hb : (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6)) :
    levelSum 𝒮 A b j = levelSum Q.system.setting (restrictBonds Q A) (Q.system.mapBond b) j := by
  have hlev : j ≤ Q.level + 1 := by omega
  have e₁ : levelSum 𝒮 A b j =
      ∑ᶠ c ∈ {c | c ∈ 𝒮.coarseBonds j ∧ TouchesBlocks 𝒮 j c (Q.thicken (2 / 3))},
        gaugeParam * 𝒮.scale j ^ (4 - 2) * avgWeight j c b * bondAvg j A c := by
    refine finsum_mem_inter_support_eq _ _ _ ?_
    ext c
    constructor
    · rintro ⟨hc, hne⟩
      refine ⟨⟨hc, ?_⟩, hne⟩
      by_contra hn
      exact hne (by simp only [bondAvg_eq_zero_of_not_touches V₁.1 W₁ hc hA hn, mul_zero])
    · rintro ⟨⟨hc, -⟩, hne⟩
      exact ⟨hc, hne⟩
  have e₂ : levelSum Q.system.setting (restrictBonds Q A) (Q.system.mapBond b) j =
      ∑ᶠ c ∈ {c | c ∈ Q.system.setting.coarseBonds j ∧
          TouchesBlocks Q.system.setting j c (Q.system.embed '' Q.thicken (2 / 3))},
        gaugeParam * Q.system.setting.scale j ^ (4 - 2) *
          avgWeight j c (Q.system.mapBond b) * bondAvg j (restrictBonds Q A) c := by
    refine finsum_mem_inter_support_eq _ _ _ ?_
    ext c
    constructor
    · rintro ⟨hc, hne⟩
      refine ⟨⟨hc, ?_⟩, hne⟩
      by_contra hn
      exact hne (by simp only [bondAvg_eq_zero_of_not_touches V₂.1 W₂ hc hA' hn, mul_zero])
    · rintro ⟨⟨hc, -⟩, hne⟩
      exact ⟨hc, hne⟩
  have : Nonempty (Q.system.setting.BondAt j) := ⟨⟨0, 0⟩⟩
  let e : 𝒮.BondAt j → Q.system.setting.BondAt j := fun c =>
    Classical.epsilon fun c' => c' ∈ Q.system.setting.coarseBonds j ∧
      TouchesBlocks Q.system.setting j c' (Q.system.embed '' Q.thicken (2 / 3)) ∧
      (c'.source : Q.system.setting.Point) = Q.system.embed (c.source : 𝒮.Point) ∧
      c'.dir = c.dir
  have he : ∀ c ∈ {c | c ∈ 𝒮.coarseBonds j ∧ TouchesBlocks 𝒮 j c (Q.thicken (2 / 3))},
      MatchedBonds Q j c (e c) := by
    rintro c ⟨hc, hm⟩
    have h := Classical.epsilon_spec (H.bond_forward j c hc hm)
    exact ⟨hlev, hc, h.1, hm, h.2.2.1, h.2.2.2⟩
  have hbij : BijOn e {c | c ∈ 𝒮.coarseBonds j ∧ TouchesBlocks 𝒮 j c (Q.thicken (2 / 3))}
      {c | c ∈ Q.system.setting.coarseBonds j ∧
        TouchesBlocks Q.system.setting j c (Q.system.embed '' Q.thicken (2 / 3))} := by
    refine ⟨fun c hc => ?_, fun c₁ h₁ c₂ h₂ h => ?_, fun c' hc' => ?_⟩
    · have h := Classical.epsilon_spec (H.bond_forward j c hc.1 hc.2)
      exact ⟨h.1, h.2.1⟩
    · have P₁ := he c₁ h₁
      have P₂ := he c₂ h₂
      have t₁ := (touching_bond_near H hlev h₁.2).1
      have t₂ := (touching_bond_near H hlev h₂.2).1
      refine bond_eq_of_source_dir (H.embed_injOn (mem_strictPts_of_mem_thicken H t₁)
        (mem_strictPts_of_mem_thicken H t₂) ?_) ?_
      · rw [← P₁.source_eq, ← P₂.source_eq, h]
      · rw [← P₁.dir_eq, ← P₂.dir_eq, h]
    · obtain ⟨c, hc, hm, ht, hd⟩ := H.bond_backward j hj c' hc'.1 hc'.2
      have P := he c ⟨hc, hm⟩
      exact ⟨c, ⟨hc, hm⟩,
        bond_eq_of_source_dir (P.source_eq.trans ht.symm) (P.dir_eq.trans hd.symm)⟩
  rw [e₁, e₂]
  refine finsum_mem_eq_of_bijOn e hbij fun c hc => ?_
  have P := he c hc
  rw [avgWeight_eq H P hb, bondAvg_eq H V₁ V₂ W₁ W₂ P A, scale_local H]
theorem coarseBonds_local_eq_empty (H : Setup Q) {j : ℕ} (hj : j < Q.level) :
    Q.system.setting.coarseBonds j = ∅ := by
  have h₁ : Q.system.setting.Ω (j + 1) = univ := H.Ω_eq_univ _ hj
  refine eq_empty_iff_forall_notMem.2 fun c hc => ?_
  by_cases h₀ : j = 0
  · subst h₀
    simp only [coarseBonds, mem_setOf_eq, if_true] at hc
    obtain ⟨b, -, -, -, h₃, -⟩ := hc
    have e : Q.system.setting.Ω 1 = univ := h₁
    exact h₃ (by rw [e]; trivial)
  · simp only [coarseBonds, mem_setOf_eq, if_neg h₀] at hc
    exact hc.2.1 (by rw [h₁]; trivial)
theorem bondFunctionsMatch (H : Setup Q) (V₁ : AvgOpFacts 𝒮) (V₂ : AvgOpFacts Q.system.setting)
    (W₁ : AvgWeightProps 𝒮)
    (W₂ : AvgWeightProps Q.system.setting)
    {A : 𝒮.FineBond → ℝ} (hs : AnchorSupported (Q.thicken (2 / 3)) A) :
    BondFunctionsMatch Q (avgOp A) (avgOp (restrictBonds Q A)) := by
  have hA : ∀ b, A b ≠ 0 → (b.source : 𝒮.Point) ∈ Q.thicken (2 / 3) := fun b hb => by
    have h₁ : (𝒮.anchor b : 𝒮.Point) ∈ Q.thicken (2 / 3) := by
      by_contra hn
      exact hb (hs b hn)
    have h₂ := anchor_eq_source_of_anchor H (thicken_mono_two_thirds H h₁)
    rwa [h₂] at h₁
  have hA' : ∀ b', restrictBonds Q A b' ≠ 0 →
      (b'.source : Q.system.setting.Point) ∈ Q.system.embed '' Q.thicken (2 / 3) := by
    intro b' hb'
    have hex : ∃ b : 𝒮.FineBond, (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6) ∧
        Q.system.mapBond b = b' := by
      by_contra hn
      exact hb' (restrictBonds_eq_zero A fun b h₁ e => hn ⟨b, h₁, e⟩)
    obtain ⟨b, h₁, rfl⟩ := hex
    rw [restrictBonds_mapBond H A h₁] at hb'
    exact ⟨_, hA b hb', (coe_mapSite H b.source (mem_strictPts_of_mem_thicken H h₁)).symm⟩
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    by_cases hbb : b ∈ 𝒮.bonds
    · rw [avgOp_eq_sum V₁ A hbb, Finset.sum_eq_zero, mul_zero]
      intro j _
      refine finsum_mem_eq_zero_of_forall_mem fun c hc => ?_
      by_contra hne
      have ha := right_ne_zero_of_mul hne
      have hw := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
      have hm : TouchesBlocks 𝒮 j c (Q.thicken (2 / 3)) :=
        by_contra fun hn => ha (bondAvg_eq_zero_of_not_touches V₁.1 W₁ hc hA hn)
      have hj := H.bond_level j c hc hm
      obtain ⟨-, -, hbl⟩ := touching_bond_near H (by omega) hm
      have ht := hbl _ (W₁.avgWeight_support j c hc b hw).2
      apply hb
      change (𝒮.anchor b : 𝒮.Point) ∈ _
      rw [anchor_eq_source H ht]
      exact ht
    · have h : ∀ b, b ∉ 𝒮.bonds → avgOp A b = 0 := (V₁.2 A).1
      exact h b hbb
  · intro b' hb'
    rw [avgOp_eq_sum V₂ _ (H.mem_bonds b'), Finset.sum_eq_zero, mul_zero]
    intro j hjr
    refine finsum_mem_eq_zero_of_forall_mem fun c' hc' => ?_
    by_contra hne
    have ha := right_ne_zero_of_mul hne
    have hw := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
    have hm' : TouchesBlocks Q.system.setting j c' (Q.system.embed '' Q.thicken (2 / 3)) :=
      by_contra fun hn => ha (bondAvg_eq_zero_of_not_touches V₂.1 W₂ hc' hA' hn)
    have hlt := Finset.mem_range.1 hjr
    rw [H.s_eq] at hlt
    have hj : j = Q.level ∨ j = Q.level + 1 := by
      by_contra hn
      have hjn : j < Q.level := by omega
      rw [coarseBonds_local_eq_empty H hjn] at hc'
      exact hc'
    obtain ⟨c, hc, hm, ht, hd⟩ := H.bond_backward j hj c' hc' hm'
    have P : MatchedBonds Q j c c' := ⟨by omega, hc, hc', hm, ht, hd⟩
    obtain ⟨x, hx, he⟩ := exists_preimage H P _ (W₂.avgWeight_support j c' hc' b' hw).2
    have hx5 := (touching_bond_near H P.level_le hm).2.2 x hx
    apply hb'
    change (Q.system.setting.anchor b' : Q.system.setting.Point) ∈ _
    rw [anchor_local H, ← he, coe_mapSite H x (mem_strictPts_of_mem_thicken H hx5)]
    exact ⟨x, hx5, rfl⟩
  · intro b hb
    have hb₁ : (𝒮.anchor b : 𝒮.Point) ∈ Q.thicken (5 / 6) := hb
    have ht : (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6) := by
      rwa [anchor_eq_source_of_anchor H hb₁] at hb₁
    have hbb : b ∈ 𝒮.bonds := 𝒮.mem_bonds_of_mem b
      (H.mem_Ω_zero b.source _ ht (by rw [sub_self, norm_zero]; exact 𝒮.ξ_pos.le))
      (H.mem_Ω_zero b.target _ ht (by
        rw [norm_sub_rev]
        exact norm_target_sub_source_le 𝒮.ξ_pos.le b))
    have z₁ : ∀ j < 𝒮.s + 1, j ≠ Q.level → j ≠ Q.level + 1 → levelSum 𝒮 A b j = 0 := by
      intro j _ h₁ h₂
      refine finsum_mem_eq_zero_of_forall_mem fun c hc => ?_
      have hn : ¬TouchesBlocks 𝒮 j c (Q.thicken (2 / 3)) := fun hm =>
        (H.bond_level j c hc hm).elim h₁ h₂
      rw [bondAvg_eq_zero_of_not_touches V₁.1 W₁ hc hA hn, mul_zero]
    have z₂ : 𝒮.s + 1 ≤ Q.level + 1 → levelSum 𝒮 A b (Q.level + 1) = 0 := by
      intro h
      unfold levelSum
      rw [𝒮.coarseBonds_eq_empty_of_lt (by omega), finsum_mem_empty]
    have z₃ : ∀ j < Q.system.setting.s + 1, j ≠ Q.level → j ≠ Q.level + 1 →
        levelSum Q.system.setting (restrictBonds Q A) (Q.system.mapBond b) j = 0 := by
      intro j hj h₁ h₂
      rw [H.s_eq] at hj
      unfold levelSum
      rw [coarseBonds_local_eq_empty H (by omega), finsum_mem_empty]
    have z₄ : Q.system.setting.s + 1 ≤ Q.level + 1 →
        levelSum Q.system.setting (restrictBonds Q A) (Q.system.mapBond b) (Q.level + 1) = 0 := by
      intro h
      rw [H.s_eq] at h
      omega
    have hl := H.level_le
    rw [avgOp_eq_sum V₁ A hbb, avgOp_eq_sum V₂ _ (H.mem_bonds _),
      sum_range_eq_add_succ_of_vanish _ (by omega) z₁ z₂,
      sum_range_eq_add_succ_of_vanish _ (by rw [H.s_eq]; omega) z₃ z₄,
      levelSum_eq H V₁ V₂ W₁ W₂ hA hA' (Or.inl rfl) ht,
      levelSum_eq H V₁ V₂ W₁ W₂ hA hA' (Or.inr rfl) ht,
      H.ξ_eq]
theorem topLevel_le (𝒮 : NestedRegions) : topLevel 𝒮 ≤ 𝒮.s := by
  refine csSup_le' fun n hn => ?_
  by_contra h
  have h' : 𝒮.s < n := not_le.1 h
  have hn' : (𝒮.Ω n).Nonempty := hn
  rw [𝒮.Ω_eq_empty n h'] at hn'
  exact not_nonempty_empty hn'
theorem mem_Ω_zero_of_near (hpos : PositionByType.FirstTypePosition Q) (hM : 1 ≤ M)
    (y : 𝒮.FineSite) {x : 𝒮.Point} (hx : x ∈ Q.thicken (5 / 6))
    (hxy : ‖x - (y : 𝒮.Point)‖ ≤ 𝒮.ξ) : (y : 𝒮.Point) ∈ 𝒮.Ω 0 := by
  have hξ := 𝒮.ξ_pos
  have hMξ : 𝒮.ξ ≤ (M : ℝ) * 𝒮.ξ := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  by_contra hn
  have hy0 : (y : 𝒮.Point) ∈ cubeAt (y : 𝒮.Point) (𝒮.scale 0) := by
    change supNorm ((y : 𝒮.Point) - (y : 𝒮.Point)) ≤ 𝒮.scale 0 / 2
    rw [sub_self, supNorm_eq_norm, norm_zero, scale_zero]
    positivity
  have hc : (y : 𝒮.Point) ∈ 𝒮.cubeComplementAt 0 (𝒮.Ω 0) :=
    ⟨cubeAt (y : 𝒮.Point) (𝒮.scale 0),
      ⟨⟨y, by rw [scale_zero]; exact y.2, rfl⟩, fun hsub => hn (hsub hy0)⟩, hy0⟩
  have h₁ : supSetDist (Q.thicken (5 / 6)) (𝒮.cubeComplementAt 0 (𝒮.Ω 0)) ≤
      ENNReal.ofReal (supNorm (x - (y : 𝒮.Point))) :=
    iInf₂_le_of_le _ hx (iInf₂_le _ hc)
  have h₂ := hpos.far_from_outside.trans_le h₁
  rw [supNorm_eq_norm] at h₂
  exact absurd h₂ (not_lt.2 (ENNReal.ofReal_le_ofReal (hxy.trans hMξ)))
end YangMills.Construction.PartitionCubes.CubeTorusAveraging

import YangMills.Construction.Lattice.AxialPathUniqueness
import YangMills.Construction.Lattice.BareBaseSitesOfTheSchemesProof
import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Towers.IteratesOfTheLinearMapsAsMeansOverBlocks
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
namespace CubeAverages
open TrivialLinearization
private def stepValues {X Y : Type*} [Add X] (g : X → Y) (d : X) : X → ℕ → List Y
  | _, 0 => []
  | x, N + 1 => g x :: stepValues g d (x + d) N
private theorem stepValues_add {X Y : Type*} [AddCommGroup X] (g : X → Y) (d : X) (a b : ℕ) :
    ∀ x, stepValues g d x (a + b) = stepValues g d x a ++ stepValues g d (x + a • d) b := by
  induction a with
  | zero => intro x; simp [stepValues]
  | succ a ih =>
    intro x
    have e : x + d + a • d = x + (a + 1) • d := by rw [add_nsmul, one_nsmul]; abel
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [stepValues, ih, List.cons_append, e]
abbrev _root_.YangMills.DeltaSharedProofs.p502542 := @stepValues_add
private theorem sum_stepValues_average {X Y P R : Type*} [AddCommGroup X] [AddCommGroup Y]
    (gX : X → P) (dX : X) (gY : Y → R) (dY : Y) (Q : P → Matrices.ComplexMatrix2)
    (B : R → Matrices.ComplexMatrix2)
    (S : X → Set Y) (w : ℂ) (M : ℕ) (hfin : ∀ x, (S x).Finite)
    (hS : ∀ x, S (x + dX) = (fun z => z + M • dY) '' S x)
    (hQ : ∀ x, Q (gX x) = w • ∑ᶠ z ∈ S x, ((stepValues gY dY z M).map B).sum) (N : ℕ) :
    ∀ x, ((stepValues gX dX x N).map Q).sum =
      w • ∑ᶠ z ∈ S x, ((stepValues gY dY z (N * M)).map B).sum := by
  induction N with
  | zero => intro x; simp [stepValues]
  | succ N ih =>
    intro x
    have hinj : Function.Injective (fun z : Y => z + M • dY) := add_left_injective _
    have hshift : ∑ᶠ z ∈ S (x + dX), ((stepValues gY dY z (N * M)).map B).sum =
        ∑ᶠ z ∈ S x, ((stepValues gY dY (z + M • dY) (N * M)).map B).sum := by
      rw [hS, finsum_mem_image hinj.injOn]
    simp only [stepValues, List.map_cons, List.sum_cons]
    rw [hQ, ih, hshift, ← smul_add, ← finsum_mem_add_distrib (hfin x)]
    congr 1
    refine finsum_mem_congr rfl fun z _ => ?_
    rw [show (N + 1) * M = M + N * M by ring, stepValues_add, List.map_append, List.sum_append]
abbrev _root_.YangMills.DeltaSharedProofs.p501359 := @sum_stepValues_average
variable {L n k : ℕ}
private theorem forwardFlow_eq_stepValues {j : ℤ} (μ : Fin 4) (N : ℕ) :
    ∀ x : PeriodicLattice.Site L n j, PeriodicLattice.forwardAxisPath x μ N =
      stepValues (fun y => PeriodicLattice.Bond.forwardFrom y μ)
        (PeriodicLattice.unitStep L n j μ) x N := by
  induction N with
  | zero => intro x; rfl
  | succ N ih => intro x; simp only [PeriodicLattice.forwardAxisPath, stepValues, ih]
abbrev _root_.YangMills.DeltaSharedProofs.p501918 := @forwardFlow_eq_stepValues
private theorem backwardFlow_eq_stepValues {j : ℤ} (μ : Fin 4) (N : ℕ) :
    ∀ x : PeriodicLattice.Site L n j, PeriodicLattice.backwardAxisPath x μ N =
      stepValues (fun y => PeriodicLattice.Bond.backwardFrom y μ)
        (-PeriodicLattice.unitStep L n j μ) x N := by
  induction N with
  | zero => intro x; rfl
  | succ N ih => intro x; simp only [PeriodicLattice.backwardAxisPath, stepValues, ih, sub_eq_add_neg]
abbrev _root_.YangMills.DeltaSharedProofs.p500527 := @backwardFlow_eq_stepValues
private theorem nsmul_pointOnAxis (N : ℕ) (μ : Fin 4) (t : ℝ) :
    N • PeriodicLattice.pointOnAxis L n μ t = PeriodicLattice.pointOnAxis L n μ ((N : ℝ) * t) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp only [PeriodicLattice.pointOnAxis, Pi.smul_apply, Pi.single_eq_same]
    rw [← nsmul_eq_mul, AddCircle.coe_nsmul]
  · simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
private theorem coe_pow_nsmul_unitStep (hL : 0 < L) {j j' : ℤ} (r : ℕ) (e : j' = j + r)
    (μ : Fin 4) :
    (((L ^ r) • PeriodicLattice.unitStep L n j' μ : PeriodicLattice.Site L n j') :
        PeriodicLattice.FourTorus L n) =
      (PeriodicLattice.unitStep L n j μ : PeriodicLattice.Site L n j) := by
  subst e
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [AddSubgroup.coe_nsmul]
  show (L ^ r) • PeriodicLattice.pointOnAxis L n μ (PeriodicLattice.meshSize L (j + r)) =
    PeriodicLattice.pointOnAxis L n μ (PeriodicLattice.meshSize L j)
  rw [nsmul_pointOnAxis]
  congr 1
  simp only [PeriodicLattice.meshSize, Nat.cast_pow]
  rw [neg_add, zpow_add₀ hL', zpow_neg _ (r : ℤ), zpow_natCast]
  field_simp
abbrev _root_.YangMills.SharedProofs.p1497 := @coe_pow_nsmul_unitStep
private theorem coe_toSublattice (hL : 0 < L) {j j' : ℤ} (h : j ≤ j')
    (y : PeriodicLattice.Site L n j) :
    ((PeriodicLattice.Site.toSublattice y j' : PeriodicLattice.Site L n j') :
      PeriodicLattice.FourTorus L n) = y := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
private theorem pow_lt_pow_levelDepth (hL : 13 ≤ L) (hn : 0 < n) {i r : ℕ} (h : i + r ≤ k) :
    ((L ^ r : ℕ) : ℝ) < (L : ℝ) ^ ((n : ℤ) + PeriodicLattice.levelDepth k i) := by
  have h1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have e : (n : ℤ) + PeriodicLattice.levelDepth k i = ((n + k - i : ℕ) : ℤ) := by
    simp only [PeriodicLattice.levelDepth]
    omega
  rw [e, zpow_natCast]
  push_cast
  exact pow_lt_pow_right₀ h1 (by omega)
abbrev _root_.YangMills.SharedProofs.p107281 := @pow_lt_pow_levelDepth
private theorem crossingPath_eq_axialPath (hS : PeriodicLattice.AxialPathUniqueness)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j j' : ℤ} (hjj : j ≤ j')
    (hj : -(n : ℤ) ≤ j') (c : PeriodicLattice.Bond L n j) (x : PeriodicLattice.Site L n j')
    (μ : Fin 4) (t : ℤ) (hlen : ((|t| : ℤ) : ℝ) < (L : ℝ) ^ ((n : ℤ) + j'))
    (hd : ((c.target - c.source : PeriodicLattice.Site L n j) : PeriodicLattice.FourTorus L n) =
      ((t • PeriodicLattice.unitStep L n j' μ : PeriodicLattice.Site L n j') :
        PeriodicLattice.FourTorus L n)) :
    PeriodicLattice.crossingPath c x = PeriodicLattice.flowAlong x μ t := by
  have hL : 0 < L := by have := hLs.2; omega
  have hdisp : PeriodicLattice.IsAxialDisplacement x (PeriodicLattice.shiftAcross c x) μ t := by
    refine ⟨?_, hlen⟩
    apply Subtype.ext
    rw [← hd]
    simp only [PeriodicLattice.shiftAcross, add_sub_cancel_left]
    exact coe_toSublattice hL hjj _
  exact (hS L n hLs hn j' hj x _ μ μ t t hdisp hdisp).2
abbrev _root_.YangMills.SharedProofs.p1693 := @crossingPath_eq_axialPath
private theorem levelDepth_eq_add {a i r : ℕ} (h : a = i + r) :
    PeriodicLattice.levelDepth k i = PeriodicLattice.levelDepth k a + (r : ℤ) := by
  subst h
  simp only [PeriodicLattice.levelDepth]
  push_cast
  ring
abbrev _root_.YangMills.SharedProofs.p67689 := @levelDepth_eq_add
private theorem neg_le_levelDepth {a : ℕ} (ha : a ≤ k) :
    -(n : ℤ) ≤ PeriodicLattice.levelDepth k a := by
  simp only [PeriodicLattice.levelDepth]
  omega
private theorem crossingPath_of_forward (hS : PeriodicLattice.AxialPathUniqueness)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {a i r : ℕ} (h : a = i + r)
    (ha : a ≤ k) (c : Edge L n k a) (μ : Fin 4)
    (hc : c.target - c.source = PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k a) μ)
    (x : Vertex L n k i) :
    PeriodicLattice.crossingPath c x =
      stepValues (fun y => PeriodicLattice.Bond.forwardFrom y μ)
        (PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ) x (L ^ r) := by
  have hL : 0 < L := by have := hLs.2; omega
  have e := levelDepth_eq_add (k := k) h
  have hjj : PeriodicLattice.levelDepth k a ≤ PeriodicLattice.levelDepth k i := by omega
  rw [crossingPath_eq_axialPath hS hLs hn hjj (neg_le_levelDepth (by omega)) c x μ
    ((L ^ r : ℕ) : ℤ)
    (by
      have := pow_lt_pow_levelDepth (k := k) hLs.2 hn (i := i) (r := r) (by omega)
      simpa using this)
    (by rw [hc, natCast_zsmul]; exact (coe_pow_nsmul_unitStep hL r e μ).symm)]
  rw [PeriodicLattice.flowAlong, if_pos (by positivity), Int.toNat_natCast,
    forwardFlow_eq_stepValues]
abbrev _root_.YangMills.DeltaSharedProofs.p502237 := @crossingPath_of_forward
private theorem crossingPath_of_backward (hS : PeriodicLattice.AxialPathUniqueness)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {a i r : ℕ} (h : a = i + r)
    (ha : a ≤ k) (c : Edge L n k a) (μ : Fin 4)
    (hc : c.target - c.source =
      -PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k a) μ)
    (x : Vertex L n k i) :
    PeriodicLattice.crossingPath c x =
      stepValues (fun y => PeriodicLattice.Bond.backwardFrom y μ)
        (-PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ) x (L ^ r) := by
  have hL : 0 < L := by have := hLs.2; omega
  have e := levelDepth_eq_add (k := k) h
  have hjj : PeriodicLattice.levelDepth k a ≤ PeriodicLattice.levelDepth k i := by omega
  rw [crossingPath_eq_axialPath hS hLs hn hjj (neg_le_levelDepth (by omega)) c x μ
    (-((L ^ r : ℕ) : ℤ))
    (by
      have := pow_lt_pow_levelDepth (k := k) hLs.2 hn (i := i) (r := r) (by omega)
      simpa using this)
    (by
      rw [hc, neg_smul, natCast_zsmul, AddSubgroup.coe_neg, AddSubgroup.coe_neg]
      exact congrArg Neg.neg (coe_pow_nsmul_unitStep hL r e μ).symm)]
  have hpos : 0 < ((L ^ r : ℕ) : ℤ) := by exact_mod_cast pow_pos hL r
  rw [PeriodicLattice.flowAlong, if_neg (by omega), neg_neg, Int.toNat_natCast,
    backwardFlow_eq_stepValues]
abbrev _root_.YangMills.DeltaSharedProofs.p500995 := @crossingPath_of_backward
private theorem levelDepth_add_self (m : ℕ) :
    PeriodicLattice.levelDepth k m + (m : ℤ) = PeriodicLattice.levelDepth k 0 := by
  simp [PeriodicLattice.levelDepth]
private theorem mem_baseVerticesOfCube {m : ℕ} (y : Vertex L n k m) (z : Vertex L n k 0) :
    z ∈ baseVerticesOfCube L n k m y ↔
      (z : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.cubeAround y := by
  show (z : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock m y ↔ _
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [levelDepth_add_self]
  exact z.2
private theorem image_baseVerticesOfCube {m : ℕ} (y : Vertex L n k m) :
    (fun z : Vertex L n k 0 => (z : PeriodicLattice.FourTorus L n)) ''
        baseVerticesOfCube L n k m y =
      PeriodicLattice.refinedBlock m y := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hp
    have hl : p ∈ PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k 0) := by
      rw [← levelDepth_add_self m]
      exact hp.2
    exact ⟨⟨p, hl⟩, hp, rfl⟩
private theorem ncard_baseVerticesOfCube (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {m : ℕ} (hm : m ≤ k)
    (y : Vertex L n k m) :
    (baseVerticesOfCube L n k m y).ncard = L ^ (4 * m) := by
  have h := ((hP L n hLs hn (PeriodicLattice.levelDepth k m) m 0
    (neg_le_levelDepth hm)).1 y).2.2
  rw [← image_baseVerticesOfCube, Set.ncard_image_of_injective _ Subtype.val_injective] at h
  exact h
private theorem finite_baseVerticesOfCube (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {m : ℕ} (hm : m ≤ k)
    (y : Vertex L n k m) :
    (baseVerticesOfCube L n k m y).Finite := by
  have hL : 0 < L := by have := hLs.2; omega
  apply Set.finite_of_ncard_pos
  rw [ncard_baseVerticesOfCube hP hLs hn hm]
  exact pow_pos hL _
private theorem baseVerticesOfCube_add {m : ℕ} (x t : Vertex L n k m) (t' : Vertex L n k 0)
    (ht : (t' : PeriodicLattice.FourTorus L n) = t) :
    baseVerticesOfCube L n k m (x + t) =
      (fun z => z + t') '' baseVerticesOfCube L n k m x := by
  have key : ∀ z : Vertex L n k 0, z - t' ∈ baseVerticesOfCube L n k m x ↔
      z ∈ baseVerticesOfCube L n k m (x + t) := by
    intro z
    rw [mem_baseVerticesOfCube, mem_baseVerticesOfCube]
    have e : (((z - t' : Vertex L n k 0) : PeriodicLattice.FourTorus L n) -
        (x : PeriodicLattice.FourTorus L n)) =
        (z : PeriodicLattice.FourTorus L n) -
          ((x + t : Vertex L n k m) : PeriodicLattice.FourTorus L n) := by
      rw [AddSubgroup.coe_sub, AddSubgroup.coe_add, ht]
      abel
    simp only [PeriodicLattice.cubeAround, Set.mem_ofPred_eq, e]
  ext z
  constructor
  · intro hz
    exact ⟨z - t', (key z).2 hz, sub_add_cancel z t'⟩
  · rintro ⟨u, hu, rfl⟩
    apply (key _).1
    simpa using hu
private theorem mem_refinedBlock_succ {j j' : ℤ} (e : j' = j + ((1 : ℕ) : ℤ)) {m : ℕ}
    (y : PeriodicLattice.Site L n j) (h : PeriodicLattice.RefinedBlockOfSumOrder L n j 1 m y)
    (p : PeriodicLattice.FourTorus L n) :
    p ∈ PeriodicLattice.refinedBlock (m + 1) y ↔
      ∃ x : PeriodicLattice.Site L n j',
        (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∧
          p ∈ PeriodicLattice.refinedBlock m x := by
  subst e
  rw [Nat.add_comm m 1, show PeriodicLattice.refinedBlock (1 + m) y = _ from h]
  simp only [mem_iUnion, exists_prop]
private theorem finsum_baseVerticesOfCube_succ (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {m : ℕ} (hm : m + 1 ≤ k)
    (y : Vertex L n k (m + 1)) (f : Vertex L n k 0 → Matrices.ComplexMatrix2) :
    ∑ᶠ z ∈ baseVerticesOfCube L n k (m + 1) y, f z =
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k m) y,
        ∑ᶠ z ∈ baseVerticesOfCube L n k m x, f z := by
  have hfinB : (PeriodicLattice.unitBlock y).Finite := by
    have hL : 0 < L := by have := hLs.2; omega
    apply Set.finite_of_ncard_pos
    rw [((hP L n hLs hn (PeriodicLattice.levelDepth k (m + 1)) 1 0
      (neg_le_levelDepth hm)).1 y).2.2]
    exact pow_pos hL _
  have hI : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k m) y).Finite :=
    hfinB.preimage Subtype.val_injective.injOn
  have hU : baseVerticesOfCube L n k (m + 1) y =
      ⋃ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k m) y,
        baseVerticesOfCube L n k m x := by
    ext z
    have hsum := (hP L n hLs hn (PeriodicLattice.levelDepth k (m + 1)) 1 m
      (neg_le_levelDepth hm)).2.2.1 y
    have e : PeriodicLattice.levelDepth k m =
        PeriodicLattice.levelDepth k (m + 1) + ((1 : ℕ) : ℤ) :=
      levelDepth_eq_add rfl
    simp only [mem_iUnion, exists_prop]
    exact mem_refinedBlock_succ e y hsum z
  have hdis : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k m) y).PairwiseDisjoint
      (baseVerticesOfCube L n k m) := by
    intro x _ x' _ hne
    have hd := (hP L n hLs hn (PeriodicLattice.levelDepth k m) m 0
      (neg_le_levelDepth (by omega))).2.1.2.2.1 hne
    exact Set.disjoint_left.2 fun z hz hz' => Set.disjoint_left.1 hd hz hz'
  rw [hU, finsum_mem_biUnion hdis hI fun x _ => finite_baseVerticesOfCube hP hLs hn (by omega) x]
private theorem setAverage_succ (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {m : ℕ} (hm : m + 1 ≤ k)
    (y : Vertex L n k (m + 1)) (f : Vertex L n k 0 → Matrices.ComplexMatrix2) :
    PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k m) y,
          setAverage (baseVerticesOfCube L n k m x) f =
      setAverage (baseVerticesOfCube L n k (m + 1) y) f := by
  have hL : (L : ℂ) ≠ 0 := by
    have : L ≠ 0 := by have := hLs.2; omega
    exact_mod_cast this
  have hI : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k m) y).Finite := by
    have hL0 : 0 < L := by have := hLs.2; omega
    have hfinB : (PeriodicLattice.unitBlock y).Finite := by
      apply Set.finite_of_ncard_pos
      rw [((hP L n hLs hn (PeriodicLattice.levelDepth k (m + 1)) 1 0
        (neg_le_levelDepth hm)).1 y).2.2]
      exact pow_pos hL0 _
    exact hfinB.preimage Subtype.val_injective.injOn
  have hc : ∀ x : Vertex L n k m, setAverage (baseVerticesOfCube L n k m x) f =
      ((L : ℂ) ^ (4 * m))⁻¹ • ∑ᶠ z ∈ baseVerticesOfCube L n k m x, f z := by
    intro x
    rw [setAverage, ncard_baseVerticesOfCube hP hLs hn (by omega) x]
    push_cast
    rfl
  simp only [hc]
  rw [← smul_finsum_mem hI, smul_smul, setAverage, ncard_baseVerticesOfCube hP hLs hn hm y,
    finsum_baseVerticesOfCube_succ hP hLs hn hm y f]
  congr 1
  have hw : PeriodicLattice.inverseFourthPowerWeight L = ((L : ℂ) ^ 4)⁻¹ := by
    simp only [PeriodicLattice.inverseFourthPowerWeight, zpow_neg]
    push_cast
    simp
  rw [hw, ← mul_inv, ← pow_add, show 4 * (m + 1) = 4 + 4 * m by ring]
  push_cast
  rfl
private theorem setAverage_zero (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (y : Vertex L n k 0)
    (f : Vertex L n k 0 → Matrices.ComplexMatrix2) :
    setAverage (baseVerticesOfCube L n k 0 y) f = f y := by
  have h1 := ncard_baseVerticesOfCube hP hLs hn (Nat.zero_le k) y
  have hy : y ∈ baseVerticesOfCube L n k 0 y :=
    (hP L n hLs hn (PeriodicLattice.levelDepth k 0) 0 0
      (neg_le_levelDepth (Nat.zero_le k))).2.1.1 y
  have h1' : (baseVerticesOfCube L n k 0 y).ncard = 1 := by rw [h1]; simp
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1'
  have hS : baseVerticesOfCube L n k 0 y = {y} := by
    rw [ha] at hy ⊢
    rw [Set.mem_singleton_iff.1 hy]
  rw [setAverage, hS, Set.ncard_singleton, finsum_mem_singleton]
  simp
private theorem edgeFormPathSum_eq_setAverage (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {m : ℕ} (hm : m + 1 ≤ k)
    (B : Edge L n k 0 → Matrices.ComplexMatrix2) (Q : Edge L n k m → Matrices.ComplexMatrix2)
    (ih : ∀ c' : Edge L n k m, Q c' = setAverage (baseVerticesOfCube L n k m c'.source)
      fun z => edgeFormPathSum B (PeriodicLattice.crossingPath c' z))
    (c : Edge L n k (m + 1))
    (gX : Vertex L n k m → Edge L n k m) (dX : Vertex L n k m)
    (gY : Vertex L n k 0 → Edge L n k 0) (dY : Vertex L n k 0)
    (h1 : ∀ x : Vertex L n k m, PeriodicLattice.crossingPath c x = stepValues gX dX x L)
    (h2 : ∀ z : Vertex L n k 0,
      PeriodicLattice.crossingPath c z = stepValues gY dY z (L * L ^ m))
    (h3 : ∀ (x : Vertex L n k m) (z : Vertex L n k 0),
      PeriodicLattice.crossingPath (gX x) z = stepValues gY dY z (L ^ m))
    (h4 : ∀ x, (gX x).source = x)
    (h5 : (((L ^ m) • dY : Vertex L n k 0) : PeriodicLattice.FourTorus L n) = dX)
    (x : Vertex L n k m) :
    edgeFormPathSum Q (PeriodicLattice.crossingPath c x) =
      setAverage (baseVerticesOfCube L n k m x)
        fun z => edgeFormPathSum B (PeriodicLattice.crossingPath c z) := by
  have hm' : m ≤ k := by omega
  have hw := sum_stepValues_average gX dX gY dY Q B (baseVerticesOfCube L n k m)
    (((L ^ (4 * m) : ℕ) : ℂ)⁻¹) (L ^ m) (fun x => finite_baseVerticesOfCube hP hLs hn hm' x)
    (fun x => baseVerticesOfCube_add x dX _ h5)
    (fun x => by
      rw [ih (gX x), h4, setAverage, ncard_baseVerticesOfCube hP hLs hn hm' x]
      congr 1
      exact finsum_mem_congr rfl fun z _ => by
        show ((PeriodicLattice.crossingPath (gX x) z).map B).sum = _
        rw [h3]) L x
  rw [setAverage, ncard_baseVerticesOfCube hP hLs hn hm' x]
  show ((PeriodicLattice.crossingPath c x).map Q).sum = _
  rw [h1, hw]
  congr 1
  exact finsum_mem_congr rfl fun z _ => by
    show _ = ((PeriodicLattice.crossingPath c z).map B).sum
    rw [h2]
private theorem crossingSmoothingIter_eq_setAverage (hS : PeriodicLattice.AxialPathUniqueness)
    (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (B : Edge L n k 0 → Matrices.ComplexMatrix2) (m : ℕ) :
    m ≤ k → ∀ c : Edge L n k m, crossingSmoothingIter L n k m B c =
      setAverage (baseVerticesOfCube L n k m c.source)
        fun z => edgeFormPathSum B (PeriodicLattice.crossingPath c z) := by
  have hL : 0 < L := by have := hLs.2; omega
  induction m with
  | zero =>
    intro hm c
    rw [setAverage_zero hP hLs hn]
    show B c = _
    obtain ⟨μ, h | h⟩ := c.isNeighbour
    · rw [crossingPath_of_forward hS hLs hn (i := 0) (r := 0) (by omega) (Nat.zero_le k) c μ h]
      have e : PeriodicLattice.Bond.forwardFrom c.source μ = c :=
        PeriodicLattice.Bond.ext rfl (by
          show c.source + PeriodicLattice.unitStep L n _ μ = c.target
          rw [← h]
          abel)
      simp [stepValues, edgeFormPathSum, PeriodicLattice.bondFormSumAlong, e]
    · rw [crossingPath_of_backward hS hLs hn (i := 0) (r := 0) (by omega) (Nat.zero_le k) c μ h]
      have e : PeriodicLattice.Bond.backwardFrom c.source μ = c :=
        PeriodicLattice.Bond.ext rfl (by
          show c.source - PeriodicLattice.unitStep L n _ μ = c.target
          rw [sub_eq_add_neg, ← h]
          abel)
      simp [stepValues, edgeFormPathSum, PeriodicLattice.bondFormSumAlong, e]
  | succ m ih =>
    intro hm c
    have hm' : m ≤ k := by omega
    have hstep : ∀ x : Vertex L n k m,
        edgeFormPathSum (crossingSmoothingIter L n k m B) (PeriodicLattice.crossingPath c x) =
          setAverage (baseVerticesOfCube L n k m x)
            fun z => edgeFormPathSum B (PeriodicLattice.crossingPath c z) := by
      obtain ⟨μ, h | h⟩ := c.isNeighbour
      · refine edgeFormPathSum_eq_setAverage hP hLs hn hm B _ (ih hm') c
          (fun y => PeriodicLattice.Bond.forwardFrom y μ) (PeriodicLattice.unitStep L n _ μ)
          (fun y => PeriodicLattice.Bond.forwardFrom y μ) (PeriodicLattice.unitStep L n _ μ)
          (fun x => ?_) (fun z => ?_) (fun x z => ?_) (fun x => rfl) ?_
        · rw [crossingPath_of_forward hS hLs hn (i := m) (r := 1) rfl hm c μ h, pow_one]
        · rw [crossingPath_of_forward hS hLs hn (i := 0) (r := m + 1) (by omega) hm c μ h,
            pow_succ']
        · exact crossingPath_of_forward hS hLs hn (i := 0) (r := m) (by omega) hm'
            (PeriodicLattice.Bond.forwardFrom x μ) μ
            (by simp [PeriodicLattice.Bond.forwardFrom]) z
        · exact coe_pow_nsmul_unitStep hL m (levelDepth_add_self m).symm μ
      · refine edgeFormPathSum_eq_setAverage hP hLs hn hm B _ (ih hm') c
          (fun y => PeriodicLattice.Bond.backwardFrom y μ) (-PeriodicLattice.unitStep L n _ μ)
          (fun y => PeriodicLattice.Bond.backwardFrom y μ) (-PeriodicLattice.unitStep L n _ μ)
          (fun x => ?_) (fun z => ?_) (fun x z => ?_) (fun x => rfl) ?_
        · rw [crossingPath_of_backward hS hLs hn (i := m) (r := 1) rfl hm c μ h, pow_one]
        · rw [crossingPath_of_backward hS hLs hn (i := 0) (r := m + 1) (by omega) hm c μ h,
            pow_succ']
        · exact crossingPath_of_backward hS hLs hn (i := 0) (r := m) (by omega) hm'
            (PeriodicLattice.Bond.backwardFrom x μ) μ
            (by simp [PeriodicLattice.Bond.backwardFrom, sub_eq_add_neg]) z
        · rw [smul_neg, AddSubgroup.coe_neg, AddSubgroup.coe_neg]
          exact congrArg Neg.neg (coe_pow_nsmul_unitStep hL m (levelDepth_add_self m).symm μ)
    show crossingSmoothing L n k m (crossingSmoothingIter L n k m B) c = _
    rw [← setAverage_succ hP hLs hn hm c.source]
    simp only [crossingSmoothing]
    congr 1
    exact finsum_mem_congr rfl fun x _ => hstep x
private theorem vertexSmoothingIter_eq_setAverage (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (l : Vertex L n k 0 → Matrices.ComplexMatrix2) (m : ℕ) :
    m ≤ k → ∀ y : Vertex L n k m, vertexSmoothingIter L n k m l y =
      setAverage (baseVerticesOfCube L n k m y) l := by
  induction m with
  | zero =>
    intro _ y
    rw [setAverage_zero hP hLs hn]
    rfl
  | succ m ih =>
    intro hm y
    show vertexSmoothing L n k m (vertexSmoothingIter L n k m l) y = _
    rw [← setAverage_succ hP hLs hn hm y]
    simp only [vertexSmoothing]
    congr 1
    exact finsum_mem_congr rfl fun x _ => ih (by omega) x
end CubeAverages
open CubeAverages in
theorem iteratesAsCubeAverages_of_blockPartition
    (h₁ : PeriodicLattice.BlockPartition.Properties)
    (h₂ : PeriodicLattice.AxialPathUniqueness) : IteratesAsCubeAverages := by
  intro L hLs n k m hn hm
  exact ⟨fun B _ c => crossingSmoothingIter_eq_setAverage h₂ h₁ hLs hn B m hm c,
    fun l _ y => vertexSmoothingIter_eq_setAverage h₁ hLs hn l m hm y⟩
end YangMills.Construction.Tower
end

import YangMills.Construction.Towers.IteratesOfTheLinearMapsAsMeansOverBlocksProof
import YangMills.Construction.Towers.ProductsOfTheAveragesAsMeansOnASide
import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOfTheLinearMapsProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.PeriodicLattice (FourTorus refinedBlock crossingPath sitesIn)
open YangMills.Construction.Matrices (ComplexMatrix2)
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.IteratedSmoothingMeans
private def stepSeq {X Y : Type*} [Add X] (g : X → Y) (d : X) : X → ℕ → List Y
  | _, 0 => []
  | x, N + 1 => g x :: stepSeq g d (x + d) N
private theorem stepSeq_length {X Y : Type*} [Add X] (g : X → Y) (d : X) (N : ℕ) :
    ∀ x, (stepSeq g d x N).length = N := by
  induction N with
  | zero => intro x; rfl
  | succ N ih => intro x; simp [stepSeq, ih]
private theorem stepSeq_add {X Y : Type*} [AddCommGroup X] (g : X → Y) (d : X) (a b : ℕ) :
    ∀ x, stepSeq g d x (a + b) = stepSeq g d x a ++ stepSeq g d (x + a • d) b := by
  induction a with
  | zero => intro x; simp [stepSeq]
  | succ a ih =>
    intro x
    have e : x + d + a • d = x + (a + 1) • d := by rw [add_nsmul, one_nsmul]; abel
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [stepSeq, ih, List.cons_append, e]
private theorem stepSeq_sum_mean {X Y P R : Type*} [AddCommGroup X] [AddCommGroup Y]
    (gX : X → P) (dX : X) (gY : Y → R) (dY : Y) (Q : P → ComplexMatrix2) (B : R → ComplexMatrix2)
    (S : X → Set Y) (w : ℂ) (M : ℕ) (hfin : ∀ x, (S x).Finite)
    (hS : ∀ x, S (x + dX) = (fun z => z + M • dY) '' S x)
    (hQ : ∀ x, Q (gX x) = w • ∑ᶠ z ∈ S x, ((stepSeq gY dY z M).map B).sum) (N : ℕ) :
    ∀ x, ((stepSeq gX dX x N).map Q).sum =
      w • ∑ᶠ z ∈ S x, ((stepSeq gY dY z (N * M)).map B).sum := by
  induction N with
  | zero => intro x; simp [stepSeq]
  | succ N ih =>
    intro x
    have hinj : Function.Injective (fun z : Y => z + M • dY) := add_left_injective _
    have hshift : ∑ᶠ z ∈ S (x + dX), ((stepSeq gY dY z (N * M)).map B).sum =
        ∑ᶠ z ∈ S x, ((stepSeq gY dY (z + M • dY) (N * M)).map B).sum := by
      rw [hS, finsum_mem_image hinj.injOn]
    simp only [stepSeq, List.map_cons, List.sum_cons]
    rw [hQ, ih, hshift, ← smul_add, ← finsum_mem_add_distrib (hfin x)]
    congr 1
    refine finsum_mem_congr rfl fun z _ => ?_
    rw [show (N + 1) * M = M + N * M by ring, stepSeq_add, List.map_append, List.sum_append]
variable {L n k : ℕ}
private theorem coe_pow_nsmul_unitStep (hL : 0 < L) {j j' : ℤ} (r : ℕ) (e : j' = j + r) (μ : Fin 4) :
    (((L ^ r) • PeriodicLattice.unitStep L n j' μ : PeriodicLattice.Site L n j') :
        FourTorus L n) =
      (PeriodicLattice.unitStep L n j μ : PeriodicLattice.Site L n j) := by apply _root_.YangMills.SharedProofs.p1497 <;> assumption
private theorem crossingPath_eq_axialPath
    (hS : PeriodicLattice.AxialPathUniqueness)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j j' : ℤ} (hjj : j ≤ j')
    (hj : -(n : ℤ) ≤ j') (c : PeriodicLattice.Bond L n j) (x : PeriodicLattice.Site L n j')
    (μ : Fin 4) (t : ℤ) (hlen : ((|t| : ℤ) : ℝ) < (L : ℝ) ^ ((n : ℤ) + j'))
    (hd : ((c.target - c.source : PeriodicLattice.Site L n j) : FourTorus L n) =
      ((t • PeriodicLattice.unitStep L n j' μ : PeriodicLattice.Site L n j') : FourTorus L n)) :
    crossingPath c x = PeriodicLattice.flowAlong x μ t := by apply _root_.YangMills.SharedProofs.p1693 <;> assumption
private theorem levelDepth_add {a i r : ℕ} (h : a = i + r) :
    PeriodicLattice.levelDepth k i = PeriodicLattice.levelDepth k a + (r : ℤ) := by apply _root_.YangMills.SharedProofs.p67689 <;> assumption
private theorem neg_le_levelDepth {a : ℕ} (ha : a ≤ k) : -(n : ℤ) ≤ PeriodicLattice.levelDepth k a := by
  simp only [PeriodicLattice.levelDepth]
  omega
private theorem pow_lt_zpow_levelDepth (hL : 13 ≤ L) (hn : 0 < n) {i r : ℕ} (h : i + r ≤ k) :
    ((L ^ r : ℕ) : ℝ) < (L : ℝ) ^ ((n : ℤ) + PeriodicLattice.levelDepth k i) := by
  have h1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have e : (n : ℤ) + PeriodicLattice.levelDepth k i = ((n + k - i : ℕ) : ℤ) := by
    simp only [PeriodicLattice.levelDepth]
    omega
  rw [e, zpow_natCast]
  push_cast
  exact pow_lt_pow_right₀ h1 (by omega)
private theorem forwardFlow_eq_stepSeq {j : ℤ} (μ : Fin 4) (N : ℕ) :
    ∀ x : PeriodicLattice.Site L n j, PeriodicLattice.forwardAxisPath x μ N =
      stepSeq (fun y => PeriodicLattice.Bond.forwardFrom y μ) (PeriodicLattice.unitStep L n j μ) x N := by
  induction N with
  | zero => intro x; rfl
  | succ N ih => intro x; simp only [PeriodicLattice.forwardAxisPath, stepSeq, ih]
private theorem backwardFlow_eq_stepSeq {j : ℤ} (μ : Fin 4) (N : ℕ) :
    ∀ x : PeriodicLattice.Site L n j, PeriodicLattice.backwardAxisPath x μ N =
      stepSeq (fun y => PeriodicLattice.Bond.backwardFrom y μ) (-PeriodicLattice.unitStep L n j μ) x N := by
  induction N with
  | zero => intro x; rfl
  | succ N ih => intro x; simp only [PeriodicLattice.backwardAxisPath, stepSeq, ih, sub_eq_add_neg]
private theorem crossingPath_eq_forward
    (hS : PeriodicLattice.AxialPathUniqueness)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {a i r : ℕ} (h : a = i + r) (ha : a ≤ k)
    (c : Edge L n k a) (μ : Fin 4)
    (hc : c.target - c.source = PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k a) μ)
    (x : Vertex L n k i) :
    crossingPath c x =
      stepSeq (fun y => PeriodicLattice.Bond.forwardFrom y μ)
        (PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ) x (L ^ r) := by
  have hL : 0 < L := by have := hLs.2; omega
  have e := levelDepth_add (k := k) h
  have hjj : PeriodicLattice.levelDepth k a ≤ PeriodicLattice.levelDepth k i := by omega
  rw [crossingPath_eq_axialPath hS hLs hn hjj (neg_le_levelDepth (by omega)) c x μ ((L ^ r : ℕ) : ℤ)
    (by
      have := pow_lt_zpow_levelDepth (k := k) hLs.2 hn (i := i) (r := r) (by omega)
      simpa using this)
    (by rw [hc, natCast_zsmul]; exact (coe_pow_nsmul_unitStep hL r e μ).symm)]
  rw [PeriodicLattice.flowAlong, if_pos (by positivity), Int.toNat_natCast, forwardFlow_eq_stepSeq]
private theorem crossingPath_eq_backward
    (hS : PeriodicLattice.AxialPathUniqueness)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {a i r : ℕ} (h : a = i + r) (ha : a ≤ k)
    (c : Edge L n k a) (μ : Fin 4)
    (hc : c.target - c.source = -PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k a) μ)
    (x : Vertex L n k i) :
    crossingPath c x =
      stepSeq (fun y => PeriodicLattice.Bond.backwardFrom y μ)
        (-PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ) x (L ^ r) := by
  have hL : 0 < L := by have := hLs.2; omega
  have e := levelDepth_add (k := k) h
  have hjj : PeriodicLattice.levelDepth k a ≤ PeriodicLattice.levelDepth k i := by omega
  rw [crossingPath_eq_axialPath hS hLs hn hjj (neg_le_levelDepth (by omega)) c x μ (-((L ^ r : ℕ) : ℤ))
    (by
      have := pow_lt_zpow_levelDepth (k := k) hLs.2 hn (i := i) (r := r) (by omega)
      simpa using this)
    (by
      rw [hc, neg_smul, natCast_zsmul, AddSubgroup.coe_neg, AddSubgroup.coe_neg]
      exact congrArg Neg.neg (coe_pow_nsmul_unitStep hL r e μ).symm)]
  have hpos : 0 < ((L ^ r : ℕ) : ℤ) := by exact_mod_cast pow_pos hL r
  rw [PeriodicLattice.flowAlong, if_neg (by omega), neg_neg, Int.toNat_natCast,
    backwardFlow_eq_stepSeq]
private theorem crossingPath_length_eq
    (hS : PeriodicLattice.AxialPathUniqueness)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {a i r : ℕ} (h : a = i + r) (ha : a ≤ k)
    (c : Edge L n k a) (x : Vertex L n k i) : (crossingPath c x).length = L ^ r := by
  obtain ⟨μ, hc | hc⟩ := c.isNeighbour
  · rw [crossingPath_eq_forward hS hLs hn h ha c μ hc, stepSeq_length]
  · rw [crossingPath_eq_backward hS hLs hn h ha c μ hc, stepSeq_length]
private abbrev blockVertices (i r : ℕ) (y : Vertex L n k (i + r)) : Set (Vertex L n k i) :=
  sitesIn (refinedBlock r y)
private theorem levelDepth_add_self (i r : ℕ) :
    PeriodicLattice.levelDepth k (i + r) + (r : ℤ) = PeriodicLattice.levelDepth k i :=
  (levelDepth_add rfl).symm
private theorem mem_blockVertices {i r : ℕ} (y : Vertex L n k (i + r)) (z : Vertex L n k i) :
    z ∈ blockVertices i r y ↔ (z : FourTorus L n) ∈ PeriodicLattice.cubeAround y := by
  show (z : FourTorus L n) ∈ refinedBlock r y ↔ _
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [levelDepth_add_self]
  exact z.2
private theorem image_blockVertices {i r : ℕ} (y : Vertex L n k (i + r)) :
    (fun z : Vertex L n k i => (z : FourTorus L n)) '' blockVertices i r y = refinedBlock r y := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hp
    have hl : p ∈ PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) := by
      rw [← levelDepth_add_self i r]
      exact hp.2
    exact ⟨⟨p, hl⟩, hp, rfl⟩
private theorem ncard_blockVertices (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {i r : ℕ} (hm : i + r ≤ k)
    (y : Vertex L n k (i + r)) : (blockVertices i r y).ncard = L ^ (4 * r) := by
  have h := ((hP L n hLs hn (PeriodicLattice.levelDepth k (i + r)) r 0 (neg_le_levelDepth hm)).1 y).2.2
  rw [← image_blockVertices, Set.ncard_image_of_injective _ Subtype.val_injective] at h
  exact h
private theorem finite_blockVertices (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {i r : ℕ} (hm : i + r ≤ k)
    (y : Vertex L n k (i + r)) : (blockVertices i r y).Finite := by
  have hL : 0 < L := by have := hLs.2; omega
  apply Set.finite_of_ncard_pos
  rw [ncard_blockVertices hP hLs hn hm]
  exact pow_pos hL _
private theorem blockVertices_add {i r : ℕ} (x t : Vertex L n k (i + r)) (t' : Vertex L n k i)
    (ht : (t' : FourTorus L n) = t) :
    blockVertices i r (x + t) = (fun z => z + t') '' blockVertices i r x := by
  have key : ∀ z : Vertex L n k i, z - t' ∈ blockVertices i r x ↔ z ∈ blockVertices i r (x + t) := by
    intro z
    rw [mem_blockVertices, mem_blockVertices]
    have e : (((z - t' : Vertex L n k i) : FourTorus L n) - (x : FourTorus L n)) =
        (z : FourTorus L n) - ((x + t : Vertex L n k (i + r)) : FourTorus L n) := by
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
    (p : FourTorus L n) :
    p ∈ refinedBlock (m + 1) y ↔
      ∃ x : PeriodicLattice.Site L n j', (x : FourTorus L n) ∈ PeriodicLattice.unitBlock y ∧
        p ∈ refinedBlock m x := by
  subst e
  rw [Nat.add_comm m 1, show refinedBlock (1 + m) y = _ from h]
  simp only [mem_iUnion, exists_prop]
private theorem finite_sitesInBlock (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {a : ℕ} (ha : a + 1 ≤ k)
    (y : Vertex L n k (a + 1)) : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k a) y).Finite := by
  have hfinB : (PeriodicLattice.unitBlock y).Finite := by
    have hL : 0 < L := by have := hLs.2; omega
    apply Set.finite_of_ncard_pos
    rw [((hP L n hLs hn (PeriodicLattice.levelDepth k (a + 1)) 1 0 (neg_le_levelDepth ha)).1 y).2.2]
    exact pow_pos hL _
  exact hfinB.preimage Subtype.val_injective.injOn
private theorem finsum_blockVertices_succ (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {i r : ℕ} (hm : i + r + 1 ≤ k)
    (y : Vertex L n k (i + r + 1)) (f : Vertex L n k i → ComplexMatrix2) :
    ∑ᶠ z ∈ blockVertices i (r + 1) y, f z =
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k (i + r)) y,
        ∑ᶠ z ∈ blockVertices i r x, f z := by
  have hI := finite_sitesInBlock hP hLs hn hm y
  have hU : blockVertices i (r + 1) y =
      ⋃ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k (i + r)) y, blockVertices i r x := by
    ext z
    have hsum := (hP L n hLs hn (PeriodicLattice.levelDepth k (i + r + 1)) 1 r (neg_le_levelDepth hm)).2.2.1 y
    have e : PeriodicLattice.levelDepth k (i + r) = PeriodicLattice.levelDepth k (i + r + 1) + ((1 : ℕ) : ℤ) :=
      levelDepth_add rfl
    simp only [mem_iUnion, exists_prop]
    exact mem_refinedBlock_succ e y hsum z
  have hdis : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k (i + r)) y).PairwiseDisjoint
      (blockVertices i r) := by
    intro x _ x' _ hne
    have hd := (hP L n hLs hn (PeriodicLattice.levelDepth k (i + r)) r 0
      (neg_le_levelDepth (by omega))).2.1.2.2.1 hne
    exact Set.disjoint_left.2 fun z hz hz' => Set.disjoint_left.1 hd hz hz'
  rw [hU, finsum_mem_biUnion hdis hI fun x _ => finite_blockVertices hP hLs hn (by omega) x]
private theorem blockMean_succ (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {i r : ℕ} (hm : i + r + 1 ≤ k)
    (y : Vertex L n k (i + r + 1)) (f : Vertex L n k i → ComplexMatrix2) :
    PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k (i + r)) y,
        ((L : ℂ) ^ (4 * r))⁻¹ • ∑ᶠ z ∈ blockVertices i r x, f z =
      ((L : ℂ) ^ (4 * (r + 1)))⁻¹ • ∑ᶠ z ∈ blockVertices i (r + 1) y, f z := by
  have hI := finite_sitesInBlock hP hLs hn hm y
  rw [← smul_finsum_mem hI, smul_smul, finsum_blockVertices_succ hP hLs hn hm y f]
  congr 1
  have hw : PeriodicLattice.inverseFourthPowerWeight L = ((L : ℂ) ^ 4)⁻¹ := by
    simp only [PeriodicLattice.inverseFourthPowerWeight, zpow_neg]
    push_cast
    simp
  rw [hw, ← mul_inv, ← pow_add, show 4 * (r + 1) = 4 + 4 * r by ring]
private theorem blockVertices_zero (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {i : ℕ} (hi : i ≤ k) (y : Vertex L n k i) :
    blockVertices i 0 y = {y} := by
  have h1 := ncard_blockVertices hP hLs hn (i := i) (r := 0) hi y
  have hy : y ∈ blockVertices i 0 y :=
    (hP L n hLs hn (PeriodicLattice.levelDepth k i) 0 0 (neg_le_levelDepth hi)).2.1.1 y
  have h1' : (blockVertices i 0 y).ncard = 1 := by rw [h1]; simp
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1'
  rw [ha] at hy ⊢
  rw [Set.mem_singleton_iff.1 hy]
private theorem edgeFormPathSum_eq_mean (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {i r : ℕ} (hm : i + r + 1 ≤ k)
    (B : Edge L n k i → ComplexMatrix2) (Q : Edge L n k (i + r) → ComplexMatrix2)
    (ih : ∀ c' : Edge L n k (i + r), Q c' = ((L : ℂ) ^ (4 * r))⁻¹ •
      ∑ᶠ z ∈ blockVertices i r c'.source, edgeFormPathSum B (crossingPath c' z))
    (c : Edge L n k (i + r + 1))
    (gX : Vertex L n k (i + r) → Edge L n k (i + r)) (dX : Vertex L n k (i + r))
    (gY : Vertex L n k i → Edge L n k i) (dY : Vertex L n k i)
    (h1 : ∀ x : Vertex L n k (i + r), crossingPath c x = stepSeq gX dX x L)
    (h2 : ∀ z : Vertex L n k i, crossingPath c z = stepSeq gY dY z (L * L ^ r))
    (h3 : ∀ (x : Vertex L n k (i + r)) (z : Vertex L n k i),
      crossingPath (gX x) z = stepSeq gY dY z (L ^ r))
    (h4 : ∀ x, (gX x).source = x)
    (h5 : (((L ^ r) • dY : Vertex L n k i) : FourTorus L n) = dX)
    (x : Vertex L n k (i + r)) :
    edgeFormPathSum Q (crossingPath c x) = ((L : ℂ) ^ (4 * r))⁻¹ •
      ∑ᶠ z ∈ blockVertices i r x, edgeFormPathSum B (crossingPath c z) := by
  have hm' : i + r ≤ k := by omega
  have hw := stepSeq_sum_mean gX dX gY dY Q B (blockVertices i r)
    (((L : ℂ) ^ (4 * r))⁻¹) (L ^ r) (fun x => finite_blockVertices hP hLs hn hm' x)
    (fun x => blockVertices_add x dX _ h5)
    (fun x => by
      rw [ih (gX x), h4]
      congr 1
      exact finsum_mem_congr rfl fun z _ => by
        show ((crossingPath (gX x) z).map B).sum = _
        rw [h3]) L x
  show ((crossingPath c x).map Q).sum = _
  rw [h1, hw]
  congr 1
  exact finsum_mem_congr rfl fun z _ => by
    show _ = ((crossingPath c z).map B).sum
    rw [h2]
private theorem apply_eq_edgeFormPathSum (hS : PeriodicLattice.AxialPathUniqueness)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {i : ℕ} (hi : i ≤ k)
    (B : Edge L n k i → ComplexMatrix2) (c : Edge L n k i) : B c = edgeFormPathSum B (crossingPath c c.source) := by
  obtain ⟨μ, h | h⟩ := c.isNeighbour
  · rw [crossingPath_eq_forward hS hLs hn (i := i) (r := 0) rfl hi c μ h]
    have e : PeriodicLattice.Bond.forwardFrom c.source μ = c :=
      PeriodicLattice.Bond.ext rfl (by
        show c.source + PeriodicLattice.unitStep L n _ μ = c.target
        rw [← h]
        abel)
    simp [stepSeq, edgeFormPathSum, PeriodicLattice.bondFormSumAlong, e]
  · rw [crossingPath_eq_backward hS hLs hn (i := i) (r := 0) rfl hi c μ h]
    have e : PeriodicLattice.Bond.backwardFrom c.source μ = c :=
      PeriodicLattice.Bond.ext rfl (by
        show c.source - PeriodicLattice.unitStep L n _ μ = c.target
        rw [sub_eq_add_neg, ← h]
        abel)
    simp [stepSeq, edgeFormPathSum, PeriodicLattice.bondFormSumAlong, e]
private theorem crossingSmoothing_iterate_mean
    (hS : PeriodicLattice.AxialPathUniqueness)
    (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {i : ℕ}
    (P : ∀ l, i ≤ l → (Edge L n k i → ComplexMatrix2) → Edge L n k l → ComplexMatrix2)
    (h0 : ∀ h, P i h = id)
    (hs : ∀ l (h : i ≤ l) (h' : i ≤ l + 1), P (l + 1) h' = crossingSmoothing L n k l ∘ P l h)
    (B : Edge L n k i → ComplexMatrix2) (r : ℕ) :
    i + r ≤ k → ∀ (h : i ≤ i + r) (c : Edge L n k (i + r)),
      P (i + r) h B c = ((L : ℂ) ^ (4 * r))⁻¹ •
        ∑ᶠ z ∈ blockVertices i r c.source, edgeFormPathSum B (crossingPath c z) := by
  have hL : 0 < L := by have := hLs.2; omega
  induction r with
  | zero =>
    intro hm h c
    have hm' : i ≤ k := hm
    show P i h B c = ((L : ℂ) ^ (4 * 0))⁻¹ •
      ∑ᶠ z ∈ blockVertices i 0 c.source, edgeFormPathSum B (crossingPath c z)
    rw [h0 h, blockVertices_zero hP hLs hn hm', finsum_mem_singleton]
    simp only [mul_zero, pow_zero, inv_one, one_smul, id]
    exact apply_eq_edgeFormPathSum hS hLs hn hm' B c
  | succ r ih =>
    intro hm h c
    have hm1 : i + r + 1 ≤ k := hm
    have hm' : i + r ≤ k := by omega
    have hle : i ≤ i + r := Nat.le_add_right i r
    have hstep : ∀ x : Vertex L n k (i + r),
        edgeFormPathSum (P (i + r) hle B) (crossingPath c x) = ((L : ℂ) ^ (4 * r))⁻¹ •
          ∑ᶠ z ∈ blockVertices i r x, edgeFormPathSum B (crossingPath c z) := by
      obtain ⟨μ, hc | hc⟩ := c.isNeighbour
      · refine edgeFormPathSum_eq_mean hP hLs hn hm1 B _ (ih hm' hle) c
          (fun y => PeriodicLattice.Bond.forwardFrom y μ) (PeriodicLattice.unitStep L n _ μ)
          (fun y => PeriodicLattice.Bond.forwardFrom y μ) (PeriodicLattice.unitStep L n _ μ)
          (fun x => ?_) (fun z => ?_) (fun x z => ?_) (fun x => rfl) ?_
        · rw [crossingPath_eq_forward hS hLs hn (i := i + r) (r := 1) rfl hm1 c μ hc, pow_one]
        · rw [crossingPath_eq_forward hS hLs hn (i := i) (r := r + 1) (by omega) hm1 c μ hc, pow_succ']
        · exact crossingPath_eq_forward hS hLs hn (i := i) (r := r) rfl hm'
            (PeriodicLattice.Bond.forwardFrom x μ) μ (by simp [PeriodicLattice.Bond.forwardFrom]) z
        · exact coe_pow_nsmul_unitStep hL r (levelDepth_add_self i r).symm μ
      · refine edgeFormPathSum_eq_mean hP hLs hn hm1 B _ (ih hm' hle) c
          (fun y => PeriodicLattice.Bond.backwardFrom y μ) (-PeriodicLattice.unitStep L n _ μ)
          (fun y => PeriodicLattice.Bond.backwardFrom y μ) (-PeriodicLattice.unitStep L n _ μ)
          (fun x => ?_) (fun z => ?_) (fun x z => ?_) (fun x => rfl) ?_
        · rw [crossingPath_eq_backward hS hLs hn (i := i + r) (r := 1) rfl hm1 c μ hc, pow_one]
        · rw [crossingPath_eq_backward hS hLs hn (i := i) (r := r + 1) (by omega) hm1 c μ hc, pow_succ']
        · exact crossingPath_eq_backward hS hLs hn (i := i) (r := r) rfl hm'
            (PeriodicLattice.Bond.backwardFrom x μ) μ
            (by simp [PeriodicLattice.Bond.backwardFrom, sub_eq_add_neg]) z
        · rw [smul_neg, AddSubgroup.coe_neg, AddSubgroup.coe_neg]
          exact congrArg Neg.neg (coe_pow_nsmul_unitStep hL r (levelDepth_add_self i r).symm μ)
    show P (i + r + 1) h B c = _
    rw [hs (i + r) hle h]
    refine Eq.trans ?_ (blockMean_succ hP hLs hn hm1 c.source _)
    show crossingSmoothing L n k (i + r) (P (i + r) hle B) c = _
    simp only [crossingSmoothing]
    congr 1
    exact finsum_mem_congr rfl fun x _ => hstep x
private theorem vertexSmoothing_iterate_mean (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {i : ℕ}
    (P : ∀ l, i ≤ l → (Vertex L n k i → ComplexMatrix2) → Vertex L n k l → ComplexMatrix2)
    (h0 : ∀ h, P i h = id)
    (hs : ∀ l (h : i ≤ l) (h' : i ≤ l + 1), P (l + 1) h' = vertexSmoothing L n k l ∘ P l h)
    (f : Vertex L n k i → ComplexMatrix2) (r : ℕ) :
    i + r ≤ k → ∀ (h : i ≤ i + r) (y : Vertex L n k (i + r)),
      P (i + r) h f y = ((L : ℂ) ^ (4 * r))⁻¹ • ∑ᶠ x ∈ blockVertices i r y, f x := by
  induction r with
  | zero =>
    intro hm h y
    have hm' : i ≤ k := hm
    show P i h f y = ((L : ℂ) ^ (4 * 0))⁻¹ • ∑ᶠ x ∈ blockVertices i 0 y, f x
    rw [h0 h, blockVertices_zero hP hLs hn hm', finsum_mem_singleton]
    simp
  | succ r ih =>
    intro hm h y
    have hm1 : i + r + 1 ≤ k := hm
    have hle : i ≤ i + r := Nat.le_add_right i r
    show P (i + r + 1) h f y = _
    rw [hs (i + r) hle h]
    refine Eq.trans ?_ (blockMean_succ hP hLs hn hm1 y f)
    show vertexSmoothing L n k (i + r) (P (i + r) hle f) y = _
    simp only [vertexSmoothing]
    congr 1
    exact finsum_mem_congr rfl fun x _ => ih (by omega) hle x
private theorem ofReal_norm_list_sum_le {β : Type*} (A : β → ComplexMatrix2) (Γ : List β) :
    ENNReal.ofReal ‖(Γ.map A).sum‖ ≤ (Γ.length : ℝ≥0∞) * maxOperatorNorm A := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_norm_list_sum_le_length_mul <;> assumption
private theorem ofReal_norm_mean_le {ι : Type*} {S : Set ι} (hS : S.Finite) {N : ℕ}
    (hN : 0 < N) (hc : S.ncard = N) (f : ι → ComplexMatrix2) (C : ℝ≥0∞)
    (h : ∀ x ∈ S, ENNReal.ofReal ‖f x‖ ≤ C) :
    ENNReal.ofReal ‖((N : ℂ))⁻¹ • ∑ᶠ x ∈ S, f x‖ ≤ C := by
  by_cases hC : C = ⊤
  · simp [hC]
  have hc' : ∀ x ∈ S, ‖f x‖ ≤ C.toReal := fun x hx =>
    (ENNReal.ofReal_le_iff_le_toReal hC).1 (h x hx)
  have hcard : (hS.toFinset.card : ℝ) = N := by
    rw [← Set.ncard_eq_toFinset_card S hS, hc]
  rw [ENNReal.ofReal_le_iff_le_toReal hC, norm_smul, finsum_mem_eq_finite_toFinset_sum f hS]
  have hsum : ‖∑ x ∈ hS.toFinset, f x‖ ≤ N * C.toReal := by
    calc ‖∑ x ∈ hS.toFinset, f x‖ ≤ ∑ x ∈ hS.toFinset, ‖f x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ hS.toFinset, C.toReal :=
          Finset.sum_le_sum fun x hx => hc' x (hS.mem_toFinset.1 hx)
      _ = N * C.toReal := by simp [hcard]
  have hw : ‖((N : ℂ))⁻¹‖ = (N : ℝ)⁻¹ := by simp
  rw [hw]
  calc (N : ℝ)⁻¹ * ‖∑ x ∈ hS.toFinset, f x‖ ≤ (N : ℝ)⁻¹ * (N * C.toReal) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C.toReal := by field_simp
private theorem maxOperatorNorm_le_of_mean
    (hS : PeriodicLattice.AxialPathUniqueness)
    (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {i r : ℕ} (hr : i + r ≤ k)
    (Q : Edge L n k (i + r) → ComplexMatrix2) (B : Edge L n k i → ComplexMatrix2)
    (hQ : ∀ c : Edge L n k (i + r), Q c = ((L : ℂ) ^ (4 * r))⁻¹ •
      ∑ᶠ z ∈ blockVertices i r c.source, edgeFormPathSum B (crossingPath c z)) :
    maxOperatorNorm Q ≤ (L : ℝ≥0∞) ^ r * maxOperatorNorm B := by
  have hL : 0 < L := by have := hLs.2; omega
  refine iSup_le fun c => ?_
  show ENNReal.ofReal ‖Q c‖ ≤ _
  have e : ((L : ℂ) ^ (4 * r))⁻¹ = (((L ^ (4 * r) : ℕ) : ℂ))⁻¹ := by push_cast; rfl
  rw [hQ c, e]
  refine ofReal_norm_mean_le (finite_blockVertices hP hLs hn hr c.source) (pow_pos hL _)
    (ncard_blockVertices hP hLs hn hr c.source) _ _ fun x _ => ?_
  have h := ofReal_norm_list_sum_le B (crossingPath c x)
  rw [crossingPath_length_eq hS hLs hn rfl hr c x, Nat.cast_pow] at h
  exact h
private theorem crossingSmoothing_iterate_mean_of_add
    (hS : PeriodicLattice.AxialPathUniqueness)
    (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {i j r : ℕ} (e : i + r = j) (hj : j ≤ k)
    (P : ∀ l, i ≤ l → (Edge L n k i → ComplexMatrix2) → Edge L n k l → ComplexMatrix2)
    (h0 : ∀ h, P i h = id)
    (hs : ∀ l (h : i ≤ l) (h' : i ≤ l + 1), P (l + 1) h' = crossingSmoothing L n k l ∘ P l h)
    (B : Edge L n k i → ComplexMatrix2) (hij : i ≤ j) (c : Edge L n k j) :
    P j hij B c = ((L : ℂ) ^ (4 * r))⁻¹ •
      ∑ᶠ x ∈ (sitesIn (refinedBlock r c.source) : Set (Vertex L n k i)),
        edgeFormPathSum B (crossingPath c x) := by
  subst e
  exact crossingSmoothing_iterate_mean hS hP hLs hn P h0 hs B r hj hij c
private theorem vertexSmoothing_iterate_mean_of_add (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {i j r : ℕ} (e : i + r = j) (hj : j ≤ k)
    (P : ∀ l, i ≤ l → (Vertex L n k i → ComplexMatrix2) → Vertex L n k l → ComplexMatrix2)
    (h0 : ∀ h, P i h = id)
    (hs : ∀ l (h : i ≤ l) (h' : i ≤ l + 1), P (l + 1) h' = vertexSmoothing L n k l ∘ P l h)
    (f : Vertex L n k i → ComplexMatrix2) (hij : i ≤ j) (y : Vertex L n k j) :
    P j hij f y = ((L : ℂ) ^ (4 * r))⁻¹ •
      ∑ᶠ x ∈ (sitesIn (refinedBlock r y) : Set (Vertex L n k i)), f x := by
  subst e
  exact vertexSmoothing_iterate_mean hP hLs hn P h0 hs f r hj hij y
private theorem maxOperatorNorm_iterate_le_of_add
    (hS : PeriodicLattice.AxialPathUniqueness)
    (hP : PeriodicLattice.BlockPartition.Properties)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {i j r : ℕ} (e : i + r = j) (hj : j ≤ k)
    (P : ∀ l, i ≤ l → (Edge L n k i → ComplexMatrix2) → Edge L n k l → ComplexMatrix2)
    (h0 : ∀ h, P i h = id)
    (hs : ∀ l (h : i ≤ l) (h' : i ≤ l + 1), P (l + 1) h' = crossingSmoothing L n k l ∘ P l h)
    (B : Edge L n k i → ComplexMatrix2) (hij : i ≤ j) :
    maxOperatorNorm (P j hij B) ≤ (L : ℝ≥0∞) ^ r * maxOperatorNorm B := by
  subst e
  exact maxOperatorNorm_le_of_mean hS hP hLs hn hj _ B fun c =>
    crossingSmoothing_iterate_mean hS hP hLs hn P h0 hs B r hj hij c
theorem iteratedMeansStatement_of_blockPartition (h₁ : PeriodicLattice.BlockPartition.Properties)
    (h₂ : PeriodicLattice.AxialPathUniqueness) : IteratedMeansStatement := by
  intro L hLs m k n j hm _ hnj hjk
  have e : j - n + n = j := Nat.sub_add_cancel hnj
  exact {
    vertexSmoothing_iterate_eq := fun P h0 hs f y =>
      vertexSmoothing_iterate_mean_of_add h₁ hLs hm e hjk P h0 hs f _ y
    crossingSmoothing_iterate_eq := fun P h0 hs B c =>
      crossingSmoothing_iterate_mean_of_add h₂ h₁ hLs hm e hjk P h0 hs B _ c
    crossingPath_length := fun c x _ => crossingPath_length_eq h₂ hLs hm e.symm hjk c x
    maxOperatorNorm_iterate_le := fun P h0 hs B =>
      maxOperatorNorm_iterate_le_of_add h₂ h₁ hLs hm e hjk P h0 hs B _ }
end YangMills.Construction.Tower.IteratedSmoothingMeans
end

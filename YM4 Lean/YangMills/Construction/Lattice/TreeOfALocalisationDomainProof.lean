import YangMills.Construction.Graphs.ClosedWalkThroughAllVertices
import YangMills.Construction.Lattice.CosetsCoordinatesAndDistances
import YangMills.Construction.Lattice.CubesVerticesAndEdgesOfThePartition
import YangMills.Construction.Lattice.EdgeGraphsThatAreNotEmpty
import YangMills.Construction.Lattice.SidesOfTheCubesAndTheLinearSize
import YangMills.Construction.Lattice.TreeOfALocalisationDomain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice
namespace TorusBound
namespace LocalisationDomainTree
open TorusBound.Coordinates PartitionCells
variable {D : Setup} {j : ℕ} {hj : j ≤ D.K} {h : D.LevelFits j}
theorem exists_two_endpoints (hL : Coordinates.CosetsAndDistancesStatement) {A : Set D.Torus}
    (hA : D.IsLevelEdge hj h A) :
    ∃ a b, a ≠ b ∧ a ∈ A ∧ b ∈ A ∧
      {x | (D.levelUnitPartition hj h).IsEdgeEndpoint A x} = {a, b} := by
  obtain ⟨hTwo, -, -, -, -, hEdges, -, -, hEnd, -⟩ := hL D j hj h
  obtain ⟨w, ν, hw, rfl⟩ := (hEdges A).1 hA
  obtain ⟨h₁, h₂⟩ := hEnd w ν hw
  exact ⟨_, _, h₂, ⟨w, ⟨0, le_rfl, hTwo.2.1.le, by simp⟩, rfl⟩,
    ⟨_, ⟨_, hTwo.2.1.le, le_rfl, rfl⟩, rfl⟩, h₁⟩
theorem exists_interior_point (hL : Coordinates.CosetsAndDistancesStatement) {A : Set D.Torus}
    (hA : D.IsLevelEdge hj h A) :
    ∃ y ∈ A, ¬(D.levelUnitPartition hj h).IsEdgeEndpoint A y := by
  obtain ⟨hTwo, -, -, -, hVert, hEdges, -, hCoord, -, -⟩ := hL D j hj h
  have hσ := hTwo.2.1
  obtain ⟨w, ν, hw, rfl⟩ := (hEdges A).1 hA
  have hdir : D.IsEdgeAxis hj h ν
      (D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν) := by
    refine ⟨D.torusCover w, w, (hVert _).2 fun μ w' hw' => ?_, rfl, rfl⟩
    exact hTwo.2.2.2.2.2 _ (Or.inr rfl) _ μ w w' rfl hw' (hw μ)
  have hmem : D.torusCover (w + (D.physicalCubeSide j / 2) • coordVec ν) ∈
      D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν :=
    ⟨_, ⟨_, by positivity, by linarith, rfl⟩, rfl⟩
  refine ⟨_, hmem, fun hy => ?_⟩
  have hy' := ((hCoord _ ν hA hdir).2 _ hmem).2 hy
  obtain ⟨b, hb⟩ := hy' _ rfl
  obtain ⟨a, ha⟩ := hw ν
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordVec, Pi.single_eq_same,
    mul_one] at hb
  have h₁ : (a : ℝ) + 1 = (b : ℝ) + 1 / 2 := by
    apply mul_left_cancel₀ hσ.ne'
    rw [ha] at hb
    linarith
  have h₂ : (2 * a + 2 : ℤ) = 2 * b + 1 := by
    have : (2 * (a : ℝ) + 2) = 2 * (b : ℝ) + 1 := by linarith
    exact_mod_cast this
  omega
theorem isLevelVertex_of_isEdgeEndpoint (hL : Coordinates.CosetsAndDistancesStatement)
    {A : Set D.Torus} {x : D.Torus} (hA : D.IsLevelEdge hj h A)
    (hx : (D.levelUnitPartition hj h).IsEdgeEndpoint A x) :
    D.IsLevelVertex hj h x := by
  obtain ⟨-, -, -, -, hVert, -, hDir, hCoord, -, -⟩ := hL D j hj h
  obtain ⟨a, b, -, ha, hb, hset⟩ := exists_two_endpoints hL hA
  have hxA : x ∈ A := by
    have : x ∈ ({a, b} : Set D.Torus) := hset ▸ hx
    rcases this with rfl | rfl
    · exact ha
    · exact hb
  obtain ⟨ν, hν, -⟩ := hDir A hA
  refine (hVert x).2 fun μ => ?_
  by_cases hμ : μ = ν
  · subst hμ
    exact ((hCoord A μ hA hν).2 x hxA).2 hx
  · exact ((hCoord A ν hA hν).1 μ hμ).2 x hxA
theorem treeGraphEdges_sUnion (hL : Coordinates.CosetsAndDistancesStatement)
    (hC : PartitionCells.Holds) {F : Set (Set D.Torus)}
    (hF : ∀ e ∈ F, D.IsLevelEdge hj h e) : D.treeGraphEdges hj h (⋃₀ F) = F := by
  ext A
  simp only [Setup.treeGraphEdges, LevelUnitPartition.graphEdges]
  constructor
  · rintro ⟨hA, hsub⟩
    obtain ⟨y, hy, hyn⟩ := exists_interior_point (hj := hj) (h := h) hL hA
    obtain ⟨e, he, hye⟩ := hsub hy
    by_contra hAF
    have hne : A ≠ e := fun hh => hAF (hh ▸ he)
    exact hyn ((hC D j hj h).2.1 A e hA (hF e he) hne y ⟨hy, hye⟩).1
  · intro hA
    exact ⟨hF A hA, subset_sUnion_of_mem hA⟩
theorem isClosed_of_isLevelEdge (hL : Coordinates.CosetsAndDistancesStatement) {A : Set D.Torus}
    (hA : D.IsLevelEdge hj h A) : IsClosed A := by
  obtain ⟨hTwo, -, -, -, -, hEdges, -⟩ := hL D j hj h
  obtain ⟨w, ν, -, rfl⟩ := (hEdges A).1 hA
  have hseg : IsCompact (Setup.axisSegment w (D.physicalCubeSide j) ν) := by
    have hs : Setup.axisSegment w (D.physicalCubeSide j) ν =
        (fun t : ℝ => w + t • coordVec ν) '' Icc 0 (D.physicalCubeSide j) := by
      ext x
      constructor
      · rintro ⟨t, h₀, h₁, rfl⟩
        exact ⟨t, ⟨h₀, h₁⟩, rfl⟩
      · rintro ⟨t, ⟨h₀, h₁⟩, rfl⟩
        exact ⟨t, h₀, h₁, rfl⟩
    rw [hs]
    exact isCompact_Icc.image (by fun_prop)
  have hcov : Continuous (D.torusCover) :=
    continuous_pi fun μ => (continuous_quotient_mk'.comp (continuous_apply μ))
  have : Fact (0 < PeriodicLattice.torusSide D.L D.m) := ⟨hTwo.2.1.trans hTwo.2.2.1⟩
  exact (hseg.image hcov).isClosed
theorem treeGraphConnected_sUnion (hL : Coordinates.CosetsAndDistancesStatement)
    (hC : PartitionCells.Holds) {F : Set (Set D.Torus)}
    (hF : ∀ e ∈ F, D.IsLevelEdge hj h e) (hfin : F.Finite) (hne : F.Nonempty)
    (hconn : IsConnected (⋃₀ F)) : D.TreeGraphConnected hj h (⋃₀ F) := by
  have hE := treeGraphEdges_sUnion (hj := hj) (h := h) hL hC hF
  have hV : ∀ u ∈ D.treeGraphVertices hj h (⋃₀ F),
      ∃ A ∈ F, (D.levelUnitPartition hj h).IsEdgeEndpoint A u := by
    rintro u (⟨e, he, hu⟩ | ⟨-, hu⟩)
    · exact ⟨e, hE ▸ he, hu⟩
    · exfalso
      obtain ⟨A₀, hA₀⟩ := hne
      obtain ⟨a, b, hab, ha, hb, -⟩ := exists_two_endpoints hL (hF A₀ hA₀)
      have h₁ : a ∈ ⋃₀ F := ⟨A₀, hA₀, ha⟩
      have h₂ : b ∈ ⋃₀ F := ⟨A₀, hA₀, hb⟩
      rw [hu] at h₁ h₂
      exact hab (h₁.trans h₂.symm)
  intro u hu u' hu'
  have hstep : ∀ A ∈ F, ∀ x y, (D.levelUnitPartition hj h).IsEdgeEndpoint A x →
      (D.levelUnitPartition hj h).IsEdgeEndpoint A y →
      Relation.ReflTransGen (D.Adjacent hj h (⋃₀ F)) u x →
      Relation.ReflTransGen (D.Adjacent hj h (⋃₀ F)) u y := by
    intro A hA x y hx hy hux
    by_cases hxy : x = y
    · exact hxy ▸ hux
    obtain ⟨a, b, -, -, -, hset⟩ := exists_two_endpoints hL (hF A hA)
    have hx' : x ∈ ({a, b} : Set D.Torus) := hset ▸ hx
    have hy' : y ∈ ({a, b} : Set D.Torus) := hset ▸ hy
    have hpair : {z | (D.levelUnitPartition hj h).IsEdgeEndpoint A z} = {x, y} := by
      rw [hset]
      rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
      · exact absurd rfl hxy
      · rfl
      · exact pair_comm _ _
      · exact absurd rfl hxy
    exact hux.tail ⟨A, hE.symm ▸ hA, hpair⟩
  classical
  set I : Set (Set D.Torus) := {A | A ∈ F ∧ ∃ x,
    Relation.ReflTransGen (D.Adjacent hj h (⋃₀ F)) u x ∧
      (D.levelUnitPartition hj h).IsEdgeEndpoint A x} with hI
  have hIF : I ⊆ F := fun A hA => hA.1
  have hclosed : ∀ G : Set (Set D.Torus), G ⊆ F → IsClosed (⋃₀ G) := by
    intro G hG
    rw [sUnion_eq_biUnion]
    exact (hfin.subset hG).isClosed_biUnion fun e he => isClosed_of_isLevelEdge hL (hF e (hG he))
  have hall : F \ I = ∅ := by
    by_contra hnon
    obtain ⟨A', hA'⟩ := nonempty_iff_ne_empty.2 hnon
    obtain ⟨A₀, hA₀, hu₀⟩ := hV u hu
    obtain ⟨a', b', -, ha', -, -⟩ := exists_two_endpoints hL (hF A' hA'.1)
    obtain ⟨a₀, b₀, -, ha₀, -, -⟩ := exists_two_endpoints hL (hF A₀ hA₀)
    have hcover : ⋃₀ F ⊆ ⋃₀ I ∪ ⋃₀ (F \ I) := by
      rintro y ⟨e, he, hye⟩
      by_cases heI : e ∈ I
      · exact Or.inl ⟨e, heI, hye⟩
      · exact Or.inr ⟨e, ⟨he, heI⟩, hye⟩
    have hA₀I : A₀ ∈ I := ⟨hA₀, u, Relation.ReflTransGen.refl, hu₀⟩
    obtain ⟨y, -, ⟨e, heI, hye⟩, ⟨e', heI', hye'⟩⟩ :=
      isPreconnected_closed_iff.1 hconn.isPreconnected (⋃₀ I) (⋃₀ (F \ I)) (hclosed _ hIF)
        (hclosed _ sdiff_subset) hcover
        ⟨a₀, ⟨A₀, hA₀, ha₀⟩, ⟨A₀, hA₀I, ha₀⟩⟩ ⟨a', ⟨A', hA'.1, ha'⟩, ⟨A', hA', ha'⟩⟩
    have hne' : e ≠ e' := fun hh => heI'.2 (hh ▸ heI)
    obtain ⟨hy₁, hy₂⟩ := (hC D j hj h).2.1 e e' (hF e heI.1) (hF e' heI'.1) hne' y ⟨hye, hye'⟩
    obtain ⟨heF, x, hux, hx⟩ := heI
    exact heI'.2 ⟨heI'.1, y, hstep e heF x y hx hy₁ hux, hy₂⟩
  obtain ⟨A, hA, hu'A⟩ := hV u' hu'
  have hAI : A ∈ I := by
    by_contra hAI
    have : A ∈ F \ I := ⟨hA, hAI⟩
    rw [hall] at this
    exact this
  obtain ⟨-, x, hux, hx⟩ := hAI
  exact hstep A hA x u' hx hu'A hux
theorem exists_seq_of_reflTransGen {α : Type} {r : α → α → Prop} {x y : α}
    (hxy : Relation.ReflTransGen r x y) :
    ∃ (n : ℕ) (p : ℕ → α), p 0 = x ∧ p n = y ∧ ∀ i < n, r (p i) (p (i + 1)) := by
  induction hxy with
  | refl => exact ⟨0, fun _ => x, rfl, rfl, by simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n, p, h₀, hn, hs⟩ := ih
    refine ⟨n + 1, fun i => if i ≤ n then p i else c, by simpa using h₀, by simp, fun i hi => ?_⟩
    by_cases hin : i < n
    · have h₁ : i ≤ n := hin.le
      have h₂ : i + 1 ≤ n := hin
      simpa [h₁, h₂] using hs i hin
    · have hi' : i = n := by omega
      subst hi'
      simpa [hn] using hbc
def multigraph (hj : j ≤ D.K) (h : D.LevelFits j) (Γ : Set D.Torus) :
    Graph D.Torus (Set D.Torus) where
  vertexSet := D.treeGraphVertices hj h Γ
  IsLink := D.TreeGraphJoins hj h Γ
  isLink_symm := fun _ _ => ⟨fun _ _ hxy => ⟨hxy.1, hxy.2.trans (pair_comm _ _)⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w h₁ h₂
    have h₃ : ({x, y} : Set D.Torus) = {v, w} := h₁.2.symm.trans h₂.2
    have hx : x ∈ ({x, y} : Set D.Torus) := Or.inl rfl
    rw [h₃] at hx
    exact hx
  left_mem_of_isLink := by
    intro e x y h₁
    refine Or.inl ⟨e, h₁.1, ?_⟩
    have hx : x ∈ {z | (D.levelUnitPartition hj h).IsEdgeEndpoint e z} := by
      rw [h₁.2]
      exact Or.inl rfl
    exact hx
theorem torusEuclidNorm_sub_self_nonpos (hL : Coordinates.CosetsAndDistancesStatement)
    (hj : j ≤ D.K) (h : D.LevelFits j) (x : D.Torus) :
    TorusMetric.torusEuclidNorm (x - x) ≤ 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hCov, -⟩ := hL D j hj h
  have h₁ := (hCov (TestFunctions.liftPoint x) (TestFunctions.liftPoint x)).2
  rw [show D.torusCover (TestFunctions.liftPoint x) = x from
    TestFunctions.torusProj_liftPoint x] at h₁
  simpa [TorusMetric.euclidNormVec] using h₁
theorem torusEuclidNorm_walk_le (hL : Coordinates.CosetsAndDistancesStatement)
    (hC : PartitionCells.Holds) {Γ : Set D.Torus} {u : ℕ → D.Torus}
    {N : ℕ} (hu : ∀ t, 1 ≤ t → t ≤ N → D.Adjacent hj h Γ (u (t - 1)) (u t)) (a d : ℕ)
    (had : a + d ≤ N) :
    TorusMetric.torusEuclidNorm (u a - u (a + d)) ≤ (d : ℝ) * D.physicalCubeSide j := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hLaws, -⟩ := hL D j hj h
  induction d with
  | zero => simpa using torusEuclidNorm_sub_self_nonpos hL hj h (u a)
  | succ d ih =>
    have h₁ := ih (by omega)
    obtain ⟨A, hA, hset⟩ := hu (a + d + 1) (by omega) (by omega)
    have hx : (D.levelUnitPartition hj h).IsEdgeEndpoint A (u (a + d + 1 - 1)) := by
      have : u (a + d + 1 - 1) ∈ {z | (D.levelUnitPartition hj h).IsEdgeEndpoint A z} := by
        rw [hset]
        exact Or.inl rfl
      exact this
    have hy : (D.levelUnitPartition hj h).IsEdgeEndpoint A (u (a + d + 1)) := by
      have : u (a + d + 1) ∈ {z | (D.levelUnitPartition hj h).IsEdgeEndpoint A z} := by
        rw [hset]
        exact Or.inr rfl
      exact this
    have h₂ := (hC D j hj h).2.2.2.1.2.2 A hA.1 _ _ hx hy
    simp only [Nat.add_sub_cancel] at h₂
    have h₃ := (hLaws (u a) (u (a + d)) (u (a + d + 1))).2.2.2.1
    rw [← add_assoc]
    push_cast
    linarith
theorem treeGraph_finite_card_dist (hL : Coordinates.CosetsAndDistancesStatement)
    (hC : PartitionCells.Holds)
    (hW : Graphs.ExistsClosedWalkThroughAllVertices) {Γ : Set D.Torus} {E : ℕ}
    (hfin : (D.treeGraphEdges hj h Γ).Finite) (hE : (D.treeGraphEdges hj h Γ).ncard = E)
    (hconn : D.TreeGraphConnected hj h Γ) :
    (D.treeGraphVertices hj h Γ).Finite ∧ (D.treeGraphVertices hj h Γ).encard ≤ (E : ℕ∞) + 1 ∧
      ∀ u ∈ D.treeGraphVertices hj h Γ, ∀ u' ∈ D.treeGraphVertices hj h Γ,
        TorusMetric.torusEuclidNorm (u - u') ≤ (E : ℝ) * D.physicalCubeSide j := by
  obtain ⟨hTwo, -, -, -, -, -, -, -, -, -, -, hLaws, -⟩ := hL D j hj h
  have hσ := hTwo.2.1
  have hedge : (multigraph hj h Γ).edgeSet = D.treeGraphEdges hj h Γ := by
    ext A
    constructor
    · rintro ⟨x, y, hxy⟩
      exact hxy.1
    · intro hA
      obtain ⟨a, b, -, -, -, hset⟩ := exists_two_endpoints (hj := hj) (h := h) hL hA.1
      exact ⟨a, b, hA, hset⟩
  have hVfin : (D.treeGraphVertices hj h Γ).Finite := by
    have hsub : D.treeGraphVertices hj h Γ ⊆
        (⋃ A ∈ D.treeGraphEdges hj h Γ,
          {x | (D.levelUnitPartition hj h).IsEdgeEndpoint A x}) ∪
          {v | D.IsLevelVertex hj h v ∧ Γ = {v}} := by
      rintro v (⟨e, he, hv⟩ | hv)
      · exact Or.inl (mem_biUnion he hv)
      · exact Or.inr hv
    refine Finite.subset (Finite.union (hfin.biUnion fun A hA => ?_) ?_) hsub
    · obtain ⟨a, b, -, -, -, hset⟩ := exists_two_endpoints (hj := hj) (h := h) hL hA.1
      exact (toFinite ({a, b} : Set D.Torus)).subset fun x hx =>
        (hset ▸ hx : x ∈ ({a, b} : Set D.Torus))
    · refine Subsingleton.finite fun x hx y hy => ?_
      have : ({x} : Set D.Torus) = {y} := hx.2.symm.trans hy.2
      exact singleton_injective this
  have hloop : (multigraph hj h Γ).Loopless := by
    refine ⟨fun A x hx => ?_⟩
    obtain ⟨a, b, hab, -, -, hset⟩ := exists_two_endpoints (hj := hj) (h := h) hL hx.1.1
    have h₁ : ({a, b} : Set D.Torus) = {x, x} := hset.symm.trans hx.2
    have ha : a ∈ ({x, x} : Set D.Torus) := h₁ ▸ Or.inl rfl
    have hb : b ∈ ({x, x} : Set D.Torus) := h₁ ▸ Or.inr rfl
    simp only [mem_insert_iff, mem_singleton_iff, or_self] at ha hb
    exact hab (ha.trans hb.symm)
  have hcG : Graphs.MultigraphPathConnected (multigraph hj h Γ) :=
    fun x hx y hy => exists_seq_of_reflTransGen (hconn x hx y hy)
  have hwalk := hW D.Torus (Set D.Torus) (multigraph hj h Γ) hVfin (hedge ▸ hfin) hloop hcG E
    (hedge ▸ hE)
  refine ⟨hVfin, ?_, ?_⟩
  · rcases (D.treeGraphVertices hj h Γ).eq_empty_or_nonempty with h₀ | ⟨r, hr⟩
    · rw [h₀]
      simp
    · have h₁ := (hwalk r hr).1
      rw [← hVfin.cast_ncard_eq]
      exact_mod_cast h₁
  · intro x hx y hy
    obtain ⟨-, w, hw₀, hwN, -, hall, hstep⟩ := hwalk x hx
    obtain ⟨b, hb, rfl⟩ := hall y hy
    have hs : ∀ t, 1 ≤ t → t ≤ 2 * E → D.Adjacent hj h Γ (w (t - 1)) (w t) := hstep
    by_cases hbE : b ≤ E
    · have h₁ := torusEuclidNorm_walk_le hL hC hs 0 b (by omega)
      simp only [zero_add, hw₀] at h₁
      have h₂ : (b : ℝ) ≤ E := by exact_mod_cast hbE
      nlinarith
    · have h₁ := torusEuclidNorm_walk_le hL hC hs b (2 * E - b) (by omega)
      have hbb : b + (2 * E - b) = 2 * E := by omega
      rw [hbb, hwN] at h₁
      have h₂ : ((2 * E - b : ℕ) : ℝ) ≤ E := by
        have : 2 * E - b ≤ E := by omega
        exact_mod_cast this
      have h₃ := (hLaws x (w b) x).1
      have h₄ := (hLaws (w b) x x).2.1
      have h₅ : TorusMetric.torusEuclidNorm (x - w b) =
          TorusMetric.torusEuclidNorm (w b - x) := h₄.symm ▸ rfl
      rw [h₅]
      nlinarith
theorem encard_biUnion_le_mul {α β : Type} {V : Set α} (hV : V.Finite) (K : α → Set β)
    (c : ℕ∞) (hK : ∀ v ∈ V, (K v).encard ≤ c) : (⋃ v ∈ V, K v).encard ≤ c * V.encard := by
  induction V, hV using Set.Finite.induction_on with
  | empty => simp
  | @insert a s ha _ ih =>
    rw [biUnion_insert, encard_insert_of_notMem ha, mul_add, mul_one, add_comm]
    exact (encard_union_le _ _).trans
      (add_le_add (hK a (Or.inl rfl)) (ih fun v hv => hK v (Or.inr hv)))
theorem treeGraph_properties (hL : Coordinates.CosetsAndDistancesStatement)
    (hC : PartitionCells.Holds)
    (hG : PeriodicLattice.EdgeGraphsDescribedByCubes)
    (hW : Graphs.ExistsClosedWalkThroughAllVertices) {d : DomainKind} {X Γ : Set D.Torus}
    {E : ℕ} (hX : X ∈ D.regionsBy d j) (hcube : (partitionCubesIn (D.cubeScaleIndex j) X).Nonempty)
    (ht : IsEdgeTreeWithCount (D.levelUnitPartition hj h) X Γ E)
    (hm : ∀ Q ∈ partitionCubesIn (D.cubeScaleIndex j) X, GraphIntersects Γ Q) :
    D.TreeGraphConnectedBounded hj h Γ E ∧ D.TreeVerticesMeetCubes hj h X Γ E := by
  have hreg : IsPartitionRegion (D.cubeScaleIndex j) X := by
    cases d <;> exact hX.2.1
  obtain ⟨Q₀, hQ₀⟩ := hcube
  have hΓne : Γ.Nonempty := (hm Q₀ hQ₀).mono inter_subset_left
  have hE : (D.treeGraphEdges hj h Γ).ncard = E := ht.2
  have hgraph : (D.levelUnitPartition hj h).IsEdgeGraphInRegion X Γ := ht.1.1
  have hconnΓ : IsConnected Γ := ht.1.2
  have hkey : (D.treeGraphEdges hj h Γ).Finite ∧ D.TreeGraphConnected hj h Γ ∧
      ∀ Q ∈ partitionCubesIn (D.cubeScaleIndex j) X, ∃ v ∈ D.treeGraphVertices hj h Γ, v ∈ Q := by
    rcases ((hG (D.levelUnitPartition hj h) X hreg).1.1 Γ hgraph hΓne) with
      ⟨Δ, hΔ, v, hv, rfl⟩ | ⟨F, hfin, hne, hF, rfl⟩
    · have hno : D.treeGraphEdges hj h {v} = ∅ := by
        refine eq_empty_of_forall_notMem fun A hA => ?_
        obtain ⟨a, b, hab, ha, hb, -⟩ := exists_two_endpoints (hj := hj) (h := h) hL hA.1
        exact hab ((hA.2 ha).trans (hA.2 hb).symm)
      have hvV : v ∈ D.treeGraphVertices hj h {v} := Or.inr ⟨⟨Δ, hΔ.1, hv⟩, rfl⟩
      have hV : ∀ u ∈ D.treeGraphVertices hj h {v}, u = v := by
        rintro u (⟨e, he, -⟩ | ⟨-, hu⟩)
        · have he' : e ∈ D.treeGraphEdges hj h {v} := he
          rw [hno] at he'
          exact absurd he' (notMem_empty e)
        · exact (singleton_injective hu).symm
      refine ⟨hno ▸ finite_empty, fun u hu u' hu' => ?_, fun Q hQ => ?_⟩
      · rw [hV u hu, hV u' hu']
        exact Relation.ReflTransGen.refl
      · obtain ⟨y, hy, hyQ⟩ := hm Q hQ
        exact ⟨v, hvV, (show y = v from hy) ▸ hyQ⟩
    · have hFe : ∀ e ∈ F, D.IsLevelEdge hj h e := fun e he => by
        obtain ⟨Δ, hΔ, hΔe⟩ := hF e he
        exact ⟨Δ, hΔ.1, hΔe⟩
      have hEq := treeGraphEdges_sUnion (hj := hj) (h := h) hL hC hFe
      refine ⟨hEq.symm ▸ hfin, treeGraphConnected_sUnion hL hC hFe hfin hne hconnΓ,
        fun Q hQ => ?_⟩
      obtain ⟨y, ⟨e, he, hye⟩, hyQ⟩ := hm Q hQ
      obtain ⟨z, hzQ, hz⟩ := (hC D j hj h).2.2.1 Q e hQ.1 (hFe e he) ⟨y, hyQ, hye⟩
      have he' : e ∈ D.treeGraphEdges hj h (⋃₀ F) := by
        rw [hEq]
        exact he
      exact ⟨z, Or.inl ⟨e, he', hz⟩, hzQ⟩
  obtain ⟨hfin, hconn, hcontain⟩ := hkey
  obtain ⟨hVfin, hVcard, hdist⟩ := treeGraph_finite_card_dist hL hC hW hfin hE hconn
  have hvert : ∀ v ∈ D.treeGraphVertices hj h Γ, D.IsLevelVertex hj h v := by
    rintro v (⟨e, he, hv⟩ | ⟨hv, -⟩)
    · exact isLevelVertex_of_isEdgeEndpoint hL he.1 hv
    · exact hv
  refine ⟨⟨hconn, fun A hA => ?_, hVcard, hdist⟩, hcontain, fun Q hQ => ?_, ?_⟩
  · obtain ⟨a, b, hab, -, -, hset⟩ := exists_two_endpoints (hj := hj) (h := h) hL hA.1
    exact ⟨a, b, hab, hA, hset⟩
  · obtain ⟨v, hv, hvQ⟩ := hcontain Q hQ
    exact mem_biUnion hv ⟨hQ.1, hvQ⟩
  · have hcount : ((D.levelUnitPartition hj h).cubesMeeting
        (D.treeGraphVertices hj h Γ)).encard ≤ 16 * (D.treeGraphVertices hj h Γ).encard := by
      refine encard_biUnion_le_mul hVfin _ 16 fun v hv => ?_
      exact (hC D j hj h).1.2.2 v (hvert v hv)
    exact hcount.trans (mul_le_mul_right hVcard 16)
section Plaquettes
variable {L m : ℕ} {k : ℤ}
theorem pointOnAxis_add (μ : Fin 4) (s t : ℝ) :
    pointOnAxis L m μ (s + t) = pointOnAxis L m μ s + pointOnAxis L m μ t := by
  simp only [pointOnAxis, AddCircle.coe_add, Pi.single_add]
theorem pointOnAxis_add_eq_torusProj (f s : Fin 4) (t₁ t₂ : ℝ) :
    pointOnAxis L m f t₁ + pointOnAxis L m s t₂ =
      TorusMetric.torusProj (torusSide L m) (Pi.single f t₁ + Pi.single s t₂) := by
  funext μ
  simp only [Pi.add_apply, pointOnAxis, TorusMetric.torusProj, AddCircle.coe_add]
  rcases eq_or_ne μ f with rfl | h₁ <;> rcases eq_or_ne μ s with rfl | h₂ <;>
    simp [*]
theorem barycenter_sub_vertex (p : Plaquette L m k) {c : Site L m k} (hc : c ∈ p.vertices) :
    ∃ t₁ t₂ : ℝ, |t₁| = |meshSize L k| / 2 ∧ |t₂| = |meshSize L k| / 2 ∧
      p.barycenter - (c : FourTorus L m) =
        pointOnAxis L m p.firstAxis t₁ + pointOnAxis L m p.secondAxis t₂ := by
  have hhalf : ∀ μ, pointOnAxis L m μ (meshSize L k / 2) =
      pointOnAxis L m μ (meshSize L k) + pointOnAxis L m μ (-(meshSize L k / 2)) := fun μ => by
    rw [← pointOnAxis_add]
    congr 1
    ring
  have hp : |meshSize L k / 2| = |meshSize L k| / 2 := by simp [abs_div]
  have hn : |-(meshSize L k / 2)| = |meshSize L k| / 2 := by simp [abs_div]
  rcases hc with rfl | rfl | rfl | rfl
  · refine ⟨_, _, hp, hp, ?_⟩
    simp only [Plaquette.barycenter]
    abel
  · refine ⟨_, _, hn, hp, ?_⟩
    simp only [Plaquette.barycenter, AddSubgroup.coe_add, unitStep]
    rw [hhalf p.firstAxis]
    abel
  · refine ⟨_, _, hn, hn, ?_⟩
    simp only [Plaquette.barycenter, AddSubgroup.coe_add, unitStep]
    rw [hhalf p.firstAxis, hhalf p.secondAxis]
    abel
  · refine ⟨_, _, hp, hn, ?_⟩
    simp only [Plaquette.barycenter, AddSubgroup.coe_add, unitStep]
    rw [hhalf p.secondAxis]
    abel
end Plaquettes
theorem barycenter_near_vertex (hL : Coordinates.CosetsAndDistancesStatement) (hj : j ≤ D.K)
    (h : D.LevelFits j) (p : Plaquette D.L D.m (D.K : ℤ)) {c : Site D.L D.m (D.K : ℤ)}
    (hc : c ∈ p.vertices) :
    TorusMetric.torusSupNorm (p.barycenter - (c : D.Torus)) ≤ meshSize D.L (D.K : ℤ) / 2 ∧
      TorusMetric.torusEuclidNorm (p.barycenter - (c : D.Torus)) ≤
        3 / 4 * meshSize D.L (D.K : ℤ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hMin, -⟩ := hL D j hj h
  have ha : 0 < meshSize D.L (D.K : ℤ) := by
    have : 0 < D.L := by
      have := D.isAdmissible.2
      omega
    exact zpow_pos (by exact_mod_cast this) _
  obtain ⟨t₁, t₂, h₁, h₂, hx⟩ := barycenter_sub_vertex p hc
  rw [abs_of_pos ha] at h₁ h₂
  have hfs : p.firstAxis ≠ p.secondAxis := p.firstAxis_lt_secondAxis.ne
  set w : Fin 4 → ℝ := Pi.single p.firstAxis t₁ + Pi.single p.secondAxis t₂ with hw
  have hcov : TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) w =
      p.barycenter - (c : D.Torus) := by
    rw [hx, pointOnAxis_add_eq_torusProj]
  have hcoord : ∀ μ, |w μ| ≤ meshSize D.L (D.K : ℤ) / 2 := by
    intro μ
    simp only [hw, Pi.add_apply]
    rcases eq_or_ne μ p.firstAxis with rfl | hμ₁
    · simp [hfs, h₁]
    · rcases eq_or_ne μ p.secondAxis with rfl | hμ₂
      · simp [hμ₁, h₂]
      · simp [hμ₁, hμ₂]
        positivity
  constructor
  · refine ((hMin _).1.2 ⟨w, hcov, rfl⟩).trans ?_
    exact Finset.sup'_le _ _ fun μ _ => hcoord μ
  · refine ((hMin _).2.2 ⟨w, hcov, rfl⟩).trans ?_
    have hsum : ∑ μ, w μ ^ 2 = t₁ ^ 2 + t₂ ^ 2 := by
      have hterm : ∀ μ, w μ ^ 2 = (Pi.single p.firstAxis (t₁ ^ 2) : Fin 4 → ℝ) μ +
          (Pi.single p.secondAxis (t₂ ^ 2) : Fin 4 → ℝ) μ := by
        intro μ
        simp only [hw, Pi.add_apply]
        rcases eq_or_ne μ p.firstAxis with rfl | hμ₁
        · simp [hfs]
        · rcases eq_or_ne μ p.secondAxis with rfl | hμ₂
          · simp [hμ₁]
          · simp [hμ₁, hμ₂]
      simp only [hterm, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true]
    have hsq₁ : t₁ ^ 2 = (meshSize D.L (D.K : ℤ) / 2) ^ 2 := by rw [← sq_abs, h₁]
    have hsq₂ : t₂ ^ 2 = (meshSize D.L (D.K : ℤ) / 2) ^ 2 := by rw [← sq_abs, h₂]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [hsum, hsq₁, hsq₂]
    nlinarith [sq_nonneg (meshSize D.L (D.K : ℤ))]
theorem exists_vertex_near_meeting_cube (hL : Coordinates.CosetsAndDistancesStatement)
    (hj : j ≤ D.K) (h : D.LevelFits j) {X : Set D.Torus} {p : Plaquette D.L D.m (D.K : ℤ)}
    (hp : p ∈ D.plaquettesOfThickened j X) :
    ∃ (q : D.Torus) (Q : Set D.Torus) (c : Site D.L D.m (D.cubeScaleIndex j)),
      D.IsLevelCube j Q ∧ q ∈ Q ∧
      D.cubeCentredAt c ∈ partitionCubesIn (D.cubeScaleIndex j) X ∧
      CubesMeet Q (D.cubeCentredAt c) ∧
      TorusMetric.torusSupNorm (p.barycenter - q) ≤ meshSize D.L (D.K : ℤ) / 2 ∧
      TorusMetric.torusEuclidNorm (p.barycenter - q) ≤ 3 / 4 * meshSize D.L (D.K : ℤ) := by
  obtain ⟨c, hc, Q, ⟨hQ, Q', hQ', hT⟩, hcQ⟩ := hp
  obtain ⟨y, rfl⟩ := hQ'.1
  obtain ⟨h₁, h₂⟩ := barycenter_near_vertex hL hj h p hc
  exact ⟨c, Q, y, hQ, hcQ, hQ', hT, h₁, h₂⟩
theorem torusEuclidNorm_barycenter_sub_lt (hL : Coordinates.CosetsAndDistancesStatement)
    (hC : PartitionCells.Holds)
    (hP : CubeSidesAndLinearSize)
    (hG : PeriodicLattice.EdgeGraphsDescribedByCubes)
    (hW : Graphs.ExistsClosedWalkThroughAllVertices) (hj : j ≤ D.K) (h : D.LevelFits j)
    {d : DomainKind} {X : Set D.Torus} (hX : X ∈ D.regionsBy d j)
    {p₁ p₂ : Plaquette D.L D.m (D.K : ℤ)} (h₁ : p₁ ∈ D.plaquettesOfThickened j X)
    (h₂ : p₂ ∈ D.plaquettesOfThickened j X) :
    TorusMetric.torusEuclidNorm (p₁.barycenter - p₂.barycenter) <
      (D.extent j X + 10) * D.physicalCubeSide j := by
  obtain ⟨hTwo, -, -, -, -, -, -, -, -, -, -, hLaws, -⟩ := hL D j hj h
  have hσ := hTwo.2.1
  have haσ : meshSize D.L (D.K : ℤ) ≤ D.physicalCubeSide j :=
    Setup.meshSize_le_cubeSide_mul_meshSize j
  obtain ⟨hcubes, hplaq⟩ := ((hP D j hj).2 h).2 d X hX
  have hne : (partitionCubesIn (D.cubeScaleIndex j) X).Nonempty := hplaq ⟨p₁, h₁⟩
  obtain ⟨-, -, -, -, n, hn, ⟨Γ, ht, hm⟩, -⟩ := hcubes hne
  obtain ⟨⟨-, -, -, hdist⟩, hcontain, -, -⟩ := treeGraph_properties hL hC hG hW hX hne ht hm
  obtain ⟨q₁, Q₁, c₁, hQ₁, hq₁, hc₁, hT₁, -, hb₁⟩ := exists_vertex_near_meeting_cube hL hj h h₁
  obtain ⟨q₂, Q₂, c₂, hQ₂, hq₂, hc₂, hT₂, -, hb₂⟩ := exists_vertex_near_meeting_cube hL hj h h₂
  obtain ⟨v₁, hv₁, hv₁Q⟩ := hcontain _ hc₁
  obtain ⟨v₂, hv₂, hv₂Q⟩ := hcontain _ hc₂
  have hnear := (hC D j hj h).2.2.2.1.2.1
  have d₁ := ((hnear c₁ Q₁ hQ₁ hT₁ q₁ hq₁).2 v₁ hv₁Q).2
  have d₂ := ((hnear c₂ Q₂ hQ₂ hT₂ q₂ hq₂).2 v₂ hv₂Q).2
  have d₃ := hdist v₁ hv₁ v₂ hv₂
  have e₁ := (hLaws p₁.barycenter q₁ p₂.barycenter).2.2.2.1
  have e₂ := (hLaws q₁ v₁ p₂.barycenter).2.2.2.1
  have e₃ := (hLaws v₁ v₂ p₂.barycenter).2.2.2.1
  have e₄ := (hLaws v₂ q₂ p₂.barycenter).2.2.2.1
  have s₁ := (hLaws v₂ q₂ q₂).2.1
  have s₂ := (hLaws q₂ p₂.barycenter q₂).2.1
  rw [hn]
  nlinarith
theorem ballReach_count_le (hj : j ≤ D.K) (hσ : 0 < D.physicalCubeSide j) {R : ℝ} (hR : 0 < R)
    (c : ConstantParameters) (hcL : c.L = D.L)
    (hcE : c.cubeExp = D.cubeExp) :
    (2 * D.ballReach j R / D.physicalCubeSide j + 1) ^ 4 ≤ c.ballCubeCount R ((D.K : ℕ) - j) := by
  have hL₀ : (0 : ℝ) < (D.L : ℝ) := by
    have : 0 < D.L := by
      have := D.isAdmissible.2
      omega
    exact_mod_cast this
  have hL₁ : (1 : ℝ) ≤ (D.L : ℝ) := by
    have : 1 ≤ D.L := by
      have := D.isAdmissible.2
      omega
    exact_mod_cast this
  have hM : (c.cubeSide : ℝ) = (D.cubeSide : ℝ) := by
    simp only [ConstantParameters.cubeSide, Setup.cubeSide, hcL, hcE]
  have hM₀ : (0 : ℝ) < (D.cubeSide : ℝ) := by
    have : 0 < D.cubeSide := by
      have : 0 < D.L := by
        have := D.isAdmissible.2
        omega
      exact Nat.pow_pos this
    exact_mod_cast this
  have hdepth : D.depthOf j = (((D.K : ℕ) - j : ℕ) : ℤ) := by
    simp only [Setup.depthOf, PeriodicLattice.levelDepth]
    omega
  have hsp : (D.L : ℝ) ^ ((D.K : ℕ) - j) * meshSize D.L (D.depthOf j) = 1 := by
    rw [hdepth, meshSize, zpow_neg, zpow_natCast]
    exact mul_inv_cancel₀ (pow_pos hL₀ _).ne'
  have hBM : (D.L : ℝ) ^ ((D.K : ℕ) - j) / (D.cubeSide : ℝ) = 1 / D.physicalCubeSide j := by
    rw [div_eq_div_iff hM₀.ne' hσ.ne']
    simp only [Setup.physicalCubeSide]
    linear_combination (D.cubeSide : ℝ) * hsp
  have haK : meshSize D.L (D.K : ℤ) ≤ 1 := by
    rw [meshSize, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hL₁)
  have haK₀ : 0 < meshSize D.L (D.K : ℤ) := zpow_pos hL₀ _
  have hlhs : 2 * D.ballReach j R / D.physicalCubeSide j + 1 =
      (2 * R + meshSize D.L (D.K : ℤ)) / D.physicalCubeSide j + 4 := by
    have hgen : ∀ σ a r : ℝ, 0 < σ →
        2 * (r + 1 / 2 * a + 3 / 2 * σ) / σ + 1 = (2 * r + a) / σ + 4 := by
      intro σ a r hs
      field_simp
      ring
    exact hgen _ _ _ hσ
  have hrhs : 2 * (R + 1) * (c.L : ℝ) ^ ((D.K : ℕ) - j) / (c.cubeSide : ℝ) + 4 =
      2 * (R + 1) / D.physicalCubeSide j + 4 := by
    rw [hM, hcL, mul_div_assoc, hBM]
    ring
  rw [ConstantParameters.ballCubeCount, hrhs, hlhs]
  refine pow_le_pow_left₀ (by positivity) ?_ 4
  have : (2 * R + meshSize D.L (D.K : ℤ)) / D.physicalCubeSide j ≤
      2 * (R + 1) / D.physicalCubeSide j :=
    div_le_div_of_nonneg_right (by linarith) hσ.le
  linarith
theorem localisationDomainTreeClaim_holds (hL : Coordinates.CosetsAndDistancesStatement)
    (hC : PartitionCells.Holds)
    (hP : CubeSidesAndLinearSize)
    (hG : PeriodicLattice.EdgeGraphsDescribedByCubes)
    (hW : Graphs.ExistsClosedWalkThroughAllVertices) :
    LocalisationDomainTreeClaim := by
  intro D j hj h d X hX
  refine ⟨fun E Γ hcube _ ht hm => treeGraph_properties hL hC hG hW hX hcube ht hm,
    fun p₁ h₁ p₂ h₂ => torusEuclidNorm_barycenter_sub_lt hL hC hP hG hW hj h hX h₁ h₂,
    fun y₀ R hR => ?_⟩
  obtain ⟨hTwo, -, -, -, -, -, -, -, -, -, hNorm, hLaws, -⟩ := hL D j hj h
  have hσ := hTwo.2.1
  have haK₀ : 0 < meshSize D.L (D.K : ℤ) := by
    have : 0 < D.L := by
      have := D.isAdmissible.2
      omega
    exact zpow_pos (by exact_mod_cast this) _
  have hρ : 0 ≤ D.ballReach j R := by
    simp only [Setup.ballReach]
    positivity
  obtain ⟨hfin, hnum⟩ := (hC D j hj h).2.2.2.2 y₀ _ hρ
  refine ⟨?_, hfin, fun c hcL hcE => hnum.trans (ballReach_count_le hj hσ hR c hcL hcE)⟩
  rintro ⟨p, hp, hpR⟩
  obtain ⟨q, Q, c, hQ, hq, hc, hT, hb, -⟩ := exists_vertex_near_meeting_cube hL hj h hp
  refine ⟨c, hc, ?_⟩
  have d₁ := ((hC D j hj h).2.2.2.1.2.1 c Q hQ hT q hq).1
  have s₁ := (hLaws (c : D.Torus) q q).1
  have s₂ := (hLaws q (c : D.Torus) q).1
  have e₁ := (hLaws (c : D.Torus) q y₀).2.2.1
  have e₂ := (hLaws q p.barycenter y₀).2.2.1
  have e₃ := (hLaws p.barycenter q q).1
  have e₄ := (hLaws q p.barycenter q).1
  have n₁ := (hNorm (p.barycenter - y₀)).1
  simp only [Setup.ballReach]
  linarith
end LocalisationDomainTree
end TorusBound
end YangMills.Construction
end

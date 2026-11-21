import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps
namespace TorusFields
variable {n : ℕ} [NeZero n]
theorem natAbs_valMinAbs_intCast_le (e : ℤ) : ((e : ZMod n).valMinAbs).natAbs ≤ e.natAbs := by
  apply ZMod.natAbs_min_of_le_div_two n _ _ (by simp) (ZMod.natAbs_valMinAbs_le _)
theorem supDist_le_iff (x y : TorusSite n) (m : ℕ) :
    supDist x y ≤ m ↔ ∀ i, ((x i - y i).valMinAbs).natAbs ≤ m := by
  simp [supDist, Finset.sup_le_iff]
theorem supDist_comm (x y : TorusSite n) : supDist x y = supDist y x := by
  unfold supDist
  congr 1
  funext i
  rw [← neg_sub (x i) (y i)]
  exact (ZMod.natAbs_valMinAbs_neg _).symm
theorem supDist_self (x : TorusSite n) : supDist x x = 0 := by
  simp [supDist]
theorem exists_offset_of_supDist (x z : TorusSite n) :
    ∃ e : Fin 4 → ℤ, z = x + siteOfInt e ∧ ∀ i, (e i).natAbs ≤ supDist x z := by
  refine ⟨fun i => (z i - x i).valMinAbs, ?_, fun i => ?_⟩
  · funext i
    simp [siteOfInt]
  · rw [supDist_comm]
    exact Finset.le_sup (f := fun i => ((z i - x i).valMinAbs).natAbs) (Finset.mem_univ i)
theorem supDist_add_siteOfInt_le (x : TorusSite n) (e : Fin 4 → ℤ) (m : ℕ)
    (he : ∀ i, (e i).natAbs ≤ m) : supDist x (x + siteOfInt e) ≤ m := by
  rw [supDist_comm, supDist_le_iff]
  intro i
  have : (x + siteOfInt e : TorusSite n) i - x i = ((e i : ℤ) : ZMod n) := by simp [siteOfInt]
  rw [this]
  exact (natAbs_valMinAbs_intCast_le _).trans (he i)
theorem siteOfInt_add (e e' : Fin 4 → ℤ) :
    (siteOfInt (e + e') : TorusSite n) = siteOfInt e + siteOfInt e' := by
  funext i
  simp [siteOfInt]
theorem supDist_triangle (x y z : TorusSite n) : supDist x z ≤ supDist x y + supDist y z := by
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist x y
  obtain ⟨e', he', hb'⟩ := exists_offset_of_supDist y z
  have hz : z = x + siteOfInt (e + e') := by rw [he', he, siteOfInt_add, add_assoc]
  have := supDist_add_siteOfInt_le x (e + e') (supDist x y + supDist y z) fun i => by
    have h1 := hb i
    have h2 := hb' i
    simp only [Pi.add_apply]
    omega
  rwa [← hz] at this
theorem supDist_add_right (x y u : TorusSite n) : supDist (x + u) (y + u) = supDist x y := by
  simp [supDist]
theorem exists_midpoint (x z : TorusSite n) (m : ℕ) (h : supDist x z ≤ 2 * m) :
    ∃ v : TorusSite n, supDist x v ≤ m ∧ supDist v z ≤ m := by
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist x z
  refine ⟨x + siteOfInt fun i => e i / 2, supDist_add_siteOfInt_le _ _ _ fun i => ?_, ?_⟩
  · have := hb i
    omega
  · have hz : z = (x + siteOfInt fun i => e i / 2) + siteOfInt fun i => e i - e i / 2 := by
      rw [add_assoc, ← siteOfInt_add, he]
      congr 2
      funext i
      simp
    rw [hz]
    refine supDist_add_siteOfInt_le _ _ _ fun i => ?_
    have := hb i
    omega
theorem mem_thickening (m : ℕ) (X : Finset (TorusSite n)) (z : TorusSite n) :
    z ∈ thickening m X ↔ ∃ x ∈ X, supDist z x ≤ m := by
  classical
  simp [thickening]
theorem supDist_add_unitStep_le (x : TorusSite n) (i : Fin 4) : supDist x (x + unitStep n i) ≤ 1 := by
  have : unitStep n i = (siteOfInt (Pi.single i 1) : TorusSite n) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [siteOfInt, unitStep]
    · simp [siteOfInt, unitStep, hk]
  rw [this]
  refine supDist_add_siteOfInt_le _ _ _ fun k => ?_
  by_cases hk : k = i
  · subst hk
    simp
  · simp [hk]
end TorusFields
namespace TorusLumps
variable {n : ℕ} [NeZero n] {r : ℕ} {Y : Finset (TorusSite n)}
theorem chainConnected_mem {y z : TorusSite n} (hy : y ∈ Y) (h : ChainConnected r Y y z) : z ∈ Y := by
  induction h with
  | refl => exact hy
  | tail _ hs _ => exact hs.2.1
theorem chainConnected_symm {y z : TorusSite n} (h : ChainConnected r Y y z) :
    ChainConnected r Y z y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    exact Relation.ReflTransGen.head ⟨hs.2.1, hs.1, by rw [supDist_comm]; exact hs.2.2⟩ ih
theorem chainConnected_of_supDist_le {y z : TorusSite n} (hy : y ∈ Y) (hz : z ∈ Y)
    (h : supDist y z ≤ r) : ChainConnected r Y y z :=
  Relation.ReflTransGen.single ⟨hy, hz, h⟩
open Classical in
theorem mem_chainComponents {X : Finset (TorusSite n)} :
    X ∈ chainComponents r Y ↔ ∃ y ∈ Y, X = Y.filter (ChainConnected r Y y) := by
  simp only [chainComponents, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
open Classical in
theorem eq_filter_of_mem_chainComponents {X : Finset (TorusSite n)} (hX : X ∈ chainComponents r Y)
    {z : TorusSite n} (hz : z ∈ X) : X = Y.filter (ChainConnected r Y z) := by
  obtain ⟨y, hy, rfl⟩ := mem_chainComponents.mp hX
  obtain ⟨hzY, hyz⟩ := Finset.mem_filter.mp hz
  ext u
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ =>
    ⟨fun h => (chainConnected_symm hyz).trans h, fun h => hyz.trans h⟩
open Classical in
theorem subset_of_mem_chainComponents {X : Finset (TorusSite n)} (hX : X ∈ chainComponents r Y) :
    X ⊆ Y := by
  obtain ⟨y, hy, rfl⟩ := mem_chainComponents.mp hX
  exact Finset.filter_subset _ _
open Classical in
theorem chainConnected_of_mem_chainComponents {X : Finset (TorusSite n)}
    (hX : X ∈ chainComponents r Y) {z z' : TorusSite n} (hz : z ∈ X) (hz' : z' ∈ X) :
    ChainConnected r Y z z' := by
  rw [eq_filter_of_mem_chainComponents hX hz] at hz'
  exact (Finset.mem_filter.mp hz').2
open Classical in
theorem mem_of_chainConnected_of_mem_chainComponents {X : Finset (TorusSite n)}
    (hX : X ∈ chainComponents r Y) {z z' : TorusSite n} (hz : z ∈ X) (hz' : z' ∈ Y)
    (h : ChainConnected r Y z z') : z' ∈ X := by
  rw [eq_filter_of_mem_chainComponents hX hz]
  exact Finset.mem_filter.mpr ⟨hz', h⟩
open Classical in
theorem eq_of_chainConnected_of_mem_chainComponents {X X' : Finset (TorusSite n)}
    (hX : X ∈ chainComponents r Y) (hX' : X' ∈ chainComponents r Y)
    {z z' : TorusSite n} (hz : z ∈ X) (hz' : z' ∈ X') (h : ChainConnected r Y z z') : X = X' := by
  have hzz : z ∈ X' :=
    mem_of_chainConnected_of_mem_chainComponents hX' hz' (subset_of_mem_chainComponents hX hz)
      (chainConnected_symm h)
  rw [eq_filter_of_mem_chainComponents hX hz, eq_filter_of_mem_chainComponents hX' hzz]
open Classical in
theorem exists_mem_chainComponents {y : TorusSite n} (hy : y ∈ Y) :
    ∃ X ∈ chainComponents r Y, y ∈ X :=
  ⟨Y.filter (ChainConnected r Y y), mem_chainComponents.mpr ⟨y, hy, rfl⟩,
    Finset.mem_filter.mpr ⟨hy, Relation.ReflTransGen.refl⟩⟩
open Classical in
theorem biUnion_chainComponents : (chainComponents r Y).biUnion id = Y := by
  ext y
  simp only [Finset.mem_biUnion, id]
  constructor
  · rintro ⟨X, hX, hy⟩
    exact subset_of_mem_chainComponents hX hy
  · intro hy
    exact exists_mem_chainComponents hy
end TorusLumps
end YangMills.Construction
end

import YangMills.Construction.Towers.BlocksOfATower
import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSites
import YangMills.Construction.Towers.InjectiveCovariantDifferenceAtTheBaseOfAChainProof
import YangMills.Construction.Towers.TriangularMapOfTheLayersOfSites
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tower
namespace Tower.VertexLayerParent
variable {L n k : ℕ}
theorem det_one_sub_nilpotent {V : Type*} [AddCommGroup V] [Module ℝ V]
    (N : V →ₗ[ℝ] V) (hN : IsNilpotent N) : LinearMap.det (1 - N) = 1 := by
  by_cases hf : Module.Finite ℝ V
  · have hc := LinearMap.eval_charpoly N (1 : ℝ)
    have hp : N.charpoly = Polynomial.X ^ Module.finrank ℝ V :=
      IsNilpotent.charpoly_eq_X_pow_finrank hN
    rw [hp] at hc
    simpa [Algebra.algebraMap_eq_smul_one] using hc.symm
  · exact LinearMap.det_eq_one_of_not_module_finite hf _
theorem sublattice_antitone (hL : 0 < L) {i j : ℕ} (h : i ≤ j) :
    PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) ≤
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) :=
  PeriodicLattice.sublattice_mono hL n (by simp only [PeriodicLattice.levelDepth]; omega)
theorem coe_toSublattice_zero (hL : 0 < L) {i : ℕ} (y : Tower.Vertex L n k i) :
    ((y.toSublattice (PeriodicLattice.levelDepth k 0) : Tower.Vertex L n k 0) :
      PeriodicLattice.FourTorus L n) = y := by apply _root_.YangMills.Construction.Tower.ChainBottom.coe_toSublattice <;> assumption
def IsParentVertex (z w : Tower.Vertex L n k 0) : Prop :=
  ∃ (i : Fin k) (y : Tower.Vertex L n k ((i : ℕ) + 1)),
    Tower.IsInVertexLayer L n k i (z : PeriodicLattice.FourTorus L n) ∧
    (z : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∧
    (z : PeriodicLattice.FourTorus L n) ≠ y ∧
    (w : PeriodicLattice.FourTorus L n) = y
def parentVertex (z : Tower.Vertex L n k 0) : Tower.Vertex L n k 0 :=
  open Classical in if h : ∃ w, IsParentVertex z w then h.choose else z
theorem IsParentVertex.not_mem_top (hL : 0 < L) {z w : Tower.Vertex L n k 0}
    (h : IsParentVertex z w) :
    (z : PeriodicLattice.FourTorus L n) ∉
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k k) := by
  obtain ⟨i, y, hl, -⟩ := h
  exact fun hz => hl.2 (sublattice_antitone hL (Nat.succ_le_of_lt i.is_lt) hz)
theorem exists_isParentVertex (hb : Tower.BlockStructure)
    (hc : ProlongCompositesAndVertexLayers.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    (z : Tower.Vertex L n k 0)
    (hz : (z : PeriodicLattice.FourTorus L n) ∉
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k k)) :
    ∃ w, IsParentVertex z w := by
  obtain ⟨i, hi, -⟩ := (hc.1 L n k hL hn hk).2.2.existsUnique_layer z hz
  have hL0 : 0 < L := by have := hL.2; omega
  have hs := ((hb L k ((i : ℕ) + 1) hL hk (Nat.succ_le_succ (Nat.zero_le _))
    (Nat.succ_le_of_lt i.is_lt)).1 n hn).2.1
  obtain ⟨y, hy, -⟩ := hs.2.2 ⟨z.1, hi.1⟩ hi.2
  refine ⟨y.toSublattice (PeriodicLattice.levelDepth k 0), i, y, hi, hy.1, ?_,
    coe_toSublattice_zero hL0 y⟩
  exact fun e => hy.2 e
theorem IsParentVertex.unique (hb : Tower.BlockStructure)
    (hc : ProlongCompositesAndVertexLayers.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    {z w w' : Tower.Vertex L n k 0}
    (h : IsParentVertex z w) (h' : IsParentVertex z w') : w = w' := by
  have hL0 : 0 < L := by have := hL.2; omega
  have htop := h.not_mem_top hL0
  obtain ⟨i, y, hl, hm, hne, hw⟩ := h
  obtain ⟨i', y', hl', hm', hne', hw'⟩ := h'
  obtain rfl : i = i' :=
    ((hc.1 L n k hL hn hk).2.2.existsUnique_layer z htop).unique hl hl'
  have hs := ((hb L k ((i : ℕ) + 1) hL hk (Nat.succ_le_succ (Nat.zero_le _))
    (Nat.succ_le_of_lt i.is_lt)).1 n hn).2.1
  have e : y = y' :=
    (hs.2.2 ⟨z.1, hl.1⟩ hl.2).unique ⟨hm, fun e => hne e⟩ ⟨hm', fun e => hne' e⟩
  subst e
  exact Subtype.ext (hw.trans hw'.symm)
theorem parentVertex_eq (hb : Tower.BlockStructure)
    (hc : ProlongCompositesAndVertexLayers.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    {z w : Tower.Vertex L n k 0}
    (h : IsParentVertex z w) : parentVertex z = w := by
  have he : ∃ w, IsParentVertex z w := ⟨w, h⟩
  rw [parentVertex, dif_pos he]
  exact he.choose_spec.unique hb hc hL hn hk h
theorem parentVertex_of_mem_top (hL : 0 < L) {z : Tower.Vertex L n k 0}
    (hz : (z : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k k)) :
    parentVertex z = z := by
  have he : ¬∃ w, IsParentVertex z w := fun ⟨w, h⟩ => h.not_mem_top hL hz
  rw [parentVertex, dif_neg he]
theorem parentVertex_mem (hb : Tower.BlockStructure)
    (hc : ProlongCompositesAndVertexLayers.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    {m : ℕ} (hm : m < k) {z : Tower.Vertex L n k 0}
    (hz : (z : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k m)) :
    (parentVertex z : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (m + 1)) := by
  have hL0 : 0 < L := by have := hL.2; omega
  by_cases ht : (z : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k k)
  · rw [parentVertex_of_mem_top hL0 ht]
    exact sublattice_antitone hL0 hm ht
  · obtain ⟨w, hw⟩ := exists_isParentVertex hb hc hL hn hk z ht
    rw [parentVertex_eq hb hc hL hn hk hw]
    obtain ⟨i, y, hl, -, -, e⟩ := hw
    have hmi : m ≤ (i : ℕ) := by
      by_contra hlt
      exact hl.2 (sublattice_antitone hL0 (by omega) hz)
    rw [e]
    exact sublattice_antitone hL0 (Nat.succ_le_succ hmi) y.2
theorem iterate_parentVertex_mem (hb : Tower.BlockStructure)
    (hc : ProlongCompositesAndVertexLayers.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    (z : Tower.Vertex L n k 0) :
    ∀ m ≤ k, ((parentVertex^[m] z : Tower.Vertex L n k 0) : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k m)
  | 0, _ => z.2
  | m + 1, h => by
      rw [Function.iterate_succ_apply']
      exact parentVertex_mem hb hc hL hn hk h
        (iterate_parentVertex_mem hb hc hL hn hk z m (by omega))
theorem apply_eq_zero_of_mem_top (hL : 0 < L) (κ : Tower.vertexFunctionsVanishingAtTop L n k)
    {z : Tower.Vertex L n k 0}
    (hz : (z : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k k)) :
    (κ : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) z = 0 := by
  have e := congrFun κ.2.2 ⟨z.1, hz⟩
  have hs : PeriodicLattice.Site.toSublattice (⟨z.1, hz⟩ : Tower.Vertex L n k k)
      (PeriodicLattice.levelDepth k 0) = z :=
    Subtype.ext (coe_toSublattice_zero hL _)
  simpa [Tower.restrictVertexFunction, PeriodicLattice.restrictGaugeMap, hs] using e
theorem comp_parentVertex_mem (hL : 0 < L) (κ : Tower.vertexFunctionsVanishingAtTop L n k) :
    (κ : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) ∘ parentVertex ∈
      Tower.vertexFunctionsVanishingAtTop L n k := by
  refine ⟨?_, funext fun x => ?_⟩
  · intro z _
    exact κ.2.1 (parentVertex z) (Set.mem_univ _)
  · have hx : ((x.toSublattice (PeriodicLattice.levelDepth k 0) : Tower.Vertex L n k 0) :
        PeriodicLattice.FourTorus L n) ∈
        PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k k) := by
      rw [coe_toSublattice_zero hL x]
      exact x.2
    simp only [Tower.restrictVertexFunction, PeriodicLattice.restrictGaugeMap, Function.comp,
      Pi.zero_apply]
    rw [parentVertex_of_mem_top hL hx]
    exact apply_eq_zero_of_mem_top hL κ hx
def parentShift (hL : 0 < L) :
    Tower.vertexFunctionsVanishingAtTop L n k →ₗ[ℝ] Tower.vertexFunctionsVanishingAtTop L n k where
  toFun κ := ⟨_, comp_parentVertex_mem hL κ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem parentShift_pow_apply (hL : 0 < L) (m : ℕ) (κ : Tower.vertexFunctionsVanishingAtTop L n k) :
    (((parentShift hL ^ m) κ : Tower.vertexFunctionsVanishingAtTop L n k) :
      Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) =
      (κ : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) ∘ parentVertex^[m] := by
  induction m generalizing κ with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ, Module.End.mul_apply, ih]
      funext z
      simp only [Function.comp, Function.iterate_succ_apply']
      rfl
theorem isNilpotent_parentShift (hb : Tower.BlockStructure)
    (hc : ProlongCompositesAndVertexLayers.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) (hL0 : 0 < L) :
    IsNilpotent (parentShift (n := n) (k := k) hL0) := by
  refine ⟨k, LinearMap.ext fun κ => Subtype.ext (funext fun z => ?_)⟩
  rw [parentShift_pow_apply]
  exact apply_eq_zero_of_mem_top hL0 κ (iterate_parentVertex_mem hb hc hL hn hk z k le_rfl)
end Tower.VertexLayerParent
open Tower.VertexLayerParent in
theorem Tower.layerDifferenceTriangular_proof (hb : Tower.BlockStructure)
    (hc : ProlongCompositesAndVertexLayers.Statement) :
    Tower.LayerDifferenceTriangular := by
  intro L n k hL hn hk
  have hL0 : 0 < L := by have := hL.2; omega
  refine ⟨1 - parentShift hL0, ?_, ?_⟩
  · intro κ i y x hx hne
    have hp : IsParentVertex (x.1.toSublattice (PeriodicLattice.levelDepth k 0) :
        Tower.Vertex L n k 0) (y.toSublattice (PeriodicLattice.levelDepth k 0)) := by
      have e := coe_toSublattice_zero (k := k) hL0 x.1
      refine ⟨i, y, ?_, ?_, ?_, coe_toSublattice_zero hL0 y⟩
      · rw [e]
        exact ⟨x.1.2, x.2⟩
      · rw [e]
        exact hx
      · rw [e]
        exact hne
    have hq := parentVertex_eq hb hc hL hn hk hp
    show ((1 - parentShift hL0) κ : Tower.vertexFunctionsVanishingAtTop L n k).1
        (x.1.toSublattice _) =
      κ.1 (x.1.toSublattice _) - κ.1 (y.toSublattice _)
    show κ.1 (x.1.toSublattice _) - κ.1 (parentVertex (x.1.toSublattice _)) = _
    rw [hq]
  · rw [det_one_sub_nilpotent _ (isNilpotent_parentShift hb hc hL hn hk hL0)]
    simp
end YangMills.Construction
end

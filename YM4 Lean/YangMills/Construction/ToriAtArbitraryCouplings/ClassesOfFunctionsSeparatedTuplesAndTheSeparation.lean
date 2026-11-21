import YangMills.Construction.ReflectionPositivity.LipschitzTuplesIsometriesOnFunctionsTensorsAndPartitions
import YangMills.Construction.ToriAtArbitraryCouplings.TheEuclideanDistanceAndTheCoveringMapProof
import YangMills.Construction.ToriAtArbitraryCouplings.TheGradientNorm
import YangMills.Construction.Torus.RescalingLiftsAndFunctionNorms
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace TorusSide
variable (s : TorusSide)
def lipSuppIn (E : Ambient) (A : Set (s.Point E)) : Set (s.Point E → ℝ) :=
  {f | TestFunctions.IsLipschitzFor (s.pointDist E) f ∧ s.IsCompactWrt E (s.closedSupport E f) ∧
    s.closedSupport E f ⊆ A}
def c1SuppIn (E : Ambient) (A : Set (s.Point E)) : Set (s.Point E → ℝ) :=
  {f | f ∈ s.c1Set E ∧ s.IsCompactWrt E (s.closedSupport E f) ∧ s.closedSupport E f ⊆ A}
theorem c1SuppIn_univ (E : Ambient) : s.c1SuppIn E univ = s.c1CompactSet E := by
  ext f
  simp [c1SuppIn, c1CompactSet]
theorem c1SuppIn_eq_compactC1SuppIn (E : Ambient) (A : Set (s.Point E)) :
    s.c1SuppIn E A = Ambient.compactC1SuppIn s.asMirrorData E A := by
  ext f
  exact and_assoc.symm
abbrev FnTuple (E : Ambient) : Type := Ambient.FnList s.asMirrorData E
abbrev sepOfLength (E : Ambient) (n : ℕ) : Set (s.FnTuple E) :=
  Ambient.separatedN s.asMirrorData E n
abbrev sepTuples (E : Ambient) : Set (s.FnTuple E) :=
  Ambient.separatedAll s.asMirrorData E
theorem mem_sepOfLength_iff (E : Ambient) (n : ℕ) (X : s.FnTuple E) :
    X ∈ s.sepOfLength E n ↔ X.length = n ∧
      (∀ f ∈ X, f ∈ s.c1Set E ∧ s.IsCompactWrt E (s.closedSupport E f)) ∧
        X.Pairwise fun f g => Disjoint (s.closedSupport E f) (s.closedSupport E g) :=
  Iff.rfl
def lipDisjointOfLength (E : Ambient) (n : ℕ) : Set (s.FnTuple E) :=
  {X | X.length = n ∧ Ambient.IsLipschitzDisjointList s.asMirrorData E X}
theorem mem_lipDisjointOfLength_iff (E : Ambient) (n : ℕ) (X : s.FnTuple E) :
    X ∈ s.lipDisjointOfLength E n ↔ X.length = n ∧
      (∀ f ∈ X, TestFunctions.IsLipschitzFor (s.pointDist E) f ∧
        s.IsCompactWrt E (s.closedSupport E f)) ∧
        X.Pairwise fun f g => Disjoint (s.closedSupport E f) (s.closedSupport E g) :=
  Iff.rfl
theorem ofFn_mem_lipDisjointOfLength_iff (E : Ambient) {n : ℕ} (f : Fin n → s.Point E → ℝ) :
    List.ofFn f ∈ s.lipDisjointOfLength E n ↔
      (∀ i, TestFunctions.IsLipschitzFor (s.pointDist E) (f i)) ∧
        (∀ i, s.IsCompactWrt E (s.closedSupport E (f i))) ∧
          ∀ i k, i ≠ k → Disjoint (s.closedSupport E (f i)) (s.closedSupport E (f k)) := by
  rw [mem_lipDisjointOfLength_iff, List.forall_mem_ofFn_iff, List.pairwise_ofFn]
  constructor
  · rintro ⟨-, h, h'⟩
    refine ⟨fun i => (h i).1, fun i => (h i).2, fun i k hik => ?_⟩
    rcases lt_or_gt_of_ne hik with hlt | hlt
    · exact h' hlt
    · exact (h' hlt).symm
  · rintro ⟨h, h', h''⟩
    exact ⟨List.length_ofFn, fun i => ⟨h i, h' i⟩, fun {i k} hik => h'' i k hik.ne⟩
theorem isCompactWrt_euclidDistTorus_iff {ℓ : ℝ} [Fact (0 < ℓ)]
    (Z : Set (TorusMetric.Torus4 ℓ)) :
    MetricNotions.IsCompactWrt TestFunctions.euclidDistTorus Z ↔ IsCompact Z := by
  have hopen : ∀ U : Set (TorusMetric.Torus4 ℓ),
      MetricNotions.IsOpenWrt TestFunctions.euclidDistTorus U ↔ IsOpen U := fun U => by
    have h : @IsOpen _ (TorusAnalysis.euclidTopology ℓ) U ↔ IsOpen U := by
      rw [TorusAnalysis.euclidTopology_eq_instTopology]
    refine Iff.trans ?_ h
    change _ ↔ ∀ y ∈ U, ∃ r > 0, ∀ y', TorusMetric.torusEuclidNorm (y' - y) < r → y' ∈ U
    refine forall₂_congr fun x _ => exists_congr fun r => and_congr_right fun _ => ?_
    refine forall_congr' fun y => ?_
    rw [AmbientPoints.torusEuclidNorm_sub_comm]
    rfl
  constructor
  · intro hZ
    refine isCompact_of_finite_subcover fun {ι} U hU hcov => ?_
    obtain ⟨𝒰, hsub, hfin, hcov'⟩ := hZ (Set.range U)
      (by rintro _ ⟨i, rfl⟩; exact (hopen _).2 (hU i)) (by rwa [sUnion_range])
    classical
    have hpick : ∀ V ∈ 𝒰, ∃ i, U i = V := fun V hV => hsub hV
    choose g hg using hpick
    refine ⟨hfin.toFinset.attach.image fun V => g V.1 (hfin.mem_toFinset.1 V.2), fun x hx => ?_⟩
    obtain ⟨V, hV, hxV⟩ := hcov' hx
    refine mem_iUnion₂.2 ⟨g V hV, Finset.mem_image.2
      ⟨⟨V, hfin.mem_toFinset.2 hV⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    rw [hg V hV]
    exact hxV
  · intro hZ 𝒰 hU hcov
    obtain ⟨t, ht, hfin, hcov'⟩ := hZ.elim_finite_subcover_image (b := 𝒰) (c := id)
      (fun V hV => (hopen V).1 (hU V hV)) (by simpa [sUnion_eq_biUnion] using hcov)
    exact ⟨t, ht, hfin, by simpa [sUnion_eq_biUnion] using hcov'⟩
theorem length_pos : 0 < s.length := by apply _root_.YangMills.Construction.ToriAtArbitraryCouplings.DistanceAndProjection.length_pos <;> assumption
def supportGap (E : Ambient) (X : s.FnTuple E) : ℝ≥0∞ :=
  ⨅ (i : Fin X.length) (k : Fin X.length) (_ : i ≠ k),
    s.setDist E (s.closedSupport E (X.get i)) (s.closedSupport E (X.get k))
theorem supportGap_ofFn (E : Ambient) {n : ℕ} (f : Fin n → s.Point E → ℝ) :
    s.supportGap E (List.ofFn f) =
      ⨅ (i : Fin n) (k : Fin n) (_ : i ≠ k),
        s.setDist E (s.closedSupport E (f i)) (s.closedSupport E (f k)) := by
  have hlen : (List.ofFn f).length = n := List.length_ofFn
  have hget : ∀ i : Fin (List.ofFn f).length, (List.ofFn f).get i = f (Fin.cast hlen i) := by
    intro i
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    rfl
  let e : Fin (List.ofFn f).length ≃ Fin n := finCongr hlen
  unfold supportGap
  refine e.iInf_congr fun i => (e.iInf_congr fun k => ?_).symm
  refine iInf_congr_Prop e.injective.ne_iff fun _ => ?_
  rw [hget, hget]
  rfl
end TorusSide
end YangMills.Construction.ToriAtArbitraryCouplings
end

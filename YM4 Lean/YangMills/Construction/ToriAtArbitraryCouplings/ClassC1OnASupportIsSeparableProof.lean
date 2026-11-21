import YangMills.Construction.PassageToTheLimit.SpacesOfFunctionsOfClassC1AreBanachSpacesProof
import YangMills.Construction.ToriAtArbitraryCouplings.ClassC1OnASupportIsCompleteProof
import YangMills.Construction.ToriAtArbitraryCouplings.ClassC1OnASupportIsSeparable
import YangMills.Construction.ToriAtArbitraryCouplings.TheEuclideanDistanceAndTheCoveringMapProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
open TestFunctions (partialDerivR4)
namespace C1SupportSeparable
private theorem partialDerivR4_eq_fderiv {φ : (Fin 4 → ℝ) → ℝ} {p : Fin 4 → ℝ}
    (hφ : DifferentiableAt ℝ φ p) (i : Fin 4) :
    partialDerivR4 i φ p = fderiv ℝ φ p (Pi.single i (1 : ℝ)) := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.C1Banach.partialDerivR4_eq_fderiv <;> assumption
private theorem continuous_partialDerivR4 {φ : (Fin 4 → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (i : Fin 4) :
    Continuous (partialDerivR4 i φ) := by apply _root_.YangMills.SharedProofs.p32205 <;> assumption
private theorem exists_countable_c1_approx {ι : Type*} (F : ι → (Fin 4 → ℝ) → ℝ)
    (hF : ∀ a, ContDiff ℝ 1 (F a)) {C : Set (Fin 4 → ℝ)} (hC : IsCompact C) :
    ∃ S : Set ι, S.Countable ∧ ∀ a, ∀ ε : ℝ, 0 < ε → ∃ b ∈ S, ∀ p ∈ C,
      |F a p - F b p| ≤ ε ∧ ∀ i, |partialDerivR4 i (F a) p - partialDerivR4 i (F b) p| ≤ ε := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let jet : ι → C(C, ℝ × (Fin 4 → ℝ)) := fun a =>
    ⟨fun p => (F a p, fun i => partialDerivR4 i (F a) p),
      (((hF a).continuous.comp continuous_subtype_val).prodMk
        (continuous_pi fun i => (continuous_partialDerivR4 (hF a) i).comp continuous_subtype_val))⟩
  obtain ⟨T, hTsub, hTcount, hTdense⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (Set.range jet)).exists_countable_dense_subset
  choose idx hidx using fun u : T => hTsub u.2
  have : Countable T := hTcount.to_subtype
  refine ⟨Set.range idx, Set.countable_range idx, fun a ε hε => ?_⟩
  obtain ⟨u, huT, hu⟩ := Metric.mem_closure_iff.mp (hTdense (Set.mem_range_self a)) ε hε
  have hb : jet (idx ⟨u, huT⟩) = u := hidx ⟨u, huT⟩
  set b := idx ⟨u, huT⟩
  refine ⟨b, Set.mem_range_self _, fun p hp => ?_⟩
  rw [← hb] at hu
  have hdist : dist (jet a ⟨p, hp⟩) (jet b ⟨p, hp⟩) ≤ ε :=
    (ContinuousMap.dist_apply_le_dist _).trans hu.le
  have hval : dist (F a p) (F b p) ≤ ε := (le_max_left _ _).trans hdist
  have hder : dist (fun i => partialDerivR4 i (F a) p) (fun i => partialDerivR4 i (F b) p) ≤ ε :=
    (le_max_right _ _).trans hdist
  refine ⟨by simpa [Real.dist_eq] using hval, fun i => ?_⟩
  have hi := (dist_le_pi_dist (fun i => partialDerivR4 i (F a) p)
    (fun i => partialDerivR4 i (F b) p) i).trans hder
  simpa [Real.dist_eq] using hi
variable (s : TorusSide)
private theorem contDiff_pullback {X : Ambient} {f : s.Point X → ℝ} (hf : f ∈ s.c1Set X) :
    ContDiff ℝ 1 (s.pullback f) := by
  cases X
  · exact hf
  · exact hf
private theorem partialD_sub (i : Fin 4) {X : Ambient} {f g : s.Point X → ℝ}
    (hf : f ∈ s.c1Set X) (hg : g ∈ s.c1Set X) :
    s.partialD i X (f - g) = s.partialD i X f - s.partialD i X g := by
  symm
  apply s.eq_partialD_of_pullback
  funext p
  have hdf : DifferentiableAt ℝ (s.pullback f) p :=
    (contDiff_pullback s hf).differentiable (by norm_num) p
  have hdg : DifferentiableAt ℝ (s.pullback g) p :=
    (contDiff_pullback s hg).differentiable (by norm_num) p
  have hf' := congrFun (s.pullback_partialD i X f) p
  have hg' := congrFun (s.pullback_partialD i X g) p
  have hsub : s.pullback (s.partialD i X f - s.partialD i X g) p =
      s.pullback (s.partialD i X f) p - s.pullback (s.partialD i X g) p := rfl
  have hpb : s.pullback (f - g) = s.pullback f - s.pullback g := rfl
  rw [hsub, hf', hg', hpb, partialDerivR4_eq_fderiv hdf, partialDerivR4_eq_fderiv hdg,
    partialDerivR4_eq_fderiv (hdf.sub hdg), fderiv_sub hdf hdg]
  rfl
private theorem uniformNorm_le_of_forall {Y : Type} [Nonempty Y] {φ : Y → ℝ} {δ : ℝ}
    (H : ∀ y, |φ y| ≤ δ) : TestFunctions.uniformNorm φ ≤ δ :=
  ciSup_le H
private theorem c1NormOn_sub_le (X : Ambient) {f g : s.Point X → ℝ} (hf : f ∈ s.c1Set X)
    (hg : g ∈ s.c1Set X) {δ : ℝ}
    (H : ∀ y, |f y - g y| ≤ δ ∧
      ∀ i, |s.partialD i X f y - s.partialD i X g y| ≤ δ) :
    s.c1NormOn X (f - g) ≤ δ := by
  have : Nonempty (s.Point X) := ⟨s.ambientProj X 0⟩
  rw [s.c1NormOn_eq_max]
  refine max_le (uniformNorm_le_of_forall fun y => (H y).1)
    (ciSup_le fun i => uniformNorm_le_of_forall fun y => ?_)
  rw [partialD_sub s i hf hg]
  exact (H y).2 i
private theorem exists_countable_dense_of_compact (X : Ambient) (Q : Set (s.Point X))
    {C : Set (Fin 4 → ℝ)} (hC : IsCompact C)
    (hcover : ∀ y : s.Point X, (∃ p ∈ C, s.ambientProj X p = y) ∨
      ∀ f ∈ s.c1VanishingOutside X Q, f y = 0 ∧ ∀ i, s.partialD i X f y = 0) :
    ∃ S : Set (s.Point X → ℝ), S ⊆ s.c1VanishingOutside X Q ∧ S.Countable ∧
      s.IsC1DenseIn X Q S := by
  obtain ⟨S, hScount, hS⟩ := exists_countable_c1_approx
    (fun f : s.c1VanishingOutside X Q => s.pullback f.1)
    (fun f => contDiff_pullback s f.2.1) hC
  refine ⟨Subtype.val '' S, ?_, hScount.image _, ?_⟩
  · rintro _ ⟨f, -, rfl⟩
    exact f.2
  · intro f hf ε hε
    obtain ⟨ψ, hψS, hψ⟩ := hS ⟨f, hf⟩ (ε / 2) (half_pos hε)
    refine ⟨ψ.1, ⟨ψ, hψS, rfl⟩, ?_⟩
    refine lt_of_le_of_lt (c1NormOn_sub_le s X hf.1 ψ.2.1 fun y => ?_) (half_lt_self hε)
    rcases hcover y with ⟨p, hp, rfl⟩ | hzero
    · obtain ⟨hval, hder⟩ := hψ p hp
      refine ⟨hval, fun i => ?_⟩
      have ef : s.partialD i X f (s.ambientProj X p) = partialDerivR4 i (s.pullback f) p :=
        congrFun (s.pullback_partialD i X f) p
      have eψ : s.partialD i X ψ.1 (s.ambientProj X p) =
          partialDerivR4 i (s.pullback ψ.1) p :=
        congrFun (s.pullback_partialD i X ψ.1) p
      rw [ef, eψ]
      exact hder i
    · obtain ⟨hf0, hfd⟩ := hzero f hf
      obtain ⟨hψ0, hψd⟩ := hzero ψ.1 ψ.2
      have hhalf : 0 ≤ ε / 2 := (half_pos hε).le
      refine ⟨by simpa [hf0, hψ0] using hhalf, fun i => ?_⟩
      simpa [hfd i, hψd i] using hhalf
private theorem length_pos : 0 < s.length := by apply _root_.YangMills.Construction.ToriAtArbitraryCouplings.DistanceAndProjection.length_pos <;> assumption
private theorem exists_preimage_mem_cube (y : s.Point .torus) :
    ∃ p ∈ Set.pi Set.univ (fun _ : Fin 4 => Set.Icc (0 : ℝ) s.length),
      s.ambientProj .torus p = y := by
  have hpos : 0 < s.length := length_pos s
  obtain ⟨p, rfl⟩ := TestFunctions.torusProj_surjective s.length y
  let r : Fin 4 → ℝ := fun i => toIcoMod hpos 0 (p i)
  let n : Fin 4 → ℤ := fun i => toIcoDiv hpos 0 (p i)
  have hp : p = r + TestFunctions.latticeTranslate s.length n := by
    funext i
    have h := self_sub_toIcoDiv_zsmul hpos (0 : ℝ) (p i)
    simp only [Pi.add_apply, TestFunctions.latticeTranslate, r, n]
    rw [← h, zsmul_eq_mul]
    ring
  refine ⟨r, fun i _ => ?_, ?_⟩
  · have h := toIcoMod_mem_Ico hpos (0 : ℝ) (p i)
    exact ⟨h.1, by simpa using h.2.le⟩
  · change TorusMetric.torusProj s.length r = TorusMetric.torusProj s.length p
    rw [hp, TestFunctions.torusProj_add_latticeTranslate]
private theorem isCompact_of_mem_euclidSupportFamily {Q : Set (Fin 4 → ℝ)}
    (hQ : Q ∈ euclidSupportFamily) : IsCompact Q := by apply _root_.YangMills.SharedProofs.p23763 <;> assumption
private theorem partialDerivR4_eq_zero_of_not_mem {Q : Set (Fin 4 → ℝ)} (hQ : IsClosed Q)
    {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hvan : ∀ p, p ∉ Q → f p = 0)
    {y : Fin 4 → ℝ} (hy : y ∉ Q) (i : Fin 4) : partialDerivR4 i f y = 0 := by
  have hev : f =ᶠ[nhds y] fun _ => 0 := by
    filter_upwards [hQ.isOpen_compl.mem_nhds hy] with p hp using hvan p hp
  rw [partialDerivR4_eq_fderiv (hf.differentiable (by norm_num) y), hev.fderiv_eq]
  simp
private theorem exists_countable_dense_euclidean {Q : Set (Fin 4 → ℝ)}
    (hQ : Q ∈ euclidSupportFamily) :
    ∃ S : Set (s.Point .euclidean → ℝ), S ⊆ s.c1VanishingOutside .euclidean Q ∧ S.Countable ∧
      s.IsC1DenseIn .euclidean Q S := by
  have hC : IsCompact Q := isCompact_of_mem_euclidSupportFamily hQ
  refine exists_countable_dense_of_compact s .euclidean Q hC fun y => ?_
  by_cases hy : y ∈ Q
  · exact Or.inl ⟨y, hy, rfl⟩
  · refine Or.inr fun f hf => ⟨hf.2 y hy, fun i => ?_⟩
    exact partialDerivR4_eq_zero_of_not_mem hC.isClosed hf.1 hf.2 hy i
theorem statement_holds : Statement := by
  intro s X Q hQ
  cases X
  · exact exists_countable_dense_of_compact s .torus Q
      (isCompact_univ_pi fun _ => isCompact_Icc) fun y => Or.inl (exists_preimage_mem_cube s y)
  · exact exists_countable_dense_euclidean s hQ
end C1SupportSeparable
end YangMills.Construction.ToriAtArbitraryCouplings
end

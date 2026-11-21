import YangMills.Construction.ToriAtArbitraryCouplings.ChoicesClosedUnderCountablyManyMaps
import YangMills.Construction.ToriAtArbitraryCouplings.ClassC1OnASupportIsComplete
import YangMills.Construction.ToriAtArbitraryCouplings.ClassC1OnASupportIsSeparable
import YangMills.Construction.ToriAtArbitraryCouplings.HypercubicMapsAndAdicTranslationsOnSupports
import YangMills.Construction.ToriAtArbitraryCouplings.NormsCuttingAndNeighbourhoods
import YangMills.Construction.ToriAtArbitraryCouplings.SupportsAreCompactAndCarryTheirClasses
import YangMills.Construction.ToriAtArbitraryCouplings.SupportsBetweenCompactAndOpenSets
import YangMills.Construction.ToriAtArbitraryCouplings.TheCountableSupportAdaptedFamily
import YangMills.Construction.ToriAtArbitraryCouplings.TheNormOfClassC1OnASupport
import YangMills.Construction.ToriAtArbitraryCouplings.TuplesOfAChoiceAreCountableAndSeparated
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace SupportAdaptedFamilyProof
variable {s : TorusSide} {E : Ambient}
theorem sub_mem_c1VanishingOutside (hN : C1NormOnSupport.Statement) {Q : Set (s.Point E)}
    (hQ : Q ∈ s.supportFamily E) {f g : s.Point E → ℝ} (hf : f ∈ s.c1VanishingOutside E Q)
    (hg : g ∈ s.c1VanishingOutside E Q) : f - g ∈ s.c1VanishingOutside E Q := by
  obtain ⟨-, hadd, hsmul, -⟩ := hN s E Q hQ
  have h := hadd f hf _ (hsmul (-1) g hg)
  simpa [sub_eq_add_neg] using h
theorem mem_c1SuppIn (hC : CompactSupports.Statement)
    {Q : Set (s.Point E)} (hQ : Q ∈ s.supportFamily E) {f : s.Point E → ℝ}
    (hf : f ∈ s.c1VanishingOutside E Q) : f ∈ s.c1SuppIn E Q := by
  rw [← (hC s E Q hQ).2]
  exact hf
theorem denseForNorm_iff (hC : CompactSupports.Statement)
    (hN : C1NormOnSupport.Statement) {m : ℕ}
    (hB : LipschitzEstimates.C1NormComparison s m E) {Q : Set (s.Point E)}
    (hQ : Q ∈ s.supportFamily E) {A : Set (s.Point E → ℝ)} (hA : A ⊆ s.c1VanishingOutside E Q) :
    (DenseForNorm (s.c1NormOn E) (s.c1VanishingOutside E Q) A ↔
      DenseForNorm (s.c1GradNorm E) (s.c1VanishingOutside E Q) A) ∧
    (DenseForNorm (s.c1NormOn E) (s.c1VanishingOutside E Q) A →
      DenseForNorm (s.sharpNormAt m E) (s.c1VanishingOutside E Q) A) := by
  have hb : ∀ f ∈ s.c1VanishingOutside E Q, ∀ φ ∈ A,
      s.c1NormOn E (f - φ) ≤ s.c1GradNorm E (f - φ) ∧
      s.c1GradNorm E (f - φ) ≤ 2 * s.c1NormOn E (f - φ) ∧
      s.sharpNormAt m E (f - φ) ≤ 40 * (cubeEdge s.L m : ℝ) * s.c1GradNorm E (f - φ) ∧
      40 * (cubeEdge s.L m : ℝ) * s.c1GradNorm E (f - φ) ≤
        80 * (cubeEdge s.L m : ℝ) * s.c1NormOn E (f - φ) := by
    intro f hf φ hφ
    have hm := mem_c1SuppIn hC hQ (sub_mem_c1VanishingOutside hN hQ hf (hA hφ))
    obtain ⟨-, -, -, -, a, b, c, d⟩ := hB (f - φ) ⟨hm.1, hm.2.1⟩
    exact ⟨a, b, c, d⟩
  have hM : (0 : ℝ) < (cubeEdge s.L m : ℝ) := by
    have h := one_le_cubeEdge s.admissible m
    have h' : (1 : ℝ) ≤ (cubeEdge s.L m : ℝ) := by exact_mod_cast h
    linarith
  refine ⟨⟨fun hd f hf ε hε => ?_, fun hd f hf ε hε => ?_⟩, fun hd f hf ε hε => ?_⟩
  · obtain ⟨φ, hφ, hlt⟩ := hd f hf (ε / 2) (by positivity)
    obtain ⟨-, b, -, -⟩ := hb f hf φ hφ
    exact ⟨φ, hφ, by linarith⟩
  · obtain ⟨φ, hφ, hlt⟩ := hd f hf ε hε
    obtain ⟨a, -, -, -⟩ := hb f hf φ hφ
    exact ⟨φ, hφ, by linarith⟩
  · obtain ⟨φ, hφ, hlt⟩ := hd f hf (ε / (80 * (cubeEdge s.L m : ℝ))) (by positivity)
    obtain ⟨-, -, c, d⟩ := hb f hf φ hφ
    refine ⟨φ, hφ, ?_⟩
    rw [lt_div_iff₀ (by positivity)] at hlt
    nlinarith
theorem supportsGiveSeparableBanach (hC : CompactSupports.Statement)
    (hN : C1NormOnSupport.Statement) (hComp : C1SupportComplete.Statement)
    (hSep : C1SupportSeparable.Statement) {m : ℕ}
    (hB : LipschitzEstimates.C1NormComparison s m E) :
    s.SupportsGiveSeparableBanach m E := by
  refine ⟨fun Q hQ => ⟨(hC s E Q hQ).1, (hC s E Q hQ).2, ?_, fun A hA => ?_⟩, ?_, fun D => ?_⟩
  · obtain ⟨h0, hadd, hsmul, hz, htri, hhom⟩ := hN s E Q hQ
    exact ⟨h0, hadd, hsmul, hz, htri, hhom, hComp s E Q hQ, hSep s E Q hQ⟩
  · exact denseForNorm_iff hC hN hB hQ hA
  · choose A hA using fun Q : s.supportFamily E => hSep s E Q.1 Q.2
    exact ⟨A, ⟨fun Q => (hA Q).2.1, fun Q => (hA Q).1, fun Q => (hA Q).2.2⟩⟩
  · constructor
    · intro h Q
      exact ⟨h.countable Q, h.subset Q,
        (denseForNorm_iff hC hN hB Q.2 (h.subset Q)).1.1 (h.dense Q)⟩
    · intro h
      exact ⟨fun Q => (h Q).1, fun Q => (h Q).2.1,
        fun Q => (denseForNorm_iff hC hN hB Q.2 (h Q).2.1).1.2 (h Q).2.2⟩
theorem countable_symmetryOrGridShift (s : TorusSide) (E : Ambient) :
    {r : Equiv.Perm (s.Point E) | s.IsSymmetryOrGridShift E r}.Countable := by
  have hcount : Countable TorusTransport.hyperoctahedral := by
    have hw : ∀ w : TorusTransport.hyperoctahedral, ∃ p : Equiv.Perm (Fin 4) × (Fin 4 → ℤˣ),
        w.1 = TorusLifts.signedCoordinateEquiv p.1 p.2 := fun w => by
      obtain ⟨π, σ, h⟩ := w.2
      exact ⟨(π, σ), h⟩
    choose g hg using hw
    exact Function.Injective.countable (f := g) fun a b hab =>
      Subtype.ext (by rw [hg a, hg b, hab])
  have hgrid : (PeriodicLattice.adicGridPoints s.L).Countable :=
    Set.countable_iUnion fun k =>
      (Set.countable_range fun n : ℤ => (n : ℝ) * PeriodicLattice.meshSize s.L (k : ℤ)).mono
        (by rintro x ⟨n, rfl⟩; exact ⟨n, rfl⟩)
  have hvec : {v : Fin 4 → ℝ | ∀ μ, v μ ∈ PeriodicLattice.adicGridPoints s.L}.Countable := by
    have h := Set.countable_univ_pi (fun _ : Fin 4 => hgrid)
    refine h.mono ?_
    intro v hv μ _
    exact hv μ
  refine ((Set.countable_range (s.symmetryPerm E)).union
    (hvec.image (s.shiftPerm E))).mono ?_
  rintro r (⟨w, rfl⟩ | ⟨v, hv, rfl⟩)
  · exact Or.inl ⟨w, rfl⟩
  · exact Or.inr ⟨v, hv, rfl⟩
theorem preservesSupports_of_isSymmetryOrGridShift
    (hS : LatticeSymmetriesOnSupports.Statement)
    {r : Equiv.Perm (s.Point E)} (hr : s.IsSymmetryOrGridShift E r) :
    LatticeSymmetriesOnSupports.PreservesSupports s E r := by
  obtain ⟨a, b, c, d⟩ := hS s
  cases E
  · rcases hr with ⟨w, rfl⟩ | ⟨v, hv, rfl⟩
    · exact a w
    · exact c v hv
  · rcases hr with ⟨w, rfl⟩ | ⟨v, hv, rfl⟩
    · exact b w
    · exact d v hv
theorem comp_symm_mem_c1VanishingOutside_image {r : Equiv.Perm (s.Point E)}
    (hr : LatticeSymmetriesOnSupports.PreservesSupports s E r) {Q : Set (s.Point E)}
    {f : s.Point E → ℝ} (hf : f ∈ s.c1VanishingOutside E Q) :
    f ∘ r.symm ∈ s.c1VanishingOutside E (r '' Q) := by
  refine ⟨hr.2.1 f hf.1, fun x hx => hf.2 _ fun hq => hx ⟨_, hq, r.apply_symm_apply x⟩⟩
theorem symm_mem_closedSupport {r : Equiv.Perm (s.Point E)}
    (hr : LatticeSymmetriesOnSupports.PreservesSupports s E r) {f : s.Point E → ℝ}
    {x : s.Point E} (hx : x ∈ s.closedSupport E (f ∘ r.symm)) :
    r.symm x ∈ s.closedSupport E f := by
  intro ρ hρ
  obtain ⟨y, hy, hlt⟩ := hx ρ hρ
  refine ⟨r.symm y, hy, ?_⟩
  have h := hr.2.2 (r.symm x) (r.symm y)
  simp only [Equiv.apply_symm_apply] at h
  exact lt_of_eq_of_lt h.symm hlt
theorem adaptedTupleSet_eq (hC : CompactSupports.Statement)
    (hBetween : SupportsBetweenCompactOpen.Statement)
    {D : s.supportFamily E → Set (s.Point E → ℝ)} (hD : s.IsStableDenseChoice E D) :
    s.adaptedTupleSet E D = {X | 1 ≤ X.length ∧ (∀ f ∈ X, f ∈ s.choiceComponents E D) ∧
      s.PairwiseDisjointSupp E X} := by
  have hsub : ∀ (Q : s.supportFamily E) (f : s.Point E → ℝ), f ∈ D Q →
      s.closedSupport E f ⊆ Q.1 :=
    fun Q f hf => (mem_c1SuppIn hC Q.2 (hD.isChoice.subset Q hf)).2.2
  ext X
  constructor
  · intro hX
    simp only [TorusSide.adaptedTupleSet, Set.mem_iUnion] at hX
    obtain ⟨n, hn, Q, φ, hdis, hφ, rfl⟩ := hX
    refine ⟨by simpa using hn, ?_, ?_⟩
    · intro f hf
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
      exact Set.mem_iUnion.2 ⟨Q i, hφ i⟩
    · refine List.pairwise_ofFn.2 fun i k hik => ?_
      exact (hdis hik.ne).mono (hsub _ _ (hφ i)) (hsub _ _ (hφ k))
  · rintro ⟨hlen, hent, hdis⟩
    have hmem : ∀ i : Fin X.length, X.get i ∈ s.choiceComponents E D :=
      fun i => hent _ (List.get_mem X i)
    have hcpt : ∀ i : Fin X.length, s.IsCompactWrt E (s.closedSupport E (X.get i)) :=
      fun i => by
        obtain ⟨Q, hQ⟩ := Set.mem_iUnion.1 (hmem i)
        exact (mem_c1SuppIn hC Q.2 (hD.isChoice.subset Q hQ)).2.1
    have hpair : Pairwise (Function.onFun Disjoint fun i : Fin X.length =>
        s.closedSupport E (X.get i)) := by
      have hp := List.pairwise_iff_get.1 hdis
      intro i k hik
      rcases lt_or_gt_of_ne hik with h | h
      · exact hp i k h
      · exact (hp k i h).symm
    obtain ⟨Q, hQ, hPQ, hQd⟩ := (hBetween s E).2 X.length
      (fun i => s.closedSupport E (X.get i))
      (fun _ => Set.univ) hcpt hpair (fun _ => fun _ _ => ⟨1, one_pos, fun _ _ => trivial⟩)
      (fun _ => Set.subset_univ _)
    simp only [TorusSide.adaptedTupleSet, Set.mem_iUnion]
    refine ⟨X.length, hlen, fun i => ⟨Q i, hQ i⟩, X.get, hQd, fun i => ?_, (List.ofFn_get X).symm⟩
    rw [hD.eq_inter]
    refine ⟨hmem i, ?_⟩
    obtain ⟨Q', hQ'⟩ := Set.mem_iUnion.1 (hmem i)
    have hm := mem_c1SuppIn hC Q'.2 (hD.isChoice.subset Q' hQ')
    rw [(hC s E (Q i) (hQ i)).2]
    exact ⟨hm.1, hm.2.1, (hPQ i).1⟩
theorem stableChoicesGiveStableTuples (hC : CompactSupports.Statement)
    (hBetween : SupportsBetweenCompactOpen.Statement)
    (hMaps : ChoicesStableUnderCountableMaps.Statement)
    (hS : LatticeSymmetriesOnSupports.Statement) :
    s.StableChoicesGiveStableTuples E := by
  refine ⟨?_, fun D hD => ⟨adaptedTupleSet_eq hC hBetween hD, fun r hr X hX => ?_,
    fun X hX Y hY hXY => ?_⟩⟩
  · obtain ⟨D, hch, hmaps, hsum, hint⟩ := hMaps s E _ (countable_symmetryOrGridShift s E)
      fun r hr Q hQ =>
        ⟨r '' Q, (preservesSupports_of_isSymmetryOrGridShift hS hr).1 Q hQ, fun f hf =>
          comp_symm_mem_c1VanishingOutside_image
            (preservesSupports_of_isSymmetryOrGridShift hS hr) hf⟩
    exact ⟨D, ⟨hch, fun r hr f hf => hmaps r hr f hf, hsum, hint⟩⟩
  · rw [adaptedTupleSet_eq hC hBetween hD] at hX ⊢
    obtain ⟨hlen, hent, hdis⟩ := hX
    refine ⟨by simpa using hlen, ?_, ?_⟩
    · intro g hg
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
      exact hD.comp_symm_mem r hr f (hent f hf)
    · refine List.pairwise_map.2 (hdis.imp fun {f g} hfg => ?_)
      refine Set.disjoint_left.2 fun x hxf hxg => ?_
      exact Set.disjoint_left.1 hfg
        (symm_mem_closedSupport (preservesSupports_of_isSymmetryOrGridShift hS hr) hxf)
        (symm_mem_closedSupport (preservesSupports_of_isSymmetryOrGridShift hS hr) hxg)
  · rw [adaptedTupleSet_eq hC hBetween hD] at hX hY ⊢
    refine ⟨?_, ?_, hXY⟩
    · have h := hX.1
      simp only [Ambient.append, List.length_append]
      omega
    · intro f hf
      rcases List.mem_append.1 hf with h | h
      · exact hX.2.1 f h
      · exact hY.2.1 f h
theorem claim (hLip : LipschitzEstimates.Combined)
    (hC : CompactSupports.Statement)
    (hN : C1NormOnSupport.Statement) (hComp : C1SupportComplete.Statement)
    (hSep : C1SupportSeparable.Statement)
    (hBetween : SupportsBetweenCompactOpen.Statement)
    (hTup : ChoiceTuplesCountableSeparated.Statement)
    (hMaps : ChoicesStableUnderCountableMaps.Statement)
    (hS : LatticeSymmetriesOnSupports.Statement) : SupportAdaptedFamily.Claim := by
  intro s hL m E
  have hB := (hLip s hL m E).1.1
  exact ⟨supportsGiveSeparableBanach hC hN hComp hSep hB, hBetween s E, fun D hD => hTup s E D hD,
    stableChoicesGiveStableTuples hC hBetween hMaps hS⟩
end SupportAdaptedFamilyProof
end YangMills.Construction.ToriAtArbitraryCouplings
end

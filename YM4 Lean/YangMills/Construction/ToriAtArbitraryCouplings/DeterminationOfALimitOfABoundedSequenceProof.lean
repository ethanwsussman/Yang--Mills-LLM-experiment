import YangMills.Construction.ToriAtArbitraryCouplings.ApproximationThatKeepsTheSeparation
import YangMills.Construction.ToriAtArbitraryCouplings.DeterminationOfALimitOfABoundedSequence
import YangMills.Construction.ToriAtArbitraryCouplings.NormsCuttingAndNeighbourhoods
import YangMills.Construction.ToriAtArbitraryCouplings.TheCountableSupportAdaptedFamily
import YangMills.Construction.TorusPowers.FromSmallBallsToAllSeparatedTuples
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace LimitDetermination
open TorusSide
variable {s : TorusSide}
private theorem evalOrZero_sub {n : ℕ} (P Q : s.sepOfLength .torus n → ℝ)
    (X : s.FnTuple .torus) :
    Ambient.evalOrZero (fun Y => P Y - Q Y) X = Ambient.evalOrZero P X - Ambient.evalOrZero Q X := by
  unfold Ambient.evalOrZero
  split_ifs <;> simp
private theorem isSeparatedMultilinear_sub {n : ℕ} {P Q : s.sepOfLength .torus n → ℝ}
    (hP : Ambient.IsSeparatedMultilinear s.asMirrorData .torus P)
    (hQ : Ambient.IsSeparatedMultilinear s.asMirrorData .torus Q) :
    Ambient.IsSeparatedMultilinear s.asMirrorData .torus fun Y => P Y - Q Y := by
  intro A hA f hf i g hg a b
  simp only [evalOrZero_sub]
  rw [hP A hA f hf i g hg a b, hQ A hA f hf i g hg a b]
  ring
private theorem coe_update_tuple {n : ℕ} {V : Fin n → Submodule ℝ (s.Point .torus → ℝ)}
    (u : ∀ l, V l) (i : Fin n) (x : V i) :
    (fun l => ((Function.update u i x l : V l) : s.Point .torus → ℝ)) =
      Function.update (fun l => (u l : s.Point .torus → ℝ)) i (x : s.Point .torus → ℝ) := by
  funext l
  by_cases h : l = i
  · subst h
    simp
  · simp [h]
private def multilinearRestriction {n : ℕ} {A : Fin n → Set (s.Point .torus)}
    (hA : s.PairwisePosSeparated .torus A) (Ψ : s.sepOfLength .torus n → ℝ)
    (hΨ : Ambient.IsSeparatedMultilinear s.asMirrorData .torus Ψ) :
    MultilinearMap ℝ (fun l => s.c1Submodule .torus (A l)) ℝ where
  toFun u := Ambient.evalOrZero Ψ (List.ofFn fun l => (u l : s.Point .torus → ℝ))
  map_update_add' := by
    intro inst u i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    have hlin := (s.isSeparatedMultilinear_iff .torus Ψ).1 hΨ A hA
    have hmem : ∀ l, Function.update (fun l => (u l : s.Point .torus → ℝ)) i
        (x : s.Point .torus → ℝ) l ∈ s.c1SuppIn .torus (A l) := fun l => by
      rw [← coe_update_tuple]
      exact (s.mem_c1Submodule_iff .torus _ _).1 (Function.update u i x l).2
    have h := hlin _ hmem i y ((s.mem_c1Submodule_iff .torus _ _).1 y.2) 1 1
    rw [Function.update_idem, Function.update_idem, Function.update_self] at h
    simp only [one_smul, one_mul] at h
    simp only [coe_update_tuple, Submodule.coe_add]
    exact h
  map_update_smul' := by
    intro inst u i a x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    have hlin := (s.isSeparatedMultilinear_iff .torus Ψ).1 hΨ A hA
    have hmem : ∀ l, Function.update (fun l => (u l : s.Point .torus → ℝ)) i
        (x : s.Point .torus → ℝ) l ∈ s.c1SuppIn .torus (A l) := fun l => by
      rw [← coe_update_tuple]
      exact (s.mem_c1Submodule_iff .torus _ _).1 (Function.update u i x l).2
    have h := hlin _ hmem i x ((s.mem_c1Submodule_iff .torus _ _).1 x.2) a 0
    rw [Function.update_idem, Function.update_idem, Function.update_self] at h
    simp only [zero_smul, add_zero, zero_mul] at h
    simp only [coe_update_tuple, Submodule.coe_smul, smul_eq_mul]
    exact h
private theorem multilinearRestriction_apply {n : ℕ} {A : Fin n → Set (s.Point .torus)}
    (hA : s.PairwisePosSeparated .torus A) (Ψ : s.sepOfLength .torus n → ℝ)
    (hΨ : Ambient.IsSeparatedMultilinear s.asMirrorData .torus Ψ)
    (u : (l : Fin n) → s.c1Submodule .torus (A l))
    (h : List.ofFn (fun l => (u l : s.Point .torus → ℝ)) ∈ s.sepOfLength .torus n) :
    multilinearRestriction hA Ψ hΨ u = Ψ ⟨_, h⟩ :=
  dif_pos h
private theorem mem_c1SuppIn_tsupport
    {g : AmbientPoints.Pt s.asMirrorData.toStandingParameters .torus → ℝ}
    (h : AmbientPoints.IsC1Fn g ∧ IsCompact (tsupport g)) :
    g ∈ s.c1SuppIn .torus
      (tsupport g : Set (AmbientPoints.Pt s.asMirrorData.toStandingParameters .torus)) :=
  (s.mem_c1Submodule_iff .torus _ _).1 ⟨h.1, h.2, subset_rfl⟩
private theorem list_ofFn_mem_sepOfLength {n : ℕ} {g : Fin n → s.Point .torus → ℝ}
    (hg : g ∈ AmbientPoints.separatedTuples s.asMirrorData.toStandingParameters .torus n) :
    List.ofFn g ∈ s.sepOfLength .torus n := by
  have hc := fun i => mem_c1SuppIn_tsupport (hg.1 i)
  refine (s.mem_sepOfLength_iff .torus n _).2 ⟨List.length_ofFn, ?_, ?_⟩
  · intro h hh
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hh
    exact ⟨(hc i).1, (hc i).2.1⟩
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact (hg.2 hij.ne).mono (hc i).2.2 (hc j).2.2
private theorem setDist_anti {A A' B B' : Set (s.Point .torus)} (hA : A' ⊆ A)
    (hB : B' ⊆ B) : s.setDist .torus A B ≤ s.setDist .torus A' B' :=
  le_iInf₂ fun a ha => le_iInf₂ fun b hb => iInf₂_le_of_le a (hA ha) (iInf₂_le b (hB hb))
private theorem le_setDist_of_le_gapAllLengths {d : ℝ≥0∞} {X : s.FnTuple .torus}
    (h : d ≤ s.gapAllLengths .torus X) {i k : Fin X.length} (hik : i ≠ k) :
    d ≤ s.setDist .torus (s.closedSupport .torus (X.get i)) (s.closedSupport .torus (X.get k)) := by
  rw [gapAllLengths_eq_supportGap] at h
  exact h.trans (iInf₂_le_of_le i k (iInf_le _ hik))
private theorem le_gapAllLengths_of_le_setDist {d : ℝ≥0∞} {X : s.FnTuple .torus}
    (h : ∀ i k : Fin X.length, i ≠ k →
      d ≤ s.setDist .torus (s.closedSupport .torus (X.get i)) (s.closedSupport .torus (X.get k))) :
    d ≤ s.gapAllLengths .torus X := by
  rw [gapAllLengths_eq_supportGap]
  exact le_iInf fun i => le_iInf fun k => le_iInf fun hik => h i k hik
private theorem exists_eq_list_ofFn {n : ℕ} (X : s.sepOfLength .torus n) :
    ∃ f : Fin n → s.Point .torus → ℝ, X.1 = List.ofFn f := by
  obtain ⟨X, hX⟩ := X
  obtain rfl : X.length = n := hX.1
  exact ⟨X.get, (List.ofFn_get X).symm⟩
private theorem sharpNormProduct_ofFn (m' : ℕ) {n : ℕ} (g : Fin n → s.Point .torus → ℝ) :
    s.sharpNormProduct m' .torus (List.ofFn g) = ∏ i, s.sharpNormAt m' .torus (g i) := by
  simp only [TorusSide.sharpNormProduct, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
private def evalOnPointTuples {n : ℕ} (Ψ : s.sepOfLength .torus n → ℝ) :
    AmbientPoints.separatedTuples s.asMirrorData.toStandingParameters .torus n → ℝ :=
  fun g => Ψ ⟨List.ofFn g.1, list_ofFn_mem_sepOfLength g.2⟩
private theorem isTupleMultilinear_evalOnPointTuples {n : ℕ} {Ψ : s.sepOfLength .torus n → ℝ}
    (hΨ : Ambient.IsSeparatedMultilinear s.asMirrorData .torus Ψ) :
    AmbientPoints.IsTupleMultilinear (evalOnPointTuples Ψ) := by
  intro A hA
  have hA' : s.PairwisePosSeparated .torus A := fun i j hij => pos_iff_ne_zero.2 (hA hij)
  exact ⟨multilinearRestriction hA' Ψ hΨ, fun g => multilinearRestriction_apply hA' Ψ hΨ g
    (list_ofFn_mem_sepOfLength
      (AmbientPoints.mem_separatedTuples_of_forall_mem_c1 hA fun i => (g i).2))⟩
private theorem boundedOnSmallBallTuples_sub {m' : ℕ} {C : ℕ → ℝ → ℝ} {hC : IsClusterConstant C}
    {S' S'' : Ambient.ConnectedFamily s.asMirrorData .torus}
    (h' : s.SatisfiesClusterBound m' hC.toClusterBound .torus S')
    (h'' : s.SatisfiesClusterBound m' hC.toClusterBound .torus S'')
    {n : ℕ} (hn : 2 ≤ n) {d : ℝ} (hd : 0 < d) :
    TorusPowers.BoundedOnSmallBallTuples (P := s.asMirrorData.toStandingParameters)
      (cubeEdge s.L m' : ℝ) d (2 * C n d) 5
      (evalOnPointTuples fun Y => S'.fn n hn Y - S''.fn n hn Y) := by
  intro u hsep hball
  have hℓ : 0 < s.length := s.length_pos
  have hRe : PeriodicLattice.torusSide s.asMirrorData.toStandingParameters.L
      s.asMirrorData.toStandingParameters.m / ((5 : ℕ) : ℝ) = s.length / 5 := by
    push_cast
    rfl
  rw [hRe] at hball
  have hR : s.length / 5 ∈ s.admissibleRadiusSet .torus :=
    ⟨by positivity, by linarith⟩
  have hcond : s.BallSupportedSeparated .torus d (s.length / 5) (List.ofFn u.1) := by
    refine ⟨fun f hf => ?_, fun i k hik => le_setDist_of_le_gapAllLengths hsep hik⟩
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    obtain ⟨x, hx⟩ := hball i
    exact ⟨_, ⟨⟨by positivity, by linarith⟩, x, rfl⟩,
      (mem_c1SuppIn_tsupport (u.2.1 i)).2.2.trans hx⟩
  have h1 := h' n hn d _ hd hR ⟨_, list_ofFn_mem_sepOfLength u.2⟩ hcond
  have h2 := h'' n hn d _ hd hR ⟨_, list_ofFn_mem_sepOfLength u.2⟩ hcond
  have e : s.sharpNormProduct m' .torus (List.ofFn u.1) =
      ∏ i, TestFunctions.sharpNormTorus (cubeEdge s.L m' : ℝ) (u.1 i) :=
    sharpNormProduct_ofFn m' u.1
  change _ ≤ C n d * s.sharpNormProduct m' .torus (List.ofFn u.1) at h1 h2
  rw [e] at h1 h2
  have h3 := abs_sub (S'.fn n hn ⟨_, list_ofFn_mem_sepOfLength u.2⟩)
    (S''.fn n hn ⟨_, list_ofFn_mem_sepOfLength u.2⟩)
  change |S'.fn n hn ⟨_, list_ofFn_mem_sepOfLength u.2⟩ -
    S''.fn n hn ⟨_, list_ofFn_mem_sepOfLength u.2⟩| ≤ _
  linarith
private theorem fn_eq_of_agree (hB : TorusPowers.SmallBallsToSeparatedTuples)
    (hAp : SeparatedApproximation.Statement)
    (hN : LipschitzEstimates.Combined) (hL : 8 * 105 ^ 4 ≤ s.L) (m' : ℕ)
    {C : ℕ → ℝ → ℝ} (hC : IsClusterConstant C)
    {D : s.supportFamily .torus → Set (s.Point .torus → ℝ)}
    (hD : s.IsCountableC1DenseChoice .torus D) {S' S'' : Ambient.ConnectedFamily s.asMirrorData .torus}
    (h' : s.SatisfiesClusterBound m' hC.toClusterBound .torus S')
    (h'' : s.SatisfiesClusterBound m' hC.toClusterBound .torus S'')
    (hag : ∀ X : s.adaptedTupleSetLengthGeTwo .torus D,
      s.evalOnAdaptedTuples S' X = s.evalOnAdaptedTuples S'' X)
    {n : ℕ} (hn : 2 ≤ n) (X : s.sepOfLength .torus n) : S'.fn n hn X = S''.fn n hn X := by
  obtain ⟨f, hfX⟩ := exists_eq_list_ofFn X
  obtain ⟨X, hX⟩ := X
  obtain rfl : X = List.ofFn f := hfX
  have hΨ := isSeparatedMultilinear_sub (S'.fn_multilinear n hn) (S''.fn_multilinear n hn)
  let Ψ : s.sepOfLength .torus n → ℝ := fun Y => S'.fn n hn Y - S''.fn n hn Y
  have hsep0 : 0 < s.gapAllLengths .torus (List.ofFn f) :=
    (hN s hL m' .torus).2.2.1.2 ⟨n, by omega⟩ _ ((hN s hL m' .torus).1.2.1.2 ⟨n, by omega⟩ hX)
  obtain ⟨d, hd, hdsep⟩ : ∃ d : ℝ, 0 < d ∧
      ENNReal.ofReal d ≤ s.gapAllLengths .torus (List.ofFn f) := by
    have he0 : 0 < min 1 (s.gapAllLengths .torus (List.ofFn f)) :=
      lt_min one_pos hsep0
    have het : min 1 (s.gapAllLengths .torus (List.ofFn f)) ≠ ⊤ :=
      (lt_of_le_of_lt (min_le_left _ _) ENNReal.one_lt_top).ne
    refine ⟨_, ENNReal.toReal_pos he0.ne' het, ?_⟩
    rw [ENNReal.ofReal_toReal het]
    exact min_le_right _ _
  have hd3 : 0 < d / 3 := by positivity
  obtain ⟨-, hdist, -, htend⟩ := hAp s hL m' .torus D hD n (by omega) f hX d hd hdsep 1 one_pos
  have hApos : s.PairwisePosSeparated .torus (s.supportThickening .torus f d) :=
    fun i k hik => lt_of_lt_of_le (ENNReal.ofReal_pos.2 hd3) (hdist i k hik)
  have hM : TorusPowers.IsPowerOfL s.asMirrorData.toStandingParameters (cubeEdge s.L m' : ℝ) :=
    ⟨m', by unfold cubeEdge; push_cast; rfl⟩
  have hc2 : 0 ≤ 2 * C n (d / 3) := mul_nonneg zero_le_two (hC.nonneg n hn _ hd3)
  obtain ⟨hall, hΘ⟩ := hB s.asMirrorData.toStandingParameters hL _ hM n hn (d / 3) _ hd3 hc2 5
    (by norm_num) (evalOnPointTuples Ψ) (isTupleMultilinear_evalOnPointTuples hΨ)
    (boundedOnSmallBallTuples_sub h' h'' hn hd3)
  have hc : 0 ≤ TorusPowers.smallBallConstant (cubeEdge s.L m' : ℝ) 5 ^ n * (2 * C n (d / 3)) :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hΘ) n) hc2
  have hApos' : Pairwise fun i j => AmbientPoints.PositivelySeparated
      s.asMirrorData.toStandingParameters .torus (s.supportThickening .torus f d i)
      (s.supportThickening .torus f d j) := fun i j hij => (hApos hij).ne'
  have hmemPT : ∀ g : Fin n → s.Point .torus → ℝ,
      (∀ i, g i ∈ s.c1Submodule .torus (s.supportThickening .torus f d i)) →
      g ∈ AmbientPoints.separatedTuples s.asMirrorData.toStandingParameters .torus n :=
    fun g hg => AmbientPoints.mem_separatedTuples_of_forall_mem_c1 hApos' hg
  have hLb : ∀ h : (i : Fin n) → s.c1Submodule .torus (s.supportThickening .torus f d i),
      |multilinearRestriction hApos Ψ hΨ h| ≤
        (TorusPowers.smallBallConstant (cubeEdge s.L m' : ℝ) 5 ^ n * (2 * C n (d / 3))) *
          ∏ l, s.sharpNormAt m' .torus (h l : s.Point .torus → ℝ) := by
    intro h
    have hp := hmemPT (fun i => (h i : s.Point .torus → ℝ)) fun i => (h i).2
    have hsepd : ENNReal.ofReal (d / 3) ≤
        s.gapAllLengths .torus (List.ofFn fun i => (h i : s.Point .torus → ℝ)) := by
      refine le_gapAllLengths_of_le_setDist fun i k hik => ?_
      rw [List.get_ofFn, List.get_ofFn]
      refine (hdist _ _ fun e => hik ?_).trans (setDist_anti
        ((s.mem_c1Submodule_iff .torus _ _).1 (h _).2).2.2
        ((s.mem_c1Submodule_iff .torus _ _).1 (h _).2).2.2)
      exact Fin.ext (by simpa [Fin.ext_iff] using e)
    rw [multilinearRestriction_apply hApos Ψ hΨ h (list_ofFn_mem_sepOfLength hp)]
    exact hall ⟨_, hp⟩ hsepd
  have key : ∀ ε : ℝ, 0 < ε → |Ψ ⟨_, hX⟩| ≤
      (TorusPowers.smallBallConstant (cubeEdge s.L m' : ℝ) 5 ^ n * (2 * C n (d / 3))) *
        s.approxDefect m' .torus f ε := by
    intro ε hε
    obtain ⟨-, -, ⟨φ, ⟨hφ, -⟩, hf, hφ', hform⟩, -⟩ :=
      hAp s hL m' .torus D hD n (by omega) f hX d hd hdsep ε hε
    have h := hform _ hc (multilinearRestriction hApos Ψ hΨ) hLb
    have hφsep : List.ofFn φ ∈ s.sepOfLength .torus n :=
      list_ofFn_mem_sepOfLength (hmemPT φ hφ')
    rw [multilinearRestriction_apply hApos Ψ hΨ _ hX,
      multilinearRestriction_apply hApos Ψ hΨ _ hφsep] at h
    have h0 : Ψ ⟨_, hφsep⟩ = 0 := by
      have hlen : (List.ofFn φ).length = n := List.length_ofFn
      have hr := hag ⟨List.ofFn φ, hφ, by rw [hlen]; exact hn⟩
      simp only [TorusSide.evalOnAdaptedTuples, hlen] at hr
      rw [S'.evalAt_of_mem hn hφsep, S''.evalAt_of_mem hn hφsep] at hr
      exact sub_eq_zero.2 hr
    rwa [h0, sub_zero] at h
  have hz : |Ψ ⟨_, hX⟩| ≤
      (TorusPowers.smallBallConstant (cubeEdge s.L m' : ℝ) 5 ^ n * (2 * C n (d / 3))) * 0 :=
    ge_of_tendsto (htend.const_mul _) (eventually_mem_nhdsWithin.mono fun ε hε => key ε hε)
  rw [mul_zero] at hz
  exact sub_eq_zero.1 (abs_nonpos_iff.1 hz)
theorem holds_proof (hF : SupportAdaptedFamily.Claim)
    (hB : TorusPowers.SmallBallsToSeparatedTuples)
    (hAp : SeparatedApproximation.Statement)
    (hN : LipschitzEstimates.Combined) : Holds := by
  intro s hL m' K β C h J _ F hlim hsym hobey
  refine ⟨fun D hD => ?_, fun D hD S' h' S'' h'' hag => ?_, ⟨hsym, ?_⟩,
    fun J' hJ' _ n hn X => ?_⟩
  · exact ((hF s hL m' .torus).2.2.1 D hD).1.mono fun X hX => hX.1
  · have hmap : S'.fn = S''.fn := by
      funext n hn X
      exact fn_eq_of_agree hB hAp hN hL m' h.isClusterConstant hD h'.2 h''.2 hag hn X
    obtain ⟨a, ha⟩ := S'
    obtain ⟨b, hb⟩ := S''
    obtain rfl : a = b := hmap
    rfl
  · intro n hn d R hd _ X hX
    have hb := hobey n hn d hd X (le_gapAllLengths_of_le_setDist hX.2)
    have e : ‖s.toComplexTupleFns F n hn X‖ = |F.fn n hn X| := by
      simp [TorusSide.toComplexTupleFns]
    rw [e] at hb
    exact hb
  · exact (hlim n hn X).mono_left (inf_le_inf_left _ (principal_mono.2 hJ'))
end LimitDetermination
end YangMills.Construction.ToriAtArbitraryCouplings
end

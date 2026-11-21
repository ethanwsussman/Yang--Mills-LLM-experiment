import YangMills.Construction.GrowingTori.TorusFunctionalsReadOnTuplesOfFourSpaceProof
import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes.FirstPartProofForm
import Mathlib
set_option autoImplicit false
open Set
open scoped NNReal ENNReal ComplexConjugate
section
set_option autoImplicit false
open Set
open scoped NNReal ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MomentsAlongSeq
open PeriodicSpace TorusTransport.TestFunctionOrders
open ReflectionSpaces (finiteUpperSequences)
variable {D : Setup}
theorem isLatticePowerScale_euclidParams (D : Setup) :
    GrowingDomains.IsLatticePowerScale D.euclidParams :=
  ⟨D.params.cubeExp, by
    show ((D.params.choice.M : ℕ) : ℝ) = ((D.params.L : ℕ) : ℝ) ^ D.params.cubeExp
    exact_mod_cast D.params.M_eq_pow⟩
theorem membersEqPeriodicClass_euclid (h : CitedFacts) (D : Setup) :
    NonlinearDomain.MembersEqPeriodicClass
      (symbolSetup D).toStandingParameters D.euclidParams :=
  ((h.multilinear (symbolSetup D)).2.2.2.2.2.2.2.2 D.euclidParams rfl).2.2.1
abbrev pnatIndex (j : ℕ+) : pnatIndices.carrier := ⟨j, Set.mem_univ j⟩
theorem mem_sepLipTuplesInBall_iff (h : CitedFacts) (S : ToriSequence D) (j : ℕ+) {q : ℕ}
    (f : Fin q → RealFn) :
    f ∈ sepLipTuplesInBall q (S.radius j) (S.radius_pos j) ↔
      f ∈ Kind.sepLipTuplesWithin D.euclidParams .euclidean q
        (Kind.centredBall D.euclidParams .euclidean (radiusSeq S (pnatIndex j))) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · constructor
    · intro _
      exact ⟨⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0⟩
    · intro _
      exact ⟨⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0⟩
  · have e := membersEqPeriodicClass_euclid h D (.ball (S.radius j) (S.radius_pos j)) q hq
    exact Set.ext_iff.1 e f
theorem centredSchwinger_eq_momentFun (h : CitedFacts) (S : ToriSequence D) {C : BoundFamily}
    {Ψ : Kind.BoundedPartialHierarchySeq D.euclidParams .euclidean pnatIndices (radiusSeq S) C}
    (hΨ : IsPartialHierarchySeqOf S C Ψ) (j : ℕ+) {q : ℕ} (f : Fin q → RealFn)
    (hf : f ∈ sepLipTuplesInBall q (S.radius j) (S.radius_pos j))
    (hf' : f ∈ Kind.sepLipTuplesWithin D.euclidParams .euclidean q
      (Kind.centredBall D.euclidParams .euclidean (radiusSeq S (pnatIndex j)))) :
    S.centred j f =
      ((Ψ.toPartialHierarchySeq.momentFun (pnatIndex j) ⟨f, hf'⟩ : ℝ) : ℂ) := by
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ := (h.cumulants D S).2.2.2.2.2 j
  have e1 := hΦ₂ q ⟨f, hf⟩
  have e2 : centredMomentOf Φ ⟨f, hf⟩ =
      Ψ.toPartialHierarchySeq.momentFun (pnatIndex j) ⟨f, hf'⟩ := by
    unfold centredMomentOf Kind.PartialHierarchySeq.momentFun
      Kind.FunctionalSystem.momentSum
    refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun B _ => ?_
    apply Complex.ofReal_injective
    refine (hΦ₁ B.1.card _ _).trans ?_
    have hb := hΨ (pnatIndex j) B.1.card (two_le_card_of_mem_singletonFree π.2 B.2)
      ⟨Kind.restrictTuple D.euclidParams .euclidean f B.1,
        Kind.restrictTuple_mem_sepLipTuplesWithin D.euclidParams .euclidean hf' B.1⟩
    exact hb.symm
  rw [← e2]
  exact e1
theorem mem_sepLipTuplesWithin_of_isDefinedAt (h : CitedFacts) (S : ToriSequence D) {n : ℕ}
    (hn : 2 ≤ n) {f : Fin n → RealFn} {j : ℕ+} (hf : S.Defined f j) :
    f ∈ Kind.sepLipTuplesWithin D.euclidParams .euclidean n
      (Kind.centredBall D.euclidParams .euclidean (radiusSeq S (pnatIndex j))) := by
  apply (mem_sepLipTuplesInBall_iff h S j f).1
  rw [sepLipTuplesInBall_eq_lipTuplesInBall D.L (by omega : 1 ≤ n)]
  exact hf
theorem tendsToPointwiseAlong (h : CitedFacts) (S : ToriSequence D) {C : BoundFamily}
    {Ψ : Kind.BoundedPartialHierarchySeq D.euclidParams .euclidean pnatIndices (radiusSeq S) C}
    (hΨ : IsPartialHierarchySeqOf S C Ψ) {J : Sequences.PNatIndexSet} {Ξ : D.LimitHierarchy}
    (hΞ : S.IsLimitHierarchy J Ξ) :
    Ψ.toPartialHierarchySeq.TendsToPointwiseAlong J (Set.subset_univ _) Ξ.func := by
  intro n hn f
  obtain ⟨j', hj'⟩ := hΞ n hn f 1 one_pos
  have hmem : ∀ j : (J.filterGe j').carrier, f.1 ∈ Kind.sepLipTuplesWithin D.euclidParams
      .euclidean n (Kind.centredBall D.euclidParams .euclidean
        (radiusSeq S ⟨j.1, Set.subset_univ _ j.2.1⟩)) :=
    fun j => mem_sepLipTuplesWithin_of_isDefinedAt h S hn (hj' j.1 j.2.1 j.2.2).choose
  refine ⟨j', hmem, fun ε hε => ?_⟩
  obtain ⟨j'', hj''⟩ := hΞ n hn f ε hε
  refine ⟨j'', fun j hj hle hj₂ => ?_⟩
  obtain ⟨g, hg⟩ := hj'' j hj hle
  have e := hΨ (pnatIndex j) n hn ⟨f.1, hmem ⟨j, hj₂⟩⟩
  refine lt_of_eq_of_lt ?_ hg
  exact congrArg (fun z : ℂ => ‖z - ((Ξ.func n hn f : ℝ) : ℂ)‖) e
theorem tendsToWhereDefined_of_momentsTendTo (h : CitedFacts) (S : ToriSequence D)
    {C : BoundFamily}
    {Ψ : Kind.BoundedPartialHierarchySeq D.euclidParams .euclidean pnatIndices (radiusSeq S) C}
    (hΨ : IsPartialHierarchySeqOf S C Ψ) {J : Sequences.PNatIndexSet} {q : ℕ}
    (H : ℕ+ → Fin q → RealFn) (z : ℝ)
    (hm : Ψ.toPartialHierarchySeq.MomentsTendToAlong J (Set.subset_univ _)
      (fun j => H j.1) z) :
    DiagonalLimits.TendsToWhereDefined J
      (fun j => H j ∈ sepLipTuplesInBall q (S.radius j) (S.radius_pos j))
      (fun j _ => S.centred j (H j)) ((z : ℝ) : ℂ) := by
  obtain ⟨j', hF, hc⟩ := hm
  intro ε hε
  obtain ⟨j'', hj''⟩ := hc ε hε
  refine ⟨max j' j'', fun j hj hle => ?_⟩
  have hjA : j ∈ (J.filterGe j').carrier := ⟨hj, (le_max_left _ _).trans hle⟩
  have hmem := hF ⟨j, hjA⟩
  have hb := (mem_sepLipTuplesInBall_iff h S j (H j)).2 hmem
  refine ⟨hb, ?_⟩
  have e := centredSchwinger_eq_momentFun h S hΨ j (H j) hb hmem
  exact (congrArg (fun w : ℂ => ‖w - ((z : ℝ) : ℂ)‖) e).trans_lt
    (hj'' j hj ((le_max_right _ _).trans hle) hjA)
theorem momentFunOfSep_eval_eq (Ξ : D.LimitHierarchy) {q : ℕ} (f : D.sepDomain q) :
    Kind.momentFunOfSep Ξ.func f = Ξ.partitionMoment f :=
  rfl
theorem centredMomentsConverge (h : CitedFacts) (S : ToriSequence D) (C : BoundFamily)
    {J : Sequences.PNatIndexSet} {Ξ : D.LimitHierarchy} (_hJ : S.IsConvergenceSet C J)
    (hΞ : S.IsLimitHierarchy J Ξ)
    (Ψ : Kind.BoundedPartialHierarchySeq D.euclidParams .euclidean pnatIndices (radiusSeq S) C)
    (hΨ : IsPartialHierarchySeqOf S C Ψ) : CentredMomentsConverge S J Ξ := by
  have hC := ((h.moments).2 D.euclidParams (isLatticePowerScale_euclidParams D)).2.2 C pnatIndices
    (radiusSeq S) Ψ J (Set.subset_univ _) Ξ.func (tendsToPointwiseAlong h S hΨ hΞ)
  refine ⟨fun q f => ?_, ?_⟩
  · rw [← momentFunOfSep_eval_eq]
    exact tendsToWhereDefined_of_momentsTendTo h S hΨ (fun _ => f.1) _ (hC.1 q f)
  · intro q hq d R hd hR A hA f H hf hH hlim
    obtain ⟨hf', hmc⟩ := hC.2 q hq d R hd hR A hA f.1 (fun j => H j.1) hf (fun j => hH j.1)
      (fun l ε hε => by
        obtain ⟨j', hj'⟩ := hlim l ε hε
        refine ⟨j', fun j hj hle hj₂ => ?_⟩
        have e := hj' j hj hle
        show ‖(((Kind.sharpNormQ D.euclidParams .euclidean (H j l - f.1 l)).toReal : ℝ) : ℂ) - 0‖ < ε
        rw [sub_zero, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
        exact e)
    rw [← momentFunOfSep_eval_eq]
    exact tendsToWhereDefined_of_momentsTendTo h S hΨ H _ hmc
theorem mem_lipTuplesBall_of_mem {q : ℕ} {ρ : ℝ} {hρ : 0 < ρ}
    {f : Fin q → RealFn} (hf : f ∈ sepLipTuplesInBall q ρ hρ) :
    f ∈ BallTuples.lipTuplesBall q ρ :=
  ⟨hf.1, fun l => ⟨hf.1.2.1 l, hf.2 l⟩⟩
theorem eventuallyAlong_sum {J : Sequences.PNatIndexSet} {n : ℕ} (c : Fin n → ℂ)
    (P : Fin n → ℕ+ → Prop) (x : ∀ b j, P b j → ℂ) (z : Fin n → ℂ)
    (hx : ∀ b, DiagonalLimits.TendsToWhereDefined J (P b) (x b) (z b)) {ε : ℝ}
    (hε : 0 < ε) :
    DiagonalLimits.EventuallyAlong J fun j =>
      ∃ h : ∀ b, P b j, ‖∑ b, c b * x b j (h b) - ∑ b, c b * z b‖ < ε := by
  have hA : 0 ≤ ∑ b, ‖c b‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set A := ∑ b, ‖c b‖ with hAdef
  have hδ : 0 < ε / (A + 1) := by positivity
  choose j₁ hj₁ using fun b => hx b _ hδ
  refine ⟨∑ b, |j₁ b|, fun j hj hle => ?_⟩
  have hb : ∀ b, ∃ h : P b j, ‖x b j h - z b‖ < ε / (A + 1) := fun b =>
    hj₁ b j hj ((le_abs_self _).trans
      ((Finset.single_le_sum (f := fun b => |j₁ b|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ b)).trans hle))
  choose h hh using hb
  refine ⟨h, ?_⟩
  rw [← Finset.sum_sub_distrib]
  have h₁ : ‖∑ b, (c b * x b j (h b) - c b * z b)‖ ≤ ∑ b, ‖c b‖ * (ε / (A + 1)) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => by
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left (hh b).le (norm_nonneg _))
  rw [← Finset.sum_mul] at h₁
  have h₂ : A * (ε / (A + 1)) < ε := by
    have e : A * (ε / (A + 1)) = ε * (A / (A + 1)) := by ring
    have h₃ : A / (A + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    rw [e]
    nlinarith
  exact h₁.trans_lt h₂
theorem momentExtensionAt_sum {Ξ : D.LimitHierarchy} (hE : MomentLinearExtension Ξ) (q : ℕ)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (T : ι → OrderedTestFun q)
    (hT : ∀ i, T i ∈ sepTensorSubmodule D.euclidParams Set.univ q) :
    momentExtensionAt Ξ ⟨q, ∑ i ∈ s, c i • T i⟩ = ∑ i ∈ s, c i * momentExtensionAt Ξ ⟨q, T i⟩ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h₀ := hE.is_linear q 0 0 0 0 (Submodule.zero_mem _) (Submodule.zero_mem _)
    simp only [smul_zero, add_zero, zero_mul] at h₀
    simpa using h₀
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have h₁ := hE.is_linear q (T i) (∑ i ∈ s, c i • T i) (c i) 1 (hT i)
      (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hT k))
    rw [one_smul, one_mul, ih] at h₁
    exact h₁
theorem tensorMoment_zero (h : CitedFacts) (S : ToriSequence D) (j : ℕ+)
    (F : OrderedTestFun 0) : S.tensorMoment j F = F := by
  have e := (h.polynomials D (S.K j) (S.m j) (S.β j) (S.β_pos j)).tensorMoment_linComb 0 1
    (fun _ => F) (fun _ => fun i => i.elim0)
    (fun _ => ⟨⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0⟩)
  have e₁ : CentredTensorMoments.TorusFunctionals.linComb (q := 0)
      (fun _ : Fin 1 => F) (fun _ => CentredTensorMoments.realTupleTensor
        (fun i => i.elim0)) = F := by
    simp [CentredTensorMoments.TorusFunctionals.linComb,
      CentredTensorMoments.realTupleTensor, CentredTensorMoments.tupleTensor]
  rw [e₁] at e
  refine e.trans ?_
  simp [Setup.centredOnFourSpace]
theorem tensorMoment_tendsTo (h : CitedFacts) (S : ToriSequence D) {J : Sequences.PNatIndexSet}
    {Ξ : D.LimitHierarchy} (hM : CentredMomentsConverge S J Ξ) (hE : MomentLinearExtension Ξ) :
    ∀ (q : ℕ) (F : OrderedTestFun q),
      F ∈ sepTensorSubmodule D.euclidParams Set.univ q →
      DiagonalLimits.TendsToWhereDefined J (fun _ => True)
        (fun j _ => S.tensorMoment j F) (momentExtensionAt Ξ ⟨q, F⟩) := by
  intro q F hF
  cases q with
  | zero =>
    intro ε hε
    refine ⟨0, fun j _ _ => ⟨trivial, ?_⟩⟩
    show ‖S.tensorMoment j F - momentExtensionAt Ξ ⟨0, F⟩‖ < ε
    rw [tensorMoment_zero h S j F, hE.at_zero, sub_self, norm_zero]
    exact hε
  | succ q =>
    have hF' : F ∈ sepTensorSpanOn D.euclidParams (q + 1) Set.univ := hF
    obtain ⟨n, c, g, hg⟩ := (Submodule.mem_span_set'
      (M := (Fin (q + 1) → Kind.euclidean.Pt D.euclidParams) → ℂ)).1 hF'
    choose X hX hXe using fun b => (g b).2
    let Xs : Fin n → D.sepDomain (q + 1) := fun b => ⟨X b, (hX b).1⟩
    let T : Fin n → (Fin (q + 1) → Fin 4 → ℝ) → ℂ := fun b =>
      TensorExtension.realTensor D.euclidParams (X b)
    have hFT : (F : (Fin (q + 1) → Fin 4 → ℝ) → ℂ) = ∑ b, c b • T b := by
      refine hg.symm.trans (Finset.sum_congr rfl fun b _ => ?_)
      rw [hXe b]
      rfl
    have hval : momentExtensionAt Ξ ⟨q + 1, F⟩ =
        ∑ b, c b * ((Ξ.partitionMoment (Xs b) : ℝ) : ℂ) := by
      refine (congrArg (fun G => momentExtensionAt Ξ ⟨q + 1, G⟩) hFT).trans ?_
      refine (momentExtensionAt_sum hE (q + 1) Finset.univ c T fun b =>
        realTensor_mem_sepTensorSpanOn D.euclidParams (Xs b)).trans ?_
      exact Finset.sum_congr rfl fun b _ => by rw [hE.at_tensor q (Xs b)]
    have hFc : F = CentredTensorMoments.TorusFunctionals.linComb c
        fun b => CentredTensorMoments.realTupleTensor (X b) := by
      refine hFT.trans ?_
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    intro ε hε
    obtain ⟨j', hj'⟩ := eventuallyAlong_sum c _ _ _ (fun b => hM.atFixed (q + 1) (Xs b)) hε
    refine ⟨j', fun j hj hle => ?_⟩
    obtain ⟨hb, hlt⟩ := hj' j hj hle
    refine ⟨trivial, ?_⟩
    have e : S.tensorMoment j F = ∑ b, c b * S.centred j (X b) := by
      rw [hFc]
      exact (h.polynomials D (S.K j) (S.m j) (S.β j) (S.β_pos j)).tensorMoment_linComb (q + 1) n c
        X fun b => mem_lipTuplesBall_of_mem (hb b)
    show ‖S.tensorMoment j F - momentExtensionAt Ξ ⟨q + 1, F⟩‖ < ε
    rw [e, hval]
    exact hlt
theorem sharpNormQ_eq_ennSharpNorm {f : RealFn}
    (hl : TorusTransport.Domain.euclidean.LipschitzOn (symbolSetup D) f) :
    Kind.sharpNormQ D.euclidParams .euclidean f =
      TorusTransport.Domain.euclidean.ennSharpNorm (symbolSetup D) f := by
  have hdist : Kind.quotDist D.euclidParams .euclidean =
      TorusTransport.Domain.euclidean.pointDist (symbolSetup D) := by
    funext x y
    exact BallPeriodization.quotDist_euclidean D.euclidParams x y
  have hM : (0 : ℝ) ≤ 40 * D.euclidParams.M := by
    have := D.euclidParams.one_le_M
    linarith
  unfold Kind.sharpNormQ TorusTransport.Domain.ennSharpNorm
  refine congrArg₂ max rfl ?_
  have e : Kind.lipConstQ D.euclidParams .euclidean f = TestFunctions.bestLipschitzConstant
      (TorusTransport.Domain.euclidean.pointDist (symbolSetup D)) f := by
    unfold Kind.lipConstQ
    rw [hdist]
    rfl
  rw [ENNReal.ofReal_mul hM, e,
    TorusTransport.Domain.euclidean.ofReal_bestLipschitzConstant_eq_lipConst (symbolSetup D) hl]
  rfl
theorem setsInBallsSeparated_of_isAdmissibleSets {k : ℕ+} {d R : ℝ} {hd : 0 < d}
    {hR : 0 < R} {A : Fin k → Set (Fin 4 → ℝ)}
    (hA : TorusTransport.IsAdmissibleSets (symbolSetup D) d R hd hR A) :
    Kind.SetsInBallsSeparated D.euclidParams .euclidean d R A := by
  have hdist : Kind.quotDist D.euclidParams .euclidean =
      TorusTransport.Domain.euclidean.pointDist (symbolSetup D) := by
    funext x y
    exact BallPeriodization.quotDist_euclidean D.euclidParams x y
  refine ⟨fun l => ?_, fun l l' hll => ?_⟩
  · obtain ⟨x, hx⟩ := hA.1 l
    refine ⟨Kind.closedBallAbout D.euclidParams .euclidean x R, ⟨hR, x, rfl⟩, fun y hy => ?_⟩
    have hy' := hx hy
    show Kind.quotDist D.euclidParams .euclidean y x ≤ R
    rw [hdist]
    exact hy'
  · have h₁ := hA.2 l l' hll
    show ENNReal.ofReal d ≤ Kind.setInfDist D.euclidParams .euclidean (A l) (A l')
    unfold Kind.setInfDist
    rw [hdist]
    exact h₁
theorem symbolMoments_isScaleBounded (h : CitedFacts) {C : BoundFamily} {Ξ : D.LimitHierarchy}
    (hΞ : Ξ ∈ boundedEuclidHierarchies D.euclidParams C) :
    TimeAxisSymbols.IsScaleBounded (symbolMoments Ξ) (momentBoundNN C) := by
  intro k d R hd hR f hf
  have hsym := TorusTransport.TupleVectors.admissibleSepTuples_subset
    (symbolSetup D) hd hR hf
  have hadm : TorusTransport.FamilyIsAdmissible (symbolSetup D) d R hd hR f := by
    rcases hf with he | hf
    · have h₀ : (k : ℕ) = 0 := congrArg Sigma.fst he
      exact absurd h₀ k.pos.ne'
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hf
      obtain ⟨f', ⟨-, hf'⟩, e⟩ := hn
      obtain rfl : n = k := PNat.eq (congrArg Sigma.fst e)
      obtain rfl : f' = f := eq_of_heq (Sigma.mk.inj_iff.1 e).2
      exact hf'
  obtain ⟨hl, -, -, -, -⟩ :=
    (TorusTransport.TupleVectors.mem_sepTuples_iff (symbolSetup D) _ _).mp hsym
  have hs := SymbolSequences.components_mem_sepC1Tuples D.euclidParams ⟨_, hsym⟩
  have hbd := (((h.moments).2 D.euclidParams (isLatticePowerScale_euclidParams D)).1 C Ξ hΞ k
    k.pos d R hd hR _ (setsInBallsSeparated_of_isAdmissibleSets hadm)).2.1.1 ⟨f, hs⟩
    (fun l _ => ?_)
  · have e : ∏ l, Kind.sharpNormQ D.euclidParams .euclidean (f l) =
        ∏ l, TorusTransport.Domain.euclidean.ennSharpNorm (symbolSetup D) (f l) :=
      Finset.prod_congr rfl fun l _ => sharpNormQ_eq_ennSharpNorm (hl l)
    rw [e] at hbd
    exact hbd
  · refine ⟨hs.1 l, hs.2.1 l, ?_⟩
    rw [BallTuples.supportQ_euclidean]
    exact subset_rfl
end YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MomentsAlongSeq
end
end
section
set_option autoImplicit false
open Set
open scoped NNReal ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.SymbolPairing
open PeriodicSpace TorusTransport.TestFunctionOrders
open ReflectionSpaces (finiteUpperSequences)
variable {D : Setup}
theorem mem_separatedMembers_iff (D : Setup) {q : ℕ} (f : Fin q → RealFn) :
    f ∈ TestTupleClass.sep.members (symbolSetup D).toStandingParameters q ↔
      f ∈ D.sepDomain q :=
  (mem_sepTuplesR4_iff _ f).trans (BallTuples.mem_sepC1Tuples_euclidean_iff f).symm
def classMoment (Ξ : D.LimitHierarchy) (q : ℕ) :
    TestTupleClass.sep.members (symbolSetup D).toStandingParameters q → ℝ :=
  fun f => Ξ.partitionMoment ⟨f.1, (mem_separatedMembers_iff D f.1).1 f.2⟩
theorem classMoment_symm_multilinear (h : CitedFacts) (Ξ : D.LimitHierarchy) (q : ℕ)
    (hq : 1 ≤ q) :
    IsClassSymmetric (symbolSetup D).toStandingParameters .sep (classMoment Ξ q) ∧
      IsClassMultilinear (symbolSetup D) .sep hq (classMoment Ξ q) := by
  obtain ⟨-, -, -, -, -, -, -, -, hY⟩ := h.multilinear (symbolSetup D)
  exact (hY D.euclidParams rfl).1 Ξ q hq (classMoment Ξ q) fun _ _ _ => rfl
theorem exists_isMomentExtension (h : CitedFacts) (Ξ : D.LimitHierarchy) (q : ℕ) :
    ∃ T, IsMomentExtension Ξ (q := q + 1) T := by
  obtain ⟨-, ⟨T, hT, -⟩⟩ := h.extension (symbolSetup D) D.euclidParams (q + 1) (by omega)
    (classMoment Ξ (q + 1)) (classMoment_symm_multilinear h Ξ (q + 1) (by omega)).2
  refine ⟨T, fun X => ?_⟩
  obtain ⟨_, hX⟩ := hT ⟨X.1, (mem_separatedMembers_iff D X.1).2 X.2⟩
  exact hX
theorem isMomentExtension_momentExtension (h : CitedFacts) (Ξ : D.LimitHierarchy) (q : ℕ) :
    IsMomentExtension Ξ (q := q + 1) (momentExtension Ξ (q + 1)) :=
  Classical.epsilon_spec (exists_isMomentExtension h Ξ q)
theorem momentLinearExtension_holds (h : CitedFacts) (Ξ : D.LimitHierarchy) :
    MomentLinearExtension Ξ where
  at_zero c := by
    have hc : c ∈ sepTensorSubmodule D.euclidParams Set.univ 0 := Submodule.mem_top
    exact dif_pos hc
  at_tensor q X := by
    have hX : TensorExtension.realTensor D.euclidParams X.1 ∈
        sepTensorSubmodule D.euclidParams Set.univ (q + 1) :=
      realTensor_mem_sepTensorSpanOn D.euclidParams X
    exact (dif_pos hX).trans (isMomentExtension_momentExtension h Ξ q X)
  is_linear q F G a b hF hG := by
    have hs : a • F + b • G ∈ sepTensorSubmodule D.euclidParams Set.univ q :=
      Submodule.add_mem _ (Submodule.smul_mem _ a hF) (Submodule.smul_mem _ b hG)
    simp only [momentExtensionAt]
    rw [dif_pos hs, dif_pos hF, dif_pos hG]
    have e : (⟨a • F + b • G, hs⟩ : sepTensorSubmodule D.euclidParams Set.univ q) =
        a • ⟨F, hF⟩ + b • ⟨G, hG⟩ := rfl
    rw [e, map_add, map_smul, map_smul]
    rfl
open TimeAxisSymbols in
theorem symbolMoments_isNormedSymmMultilinear (h : CitedFacts) (Ξ : D.LimitHierarchy) :
    IsNormedSymmMultilinear (symbolMoments Ξ) where
  unit_eq_one := SymbolSequences.momentOnSymbol_unitSymbol Ξ
  multilinear k := by
    have hk : 1 ≤ (k : ℕ) := k.pos
    have hm := (classMoment_symm_multilinear h Ξ k hk).2
    have conv : ∀ f : Fin k → RealFn, f ∈ symbolsOfCard (symbolSetup D) k →
        f ∈ TestTupleClass.sep.members (symbolSetup D).toStandingParameters k := fun f hf =>
      (mem_separatedMembers_iff D f).2
        (SymbolSequences.components_mem_sepC1Tuples D.euclidParams (ofSepTuple f hf))
    intro i f f' hne c c' hmem
    exact hm i ⟨f.1, conv _ f.2⟩ ⟨f'.1, conv _ f'.2⟩ hne c c' (conv _ hmem)
  symmetric k := by
    have hk : 1 ≤ (k : ℕ) := k.pos
    have hs := (classMoment_symm_multilinear h Ξ k hk).1
    have conv : ∀ f : Fin k → RealFn, f ∈ symbolsOfCard (symbolSetup D) k →
        f ∈ TestTupleClass.sep.members (symbolSetup D).toStandingParameters k := fun f hf =>
      (mem_separatedMembers_iff D f).2
        (SymbolSequences.components_mem_sepC1Tuples D.euclidParams (ofSepTuple f hf))
    intro f σ
    exact (hs σ ⟨f.1, conv _ f.2⟩).symm
end YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.SymbolPairing
end
end
section
set_option autoImplicit false
open Set
open scoped NNReal ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.SymbolPairing
open ReflectionSpaces (finiteUpperSequences)
open PeriodicSpace TorusTransport.TestFunctionOrders
abbrev axisReflect (μ : Fin 4) (c : ℝ) : Equiv.Perm (Fin 4 → ℝ) :=
  BallPeriodization.hyperplaneReflection μ c
theorem axisReflect_apply_self (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    axisReflect μ c x μ = 2 * c - x μ := by apply _root_.YangMills.Construction.CentredTensorMoments.TorusFunctionals.axisRefl_apply_self <;> assumption
theorem axisReflect_axisReflect (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    axisReflect μ c (axisReflect μ c x) = x := by apply _root_.YangMills.Construction.CentredTensorMoments.TorusFunctionals.axisRefl_axisRefl <;> assumption
theorem contDiff_axisReflect (μ : Fin 4) (c : ℝ) : ContDiff ℝ 1 (axisReflect μ c) := by
  have e : (axisReflect μ c : (Fin 4 → ℝ) → Fin 4 → ℝ) =
      fun x => x - (2 * (x μ - c)) • PeriodicLattice.coordVec μ :=
    funext fun x => BallPeriodization.hyperplaneReflection_apply μ c x
  rw [e]
  exact contDiff_id.sub ((contDiff_const.mul ((contDiff_apply ℝ ℝ μ).sub contDiff_const)).smul
    contDiff_const)
def axisReflectHomeomorph (μ : Fin 4) (c : ℝ) : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toFun := axisReflect μ c
  invFun := axisReflect μ c
  left_inv := axisReflect_axisReflect μ c
  right_inv := axisReflect_axisReflect μ c
  continuous_toFun := (contDiff_axisReflect μ c).continuous
  continuous_invFun := (contDiff_axisReflect μ c).continuous
theorem tsupport_comp_axisReflect (μ : Fin 4) (c : ℝ) (f : RealFn) :
    tsupport (f ∘ axisReflect μ c) = axisReflect μ c ⁻¹' tsupport f :=
  tsupport_comp_eq_preimage f (axisReflectHomeomorph μ c)
variable (Y : Params)
theorem mem_sepC1Tuples_euclidean_iff' {n : ℕ} (f : Fin n → RealFn) :
    f ∈ Kind.sepC1Tuples Y .euclidean n ↔
      (∀ l, ContDiff ℝ 1 (f l)) ∧ (∀ l, IsCompact (tsupport (f l))) ∧
        ∀ l l', l ≠ l' → Disjoint (tsupport (f l)) (tsupport (f l')) :=
  BallTuples.mem_sepC1Tuples_euclidean_iff f
theorem supportQ_euclidean_eq_tsupport (f : RealFn) :
    Kind.supportQ Y .euclidean f = tsupport f :=
  BallTuples.supportQ_euclidean Y f
variable {Y}
theorem comp_axisReflect_mem {n : ℕ} {f : Fin n → RealFn} (μ : Fin 4) (c : ℝ)
    (hf : f ∈ Kind.sepC1Tuples Y .euclidean n) :
    (fun i => f i ∘ axisReflect μ c) ∈ Kind.sepC1Tuples Y .euclidean n := by
  obtain ⟨h₁, h₂, h₃⟩ := (mem_sepC1Tuples_euclidean_iff' Y f).1 hf
  refine (mem_sepC1Tuples_euclidean_iff' Y _).2 ⟨fun l => (h₁ l).comp (contDiff_axisReflect μ c),
    fun l => ?_, fun l l' hl => ?_⟩
  · rw [tsupport_comp_axisReflect]
    exact (axisReflectHomeomorph μ c).isCompact_preimage.2 (h₂ l)
  · rw [tsupport_comp_axisReflect, tsupport_comp_axisReflect]
    exact (h₃ l l' hl).preimage _
theorem finAppend_mem {p q : ℕ} {f : Fin p → RealFn}
    {g : Fin q → RealFn} (hf : f ∈ Kind.sepC1Tuples Y .euclidean p)
    (hg : g ∈ Kind.sepC1Tuples Y .euclidean q)
    (hd : ∀ i j, Disjoint (tsupport (f i)) (tsupport (g j))) :
    Fin.append f g ∈ Kind.sepC1Tuples Y .euclidean (p + q) := by
  obtain ⟨a₁, a₂, a₃⟩ := (mem_sepC1Tuples_euclidean_iff' Y f).1 hf
  obtain ⟨b₁, b₂, b₃⟩ := (mem_sepC1Tuples_euclidean_iff' Y g).1 hg
  refine (mem_sepC1Tuples_euclidean_iff' Y _).2 ⟨fun l => ?_, fun l => ?_, fun l l' hl => ?_⟩
  · induction l using Fin.addCases with
    | left i => simpa using a₁ i
    | right j => simpa using b₁ j
  · induction l using Fin.addCases with
    | left i => simpa using a₂ i
    | right j => simpa using b₂ j
  · induction l using Fin.addCases with
    | left i =>
      induction l' using Fin.addCases with
      | left k => simpa using a₃ i k fun e => hl (by rw [e])
      | right k => simpa using hd i k
    | right i =>
      induction l' using Fin.addCases with
      | left k => simpa using (hd k i).symm
      | right k => simpa using b₃ i k fun e => hl (by rw [e])
abbrev realProdTensor (Y : Params) {n : ℕ} (f : Fin n → RealFn) :
    (Fin n → Kind.euclidean.Pt Y) → ℂ :=
  TensorExtension.realTensor Y f
theorem mem_of_eq_of_mem {A B : Type*} [SetLike A B] {S : A} {x y : B} (h : x = y)
    (hy : y ∈ S) : x ∈ S :=
  h ▸ hy
def conjReflect (μ : Fin 4) (c : ℝ) {q : ℕ} (A : Configuration q → ℂ) : Configuration q → ℂ :=
  fun x => conj (A fun i => axisReflect μ c (x i))
theorem conjReflect_zero (μ : Fin 4) (c : ℝ) {q : ℕ} :
    conjReflect μ c (0 : Configuration q → ℂ) = 0 :=
  funext fun x => by simp [conjReflect]
theorem conjReflect_add (μ : Fin 4) (c : ℝ) {q : ℕ} (A B : Configuration q → ℂ) :
    conjReflect μ c (A + B) = conjReflect μ c A + conjReflect μ c B :=
  funext fun x => by simp [conjReflect]
theorem conjReflect_smul (μ : Fin 4) (c : ℝ) {q : ℕ} (a : ℂ) (A : Configuration q → ℂ) :
    conjReflect μ c (a • A) = conj a • conjReflect μ c A :=
  funext fun x => by simp [conjReflect]
theorem conjReflect_realProdTensor (μ : Fin 4) (c : ℝ) {q : ℕ} (f : Fin q → RealFn) :
    conjReflect μ c (realProdTensor Y f) = realProdTensor Y fun i => f i ∘ axisReflect μ c := by
  funext x
  show conj (∏ i, ((f i (axisReflect μ c (x i)) : ℝ) : ℂ)) =
    ∏ i, ((f i (axisReflect μ c (x i)) : ℝ) : ℂ)
  rw [map_prod]
  simp
theorem tensor_realProdTensor {p q : ℕ} (f : Fin p → RealFn)
    (g : Fin q → RealFn) :
    tensor (realProdTensor Y f) (realProdTensor Y g) = realProdTensor Y (Fin.append f g) := by
  funext x
  show (∏ i, ((f i (x (Fin.castAdd q i)) : ℝ) : ℂ)) * ∏ j, ((g j (x (Fin.natAdd p j)) : ℝ) : ℂ) =
    ∏ i, ((Fin.append f g i (x i) : ℝ) : ℂ)
  rw [Fin.prod_univ_add]
  simp
theorem conjReflect_mem_span (μ : Fin 4) (c : ℝ) {q : ℕ} {O : Set (Fin 4 → ℝ)}
    {A : Configuration q → ℂ} (hA : A ∈ sepTensorSpanOn Y q O) :
    conjReflect μ c A ∈ sepTensorSpanOn Y q Set.univ := by
  induction hA using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨f, hf, rfl⟩ := hF
    exact mem_of_eq_of_mem (conjReflect_realProdTensor μ c f)
      (realTensor_mem_sepTensorSpanOn Y ⟨_, comp_axisReflect_mem μ c hf.1⟩)
  | zero =>
    exact mem_of_eq_of_mem (conjReflect_zero μ c) (Submodule.zero_mem _)
  | add F G _ _ hF hG =>
    exact mem_of_eq_of_mem (conjReflect_add μ c F G) (Submodule.add_mem _ hF hG)
  | smul a F _ hF =>
    exact mem_of_eq_of_mem (conjReflect_smul μ c a F) (Submodule.smul_mem _ _ hF)
theorem sepTensorSpanOn_mono {q : ℕ} {O O' : Set (Fin 4 → ℝ)} (h : O ⊆ O') :
    sepTensorSpanOn Y q O ≤ sepTensorSpanOn Y q O' := by
  refine Submodule.span_mono ?_
  rintro F ⟨f, hf, rfl⟩
  exact ⟨f, ⟨hf.1, fun i => (hf.2 i).trans h⟩, rfl⟩
theorem tensor_add_left {p q : ℕ} (A A' : Configuration p → ℂ) (B : Configuration q → ℂ) :
    tensor (A + A') B = tensor A B + tensor A' B :=
  funext fun x => by simp [tensor, add_mul]
theorem tensor_add_right {p q : ℕ} (A : Configuration p → ℂ) (B B' : Configuration q → ℂ) :
    tensor A (B + B') = tensor A B + tensor A B' :=
  funext fun x => by simp [tensor, mul_add]
theorem tensor_smul_left {p q : ℕ} (a : ℂ) (A : Configuration p → ℂ) (B : Configuration q → ℂ) :
    tensor (a • A) B = a • tensor A B :=
  funext fun x => by simp [tensor, mul_assoc]
theorem tensor_smul_right {p q : ℕ} (a : ℂ) (A : Configuration p → ℂ) (B : Configuration q → ℂ) :
    tensor A (a • B) = a • tensor A B :=
  funext fun x => by simp [tensor]; ring
theorem tensor_zero_left {p q : ℕ} (B : Configuration q → ℂ) :
    tensor (0 : Configuration p → ℂ) B = 0 :=
  funext fun x => by simp [tensor]
theorem tensor_zero_right {p q : ℕ} (A : Configuration p → ℂ) :
    tensor A (0 : Configuration q → ℂ) = 0 :=
  funext fun x => by simp [tensor]
theorem tensor_conjReflect_mem_span (μ : Fin 4) (c : ℝ) {p q : ℕ} {A : Configuration p → ℂ}
    {B : Configuration q → ℂ}
    (hA : A ∈ sepTensorSpanOn Y p (openHalfSpace μ c : Set (Fin 4 → ℝ)))
    (hB : B ∈ sepTensorSpanOn Y q (openHalfSpace μ c : Set (Fin 4 → ℝ))) :
    tensor (conjReflect μ c A) B ∈ sepTensorSpanOn Y (p + q) Set.univ := by
  induction hA using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨f, hf, rfl⟩ := hF
    induction hB using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨g, hg, rfl⟩ := hG
      have e := conjReflect_realProdTensor (Y := Y) μ c f
      refine mem_of_eq_of_mem ((congrArg (fun A => tensor A _) e).trans
        (tensor_realProdTensor (Y := Y) _ g)) ?_
      refine realTensor_mem_sepTensorSpanOn Y
        ⟨_, finAppend_mem (comp_axisReflect_mem μ c hf.1) hg.1 ?_⟩
      intro i j
      refine Set.disjoint_left.2 fun x hx hy => ?_
      have hx' : x ∈ axisReflect μ c ⁻¹' tsupport (f i) :=
        (tsupport_comp_axisReflect μ c (f i)).le hx
      have h₁ : c < axisReflect μ c x μ :=
        ((supportQ_euclidean_eq_tsupport Y (f i)).symm.le.trans (hf.2 i)) hx'
      have h₂ : c < x μ := ((supportQ_euclidean_eq_tsupport Y (g j)).symm.le.trans (hg.2 j)) hy
      rw [axisReflect_apply_self] at h₁
      linarith
    | zero =>
      exact mem_of_eq_of_mem (tensor_zero_right _) (Submodule.zero_mem _)
    | add G H _ _ hG hH =>
      exact mem_of_eq_of_mem (tensor_add_right _ G H) (Submodule.add_mem _ hG hH)
    | smul a G _ hG =>
      exact mem_of_eq_of_mem (tensor_smul_right a _ G) (Submodule.smul_mem _ a hG)
  | zero =>
    exact mem_of_eq_of_mem ((congrArg (fun A => tensor A B) (conjReflect_zero μ c)).trans
      (tensor_zero_left B)) (Submodule.zero_mem _)
  | add F G _ _ hF hG =>
    exact mem_of_eq_of_mem ((congrArg (fun A => tensor A B) (conjReflect_add μ c F G)).trans
      (tensor_add_left _ _ B)) (Submodule.add_mem _ hF hG)
  | smul a F _ hF =>
    exact mem_of_eq_of_mem ((congrArg (fun A => tensor A B) (conjReflect_smul μ c a F)).trans
      (tensor_smul_left _ _ B)) (Submodule.smul_mem _ _ hF)
theorem reflectedTensorsSeparated_holds (Y : Params) (μ : Fin 4) (c : ℝ) :
    ReflectedTensorsSeparated Y μ c := by
  intro F hF F' hF' q q'
  have hA := hF.1
  have hB := hF'.1
  cases q with
  | zero =>
    cases q' with
    | zero =>
      show conj (F 0 : ℂ) * (F' 0 : ℂ) ∈ sepTensorSubmodule Y Set.univ 0
      exact Submodule.mem_top
    | succ q' =>
      exact Submodule.smul_mem (sepTensorSpanOn Y (q' + 1) Set.univ) (conj (F 0 : ℂ))
        (sepTensorSpanOn_mono (Set.subset_univ _) (hB (q' + 1)))
  | succ q =>
    cases q' with
    | zero =>
      exact Submodule.smul_mem (sepTensorSpanOn Y (q + 1) Set.univ) (F' 0 : ℂ)
        (conjReflect_mem_span μ c (hA (q + 1)))
    | succ q' => exact tensor_conjReflect_mem_span μ c (hA (q + 1)) (hB (q' + 1))
end YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.SymbolPairing
end
end
section
set_option autoImplicit false
open Set
open scoped NNReal ENNReal ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.SymbolPairing
open ReflectionSpaces (finiteUpperSequences)
variable {D : Setup}
open PeriodicSpace TorusTransport.TestFunctionOrders
theorem momentExtensionAt_of_eq_zero (Ξ : D.LimitHierarchy) (A : GradedTestFun) (h : A.2 = 0) :
    momentExtensionAt Ξ A = 0 := by
  obtain ⟨n, a⟩ := A
  obtain rfl : a = 0 := h
  have h₀ : (0 : OrderedTestFun n) ∈ sepTensorSubmodule D.euclidParams Set.univ n :=
    Submodule.zero_mem _
  exact (dif_pos h₀).trans (map_zero (momentExtension Ξ n))
abbrev reflectionTerm (Ξ : D.LimitHierarchy) (μ : Fin 4) (c : ℝ) (F F' : TestFamily)
    (q q' : ℕ) : ℂ :=
  momentExtensionAt Ξ (reflectedTensor μ c F F' q q')
theorem reflectionTerm_left_zero (Ξ : D.LimitHierarchy) (μ : Fin 4) (c : ℝ) {F : TestFamily}
    (F' : TestFamily) {q : ℕ} (h : F q = 0) (q' : ℕ) : reflectionTerm Ξ μ c F F' q q' = 0 := by
  refine momentExtensionAt_of_eq_zero Ξ _ ?_
  cases q with
  | zero =>
    have h₀ : (F 0 : ℂ) = 0 := h
    cases q' with
    | zero =>
      show conj (F 0 : ℂ) * (F' 0 : ℂ) = 0
      rw [h₀]
      simp
    | succ q' =>
      funext x
      show conj (F 0 : ℂ) * F' (q' + 1) x = 0
      rw [h₀]
      simp
  | succ q =>
    have h₀ : ∀ y, F (q + 1) y = 0 := fun y => congrFun h y
    cases q' with
    | zero =>
      funext x
      show (F' 0 : ℂ) * conjReflect μ c (F (q + 1)) x = 0
      simp [conjReflect, h₀]
    | succ q' =>
      funext x
      show conjReflect μ c (F (q + 1)) (initPoints (q := q' + 1) x) *
        F' (q' + 1) (tailPoints (p := q + 1) x) = 0
      simp [conjReflect, h₀]
theorem reflectionTerm_right_zero (Ξ : D.LimitHierarchy) (μ : Fin 4) (c : ℝ) (F : TestFamily)
    {F' : TestFamily} (q : ℕ) {q' : ℕ} (h : F' q' = 0) : reflectionTerm Ξ μ c F F' q q' = 0 := by
  refine momentExtensionAt_of_eq_zero Ξ _ ?_
  cases q' with
  | zero =>
    have h₀ : (F' 0 : ℂ) = 0 := h
    cases q with
    | zero =>
      show conj (F 0 : ℂ) * (F' 0 : ℂ) = 0
      rw [h₀]
      simp
    | succ q =>
      funext x
      show (F' 0 : ℂ) * conjReflect μ c (F (q + 1)) x = 0
      rw [h₀]
      simp
  | succ q' =>
    have h₀ : ∀ y, F' (q' + 1) y = 0 := fun y => congrFun h y
    cases q with
    | zero =>
      funext x
      show conj (F 0 : ℂ) * F' (q' + 1) x = 0
      simp [h₀]
    | succ q =>
      funext x
      show conjReflect μ c (F (q + 1)) (initPoints (q := q' + 1) x) *
        F' (q' + 1) (tailPoints (p := q + 1) x) = 0
      simp [h₀]
theorem reflectionForm_eq_sum (Ξ : D.LimitHierarchy) (μ : Fin 4) (c : ℝ) {F F' : TestFamily}
    {N : ℕ} (hF : ∀ q, N ≤ q → F q = 0) (hF' : ∀ q, N ≤ q → F' q = 0) :
    reflectionForm Ξ μ c F F' =
      ∑ q ∈ Finset.range N, ∑ q' ∈ Finset.range N, reflectionTerm Ξ μ c F F' q q' := by
  rw [reflectionForm, finsum_eq_sum_of_support_subset (s := Finset.range N ×ˢ Finset.range N),
    Finset.sum_product]
  intro p hp
  have hp' : reflectionTerm Ξ μ c F F' p.1 p.2 ≠ 0 := hp
  simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
  constructor
  · by_contra h
    exact hp' (reflectionTerm_left_zero Ξ μ c F' (hF _ (not_lt.1 h)) _)
  · by_contra h
    exact hp' (reflectionTerm_right_zero Ξ μ c F _ (hF' _ (not_lt.1 h)))
theorem momentExtensionAt_combination {Ξ : D.LimitHierarchy} (hE : MomentLinearExtension Ξ)
    {n : ℕ} {Z X W : OrderedTestFun n} {a b : ℂ} (hZ : Z = a • X + b • W)
    (hX : X ∈ sepTensorSubmodule D.euclidParams Set.univ n)
    (hW : W ∈ sepTensorSubmodule D.euclidParams Set.univ n) :
    momentExtensionAt Ξ ⟨n, Z⟩ =
      a * momentExtensionAt Ξ ⟨n, X⟩ + b * momentExtensionAt Ξ ⟨n, W⟩ := by
  subst hZ
  exact hE.is_linear n X W a b hX hW
theorem reflectionTerm_right_linear {Ξ : D.LimitHierarchy} (hE : MomentLinearExtension Ξ)
    (μ : Fin 4) (c : ℝ) {F G H : TestFamily} (a b : ℂ) (q q' : ℕ)
    (hG : (reflectedTensor μ c F G q q').2 ∈
      sepTensorSubmodule D.euclidParams Set.univ (reflectedTensor μ c F G q q').1)
    (hH : (reflectedTensor μ c F H q q').2 ∈
      sepTensorSubmodule D.euclidParams Set.univ (reflectedTensor μ c F H q q').1) :
    reflectionTerm Ξ μ c F (a • G + b • H) q q' =
      a * reflectionTerm Ξ μ c F G q q' + b * reflectionTerm Ξ μ c F H q q' := by
  cases q with
  | zero =>
    cases q' with
    | zero =>
      refine momentExtensionAt_combination hE ?_ hG hH
      show conj (F 0 : ℂ) * (a * (G 0 : ℂ) + b * (H 0 : ℂ)) =
        a * (conj (F 0 : ℂ) * (G 0 : ℂ)) + b * (conj (F 0 : ℂ) * (H 0 : ℂ))
      ring
    | succ q' =>
      refine momentExtensionAt_combination hE ?_ hG hH
      funext x
      show conj (F 0 : ℂ) * (a * G (q' + 1) x + b * H (q' + 1) x) =
        a * (conj (F 0 : ℂ) * G (q' + 1) x) + b * (conj (F 0 : ℂ) * H (q' + 1) x)
      ring
  | succ q =>
    cases q' with
    | zero =>
      refine momentExtensionAt_combination hE ?_ hG hH
      funext x
      show (a * (G 0 : ℂ) + b * (H 0 : ℂ)) * conjReflect μ c (F (q + 1)) x =
        a * ((G 0 : ℂ) * conjReflect μ c (F (q + 1)) x) +
          b * ((H 0 : ℂ) * conjReflect μ c (F (q + 1)) x)
      ring
    | succ q' =>
      refine momentExtensionAt_combination hE ?_ hG hH
      funext x
      show conjReflect μ c (F (q + 1)) (initPoints x) *
          (a * G (q' + 1) (tailPoints x) + b * H (q' + 1) (tailPoints x)) =
        a * (conjReflect μ c (F (q + 1)) (initPoints x) * G (q' + 1) (tailPoints x)) +
          b * (conjReflect μ c (F (q + 1)) (initPoints x) * H (q' + 1) (tailPoints x))
      ring
theorem reflectionTerm_left_antilinear {Ξ : D.LimitHierarchy} (hE : MomentLinearExtension Ξ)
    (μ : Fin 4) (c : ℝ) {F G H : TestFamily} (a b : ℂ) (q q' : ℕ)
    (hF : (reflectedTensor μ c F H q q').2 ∈
      sepTensorSubmodule D.euclidParams Set.univ (reflectedTensor μ c F H q q').1)
    (hG : (reflectedTensor μ c G H q q').2 ∈
      sepTensorSubmodule D.euclidParams Set.univ (reflectedTensor μ c G H q q').1) :
    reflectionTerm Ξ μ c (a • F + b • G) H q q' =
      conj a * reflectionTerm Ξ μ c F H q q' + conj b * reflectionTerm Ξ μ c G H q q' := by
  cases q with
  | zero =>
    cases q' with
    | zero =>
      refine momentExtensionAt_combination hE ?_ hF hG
      show conj (a * (F 0 : ℂ) + b * (G 0 : ℂ)) * (H 0 : ℂ) =
        conj a * (conj (F 0 : ℂ) * (H 0 : ℂ)) + conj b * (conj (G 0 : ℂ) * (H 0 : ℂ))
      simp only [map_add, map_mul]
      ring
    | succ q' =>
      refine momentExtensionAt_combination hE ?_ hF hG
      funext x
      show conj (a * (F 0 : ℂ) + b * (G 0 : ℂ)) * H (q' + 1) x =
        conj a * (conj (F 0 : ℂ) * H (q' + 1) x) + conj b * (conj (G 0 : ℂ) * H (q' + 1) x)
      simp only [map_add, map_mul]
      ring
  | succ q =>
    cases q' with
    | zero =>
      refine momentExtensionAt_combination hE ?_ hF hG
      funext x
      show (H 0 : ℂ) * conj (a * F (q + 1) _ + b * G (q + 1) _) =
        conj a * ((H 0 : ℂ) * conjReflect μ c (F (q + 1)) x) +
          conj b * ((H 0 : ℂ) * conjReflect μ c (G (q + 1)) x)
      simp only [map_add, map_mul, conjReflect]
      ring
    | succ q' =>
      refine momentExtensionAt_combination hE ?_ hF hG
      funext x
      show conj (a * F (q + 1) _ + b * G (q + 1) _) * H (q' + 1) (tailPoints x) =
        conj a * (conjReflect μ c (F (q + 1)) (initPoints x) * H (q' + 1) (tailPoints x)) +
          conj b * (conjReflect μ c (G (q + 1)) (initPoints x) * H (q' + 1) (tailPoints x))
      simp only [map_add, map_mul, conjReflect]
      ring
theorem eventually_zero_of_mem {μ : Fin 4} {c : ℝ} {F : TestFamily}
    (hF : F ∈ finiteSeqsAbove D.euclidParams μ c) : ∃ N, ∀ q, N ≤ q → F q = 0 :=
  hF.2
theorem reflectionForm_right_linear {Ξ : D.LimitHierarchy} (hE : MomentLinearExtension Ξ)
    (μ : Fin 4) (c : ℝ) {F G H : TestFamily} (hF : F ∈ finiteSeqsAbove D.euclidParams μ c)
    (hG : G ∈ finiteSeqsAbove D.euclidParams μ c)
    (hH : H ∈ finiteSeqsAbove D.euclidParams μ c) (a b : ℂ) :
    reflectionForm Ξ μ c F (a • G + b • H) =
      a * reflectionForm Ξ μ c F G + b * reflectionForm Ξ μ c F H := by
  obtain ⟨N₁, h₁⟩ := eventually_zero_of_mem hF
  obtain ⟨N₂, h₂⟩ := eventually_zero_of_mem hG
  obtain ⟨N₃, h₃⟩ := eventually_zero_of_mem hH
  have e₁ : ∀ q, max N₁ (max N₂ N₃) ≤ q → F q = 0 := fun q hq =>
    h₁ q (le_trans (le_max_left _ _) hq)
  have e₂ : ∀ q, max N₁ (max N₂ N₃) ≤ q → G q = 0 := fun q hq =>
    h₂ q (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq)
  have e₃ : ∀ q, max N₁ (max N₂ N₃) ≤ q → H q = 0 := fun q hq =>
    h₃ q (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq)
  have e₄ : ∀ q, max N₁ (max N₂ N₃) ≤ q → (a • G + b • H) q = 0 := fun q hq => by
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, e₂ q hq, e₃ q hq, smul_zero, smul_zero,
      add_zero]
  rw [reflectionForm_eq_sum Ξ μ c e₁ e₄, reflectionForm_eq_sum Ξ μ c e₁ e₂,
    reflectionForm_eq_sum Ξ μ c e₁ e₃, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q' _ => ?_
  have hs := reflectedTensorsSeparated_holds D.euclidParams μ c
  exact reflectionTerm_right_linear hE μ c a b q q' (hs F hF G hG q q') (hs F hF H hH q q')
theorem reflectionForm_left_antilinear {Ξ : D.LimitHierarchy} (hE : MomentLinearExtension Ξ)
    (μ : Fin 4) (c : ℝ) {F G H : TestFamily} (hF : F ∈ finiteSeqsAbove D.euclidParams μ c)
    (hG : G ∈ finiteSeqsAbove D.euclidParams μ c)
    (hH : H ∈ finiteSeqsAbove D.euclidParams μ c) (a b : ℂ) :
    reflectionForm Ξ μ c (a • F + b • G) H =
      conj a * reflectionForm Ξ μ c F H + conj b * reflectionForm Ξ μ c G H := by
  obtain ⟨N₁, h₁⟩ := eventually_zero_of_mem hF
  obtain ⟨N₂, h₂⟩ := eventually_zero_of_mem hG
  obtain ⟨N₃, h₃⟩ := eventually_zero_of_mem hH
  have e₁ : ∀ q, max N₁ (max N₂ N₃) ≤ q → F q = 0 := fun q hq =>
    h₁ q (le_trans (le_max_left _ _) hq)
  have e₂ : ∀ q, max N₁ (max N₂ N₃) ≤ q → G q = 0 := fun q hq =>
    h₂ q (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq)
  have e₃ : ∀ q, max N₁ (max N₂ N₃) ≤ q → H q = 0 := fun q hq =>
    h₃ q (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq)
  have e₄ : ∀ q, max N₁ (max N₂ N₃) ≤ q → (a • F + b • G) q = 0 := fun q hq => by
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, e₁ q hq, e₂ q hq, smul_zero, smul_zero,
      add_zero]
  rw [reflectionForm_eq_sum Ξ μ c e₄ e₃, reflectionForm_eq_sum Ξ μ c e₁ e₃,
    reflectionForm_eq_sum Ξ μ c e₂ e₃, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q' _ => ?_
  have hs := reflectedTensorsSeparated_holds D.euclidParams μ c
  exact reflectionTerm_left_antilinear hE μ c a b q q' (hs F hF H hH q q') (hs G hG H hH q q')
theorem reflectionForm_sum_right {Ξ : D.LimitHierarchy} (hE : MomentLinearExtension Ξ)
    (μ : Fin 4) (c : ℝ) {F : TestFamily} (hF : F ∈ finiteSeqsAbove D.euclidParams μ c)
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (G : ι → TestFamily)
    (hG : ∀ i, G i ∈ finiteSeqsAbove D.euclidParams μ c) :
    reflectionForm Ξ μ c F (∑ i ∈ s, a i • G i) =
      ∑ i ∈ s, a i * reflectionForm Ξ μ c F (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h₀ := reflectionForm_right_linear hE μ c hF (Submodule.zero_mem _)
      (Submodule.zero_mem _) 0 0
    simpa using h₀
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    have h₀ := reflectionForm_right_linear hE μ c hF (hG i)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (a i) (hG i) :
        ∑ i ∈ s, a i • G i ∈ finiteSeqsAbove D.euclidParams μ c) (a i) 1
    simpa using h₀
theorem reflectionForm_sum_left {Ξ : D.LimitHierarchy} (hE : MomentLinearExtension Ξ)
    (μ : Fin 4) (c : ℝ) {H : TestFamily} (hH : H ∈ finiteSeqsAbove D.euclidParams μ c)
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (G : ι → TestFamily)
    (hG : ∀ i, G i ∈ finiteSeqsAbove D.euclidParams μ c) :
    reflectionForm Ξ μ c (∑ i ∈ s, a i • G i) H =
      ∑ i ∈ s, conj (a i) * reflectionForm Ξ μ c (G i) H := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h₀ := reflectionForm_left_antilinear hE μ c (Submodule.zero_mem _)
      (Submodule.zero_mem _) hH 0 0
    simpa using h₀
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    have h₀ := reflectionForm_left_antilinear hE μ c (hG i)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (a i) (hG i) :
        ∑ i ∈ s, a i • G i ∈ finiteSeqsAbove D.euclidParams μ c) hH (a i) 1
    simpa using h₀
theorem mem_finiteSeqsAbove_of_upper {F : TestFamily}
    (hF : F ∈ finiteUpperSequences D.euclidParams) :
    F ∈ finiteSeqsAbove D.euclidParams 3 0 := by
  refine ⟨fun q => ?_, hF.2⟩
  cases q with
  | zero => exact Submodule.mem_top
  | succ q => exact hF.1 (q + 1)
end YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.SymbolPairing
end
end
section
set_option autoImplicit false
open Set
open scoped NNReal ENNReal ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.SymbolPairing
open ReflectionSpaces (finiteUpperSequences)
variable {D : Setup}
open PeriodicSpace TorusTransport.TestFunctionOrders
open TorusTransport.TupleVectors
open TimeAxisSymbols
open SymbolSequences
theorem momentExtensionAt_realProdTensor {Ξ : D.LimitHierarchy} (hE : MomentLinearExtension Ξ)
    {n : ℕ} (a : Fin (n + 1) → RealFn) (Z : SpaceTimeSymbol (symbolSetup D))
    (hZ : Z.1 = ⟨n + 1, a⟩) :
    momentExtensionAt Ξ ⟨n + 1, realProdTensor D.euclidParams a⟩ =
      ((symbolMoments Ξ Z : ℝ) : ℂ) := by
  obtain ⟨⟨m, b⟩, hb⟩ := Z
  cases hZ
  exact hE.at_tensor n ⟨a, components_mem_sepC1Tuples D.euclidParams ⟨⟨n + 1, a⟩, hb⟩⟩
theorem reflectSymbol_val (X : SpaceTimeSymbol (symbolSetup D)) :
    (reflectSymbol X).1 = ⟨X.1.1, fun i => X.1.2 i ∘ axisReflect 3 0⟩ := by
  refine congrArg (Sigma.mk X.1.1) (funext fun i => ?_)
  refine (reflectSymbol_fn X i).trans ?_
  funext x
  exact congrArg (X.1.2 i) (CentredTensorMoments.hyperplaneReflection_three_zero x).symm
theorem momentExtensionAt_gradedTensor {Ξ : D.LimitHierarchy} (hE : MomentLinearExtension Ξ)
    (X X' : PosSymbol (symbolSetup D)) :
    momentExtensionAt Ξ (gradedTensor
        ⟨X.1.1, CentredTensorMoments.conjReflectTest 3 0 (symbolTensor X)⟩
        ⟨X'.1.1, symbolTensor X'⟩) =
      ((symbolMoments Ξ (reflectAppend X X') : ℝ) : ℂ) := by
  have hZ : (reflectAppend X X').1 =
      tupleAppend (reflectSymbol (posToSymbol X)).1 X'.1 := rfl
  rw [reflectSymbol_val] at hZ
  obtain ⟨⟨k, f⟩, hX⟩ := X
  obtain ⟨⟨k', g⟩, hX'⟩ := X'
  cases k with
  | zero =>
    cases k' with
    | zero =>
      have e := hE.at_zero (conj (1 : ℂ) * 1)
      refine e.trans ?_
      have h₁ : symbolMoments Ξ (reflectAppend ⟨⟨0, f⟩, hX⟩ ⟨⟨0, g⟩, hX'⟩) = 1 :=
        Ξ.partitionMoment_zero _
      rw [h₁]
      simp
    | succ k' =>
      have e : gradedTensor
          ⟨0, CentredTensorMoments.conjReflectTest 3 0
            (symbolTensor (D := symbolSetup D) ⟨⟨0, f⟩, hX⟩)⟩
          ⟨k' + 1, symbolTensor (D := symbolSetup D) ⟨⟨k' + 1, g⟩, hX'⟩⟩ =
          ⟨k' + 1, realProdTensor D.euclidParams g⟩ := by
        refine congrArg (Sigma.mk (k' + 1)) (funext fun x => ?_)
        show conj (1 : ℂ) * _ = _
        simp
        rfl
      refine (congrArg (momentExtensionAt Ξ) e).trans
        (momentExtensionAt_realProdTensor hE g _ ?_)
      rw [hZ]
      exact (congrArg (fun t => tupleAppend t _) ((fst_eq_zero_iff _).1 rfl)).trans
        (nil_tupleAppend _)
  | succ k =>
    have hr : CentredTensorMoments.conjReflectTest 3 0 (q := k + 1)
        (symbolTensor (D := symbolSetup D) ⟨⟨k + 1, f⟩, hX⟩) =
        realProdTensor D.euclidParams fun i => f i ∘ axisReflect 3 0 :=
      conjReflect_realProdTensor 3 0 f
    cases k' with
    | zero =>
      have e : gradedTensor
          ⟨k + 1, CentredTensorMoments.conjReflectTest 3 0
            (symbolTensor (D := symbolSetup D) ⟨⟨k + 1, f⟩, hX⟩)⟩
          ⟨0, symbolTensor (D := symbolSetup D) ⟨⟨0, g⟩, hX'⟩⟩ =
          ⟨k + 1, realProdTensor D.euclidParams fun i => f i ∘ axisReflect 3 0⟩ := by
        refine congrArg (Sigma.mk (k + 1)) (funext fun x => ?_)
        show (1 : ℂ) * _ = _
        rw [one_mul]
        exact congrFun hr x
      refine (congrArg (momentExtensionAt Ξ) e).trans
        (momentExtensionAt_realProdTensor hE _ _ ?_)
      rw [hZ]
      have h₀ : (⟨0, g⟩ : FnTuple) = nilTuple _ := (fst_eq_zero_iff _).1 rfl
      show tupleAppend _ (⟨0, g⟩ : FnTuple) = _
      rw [h₀, tupleAppend_nil]
      rfl
    | succ k' =>
      have e : gradedTensor
          ⟨k + 1, CentredTensorMoments.conjReflectTest 3 0
            (symbolTensor (D := symbolSetup D) ⟨⟨k + 1, f⟩, hX⟩)⟩
          ⟨k' + 1, symbolTensor (D := symbolSetup D) ⟨⟨k' + 1, g⟩, hX'⟩⟩ =
          ⟨k + 1 + k' + 1, realProdTensor D.euclidParams
            (Fin.append (m := k + 1) (n := k' + 1) (fun i => f i ∘ axisReflect 3 0) g)⟩ := by
        refine congrArg (Sigma.mk (k + 1 + (k' + 1))) ?_
        exact (congrArg (fun A => tensor (p := k + 1) (q := k' + 1) A _) hr).trans
          (tensor_realProdTensor (Y := D.euclidParams) _ g)
      refine (congrArg (momentExtensionAt Ξ) e).trans
        (momentExtensionAt_realProdTensor hE (n := k + 1 + k')
          (Fin.append (m := k + 1) (n := k' + 1) (fun i => f i ∘ axisReflect 3 0) g) _ ?_)
      rw [hZ]
      rfl
theorem reflectionPairing_symbolSequence {Ξ : D.LimitHierarchy} (hE : MomentLinearExtension Ξ)
    (X X' : PosSymbol (symbolSetup D)) :
    reflectionPairing Ξ (symbolSequence D.euclidParams X) (symbolSequence D.euclidParams X') =
      ((symbolMoments Ξ (reflectAppend X X') : ℝ) : ℂ) := by
  rw [reflectionPairing, reflectionForm,
    finsum_eq_single (fun p : ℕ × ℕ => reflectionTerm Ξ 3 0 (symbolSequence D.euclidParams X).1
      (symbolSequence D.euclidParams X').1 p.1 p.2) (X.1.1, X'.1.1)]
  · have e₁ := symbolSequence_self D.euclidParams X
    have e₂ := symbolSequence_self D.euclidParams X'
    simp only [reflectionTerm, reflectedTensor, thetaReflect]
    rw [e₁, e₂]
    exact momentExtensionAt_gradedTensor hE X X'
  · rintro ⟨q, q'⟩ hp
    by_cases hq : q = X.1.1
    · have hq' : q' ≠ X'.1.1 := fun h => hp (by rw [hq, h])
      exact reflectionTerm_right_zero Ξ 3 0 _ q (symbolSequence_of_ne D.euclidParams X' hq')
    · exact reflectionTerm_left_zero Ξ 3 0 _ (symbolSequence_of_ne D.euclidParams X hq) q'
theorem spanSequence_linComb {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (X : ι → PosSymbol (symbolSetup D)) :
    (spanSequence D.euclidParams (linComb c X)).1 =
      ∑ b, c b • (symbolSequence D.euclidParams (X b)).1 := by
  have e : spanSequence D.euclidParams (linComb c X) =
      ∑ b, c b • symbolSequence D.euclidParams (X b) :=
    (linExtend_linComb _ c X).trans rfl
  rw [e]
  simp
theorem reflectionPairing_spanSequence {Ξ : D.LimitHierarchy} (hE : MomentLinearExtension Ξ)
    (X X' : PosSymbolSpan (symbolSetup D)) :
    reflectionPairing Ξ (spanSequence D.euclidParams X) (spanSequence D.euclidParams X') =
      osForm (symbolMoments Ξ) X X' := by
  rw [eq_linComb_support X, eq_linComb_support X', osForm_linComb]
  have hm : ∀ Z, (symbolSequence (D := symbolSetup D) D.euclidParams Z).1 ∈
      finiteSeqsAbove D.euclidParams 3 0 := fun Z =>
    mem_finiteSeqsAbove_of_upper (symbolSequence D.euclidParams Z).2
  rw [reflectionPairing, spanSequence_linComb, spanSequence_linComb,
    reflectionForm_sum_left hE 3 0
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hm _)) _ _ _ fun b => hm _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [reflectionForm_sum_right hE 3 0 (hm _) _ _ _ fun b => hm _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [← mul_assoc]
  exact congrArg _ (reflectionPairing_symbolSequence hE _ _)
theorem exists_spanSequence_single {q : ℕ} {A : OrderedTestFun q}
    (hA : A ∈ ReflectionSpaces.sepTensorsUpper D.euclidParams q) :
    ∃ v : PosSymbolSpan (symbolSetup D),
      (spanSequence D.euclidParams v).1 = Pi.single q A := by
  cases q with
  | zero =>
    refine ⟨(A : ℂ) • basisVec posUnitSymbol, ?_⟩
    rw [map_smul, spanSequence_basisVec]
    funext p
    cases p with
    | zero =>
      show (A : ℂ) * ((symbolSequence D.euclidParams posUnitSymbol).1 0 : ℂ) = _
      have e := symbolSequence_self (D := symbolSetup D) D.euclidParams posUnitSymbol
      rw [show ((symbolSequence D.euclidParams posUnitSymbol).1 0 : ℂ) = 1 from e]
      simp
    | succ p =>
      have h₁ := symbolSequence_of_ne (D := symbolSetup D) D.euclidParams
        (posUnitSymbol) (q := p + 1) (by simp [posUnitSymbol, nilTuple])
      have h₂ : Pi.single (M := OrderedTestFun) 0 A (p + 1) = 0 :=
        Pi.single_eq_of_ne (by omega) _
      show A • (symbolSequence D.euclidParams posUnitSymbol).1 (p + 1) = _
      rw [h₁, h₂, smul_zero]
  | succ q =>
    have key : ∀ A : (Fin (q + 1) → Fin 4 → ℝ) → ℂ,
        A ∈ sepTensorSpanOn D.euclidParams (q + 1)
          (ReflectionSpaces.upperHalfOpen : Set (Fin 4 → ℝ)) →
        ∃ v : PosSymbolSpan (symbolSetup D),
          (spanSequence D.euclidParams v).1 = Pi.single (M := OrderedTestFun) (q + 1) A := by
      intro A hA
      induction hA using Submodule.span_induction with
      | mem F hF =>
        obtain ⟨f, hf, rfl⟩ := hF
        obtain ⟨c₁, c₂, c₃⟩ := (mem_sepC1Tuples_euclidean_iff' D.euclidParams f).1 hf.1
        have hX : (⟨q + 1, f⟩ : FnTuple) ∈ posSymbols (symbolSetup D) :=
          (TorusTransport.TupleVectors.mem_sepTuples_iff (symbolSetup D) _ _).2
            ⟨fun i => lipschitzOn_of_isC1On _ (c₁ i) (c₂ i), c₂, fun i k hik => c₃ i k hik, c₁,
              fun i => (supportQ_euclidean_eq_tsupport D.euclidParams (f i)).symm.le.trans
                (hf.2 i)⟩
        refine ⟨basisVec ⟨_, hX⟩, ?_⟩
        rw [spanSequence_basisVec]
        rfl
      | zero =>
        refine ⟨0, ?_⟩
        rw [map_zero]
        exact (Pi.single_zero _).symm
      | add F G _ _ hF hG =>
        obtain ⟨v, hv⟩ := hF
        obtain ⟨w, hw⟩ := hG
        refine ⟨v + w, ?_⟩
        rw [map_add, Submodule.coe_add, hv, hw]
        exact (Pi.single_add (f := OrderedTestFun) (q + 1) F G).symm
      | smul a F _ hF =>
        obtain ⟨v, hv⟩ := hF
        refine ⟨a • v, ?_⟩
        rw [map_smul, Submodule.coe_smul, hv]
        exact (Pi.single_smul (f := OrderedTestFun) (q + 1) a F).symm
    exact key A hA
theorem spanSequence_surjective (D : Setup) : Function.Surjective
    (spanSequence (D := symbolSetup D) D.euclidParams) := by
  rintro ⟨F, hF, N, hN⟩
  choose v hv using fun q => exists_spanSequence_single (D := D) (hF q)
  refine ⟨∑ q ∈ Finset.range N, v q, Subtype.ext ?_⟩
  rw [map_sum, Submodule.coe_sum]
  simp only [hv]
  funext q
  rw [Finset.sum_apply]
  rw [Finset.sum_pi_single]
  by_cases hq : q ∈ Finset.range N
  · rw [if_pos hq]
  · rw [if_neg hq]
    exact (hN q (by simpa using hq)).symm
theorem symbolPairingMatches_holds (h : CitedFacts) (Ξ : D.LimitHierarchy) :
    SymbolPairingMatches Ξ where
  surjective := spanSequence_surjective D
  pairing_eq := reflectionPairing_spanSequence (momentLinearExtension_holds h Ξ)
theorem symbolMoments_isReflPositive (h : CitedFacts) {Ξ : D.LimitHierarchy}
    (hpos : ReflectionPositive Ξ) : IsReflPositive (symbolMoments Ξ) := by
  intro n _ X c
  obtain ⟨r, hr, e⟩ := hpos (spanSequence D.euclidParams (linComb c X))
  rw [reflectionPairing_spanSequence (momentLinearExtension_holds h Ξ), osForm_linComb] at e
  rw [← e]
  exact Complex.zero_le_real.2 hr
end YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.SymbolPairing
end
end
section
set_option autoImplicit false
open Set Filter Topology
open scoped NNReal ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorFamilies
open PeriodicSpace TorusTransport.TestFunctionOrders
def smoothSepTensors (Y : Params) (O : Set (Fin 4 → ℝ)) :
    (q : ℕ) → Submodule ℂ (OrderedTestFun q)
  | 0 => ⊤
  | q + 1 => DenseTensorSpan.smoothSepTensorSpan Y q.succPNat O
abbrev injTestFns (Y : Params) (O : Set (Fin 4 → ℝ)) (n : ℕ+) :
    Set (Kind.euclidean.Tuple Y n → ℂ) :=
  Kind.Tuple.testFns Y Kind.euclidean (Euclid.injTuplesIn O (n : ℕ))
def TendstoInInjTestFns (Y : Params) (O : Set (Fin 4 → ℝ)) {n : ℕ+}
    (Fs : ℕ+ → Kind.euclidean.Tuple Y n → ℂ)
    (F : Kind.euclidean.Tuple Y n → ℂ) : Prop :=
  ∃ (hs : ∀ t, Fs t ∈ injTestFns Y O n) (h : F ∈ injTestFns Y O n),
    Kind.Tuple.TendstoInTestFns (fun t => ⟨Fs t, hs t⟩) ⟨F, h⟩
end YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorFamilies
end
end

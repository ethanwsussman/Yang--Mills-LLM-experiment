import YangMills.Construction.InfiniteLattice.FunctionsStatesSupportsClassesMirrorsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.OneFamilyOfMirrors
import YangMills.Construction.InfiniteLattice.PeriodsFoldCompactnessAndLimitsOfTori
import YangMills.Construction.InfiniteLattice.StatesWithAGivenMirrorDominateLocalObservables
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped ComplexOrder NNReal Matrix Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open NormalFamilies GibbsAtFixedSpacing
namespace MirrorDomination
def cubicSubgroup (s : ℕ) : AddSubgroup (LatticePoint 1) :=
  (latticeSubgroup (s : ℝ)).addSubgroupOf (latticeSubgroup 1)
def scaledBasisVec (s : ℕ) (μ : Fin 4) : LatticePoint 1 :=
  ⟨Pi.single μ (s : ℝ), Pi.single μ (s : ℤ), fun ν => by
    by_cases h : ν = μ
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]⟩
theorem scaledBasisVec_mem (s : ℕ) (μ : Fin 4) : scaledBasisVec s μ ∈ cubicSubgroup s := by
  refine AddSubgroup.mem_addSubgroupOf.2 ⟨Pi.single μ 1, fun ν => ?_⟩
  by_cases h : ν = μ
  · subst h; simp [scaledBasisVec]
  · simp [scaledBasisVec, Pi.single_eq_of_ne h]
theorem scaledBasisVec_ne_zero {s : ℕ} (hs : s ≠ 0) (μ : Fin 4) : scaledBasisVec s μ ≠ 0 := by
  intro h
  have h' := congrFun (congrArg Subtype.val h) μ
  simp [scaledBasisVec] at h'
  exact hs h'
theorem le_norm_of_mem_cubicSubgroup {s : ℕ} {γ : LatticePoint 1} (hγ : γ ∈ cubicSubgroup s)
    (h0 : γ ≠ 0) : (s : ℝ) ≤ ‖(γ : AmbientSpace)‖ := by
  obtain ⟨n, hn⟩ := AddSubgroup.mem_addSubgroupOf.1 hγ
  have hne : ∃ μ, n μ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact h0 (Subtype.ext (funext fun μ => by simp [hn μ, hall μ]))
  obtain ⟨μ, hμ⟩ := hne
  have h1 : (1 : ℝ) ≤ |(n μ : ℝ)| := by
    have := Int.one_le_abs hμ
    exact_mod_cast this
  calc (s : ℝ) = 1 * s := (one_mul _).symm
    _ ≤ |(n μ : ℝ)| * s := by gcongr
    _ = ‖(γ : AmbientSpace) μ‖ := by
        rw [hn μ, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
    _ ≤ ‖(γ : AmbientSpace)‖ := norm_le_pi_norm _ μ
def cubicPeriods (i : ℕ) : PeriodSublattice 1 where
  periods := cubicSubgroup (i + 3)
  exists_linearIndependent := by
    refine ⟨scaledBasisVec (i + 3), scaledBasisVec_mem _, ?_⟩
    rw [Fintype.linearIndependent_iff]
    intro g hg μ
    have h := congrFun hg μ
    have hs : (i : ℝ) + 3 ≠ 0 := by positivity
    simpa [scaledBasisVec, Finset.sum_apply, Pi.single_apply, hs] using h
  le_norm_of_ne_zero := by
    intro γ hγ h0
    have h := le_norm_of_mem_cubicSubgroup hγ h0
    push_cast at h
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    simp only [minimalPeriodRatio]
    linarith
theorem minNonzeroNorm_cubicPeriods : MinNonzeroNormTendsToInfinity cubicPeriods := by
  refine tendsto_atTop_mono (f := fun i : ℕ => (i : ℝ)) (fun i => ?_) tendsto_natCast_atTop_atTop
  refine le_csInf ⟨_, scaledBasisVec (i + 3) 0, scaledBasisVec_mem _ 0,
    scaledBasisVec_ne_zero (by omega) 0, rfl⟩ ?_
  rintro s ⟨γ, hγ, h0, rfl⟩
  have h := le_norm_of_mem_cubicSubgroup hγ h0
  push_cast at h
  linarith
theorem integrable_of_isBoundedObservable {G : GaugeField 1 → ℂ} (hG : IsBoundedObservable G)
    (ρ : Measure (GaugeField 1)) [IsFiniteMeasure ρ] : Integrable G ρ := by
  obtain ⟨hm, C, hC⟩ := hG
  exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
theorem isBoundedObservable_of_continuous (hc : CompactSpace (GaugeField 1))
    {G : GaugeField 1 → ℂ} (hG : Continuous G) : IsBoundedObservable G := by
  refine ⟨hG.measurable, ?_⟩
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hG.continuousOn
  exact ⟨C, fun U => hC U (Set.mem_univ U)⟩
theorem stateEval_add_smul {G : GaugeField 1 → ℂ} (hG : IsBoundedObservable G)
    (ρ₁ ρ₂ : Measure (GaugeField 1)) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (s t : ℝ≥0) :
    stateEval (s • ρ₁ + t • ρ₂) G =
      ((s : ℝ) : ℂ) * stateEval ρ₁ G + ((t : ℝ) : ℂ) * stateEval ρ₂ G := by
  have h₁ := integrable_of_isBoundedObservable hG (s • ρ₁)
  have h₂ := integrable_of_isBoundedObservable hG (t • ρ₂)
  simp only [stateEval]
  rw [integral_add_measure h₁ h₂, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    NNReal.smul_def, NNReal.smul_def, Complex.real_smul, Complex.real_smul]
theorem continuous_stateEval {G : GaugeField 1 → ℂ} (hG : Continuous G) :
    @Continuous _ ℂ (probabilityMeasuresWeakTopology 1) _
      (fun ν : ProbabilityMeasure (GaugeField 1) =>
        stateEval (ν : Measure (GaugeField 1)) G) :=
  continuous_iInf_dom (i := (⟨G, hG⟩ : C(GaugeField 1, ℂ))) continuous_induced_dom
theorem isClosed_setOf_eq_and_nonneg {X ι κ : Type*} [TopologicalSpace X] (f g : ι → X → ℂ)
    (p : κ → X → ℂ) (hf : ∀ i, Continuous (f i)) (hg : ∀ i, Continuous (g i))
    (hp : ∀ k, Continuous (p k)) :
    IsClosed {x | (∀ i, f i x = g i x) ∧ ∀ k, 0 ≤ p k x} := by
  have h₁ : IsClosed {x | ∀ i, f i x = g i x} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (hf i) (hg i)
  have h₂ : IsClosed {x | ∀ k, 0 ≤ p k x} := by
    simp only [Set.ofPred_forall, Complex.le_def, Complex.zero_re, Complex.zero_im]
    refine isClosed_iInter fun k => ?_
    exact (isClosed_le continuous_const (Complex.continuous_re.comp (hp k))).inter
      (isClosed_eq continuous_const (Complex.continuous_im.comp (hp k)))
  exact h₁.inter h₂
variable (hf : BasicStructure.Statement)
  (hi : PeriodicGibbsFoldAndCompactness.Statement)
include hf hi in
theorem gibbsClassOf_evenLattice_nonempty {β : ℝ} (hβ : 0 < β) :
    (gibbsClassOf β evenLattice).Nonempty := by
  obtain ⟨hstates, hlim⟩ := (hi β hβ).2.2.2.1
  obtain ⟨-, -, fst, -, -, fe, -, -⟩ := hf.1 1 one_pos β hβ
  obtain ⟨ν₀, hs, hlp⟩ := fst.2.2.2.2.1 (fun i => (cubicPeriods i).liftedGibbsMeasure β)
    (fun i _ => hstates _)
  exact ⟨ν₀, fe _ _ le_top (hlim cubicPeriods minNonzeroNorm_cubicPeriods ν₀ hs hlp)⟩
include hf hi in
theorem classInclusions {β : ℝ} (hβ : 0 < β) (P : NormalLevelPair 1) : ClassInclusions β P := by
  intro h hev h2
  obtain ⟨-, -, -, -, -, fe, -, -⟩ := hf.1 1 one_pos β hβ
  obtain ⟨-, -, hPQ, hQP, -, -, ⟨-, hfin⟩, -⟩ := hf.2 P.normal P.normal_mem h hev h2
  refine ⟨fe _ _ fun x hx => ?_, fe _ _ fun x hx => ?_, fun ν hν => ?_, (hi β hβ).1⟩
  · exact AddSubgroup.mem_addSubgroupOf.2 (hQP (AddSubgroup.mem_addSubgroupOf.1 hx))
  · exact AddSubgroup.mem_addSubgroupOf.2 (hPQ (AddSubgroup.mem_addSubgroupOf.1 hx))
  · exact Set.mem_iUnion₂.2 ⟨_, ⟨hfin⟩, hν⟩
include hf in
theorem mirrorStatesCompact {β : ℝ} (hβ : 0 < β) (P : NormalLevelPair 1)
    (hconv : Convex ℝ≥0 (gibbsClassOf β evenLattice))
    (hcomp : IsWeakCompact (gibbsClassOf β evenLattice)) :
    MirrorStatesCompact β P := by
  obtain ⟨fa, fiso, -, -, -, -, -, -⟩ := hf.1 1 one_pos β hβ
  have hc : CompactSpace (GaugeField 1) := fa.1
  have hθ : ∀ r : LatticeSymmetry 1, ∀ F ∈ continuousFns 1,
      r.actOn F ∈ continuousFns 1 := fun r => (fiso r r).2.2.2.1
  have hθP : ∀ F ∈ continuousFns 1, Continuous (P.reflectObservable F) :=
    fun F hF => hθ _ F hF
  have hΘP : ∀ F ∈ halfSpaceContinuousLocal 1 P.normal P.level 1,
      Continuous (P.conjReflectObservable F * F) := fun F hF =>
    (Complex.continuous_conj.comp (hθP F hF.2.2.2)).mul hF.2.2.2
  let 𝒞 : Set (Measure (GaugeField 1)) :=
    {ρ | IsLatticeState ρ ∧ (∀ F ∈ continuousFns 1,
        stateEval ρ (P.reflectObservable F) = stateEval ρ F) ∧
      ∀ F ∈ halfSpaceContinuousLocal 1 P.normal P.level 1,
        0 ≤ stateEval ρ (P.conjReflectObservable F * F)}
  have hclosed : IsClosed[probabilityMeasuresWeakTopology 1] (asProbabilityMeasures 𝒞) := by
    have h := @isClosed_setOf_eq_and_nonneg (ProbabilityMeasure (GaugeField 1))
      {F // F ∈ continuousFns 1}
      {F // F ∈ halfSpaceContinuousLocal 1 P.normal P.level 1}
      (probabilityMeasuresWeakTopology 1)
      (fun F ν => stateEval (ν : Measure (GaugeField 1)) (P.reflectObservable F.1))
      (fun F ν => stateEval (ν : Measure (GaugeField 1)) F.1)
      (fun F ν => stateEval (ν : Measure (GaugeField 1)) (P.conjReflectObservable F.1 * F.1))
      (fun F => continuous_stateEval (hθP F.1 F.2))
      (fun F => continuous_stateEval F.2)
      (fun F => continuous_stateEval (hΘP F.1 F.2))
    convert h using 1
    ext ν
    constructor
    · rintro ⟨-, h₁, h₂⟩
      exact ⟨fun F => h₁ F.1 F.2, fun F => h₂ F.1 F.2⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨(inferInstance : IsProbabilityMeasure (ν : Measure (GaugeField 1))),
        fun F hF => h₁ ⟨F, hF⟩, fun F hF => h₂ ⟨F, hF⟩⟩
  have hinter : mirrorReflectionPositiveStates β P = gibbsClassOf β evenLattice ∩ 𝒞 := by
    ext ρ
    constructor
    · rintro ⟨h₀, h₁, h₂⟩
      exact ⟨h₀, hcomp.1 ρ h₀, h₁, h₂⟩
    · rintro ⟨h₀, -, h₁, h₂⟩
      exact ⟨h₀, h₁, h₂⟩
  refine ⟨?_, ⟨hcomp.1, 𝒞, ⟨fun ρ h => h.1, hclosed⟩, hinter⟩, ?_, ?_⟩
  · intro ρ₁ h₁ ρ₂ h₂ s t hs ht hst
    have : IsProbabilityMeasure ρ₁ := hcomp.1 ρ₁ h₁.1
    have : IsProbabilityMeasure ρ₂ := hcomp.1 ρ₂ h₂.1
    refine ⟨hconv h₁.1 h₂.1 hs ht hst, fun F hF => ?_, fun F hF => ?_⟩
    · rw [stateEval_add_smul (isBoundedObservable_of_continuous hc (hθP F hF)),
        stateEval_add_smul (isBoundedObservable_of_continuous hc hF), h₁.2.1 F hF, h₂.2.1 F hF]
    · rw [stateEval_add_smul (isBoundedObservable_of_continuous hc (hΘP F hF))]
      have hr : ∀ u : ℝ≥0, (0 : ℂ) ≤ ((u : ℝ) : ℂ) := fun u => by
        exact_mod_cast u.2
      exact add_nonneg (mul_nonneg (hr s) (h₁.2.2 F hF)) (mul_nonneg (hr t) (h₂.2.2 F hF))
  · exact fun ρ h => hcomp.1 ρ h.1
  · have hpts : asProbabilityMeasures (mirrorReflectionPositiveStates β P) =
        asProbabilityMeasures (gibbsClassOf β evenLattice) ∩ asProbabilityMeasures 𝒞 := by
      rw [hinter]
      rfl
    rw [hpts]
    exact @IsCompact.inter_right _ (probabilityMeasuresWeakTopology 1) _ _ hcomp.2 hclosed
theorem intCast_two_mul_smul_firstNonzeroBasisVec_mem (n : AmbientSpace) (k : ℤ) :
    ((2 * k : ℤ) : ℝ) • firstNonzeroBasisVec n ∈ evenLattice := by
  refine ⟨Pi.single (firstNonzeroIndex n) k, fun ν => ?_⟩
  by_cases h : ν = firstNonzeroIndex n
  · subst h
    simp [firstNonzeroBasisVec, PeriodicLattice.coordVec]
    ring
  · simp [firstNonzeroBasisVec, PeriodicLattice.coordVec, Pi.single_eq_of_ne h]
theorem evenLattice_le_latticeSubgroup : evenLattice ≤ latticeSubgroup 1 := by
  rintro x ⟨m, hm⟩
  exact ⟨2 • m, fun ν => by simp [hm ν]; ring⟩
include hf hi in
theorem dominates {β : ℝ} (hβ : 0 < β) (P : NormalLevelPair 1) : Dominates β P := by
  intro ν hν A hA hre
  obtain ⟨fa, -, -, -, fsup, -, -, -⟩ := hf.1 1 one_pos β hβ
  have hc : CompactSpace (GaugeField 1) := fa.1
  set n := P.normal with hn
  set c := P.level with hcdef
  have hne : n ⬝ᵥ firstNonzeroBasisVec n = 1 := dotProduct_firstNonzeroBasisVec P.normal_mem
  have hfin : (observableSupport A).Finite := (fsup.1 A hA.1 hA.2.1).1
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ b ∈ observableSupport A,
      |n ⬝ᵥ (b.initial : AmbientSpace)| + |n ⬝ᵥ (b.terminal : AmbientSpace)| ≤ M := by
    obtain ⟨M, hM⟩ := (hfin.image
      fun b => |n ⬝ᵥ (b.initial : AmbientSpace)| + |n ⬝ᵥ (b.terminal : AmbientSpace)|).bddAbove
    exact ⟨M, fun b hb => hM ⟨b, hb, rfl⟩⟩
  let k : ℤ := ⌈(c + M) / 2⌉
  have hk : c + M ≤ 2 * (k : ℝ) := by
    have := Int.le_ceil ((c + M) / 2)
    linarith
  let N : ℕ := ⌈M + 2 * (k : ℝ) - c⌉₊
  have hN : M + 2 * (k : ℝ) - c ≤ N := Nat.le_ceil _
  let h : ℤ := 2 * ((N : ℤ) + 1)
  have hev : Even h := even_two_mul _
  have h2 : 2 ≤ h := by
    have : (0 : ℤ) ≤ N := Int.natCast_nonneg N
    simp only [h]
    omega
  have hhN : (N : ℝ) ≤ (h : ℝ) := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    simp only [h]
    push_cast
    linarith
  have hvP := intCast_two_mul_smul_firstNonzeroBasisVec_mem n k
  let v : LatticePoint 1 := ⟨_, evenLattice_le_latticeSubgroup hvP⟩
  have hvQ : v ∈ evenLattice.addSubgroupOf (latticeSubgroup 1) :=
    AddSubgroup.mem_addSubgroupOf.2 hvP
  have hheight : ∀ y : AmbientSpace, n ⬝ᵥ (y + (v : AmbientSpace)) = n ⬝ᵥ y + 2 * (k : ℝ) := by
    intro y
    change n ⬝ᵥ (y + ((2 * k : ℤ) : ℝ) • firstNonzeroBasisVec n) = _
    rw [dotProduct_add, dotProduct_smul, hne]
    simp
  let L : MirrorLadder := ⟨n, P.normal_mem, c, P.allowed, h, hev, h2⟩
  let A' := (shift v).actOn A
  have hA' : A' ∈ continuousLocalFunctions 1 := (fsup.2 A hA v).1
  have hin : ∀ y : AmbientSpace, |n ⬝ᵥ y| ≤ M → y + (v : AmbientSpace) ∈ L.slabSet := by
    intro y hy
    have hy' := abs_le.1 hy
    refine ⟨?_, ?_⟩
    · change c ≤ n ⬝ᵥ (y + (v : AmbientSpace))
      rw [hheight]
      linarith [hy'.1]
    · change n ⬝ᵥ (y + (v : AmbientSpace)) ≤ c + (h : ℝ)
      rw [hheight]
      linarith [hy'.2]
  have hslab : IsSupportedIn A' L.slabSet := by
    have hs : observableSupport A' = shiftLinks (observableSupport A) v :=
      (fsup.2 A hA v).2
    intro b' hb'
    rw [hs] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    have ht : |n ⬝ᵥ (b.initial : AmbientSpace)| ≤ M :=
      le_trans (le_add_of_nonneg_right (abs_nonneg _)) (hM b hb)
    have hh : |n ⬝ᵥ (b.terminal : AmbientSpace)| ≤ M :=
      le_trans (le_add_of_nonneg_left (abs_nonneg _)) (hM b hb)
    by_cases hp : ((shift v).linkMap b).IsPositivelyOriented
    · have he : ((shift v).linkMap b).orientedRepresentative = (shift v).linkMap b := by
        simp [Link.orientedRepresentative, hp]
      beta_reduce
      rw [he]
      exact ⟨hin _ ht, hin _ hh⟩
    · have he : ((shift v).linkMap b).orientedRepresentative =
          ((shift v).linkMap b).opposite := by
        simp [Link.orientedRepresentative, hp]
      beta_reduce
      rw [he]
      exact ⟨hin _ hh, hin _ ht⟩
  have hchain := classInclusions hf hi hβ P h hev h2
  obtain ⟨ν₀, hν₀, hle, hmir⟩ := (hi β hβ).2.1 L A' hA' (fun U => hre _) hslab ν (hchain.1 hν)
  have hν₀P : ν₀ ∈ gibbsClassOf β evenLattice :=
    hchain.2.2.2 ▸ hchain.2.2.1 hν₀
  obtain ⟨hinv, hpos⟩ := hmir P ⟨rfl, 0, by simp [L, hcdef]⟩
  refine ⟨ν₀, ⟨hν₀P, fun F hF => hinv F (isBoundedObservable_of_continuous hc hF),
    fun F hF => hpos F (Or.inl hF.1)⟩, ?_⟩
  have hνA : stateEval ν A' = stateEval ν A := hν.2 v hvQ A hA.1
  have hν₀A : stateEval ν₀ A' = stateEval ν₀ A := hν₀P.2 v hvQ A hA.1
  rw [← hνA, ← hν₀A]
  exact hle
theorem statement_holds (hf : BasicStructure.Statement)
    (hi : PeriodicGibbsFoldAndCompactness.Statement) : Statement := by
  intro β hβ P
  obtain ⟨-, hconv, hcomp⟩ :=
    (hi β hβ).2.2.1 1 one_pos (evenLattice.addSubgroupOf (latticeSubgroup 1))
  have hne := gibbsClassOf_evenLattice_nonempty hf hi hβ
  have hdom := dominates hf hi hβ P
  refine ⟨⟨hconv, hcomp, hne⟩, mirrorStatesCompact hf hβ P hconv hcomp,
    classInclusions hf hi hβ P, hdom, ?_⟩
  obtain ⟨ν, hν⟩ := hne
  obtain ⟨fa, -, -, -, -, -, -, -⟩ := hf.1 1 one_pos β hβ
  obtain ⟨ν₀, h₀, -⟩ := hdom ν hν (fun _ => 0) (fa.2.2.2.2.2.2.1 0) (fun _ => rfl)
  exact ⟨ν₀, h₀⟩
end MirrorDomination
end YangMills.Construction.InfiniteLattice

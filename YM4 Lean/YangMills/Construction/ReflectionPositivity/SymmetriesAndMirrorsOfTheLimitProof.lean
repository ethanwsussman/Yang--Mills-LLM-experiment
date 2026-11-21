import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfASpacingAndTheirActions
import YangMills.Construction.InfiniteLattice.StatesReflectionPositiveAtEveryLatticeMirror
import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBounded
import YangMills.Construction.ReflectionPositivity.ContinuityOfTheLimitOfABoundedLatticeApproximation
import YangMills.Construction.ReflectionPositivity.CovarianceAlgebraAndLocalisationOfTheRepresentatives
import YangMills.Construction.ReflectionPositivity.PropertiesOfTheFormOfAFunctionalProof
import YangMills.Construction.ReflectionPositivity.SymmetriesAndMirrorsOfTheLimit
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
open scoped ComplexConjugate ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LimitSymmetryArgument
open YangMills.Construction.ReflectionPositivity.RepresentativeCovariance
open YangMills.Construction.InfiniteLattice (IsSymmetricUnder LatticeSymmetry LatticePoint AmbientSpace
  refinedSpacing hyperoctahedralLinearGroup latticeMotionSymmetry localRegionObservables
  boundedRegionObservables hyperplaneReflect regionSigma regionSigma_mono latticeSubgroup)
open YangMills.Construction.LimitConventions (ApproxTriple cubicMotionGroup)
open YangMills.Construction.LatticeConventions (NormalHyperplane supNorm)
open YangMills.Construction.Mirrors (ReflectingHyperplane)
open YangMills.Construction.SeparatedTuples (FormalSpan TupleFunctional IsEuclidIsometry SepTuple push
  pushSpan formalMul spanIn conjugation linearExtend_basisVec basisVec supportedIn)
section Spacing
variable {L : ℕ}
theorem refinedSpacing_eq_inv_pow (K : ℕ) : refinedSpacing L K = ((L : ℝ) ^ K)⁻¹ := by
  simp [refinedSpacing, PeriodicLattice.meshSize]
theorem refinedSpacing_pos (hL : 1 < L) (K : ℕ) : 0 < refinedSpacing L K := by
  have h : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  rw [refinedSpacing_eq_inv_pow]
  exact inv_pos.mpr (pow_pos h K)
theorem tendsto_refinedSpacing_zero (hL : 1 < L) :
    Tendsto (fun K : ℕ => refinedSpacing L K) atTop (𝓝 0) := by
  have h : (1 : ℝ) < L := by exact_mod_cast hL
  simp_rw [refinedSpacing_eq_inv_pow]
  exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt h)
theorem exists_refinedSpacing_eq_int_mul (hL : 1 < L) {k K : ℕ} (h : k ≤ K) :
    ∃ q : ℤ, refinedSpacing L k = (q : ℝ) * refinedSpacing L K := by
  refine ⟨(L : ℤ) ^ (K - k), ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [refinedSpacing_eq_inv_pow, Nat.add_sub_cancel_left]
  push_cast
  rw [pow_add]
  field_simp
theorem exists_tendsto_int_mul_refinedSpacing_le (hL : 1 < L) (c : ℝ) :
    ∃ u : ℕ → ℝ, (∀ n, ∃ q : ℤ, u n = (q : ℝ) * refinedSpacing L n) ∧ (∀ n, u n ≤ c) ∧
      Tendsto u atTop (𝓝 c) := by
  refine ⟨fun n => (⌊c / refinedSpacing L n⌋ : ℝ) * refinedSpacing L n, fun n => ⟨_, rfl⟩, ?_, ?_⟩
  · intro n
    have ha := refinedSpacing_pos hL n
    have h := Int.floor_le (c / refinedSpacing L n)
    calc (⌊c / refinedSpacing L n⌋ : ℝ) * refinedSpacing L n
        ≤ c / refinedSpacing L n * refinedSpacing L n := mul_le_mul_of_nonneg_right h ha.le
      _ = c := div_mul_cancel₀ c ha.ne'
  · have hlow : Tendsto (fun n : ℕ => c - refinedSpacing L n) atTop (𝓝 c) := by
      simpa using tendsto_const_nhds.sub (tendsto_refinedSpacing_zero hL)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
      (fun n => ?_)
    · have ha := refinedSpacing_pos hL n
      have h := Int.lt_floor_add_one (c / refinedSpacing L n)
      have h2 : c < ((⌊c / refinedSpacing L n⌋ : ℝ) + 1) * refinedSpacing L n :=
        (div_lt_iff₀ ha).mp h
      simp only
      nlinarith
    · have ha := refinedSpacing_pos hL n
      have h := Int.floor_le (c / refinedSpacing L n)
      calc (⌊c / refinedSpacing L n⌋ : ℝ) * refinedSpacing L n
          ≤ c / refinedSpacing L n * refinedSpacing L n := mul_le_mul_of_nonneg_right h ha.le
        _ = c := div_mul_cancel₀ c ha.ne'
variable (T : ApproxTriple L)
theorem tendsto_scale_coe : Tendsto (fun j => ((T.cutoff j : ℕ+) : ℕ)) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [T.tendsto_cutoff.eventually_ge_atTop (⟨b + 1, Nat.succ_pos b⟩ : ℕ+)] with j hj
  have h : b + 1 ≤ ((T.cutoff j : ℕ+) : ℕ) := hj
  omega
theorem tendsto_refinedSpacing_scale (hL : 1 < L) :
    Tendsto (fun j => refinedSpacing L (T.cutoff j)) atTop (𝓝 0) :=
  (tendsto_refinedSpacing_zero hL).comp (tendsto_scale_coe T)
theorem eventually_int_mul_refinedSpacing_scale (hL : 1 < L) {k : ℕ} {c : ℝ}
    (hc : ∃ q : ℤ, c = (q : ℝ) * refinedSpacing L k) :
    ∀ᶠ j in atTop, ∃ q : ℤ, c = (q : ℝ) * refinedSpacing L (T.cutoff j) := by
  obtain ⟨q, rfl⟩ := hc
  filter_upwards [(tendsto_scale_coe T).eventually_ge_atTop k] with j hj
  obtain ⟨p, hp⟩ := exists_refinedSpacing_eq_int_mul hL hj
  refine ⟨q * p, ?_⟩
  rw [hp]
  push_cast
  ring
end Spacing
section Tuples
theorem pushSpan_basisVec (r : AmbientSpace → AmbientSpace) (X : SepTuple) :
    pushSpan r (basisVec X) = basisVec (push r X) := by
  simp [pushSpan, linearExtend_basisVec]
theorem basisVec_injective : Function.Injective basisVec :=
  Finsupp.single_left_injective one_ne_zero
theorem push_comp (hf : SeparatedTuples.BasicFacts.MainFacts) {r r' : AmbientSpace → AmbientSpace}
    (hr : IsEuclidIsometry r) (hr' : IsEuclidIsometry r') (X : SepTuple) :
    push (r ∘ r') X = push r (push r' X) := by
  have h := (hf.2.2.2.2.1 r r' hr hr' 0 0 (basisVec X)).1
  simp only [pushSpan_basisVec] at h
  exact basisVec_injective h
theorem push_translate_zero (hf : SeparatedTuples.BasicFacts.MainFacts) (X : SepTuple) :
    push (SeparatedTuples.translate 0) X = X := by
  have h := (hf.2.2.2.2.1 id id (fun _ _ => rfl) (fun _ _ => rfl) 0 0 (basisVec X)).2.2.1
  simp only [pushSpan_basisVec] at h
  exact basisVec_injective h
theorem nil_juxt (X : SepTuple) : SepTuple.juxt SepTuple.nil X = X := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.nil_juxt <;> assumption
theorem composable_nil_left (X : SepTuple) : SepTuple.Composable SepTuple.nil X :=
  fun f hf => by simp [SepTuple.nil] at hf
end Tuples
section Mirrors
def toNormalHyperplane (M : ReflectingHyperplane) (c : ℝ) : NormalHyperplane where
  normal := M.normalVec
  level := c
  normal_valid := by
    rcases M.normalVec_mem with ⟨μ, h⟩ | ⟨μ, ν, hlt, h⟩
    · exact Or.inl ⟨μ, h⟩
    · exact Or.inr ⟨μ, ν, hlt.ne, h⟩
theorem toNormalHyperplane_reflect (M : ReflectingHyperplane) :
    (toNormalHyperplane M M.offset).reflect = M.reflect := by
  rw [NormalHyperplane.reflect_eq_hyperplaneReflect, M.reflect_eq_hyperplaneReflect]
  rfl
theorem toNormalHyperplane_isLatticeMirror (M : ReflectingHyperplane) {c a : ℝ}
    (h : ∃ q : ℤ, c = (q : ℝ) * a) : (toNormalHyperplane M c).IsLatticeMirror a := by
  obtain ⟨q, hq⟩ := h
  refine ⟨fun _ => ⟨2 * q, ?_⟩, fun _ => ⟨q, hq⟩⟩
  change c = _
  rw [hq]
  push_cast
  ring
theorem normalVec_dotProduct_self_ne_zero (M : ReflectingHyperplane) :
    M.normalVec ⬝ᵥ M.normalVec ≠ 0 :=
  Mirrors.dotProduct_self_ne_zero_of_mem M.normalVec_mem
theorem isEuclidIsometry_reflect (M : ReflectingHyperplane) : IsEuclidIsometry M.reflect := by
  rw [M.reflect_eq_hyperplaneReflect]
  exact InfiniteLattice.euclidNormVec_hyperplaneReflect_sub (normalVec_dotProduct_self_ne_zero M) _
theorem hyperplaneReflect_eq_add_smul (n : AmbientSpace) (c c' : ℝ) (x : AmbientSpace) :
    hyperplaneReflect n c x = hyperplaneReflect n c' x + (2 * (c - c') / (n ⬝ᵥ n)) • n := by
  funext μ
  simp only [hyperplaneReflect, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem neg_two_mul_supNorm_le_dotProduct (M : ReflectingHyperplane) (d : AmbientSpace) :
    -(2 * supNorm d) ≤ M.normalVec ⬝ᵥ d := by
  have hab : ∀ μ, |d μ| ≤ supNorm d := fun μ =>
    Finset.le_sup' (fun μ => |d μ|) (Finset.mem_univ μ)
  have hnn : 0 ≤ supNorm d := (abs_nonneg _).trans (hab 0)
  rcases M.normalVec_mem with ⟨μ, h⟩ | ⟨μ, ν, -, h | h⟩
  · have e : M.normalVec ⬝ᵥ d = d μ := by
      rw [h]
      simp [PeriodicLattice.coordVec]
    rw [e]
    linarith [neg_abs_le (d μ), hab μ]
  · have e : M.normalVec ⬝ᵥ d = d μ + d ν := by
      rw [h]
      simp [PeriodicLattice.coordVec, add_dotProduct]
    rw [e]
    linarith [neg_abs_le (d μ), hab μ, neg_abs_le (d ν), hab ν]
  · have e : M.normalVec ⬝ᵥ d = d μ - d ν := by
      rw [h]
      simp [PeriodicLattice.coordVec, sub_dotProduct]
    rw [e]
    linarith [neg_abs_le (d μ), hab μ, le_abs_self (d ν), hab ν]
theorem exists_pos_gap (M : ReflectingHyperplane) {X : SepTuple} (hX : X ∈ supportedIn M.positiveSide) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ ⋃ f ∈ X.1, tsupport f, M.offset + 2 * δ ≤ M.normalVec ⬝ᵥ x := by
  have hK : IsCompact (⋃ f ∈ X.1, tsupport f) :=
    (List.finite_toSet X.1).isCompact_biUnion fun f hf => (X.2.1 f hf).2
  rcases (⋃ f ∈ X.1, tsupport f).eq_empty_or_nonempty with hE | hN
  · exact ⟨1, one_pos, fun x hx => by simp [hE] at hx⟩
  · have hcont : Continuous fun x : AmbientSpace => M.normalVec ⬝ᵥ x := by
      simp only [dotProduct]
      fun_prop
    obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hN hcont.continuousOn
    obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 hx₀
    have hpos : M.offset < M.normalVec ⬝ᵥ x₀ := hX f hf hxf
    refine ⟨(M.normalVec ⬝ᵥ x₀ - M.offset) / 2, by linarith, fun x hx => ?_⟩
    have h : M.normalVec ⬝ᵥ x₀ ≤ M.normalVec ⬝ᵥ x := hmin hx
    linarith
theorem supportHalo_subset_upperHalfSpace (M : ReflectingHyperplane) {X : SepTuple} {δ a : ℝ}
    (hδ : ∀ x ∈ ⋃ f ∈ X.1, tsupport f, M.offset + 2 * δ ≤ M.normalVec ⬝ᵥ x) (ha : 0 < a)
    (haδ : a ≤ δ) :
    supportHalo a X ⊆ (toNormalHyperplane M M.offset).upperHalfSpace := by
  intro y hy
  have h1 : LimitConventions.supDist y (⋃ f ∈ X.1, tsupport f) ≤
      ENNReal.ofReal (a / 2) := hy
  have h2 : LimitConventions.supDist y (⋃ f ∈ X.1, tsupport f) <
      ENNReal.ofReal a := h1.trans_lt ((ENNReal.ofReal_lt_ofReal_iff ha).2 (by linarith))
  obtain ⟨x, hx'⟩ := iInf_lt_iff.1 h2
  obtain ⟨hx, hxy⟩ := iInf_lt_iff.1 hx'
  have h3 : supNorm (y - x) < a := (ENNReal.ofReal_lt_ofReal_iff ha).1 hxy
  have h4 := neg_two_mul_supNorm_le_dotProduct M (y - x)
  rw [dotProduct_sub] at h4
  have h5 := hδ x hx
  change M.offset ≤ M.normalVec ⬝ᵥ y
  linarith
end Mirrors
section Values
variable {L : ℕ} (T : ApproxTriple L)
theorem spanRep_basisVec (j : ℕ+) (X : SepTuple) :
    T.spanRep j (basisVec X) = fun U => (T.tupleRep j X U : ℂ) := by
  simp [ApproxTriple.spanRep, linearExtend_basisVec]
theorem actOn_tupleRep {j : ℕ+} (hb : RepsCompatible T j)
    (r : LatticeSymmetry (refinedSpacing L (T.cutoff j))) (X : SepTuple) :
    r.actOn (fun U => (T.tupleRep j X U : ℂ)) =
      fun U => (T.tupleRep j (push r.toFun X) U : ℂ) := by
  have h := hb.1 r (basisVec X)
  rwa [spanRep_basisVec, pushSpan_basisVec, spanRep_basisVec] at h
theorem integral_tupleRep_push {j : ℕ+} (hb : RepsCompatible T j) (hl : RepsLocalized T j)
    (r : LatticeSymmetry (refinedSpacing L (T.cutoff j))) (hr : IsSymmetricUnder (T.state j) r)
    (X : SepTuple) :
    ∫ U, T.tupleRep j (push r.toFun X) U ∂T.state j =
      ∫ U, T.tupleRep j X U ∂T.state j := by
  have h := hr _ (hl X).2.1.1
  rw [actOn_tupleRep T hb, integral_complex_ofReal, integral_complex_ofReal] at h
  exact_mod_cast h
theorem integrable_tupleRep {j : ℕ+} (hl : RepsLocalized T j) (X : SepTuple) :
    Integrable (fun U => (T.tupleRep j X U : ℂ)) (T.state j) := by
  obtain ⟨hm, C, hC⟩ := (hl X).2.1.1
  exact Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC)
theorem sum_mem_regionObservables {a : ℝ} {S : Set AmbientSpace} {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (A : ι → InfiniteLattice.GaugeField a → ℂ)
    (h : ∀ b ∈ s, A b ∈ boundedRegionObservables a S) :
    (fun U => ∑ b ∈ s, c b * A b U) ∈ boundedRegionObservables a S := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨⟨?_, 0, fun U => by simp⟩, ?_⟩
    · simp
    · change Measurable[regionSigma S] _
      simp
  | insert b s hb ih =>
    have h1 := h b (Finset.mem_insert_self b s)
    have h2 := ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb')
    have he : (fun U => ∑ x ∈ insert b s, c x * A x U) =
        c b • A b + fun U => ∑ x ∈ s, c x * A x U := by
      funext U
      simp [Finset.sum_insert hb]
    rw [he]
    refine ⟨(h1.1.const_smul (c b)).add h2.1, ?_⟩
    have m1 : Measurable[regionSigma S] (A b) := h1.2
    have m2 : Measurable[regionSigma S] (fun U => ∑ x ∈ s, c x * A x U) := h2.2
    exact (m1.const_smul (c b)).add m2
theorem reflection_sum_nonneg_at {ι : Type*} (s : Finset ι) (X : ι → SepTuple) (c : ι → ℂ) {j : ℕ+}
    (hb : RepsCompatible T j) (hl : RepsLocalized T j)
    {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror (refinedSpacing L (T.cutoff j)))
    (hrp : NormalHyperplane.IsReflectionPositiveAcrossMirror hQ (T.state j))
    (hprod : ∀ b ∈ s, ∀ b' ∈ s, SepTuple.Composable (push Q.reflect (X b)) (X b'))
    (hside : ∀ b ∈ s, supportHalo (refinedSpacing L (T.cutoff j)) (X b) ⊆ Q.upperHalfSpace) :
    0 ≤ ∑ b ∈ s, ∑ b' ∈ s, conj (c b) * c b' *
      ((∫ U, T.tupleRep j (SepTuple.juxt (push Q.reflect (X b)) (X b')) U
        ∂T.state j : ℝ) : ℂ) := by
  classical
  set a := refinedSpacing L (T.cutoff j) with ha
  let G : InfiniteLattice.GaugeField a → ℂ :=
    fun U => ∑ b ∈ s, c b * (T.tupleRep j (X b) U : ℂ)
  have hG : G ∈ localRegionObservables a Q.upperHalfSpace := by
    refine Set.mem_iUnion₂.2 ⟨⋃ b ∈ s, supportHalo a (X b),
      (Bornology.isBounded_biUnion_finset s).2 fun b _ => (hl (X b)).2.2, ?_⟩
    refine sum_mem_regionObservables s c _ fun b hb' => ?_
    have h := (hl (X b)).2.1
    exact ⟨h.1, h.2.mono (regionSigma_mono (Set.subset_inter (hside b hb')
      (Set.subset_biUnion_of_mem (u := fun b => supportHalo a (X b)) hb'))) le_rfl⟩
  have h := hrp ⟨G, hG⟩
  have hpt : ∀ U, LatticeConventions.conjFun
        ((NormalHyperplane.reflectSymmetry hQ).actOn G) U * G U =
      ∑ b ∈ s, ∑ b' ∈ s, conj (c b) * c b' *
        (T.tupleRep j (SepTuple.juxt (push Q.reflect (X b)) (X b')) U : ℂ) := by
    intro U
    have h1 : (NormalHyperplane.reflectSymmetry hQ).actOn G U =
        ∑ b ∈ s, c b * (T.tupleRep j (push Q.reflect (X b)) U : ℂ) :=
      Finset.sum_congr rfl fun b _ => congrArg (c b * ·)
        (congrFun (actOn_tupleRep T hb (NormalHyperplane.reflectSymmetry hQ) (X b)) U)
    change conj ((NormalHyperplane.reflectSymmetry hQ).actOn G U) * G U = _
    rw [h1, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b hb1 => ?_
    simp only [G]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' hb2 => ?_
    rw [hb.2.1 _ _ (hprod b hb1 b' hb2)]
    simp only [map_mul, Complex.conj_ofReal, Pi.mul_apply, Complex.ofReal_mul]
    ring
  have hform : NormalHyperplane.reflectionForm hQ (T.state j) ⟨G, hG⟩ ⟨G, hG⟩ =
      ∑ b ∈ s, ∑ b' ∈ s, conj (c b) * c b' *
        ((∫ U, T.tupleRep j (SepTuple.juxt (push Q.reflect (X b)) (X b')) U
          ∂T.state j : ℝ) : ℂ) := by
    change ∫ U, LatticeConventions.conjFun
      ((NormalHyperplane.reflectSymmetry hQ).actOn G) U * G U ∂T.state j = _
    simp_rw [hpt]
    rw [integral_finsetSum _ fun b _ => integrable_finsetSum _ fun b' _ =>
      (integrable_tupleRep T hl _).const_mul _]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finsetSum _ fun b' _ => (integrable_tupleRep T hl _).const_mul _]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [integral_const_mul, integral_complex_ofReal]
  rw [hform] at h
  exact (SeparatedTupleFunctionals.isRealNonneg_iff _).1 h
end Values
section Limit
variable {L : ℕ} (T : ApproxTriple L)
structure LimitHypotheses (σ : SepTuple → ℝ) : Prop where
  one_lt_L : 1 < L
  converges : ApproxTriple.ConvergesTo T σ
  reflPos : ApproxTriple.IsReflPos T
  compatible : ∀ j, RepsCompatible T j
  localized : ∀ j, RepsLocalized T j
  symmetric : ∀ (j : ℕ+) (r : LatticeSymmetry (refinedSpacing L (T.cutoff j))),
    IsSymmetricUnder (T.state j) r
  mem_motions : ∀ (j : ℕ+) (r : LatticeSymmetry (refinedSpacing L (T.cutoff j))),
    r.toFun ∈ InfiniteLattice.affineHyperoctahedralMaps (refinedSpacing L (T.cutoff j))
  tupleFacts : SeparatedTuples.BasicFacts.MainFacts
  translationContinuous : LimitContinuity.TranslationContinuousOnTuples σ
variable {T} {σ : SepTuple → ℝ}
theorem LimitHypotheses.eq_of_eventually_symmetry (H : LimitHypotheses T σ)
    {ρ : AmbientSpace → AmbientSpace}
    (h : ∀ᶠ j in atTop, ∃ r : LatticeSymmetry (refinedSpacing L (T.cutoff j)), r.toFun = ρ)
    (X : SepTuple) : σ (push ρ X) = σ X := by
  refine tendsto_nhds_unique_of_eventuallyEq (H.converges (push ρ X)) (H.converges X) ?_
  filter_upwards [h] with j hj
  obtain ⟨r, rfl⟩ := hj
  exact integral_tupleRep_push T (H.compatible j) (H.localized j) r (H.symmetric j r) X
theorem LimitHypotheses.translate_invariant (H : LimitHypotheses T σ) (v : AmbientSpace)
    (X : SepTuple) : σ (push (SeparatedTuples.translate v) X) = σ X := by
  choose u hu1 _ hu3 using fun μ => exists_tendsto_int_mul_refinedSpacing_le H.one_lt_L (v μ)
  have hlim : Tendsto (fun n μ => u μ n) atTop (𝓝 v) := tendsto_pi_nhds.2 hu3
  have hinv : ∀ n : ℕ, σ (push (SeparatedTuples.translate fun μ => u μ n) X) = σ X := by
    intro n
    refine H.eq_of_eventually_symmetry ?_ X
    have hall : ∀ᶠ j in atTop, ∀ μ : Fin 4,
        ∃ q : ℤ, u μ n = (q : ℝ) * refinedSpacing L (T.cutoff j) :=
      eventually_all.2 fun μ => eventually_int_mul_refinedSpacing_scale T H.one_lt_L (hu1 μ n)
    filter_upwards [hall] with j hj
    choose q hq using hj
    exact ⟨InfiniteLattice.shift ⟨fun μ => u μ n, q, hq⟩, rfl⟩
  obtain ⟨δ, -, -, ht, -⟩ := H.translationContinuous X SepTuple.nil v (composable_nil_left _)
  have ht' := ht.comp hlim
  simp only [Function.comp_def, nil_juxt, hinv] at ht'
  exact tendsto_nhds_unique ht' tendsto_const_nhds
theorem exists_latticeSymmetry_of_mem (a : ℝ) {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace}
    (hw : w ∈ hyperoctahedralLinearGroup) : ∃ r : LatticeSymmetry a, r.toFun = w :=
  ⟨latticeMotionSymmetry ⟨w, (w : AmbientSpace →ₗ[ℝ] AmbientSpace),
    (InfiniteLattice.linearMap_mem_hypercubicGroup_iff w).mpr hw, 0, zero_mem _,
    fun x => by simp⟩, rfl⟩
theorem isEuclidIsometry_of_mem {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace}
    (hw : w ∈ hyperoctahedralLinearGroup) : IsEuclidIsometry w := by
  obtain ⟨r, hr⟩ := exists_latticeSymmetry_of_mem 1 hw
  rw [← hr]
  exact r.preservesDist
theorem LimitHypotheses.motion_invariant (H : LimitHypotheses T σ) {r : Equiv.Perm AmbientSpace}
    (hr : r ∈ cubicMotionGroup) (X : SepTuple) : σ (push r X) = σ X := by
  obtain ⟨w, hw, v, h⟩ := hr
  have hcomp : ⇑r = SeparatedTuples.translate v ∘ ⇑w := funext h
  rw [hcomp, push_comp H.tupleFacts (SeparatedTuples.isEuclidIsometry_translate v)
    (isEuclidIsometry_of_mem hw), H.translate_invariant]
  exact H.eq_of_eventually_symmetry
    (Eventually.of_forall fun j => exists_latticeSymmetry_of_mem _ hw) X
theorem LimitHypotheses.exists_motion_eq_reflect (H : LimitHypotheses T σ) (M : ReflectingHyperplane) :
    ∃ r ∈ cubicMotionGroup, ⇑r = M.reflect := by
  have hQ := toNormalHyperplane_isLatticeMirror M (c := 0)
    (a := refinedSpacing L (T.cutoff 1)) ⟨0, by simp⟩
  obtain ⟨w, hw, v, hv⟩ := H.mem_motions 1 (NormalHyperplane.reflectSymmetry hQ)
  have hrefl : ∀ x, (toNormalHyperplane M 0).reflect x = w x + (v : AmbientSpace) :=
    fun x => congrFun hv x
  have hzero : (toNormalHyperplane M 0).reflect 0 = 0 := by
    rw [NormalHyperplane.reflect_eq_hyperplaneReflect]
    funext μ
    simp [hyperplaneReflect, toNormalHyperplane]
  have hv0 : (v : AmbientSpace) = 0 := by
    have h := hrefl 0
    rw [hzero, map_zero, zero_add] at h
    exact h.symm
  have hinv : Function.Involutive M.reflect := by
    intro x
    rw [M.reflect_eq_hyperplaneReflect]
    exact InfiniteLattice.hyperplaneReflect_hyperplaneReflect (normalVec_dotProduct_self_ne_zero M) _ x
  refine ⟨hinv.toPerm, ⟨w, hw, (2 * (M.offset - 0) / (M.normalVec ⬝ᵥ M.normalVec)) • M.normalVec,
    fun x => ?_⟩, rfl⟩
  have h := hrefl x
  rw [hv0, add_zero, NormalHyperplane.reflect_eq_hyperplaneReflect] at h
  change M.reflect x = _
  rw [M.reflect_eq_hyperplaneReflect, hyperplaneReflect_eq_add_smul M.normalVec M.offset 0 x, ← h]
  rfl
theorem LimitHypotheses.reflection_sum_nonneg_of_lattice_offset (H : LimitHypotheses T σ)
    (M : ReflectingHyperplane) {k : ℕ}
    (hc : ∃ q : ℤ, M.offset = (q : ℝ) * refinedSpacing L k) {ι : Type*} (s : Finset ι)
    (X : ι → SepTuple) (hX : ∀ b ∈ s, X b ∈ supportedIn M.positiveSide) (c : ι → ℂ) :
    0 ≤ ∑ b ∈ s, ∑ b' ∈ s, conj (c b) * c b' *
      (σ (SepTuple.juxt (push M.reflect (X b)) (X b')) : ℂ) := by
  have hlimit : Tendsto (fun j => ∑ b ∈ s, ∑ b' ∈ s, conj (c b) * c b' *
      ((∫ U, T.tupleRep j (SepTuple.juxt (push M.reflect (X b)) (X b')) U
        ∂T.state j : ℝ) : ℂ)) atTop
      (𝓝 (∑ b ∈ s, ∑ b' ∈ s, conj (c b) * c b' *
        (σ (SepTuple.juxt (push M.reflect (X b)) (X b')) : ℂ))) :=
    tendsto_finsetSum _ fun b _ => tendsto_finsetSum _ fun b' _ =>
      tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp (H.converges _))
  refine ge_of_tendsto hlimit ?_
  have hev : ∀ᶠ j in atTop, ∀ b ∈ s,
      supportHalo (refinedSpacing L (T.cutoff j)) (X b) ⊆
        (toNormalHyperplane M M.offset).upperHalfSpace := by
    refine (Filter.eventually_all_finset s).2 fun b hb => ?_
    obtain ⟨δ, hδ, hm⟩ := exists_pos_gap M (hX b hb)
    filter_upwards [(tendsto_refinedSpacing_scale T H.one_lt_L).eventually_le_const hδ] with j hj
    exact supportHalo_subset_upperHalfSpace M hm (refinedSpacing_pos H.one_lt_L _) hj
  filter_upwards [hev, eventually_int_mul_refinedSpacing_scale T H.one_lt_L hc] with j hj hq
  have hQ := toNormalHyperplane_isLatticeMirror M hq
  have h := reflection_sum_nonneg_at T s X c (H.compatible j) (H.localized j) hQ
    ((H.reflPos j).2 _ hQ)
    (fun b hb b' hb' => by
      rw [toNormalHyperplane_reflect]
      exact (H.tupleFacts.2.2.1 M (X b) (X b') (hX b hb) (hX b' hb')).2) hj
  rwa [toNormalHyperplane_reflect] at h
theorem LimitHypotheses.reflection_sum_nonneg (H : LimitHypotheses T σ) (M : ReflectingHyperplane)
    {ι : Type*} (s : Finset ι) (X : ι → SepTuple) (hX : ∀ b ∈ s, X b ∈ supportedIn M.positiveSide)
    (c : ι → ℂ) :
    0 ≤ ∑ b ∈ s, ∑ b' ∈ s, conj (c b) * c b' *
      (σ (SepTuple.juxt (push M.reflect (X b)) (X b')) : ℂ) := by
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_tendsto_int_mul_refinedSpacing_le H.one_lt_L M.offset
  let N : ℕ → ReflectingHyperplane := fun n => ⟨M.normalVec, M.normalVec_mem, u n⟩
  let t : ℕ → AmbientSpace :=
    fun n => (2 * (u n - M.offset) / (M.normalVec ⬝ᵥ M.normalVec)) • M.normalVec
  have hrefl : ∀ n, (N n).reflect = SeparatedTuples.translate (t n) ∘ M.reflect := by
    intro n
    funext x
    change hyperplaneReflect M.normalVec (u n) x = hyperplaneReflect M.normalVec M.offset x + t n
    exact hyperplaneReflect_eq_add_smul M.normalVec (u n) M.offset x
  have ht : Tendsto t atTop (𝓝 0) := by
    have h : Tendsto (fun n => 2 * (u n - M.offset) / (M.normalVec ⬝ᵥ M.normalVec)) atTop
        (𝓝 0) := by
      simpa using (((hu3.sub_const M.offset).const_mul 2).div_const (M.normalVec ⬝ᵥ M.normalVec))
    simpa using h.smul_const M.normalVec
  have hN : ∀ n, 0 ≤ ∑ b ∈ s, ∑ b' ∈ s, conj (c b) * c b' *
      (σ (SepTuple.juxt (push (N n).reflect (X b)) (X b')) : ℂ) := by
    intro n
    refine H.reflection_sum_nonneg_of_lattice_offset (N n) (hu1 n) s X (fun b hb f hf x hx => ?_) c
    have h1 : M.offset < M.normalVec ⬝ᵥ x := hX b hb f hf hx
    exact show u n < M.normalVec ⬝ᵥ x from (hu2 n).trans_lt h1
  have hlimit : Tendsto (fun n => ∑ b ∈ s, ∑ b' ∈ s, conj (c b) * c b' *
      (σ (SepTuple.juxt (push (N n).reflect (X b)) (X b')) : ℂ)) atTop
      (𝓝 (∑ b ∈ s, ∑ b' ∈ s, conj (c b) * c b' *
        (σ (SepTuple.juxt (push M.reflect (X b)) (X b')) : ℂ))) := by
    refine tendsto_finsetSum _ fun b hb => tendsto_finsetSum _ fun b' hb' =>
      tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp ?_)
    have hdef : SepTuple.Composable (X b') (push (SeparatedTuples.translate 0) (push M.reflect (X b))) := by
      rw [push_translate_zero H.tupleFacts]
      have h := (H.tupleFacts.2.2.1 M (X b) (X b') (hX b hb) (hX b' hb')).2
      exact fun f hf g hg => (h g hg f hf).symm
    obtain ⟨δ, -, -, -, hlim⟩ := H.translationContinuous (push M.reflect (X b)) (X b') 0 hdef
    have h := hlim.comp ht
    rw [push_translate_zero H.tupleFacts] at h
    refine h.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [hrefl n, push_comp H.tupleFacts (SeparatedTuples.isEuclidIsometry_translate _)
      (isEuclidIsometry_reflect M)]
  exact ge_of_tendsto' hlimit hN
end Limit
theorem spanExtension_basisVec (F : TupleFunctional) (X : SepTuple) :
    F.spanExtension (basisVec X) = (F X : ℂ) := by
  simp [TupleFunctional.spanExtension, linearExtend_basisVec]
theorem spanExtension_formalMul_sum (F : TupleFunctional) (θ : AmbientSpace → AmbientSpace)
    {ι : Type*} (s : Finset ι) (X : ι → SepTuple) (c : ι → ℂ) :
    F.spanExtension (formalMul
        (pushSpan θ (conjugation (∑ b ∈ s, c b • basisVec (X b))))
        (∑ b ∈ s, c b • basisVec (X b))) =
      ∑ b ∈ s, ∑ b' ∈ s, conj (c b) * c b' * (F (SepTuple.juxt (push θ (X b)) (X b')) : ℂ) := by
  have h : pushSpan θ (conjugation (∑ b ∈ s, c b • basisVec (X b))) =
      ∑ b ∈ s, conj (c b) • basisVec (push θ (X b)) := by
    rw [SeparatedTuples.conjugation_sum]
    simp only [map_sum, map_smul, pushSpan_basisVec]
  rw [h, SeparatedTuples.formalMul_sum]
  simp only [map_sum, map_smul, spanExtension_basisVec, smul_eq_mul]
theorem limitHasSymmetries
    (hbounded : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (hcontinuity : ReflectionPositivity.LimitContinuity.LimitIsContinuousFunctional)
    (hcovariance : ReflectionPositivity.RepresentativeCovariance.RepresentativesCovariantAndLocal)
    (hstates : LatticeConventions.ReflectionPositiveStates.Statement)
    (hfacts : SeparatedTuples.BasicFacts.MainFacts) :
    ReflectionPositivity.LimitSymmetries.LimitHasSymmetries := by
  intro D T σ hbd hrp hlim
  have hL := D.isAdmissible
  have hL1 : 1 < D.L := by
    have := hL.2
    omega
  obtain ⟨C, hC⟩ := ((hbounded.2.2 D T).2.1).1 hbd
  obtain ⟨F, rfl, hsym, hmul, -, hcont, -, htrans, -⟩ := hcontinuity D T C σ hbd hC hlim
  have H : LimitHypotheses T F.toFun :=
    { one_lt_L := hL1
      converges := hlim
      reflPos := hrp
      compatible := fun j => (hcovariance D.L hL T j).2.1
      localized := fun j => (hcovariance D.L hL T j).2.2.1
      symmetric := fun j =>
        (hstates ⟨refinedSpacing D.L (T.cutoff j), refinedSpacing_pos hL1 _⟩ (T.state j) (hrp j).1
          (hrp j).2).1.1
      mem_motions := fun j r => (hcovariance D.L hL T j).1 r |>.1
      tupleFacts := hfacts
      translationContinuous := htrans }
  refine ⟨F.map_nil, ⟨hsym, hmul, hcont⟩, ⟨fun r hr X => H.motion_invariant hr X, fun M => ?_⟩,
    fun M => ⟨fun Z hZ => ?_, fun J _ X hX c =>
      H.reflection_sum_nonneg M Finset.univ X (fun b _ => hX b) c⟩⟩
  · obtain ⟨r, hr, he⟩ := H.exists_motion_eq_reflect M
    refine ⟨⟨r, hr, he⟩, fun X => ?_⟩
    rw [← he]
    exact H.motion_invariant hr X
  · obtain ⟨f, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hZ
    rw [SeparatedTupleFunctionals.isRealNonneg_iff]
    have h := H.reflection_sum_nonneg M f.support (fun b => b.1) (fun b _ => b.2) f
    have e := spanExtension_formalMul_sum F M.reflect f.support (fun b => b.1) f
    simp only [Finsupp.sum]
    exact e ▸ h
end YangMills.Construction.ReflectionPositivity.LimitSymmetryArgument
end

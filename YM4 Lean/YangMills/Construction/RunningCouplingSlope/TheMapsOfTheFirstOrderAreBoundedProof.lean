import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.SumsOfExponentials
import YangMills.Construction.RunningCouplingSlope.ColourCoordinatesOfATower
import YangMills.Construction.RunningCouplingSlope.EvaluationsOfKernelsOnASide
import YangMills.Construction.RunningCouplingSlope.GradientAndMultiplierAtALeastPointProof
import YangMills.Construction.RunningCouplingSlope.TheMapsOfTheFirstOrderAreBounded
import YangMills.Construction.Towers.CellsAndClassesOfThePeriodicExtension
import YangMills.Construction.Towers.ImagesUnderTheResponseReadAtTheSideInfinity
import YangMills.Construction.Towers.MapsOfTheResponseAndTheirTransposesProof
import Mathlib
set_option autoImplicit false
open Filter Set
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FirstVariationBounds
open Matrices
open Tower Tower.CriticalBranchResponse
open PeriodicOperators (PeriodicData IsPeriodic ExpDecay castVec expHalfSum applyKernel
  ApplySummableAt)
open TorusMetric (euclidNormVec)
section Schur
variable {I I' : PeriodicData}
private theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
private def classSpread (I : PeriodicData) (c : ℝ) : ℝ :=
  (Nat.card I.UnitQuot : ℝ) * (Real.exp (2 * c) * expHalfSum c ^ 4)
private theorem translate_cancel (hI : IsPeriodic I) {a b : Fin 4 → ℤ} {x : I.Carrier}
    (h : I.translate a x = I.translate b x) : a = b := by
  have h1 : I.translate (a + -b) x = x := by
    rw [hI.translate_add, h, ← hI.translate_add, add_neg_cancel, hI.translate_zero]
  have h2 := hI.free _ _ h1
  exact add_neg_eq_zero.mp h2
private theorem unfold_bijective (hI : IsPeriodic I) {J : Type} {q : I.Carrier → J} {s : ℕ}
    (hs : 0 < s) (hq : IsPeriodicQuotient I q s) {ρ : J → I.Carrier} (hρ : ∀ j, q (ρ j) = j) :
    Function.Bijective (fun p : J × (Fin 4 → ℤ) => I.translate (s • p.2) (ρ p.1)) := by
  refine ⟨?_, fun ι => ?_⟩
  · rintro ⟨j, m⟩ ⟨j', m'⟩ h
    simp only at h
    have e : ∀ (j : J) (m : Fin 4 → ℤ), q (I.translate (s • m) (ρ j)) = j := fun j m => by
      rw [← (hq.eq_iff_exists_translate _ _).2 ⟨m, rfl⟩, hρ]
    have ej : j = j' := by rw [← e j m, h, e]
    subst ej
    have em := translate_cancel hI h
    have : m = m' := by
      funext μ
      have := congrFun em μ
      simp only [Pi.smul_apply, nsmul_eq_mul] at this
      exact mul_left_cancel₀ (by exact_mod_cast hs.ne') this
    rw [this]
  · obtain ⟨m, hm⟩ := (hq.eq_iff_exists_translate (ρ (q ι)) ι).1 (hρ _)
    exact ⟨(q ι, m), hm.symm⟩
private def unfoldIdx (I : PeriodicData) (s : ℕ) {J : Type} (ρ : J → I.Carrier)
    (p : J × (Fin 4 → ℤ)) : I.Carrier := I.translate (s • p.2) (ρ p.1)
private def periodSlice (I : PeriodicData) (s : ℕ) {J : Type} (ρ : J → I.Carrier) (c : ℝ)
    (y : Fin 4 → ℝ) (j : J) : ℝ :=
  ∑' m : Fin 4 → ℤ, Real.exp (-c * euclidNormVec (I.pos (unfoldIdx I s ρ (j, m)) - y))
private theorem periodSlice_nonneg (I : PeriodicData) (s : ℕ) {J : Type} (ρ : J → I.Carrier)
    (c : ℝ) (y : Fin 4 → ℝ) (j : J) : 0 ≤ periodSlice I s ρ c y j :=
  tsum_nonneg fun _ => (Real.exp_pos _).le
private theorem periodSlice_sum_le (hE : PeriodicOperators.ExponentialSums.Bounds)
    (hI : IsPeriodic I) {c : ℝ}
    (hc : 0 < c) {J : Type} [Fintype J] {q : I.Carrier → J} {s : ℕ} (hs : 0 < s)
    (hq : IsPeriodicQuotient I q s) {ρ : J → I.Carrier} (hρ : ∀ j, q (ρ j) = j) (y : Fin 4 → ℝ) :
    Summable (fun p : J × (Fin 4 → ℤ) =>
        Real.exp (-c * euclidNormVec (I.pos (unfoldIdx I s ρ p) - y))) ∧
      ∑ j, periodSlice I s ρ c y j ≤ classSpread I c := by
  obtain ⟨h1, h2⟩ := (hE c hc).2.2 I hI y
  have hb : Function.Bijective (unfoldIdx I s ρ) := unfold_bijective hI hs hq hρ
  have h3 : Summable (fun p : J × (Fin 4 → ℤ) =>
      Real.exp (-c * euclidNormVec (I.pos (unfoldIdx I s ρ p) - y))) :=
    (Equiv.ofBijective _ hb).summable_iff.mpr h1
  refine ⟨h3, ?_⟩
  have h5 := (Equiv.ofBijective _ hb).tsum_eq
    (fun ι => Real.exp (-c * euclidNormVec (I.pos ι - y)))
  have h6 : ∑ j, periodSlice I s ρ c y j = ∑' ι, Real.exp (-c * euclidNormVec (I.pos ι - y)) := by
    rw [← h5]
    exact (tsum_fintype _).symm.trans h3.tsum_prod.symm
  rw [h6]
  exact h2
private theorem schur_test_finite {J J' : Type} [Fintype J] [Fintype J'] {Bm : J' → J → ℝ}
    (hB0 : ∀ j' j, 0 ≤ Bm j' j) {a : J → ℝ} {v : J' → ℝ} (hv0 : ∀ j', 0 ≤ v j')
    {C D D' : ℝ} (hD : 0 ≤ D)
    (hrow : ∀ j', ∑ j, Bm j' j ≤ D) (hcol : ∀ j, ∑ j', Bm j' j ≤ D')
    (hv : ∀ j', v j' ≤ C * ∑ j, Bm j' j * a j) :
    ∑ j', v j' ^ 2 ≤ C ^ 2 * D * D' * ∑ j, a j ^ 2 := by
  have hsq : ∀ j', v j' ^ 2 ≤ C ^ 2 * D * ∑ j, Bm j' j * a j ^ 2 := by
    intro j'
    have h1 : (∑ j, Bm j' j * a j) ^ 2 ≤ (∑ j, Bm j' j) * ∑ j, Bm j' j * a j ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ => hB0 j' j)
        (fun j _ => mul_nonneg (hB0 j' j) (by positivity)) (fun j _ => le_of_eq (by ring))
    have h2 : 0 ≤ ∑ j, Bm j' j * a j ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hB0 j' j) (by positivity)
    have h3 : v j' ^ 2 ≤ (C * ∑ j, Bm j' j * a j) ^ 2 := pow_le_pow_left₀ (hv0 _) (hv j') 2
    calc v j' ^ 2 ≤ C ^ 2 * (∑ j, Bm j' j * a j) ^ 2 := by rw [← mul_pow]; exact h3
      _ ≤ C ^ 2 * (D * ∑ j, Bm j' j * a j ^ 2) :=
          mul_le_mul_of_nonneg_left
            (h1.trans (mul_le_mul_of_nonneg_right (hrow j') h2)) (by positivity)
      _ = _ := by ring
  calc ∑ j', v j' ^ 2 ≤ ∑ j', C ^ 2 * D * ∑ j, Bm j' j * a j ^ 2 :=
        Finset.sum_le_sum fun j' _ => hsq j'
    _ = C ^ 2 * D * ∑ j, (∑ j', Bm j' j) * a j ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ ≤ C ^ 2 * D * ∑ j, D' * a j ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)
        exact mul_le_mul_of_nonneg_right (hcol j) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring
private theorem periodSlice_symm (hI : IsPeriodic I) (hI' : IsPeriodic I') {c : ℝ} {s : ℕ}
    {J J' : Type} (ρ : J → I.Carrier) (ρ' : J' → I'.Carrier) (j : J) (j' : J') :
    periodSlice I s ρ c (I'.pos (ρ' j')) j = periodSlice I' s ρ' c (I.pos (ρ j)) j' := by
  unfold periodSlice
  rw [← (Equiv.neg (Fin 4 → ℤ)).tsum_eq]
  refine tsum_congr fun m => ?_
  have e : I.pos (unfoldIdx I s ρ (j, (Equiv.neg (Fin 4 → ℤ)) m)) - I'.pos (ρ' j') =
      -(I'.pos (unfoldIdx I' s ρ' (j', m)) - I.pos (ρ j)) := by
    unfold unfoldIdx
    simp only [Equiv.neg_apply]
    rw [hI.pos_translate, hI'.pos_translate]
    funext μ
    simp [castVec]
    ring
  rw [e, euclidNormVec_neg]
private theorem norm_apply_le (hE : PeriodicOperators.ExponentialSums.Bounds) (hI : IsPeriodic I)
    {T : I.Carrier → ℂ} {C c : ℝ} (hc : 0 < c) {y : Fin 4 → ℝ}
    (hT : ∀ ι, ‖T ι‖ ≤ C * Real.exp (-c * euclidNormVec (I.pos ι - y)))
    {J : Type} [Fintype J] {q : I.Carrier → J} {s : ℕ} (hs : 0 < s) (hq : IsPeriodicQuotient I q s)
    {ρ : J → I.Carrier} (hρ : ∀ j, q (ρ j) = j) (g : J → ℂ) :
    ‖∑' ι, T ι * g (q ι)‖ ≤ C * ∑ j, periodSlice I s ρ c y j * ‖g j‖ := by
  have hb : Function.Bijective (unfoldIdx I s ρ) := unfold_bijective hI hs hq hρ
  obtain ⟨hsum, -⟩ := periodSlice_sum_le hE hI hc hs hq hρ y
  have he : ∀ p, q (unfoldIdx I s ρ p) = p.1 := fun p => by
    show q (I.translate (s • p.2) (ρ p.1)) = p.1
    rw [← (hq.eq_iff_exists_translate _ _).2 ⟨p.2, rfl⟩, hρ]
  have hv' : Summable (fun p : J × (Fin 4 → ℤ) =>
      Real.exp (-c * euclidNormVec (I.pos (unfoldIdx I s ρ p) - y)) * ‖g p.1‖) := by
    refine (summable_prod_of_nonneg fun p => by positivity).2 ⟨fun j => ?_,
      (hasSum_fintype _).summable⟩
    exact (hsum.prod_factor j).mul_right ‖g j‖
  have hv := hv'.mul_left C
  have hbd : ∀ p : J × (Fin 4 → ℤ), ‖T (unfoldIdx I s ρ p) * g (q (unfoldIdx I s ρ p))‖ ≤ C *
      (Real.exp (-c * euclidNormVec (I.pos (unfoldIdx I s ρ p) - y)) * ‖g p.1‖) := by
    intro p
    rw [norm_mul, he, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hT _) (norm_nonneg _)
  have hn : Summable fun p => ‖T (unfoldIdx I s ρ p) * g (q (unfoldIdx I s ρ p))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd hv
  have e1 : ∑' ι, T ι * g (q ι) = ∑' p, T (unfoldIdx I s ρ p) * g (q (unfoldIdx I s ρ p)) :=
    ((Equiv.ofBijective _ hb).tsum_eq fun ι => T ι * g (q ι)).symm
  have e2 : ∑' p : J × (Fin 4 → ℤ),
      Real.exp (-c * euclidNormVec (I.pos (unfoldIdx I s ρ p) - y)) * ‖g p.1‖ =
      ∑ j, periodSlice I s ρ c y j * ‖g j‖ := by
    rw [hv'.tsum_prod, tsum_fintype]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold periodSlice
    exact tsum_mul_right (f := fun m : Fin 4 → ℤ =>
      Real.exp (-c * euclidNormVec (I.pos (unfoldIdx I s ρ (j, m)) - y))) (a := ‖g j‖)
  rw [e1]
  calc _ ≤ ∑' p, ‖T (unfoldIdx I s ρ p) * g (q (unfoldIdx I s ρ p))‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' p : J × (Fin 4 → ℤ), C *
        (Real.exp (-c * euclidNormVec (I.pos (unfoldIdx I s ρ p) - y)) * ‖g p.1‖) :=
        hn.tsum_le_tsum hbd hv
    _ = _ := by rw [tsum_mul_left, e2]
private theorem schur_test (hE : PeriodicOperators.ExponentialSums.Bounds) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} {C c : ℝ} (hc : 0 < c)
    (hT : ExpDecay I I' T C c) {J J' : Type} [Fintype J] [Fintype J'] {q : I.Carrier → J}
    {q' : I'.Carrier → J'} {s : ℕ} (hs : 0 < s) (hq : IsPeriodicQuotient I q s)
    (hq' : IsPeriodicQuotient I' q' s)
    {g : J → ℂ} {g' : J' → ℂ} (hg : ∀ ι', g' (q' ι') = ∑' ι, T ι' ι * g (q ι)) :
    ∑ j', ‖g' j'‖ ^ 2 ≤ C ^ 2 * classSpread I c * classSpread I' c * ∑ j, ‖g j‖ ^ 2 := by
  choose ρ hρ using hq.surjective
  choose ρ' hρ' using hq'.surjective
  have hD0 : 0 ≤ classSpread I c := by unfold classSpread; positivity
  refine schur_test_finite (Bm := fun j' j => periodSlice I s ρ c (I'.pos (ρ' j')) j)
    (fun _ _ => periodSlice_nonneg _ _ _ _ _ _) (fun _ => norm_nonneg _) hD0
    (fun j' => (periodSlice_sum_le hE hI hc hs hq hρ _).2) (fun j => ?_) (fun j' => ?_)
  · simp only [periodSlice_symm hI hI' ρ ρ' j]
    exact (periodSlice_sum_le hE hI' hc hs hq' hρ' _).2
  · have h := norm_apply_le hE hI (T := T (ρ' j')) (y := I'.pos (ρ' j')) hc
      (fun ι => by
        have := hT (ρ' j') ι
        rwa [← euclidNormVec_neg, neg_sub] at this) hs hq hρ g
    rw [← hg, hρ'] at h
    exact h
end Schur
section Coefficients
private theorem combination_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
end Coefficients
section Norms
open PeriodicOperators (KernelMatrix wNorm wUnitBall)
open Tower.SmoothingContraction (TorusOpNormLE)
private theorem wNorm_meshWeight {τ : Type} [Fintype (Fin 3 × τ)] (b : ℝ) (u : Fin 3 × τ → ℂ) :
    wNorm (meshWeight b) u = Real.sqrt (b ^ 4 * ∑ ι, ‖u ι‖ ^ 2) := by
  unfold wNorm
  rw [tsum_fintype, Finset.mul_sum]
  rfl
private theorem sum_sq_inv_smul {τ : Type} [Fintype (Fin 3 × τ)] {t : ℝ} (ht : 0 < t)
    (u : Fin 3 × τ → ℂ) :
    ∑ ι, ‖(((t⁻¹ : ℝ) : ℂ) • u) ι‖ ^ 2 = (t ^ 2)⁻¹ * ∑ ι, ‖u ι‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    mul_pow, inv_pow]
private theorem sum_sq_apply_le {σ σ' : Type} [Fintype (Fin 3 × σ)] [Fintype (Fin 3 × σ')]
    {a a' : ℝ} {K : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')} (h : TorusOpNormLE a a' K 1)
    (f : Fin 3 × σ → ℂ) :
    a' ^ 4 * ∑ ι, ‖applyKernel K f ι‖ ^ 2 ≤ a ^ 4 * ∑ ι, ‖f ι‖ ^ 2 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hN⟩ : ∃ N, N = a ^ 4 * ∑ ι, ‖f ι‖ ^ 2 := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  rw [← hN]
  obtain ⟨t, ht⟩ : ∃ t, t = Real.sqrt (N + ε) := ⟨_, rfl⟩
  have ht2 : t ^ 2 = N + ε := by rw [ht]; exact Real.sq_sqrt (by positivity)
  have ht0 : 0 < t := by rw [ht]; exact Real.sqrt_pos.2 (by positivity)
  have hball : ((t⁻¹ : ℝ) : ℂ) • f ∈ wUnitBall (meshWeight a) univ := by
    refine ⟨mem_univ _, (hasSum_fintype _).summable, ?_⟩
    rw [wNorm_meshWeight, sum_sq_inv_smul ht0]
    refine Real.sqrt_le_iff.2 ⟨zero_le_one, ?_⟩
    have : a ^ 4 * ((t ^ 2)⁻¹ * ∑ ι, ‖f ι‖ ^ 2) = N / t ^ 2 := by
      rw [hN]
      field_simp
    rw [this, ht2, one_pow, div_le_one (by positivity)]
    linarith
  have h1 : ENNReal.ofReal (wNorm (meshWeight a')
      (applyKernel K (((t⁻¹ : ℝ) : ℂ) • f))) ≤ ENNReal.ofReal 1 :=
    le_trans (le_iSup₂ (f := fun g (_ : g ∈ wUnitBall (meshWeight a) univ) =>
      ENNReal.ofReal (wNorm (meshWeight a') (applyKernel K g))) _ hball) h.2
  have h2 := (ENNReal.ofReal_le_ofReal_iff zero_le_one).1 h1
  have e : applyKernel K (((t⁻¹ : ℝ) : ℂ) • f) = ((t⁻¹ : ℝ) : ℂ) • applyKernel K f := by
    funext p
    simp only [applyKernel, Pi.smul_apply, smul_eq_mul, tsum_fintype, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [e, wNorm_meshWeight, sum_sq_inv_smul ht0] at h2
  have h3 := (Real.sqrt_le_iff.1 h2).2
  rw [one_pow] at h3
  have h4 : a' ^ 4 * ∑ ι, ‖applyKernel K f ι‖ ^ 2 ≤ t ^ 2 := by
    have e' : a' ^ 4 * ((t ^ 2)⁻¹ * ∑ ι, ‖applyKernel K f ι‖ ^ 2) =
        (a' ^ 4 * ∑ ι, ‖applyKernel K f ι‖ ^ 2) / t ^ 2 := by
      field_simp
    rwa [e', div_le_one (by positivity)] at h3
  rwa [ht2] at h4
private theorem kernelOfBasisImages_apply (r r' : PauliComponentsOfSymmetricKernel)
    (m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2) (ι' : r'.Index)
    (ι : r.Index) (c : r.Index → ℂ) (h1 : c ι = 1) (h0 : ∀ x, x ≠ ι → c x = 0) :
    r.kernelOfBasisImages r' m ι' ι = r'.coeffs (m (r.ofCoeffs c)) ι' := by
  classical
  have e : ∀ d : DecidableEq r.Index, @Pi.single r.Index (fun _ => ℂ) _ d ι (1 : ℂ) = c := by
    intro d
    funext x
    by_cases hx : x = ι
    · subst hx
      rw [h1]
      simp
    · rw [h0 x hx]
      simp [hx]
  unfold PauliComponentsOfSymmetricKernel.kernelOfBasisImages PauliComponentsOfSymmetricKernel.mapOnCoeffs
  rw [e]
end Norms
section Levels
private structure Inputs : Prop where
  faces : Tower.FaceSums.FacesAndPairings
  coords : PauliCoordsOrthonormal
  expSums : PeriodicOperators.ExponentialSums.Bounds
  respImages : Tower.ResponseImagesFullSide.ResponseImagesHold
  indexSets : PeriodicOperators.TowerIndexSets.Claim
  liftCells : LocalKernels.PeriodicLiftCells.CellsAndClassesHold
  contraction : Tower.SmoothingContraction.Claim
  linValues : Tower.LinearMapValues.Statement
variable {L n k j : ℕ}
private abbrev pairRe (X Y : edgeFormSpace L n k j) : ℝ :=
  (edgeFormPairing (X : Edge L n k j → ComplexMatrix2) (Y : Edge L n k j → ComplexMatrix2)).re
private theorem finite_positiveEdge (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) : Finite (PositiveEdge L n k j) :=
  Set.finite_univ_iff.mp (((G.faces L hL k j hj).1 n hn).2.2.1 univ).2.1
private theorem finite_vertex (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) : Finite (Vertex L n k j) :=
  Set.finite_univ_iff.mp (((G.faces L hL k j hj).1 n hn).2.1 univ).2.1
private theorem exists_orthonormal_coords (G : Inputs)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) : ∃ (ι : Type) (_ : Fintype ι) (Ψ : edgeFormSpace L n k j ≃ₗ[ℝ] (ι → ℝ)),
      ∀ f g : edgeFormSpace L n k j, pairRe f g = ∑ i, Ψ f i * Ψ g i := by
  have hfin := finite_positiveEdge G hL hn hj
  let _ : Fintype (Fin 3 × PositiveEdge L n k j) := Fintype.ofFinite _
  obtain ⟨Ψ, -, hΨ⟩ := (G.coords L n k j hL hn hj).1
  exact ⟨_, inferInstance, Ψ, fun f g => by rw [pairRe, hΨ f g, Complex.ofReal_re]⟩
private theorem pairRe_add_left (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k)
    (X X' Y : edgeFormSpace L n k j) : pairRe (X + X') Y = pairRe X Y + pairRe X' Y := by
  obtain ⟨ι, _, Ψ, h⟩ := exists_orthonormal_coords G hL hn hj
  rw [h, h, h, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, Pi.add_apply, add_mul]
private theorem pairRe_smul_left (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k)
    (r : ℝ) (X Y : edgeFormSpace L n k j) : pairRe (r • X) Y = r * pairRe X Y := by
  obtain ⟨ι, _, Ψ, h⟩ := exists_orthonormal_coords G hL hn hj
  rw [h, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
private theorem pairRe_comm (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k)
    (X Y : edgeFormSpace L n k j) : pairRe X Y = pairRe Y X := by
  obtain ⟨ι, _, Ψ, h⟩ := exists_orthonormal_coords G hL hn hj
  rw [h, h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
private theorem pairRe_self_nonneg (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) (X : edgeFormSpace L n k j) : 0 ≤ pairRe X X := by
  obtain ⟨ι, _, Ψ, h⟩ := exists_orthonormal_coords G hL hn hj
  rw [h]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
private theorem eq_zero_of_pairRe_self (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) {X : edgeFormSpace L n k j} (h0 : pairRe X X = 0) : X = 0 := by
  obtain ⟨ι, _, Ψ, h⟩ := exists_orthonormal_coords G hL hn hj
  rw [h] at h0
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (Ψ X i)).mp h0
  apply Ψ.injective
  rw [map_zero]
  funext i
  exact mul_self_eq_zero.mp (h1 i (Finset.mem_univ i))
private theorem pairRe_zero (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) :
    pairRe (0 : edgeFormSpace L n k j) 0 = 0 := by
  obtain ⟨ι, _, Ψ, h⟩ := exists_orthonormal_coords G hL hn hj
  rw [h]
  simp
private theorem pairRe_smul_self (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k)
    (r : ℝ) (X : edgeFormSpace L n k j) : pairRe (r • X) (r • X) = r ^ 2 * pairRe X X := by
  obtain ⟨ι, _, Ψ, h⟩ := exists_orthonormal_coords G hL hn hj
  rw [h, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]
  ring
private theorem pairRe_add_self_le (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k)
    (X Y : edgeFormSpace L n k j) : pairRe (X + Y) (X + Y) ≤ 2 * pairRe X X + 2 * pairRe Y Y := by
  obtain ⟨ι, _, Ψ, h⟩ := exists_orthonormal_coords G hL hn hj
  rw [h, h, h, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [map_add, Pi.add_apply]
  nlinarith [sq_nonneg (Ψ X i - Ψ Y i)]
private theorem pairRe_self_eq_sum (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k)
    [Fintype (Fin 3 × PositiveEdge L n k j)] (X : edgeFormSpace L n k j) :
    pairRe X X = ∑ ι, ‖toPauliCoeffs (restrictToPositiveEdges
      (X : Edge L n k j → ComplexMatrix2)) ι‖ ^ 2 := by
  obtain ⟨Ψ, h1, h2⟩ := (G.coords L n k j hL hn hj).1
  rw [pairRe, h2, Complex.ofReal_re]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [h1, Complex.norm_real, Real.norm_eq_abs, sq_abs, sq]
private theorem quotient_of_edges (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) :
    IsPeriodicQuotient (PeriodicOperators.colourEdges L k j)
      (fun ι => ((ι.1, LocalKernels.projPositiveEdge L n k j ι.2) :
        Fin 3 × PositiveEdge L n k j))
      (LocalKernels.Periodisation.periodSide L n) := by
  have hcell := ((G.liftCells L hL k n hn).1 j hj).1 LocalKernels.CellType.edge
  have hsurj : Function.Surjective (LocalKernels.projPositiveEdge L n k j) := hcell.1
  have hiff : ∀ x y : PeriodicOperators.PosEdge L k j,
      LocalKernels.projPositiveEdge L n k j x =
          LocalKernels.projPositiveEdge L n k j y ↔
        ∃ m : Fin 4 → ℤ, y = PeriodicOperators.shiftEdge
          (LocalKernels.Periodisation.periodSide L n • m) x := hcell.2
  refine ⟨?_, fun i i' => ⟨fun h => ?_, ?_⟩⟩
  · rintro ⟨a, b⟩
    obtain ⟨x, hx⟩ := hsurj b
    exact ⟨(a, x), Prod.ext rfl hx⟩
  · obtain ⟨m, hm⟩ := (hiff _ _).1 (congrArg Prod.snd h)
    exact ⟨m, Prod.ext (congrArg Prod.fst h).symm hm⟩
  · rintro ⟨m, rfl⟩
    exact Prod.ext rfl ((hiff _ _).2 ⟨m, rfl⟩)
end Levels
section Response
open Tower.PeriodicForm (coeffsOnEdges)
variable {L n k i j : ℕ}
private theorem kernel_sq_bound (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hi : i ≤ k) (hj : j ≤ k)
    {T : (PeriodicOperators.colourEdges L k j).Carrier →
      (PeriodicOperators.colourEdges L k i).Carrier → ℂ}
    (hT : PeriodicOperators.IsPeriodicKernel (PeriodicOperators.colourEdges L k i)
      (PeriodicOperators.colourEdges L k j) T) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ, 0 < n → ∀ (X : edgeFormSpace L n k i) (Y : edgeFormSpace L n k j),
      coeffsOnEdges L n k j Y = applyKernel T (coeffsOnEdges L n k i X) →
        pairRe Y Y ≤ c * pairRe X X := by
  obtain ⟨-, C, δ, hC, hδ, hb⟩ := hT
  have hI := (G.indexSets L hL k i hi).2.1
  have hI' := (G.indexSets L hL k j hj).2.1
  refine ⟨C ^ 2 * classSpread (PeriodicOperators.colourEdges L k i) δ *
    classSpread (PeriodicOperators.colourEdges L k j) δ, by unfold classSpread; positivity, ?_⟩
  intro n hn X Y h
  have f1 := finite_positiveEdge G hL hn hi
  have f2 := finite_positiveEdge G hL hn hj
  let _ : Fintype (Fin 3 × PositiveEdge L n k i) := Fintype.ofFinite _
  let _ : Fintype (Fin 3 × PositiveEdge L n k j) := Fintype.ofFinite _
  have hs : 0 < LocalKernels.Periodisation.periodSide L n := by
    have hL0 : 0 < L := by
      have := hL.2
      omega
    exact Nat.mul_pos (by norm_num) (pow_pos hL0 n)
  rw [pairRe_self_eq_sum G hL hn hj, pairRe_self_eq_sum G hL hn hi]
  exact schur_test G.expSums hI hI' hδ hb hs (quotient_of_edges G hL hn hi)
    (quotient_of_edges G hL hn hj) (fun ι' => congrFun h ι')
private theorem coeffsOnEdges_injective (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) {Y Y' : edgeFormSpace L n k j}
    (h : coeffsOnEdges L n k j Y = coeffsOnEdges L n k j Y') : Y = Y' := by
  have f2 := finite_positiveEdge G hL hn hj
  let _ : Fintype (Fin 3 × PositiveEdge L n k j) := Fintype.ofFinite _
  obtain ⟨Ψ, h1, -⟩ := (G.coords L n k j hL hn hj).1
  apply Ψ.injective
  funext p
  obtain ⟨x, hx⟩ := (quotient_of_edges G hL hn hj).surjective p
  have e := congrFun h x
  have e' : toPauliCoeffs (restrictToPositiveEdges (Y : Edge L n k j → ComplexMatrix2)) p =
      toPauliCoeffs (restrictToPositiveEdges (Y' : Edge L n k j → ComplexMatrix2)) p := by
    rw [← hx]
    exact e
  rw [h1, h1] at e'
  exact_mod_cast e'
private theorem coeffsOnEdges_sub (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) (Y Y' : edgeFormSpace L n k j) :
    coeffsOnEdges L n k j ((Y - Y' : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2) =
      coeffsOnEdges L n k j Y - coeffsOnEdges L n k j Y' := by
  have f2 := finite_positiveEdge G hL hn hj
  let _ : Fintype (Fin 3 × PositiveEdge L n k j) := Fintype.ofFinite _
  obtain ⟨Ψ, h1, -⟩ := (G.coords L n k j hL hn hj).1
  funext ι
  show toPauliCoeffs (restrictToPositiveEdges
      ((Y - Y' : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2)) _ =
    toPauliCoeffs (restrictToPositiveEdges (Y : Edge L n k j → ComplexMatrix2)) _ -
      toPauliCoeffs (restrictToPositiveEdges (Y' : Edge L n k j → ComplexMatrix2)) _
  rw [h1, h1, h1, map_sub, Pi.sub_apply, Complex.ofReal_sub]
private theorem map_sub_of_kernel (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hi : i ≤ k)
    (hj : j ≤ k) {T : (PeriodicOperators.colourEdges L k j).Carrier →
      (PeriodicOperators.colourEdges L k i).Carrier → ℂ}
    {F : (Edge L n k i → ComplexMatrix2) → edgeFormSpace L n k j}
    (hF : ∀ X : edgeFormSpace L n k i, (∀ ι', ApplySummableAt T (coeffsOnEdges L n k i X) ι') ∧
      coeffsOnEdges L n k j (F X) = applyKernel T (coeffsOnEdges L n k i X))
    (B B' : edgeFormSpace L n k i) :
    F ((B : Edge L n k i → ComplexMatrix2) - B') = F B - F B' := by
  apply coeffsOnEdges_injective G hL hn hj
  rw [coeffsOnEdges_sub G hL hn hj, (hF B).2, (hF B').2]
  have h := (hF (B - B')).2
  rw [coeffsOnEdges_sub G hL hn hi] at h
  refine h.trans ?_
  funext ι'
  have s1 := ((hF B).1 ι').of_norm
  have s2 := ((hF B').1 ι').of_norm
  show ∑' ι, T ι' ι * (coeffsOnEdges L n k i B ι - coeffsOnEdges L n k i B' ι) =
    ∑' ι, T ι' ι * coeffsOnEdges L n k i B ι - ∑' ι, T ι' ι * coeffsOnEdges L n k i B' ι
  rw [← s1.tsum_sub s2]
  exact tsum_congr fun ι => mul_sub _ _ _
end Response
section Step
open PeriodicOperators (KernelMatrix)
open Tower.SmoothingContraction (TorusOpNormLE)
variable {L n k j : ℕ}
private theorem crossingSmoothing_add (hfin : Finite (Vertex L n k j))
    (A A' : Edge L n k j → ComplexMatrix2) :
    crossingSmoothing L n k j (A + A') =
      crossingSmoothing L n k j A + crossingSmoothing L n k j A' := by apply _root_.YangMills.SharedProofs.p41844 <;> assumption
private theorem crossingSmoothing_smul (hfin : Finite (Vertex L n k j)) (r : ℝ)
    (A : Edge L n k j → ComplexMatrix2) :
    crossingSmoothing L n k j (r • A) = r • crossingSmoothing L n k j A := by apply _root_.YangMills.Construction.Tower.ResponseMaps.crossingSmoothing_smul <;> assumption
private theorem crossingSmoothing_mem (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j) :
    crossingSmoothing L n k j B ∈ edgeFormSpace L n k (j + 1) :=
  (((((G.linValues L hL k).1 n hn).1 j hj).1 B hB).2.1)
private theorem isPositive_or_opposite (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
open Classical in
private theorem ofCoeffs_toPauliCoeffs (X : edgeFormSpace L n k j) :
    (edgePauliCoordinates L n k j).ofCoeffs
      (toPauliCoeffs (restrictToPositiveEdges (X : Edge L n k j → ComplexMatrix2))) =
      (X : Edge L n k j → ComplexMatrix2) := by
  have hdef : ∀ c : Fin 3 × PositiveEdge L n k j → ℂ, (edgePauliCoordinates L n k j).ofCoeffs c =
      extendOddly (fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0) :=
    fun c => rfl
  have hval : ∀ (b : Edge L n k j) (h : b.IsPositivelyOriented), ofPauliCoeffs
      (toPauliCoeffs (restrictToPositiveEdges (X : Edge L n k j → ComplexMatrix2))) ⟨b, h⟩ =
      (X : Edge L n k j → ComplexMatrix2) b := by
    intro b h
    have h1 : (X : Edge L n k j → ComplexMatrix2) b ∈ ComplexMatrix2.hermitianTraceless :=
      X.2.1 b h
    have hs : (X : Edge L n k j → ComplexMatrix2) b ∈ ComplexMatrix2.traceless := h1.2
    have e := combination_pauliCoeff hs
    unfold ofPauliCoeffs toPauliCoeffs restrictToPositiveEdges
    exact e
  refine (hdef _).trans ?_
  funext b
  by_cases hb : b.IsPositivelyOriented
  · have e : ∀ f : Edge L n k j → ComplexMatrix2, extendOddly f b = f b := fun f => if_pos hb
    rw [e, dif_pos hb]
    exact hval b hb
  · have hr : b.opposite.IsPositivelyOriented := (isPositive_or_opposite b).resolve_left hb
    have e : ∀ f : Edge L n k j → ComplexMatrix2, extendOddly f b = -f b.opposite :=
      fun f => if_neg hb
    rw [e, dif_pos hr]
    refine (congrArg Neg.neg (hval _ hr)).trans ?_
    rw [X.2.2 b, neg_neg]
private def levelGain (L k j : ℕ) : ℝ :=
  (L : ℝ) ^ 2 * meshAt L k j ^ 4 / meshAt L k (j + 1) ^ 4
private theorem levelGain_nonneg (L k j : ℕ) : 0 ≤ levelGain L k j := by
  unfold levelGain
  positivity
private theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
private theorem crossingSmoothing_sq_le (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) (X : edgeFormSpace L n k j)
    (Y : edgeFormSpace L n k (j + 1))
    (hY : (Y : Edge L n k (j + 1) → ComplexMatrix2) = crossingSmoothing L n k j X) :
    pairRe Y Y ≤ levelGain L k j * pairRe X X := by
  classical
  have hL0 : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  have f1 := finite_positiveEdge G hL hn hj.le
  have f2 := finite_positiveEdge G hL hn (show j + 1 ≤ k from hj)
  have fs := finite_vertex G hL hn hj.le
  let _ : Fintype (Fin 3 × PositiveEdge L n k j) := Fintype.ofFinite _
  let _ : Fintype (Fin 3 × PositiveEdge L n k (j + 1)) := Fintype.ofFinite _
  obtain ⟨Ψ, c1, -⟩ := (G.coords L n k j hL hn hj.le).1
  obtain ⟨Ψ', c2, -⟩ := (G.coords L n k (j + 1) hL hn hj).1
  let Cm : edgeFormSpace L n k j →ₗ[ℝ] edgeFormSpace L n k (j + 1) :=
    { toFun := fun Z => ⟨(L : ℝ)⁻¹ • crossingSmoothing L n k j Z,
        (edgeFormSpace L n k (j + 1)).smul_mem _ (crossingSmoothing_mem G hL hn hj Z.2)⟩
      map_add' := fun Z Z' => Subtype.ext (by
        show (L : ℝ)⁻¹ • crossingSmoothing L n k j ((Z : Edge L n k j → ComplexMatrix2) + Z') = _
        rw [crossingSmoothing_add fs, smul_add]
        rfl)
      map_smul' := fun r Z => Subtype.ext (by
        show (L : ℝ)⁻¹ • crossingSmoothing L n k j (r • (Z : Edge L n k j → ComplexMatrix2)) = _
        rw [crossingSmoothing_smul fs, smul_comm]
        rfl) }
  have hCm : ∀ Z : edgeFormSpace L n k j,
      ((Cm Z : edgeFormSpace L n k (j + 1)) : Edge L n k (j + 1) → ComplexMatrix2) =
      (L : ℝ)⁻¹ • crossingSmoothing L n k j Z := fun _ => rfl
  have hN := (((G.contraction L hL k hk).2.1 n hn).2.1 j hj).1
  have e0 : Real.exp (2 * TorusMetric.l1NormVec 0 * meshAt L k (j + 1)) = 1 := by
    simp [TorusMetric.l1NormVec]
  rw [e0] at hN
  obtain ⟨K, hKe⟩ : ∃ K : KernelMatrix (Fin 3 × PositiveEdge L n k j)
      (Fin 3 × PositiveEdge L n k (j + 1)), K = expConjOfMapAtZero
        (edgePauliCoordinates L n k j) (edgePauliCoordinates L n k (j + 1))
        (fun B => (L : ℝ)⁻¹ • crossingSmoothing L n k j B) := ⟨_, rfl⟩
  have hN' : TorusOpNormLE (meshAt L k j) (meshAt L k (j + 1)) K 1 := by
    rw [hKe]
    exact hN
  let E : Fin 3 × PositiveEdge L n k j → edgeFormSpace L n k j := fun ι =>
    Ψ.symm (fun x => if x = ι then 1 else 0)
  have hE : ∀ ι x, toPauliCoeffs (restrictToPositiveEdges (E ι : Edge L n k j → ComplexMatrix2)) x =
      (((if x = ι then 1 else 0 : ℝ)) : ℂ) := fun ι x => by
    rw [c1]
    simp only [E, LinearEquiv.apply_symm_apply]
  have hK : ∀ ι' ι, K ι' ι = ((Ψ' (Cm (E ι)) ι' : ℝ) : ℂ) := by
    intro ι' ι
    rw [hKe]
    change (edgePauliCoordinates L n k j).kernelOfBasisImages (edgePauliCoordinates L n k (j + 1))
      (fun B => (L : ℝ)⁻¹ • crossingSmoothing L n k j B) ι' ι = _
    refine (kernelOfBasisImages_apply (edgePauliCoordinates L n k j) (edgePauliCoordinates L n k (j + 1)) _ ι' ι
      (toPauliCoeffs (restrictToPositiveEdges (E ι : Edge L n k j → ComplexMatrix2))) ?_ ?_).trans ?_
    · exact (hE ι ι).trans (by simp)
    · intro x hx
      refine (hE ι x).trans ?_
      split_ifs with h
      · exact absurd h hx
      · simp
    · rw [ofCoeffs_toPauliCoeffs (E ι)]
      exact c2 (Cm (E ι)) ι'
  have hexp : ∀ Z : edgeFormSpace L n k j, Z = ∑ ι, Ψ Z ι • E ι := by
    intro Z
    apply Ψ.injective
    rw [map_sum]
    funext x
    rw [Finset.sum_apply]
    simp [E]
  have hact : applyKernel K (toPauliCoeffs (restrictToPositiveEdges
      (X : Edge L n k j → ComplexMatrix2))) =
      toPauliCoeffs (restrictToPositiveEdges ((Cm X : edgeFormSpace L n k (j + 1)) :
        Edge L n k (j + 1) → ComplexMatrix2)) := by
    funext ι'
    rw [c2]
    have e1 : Ψ' (Cm X) ι' = ∑ ι, Ψ X ι * Ψ' (Cm (E ι)) ι' := by
      conv_lhs => rw [hexp X]
      rw [map_sum, map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun ι _ => ?_
      rw [map_smul, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [e1, Complex.ofReal_sum]
    show ∑' ι, K ι' ι * _ = _
    rw [tsum_fintype]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [hK, c1, Complex.ofReal_mul, mul_comm]
  have hmain := sum_sq_apply_le hN'
    (toPauliCoeffs (restrictToPositiveEdges (X : Edge L n k j → ComplexMatrix2)))
  rw [hact, ← pairRe_self_eq_sum G hL hn hj.le X, ← pairRe_self_eq_sum G hL hn hj (Cm X)] at hmain
  have hCY : Cm X = (L : ℝ)⁻¹ • Y := Subtype.ext (by
    rw [hCm]
    show _ = (L : ℝ)⁻¹ • (Y : Edge L n k (j + 1) → ComplexMatrix2)
    rw [hY])
  rw [hCY, pairRe_smul_self G hL hn hj] at hmain
  have a0 := meshAt_pos hL k j
  have a1 := meshAt_pos hL k (j + 1)
  unfold levelGain
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have e : (pairRe Y Y) * meshAt L k (j + 1) ^ 4 = (L : ℝ) ^ 2 *
      (meshAt L k (j + 1) ^ 4 * ((L : ℝ)⁻¹ ^ 2 * pairRe Y Y)) := by
    field_simp
  rw [e, mul_assoc]
  exact mul_le_mul_of_nonneg_left hmain (by positivity)
end Step
section Straight
variable {L n k : ℕ}
private theorem linearChain_succ (ξ : LevelForms L n k) {j : ℕ} (hj : j < k) :
    linearChain ξ (j + 1) = crossingSmoothing L n k j (linearChain ξ j) +
      (ξ.2 ⟨j, hj⟩ : Edge L n k (j + 1) → ComplexMatrix2) := by
  rw [linearChain, dif_pos hj]
private theorem linearChain_mem (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (ξ : LevelForms L n k) : ∀ j, j ≤ k → linearChain ξ j ∈ edgeFormSpace L n k j := by
  intro j
  induction j with
  | zero => exact fun _ => ξ.1.2
  | succ j ih =>
    intro h
    have hj : j < k := h
    rw [linearChain_succ ξ hj]
    exact (edgeFormSpace L n k (j + 1)).add_mem (crossingSmoothing_mem G hL hn hj (ih hj.le))
      (ξ.2 ⟨j, hj⟩).2
private theorem linearChain_add (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (ξ ξ' : LevelForms L n k) : ∀ j, j ≤ k →
      linearChain (ξ + ξ') j = linearChain ξ j + linearChain ξ' j := by
  intro j
  induction j with
  | zero => exact fun _ => rfl
  | succ j ih =>
    intro h
    have hj : j < k := h
    rw [linearChain_succ _ hj, linearChain_succ _ hj, linearChain_succ _ hj, ih hj.le,
      crossingSmoothing_add (finite_vertex G hL hn hj.le)]
    simp only [Prod.snd_add, Pi.add_apply, Submodule.coe_add]
    abel
private theorem linearChain_smul (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (r : ℝ) (ξ : LevelForms L n k) : ∀ j, j ≤ k →
      linearChain (r • ξ) j = r • linearChain ξ j := by
  intro j
  induction j with
  | zero => exact fun _ => rfl
  | succ j ih =>
    intro h
    have hj : j < k := h
    rw [linearChain_succ _ hj, linearChain_succ _ hj, ih hj.le,
      crossingSmoothing_smul (finite_vertex G hL hn hj.le)]
    simp only [Prod.smul_snd, Pi.smul_apply, Submodule.coe_smul, smul_add]
private def chainGrowth (L k : ℕ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => 2 * levelGain L k j * chainGrowth L k j + 2
private theorem chainGrowth_nonneg (L k j : ℕ) : 0 ≤ chainGrowth L k j := by
  induction j with
  | zero => exact zero_le_one
  | succ j ih =>
    have := levelGain_nonneg L k j
    show 0 ≤ 2 * levelGain L k j * chainGrowth L k j + 2
    positivity
private theorem levelFormsNormSq_eq (ξ : LevelForms L n k) :
    levelFormsNormSq ξ = pairRe ξ.1 ξ.1 + ∑ i : Fin k, pairRe (ξ.2 i) (ξ.2 i) := rfl
private theorem pairRe_snd_le (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (ξ : LevelForms L n k) (i : Fin k) :
    pairRe (ξ.2 i) (ξ.2 i) ≤ levelFormsNormSq ξ := by
  rw [levelFormsNormSq_eq]
  have h0 := pairRe_self_nonneg G hL hn (Nat.zero_le k) ξ.1
  have h1 := Finset.single_le_sum (f := fun i : Fin k => pairRe (ξ.2 i) (ξ.2 i))
    (fun i _ => pairRe_self_nonneg G hL hn i.2 _) (Finset.mem_univ i)
  linarith
private theorem pairRe_fst_le (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (ξ : LevelForms L n k) : pairRe ξ.1 ξ.1 ≤ levelFormsNormSq ξ := by
  rw [levelFormsNormSq_eq]
  have h1 : 0 ≤ ∑ i : Fin k, pairRe (ξ.2 i) (ξ.2 i) :=
    Finset.sum_nonneg fun i _ => pairRe_self_nonneg G hL hn i.2 _
  linarith
private theorem linearChain_sq_le (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (ξ : LevelForms L n k) : ∀ j, j ≤ k → ∃ X : edgeFormSpace L n k j,
      (X : Edge L n k j → ComplexMatrix2) = linearChain ξ j ∧
        pairRe X X ≤ chainGrowth L k j * levelFormsNormSq ξ := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨ξ.1, rfl, ?_⟩
    rw [show chainGrowth L k 0 = 1 from rfl, one_mul]
    exact pairRe_fst_le G hL hn ξ
  | succ j ih =>
    intro h
    have hj : j < k := h
    obtain ⟨X, hX, hb⟩ := ih hj.le
    let Y : edgeFormSpace L n k (j + 1) :=
      ⟨crossingSmoothing L n k j X, crossingSmoothing_mem G hL hn hj X.2⟩
    refine ⟨Y + ξ.2 ⟨j, hj⟩, ?_, ?_⟩
    · rw [linearChain_succ ξ hj, ← hX]
      rfl
    · have h1 := pairRe_add_self_le G hL hn h Y (ξ.2 ⟨j, hj⟩)
      have h2 := crossingSmoothing_sq_le G hL hn hk hj X Y rfl
      have h3 := pairRe_snd_le G hL hn ξ ⟨j, hj⟩
      have h4 := mul_le_mul_of_nonneg_left hb (levelGain_nonneg L k j)
      show _ ≤ (2 * levelGain L k j * chainGrowth L k j + 2) * levelFormsNormSq ξ
      nlinarith
end Straight
section Transpose
variable {L n k : ℕ}
private theorem exists_representing_map {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] (p : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hp : ∀ x, p x x = 0 → x = 0)
    (φ : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) : ∃ T : F →ₗ[ℝ] E, ∀ f e, p (T f) e = φ f e := by apply _root_.YangMills.SharedProofs.p13845 <;> assumption
private theorem levelPairing_add_left (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (ξ ξ' η : LevelForms L n k) :
    levelPairing (formValues (ξ + ξ')) (formValues η) =
      levelPairing (formValues ξ) (formValues η) + levelPairing (formValues ξ') (formValues η) := by
  have e0 : (edgeFormPairing ((ξ + ξ').1 : Edge L n k 0 → ComplexMatrix2)
      (η.1 : Edge L n k 0 → ComplexMatrix2)).re =
      pairRe ξ.1 η.1 + pairRe ξ'.1 η.1 := pairRe_add_left G hL hn (Nat.zero_le k) ξ.1 ξ'.1 η.1
  have e1 : ∀ i : Fin k, (edgeFormPairing ((ξ + ξ').2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)
      (η.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)).re =
      pairRe (ξ.2 i) (η.2 i) + pairRe (ξ'.2 i) (η.2 i) := fun i =>
    pairRe_add_left G hL hn i.2 (ξ.2 i) (ξ'.2 i) (η.2 i)
  show (edgeFormPairing ((ξ + ξ').1 : Edge L n k 0 → ComplexMatrix2)
      (η.1 : Edge L n k 0 → ComplexMatrix2)).re +
      ∑ i : Fin k, (edgeFormPairing ((ξ + ξ').2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)
        (η.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)).re =
    (pairRe ξ.1 η.1 + ∑ i : Fin k, pairRe (ξ.2 i) (η.2 i)) +
      (pairRe ξ'.1 η.1 + ∑ i : Fin k, pairRe (ξ'.2 i) (η.2 i))
  rw [e0, Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib]
  ring
private theorem levelPairing_smul_left (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (r : ℝ) (ξ η : LevelForms L n k) :
    levelPairing (formValues (r • ξ)) (formValues η) =
      r * levelPairing (formValues ξ) (formValues η) := by
  have e0 : (edgeFormPairing ((r • ξ).1 : Edge L n k 0 → ComplexMatrix2)
      (η.1 : Edge L n k 0 → ComplexMatrix2)).re =
      r * pairRe ξ.1 η.1 := pairRe_smul_left G hL hn (Nat.zero_le k) r ξ.1 η.1
  have e1 : ∀ i : Fin k, (edgeFormPairing ((r • ξ).2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)
      (η.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)).re = r * pairRe (ξ.2 i) (η.2 i) :=
    fun i => pairRe_smul_left G hL hn i.2 r (ξ.2 i) (η.2 i)
  show (edgeFormPairing ((r • ξ).1 : Edge L n k 0 → ComplexMatrix2)
      (η.1 : Edge L n k 0 → ComplexMatrix2)).re +
      ∑ i : Fin k, (edgeFormPairing ((r • ξ).2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)
        (η.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)).re =
    r * (pairRe ξ.1 η.1 + ∑ i : Fin k, pairRe (ξ.2 i) (η.2 i))
  rw [e0, Finset.sum_congr rfl fun i _ => e1 i, ← Finset.mul_sum]
  ring
private theorem levelPairing_comm (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (ξ η : LevelForms L n k) :
    levelPairing (formValues ξ) (formValues η) = levelPairing (formValues η) (formValues ξ) := by
  show pairRe ξ.1 η.1 + ∑ i : Fin k, pairRe (ξ.2 i) (η.2 i) =
    pairRe η.1 ξ.1 + ∑ i : Fin k, pairRe (η.2 i) (ξ.2 i)
  rw [pairRe_comm G hL hn (Nat.zero_le k)]
  congr 1
  exact Finset.sum_congr rfl fun i _ => pairRe_comm G hL hn i.2 _ _
private def levelBilin (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    LevelForms L n k →ₗ[ℝ] LevelForms L n k →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun ξ η => levelPairing (formValues ξ) (formValues η))
    (levelPairing_add_left G hL hn)
    (fun r ξ η => by rw [levelPairing_smul_left G hL hn, smul_eq_mul])
    (fun ξ η η' => by
      rw [levelPairing_comm G hL hn, levelPairing_add_left G hL hn, levelPairing_comm G hL hn η,
        levelPairing_comm G hL hn η'])
    (fun r ξ η => by
      rw [levelPairing_comm G hL hn, levelPairing_smul_left G hL hn, levelPairing_comm G hL hn η,
        smul_eq_mul])
private theorem levelBilin_definite (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (ξ : LevelForms L n k) (h : levelBilin G hL hn ξ ξ = 0) : ξ = 0 := by
  have h' : pairRe ξ.1 ξ.1 + ∑ i : Fin k, pairRe (ξ.2 i) (ξ.2 i) = 0 := h
  have h0 := pairRe_self_nonneg G hL hn (Nat.zero_le k) ξ.1
  have hi := fun i : Fin k => pairRe_self_nonneg G hL hn i.2 (ξ.2 i)
  have hs : 0 ≤ ∑ i : Fin k, pairRe (ξ.2 i) (ξ.2 i) := Finset.sum_nonneg fun i _ => hi i
  have e0 : pairRe ξ.1 ξ.1 = 0 := by linarith
  have es : ∑ i : Fin k, pairRe (ξ.2 i) (ξ.2 i) = 0 := by linarith
  have ei := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hi i).mp es
  refine Prod.ext (eq_zero_of_pairRe_self G hL hn (Nat.zero_le k) e0) (funext fun i => ?_)
  exact eq_zero_of_pairRe_self G hL hn i.2 (ei i (Finset.mem_univ i))
private theorem finiteDimensional_edgeFormSpace (G : Inputs)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ}
    (hj : j ≤ k) : FiniteDimensional ℝ (edgeFormSpace L n k j) := by
  obtain ⟨ι, _, Ψ, -⟩ := exists_orthonormal_coords G hL hn hj
  exact Module.Finite.equiv Ψ.symm
private theorem linearConstraintAdjoint_spec (G : Inputs)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    IsLinearConstraintAdjoint (linearConstraintAdjoint L n k) := by
  have := finiteDimensional_edgeFormSpace G hL hn (Nat.zero_le k)
  have : ∀ i : Fin k, FiniteDimensional ℝ (edgeFormSpace L n k ((i : ℕ) + 1)) := fun i =>
    finiteDimensional_edgeFormSpace G hL hn i.2
  let S : LevelForms L n k →ₗ[ℝ] edgeFormSpace L n k k :=
    { toFun := fun ξ => ⟨linearChain ξ k, linearChain_mem G hL hn ξ k le_rfl⟩
      map_add' := fun ξ ξ' => Subtype.ext (linearChain_add G hL hn ξ ξ' k le_rfl)
      map_smul' := fun r ξ => Subtype.ext (linearChain_smul G hL hn r ξ k le_rfl) }
  let φ : edgeFormSpace L n k k →ₗ[ℝ] LevelForms L n k →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun μ ξ => pairRe μ (S ξ))
      (fun μ μ' ξ => pairRe_add_left G hL hn le_rfl _ _ _)
      (fun r μ ξ => by rw [pairRe_smul_left G hL hn le_rfl, smul_eq_mul])
      (fun μ ξ ξ' => by
        rw [map_add, pairRe_comm G hL hn le_rfl, pairRe_add_left G hL hn le_rfl,
          pairRe_comm G hL hn le_rfl (S ξ), pairRe_comm G hL hn le_rfl (S ξ')])
      (fun r μ ξ => by
        rw [map_smul, pairRe_comm G hL hn le_rfl, pairRe_smul_left G hL hn le_rfl,
          pairRe_comm G hL hn le_rfl (S ξ), smul_eq_mul])
  obtain ⟨T0, hT0⟩ := exists_representing_map (levelBilin G hL hn) (levelBilin_definite G hL hn) φ
  exact Classical.epsilon_spec (p := IsLinearConstraintAdjoint) ⟨T0, fun μ ξ => hT0 μ ξ⟩
end Transpose
theorem firstVariationMapsBounded_of (hP : Tower.FaceSums.FacesAndPairings)
    (hC : PauliCoordsOrthonormal)
    (hE : PeriodicOperators.ExponentialSums.Bounds) (hR : Tower.ResponseOperators.Claim)
    (hIm : Tower.ResponseImagesFullSide.ResponseImagesHold)
    (hI : PeriodicOperators.TowerIndexSets.Claim)
    (hY : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (hA : Tower.SmoothingContraction.Claim) (hV : Tower.LinearMapValues.Statement) :
    FirstVariationMapsBounded := by
  have G : Inputs := ⟨hP, hC, hE, hIm, hI, hY, hA, hV⟩
  intro L hL k hk
  obtain ⟨δ₀, -, hδ⟩ := hR
  have hAt := hδ L hL k hk
  obtain ⟨c₁, hc₁, h₁⟩ := kernel_sq_bound G hL le_rfl le_rfl hAt.defect_periodic
  obtain ⟨c₂, hc₂, h₂⟩ := kernel_sq_bound G hL le_rfl (Nat.zero_le k) hAt.resp_periodic
  have hg := chainGrowth_nonneg L k k
  obtain ⟨η, hη⟩ : ∃ η, η = finestMesh L k := ⟨_, rfl⟩
  refine ⟨chainGrowth L k k + c₁ + η ^ 2 * c₂, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  have himg := hIm L hL k hk n hn
  have hsq : ∀ B : edgeFormSpace L n k k, 0 ≤ pairRe B B := pairRe_self_nonneg G hL hn le_rfl
  refine ⟨linearConstraintAdjoint_spec G hL hn, fun ξ => ?_, fun B B' => ⟨?_, ?_⟩,
    fun B => ⟨?_, ?_⟩⟩
  · obtain ⟨X, hX, hb⟩ := linearChain_sq_le G hL hn hk ξ k le_rfl
    refine ⟨X, hX, hb.trans ?_⟩
    have hT : 0 ≤ levelFormsNormSq ξ := by
      rw [levelFormsNormSq_eq]
      exact add_nonneg (pairRe_self_nonneg G hL hn (Nat.zero_le k) _)
        (Finset.sum_nonneg fun i _ => pairRe_self_nonneg G hL hn i.2 _)
    refine mul_le_mul_of_nonneg_right ?_ hT
    have : 0 ≤ η ^ 2 * c₂ := by positivity
    linarith
  · exact map_sub_of_kernel G hL hn le_rfl le_rfl (F := periodicDefect L n k)
      (fun X => ⟨(himg X).defect_summable, (himg X).defect_coeffs⟩) B B'
  · have e := map_sub_of_kernel G hL hn le_rfl (Nat.zero_le k) (F := periodicResponse L n k)
      (fun X => ⟨(himg X).resp_summable, (himg X).resp_coeffs⟩) B B'
    show finestMesh L k • periodicResponse L n k _ =
      finestMesh L k • periodicResponse L n k _ - finestMesh L k • periodicResponse L n k _
    rw [e, smul_sub]
  · have h := h₁ n hn B (periodicDefect L n k B) (himg B).defect_coeffs
    refine le_trans h (mul_le_mul_of_nonneg_right ?_ (hsq B))
    have : 0 ≤ η ^ 2 * c₂ := by positivity
    linarith
  · have h := h₂ n hn B (periodicResponse L n k B) (himg B).resp_coeffs
    have e : levelFormsNormSq ((meshScaledResponse L n k B, 0) : LevelForms L n k) =
        η ^ 2 * pairRe (periodicResponse L n k B) (periodicResponse L n k B) := by
      rw [levelFormsNormSq_eq]
      have e1 : ∑ i : Fin k, pairRe (((meshScaledResponse L n k B, 0) : LevelForms L n k).2 i)
          (((meshScaledResponse L n k B, 0) : LevelForms L n k).2 i) = 0 :=
        Finset.sum_eq_zero fun i _ => pairRe_zero G hL hn i.2
      rw [e1, add_zero, hη]
      exact pairRe_smul_self G hL hn (Nat.zero_le k) _ _
    rw [e]
    have h3 : η ^ 2 * pairRe (periodicResponse L n k B) (periodicResponse L n k B) ≤
        η ^ 2 * (c₂ * pairRe B B) := mul_le_mul_of_nonneg_left h (by positivity)
    refine h3.trans ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (hsq B)
    have : 0 ≤ c₁ := hc₁
    linarith
end YangMills.Construction.RunningCouplingSlope.FirstVariationBounds
end

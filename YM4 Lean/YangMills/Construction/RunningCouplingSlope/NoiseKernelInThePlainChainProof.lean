import YangMills.Construction.RunningCouplingSlope.PlainCovariantStepOnTheForms
import YangMills.Construction.RunningCouplingSlope.TheSaddleOfTheWholeChainHasABoundedInverseAtOneProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace NoiseCovarianceChain
open Tower PeriodicOperators Matrices
private theorem pauliCoeff_smul_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (w : ℂ) (a : Fin 3) :
    pauliCoeff a (w • X + Y) = w * pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.pauliCoeff_smul_add <;> assumption
private theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
variable {L n k m : ℕ}
private theorem ofCoeffs_coeffs
    (hX : ∀ b : Edge L n k m, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {B : Edge L n k m → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k m) :
    (edgePauliCoordinates L n k m).ofCoeffs ((edgePauliCoordinates L n k m).coeffs B) = B := by apply _root_.YangMills.SharedProofs.p21342 <;> assumption
private theorem toPauliCoeffs_smul_add {A B : Edge L n k m → ComplexMatrix2}
    (hA : A ∈ complexEdgeForms L n k m) (hB : B ∈ complexEdgeForms L n k m) (w : ℂ)
    (t : Fin 3 × PositiveEdge L n k m) :
    toPauliCoeffs (restrictToPositiveEdges (w • A + B)) t =
      w * toPauliCoeffs (restrictToPositiveEdges A) t + toPauliCoeffs (restrictToPositiveEdges B) t :=
  pauliCoeff_smul_add (hA.1 _ t.2.2) (hB.1 _ t.2.2) w t.1
private theorem toPauliCoeffs_zero (t : Fin 3 × PositiveEdge L n k m) :
    toPauliCoeffs (restrictToPositiveEdges (0 : Edge L n k m → ComplexMatrix2)) t = 0 :=
  pauliCoeff_zero t.1
private theorem sum_comm_three {A B C : Type} [Fintype A] [Fintype B] [Fintype C] (F : A → B → C → ℂ) :
    ∑ c, ∑ b, ∑ a, F a b c = ∑ a, ∑ b, ∑ c, F a b c := by
  calc ∑ c, ∑ b, ∑ a, F a b c = ∑ b, ∑ c, ∑ a, F a b c := Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ c, F a b c := Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, F a b c := Finset.sum_comm
end NoiseCovarianceChain
open NoiseCovarianceChain Tower PeriodicOperators Matrices in
theorem noiseCovarianceAsPlainChainSum_holds (hO : ShiftedGaugeMapAtQuietPoint)
    (hK : MeanKernelsRepresent) (hS : MeanCovariantStepOnForms)
    (hP : MeanDerivOnForms.Claim) (hI : MeanIteratesTendToOne) :
    NoiseCovarianceAsPlainChainSum := by
  intro a ha L hL k n hk hn
  classical
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  haveI : NeZero L := ⟨by omega⟩
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hLC : ((L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hLpos.ne'
  have hX : ∀ i, i ≤ k → ∀ b : Edge L n k i,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun i hi b =>
    PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  have hfinB : ∀ i, Finite (Fin 3 × PositiveEdge L n k i) := fun i => by
    have : Finite (Edge L n k i) := PeriodicLattice.instFiniteBond _
    infer_instance
  let _ : ∀ i, Fintype (Fin 3 × PositiveEdge L n k i) := fun i =>
    have := hfinB i
    Fintype.ofFinite _
  have hev : ∀ᶠ U in 𝓝[fieldSpace L n k 0] (fun _ => (1 : ComplexMatrix2)), ∀ i ∈ Finset.range k,
      (∀ B ∈ complexEdgeForms L n k i, meanCovariantStep (meanIterate U i) B ∈
        complexEdgeForms L n k (i + 1)) ∧
      (∀ B ∈ complexEdgeForms L n k i, ∀ B' ∈ complexEdgeForms L n k i, ∀ w : ℂ,
        meanCovariantStep (meanIterate U i) (w • B + B') =
          w • meanCovariantStep (meanIterate U i) B + meanCovariantStep (meanIterate U i) B') ∧
      ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
        meanRadius (meanIterate U i) c = (((meanRadius (meanIterate U i) c).re : ℝ) : ℂ) := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hik : i < k := Finset.mem_range.1 hi
    have hT := hI L hL k n hn i hik.le
    filter_upwards [hT.eventually (hS L hL n k i hn hk hik), hT.eventually (hP L hL n k i hn hik)]
      with U f g
    exact ⟨f.1, f.2.1, fun c hc => (g.2.1 c hc).1⟩
  have e₁ := hO L hL k n hk hn
  have e₂ := hK L hL k n hk hn
  unfold EventuallyNearIdentity at e₁ e₂ ⊢
  filter_upwards [e₁, e₂, hev] with U fO fK fU E hE0 hE1 hE2
  have hmem : ∀ κ i, i ≤ k → tangentForms U (E κ) i ∈ edgeFormSpace L n k i :=
    fun κ i hi => (fO (E κ)).1 i hi
  have hcm : ∀ {i : ℕ} {B : Edge L n k i → ComplexMatrix2}, B ∈ edgeFormSpace L n k i →
      B ∈ complexEdgeForms L n k i :=
    fun hB => ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
  have hstep0 : ∀ i, i < k → meanCovariantStep (meanIterate U i) 0 = 0 := by
    intro i hi
    have h := (fU i (Finset.mem_range.2 hi)).2.1 0 (complexEdgeForms L n k i).zero_mem 0
      (complexEdgeForms L n k i).zero_mem 1
    simp only [one_smul, add_zero] at h
    exact left_eq_add.1 h
  have hZ : ∀ (κ : Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) (i : ℕ), i ≤ κ.1 →
      tangentForms U (E κ) i = 0 := by
    intro κ i
    induction i with
    | zero =>
      intro _
      change (((E κ).1 : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) = 0
      rw [hE0 κ]
      rfl
    | succ i ih =>
      intro hi
      have hik : i < k := lt_of_lt_of_le (Nat.lt_of_succ_le hi) κ.1.2.le
      change meanCovariantStep (meanIterate U i) (tangentForms U (E κ) i) +
        (if h : i < k then _ else _) = 0
      rw [ih (by omega), hstep0 i hik, dif_pos hik, hE1 κ ⟨i, hik⟩ (fun h => by
        have : i = κ.1 := congrArg Fin.val h
        omega)]
      simp
  intro i
  induction i with
  | zero =>
    intro _ t t'
    have : ∀ κ, toPauliCoeffs (restrictToPositiveEdges (tangentForms U (E κ) 0)) t = 0 := by
      intro κ
      rw [hZ κ 0 (Nat.zero_le _)]
      exact toPauliCoeffs_zero t
    simp only [this, zero_mul, finsum_zero]
    rfl
  | succ m ih =>
    intro hm t t'
    have hlt : m < k := by omega
    have IH := ih hlt.le
    set V := meanIterate U m with hV
    set S := meanStepKernel L n k U m with hSdef
    set w : (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℂ := fun κ =>
      (((a * (meanRadius (meanIterate U κ.1) κ.2.2.1).re)⁻¹ : ℝ) : ℂ) with hw
    have hstep : ∀ B ∈ edgeFormSpace L n k m, ∀ t,
        toPauliCoeffs (restrictToPositiveEdges (meanCovariantStep V B)) t =
          ((L : ℝ) : ℂ) * ∑ s, S t s * toPauliCoeffs (restrictToPositiveEdges B) s := by
      intro B hB t
      have g := congrFun ((fK.1 m hlt) (toPauliCoeffs (restrictToPositiveEdges B))).2 t
      change applyKernel S (toPauliCoeffs (restrictToPositiveEdges B)) t =
        toPauliCoeffs (restrictToPositiveEdges
        ((L : ℝ)⁻¹ • meanCovariantStep V ((edgePauliCoordinates L n k m).ofCoeffs
          ((edgePauliCoordinates L n k m).coeffs B)))) t at g
      rw [ofCoeffs_coeffs (hX m hlt.le) (hcm hB)] at g
      have hm' := (fU m (Finset.mem_range.2 hlt)).1 B (hcm hB)
      have e : (L : ℝ)⁻¹ • meanCovariantStep V B =
          (((L : ℝ)⁻¹ : ℝ) : ℂ) • meanCovariantStep V B + 0 := by
        rw [add_zero]
        funext b
        exact (Complex.coe_smul _ _).symm
      rw [e, toPauliCoeffs_smul_add hm' (complexEdgeForms L n k (m + 1)).zero_mem,
        toPauliCoeffs_zero, add_zero] at g
      simp only [applyKernel, tsum_fintype] at g
      rw [g, ← mul_assoc, Complex.ofReal_inv, mul_inv_cancel₀ hLC, one_mul]
    set m0 : Fin k := ⟨m, hlt⟩ with hm0
    let c : (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → Fin 3 × PositiveEdge L n k m → ℂ :=
      fun κ s => toPauliCoeffs (restrictToPositiveEdges (tangentForms U (E κ) m)) s
    let e : (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) →
        Fin 3 × PositiveEdge L n k (m + 1) → ℂ := fun κ t =>
      toPauliCoeffs (restrictToPositiveEdges (((E κ).2 m0 : edgeFormSpace L n k (m + 1)) :
        Edge L n k (m + 1) → ComplexMatrix2)) t
    let Pq : (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) →
        Fin 3 × PositiveEdge L n k (m + 1) → ℂ := fun κ t =>
      ((L : ℝ) : ℂ) * ∑ s, S t s * c κ s
    have hco : ∀ κ t, toPauliCoeffs (restrictToPositiveEdges (tangentForms U (E κ) (m + 1))) t =
        Pq κ t + e κ t := by
      intro κ t
      have e1 : tangentForms U (E κ) (m + 1) =
          (1 : ℂ) • meanCovariantStep V (tangentForms U (E κ) m) +
            (((E κ).2 m0 : edgeFormSpace L n k (m + 1)) : Edge L n k (m + 1) → ComplexMatrix2) := by
        change meanCovariantStep V (tangentForms U (E κ) m) + (if h : m < k then _ else _) = _
        rw [dif_pos hlt, one_smul]
      rw [e1, toPauliCoeffs_smul_add ((fU m (Finset.mem_range.2 hlt)).1 _ (hcm (hmem κ m hlt.le)))
        (hcm ((E κ).2 m0).2) 1 t, one_mul, hstep _ (hmem κ m hlt.le) t]
    have hPe : ∀ κ t t', Pq κ t * e κ t' = 0 := by
      intro κ t t'
      by_cases hκ : κ.1 = m0
      · have h0 : tangentForms U (E κ) m = 0 := hZ κ m (by rw [hκ])
        have : Pq κ t = 0 := by
          simp only [Pq, c, h0, toPauliCoeffs_zero, mul_zero, Finset.sum_const_zero]
        rw [this, zero_mul]
      · have h0 := hE1 κ m0 (fun h => hκ h.symm)
        have : e κ t' = 0 := by
          simp only [e, h0]
          exact toPauliCoeffs_zero t'
        rw [this, mul_zero]
    have he : ∀ κ t, e κ t = if κ = (⟨m0, t⟩ : Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1))
        then 1 else 0 := by
      rintro ⟨i, ι⟩ t
      by_cases h : i = m0
      · subst h
        have h2 := hE2 ⟨m0, ι⟩ t
        change e ⟨m0, ι⟩ t = _ at h2
        rw [h2]
        by_cases h3 : t = ι
        · subst h3
          simp
        · have h4 : (⟨m0, ι⟩ : Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) ≠ ⟨m0, t⟩ := by
            intro h5
            exact h3 (eq_of_heq (Sigma.mk.inj h5).2).symm
          rw [if_neg h3, if_neg h4]
      · have h0 := hE1 ⟨i, ι⟩ m0 (fun h' => h h'.symm)
        have h4 : (⟨i, ι⟩ : Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) ≠ ⟨m0, t⟩ := by
          intro h5
          exact h (Sigma.mk.inj h5).1
        rw [if_neg h4]
        simp only [e, h0]
        exact toPauliCoeffs_zero t
    rw [finsum_eq_sum_of_fintype]
    simp only [hco]
    have hterm : ∀ κ, (Pq κ t + e κ t) * (Pq κ t' + e κ t') * w κ =
        Pq κ t * Pq κ t' * w κ + e κ t * e κ t' * w κ := by
      intro κ
      linear_combination (w κ) * hPe κ t t' + (w κ) * hPe κ t' t
    change _ = ∑ κ, (Pq κ t + e κ t) * (Pq κ t' + e κ t') * w κ
    simp only [hterm, Finset.sum_add_distrib]
    have hsecond : ∑ κ, e κ t * e κ t' * w κ =
        if t = t' then w ⟨m0, t⟩ else 0 := by
      rw [Finset.sum_eq_single (⟨m0, t⟩ : Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1))]
      · rw [he, he, if_pos rfl, one_mul]
        by_cases h3 : t = t'
        · subst h3
          simp
        · have h4 : (⟨m0, t⟩ : Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) ≠ ⟨m0, t'⟩ := by
            intro h5
            exact h3 (eq_of_heq (Sigma.mk.inj h5).2)
          rw [if_neg h4, if_neg h3, zero_mul]
      · intro κ _ hκ
        rw [he κ t, if_neg hκ, zero_mul, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hfirst : (((L : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ) * compKernel (compKernel S
        (noiseCovariance a L n k U m)) (meshTranspose (meshAt L k m) (meshAt L k (m + 1)) S)
        t t' = ∑ κ, Pq κ t * Pq κ t' * w κ := by
      have hratio : (((L : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ) *
          (((meshAt L k (m + 1) ^ 4 / meshAt L k m ^ 4 : ℝ)) : ℂ) =
          ((L : ℝ) : ℂ) ^ 2 := by
        have h1 : meshAt L k (m + 1) = L * meshAt L k m := by
          simp only [meshAt]
          rw [show (((m + 1 : ℕ) : ℤ) - (k : ℤ)) = ((m : ℤ) - (k : ℤ)) + 1 by push_cast; ring,
            zpow_add_one₀ hLpos.ne', mul_comm]
        have h2 : meshAt L k m ≠ 0 := (zpow_pos hLpos _).ne'
        rw [h1, mul_pow, mul_div_assoc, div_self (pow_ne_zero 4 h2), mul_one, zpow_neg]
        push_cast
        field_simp
      have hW : ∀ s' t'', meshTranspose (meshAt L k m) (meshAt L k (m + 1)) S s' t'' =
          (((meshAt L k (m + 1) ^ 4 / meshAt L k m ^ 4 : ℝ)) : ℂ) * S t'' s' :=
        fun _ _ => rfl
      have hG : ∀ s s', noiseCovariance a L n k U m s s' = ∑ κ, c κ s * c κ s' * w κ := by
        intro s s'
        rw [IH s s', finsum_eq_sum_of_fintype]
      simp only [compKernel, tsum_fintype, hW, hG]
      have expand : ∀ κ, Pq κ t * Pq κ t' * w κ = ∑ s, ∑ s',
          (((L : ℝ) : ℂ) ^ 2) * (S t s * (c κ s * c κ s' * w κ)) * S t' s' := by
        intro κ
        simp only [Pq]
        rw [mul_mul_mul_comm, Finset.sum_mul_sum, ← sq, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun s' _ => ?_
        ring
      simp only [expand]
      rw [← sum_comm_three
          (fun κ s s' => (((L : ℝ) : ℂ) ^ 2) * (S t s * (c κ s * c κ s' * w κ)) * S t' s'),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [← hratio]
      ring
    rw [hsecond, ← hfirst]
    have hnk : noiseCovariance a L n k U (m + 1) t t' =
        ((a⁻¹ : ℝ) : ℂ) * invRadiusDiag U m t t' +
        (((L : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ) * compKernel (compKernel S (noiseCovariance a L n k U m))
          (meshTranspose (meshAt L k m) (meshAt L k (m + 1)) S) t t' := rfl
    rw [hnk, add_comm]
    congr 1
    by_cases h3 : t = t'
    · subst h3
      have hr := (fU m (Finset.mem_range.2 hlt)).2.2 t.2.1 t.2.2
      have hwt : w ⟨m0, t⟩ = (((a * (meanRadius (meanIterate U m) t.2.1).re)⁻¹ : ℝ) : ℂ) := rfl
      simp only [invRadiusDiag, if_true, hwt]
      set r := (meanRadius (meanIterate U m) t.2.1).re
      rw [hr]
      push_cast
      rw [mul_inv]
    · simp only [invRadiusDiag, if_neg h3, mul_zero]
end YangMills.Construction.RunningCouplingSlope
end

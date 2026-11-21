import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Towers.EntriesAlongAFieldAsSumsOverBonds
import YangMills.Construction.Towers.VariationsOfALocalFamily
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.OneLoopNotation
open YangMills.Construction.Tower.LocalFamilies
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
namespace EdgeSums
variable {J B : Type}
theorem euclidNormVec_add_le (v w : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (v + w) ≤
      TorusMetric.euclidNormVec v + TorusMetric.euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_nonneg <;> assumption
theorem exists_finset_near_point {src : B → InfiniteLattice.AmbientSpace} {k : ℕ}
    (hp : IsIntegerPlacement src k) (n : Fin 4 → ℤ) :
    ∃ F : Finset B, (∀ b, b ∈ F ↔
        TorusMetric.euclidNormVec (src b - PeriodicOperators.castVec n) ≤ 2) ∧
      F.card ≤ 5 ^ 4 * k := by
  classical
  let f : (Fin 4 → ℤ) → Finset B := fun j => (hp.fibre_bounded (PeriodicOperators.castVec j)).1.toFinset
  let big : Finset B := (Finset.Icc (n - 2) (n + 2)).biUnion f
  have hcard : big.card ≤ 5 ^ 4 * k := by
    have h1 : big.card ≤ (Finset.Icc (n - 2) (n + 2)).card * k := by
      refine Finset.card_biUnion_le_card_mul _ _ _ fun j _ => ?_
      have := (hp.fibre_bounded (PeriodicOperators.castVec j)).2
      rwa [Set.ncard_eq_toFinset_card _ (hp.fibre_bounded (PeriodicOperators.castVec j)).1] at this
    have h2 : (Finset.Icc (n - 2) (n + 2)).card = 5 ^ 4 := by
      rw [Pi.card_Icc]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.ofNat_apply, Int.card_Icc]
      have : ∀ i : Fin 4, (n i + 2 + 1 - (n i - 2)).toNat = 5 := fun i => by omega
      simp [this]
    rwa [h2] at h1
  have hmem : ∀ b, TorusMetric.euclidNormVec (src b - PeriodicOperators.castVec n) ≤ 2 →
      b ∈ big := by
    intro b hb
    obtain ⟨j, hj⟩ := hp.on_lattice b
    refine Finset.mem_biUnion.2 ⟨j, ?_, ?_⟩
    · have hcoord : ∀ μ, |(j μ : ℝ) - n μ| ≤ 2 := by
        intro μ
        have hb' : Real.sqrt (∑ ν, (src b - PeriodicOperators.castVec n) ν ^ 2) ≤ 2 := hb
        have h1 : ((j μ : ℝ) - n μ) ^ 2 ≤
            ∑ ν, (src b - PeriodicOperators.castVec n) ν ^ 2 := by
          have := Finset.single_le_sum
            (f := fun ν => (src b - PeriodicOperators.castVec n) ν ^ 2)
            (fun ν _ => sq_nonneg _) (Finset.mem_univ μ)
          simpa [hj, PeriodicOperators.castVec] using this
        exact (Real.abs_le_sqrt h1).trans hb'
      rw [Finset.mem_Icc]
      constructor
      · intro μ
        have := (abs_le.1 (hcoord μ)).1
        have h' : -2 ≤ j μ - n μ := by exact_mod_cast this
        simp only [Pi.sub_apply, Pi.ofNat_apply]
        omega
      · intro μ
        have := (abs_le.1 (hcoord μ)).2
        have h' : j μ - n μ ≤ 2 := by exact_mod_cast this
        simp only [Pi.add_apply, Pi.ofNat_apply]
        omega
    · simp [f, hj]
  refine ⟨big.filter fun b =>
    TorusMetric.euclidNormVec (src b - PeriodicOperators.castVec n) ≤ 2, fun b => ?_,
    (Finset.card_filter_le _ _).trans hcard⟩
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hmem b h, h⟩⟩
theorem summable_norm_and_tsum_le_of_finset {N : Type} (X : N → ℂ) (s : Finset N) (M K : ℝ)
    (hK : 0 ≤ K) (hs : (s.card : ℝ) ≤ M) (h0 : ∀ n, n ∉ s → X n = 0)
    (hb : ∀ n ∈ s, ‖X n‖ ≤ K) :
    Summable (fun n => ‖X n‖) ∧ ∑' n, ‖X n‖ ≤ M * K := by
  have hz : ∀ n, n ∉ s → ‖X n‖ = 0 := fun n hn => by simp [h0 n hn]
  refine ⟨summable_of_ne_finset_zero hz, ?_⟩
  rw [tsum_eq_sum hz]
  calc ∑ n ∈ s, ‖X n‖ ≤ ∑ _n ∈ s, K := Finset.sum_le_sum hb
    _ = s.card * K := by simp
    _ ≤ M * K := by gcongr
theorem matrixEntry_add (S S' : BddOp (IndexL2 J)) (a c : J) :
    matrixEntry (S + S') a c = matrixEntry S a c + matrixEntry S' a c := by
  simp [matrixEntry]
def matrixEntryCLM (hE : MatrixEntryProperties J) (a c : J) :
    BddOp (IndexL2 J) →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun S => matrixEntry S a c
      map_add' := fun S S' => matrixEntry_add S S' a c
      map_smul' := fun r S => by simp [matrixEntry] }
    1 (fun S => by simpa using ((hE S).1 a c).2)
section Derivatives
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem clm_deriv_comm {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : X →L[ℝ] Y)
    {g : ℝ → X} {x : ℝ} (hg : DifferentiableAt ℝ g x) :
    L (deriv g x) = deriv (fun y => L (g y)) x :=
  ((L.hasFDerivAt).comp_hasDerivAt x hg.hasDerivAt).deriv.symm
theorem hasDerivAt_comp_line {Q : X → ℂ} (hQ : Differentiable ℝ Q) (w u : X) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Q (w + t • u)) (fderiv ℝ Q (w + x • u) u) x := by
  have hline : HasDerivAt (fun t : ℝ => w + t • u) u x := by
    simpa using ((hasDerivAt_id x).smul_const u).const_add w
  exact (hQ (w + x • u)).hasFDerivAt.comp_hasDerivAt x hline
theorem deriv_comp_smul_zero {Q : X → ℂ} (hQ : Differentiable ℝ Q) (v : X) :
    deriv (fun r : ℝ => Q (r • v)) 0 = fderiv ℝ Q 0 v := by
  have h := (hasDerivAt_comp_line hQ 0 v 0).deriv
  simpa using h
theorem deriv_fderiv_smul_zero {Q : X → ℂ} (hQ : ContDiff ℝ 2 Q) (u v : X) :
    deriv (fun s : ℝ => fderiv ℝ Q (s • u) v) 0 = fderiv ℝ (fderiv ℝ Q) 0 u v := by
  have hD : Differentiable ℝ (fderiv ℝ Q) :=
    (hQ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hline : HasDerivAt (fun s : ℝ => s • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have hz : (0 : ℝ) • u = 0 := by simp
  have h2 := (hD ((0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
  rw [hz] at h2
  have h3 := ((ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt).comp_hasDerivAt (0 : ℝ) h2
  exact h3.deriv
theorem deriv_deriv_comp_smul_zero {Q : X → ℂ} (hQ : ContDiff ℝ 2 Q) (v : X) :
    deriv (deriv (fun r : ℝ => Q (r • v))) 0 = fderiv ℝ (fderiv ℝ Q) 0 v v := by
  have hQd : Differentiable ℝ Q := hQ.differentiable (by norm_num)
  have h1 : deriv (fun r : ℝ => Q (r • v)) = fun r : ℝ => fderiv ℝ Q (r • v) v := by
    funext r
    have h := (hasDerivAt_comp_line hQd 0 v r).deriv
    simpa using h
  rw [h1]
  exact deriv_fderiv_smul_zero hQ v v
theorem deriv_deriv_comp_add_smul_zero {Q : X → ℂ} (hQ : ContDiff ℝ 2 Q) (u v : X) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => Q (s • u + t • v)) 0) 0 =
      fderiv ℝ (fderiv ℝ Q) 0 u v := by
  have hQd : Differentiable ℝ Q := hQ.differentiable (by norm_num)
  have h1 : (fun s : ℝ => deriv (fun t : ℝ => Q (s • u + t • v)) 0) =
      fun s : ℝ => fderiv ℝ Q (s • u) v := by
    funext s
    have h := (hasDerivAt_comp_line hQd (s • u) v 0).deriv
    simpa using h
  rw [h1]
  exact deriv_fderiv_smul_zero hQ u v
theorem clm_deriv_deriv_comm {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y) {G : ℝ × ℝ → X} (hG : ContDiff ℝ 2 G) :
    L (deriv (fun s : ℝ => deriv (fun t : ℝ => G (s, t)) 0) 0) =
      deriv (fun s : ℝ => deriv (fun t : ℝ => L (G (s, t))) 0) 0 := by
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hcurve : ∀ s : ℝ, HasDerivAt (fun t : ℝ => (s, t)) ((0 : ℝ), (1 : ℝ)) 0 := fun s =>
    (hasDerivAt_const (0 : ℝ) s).prodMk (hasDerivAt_id (0 : ℝ))
  have hin : ∀ s : ℝ, deriv (fun t : ℝ => G (s, t)) 0 = fderiv ℝ G (s, 0) (0, 1) := fun s =>
    ((hGd (s, 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hcurve s)).deriv
  have hdiff : ∀ s : ℝ, DifferentiableAt ℝ (fun t : ℝ => G (s, t)) 0 := fun s =>
    ((hGd (s, 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hcurve s)).differentiableAt
  have hD : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hout : DifferentiableAt ℝ (fun s : ℝ => deriv (fun t : ℝ => G (s, t)) 0) 0 := by
    have h1 : (fun s : ℝ => deriv (fun t : ℝ => G (s, t)) 0) =
        fun s : ℝ => fderiv ℝ G (s, 0) (0, 1) := funext hin
    rw [h1]
    have h2 : Differentiable ℝ (fun s : ℝ => fderiv ℝ G (s, 0)) :=
      hD.comp (differentiable_id.prodMk (differentiable_const 0))
    exact (h2 0).clm_apply (differentiableAt_const _)
  rw [clm_deriv_comm L hout]
  congr 1
  funext s
  exact clm_deriv_comm L (hdiff s)
end Derivatives
def restrictIndicator (E : Finset B) (b : B) : E → ℝ := fun e => bondIndicator b e.1
theorem restrictIndicator_of_not_mem {E : Finset B} {b : B} (h : b ∉ E) :
    restrictIndicator E b = 0 := by
  funext e
  have : e.1 ≠ b := fun he => h (he ▸ e.2)
  simp [restrictIndicator, bondIndicator, this]
theorem restrict_eq_sum_smul_restrictIndicator (E : Finset B) (ξ : B → ℝ) :
    (fun e : E => ξ e.1) = ∑ b ∈ E, ξ b • restrictIndicator E b := by
  classical
  funext e
  rw [Finset.sum_apply, Finset.sum_eq_single_of_mem e.1 e.2]
  · simp [restrictIndicator, bondIndicator]
  · intro b _ hb
    have : e.1 ≠ b := fun h => hb h.symm
    simp [restrictIndicator, bondIndicator, this]
theorem matrixEntry_variations_eq_fderiv {T : (B → ℝ) → BddOp (IndexL2 J)}
    (hE : MatrixEntryProperties J)
    (hV : ∀ b b' : B, ContDiff ℝ 2 (fun p : ℝ × ℝ => T (twoBondField b b' p.1 p.2)))
    {a c : J} {E : Finset B} {Q : (E → ℝ) → ℂ} (hQ : ContDiff ℝ 3 Q)
    (hval : ∀ θ, matrixEntry (T θ) a c = Q fun b => θ b.1) (b b' : B) :
    matrixEntry (firstVar T b) a c = fderiv ℝ Q 0 (restrictIndicator E b) ∧
      matrixEntry (secondVar T b b') a c =
        fderiv ℝ (fderiv ℝ Q) 0 (restrictIndicator E b) (restrictIndicator E b') := by
  set G : ℝ × ℝ → BddOp (IndexL2 J) := fun p => T (twoBondField b b' p.1 p.2) with hGdef
  have hG : ContDiff ℝ 2 G := hV b b'
  have hGval : ∀ p : ℝ × ℝ, matrixEntry (G p) a c =
      Q (p.1 • restrictIndicator E b + p.2 • restrictIndicator E b') := by
    intro p
    rw [hGdef]
    simp only
    rw [hval]
    congr 1
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hlineDiff : DifferentiableAt ℝ (fun s : ℝ => G (s, 0)) 0 :=
    ((hGd _).comp (0 : ℝ) (differentiableAt_id.prodMk (differentiableAt_const 0)))
  have hfirstG : firstVar T b = deriv (fun s : ℝ => G (s, 0)) 0 := by
    unfold firstVar
    congr 1
    funext s
    simp only [hGdef]
    congr 1
    funext x
    simp [twoBondField]
  have hsecondG : secondVar T b b' =
      deriv (fun s : ℝ => deriv (fun t : ℝ => G (s, t)) 0) 0 := rfl
  constructor
  · have h1 : matrixEntry (firstVar T b) a c =
        deriv (fun s : ℝ => matrixEntry (G (s, 0)) a c) 0 := by
      rw [hfirstG]
      exact clm_deriv_comm (matrixEntryCLM hE a c) hlineDiff
    have h2 : (fun s : ℝ => matrixEntry (G (s, 0)) a c) =
        fun s : ℝ => Q (s • restrictIndicator E b) := by
      funext s
      rw [hGval]
      simp
    rw [h1, h2]
    exact deriv_comp_smul_zero (hQ.differentiable (by norm_num)) _
  · have h1 : matrixEntry (secondVar T b b') a c =
        deriv (fun s : ℝ => deriv (fun t : ℝ => matrixEntry (G (s, t)) a c) 0) 0 := by
      rw [hsecondG]
      exact clm_deriv_deriv_comm (matrixEntryCLM hE a c) hG
    have h2 : (fun s : ℝ => deriv (fun t : ℝ => matrixEntry (G (s, t)) a c) 0) =
        fun s : ℝ => deriv (fun t : ℝ =>
          Q (s • restrictIndicator E b + t • restrictIndicator E b')) 0 := by
      funext s
      congr 1
      funext t
      exact hGval (s, t)
    rw [h1, h2]
    exact deriv_deriv_comp_add_smul_zero (hQ.of_le (by norm_num)) _ _
theorem first_sum_bound {N C u : ℝ} (hN : 0 ≤ N) (hC : 0 ≤ C) (hu : 1 ≤ u) :
    N * (4 * u * C) ≤ (16 * N ^ 2 * C + 4 * N * C) * u ^ 3 := by
  have h1 : u ≤ u ^ 3 := le_self_pow₀ hu (by norm_num)
  have hP : 0 ≤ N * C := mul_nonneg hN hC
  have a := mul_le_mul_of_nonneg_left h1 hP
  have b : 0 ≤ N ^ 2 * C * u ^ 3 := by positivity
  nlinarith [a, b]
theorem second_sum_bound {N C u : ℝ} (hN : 0 ≤ N) (hC : 0 ≤ C) (hu : 1 ≤ u) :
    N ^ 2 * ((4 * u) ^ 2 * C) ≤ (16 * N ^ 2 * C + 4 * N * C) * u ^ 3 := by
  have h1 : u ^ 2 ≤ u ^ 3 := pow_le_pow_right₀ hu (by norm_num)
  have hP : 0 ≤ N ^ 2 * C := by positivity
  have a := mul_le_mul_of_nonneg_left h1 hP
  have b : 0 ≤ N * C * u ^ 3 := by positivity
  nlinarith [a, b]
end EdgeSums
open EdgeSums in
theorem FieldVariationsAsEdgeSums.of_localFamilyVariations (hV : LocalFamilyVariations) :
    FieldVariationsAsEdgeSums := by
  classical
  intro C k hC
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = 5 ^ 4 * (k : ℝ) := ⟨_, rfl⟩
  have hN : 0 ≤ N := by rw [hNdef]; positivity
  refine ⟨16 * N ^ 2 * C + 4 * N * C, by positivity, ?_⟩
  intro J B pos src m z T hz hT ξ hξ
  have hvar := hV J B pos src m k z C T hz hC hT
  have hE := hT.space.entryFacts
  have hnear : ∀ a : J, ∃ F : Finset B,
      (∀ b, b ∈ F ↔ TorusMetric.euclidNormVec (src b - pos a) ≤ 2) ∧
        (F.card : ℝ) ≤ N := by
    intro a
    obtain ⟨n, hn⟩ := hT.space.placement.on_lattice a
    obtain ⟨F, hF, hc⟩ := exists_finset_near_point hT.edges n
    refine ⟨F, fun b => by rw [hn]; exact hF b, ?_⟩
    rw [hNdef]
    exact_mod_cast hc
  have hu : ∀ a : J, 1 ≤ 1 + TorusMetric.euclidNormVec (pos a) := fun a => by
    have := euclidNormVec_nonneg (pos a)
    linarith
  have hξnear : ∀ (a : J) (b : B), TorusMetric.euclidNormVec (src b - pos a) ≤ 2 →
      ‖(ξ b : ℂ)‖ ≤ 4 * (1 + TorusMetric.euclidNormVec (pos a)) := by
    intro a b hb
    have h1 : TorusMetric.euclidNormVec (src b) ≤
        TorusMetric.euclidNormVec (src b - pos a) + TorusMetric.euclidNormVec (pos a) := by
      have := euclidNormVec_add_le (src b - pos a) (pos a)
      rwa [sub_add_cancel] at this
    have h2 := hξ b
    have h3 := euclidNormVec_nonneg (pos a)
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith
  refine ⟨⟨fun b a c hr => ?_, fun a c => ?_⟩, ⟨fun p a c hr => ?_, fun a c => ?_⟩,
    fun a c => ?_, fun a c => ?_⟩
  · show (ξ b : ℂ) * matrixEntry (firstVar T b) a c = 0
    rw [((hvar b b).2.2.1 a c hr).1, mul_zero]
  · obtain ⟨F, hF, hc⟩ := hnear a
    have hK : 0 ≤ 4 * (1 + TorusMetric.euclidNormVec (pos a)) * C := by
      have := hu a
      positivity
    obtain ⟨hs, hb⟩ := summable_norm_and_tsum_le_of_finset
      (fun b => (ξ b : ℂ) * matrixEntry (firstVar T b) a c) F N _ hK hc
      (fun b hbF => by
        have : ¬ TorusMetric.euclidNormVec (src b - pos a) ≤ 2 :=
          fun h => hbF ((hF b).2 h)
        rw [((hvar b b).2.2.2.1 a c this).1, mul_zero])
      (fun b hbF => by
        rw [norm_mul]
        exact mul_le_mul (hξnear a b ((hF b).1 hbF)) ((hvar b b).2.1 a c).1 (norm_nonneg _)
          (by have := hu a; positivity))
    exact ⟨hs, hb.trans (first_sum_bound hN hC.le (hu a))⟩
  · show (ξ p.1 : ℂ) * (ξ p.2 : ℂ) * matrixEntry (secondVar T p.1 p.2) a c = 0
    rw [((hvar p.1 p.2).2.2.1 a c hr).2, mul_zero]
  · obtain ⟨F, hF, hc⟩ := hnear a
    have hK : 0 ≤ (4 * (1 + TorusMetric.euclidNormVec (pos a))) ^ 2 * C := by positivity
    have hc2 : ((F ×ˢ F).card : ℝ) ≤ N ^ 2 := by
      rw [Finset.card_product, Nat.cast_mul, sq]
      exact mul_le_mul hc hc (Nat.cast_nonneg _) hN
    obtain ⟨hs, hb⟩ := summable_norm_and_tsum_le_of_finset
      (fun p : B × B => (ξ p.1 : ℂ) * (ξ p.2 : ℂ) * matrixEntry (secondVar T p.1 p.2) a c)
      (F ×ˢ F) (N ^ 2) _ hK hc2
      (fun p hp => by
        by_cases h1 : p.1 ∈ F
        · have h2 : p.2 ∉ F := fun h2 => hp (Finset.mem_product.2 ⟨h1, h2⟩)
          have : ¬ TorusMetric.euclidNormVec (src p.2 - pos a) ≤ 2 :=
            fun h => h2 ((hF _).2 h)
          rw [(hvar p.1 p.2).2.2.2.2.1 a c this, mul_zero]
        · have : ¬ TorusMetric.euclidNormVec (src p.1 - pos a) ≤ 2 :=
            fun h => h1 ((hF _).2 h)
          rw [((hvar p.1 p.2).2.2.2.1 a c this).2, mul_zero])
      (fun p hp => by
        obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
        have hu0 : 0 ≤ 4 * (1 + TorusMetric.euclidNormVec (pos a)) := by
          have := hu a
          positivity
        rw [norm_mul, norm_mul, sq]
        exact mul_le_mul
          (mul_le_mul (hξnear a _ ((hF _).1 h1)) (hξnear a _ ((hF _).1 h2)) (norm_nonneg _) hu0)
          ((hvar p.1 p.2).2.1 a c).2 (norm_nonneg _) (mul_nonneg hu0 hu0))
    exact ⟨hs, hb.trans (second_sum_bound hN hC.le (hu a))⟩
  · obtain ⟨E, Q, -, hQ, -, hval⟩ := hT.family.entry_smooth a c
    have hent := matrixEntry_variations_eq_fderiv hE (fun b b' => (hvar b b').1) hQ hval
    have hfe : entryAlong T ξ a c = fun r : ℝ => Q (r • fun e : E => ξ e.1) := by
      funext r
      simp only [entryAlong]
      rw [hval]
      rfl
    have hzero : ∀ b, b ∉ E → (ξ b : ℂ) * matrixEntry (firstVar T b) a c = 0 := by
      intro b hb
      rw [(hent b b).1, restrictIndicator_of_not_mem hb, map_zero, mul_zero]
    rw [tsum_eq_sum hzero]
    show deriv (entryAlong T ξ a c) 0 = _
    rw [hfe, deriv_comp_smul_zero (hQ.differentiable (by norm_num)),
      restrict_eq_sum_smul_restrictIndicator, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, Complex.real_smul, (hent b b).1]
  · obtain ⟨E, Q, -, hQ, -, hval⟩ := hT.family.entry_smooth a c
    have hent := matrixEntry_variations_eq_fderiv hE (fun b b' => (hvar b b').1) hQ hval
    have hfe : entryAlong T ξ a c = fun r : ℝ => Q (r • fun e : E => ξ e.1) := by
      funext r
      simp only [entryAlong]
      rw [hval]
      rfl
    have hzero : ∀ p : B × B, p ∉ E ×ˢ E →
        (ξ p.1 : ℂ) * (ξ p.2 : ℂ) * matrixEntry (secondVar T p.1 p.2) a c = 0 := by
      intro p hp
      rw [(hent p.1 p.2).2]
      by_cases h1 : p.1 ∈ E
      · have h2 : p.2 ∉ E := fun h2 => hp (Finset.mem_product.2 ⟨h1, h2⟩)
        rw [restrictIndicator_of_not_mem h2, map_zero, mul_zero]
      · rw [restrictIndicator_of_not_mem h1, map_zero, ContinuousLinearMap.zero_apply, mul_zero]
    rw [tsum_eq_sum hzero, Finset.sum_product]
    show deriv (deriv (entryAlong T ξ a c)) 0 = _
    rw [hfe, deriv_deriv_comp_smul_zero (hQ.of_le (by norm_num)),
      restrict_eq_sum_smul_restrictIndicator]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
      Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [(hent b b').2, Complex.real_smul, Complex.real_smul]
    ring
end YangMills.Construction.Tower.LocalFamilies
end

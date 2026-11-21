import YangMills.Construction.Towers.EntriesAlongAFieldAsSumsOverBondsProof
import YangMills.Construction.Towers.GaugeTransformationsKeepTheDensityProof
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.LocalFamilies
open YangMills.Construction.OneLoopNotation
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
namespace Variations
variable {J B : Type}
theorem matrixEntry_add (S S' : BddOp (IndexL2 J)) (a c : J) :
    matrixEntry (S + S') a c = matrixEntry S a c + matrixEntry S' a c := by
  simp [matrixEntry]
theorem matrixEntry_smul (w : ℂ) (S : BddOp (IndexL2 J)) (a c : J) :
    matrixEntry (w • S) a c = w * matrixEntry S a c := by
  simp [matrixEntry]
def matrixEntryCLM (hE : MatrixEntryProperties J) (a c : J) :
    BddOp (IndexL2 J) →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun S => matrixEntry S a c
      map_add' := fun S S' => matrixEntry_add S S' a c
      map_smul' := fun r S => by simp [matrixEntry] }
    1 (fun S => by simpa using ((hE S).1 a c).2)
theorem matrixEntryCLM_apply (hE : MatrixEntryProperties J) (a c : J)
    (S : BddOp (IndexL2 J)) : matrixEntryCLM hE a c S = matrixEntry S a c := rfl
theorem ext_of_matrixEntry (hE : MatrixEntryProperties J) {S S' : BddOp (IndexL2 J)}
    (h : ∀ a c, matrixEntry S a c = matrixEntry S' a c) : S = S' := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext a
  rw [((hE S).2 f a).2, ((hE S').2 f a).2]
  simp only [h]
theorem inner_basisVec_left (i : J) (g : IndexL2 J) : inner ℂ (basisVec i) g = g i := by
  classical
  unfold basisVec
  rw [lp.inner_single_left]
  simp [RCLike.inner_apply]
open Classical in
theorem basisVec_apply (a a' : J) : (basisVec a : IndexL2 J) a' = if a' = a then 1 else 0 := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.GaugeConjugation.basisVec_apply <;> assumption
def elementaryOp (a c : J) : BddOp (IndexL2 J) :=
  (innerSL ℂ (basisVec c : IndexL2 J)).smulRight (basisVec a : IndexL2 J)
open Classical in
theorem matrixEntry_elementaryOp (a c a' c' : J) :
    matrixEntry (elementaryOp a c) a' c' = if a' = a ∧ c' = c then 1 else 0 := by
  have h : elementaryOp a c (basisVec c') =
      (inner ℂ (basisVec c : IndexL2 J) (basisVec c')) • (basisVec a : IndexL2 J) := by
    simp [elementaryOp]
  unfold matrixEntry
  rw [h, inner_basisVec_left, lp.coeFn_smul, Pi.smul_apply, basisVec_apply, basisVec_apply]
  by_cases h1 : a' = a <;> by_cases h2 : c = c' <;> simp [h1, h2, eq_comm]
theorem eq_add_sum_elementaryOp (hE : MatrixEntryProperties J) (S : Finset (J × J))
    (A A₀ : BddOp (IndexL2 J))
    (h : ∀ a c, (a, c) ∉ S → matrixEntry A a c = matrixEntry A₀ a c) :
    A = A₀ + ∑ x ∈ S, (matrixEntry A x.1 x.2 - matrixEntry A₀ x.1 x.2) • elementaryOp x.1 x.2 := by
  classical
  apply ext_of_matrixEntry hE
  intro a c
  have hsum : matrixEntry (∑ x ∈ S, (matrixEntry A x.1 x.2 - matrixEntry A₀ x.1 x.2) •
      elementaryOp x.1 x.2) a c =
      ∑ x ∈ S, (matrixEntry A x.1 x.2 - matrixEntry A₀ x.1 x.2) *
        matrixEntry (elementaryOp x.1 x.2) a c := by
    have := map_sum (matrixEntryCLM hE a c)
      (fun x : J × J => (matrixEntry A x.1 x.2 - matrixEntry A₀ x.1 x.2) • elementaryOp x.1 x.2) S
    simpa only [matrixEntryCLM_apply, matrixEntry_smul] using this
  rw [matrixEntry_add, hsum]
  simp only [matrixEntry_elementaryOp]
  by_cases hx : (a, c) ∈ S
  · rw [Finset.sum_eq_single_of_mem (a, c) hx]
    · simp
    · intro y _ hy
      have : ¬ (a = y.1 ∧ c = y.2) := fun h' => hy (Prod.ext h'.1.symm h'.2.symm)
      simp [this]
  · rw [Finset.sum_eq_zero, h a c hx]
    · simp
    · intro y hy
      have : ¬ (a = y.1 ∧ c = y.2) := by
        rintro ⟨rfl, rfl⟩
        exact hx hy
      simp [this]
theorem contDiff_of_matrixEntry (hE : MatrixEntryProperties J) (S : Finset (J × J))
    (F : ℝ × ℝ → BddOp (IndexL2 J))
    (hS : ∀ p a c, (a, c) ∉ S → matrixEntry (F p) a c = matrixEntry (F 0) a c)
    (hF : ∀ a c, ContDiff ℝ 2 (fun p => matrixEntry (F p) a c)) : ContDiff ℝ 2 F := by
  have h : F = fun p => F 0 +
      ∑ x ∈ S, (matrixEntry (F p) x.1 x.2 - matrixEntry (F 0) x.1 x.2) • elementaryOp x.1 x.2 :=
    funext fun p => eq_add_sum_elementaryOp hE S (F p) (F 0) (hS p)
  rw [h]
  refine contDiff_const.add (ContDiff.sum fun x _ => ?_)
  exact ((hF x.1 x.2).sub contDiff_const).smul contDiff_const
theorem opNorm_le_of_matrixEntry {pos : J → InfiniteLattice.AmbientSpace}
    (hE : MatrixEntryProperties J) (hO : BoundedKernelOperator pos)
    (S : BddOp (IndexL2 J)) (K : ℝ) (hb : ∀ a c, ‖matrixEntry S a c‖ ≤ K)
    (hr : ∀ a c, ¬ TorusMetric.euclidNormVec (pos a - pos c) ≤ 2 → matrixEntry S a c = 0) :
    ‖S‖ ≤ 12 * 5 ^ 4 * K := by
  obtain ⟨T', h1, h2, -⟩ := hO K (fun a c => matrixEntry S a c) hb hr
  have hST : S = T' := by
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext a
    rw [((hE S).2 f a).2, (h1 f a).2.2]
  rw [hST]
  exact h2
section Derivatives
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem clm_deriv_comm {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : X →L[ℝ] Y)
    {g : ℝ → X} {x : ℝ} (hg : DifferentiableAt ℝ g x) :
    L (deriv g x) = deriv (fun y => L (g y)) x :=
  ((L.hasFDerivAt).comp_hasDerivAt x hg.hasDerivAt).deriv.symm
theorem hasDerivAt_lineComp {Q : X → ℂ} (hQ : Differentiable ℝ Q) (w u : X) :
    HasDerivAt (fun t : ℝ => Q (w + t • u)) (fderiv ℝ Q w u) 0 := by
  have hline : HasDerivAt (fun t : ℝ => w + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add w
  have hw : w + (0 : ℝ) • u = w := by simp
  have h := (hQ (w + (0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
  rw [hw] at h
  exact h
theorem deriv_deriv_lineComp {Q : X → ℂ} (hQ : ContDiff ℝ 2 Q) (u v : X) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => Q (s • u + t • v)) 0) 0 =
      fderiv ℝ (fderiv ℝ Q) 0 u v := by apply _root_.YangMills.Construction.Tower.LocalFamilies.EdgeSums.deriv_deriv_comp_add_smul_zero <;> assumption
theorem clm_deriv_deriv_comm {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y) {G : ℝ × ℝ → X} (hG : ContDiff ℝ 2 G) :
    L (deriv (fun s : ℝ => deriv (fun t : ℝ => G (s, t)) 0) 0) =
      deriv (fun s : ℝ => deriv (fun t : ℝ => L (G (s, t))) 0) 0 := by apply _root_.YangMills.Construction.Tower.LocalFamilies.EdgeSums.clm_deriv_deriv_comm <;> assumption
end Derivatives
theorem finite_indices_near {pos : J → InfiniteLattice.AmbientSpace} {m : ℕ}
    (hp : IsIntegerPlacement pos m) (n : Fin 4 → ℤ) :
    {i | TorusMetric.euclidNormVec (PeriodicOperators.castVec n - pos i) ≤ 2}.Finite := by
  have hfin : (⋃ k ∈ Set.Icc (n - 2) (n + 2),
      {i | pos i = PeriodicOperators.castVec k}).Finite :=
    (Set.finite_Icc _ _).biUnion fun k _ => (hp.fibre_bounded _).1
  refine hfin.subset fun i hi => ?_
  obtain ⟨k, hk⟩ := hp.on_lattice i
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨k, ?_, hk⟩
  have hcoord : ∀ μ, |(n μ : ℝ) - k μ| ≤ 2 := by
    intro μ
    have hi' : Real.sqrt (∑ ν, (PeriodicOperators.castVec n - pos i) ν ^ 2) ≤ 2 := hi
    have h1 : ((n μ : ℝ) - k μ) ^ 2 ≤
        ∑ ν, (PeriodicOperators.castVec n - pos i) ν ^ 2 := by
      have := Finset.single_le_sum (f := fun ν => (PeriodicOperators.castVec n - pos i) ν ^ 2)
        (fun ν _ => sq_nonneg _) (Finset.mem_univ μ)
      simpa [hk, PeriodicOperators.castVec] using this
    exact (Real.abs_le_sqrt h1).trans hi'
  constructor
  · intro μ
    have := (abs_le.1 (hcoord μ)).2
    have h' : n μ - k μ ≤ 2 := by exact_mod_cast this
    simp only [Pi.sub_apply, Pi.ofNat_apply]
    omega
  · intro μ
    have := (abs_le.1 (hcoord μ)).1
    have h' : -2 ≤ n μ - k μ := by exact_mod_cast this
    simp only [Pi.add_apply, Pi.ofNat_apply]
    omega
def restrictIndicator (E : Finset B) (b : B) : E → ℝ := fun e => bondIndicator b e.1
theorem restrictIndicator_eq_zero {E : Finset B} {b : B} (h : b ∉ E) :
    restrictIndicator E b = 0 := by apply _root_.YangMills.Construction.Tower.LocalFamilies.EdgeSums.restrictIndicator_of_not_mem <;> assumption
theorem norm_restrictIndicator_le (E : Finset B) (b : B) : ‖restrictIndicator E b‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun e => ?_
  by_cases h : e.1 = b <;> simp [restrictIndicator, bondIndicator, h]
end Variations
open Variations in
theorem localFamilyVariations_holds : LocalFamilyVariations := by
  classical
  intro J B pos src m m' z C T hz hC hT b b'
  have hE := hT.space.entryFacts
  have hO := hT.space.kernelOps
  set G : ℝ × ℝ → BddOp (IndexL2 J) := fun p => T (twoBondField b b' p.1 p.2) with hGdef
  have hform : ∀ a c, ∃ (E : Finset B) (Q : (E → ℝ) → ℂ),
      (b ∈ E → TorusMetric.euclidNormVec (src b - pos a) ≤ 2) ∧
      (b' ∈ E → TorusMetric.euclidNormVec (src b' - pos a) ≤ 2) ∧
      ContDiff ℝ 3 Q ∧ (∀ k : ℕ, k ≤ 3 → ∀ φ, ‖iteratedFDeriv ℝ k Q φ‖ ≤ C) ∧
      ∀ p : ℝ × ℝ, matrixEntry (G p) a c =
        Q (p.1 • restrictIndicator E b + p.2 • restrictIndicator E b') := by
    intro a c
    obtain ⟨E, Q, hnear, hQ, hbd, hval⟩ := hT.family.entry_smooth a c
    refine ⟨E, Q, hnear b, hnear b', hQ, hbd, fun p => ?_⟩
    rw [hGdef]
    simp only
    rw [hval]
    congr 1
  have hentry : ∀ a c, ContDiff ℝ 2 (fun p => matrixEntry (G p) a c) := by
    intro a c
    obtain ⟨E, Q, -, -, hQ, -, hval⟩ := hform a c
    have : (fun p => matrixEntry (G p) a c) =
        fun p : ℝ × ℝ => Q (p.1 • restrictIndicator E b + p.2 • restrictIndicator E b') :=
      funext hval
    rw [this]
    exact (hQ.of_le (by norm_num)).comp
      ((contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const))
  have hnearFin : ∀ x : B, {i | TorusMetric.euclidNormVec (src x - pos i) ≤ 2}.Finite := by
    intro x
    obtain ⟨n, hn⟩ := hT.edges.on_lattice x
    rw [hn]
    exact finite_indices_near hT.space.placement n
  have hrangeFin : ∀ a : J,
      {i | TorusMetric.euclidNormVec (pos a - pos i) ≤ 2}.Finite := by
    intro a
    obtain ⟨n, hn⟩ := hT.space.placement.on_lattice a
    rw [hn]
    exact finite_indices_near hT.space.placement n
  have hSfin : (⋃ a ∈ {i | TorusMetric.euclidNormVec (src b - pos i) ≤ 2} ∪
      {i | TorusMetric.euclidNormVec (src b' - pos i) ≤ 2},
      (fun c => (a, c)) '' {i | TorusMetric.euclidNormVec (pos a - pos i) ≤ 2}).Finite :=
    ((hnearFin b).union (hnearFin b')).biUnion fun a _ => (hrangeFin a).image _
  have hmove : ∀ p a c, (a, c) ∉ hSfin.toFinset → matrixEntry (G p) a c = matrixEntry (G 0) a c := by
    intro p a c hac
    by_cases hr : TorusMetric.euclidNormVec (pos a - pos c) ≤ 2
    · have hnb : ¬ TorusMetric.euclidNormVec (src b - pos a) ≤ 2 := fun h => hac (by
        simp only [Set.Finite.mem_toFinset, Set.mem_iUnion]
        exact ⟨a, Or.inl h, c, hr, rfl⟩)
      have hnb' : ¬ TorusMetric.euclidNormVec (src b' - pos a) ≤ 2 := fun h => hac (by
        simp only [Set.Finite.mem_toFinset, Set.mem_iUnion]
        exact ⟨a, Or.inr h, c, hr, rfl⟩)
      obtain ⟨E, Q, h1, h2, -, -, hval⟩ := hform a c
      rw [hval, hval, restrictIndicator_eq_zero (fun h => hnb (h1 h)),
        restrictIndicator_eq_zero (fun h => hnb' (h2 h))]
      simp
    · rw [show matrixEntry (G p) a c = 0 from hT.family.finite_range _ a c hr,
        show matrixEntry (G 0) a c = 0 from hT.family.finite_range _ a c hr]
  have hG : ContDiff ℝ 2 G := contDiff_of_matrixEntry hE hSfin.toFinset G hmove hentry
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
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hlineDiff : DifferentiableAt ℝ (fun s : ℝ => G (s, 0)) 0 :=
    ((hGd _).comp (0 : ℝ) (differentiableAt_id.prodMk (differentiableAt_const 0)))
  have hfirst : ∀ a c, matrixEntry (firstVar T b) a c =
      deriv (fun s : ℝ => matrixEntry (G (s, 0)) a c) 0 := by
    intro a c
    rw [hfirstG]
    exact clm_deriv_comm (matrixEntryCLM hE a c) hlineDiff
  have hsecond : ∀ a c, matrixEntry (secondVar T b b') a c =
      deriv (fun s : ℝ => deriv (fun t : ℝ => matrixEntry (G (s, t)) a c) 0) 0 := by
    intro a c
    rw [hsecondG]
    exact clm_deriv_deriv_comm (matrixEntryCLM hE a c) hG
  have hfirstQ : ∀ a c (E : Finset B) (Q : (E → ℝ) → ℂ), ContDiff ℝ 3 Q →
      (∀ p : ℝ × ℝ, matrixEntry (G p) a c =
        Q (p.1 • restrictIndicator E b + p.2 • restrictIndicator E b')) →
      matrixEntry (firstVar T b) a c = fderiv ℝ Q 0 (restrictIndicator E b) := by
    intro a c E Q hQ hval
    rw [hfirst]
    have h1 : (fun s : ℝ => matrixEntry (G (s, 0)) a c) =
        fun s : ℝ => Q (0 + s • restrictIndicator E b) := by
      funext s
      rw [hval]
      simp
    rw [h1]
    exact (hasDerivAt_lineComp (hQ.differentiable (by norm_num)) 0 _).deriv
  have hsecondQ : ∀ a c (E : Finset B) (Q : (E → ℝ) → ℂ), ContDiff ℝ 3 Q →
      (∀ p : ℝ × ℝ, matrixEntry (G p) a c =
        Q (p.1 • restrictIndicator E b + p.2 • restrictIndicator E b')) →
      matrixEntry (secondVar T b b') a c =
        fderiv ℝ (fderiv ℝ Q) 0 (restrictIndicator E b) (restrictIndicator E b') := by
    intro a c E Q hQ hval
    rw [hsecond]
    have h1 : (fun s : ℝ => deriv (fun t : ℝ => matrixEntry (G (s, t)) a c) 0) =
        fun s : ℝ => deriv (fun t : ℝ =>
          Q (s • restrictIndicator E b + t • restrictIndicator E b')) 0 := by
      funext s
      congr 1
      funext t
      exact hval (s, t)
    rw [h1]
    exact deriv_deriv_lineComp (hQ.of_le (by norm_num)) _ _
  have hbound1 : ∀ a c, ‖matrixEntry (firstVar T b) a c‖ ≤ C := by
    intro a c
    obtain ⟨E, Q, -, -, hQ, hbd, hval⟩ := hform a c
    rw [hfirstQ a c E Q hQ hval]
    have h1 : ‖fderiv ℝ Q 0‖ ≤ C := by
      rw [← norm_iteratedFDeriv_one]
      exact hbd 1 (by norm_num) 0
    calc ‖fderiv ℝ Q 0 (restrictIndicator E b)‖
        ≤ ‖fderiv ℝ Q 0‖ * ‖restrictIndicator E b‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * 1 := mul_le_mul h1 (norm_restrictIndicator_le E b) (norm_nonneg _) hC.le
      _ = C := mul_one C
  have hbound2 : ∀ a c, ‖matrixEntry (secondVar T b b') a c‖ ≤ C := by
    intro a c
    obtain ⟨E, Q, -, -, hQ, hbd, hval⟩ := hform a c
    rw [hsecondQ a c E Q hQ hval]
    have h1 : ‖fderiv ℝ (fderiv ℝ Q) 0‖ ≤ C := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
      exact hbd 2 (by norm_num) 0
    calc ‖fderiv ℝ (fderiv ℝ Q) 0 (restrictIndicator E b) (restrictIndicator E b')‖
        ≤ ‖fderiv ℝ (fderiv ℝ Q) 0‖ * ‖restrictIndicator E b‖ * ‖restrictIndicator E b'‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ C * 1 * 1 := by
          gcongr
          · exact norm_restrictIndicator_le E b
          · exact norm_restrictIndicator_le E b'
      _ = C := by ring
  have hrange : ∀ a c, ¬ TorusMetric.euclidNormVec (pos a - pos c) ≤ 2 →
      matrixEntry (firstVar T b) a c = 0 ∧ matrixEntry (secondVar T b b') a c = 0 := by
    intro a c hr
    have hzero : ∀ p, matrixEntry (G p) a c = 0 := fun p => hT.family.finite_range _ a c hr
    constructor
    · rw [hfirst]
      simp [hzero]
    · rw [hsecond]
      simp [hzero]
  have hplace : ∀ a c, ¬ TorusMetric.euclidNormVec (src b - pos a) ≤ 2 →
      matrixEntry (firstVar T b) a c = 0 ∧ matrixEntry (secondVar T b b') a c = 0 := by
    intro a c hn
    obtain ⟨E, Q, h1, -, hQ, -, hval⟩ := hform a c
    have hu := restrictIndicator_eq_zero (fun h => hn (h1 h))
    rw [hfirstQ a c E Q hQ hval, hsecondQ a c E Q hQ hval, hu]
    simp
  have hplace' : ∀ a c, ¬ TorusMetric.euclidNormVec (src b' - pos a) ≤ 2 →
      matrixEntry (secondVar T b b') a c = 0 := by
    intro a c hn
    obtain ⟨E, Q, -, h2, hQ, -, hval⟩ := hform a c
    have hv := restrictIndicator_eq_zero (fun h => hn (h2 h))
    rw [hsecondQ a c E Q hQ hval, hv]
    simp
  exact ⟨hG, fun a c => ⟨hbound1 a c, hbound2 a c⟩, hrange, hplace, hplace',
    opNorm_le_of_matrixEntry hE hO _ C hbound1 fun a c h => (hrange a c h).1,
    opNorm_le_of_matrixEntry hE hO _ C hbound2 fun a c h => (hrange a c h).2⟩
end YangMills.Construction.Tower.LocalFamilies
end

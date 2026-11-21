import YangMills.Construction.InfiniteLattice.MomentsOfTheColumnOverACell
import YangMills.Construction.InfiniteLattice.MovesOfTheColumnOverACell
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAreReflectionPositiveOnHalfSpaces
import YangMills.Construction.InfiniteLattice.ReflectionFormAndTransferOperatorOfAPeriodicGibbsState
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (IsBoundedObservable IsBoundedlyLocalizedIn IsLocalizedAbove IsLocalizedBelow
  AmbientSpace upperAlgebra halfSpaceAbove halfSpaceBelow reflectionPairing reflectionPairingRoot
  timeAxis ReflectionPairingIsPosHermitian ReflectionSeminormEstimates)
namespace MultipleReflections
namespace StackCorrelations
variable {D : Setup} (G : D.Grid) (k : Fin 4 → ℤ)
theorem isBoundedObservable_mul {A A' : D.GaugeField → ℂ} (h : IsBoundedObservable A)
    (h' : IsBoundedObservable A') : IsBoundedObservable (A * A') := by
  obtain ⟨m, C, hC⟩ := h
  obtain ⟨m', C', hC'⟩ := h'
  refine ⟨m.mul m', |C| * |C'|, fun U => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul ((hC U).trans (le_abs_self C)) ((hC' U).trans (le_abs_self C'))
    (norm_nonneg _) (abs_nonneg _)
theorem isBoundedlyLocalizedIn_mono {H H' : Set AmbientSpace} (hH : H ⊆ H') {A : D.GaugeField → ℂ}
    (h : IsBoundedlyLocalizedIn H A) : IsBoundedlyLocalizedIn H' A := by
  obtain ⟨hA, S, hS, hb, hm⟩ := h
  exact ⟨hA, S, hS.trans hH, hb, hm⟩
theorem regionSigma_mono {S S' : Set AmbientSpace} (h : S ⊆ S') :
    (InfiniteLattice.regionSigma S : MeasurableSpace D.GaugeField) ≤ InfiniteLattice.regionSigma S' :=
  biSup_mono fun _ hb => ⟨h hb.1, h hb.2⟩
theorem isBoundedlyLocalizedIn_mul {H : Set AmbientSpace} {A A' : D.GaugeField → ℂ}
    (h : IsBoundedlyLocalizedIn H A) (h' : IsBoundedlyLocalizedIn H A') :
    IsBoundedlyLocalizedIn H (A * A') := by
  obtain ⟨hA, S, hS, hb, hm⟩ := h
  obtain ⟨hA', S', hS', hb', hm'⟩ := h'
  refine ⟨isBoundedObservable_mul hA hA', S ∪ S', Set.union_subset hS hS', hb.union hb', ?_⟩
  exact (hm.mono (regionSigma_mono Set.subset_union_left) le_rfl).mul
    (hm'.mono (regionSigma_mono Set.subset_union_right) le_rfl)
theorem wallTime_mono {i j : ℤ} (h : i ≤ j) : G.wallTime k i ≤ G.wallTime k j := by
  have hl := G.edge_pos
  have hij : (i : ℝ) ≤ j := by exact_mod_cast h
  simp only [Setup.Grid.wallTime]
  nlinarith
theorem isLocalizedBelow_mono {i j : ℤ} (h : i ≤ j) {Z : D.GaugeField → ℂ}
    (hZ : IsLocalizedBelow (G.wallTimeHalf k i) Z) : IsLocalizedBelow (G.wallTimeHalf k j) Z :=
  isBoundedlyLocalizedIn_mono (fun _ hx => lt_of_lt_of_le hx (wallTime_mono G k h)) hZ
theorem isLocalizedAbove_mono {i j : ℤ} (h : i ≤ j) {Z : D.GaugeField → ℂ}
    (hZ : IsLocalizedAbove (G.wallTimeHalf k j) Z) : IsLocalizedAbove (G.wallTimeHalf k i) Z :=
  isBoundedlyLocalizedIn_mono (fun _ hx => lt_of_le_of_lt (wallTime_mono G k h) hx) hZ
theorem stackReflect_mul (n : ℤ) (A A' : D.GaugeField → ℂ) :
    G.stackReflect k n (A * A') = G.stackReflect k n A * G.stackReflect k n A' := by
  funext U
  simp [Setup.Grid.stackReflect, InfiniteLattice.LatticeSymmetry.actOn]
theorem stackProd_mul_stackProd (F : D.GaugeField → ℂ) {i₁ j i₂ : ℤ} (h₁ : i₁ ≤ j + 1)
    (h₂ : j ≤ i₂) (U : D.GaugeField) :
    G.stackProd k F i₁ j U * G.stackProd k F (j + 1) i₂ U = G.stackProd k F i₁ i₂ U := by
  have hu : Finset.Icc i₁ i₂ = Finset.Icc i₁ j ∪ Finset.Icc (j + 1) i₂ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hd : Disjoint (Finset.Icc i₁ j) (Finset.Icc (j + 1) i₂) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rw [Finset.mem_Icc] at hx hy
    omega
  simp only [Setup.Grid.stackProd]
  rw [hu, Finset.prod_union hd]
variable {G k}
theorem stackReflect_stackReflect (hC : G.StackReflectionsCompose k) (n : ℤ)
    {A : D.GaugeField → ℂ} (hA : IsBoundedObservable A) :
    G.stackReflect k n (G.stackReflect k n A) = A := by
  have h := hC.1 n n A hA
  rw [sub_self, mul_zero, G.stackShift_zero] at h
  exact h
theorem reflectionPairing_stackReflect {μ : Measure D.GaugeField} (hC : G.StackReflectionsCompose k)
    (n : ℤ) {Z Z' : D.GaugeField → ℂ} (hZ : IsBoundedObservable Z) :
    reflectionPairing μ (G.wallTimeHalf k n) (G.stackReflect k n Z) Z' = ∫ U, Z U * Z' U ∂μ := by
  change ∫ U, G.stackReflect k n (G.stackReflect k n Z) U * Z' U ∂μ = _
  rw [stackReflect_stackReflect hC n hZ]
theorem reflectionSeminorm_sq {μ : Measure D.GaugeField}
    {t : InfiniteLattice.halfSpacingTimes D.mesh} {A : D.GaugeField → ℂ}
    (h : 0 ≤ (reflectionPairing μ t A A).re) :
    reflectionPairingRoot μ t A ^ 2 = (reflectionPairing μ t A A).re :=
  Real.sq_sqrt h
theorem integral_mul_stackReflect_nonneg {μ : Measure D.GaugeField}
    (hC : G.StackReflectionsCompose k) (hX : G.StackReflectionsCrossWalls k)
    (hP : ∀ n, ReflectionPairingIsPosHermitian μ (G.wallTimeHalf k n)) (n : ℤ)
    {Z : D.GaugeField → ℂ} (hZ : IsLocalizedBelow (G.wallTimeHalf k n) Z) :
    (∫ U, Z U * G.stackReflect k n Z U ∂μ).im = 0 ∧
      0 ≤ (∫ U, Z U * G.stackReflect k n Z U ∂μ).re := by
  rw [← reflectionPairing_stackReflect hC n hZ.1]
  exact (hP n).2.2.2 _ (hX.1 n Z hZ)
theorem norm_integral_sq_le {μ : Measure D.GaugeField} (hC : G.StackReflectionsCompose k)
    (hX : G.StackReflectionsCrossWalls k)
    (hP : ∀ n, ReflectionPairingIsPosHermitian μ (G.wallTimeHalf k n))
    (hS : ∀ n, ReflectionSeminormEstimates μ (G.wallTimeHalf k n)) (n : ℤ)
    {Z Z' : D.GaugeField → ℂ} (hZ : IsLocalizedBelow (G.wallTimeHalf k n) Z)
    (hZ' : IsLocalizedAbove (G.wallTimeHalf k n) Z') :
    ‖∫ U, Z U * Z' U ∂μ‖ ^ 2 ≤
      (∫ U, Z U * G.stackReflect k n Z U ∂μ).re * (∫ U, G.stackReflect k n Z' U * Z' U ∂μ).re := by
  have hc := hX.1 n Z hZ
  have h₁ := (hS n).1 _ hc _ hZ'
  have p₁ := ((hP n).2.2.2 _ hc).2
  have p₂ := ((hP n).2.2.2 _ hZ').2
  rw [reflectionPairing_stackReflect hC n hZ.1] at h₁
  have e₁ : (∫ U, Z U * G.stackReflect k n Z U ∂μ).re =
      reflectionPairingRoot μ (G.wallTimeHalf k n) (G.stackReflect k n Z) ^ 2 := by
    rw [reflectionSeminorm_sq p₁, reflectionPairing_stackReflect hC n hZ.1]
  have e₂ : (∫ U, G.stackReflect k n Z' U * Z' U ∂μ).re =
      reflectionPairingRoot μ (G.wallTimeHalf k n) Z' ^ 2 := by
    rw [reflectionSeminorm_sq p₂]
    rfl
  rw [e₁, e₂, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h₁ 2
end StackCorrelations
open StackCorrelations in
theorem stackCorrelationsLogConvex_of
    (hMoves : StackMovesHold)
    (hRF : InfiniteLattice.PeriodicGibbsReflectionTransfer)
    (hStrong : HalfSpacePositivity.Statement) :
    StackCorrelationsLogConvex := by
  intro D μ hμ G k F hF
  obtain ⟨hC, hX, hCop⟩ := hMoves D G k
  obtain ⟨hc1, -, -, hthP, htauP, hslab⟩ := hCop F hF
  have hP : ∀ n, ReflectionPairingIsPosHermitian μ (G.wallTimeHalf k n) :=
    fun n => (hRF D μ hμ (G.wallTimeHalf k n)).2.1
  have hS : ∀ n, ReflectionSeminormEstimates μ (G.wallTimeHalf k n) :=
    fun n => (hRF D μ hμ (G.wallTimeHalf k n)).2.2.1
  have hInv : ∀ (i : ℤ) (X : D.GaugeField → ℂ), IsBoundedObservable X →
      ∫ U, (G.stackShift i).actOn X U ∂μ = ∫ U, X U ∂μ :=
    fun i X hX' => (hStrong D μ hμ).1 _ X hX'
  have hbelow : ∀ A ∈ upperAlgebra (G.wallTimeHalf k 0), ∀ n : ℕ,
      IsLocalizedBelow (G.wallTimeHalf k n) (G.stackReflect k 0 A * G.stackProd k F 1 n) := by
    intro A hA n
    refine isBoundedlyLocalizedIn_mul
      (isLocalizedBelow_mono G k (Int.natCast_nonneg n) (hX.2.1 0 A hA)) ?_
    exact isBoundedlyLocalizedIn_mono (fun _ hx => hx.2) (hslab 1 n (by omega))
  have hmoment : ∀ A ∈ upperAlgebra (G.wallTimeHalf k 0), ∀ n : ℕ,
      ∫ U, (G.stackReflect k 0 A * G.stackProd k F 1 n) U *
        G.stackReflect k n (G.stackReflect k 0 A * G.stackProd k F 1 n) U ∂μ =
      G.stackCorrelation k μ F A n := by
    intro A hA n
    have h1 : G.stackReflect k n (G.stackReflect k 0 A) =
        (G.stackShift (2 * (n : ℤ))).actOn A := by
      have := hC.1 n 0 A hA.1
      rwa [sub_zero] at this
    have h2 : G.stackReflect k n (G.stackProd k F 1 n) =
        G.stackProd k F ((n : ℤ) + 1) (2 * n) := by
      have := hthP n 1 n (by omega)
      rw [this]
      congr 1 <;> ring
    rw [stackReflect_mul, h1, h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    have h3 := stackProd_mul_stackProd G k F (i₁ := 1) (j := n) (i₂ := 2 * n) (by omega) (by omega) U
    simp only [Pi.mul_apply]
    rw [← h3]
    ring
  refine ⟨fun A hA => ⟨fun n => ?_, ?_, fun n hn => ?_⟩, fun A hA B hB => ?_⟩
  · rw [← hmoment A hA n]
    exact integral_mul_stackReflect_nonneg hC hX hP n (hbelow A hA n)
  · have hz := (hP 0).2.2.2 A hA
    have e : G.stackCorrelation k μ F A 0 = reflectionPairing μ (G.wallTimeHalf k 0) A A := by
      have hp : G.stackProd k F 1 (2 * ((0 : ℕ) : ℤ)) = 1 := by
        simpa using G.stackProd_empty k F 1
      have hs : (G.stackShift (2 * ((0 : ℕ) : ℤ))).actOn A = A := by
        simpa using G.stackShift_zero A
      simp only [Setup.Grid.stackCorrelation]
      rw [hp, hs]
      simp only [Pi.one_apply, mul_one]
      rfl
    rw [e]
    apply Complex.ext
    · rw [Complex.ofReal_re, reflectionSeminorm_sq hz.2]
    · rw [Complex.ofReal_im, hz.1]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hT : IsLocalizedBelow (G.wallTimeHalf k 0) (G.stackReflect k 0 A) := hX.2.1 0 A hA
    have hZ := hbelow A hA m
    have hZ' : IsLocalizedAbove (G.wallTimeHalf k m)
        (G.stackProd k F ((m : ℤ) + 1) (2 * ((m + 1 : ℕ) : ℤ)) *
          (G.stackShift (2 * ((m + 1 : ℕ) : ℤ))).actOn A) := by
      refine isBoundedlyLocalizedIn_mul
        (isBoundedlyLocalizedIn_mono (fun x hx => ?_) (hslab _ _ (by omega)))
        (isLocalizedAbove_mono G k (by omega) (hX.2.2 _ A hA))
      have h := hx.1
      rw [add_sub_cancel_right] at h
      exact h
    have e₁ : ∫ U, (G.stackReflect k 0 A * G.stackProd k F 1 m) U *
        (G.stackProd k F ((m : ℤ) + 1) (2 * ((m + 1 : ℕ) : ℤ)) *
          (G.stackShift (2 * ((m + 1 : ℕ) : ℤ))).actOn A) U ∂μ =
        G.stackCorrelation k μ F A (m + 1) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
      have h3 := stackProd_mul_stackProd G k F (i₁ := 1) (j := m) (i₂ := 2 * ((m + 1 : ℕ) : ℤ))
        (by omega) (by omega) U
      simp only [Pi.mul_apply]
      rw [← h3]
      ring
    have hθ₁ : G.stackReflect k m (G.stackProd k F ((m : ℤ) + 1) (2 * ((m + 1 : ℕ) : ℤ))) =
        G.stackProd k F (-1) m := by
      rw [hthP m _ _ (by omega)]
      congr 1 <;> push_cast <;> ring
    have hθ₂ : G.stackReflect k m ((G.stackShift (2 * ((m + 1 : ℕ) : ℤ))).actOn A) =
        (G.stackShift (-2)).actOn (G.stackReflect k 0 A) := by
      have h1 : G.stackReflect k m A =
          (G.stackShift (2 * (m : ℤ))).actOn (G.stackReflect k 0 A) := by
        have h := hC.1 m 0 (G.stackReflect k 0 A) hT.1
        rw [stackReflect_stackReflect hC 0 hA.1, sub_zero] at h
        exact h
      have h2 : -(2 * ((m + 1 : ℕ) : ℤ)) + 2 * (m : ℤ) = -2 := by
        push_cast
        ring
      rw [hC.2.1 m _ A hA.1, h1, ← G.stackShift_add, h2]
    have e₃ : ∫ U, G.stackReflect k m
          (G.stackProd k F ((m : ℤ) + 1) (2 * ((m + 1 : ℕ) : ℤ)) *
            (G.stackShift (2 * ((m + 1 : ℕ) : ℤ))).actOn A) U *
          (G.stackProd k F ((m : ℤ) + 1) (2 * ((m + 1 : ℕ) : ℤ)) *
            (G.stackShift (2 * ((m + 1 : ℕ) : ℤ))).actOn A) U ∂μ =
        G.stackCorrelation k μ F A (m + 1 + 1) := by
      have hobs := isBoundedObservable_mul (hX.2.1 m _ hZ').1 hZ'.1
      have hI := hInv (2 * 1) _ hobs
      refine ((integral_congr_ae (Filter.Eventually.of_forall fun U => rfl)).trans hI.symm).trans ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
      have t₁ : (G.stackShift (2 * 1)).actOn (G.stackProd k F (-1) m) =
          G.stackProd k F 1 ((m : ℤ) + 2) := by
        rw [htauP 1 _ _ (by omega)]
        congr 1
      have t₂ : (G.stackShift (2 * 1)).actOn
          ((G.stackShift (-2)).actOn (G.stackReflect k 0 A)) = G.stackReflect k 0 A := by
        rw [← G.stackShift_add]
        exact G.stackShift_zero _
      have t₃ : (G.stackShift (2 * 1)).actOn
          (G.stackProd k F ((m : ℤ) + 1) (2 * ((m + 1 : ℕ) : ℤ))) =
          G.stackProd k F ((m : ℤ) + 2 + 1) (2 * ((m + 1 + 1 : ℕ) : ℤ)) := by
        rw [htauP 1 _ _ (by omega)]
        congr 1
      have t₄ : (G.stackShift (2 * 1)).actOn
          ((G.stackShift (2 * ((m + 1 : ℕ) : ℤ))).actOn A) =
          (G.stackShift (2 * ((m + 1 + 1 : ℕ) : ℤ))).actOn A := by
        rw [← G.stackShift_add]
        congr 2
        push_cast
        ring
      have h3 := stackProd_mul_stackProd G k F (i₁ := 1) (j := (m : ℤ) + 2)
        (i₂ := 2 * ((m + 1 + 1 : ℕ) : ℤ)) (by omega) (by omega) U
      have a₁ := congrFun t₁ U
      have a₂ := congrFun t₂ U
      have a₃ := congrFun t₃ U
      have a₄ := congrFun t₄ U
      rw [stackReflect_mul, hθ₁, hθ₂]
      change ((G.stackShift (2 * 1)).actOn (G.stackProd k F (-1) m) U *
          (G.stackShift (2 * 1)).actOn
            ((G.stackShift (-2)).actOn (G.stackReflect k 0 A)) U) *
          ((G.stackShift (2 * 1)).actOn
            (G.stackProd k F ((m : ℤ) + 1) (2 * ((m + 1 : ℕ) : ℤ))) U *
          (G.stackShift (2 * 1)).actOn
            ((G.stackShift (2 * ((m + 1 : ℕ) : ℤ))).actOn A) U) = _
      rw [a₁, a₂, a₃, a₄]
      change _ = G.stackReflect k 0 A U * G.stackProd k F 1 (2 * ((m + 1 + 1 : ℕ) : ℤ)) U *
        (G.stackShift (2 * ((m + 1 + 1 : ℕ) : ℤ))).actOn A U
      rw [← h3]
      ring
    have sw := norm_integral_sq_le hC hX hP hS m hZ hZ'
    rw [e₁, hmoment A hA m, e₃] at sw
    have hre := Complex.abs_re_le_norm (G.stackCorrelation k μ F A (m + 1))
    calc (G.stackCorrelation k μ F A (m + 1)).re ^ 2
        = |(G.stackCorrelation k μ F A (m + 1)).re| ^ 2 := (sq_abs _).symm
      _ ≤ ‖G.stackCorrelation k μ F A (m + 1)‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hre 2
      _ ≤ _ := sw
  · have hP11 : G.stackProd k F 1 ((1 : ℕ) : ℤ) = F := by
      funext U
      simp only [Setup.Grid.stackProd, Nat.cast_one, Finset.Icc_self, Finset.prod_singleton]
      exact congrFun hc1 U
    have hT : IsLocalizedBelow (G.wallTimeHalf k 0) (G.stackReflect k 0 A) := hX.2.1 0 A hA
    have hZ := hbelow B hB 1
    have hZ' : IsLocalizedAbove (G.wallTimeHalf k ((1 : ℕ) : ℤ)) ((G.stackShift 1).actOn A) := by
      rw [Nat.cast_one]
      exact hX.2.2 1 A hA
    have e₃ : ∫ U, G.stackReflect k ((1 : ℕ) : ℤ) ((G.stackShift 1).actOn A) U *
        (G.stackShift 1).actOn A U ∂μ =
        reflectionPairing μ (G.wallTimeHalf k 0) A A := by
      have h := hC.2.2.1 0 1 A hA.1
      rw [zero_add] at h
      rw [Nat.cast_one, h]
      exact hInv 1 (G.stackReflect k 0 A * A) (isBoundedObservable_mul hT.1 hA.1)
    have sw := norm_integral_sq_le hC hX hP hS ((1 : ℕ) : ℤ) hZ hZ'
    rw [hmoment B hB 1, e₃, hP11, ← reflectionSeminorm_sq ((hP 0).2.2.2 A hA).2] at sw
    exact sw
end MultipleReflections
end YangMills.Construction
end

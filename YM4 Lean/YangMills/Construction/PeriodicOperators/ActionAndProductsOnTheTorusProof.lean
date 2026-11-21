import YangMills.Construction.PeriodicOperators.ActionAndProductsOnTheTorus
import YangMills.Construction.PeriodicOperators.OrbitsOfAPeriodicIndexSet
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.PeriodicOperators.SymbolsOfPeriodicOperators
import YangMills.Construction.PeriodicOperators.TorusKernelOfAPeriodicOperator
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TorusAction
open YangMills.Construction.TorusMetric (euclidNormVec)
variable {I I' I'' : PeriodicData}
theorem exists_decayRate {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) :
    ∃ δ, IsDecayRate I I' T δ := by
  obtain ⟨_, C, δ, hC, hδ, hb⟩ := hT
  exact ⟨δ, hδ, C, hC, hb⟩
theorem decayRate_of_le {T : I'.Carrier → I.Carrier → ℂ} {δ δ' : ℝ} (h : IsDecayRate I I' T δ)
    (h0 : 0 < δ') (hle : δ' ≤ δ) : IsDecayRate I I' T δ' := by
  obtain ⟨_, C, hC, hb⟩ := h
  refine ⟨h0, C, hC, fun x y => (hb x y).trans ?_⟩
  have hd : 0 ≤ euclidNormVec (I'.pos x - I.pos y) := Real.sqrt_nonneg _
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
  nlinarith
def quotRep {s : ℕ} (c : I.QuotMod s) : I.Carrier := Quot.out c
theorem mkQuot_quotRep {s : ℕ} (c : I.QuotMod s) :
    I.mkQuot s (quotRep c) = c := Quot.out_eq c
def orbitEquiv (ho : QuotOrbits.Claim) (hI : IsPeriodic I) {s : ℕ}
    (hs : 0 < s) : I.QuotMod s × (Fin 4 → ℤ) ≃ I.Carrier :=
  Equiv.ofBijective _ ((ho I hI).2 s hs quotRep mkQuot_quotRep)
def translateEquiv (hI : IsPeriodic I) (m : Fin 4 → ℤ) : I.Carrier ≃ I.Carrier where
  toFun := I.translate m
  invFun := I.translate (-m)
  left_inv x := by
    show I.translate (-m) (I.translate m x) = x
    rw [← hI.translate_add, add_neg_cancel, hI.translate_zero]
  right_inv x := by
    show I.translate m (I.translate (-m) x) = x
    rw [← hI.translate_add, neg_add_cancel, hI.translate_zero]
theorem tsum_eq_tsum_orbits (ho : QuotOrbits.Claim) (hI : IsPeriodic I)
    {s : ℕ} (hs : 0 < s) {F : I.Carrier → ℂ} (hF : Summable F) :
    ∑' x, F x = ∑' c : I.QuotMod s, ∑' n : Fin 4 → ℤ, F (I.translate (s • n) (quotRep c)) := by
  rw [← (orbitEquiv ho hI hs).tsum_eq F]
  exact ((orbitEquiv ho hI hs).summable_iff.mpr hF).tsum_prod
theorem summable_norm_row (ho : QuotOrbits.Claim)
    (ht : Periodized.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {s : ℕ} (hs : 0 < s) [Finite (I.QuotMod s)]
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) (x : I'.Carrier) :
    Summable fun y => ‖T x y‖ := by
  obtain ⟨δ, hδ⟩ := exists_decayRate hT
  have facts := ht I I' hI hI' T δ hT hδ
  rw [← (orbitEquiv ho hI hs).summable_iff]
  refine (summable_prod_of_nonneg fun _ => norm_nonneg _).mpr ⟨fun c => ?_, Summable.of_finite⟩
  exact facts.summable s hs x (quotRep c)
theorem exists_bound_of_invariant (ho : QuotOrbits.Claim)
    (hI : IsPeriodic I) {s : ℕ} [Finite (I.QuotMod s)] (F : I.Carrier → ℝ)
    (hF : ∀ (n : Fin 4 → ℤ) x, F (I.translate (s • n) x) = F x) : ∃ B, ∀ x, F x ≤ B := by
  obtain ⟨B, hB⟩ := (Set.finite_range fun c : I.QuotMod s => F (quotRep c)).bddAbove
  refine ⟨B, fun x => ?_⟩
  obtain ⟨n, hn⟩ := ((ho I hI).1 s (quotRep (I.mkQuot s x)) x).mp
    (mkQuot_quotRep _)
  rw [hn, hF]
  exact hB ⟨_, rfl⟩
theorem applyKernel_invariant (ho : QuotOrbits.Claim)
    (ht : Periodized.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {s : ℕ} (hs : 0 < s) [Finite (I.QuotMod s)]
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) (f : I.Carrier → ℂ)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hf : ∀ (n : Fin 4 → ℤ) x, f (I.translate (s • n) x) = f x) :
    (∀ x, ApplySummableAt T f x) ∧
      (∀ (n : Fin 4 → ℤ) x, applyKernel T f (I'.translate (s • n) x) = applyKernel T f x) ∧
      ∀ g : I.QuotMod s → ℂ, (∀ y, g (I.mkQuot s y) = f y) → ∀ x,
        applyKernel (periodicMatrix I I' T s) g (I'.mkQuot s x) = applyKernel T f x := by
  obtain ⟨C, hC⟩ := hb
  have formed : ∀ x, ApplySummableAt T f x := by
    intro x
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun y => ?_)
      ((summable_norm_row ho ht hI hI' hs hT x).mul_right C)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)
  refine ⟨formed, fun n x => ?_, fun g hg x => ?_⟩
  · show ∑' y, T (I'.translate (s • n) x) y * f y = ∑' y, T x y * f y
    rw [← (translateEquiv hI (s • n)).tsum_eq]
    refine tsum_congr fun y => ?_
    show T (I'.translate (s • n) x) (I.translate (s • n) y) * f (I.translate (s • n) y) = T x y * f y
    rw [hT.1, hf]
  · obtain ⟨δ, hδ⟩ := exists_decayRate hT
    have facts := ht I I' hI hI' T δ hT hδ
    show ∑' c, periodicMatrix I I' T s (I'.mkQuot s x) c * g c = ∑' y, T x y * f y
    rw [tsum_eq_tsum_orbits ho hI hs (formed x).of_norm]
    refine tsum_congr fun c => ?_
    have hrep : f (quotRep c) = g c := by
      rw [← hg, mkQuot_quotRep]
    have hinv : ∀ n : Fin 4 → ℤ, T x (I.translate (s • n) (quotRep c)) *
        f (I.translate (s • n) (quotRep c)) =
          T x (I.translate (s • n) (quotRep c)) * g c := fun n => by
      rw [hf, hrep]
    simp only [hinv]
    rw [tsum_mul_right]
    congr 1
    rw [← mkQuot_quotRep c, facts.matrix_entries s hs, mkQuot_quotRep c]
    rfl
theorem periodicMatrix_compKernel (ho : QuotOrbits.Claim)
    (hsym : Symbols.Claim)
    (ht : Periodized.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hI'' : IsPeriodic I'') {s : ℕ} (hs : 0 < s)
    [Finite (I.QuotMod s)] {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    {S : I.Carrier → I''.Carrier → ℂ} (hS : IsPeriodicKernel I'' I S) :
    periodicMatrix I'' I' (compKernel T S) s =
      compKernel (periodicMatrix I I' T s) (periodicMatrix I'' I S s) := by
  obtain ⟨δ₁, h₁⟩ := exists_decayRate hT
  obtain ⟨δ₂, h₂⟩ := exists_decayRate hS
  have hδ : 0 < min δ₁ δ₂ := lt_min h₁.1 h₂.1
  have facts := hsym.1 I I' I'' hI hI' hI'' T S (min δ₁ δ₂) hT
    (decayRate_of_le h₁ hδ (min_le_left _ _)) hS (decayRate_of_le h₂ hδ (min_le_right _ _))
  have hTS := facts.compKernel_isPeriodicKernel.2
  obtain ⟨δ₃, h₃⟩ := exists_decayRate hTS
  have fTS := ht I'' I' hI'' hI' _ δ₃ hTS h₃
  have fS := ht I'' I hI'' hI S δ₂ hS h₂
  funext c' c''
  obtain ⟨x, rfl⟩ : ∃ x, I'.mkQuot s x = c' := ⟨_, mkQuot_quotRep c'⟩
  obtain ⟨z, rfl⟩ : ∃ z, I''.mkQuot s z = c'' := ⟨_, mkQuot_quotRep c''⟩
  rw [fTS.matrix_entries s hs]
  have hclass : ∀ (n : Fin 4 → ℤ) y, I.mkQuot s (I.translate (s • n) y) = I.mkQuot s y :=
    fun n y => (((ho I hI).1 s y _).mpr ⟨n, rfl⟩).symm
  have hinv : ∀ (n : Fin 4 → ℤ) y, periodization I'' I S s (I.translate (s • n) y) z =
      periodization I'' I S s y z :=
    fun n y => fS.depends_quot s hs _ _ _ _ (hclass n y) rfl
  have hbd : ∃ C : ℝ, ∀ y, ‖periodization I'' I S s y z‖ ≤ C :=
    exists_bound_of_invariant ho hI _ fun n y => by rw [hinv]
  have act := (applyKernel_invariant ho ht hI hI' hs hT _ hbd hinv).2.2
    (fun c => periodicMatrix I'' I S s c (I''.mkQuot s z))
    (fun y => fS.matrix_entries s hs y z) x
  refine Eq.trans ?_ act.symm
  show ∑' n : Fin 4 → ℤ, ∑' y, T x y * S y (I''.translate (s • n) z) =
    ∑' y, T x y * ∑' n : Fin 4 → ℤ, S y (I''.translate (s • n) z)
  have hG : ∀ (m : Fin 4 → ℤ) y,
      ∑' n : Fin 4 → ℤ, ‖S (I.translate (s • m) y) (I''.translate (s • n) z)‖ =
        ∑' n : Fin 4 → ℤ, ‖S y (I''.translate (s • n) z)‖ := by
    intro m y
    rw [← (Equiv.addRight m).tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [Equiv.coe_addRight]
    rw [smul_add, hI''.translate_add, hS.1]
  obtain ⟨B, hB⟩ := exists_bound_of_invariant ho hI
    (fun y => ∑' n : Fin 4 → ℤ, ‖S y (I''.translate (s • n) z)‖) hG
  have hsum : Summable (Function.uncurry fun (y : I.Carrier) (n : Fin 4 → ℤ) =>
      T x y * S y (I''.translate (s • n) z)) := by
    refine Summable.of_norm ((summable_prod_of_nonneg fun _ => norm_nonneg _).mpr
      ⟨fun y => ?_, ?_⟩)
    · simp only [Function.uncurry, norm_mul]
      exact (fS.summable s hs y z).mul_left _
    · refine Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) (fun y => ?_)
        ((summable_norm_row ho ht hI hI' hs hT x).mul_right B)
      simp only [Function.uncurry, norm_mul]
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (hB y) (norm_nonneg _)
  simp only [← tsum_mul_left]
  exact hsum.tsum_comm
theorem claim_holds (ho : QuotOrbits.Claim)
    (hq : Quotients.QuotientTransposeNorm) (ht : Periodized.Claim)
    (hsym : Symbols.Claim) : Claim := by
  intro I I' hI hI' s hs T hT
  have hs' : 0 < s := hs
  have : Finite (I.QuotMod s) := (hq I I' hI hI' s hs').1.2.1
  refine ⟨fun f hb hf => applyKernel_invariant ho ht hI hI' hs' hT f hb hf, ?_⟩
  intro I'' hI'' S hS
  exact periodicMatrix_compKernel ho hsym ht hI hI' hI'' hs' hT hS
end YangMills.Construction.PeriodicOperators.TorusAction
end

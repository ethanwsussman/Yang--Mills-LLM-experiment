import YangMills.Construction.Lattice.BlocksInTheCoordinatesOfAFinerLatticeProof
import YangMills.Construction.PeriodicOperators.MatricesOnATorusInCoordinatesProof
import YangMills.Construction.Towers.IndexSetsArePeriodic
import YangMills.Construction.Towers.KernelsOfPeriodicLocalBilinearMapsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels.DescendingKernels
open Periodisation
open PeriodicOperators (PeriodicData IsPeriodic KernelMatrix applyKernel compKernel
  periodization castVec wTranspose)
open TorusMetric (supNormVec)
theorem abs_le_supNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ supNormVec v := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.abs_le_supNormVec <;> assumption
theorem supNormVec_le {v : Fin 4 → ℝ} {r : ℝ} (h : ∀ μ, |v μ| ≤ r) : supNormVec v ≤ r :=
  Finset.sup'_le _ _ fun μ _ => h μ
theorem supNormVec_sub_comm (a b : Fin 4 → ℝ) : supNormVec (a - b) = supNormVec (b - a) := by apply _root_.YangMills.Construction.LocalKernels.LocalBilinearKernels.supNormVec_sub_comm <;> assumption
theorem supNormVec_add_le (a b : Fin 4 → ℝ) :
    supNormVec (a + b) ≤ supNormVec a + supNormVec b :=
  supNormVec_le fun μ => (abs_add_le _ _).trans
    (add_le_add (abs_le_supNormVec a μ) (abs_le_supNormVec b μ))
theorem finite_intVec_ball (a : Fin 4 → ℝ) (r : ℝ) :
    {m : Fin 4 → ℤ | supNormVec (a + castVec m) ≤ r}.Finite := by
  refine (Set.Finite.pi (t := fun μ => Set.Icc ⌊-r - a μ⌋ ⌈r - a μ⌉)
    fun μ => Set.finite_Icc _ _).subset ?_
  intro m hm
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
  intro μ
  have h := (abs_le_supNormVec _ μ).trans (show _ ≤ r from hm)
  have h' := abs_le.mp h
  simp only [Pi.add_apply, castVec] at h'
  constructor
  · have : ((⌊-r - a μ⌋ : ℤ) : ℝ) ≤ (m μ : ℝ) := (Int.floor_le _).trans (by linarith [h'.1])
    exact_mod_cast this
  · have : (m μ : ℝ) ≤ ((⌈r - a μ⌉ : ℤ) : ℝ) := le_trans (by linarith [h'.2]) (Int.le_ceil _)
    exact_mod_cast this
section Periodic
variable {D : PeriodicData} (hD : IsPeriodic D)
include hD
theorem translate_neg_translate (a : Fin 4 → ℤ) (ι : D.Carrier) :
    D.translate (-a) (D.translate a ι) = ι := by
  rw [← hD.translate_add, add_neg_cancel, hD.translate_zero]
theorem exists_translate_of_mkQuot_eq (s : ℕ) {ι ι' : D.Carrier}
    (h : D.mkQuot s ι = D.mkQuot s ι') :
    ∃ m : Fin 4 → ℤ, ι' = D.translate (s • m) ι := by
  have key : ∀ a b, Relation.EqvGen
      (fun ι ι' : D.Carrier => ∃ n : Fin 4 → ℤ, ι' = D.translate (s • n) ι) a b →
      ∃ m : Fin 4 → ℤ, b = D.translate (s • m) a := by
    intro a b h
    induction h with
    | rel _ _ r => exact r
    | refl x => exact ⟨0, by rw [smul_zero, hD.translate_zero]⟩
    | symm x y _ ih =>
      obtain ⟨m, rfl⟩ := ih
      exact ⟨-m, by rw [smul_neg, translate_neg_translate hD]⟩
    | trans x y z _ _ ih₁ ih₂ =>
      obtain ⟨m, rfl⟩ := ih₁
      obtain ⟨m', rfl⟩ := ih₂
      exact ⟨m + m', by rw [smul_add, hD.translate_add]⟩
  exact key _ _ (Quot.eqvGen_exact h)
theorem finite_pos_ball (y : Fin 4 → ℝ) (r : ℝ) :
    {ι : D.Carrier | supNormVec (D.pos ι - y) ≤ r}.Finite := by
  have := hD.finite_quot
  choose rep hrep using fun c : D.UnitQuot => Quot.exists_rep c
  have hfin : (⋃ c : D.UnitQuot, (fun m => D.translate m (rep c)) ''
      {m : Fin 4 → ℤ | supNormVec ((D.pos (rep c) - y) + castVec m) ≤ r}).Finite :=
    Set.finite_iUnion fun c => (finite_intVec_ball _ r).image _
  refine hfin.subset fun ι hι => ?_
  obtain ⟨m, hm⟩ := exists_translate_of_mkQuot_eq hD 1 (hrep (D.mkQuot 1 ι))
  rw [one_smul] at hm
  refine Set.mem_iUnion.mpr ⟨D.mkQuot 1 ι, m, ?_, hm.symm⟩
  have hp : D.pos ι = D.pos (rep (D.mkQuot 1 ι)) + castVec m := by
    conv_lhs => rw [hm]
    exact hD.pos_translate _ _
  show supNormVec _ ≤ r
  have : D.pos (rep (D.mkQuot 1 ι)) - y + castVec m = D.pos ι - y := by
    rw [hp]; abel
  rw [this]
  exact hι
theorem translate_nsmul_injective {s : ℕ} (hs : 0 < s) (ι : D.Carrier) :
    Function.Injective fun m : Fin 4 → ℤ => D.translate (s • m) ι := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.translate_nsmul_injective <;> assumption
end Periodic
section Local
variable {D D' D'' : PeriodicData} {R : ℝ}
theorem support_row_finite (hD : IsPeriodic D) {T : D'.Carrier → D.Carrier → ℂ}
    (hT : IsLocalKernel D D' R T) (ι' : D'.Carrier) : (Function.support (T ι')).Finite :=
  (finite_pos_ball hD (D'.pos ι') R).subset fun ι h => by
    by_contra hc
    exact h (hT ι' ι hc)
theorem support_col_finite (hD' : IsPeriodic D') {T : D'.Carrier → D.Carrier → ℂ}
    (hT : IsLocalKernel D D' R T) (ι : D.Carrier) :
    (Function.support fun ι' => T ι' ι).Finite :=
  (finite_pos_ball hD' (D.pos ι) R).subset fun ι' h => by
    by_contra hc
    refine h (hT ι' ι fun hc' => hc ?_)
    show supNormVec _ ≤ R
    rw [supNormVec_sub_comm]
    exact hc'
end Local
section Actions
variable {J J' J'' : Type}
theorem summable_row_mul {T : J' → J → ℂ} (f : J → ℂ) {ι' : J'}
    (h : (Function.support (T ι')).Finite) : Summable fun ι => T ι' ι * f ι :=
  summable_of_hasFiniteSupport (h.subset fun ι hι => by
    intro h0
    exact hι (by simp [h0]))
theorem applyKernel_add {T T' : J' → J → ℂ} (hT : ∀ ι', (Function.support (T ι')).Finite)
    (hT' : ∀ ι', (Function.support (T' ι')).Finite) (f : J → ℂ) :
    applyKernel (T + T') f = applyKernel T f + applyKernel T' f := by
  funext ι'
  simp only [applyKernel, Pi.add_apply, add_mul]
  exact (summable_row_mul f (hT ι')).tsum_add (summable_row_mul f (hT' ι'))
theorem applyKernel_compKernel {T : J' → J → ℂ} {S : J → J'' → ℂ}
    (hT : ∀ ι', (Function.support (T ι')).Finite) (hS : ∀ ι, (Function.support (S ι)).Finite)
    (f : J'' → ℂ) : applyKernel (compKernel T S) f = applyKernel T (applyKernel S f) := by
  funext ι'
  simp only [applyKernel, compKernel]
  have hsum : Summable (Function.uncurry fun (c : J'') (b : J) => T ι' b * S b c * f c) := by
    refine summable_of_hasFiniteSupport
      ((((hT ι').biUnion fun b _ => hS b).prod (hT ι')).subset ?_)
    rintro ⟨c, b⟩ h
    have hb : T ι' b ≠ 0 := fun h0 => h (by simp [Function.uncurry, h0])
    have hc : S b c ≠ 0 := fun h0 => h (by simp [Function.uncurry, h0])
    exact ⟨Set.mem_biUnion (show b ∈ Function.support (T ι') from hb) hc, hb⟩
  calc ∑' c, (∑' b, T ι' b * S b c) * f c
      = ∑' c, ∑' b, T ι' b * S b c * f c := by
        refine tsum_congr fun c => ?_
        exact tsum_mul_right.symm
    _ = ∑' b, ∑' c, T ι' b * S b c * f c := hsum.tsum_comm.symm
    _ = ∑' b, T ι' b * ∑' c, S b c * f c := by
        refine tsum_congr fun b => ?_
        rw [← tsum_mul_left]
        exact tsum_congr fun c => mul_assoc _ _ _
end Actions
section Descent
variable {D D' : PeriodicData} {C C' : Type} {s : ℕ}
def IsOrbitFibration (D : PeriodicData) (s : ℕ) {C : Type} (q : D.Carrier → C) : Prop :=
  ∀ ι ι', q ι = q ι' ↔ ∃ m : Fin 4 → ℤ, ι' = D.translate (s • m) ι
theorem entry_eq_periodization (hD : IsPeriodic D) (hs : 0 < s) {q : D.Carrier → C}
    {q' : D'.Carrier → C'} (hq : IsOrbitFibration D s q) {T : D'.Carrier → D.Carrier → ℂ}
    {M : C' → C → ℂ} (hd : ∀ f : C → ℂ, applyKernel T (f ∘ q) = applyKernel M f ∘ q')
    (ι' : D'.Carrier) (ι : D.Carrier) : M (q' ι') (q ι) = periodization D D' T s ι' ι := by
  classical
  let f : C → ℂ := fun c => if c = q ι then 1 else 0
  have h := congrFun (hd f) ι'
  have hR : (applyKernel M f ∘ q') ι' = M (q' ι') (q ι) := by
    simp only [Function.comp, applyKernel]
    rw [tsum_eq_single (q ι) fun c hc => by simp [f, hc]]
    simp [f]
  rw [← hR, ← h]
  simp only [applyKernel, periodization]
  have hsupp : Function.support (fun x => T ι' x * (f ∘ q) x) ⊆
      Set.range fun m : Fin 4 → ℤ => D.translate (s • m) ι := by
    intro x hx
    by_contra hc
    apply hx
    have : q x ≠ q ι := fun e => hc (by
      obtain ⟨m, hm⟩ := (hq ι x).mp e.symm
      exact ⟨m, hm.symm⟩)
    simp [f, this]
  rw [← (translate_nsmul_injective hD hs ι).tsum_eq hsupp]
  refine tsum_congr fun m => ?_
  have hqm : q (D.translate (s • m) ι) = q ι := ((hq ι _).mpr ⟨m, rfl⟩).symm
  have hf : (f ∘ q) (D.translate (s • m) ι) = 1 := by
    simp only [Function.comp, f]
    rw [hqm]
    exact if_pos rfl
  show T ι' (D.translate (s • m) ι) * (f ∘ q) (D.translate (s • m) ι) =
    T ι' (D.translate (s • m) ι)
  rw [hf, mul_one]
theorem le_supNormVec_period {m : Fin 4 → ℤ} (hm : m ≠ 0) :
    (s : ℝ) ≤ supNormVec (castVec (s • m)) := by
  obtain ⟨μ, hμ⟩ := Function.ne_iff.mp hm
  refine le_trans ?_ (abs_le_supNormVec _ μ)
  have h1 : (1 : ℝ) ≤ |(m μ : ℝ)| := by
    have : (1 : ℤ) ≤ |m μ| := Int.one_le_abs hμ
    exact_mod_cast this
  simp only [castVec, Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, abs_mul,
    Nat.abs_cast]
  nlinarith [Nat.cast_nonneg (α := ℝ) s]
theorem periodization_of_near (hD : IsPeriodic D) {R : ℝ} (h2 : 2 * R < s)
    {T : D'.Carrier → D.Carrier → ℂ} (hT : IsLocalKernel D D' R T) {ι' : D'.Carrier}
    {ι : D.Carrier} (hn : supNormVec (D.pos ι - D'.pos ι') ≤ R) :
    periodization D D' T s ι' ι = T ι' ι := by
  simp only [periodization]
  rw [tsum_eq_single 0]
  · rw [smul_zero, hD.translate_zero]
  · intro m hm
    refine hT _ _ fun hc => ?_
    have hp := hD.pos_translate (s • m) ι
    have he : castVec (s • m) =
        (D.pos (D.translate (s • m) ι) - D'.pos ι') + (D'.pos ι' - D.pos ι) := by
      rw [hp]; abel
    have h3 := le_supNormVec_period (s := s) hm
    rw [he] at h3
    have h4 := supNormVec_add_le (D.pos (D.translate (s • m) ι) - D'.pos ι')
      (D'.pos ι' - D.pos ι)
    rw [supNormVec_sub_comm (D'.pos ι')] at h4
    linarith
theorem translate_invariant_of_descends (hD : IsPeriodic D) (hD' : IsPeriodic D')
    (hs : 0 < s) {R : ℝ} (h2 : 2 * R < s) {q : D.Carrier → C} {q' : D'.Carrier → C'}
    (hq : IsOrbitFibration D s q) (hq' : IsOrbitFibration D' s q')
    {T : D'.Carrier → D.Carrier → ℂ} {M : C' → C → ℂ} (hT : IsLocalKernel D D' R T)
    (hd : ∀ f : C → ℂ, applyKernel T (f ∘ q) = applyKernel M f ∘ q')
    (ι' : D'.Carrier) (ι : D.Carrier) (m : Fin 4 → ℤ) :
    T (D'.translate (s • m) ι') (D.translate (s • m) ι) = T ι' ι := by
  have hdiff : D.pos (D.translate (s • m) ι) - D'.pos (D'.translate (s • m) ι') =
      D.pos ι - D'.pos ι' := by
    rw [hD.pos_translate, hD'.pos_translate]; abel
  by_cases hn : supNormVec (D.pos ι - D'.pos ι') ≤ R
  · have e1 := entry_eq_periodization hD hs hq hd ι' ι
    have e2 := entry_eq_periodization hD hs hq hd (D'.translate (s • m) ι')
      (D.translate (s • m) ι)
    rw [periodization_of_near hD h2 hT hn] at e1
    rw [periodization_of_near hD h2 hT (by rw [hdiff]; exact hn)] at e2
    rw [← e1, ← e2, ← (hq ι _).mpr ⟨m, rfl⟩, ← (hq' ι' _).mpr ⟨m, rfl⟩]
  · rw [hT _ _ (by rw [hdiff]; exact hn), hT _ _ hn]
theorem tsum_eq_tsum_image_periods [Finite C'] (hD' : IsPeriodic D') (hs : 0 < s)
    {q' : D'.Carrier → C'} (hq' : IsOrbitFibration D' s q') {σ : C' → D'.Carrier}
    (hσ : ∀ c, q' (σ c) = c) {G : D'.Carrier → ℂ} (hG : (Function.support G).Finite) :
    ∑' x, G x = ∑' c, ∑' m : Fin 4 → ℤ, G (D'.translate (s • m) (σ c)) := by
  let e : C' × (Fin 4 → ℤ) → D'.Carrier := fun p => D'.translate (s • p.2) (σ p.1)
  have hqe : ∀ p, q' (e p) = p.1 := fun p => by
    rw [← (hq' (σ p.1) _).mpr ⟨p.2, rfl⟩, hσ]
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨c, m⟩ ⟨c', m'⟩ h
      have hc : c = c' := by simpa [hqe] using congrArg q' h
      subst hc
      have : m = m' := translate_nsmul_injective hD' hs (σ c) h
      rw [this]
    · intro x
      obtain ⟨m, hm⟩ := (hq' (σ (q' x)) x).mp (hσ _)
      exact ⟨(q' x, m), hm.symm⟩
  have hsum : Summable (G ∘ e) :=
    summable_of_hasFiniteSupport ((hG.preimage he.1.injOn).subset fun p hp => hp)
  rw [← (Equiv.ofBijective e he).tsum_eq G]
  exact hsum.tsum_prod
theorem wTranspose_descends [Finite C'] (hD : IsPeriodic D) (hD' : IsPeriodic D')
    (hs : 0 < s) {R : ℝ} (h2 : 2 * R < s) {q : D.Carrier → C} {q' : D'.Carrier → C'}
    (hq : IsOrbitFibration D s q) (hq' : IsOrbitFibration D' s q')
    (hsurj' : Function.Surjective q')
    {T : D'.Carrier → D.Carrier → ℂ} {M : C' → C → ℂ} (hT : IsLocalKernel D D' R T)
    (hd : ∀ f : C → ℂ, applyKernel T (f ∘ q) = applyKernel M f ∘ q')
    {w : D.Carrier → ℝ} {w' : D'.Carrier → ℝ} {v : C → ℝ} {v' : C' → ℝ}
    (hw : ∀ ι, w ι = v (q ι)) (hw' : ∀ ι', w' ι' = v' (q' ι')) (g : C' → ℂ) :
    applyKernel (wTranspose w w' T) (g ∘ q') = applyKernel (wTranspose v v' M) g ∘ q := by
  funext ι
  obtain ⟨σ, hσ⟩ := hsurj'.hasRightInverse
  have hG : (Function.support fun x => wTranspose w w' T ι x * g (q' x)).Finite :=
    (support_col_finite hD' hT ι).subset fun x hx h0 =>
      hx (by simp [wTranspose, show T x ι = 0 from h0])
  simp only [applyKernel, Function.comp]
  rw [tsum_eq_tsum_image_periods hD' hs hq' hσ hG]
  refine tsum_congr fun c => ?_
  have hcov : ∀ m : Fin 4 → ℤ, T (D'.translate (s • m) (σ c)) ι =
      T (σ c) (D.translate (s • -m) ι) := fun m => by
    have := translate_invariant_of_descends hD hD' hs h2 hq hq' hT hd
      (D'.translate (s • m) (σ c)) ι (-m)
    rw [smul_neg, translate_neg_translate hD'] at this
    rw [smul_neg]
    exact this.symm
  have hqm : ∀ m : Fin 4 → ℤ, q' (D'.translate (s • m) (σ c)) = c := fun m => by
    rw [← (hq' (σ c) _).mpr ⟨m, rfl⟩, hσ]
  have hterm : ∀ m : Fin 4 → ℤ,
      wTranspose w w' T ι (D'.translate (s • m) (σ c)) * g (q' (D'.translate (s • m) (σ c))) =
        ((v' c / v (q ι) : ℝ) : ℂ) * T (σ c) (D.translate (s • -m) ι) * g c := fun m => by
    simp only [wTranspose]
    rw [hw', hw, hqm, hcov]
  have hperiods : ∑' m : Fin 4 → ℤ, T (σ c) (D.translate (s • -m) ι) = M c (q ι) := by
    have hneg := (Equiv.neg (Fin 4 → ℤ)).tsum_eq fun m => T (σ c) (D.translate (s • m) ι)
    have := entry_eq_periodization hD hs hq hd (σ c) ι
    rw [hσ] at this
    exact hneg.trans this.symm
  simp only [hterm]
  rw [tsum_mul_right, tsum_mul_left, hperiods]
  rfl
end Descent
section Tower
variable {k : ℕ} {L n : ℕ}
theorem isOrbitFibration_proj (X : WeightedIndexSet k) (hX : IsPeriodic (X.toPeriodicData L))
    (hC : QuotientClassesPeriodic L n X) :
    IsOrbitFibration (X.toPeriodicData L) (periodSide L n) (X.proj L n) := by
  obtain ⟨-, ⟨φ, hφ, hcomm⟩, -⟩ := hC
  intro ι ι'
  constructor
  · intro h
    apply exists_translate_of_mkQuot_eq hX
    apply hφ.1
    rw [hcomm, hcomm, h]
  · rintro ⟨m, rfl⟩
    rw [← hcomm, ← hcomm]
    exact congrArg φ (Quot.sound ⟨m, rfl⟩)
theorem proj_surjective (X : WeightedIndexSet k) : Function.Surjective (X.proj L n) := by
  rintro ⟨p, _, y, rfl⟩
  exact ⟨(⟨p, y⟩ : Σ q, ((X.comp q).toPeriodicData L).Carrier), rfl⟩
theorem periodSide_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < periodSide L n := by
  have : 0 < L := by
    have := hL.2
    omega
  exact Nat.mul_pos two_pos (Nat.pow_pos this)
theorem applyKernel_comp_proj {X X' : WeightedIndexSet k}
    {T : KernelMatrix (Idx L X) (Idx L X')}
    {M : KernelMatrix (X.ImageCarrier L n) (X'.ImageCarrier L n)}
    (h : KernelDescends L n X X' T M) (f : X.ImageCarrier L n → ℂ) :
    applyKernel T (f ∘ X.proj L n) = applyKernel M f ∘ X'.proj L n :=
  h.2 f
end Tower
theorem descendingKernelAlgebra (hCells : PeriodicLiftCells.CellsAndClassesHold)
    (hPer : IndexSetPeriodicity.Statement) : DescendingKernelAlgebra := by
  intro L hL k n hn I I' I'' R hR T T' S M M' N hT hT' hS dT dT' dS
  have hs : 0 < periodSide L n := periodSide_pos hL
  have per : ∀ X : WeightedIndexSet k, IsPeriodic (X.toPeriodicData L) :=
    fun X => ((hPer L hL k).2 X).1
  have cl : ∀ X : WeightedIndexSet k, QuotientClassesPeriodic L n X := (hCells L hL k n hn).2
  have fib := fun X : WeightedIndexSet k => isOrbitFibration_proj X (per X) (cl X)
  have : Finite (I.ImageCarrier L n) := (cl I).1
  have : Finite (I'.ImageCarrier L n) := (cl I').1
  have : Finite (I''.ImageCarrier L n) := (cl I'').1
  have rT := support_row_finite (per I) hT
  have rT' := support_row_finite (per I) hT'
  have rS := support_row_finite (per I'') hS
  have rM : ∀ c, (Function.support (M c)).Finite := fun _ => Set.toFinite _
  have rM' : ∀ c, (Function.support (M' c)).Finite := fun _ => Set.toFinite _
  have rN : ∀ c, (Function.support (N c)).Finite := fun _ => Set.toFinite _
  have hsumLocal : IsRLocal L I I' R (T + T') := fun ι' ι h => by
    simp [hT ι' ι h, hT' ι' ι h]
  have hprodLocal : IsRLocal L I'' I' (2 * R) (compKernel T S) := by
    intro ι' ι'' h
    simp only [compKernel]
    refine (tsum_congr fun ι => ?_).trans tsum_zero
    by_cases h1 : supNormVec ((I.toPeriodicData L).pos ι - (I'.toPeriodicData L).pos ι') ≤ R
    · by_cases h2 : supNormVec ((I''.toPeriodicData L).pos ι'' - (I.toPeriodicData L).pos ι) ≤ R
      · exfalso
        apply h
        have he : (I''.toPeriodicData L).pos ι'' - (I'.toPeriodicData L).pos ι' =
            ((I''.toPeriodicData L).pos ι'' - (I.toPeriodicData L).pos ι) +
              ((I.toPeriodicData L).pos ι - (I'.toPeriodicData L).pos ι') := by abel
        rw [he]
        have := supNormVec_add_le ((I''.toPeriodicData L).pos ι'' - (I.toPeriodicData L).pos ι)
          ((I.toPeriodicData L).pos ι - (I'.toPeriodicData L).pos ι')
        linarith
      · rw [hS ι ι'' h2, mul_zero]
    · rw [hT ι' ι h1, zero_mul]
  refine ⟨⟨fun ι' ι => entry_eq_periodization (per I) hs (fib I) (applyKernel_comp_proj dT) ι' ι,
      fun M₂ h₂ => ?_⟩, hsumLocal, ⟨⟨R, hR, hsumLocal⟩, fun f => ?_⟩, hprodLocal,
      ⟨⟨2 * R, by positivity, hprodLocal⟩, fun f => ?_⟩, fun h2 => ?_⟩
  · funext κ' κ
    obtain ⟨ι', rfl⟩ := proj_surjective I' κ'
    obtain ⟨ι, rfl⟩ := proj_surjective I κ
    rw [entry_eq_periodization (per I) hs (fib I) (applyKernel_comp_proj h₂) ι' ι,
      entry_eq_periodization (per I) hs (fib I) (applyKernel_comp_proj dT) ι' ι]
  · rw [applyKernel_add rT rT', applyKernel_add rM rM', dT.2 f, dT'.2 f]
    rfl
  · rw [applyKernel_compKernel rT rS, dS.2 f, dT.2, applyKernel_compKernel rM rN]
  · refine ⟨fun ι' ι m => translate_invariant_of_descends (per I) (per I') hs h2 (fib I)
        (fib I') hT (applyKernel_comp_proj dT) ι' ι m, ?_, ⟨⟨R, hR, ?_⟩, fun g => ?_⟩⟩
    · intro ι ι' h
      have h0 : T ι' ι = 0 := hT ι' ι fun hc => h (by
        show supNormVec _ ≤ R
        rw [supNormVec_sub_comm]
        exact hc)
      simp [kernelT, wTranspose, h0]
    · intro ι ι' h
      have h0 : T ι' ι = 0 := hT ι' ι fun hc => h (by
        show supNormVec _ ≤ R
        rw [supNormVec_sub_comm]
        exact hc)
      simp [kernelT, wTranspose, h0]
    · exact wTranspose_descends (per I) (per I') hs h2 (fib I) (fib I') (proj_surjective I') hT
        (applyKernel_comp_proj dT) (v := I.imageWeight L n) (v' := I'.imageWeight L n)
        (fun _ => rfl) (fun _ => rfl) g
end YangMills.Construction.LocalKernels.DescendingKernels
end

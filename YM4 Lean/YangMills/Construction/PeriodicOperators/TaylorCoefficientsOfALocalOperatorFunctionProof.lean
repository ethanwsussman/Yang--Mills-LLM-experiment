import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.PeriodicOperators.NumbersOfALocalOperatorFunctionProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology Asymptotics
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LocalOpFunTaylor
open TorusMetric (euclidNormVec)
open Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
section Generalities
variable {F : PeriodicData}
open Classical in
def deltaField (a : F.Carrier) : F.Carrier → ℂ := fun b => if b = a then 1 else 0
theorem isSupBelow_zero {r : ℝ} (hr : 0 < r) : IsSupBelow F 0 r :=
  ⟨0, hr, fun b => by simp⟩
theorem fieldExtend_apply {S : Set F.Carrier} {m : ℕ} (e : Fin m ≃ S)
    (z : Coordinates.ComplexCoordinates m) (i : Fin m) :
    fieldExtend e z ((e i : S) : F.Carrier) = z i := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.fieldExtend_apply <;> assumption
theorem fieldExtend_of_not_mem_range {S : Set F.Carrier} {m : ℕ} (e : Fin m ≃ S)
    (z : Coordinates.ComplexCoordinates m) (x : F.Carrier)
    (hx : ¬ ∃ i, ((e i : S) : F.Carrier) = x) : fieldExtend e z x = 0 :=
  Function.extend_apply' z (0 : F.Carrier → ℂ) x hx
theorem eventually_isSupBelow {S : Set F.Carrier} {m : ℕ} (e : Fin m ≃ S) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ z in 𝓝 (0 : Coordinates.ComplexCoordinates m), IsSupBelow F (fieldExtend e z) r := by
  filter_upwards [Metric.ball_mem_nhds (0 : Coordinates.ComplexCoordinates m) (half_pos hr)] with z hz
  refine ⟨r / 2, half_lt_self hr, fun b => ?_⟩
  by_cases hb : ∃ i, ((e i : S) : F.Carrier) = b
  · obtain ⟨i, rfl⟩ := hb
    rw [fieldExtend_apply]
    have hz' : ‖z‖ < r / 2 := by simpa using hz
    exact (norm_le_pi_norm z i).trans hz'.le
  · rw [fieldExtend_of_not_mem_range e z b hb, norm_zero]
    exact (half_pos hr).le
theorem isSecondOrderExpansion_congr {m : ℕ} {f g : Coordinates.ComplexCoordinates m → ℂ}
    {L : Coordinates.ComplexCoordinates m →ₗ[ℂ] ℂ}
    {B : Coordinates.ComplexCoordinates m →ₗ[ℂ] Coordinates.ComplexCoordinates m →ₗ[ℂ] ℂ}
    (hfg : f =ᶠ[𝓝 0] g) (hf : IsSecondOrderExpansion f L B) : IsSecondOrderExpansion g L B := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.secondOrder_congr <;> assumption
theorem isSecondOrderExpansion_zero {m : ℕ} :
    IsSecondOrderExpansion (fun _ : Coordinates.ComplexCoordinates m => (0 : ℂ)) 0 0 := by
  refine ⟨fun z w => rfl, (isBigO_zero _ _).congr_left fun z => ?_⟩
  simp
theorem finsum_eq_sum_equiv {α : Type} {m : ℕ} (e : Fin m ≃ α) (g : α → ℂ) :
    ∑ᶠ a, g a = ∑ i, g (e i) := by
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
theorem eq_sum_single {m : ℕ} (z : Coordinates.ComplexCoordinates m) :
    z = ∑ i, z i • (Pi.single i 1 : Coordinates.ComplexCoordinates m) := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.eq_sum_stdBasisVector <;> assumption
theorem linear_eq_sum {m : ℕ} (L : Coordinates.ComplexCoordinates m →ₗ[ℂ] ℂ)
    (z : Coordinates.ComplexCoordinates m) :
    L z = ∑ i, L (Pi.single i 1) * z i := by
  conv_lhs => rw [eq_sum_single z]
  simp [map_sum, mul_comm]
theorem bilinear_eq_sum {m : ℕ}
    (B : Coordinates.ComplexCoordinates m →ₗ[ℂ] Coordinates.ComplexCoordinates m →ₗ[ℂ] ℂ)
    (z w : Coordinates.ComplexCoordinates m) :
    B z w = ∑ i, ∑ k, B (Pi.single i 1) (Pi.single k 1) * z i * w k := by
  have hcol : ∀ k, B z (Pi.single k 1) = ∑ i, B (Pi.single i 1) (Pi.single k 1) * z i :=
    fun k => linear_eq_sum (B.flip (Pi.single k 1)) z
  rw [linear_eq_sum (B z) w, Finset.sum_comm]
  simp_rw [hcol, Finset.sum_mul]
theorem translate_neg_translate {F : PeriodicData} (hF : IsPeriodic F) (n : Fin 4 → ℤ)
    (a : F.Carrier) : F.translate (-n) (F.translate n a) = a := by
  rw [← hF.translate_add, add_neg_cancel, hF.translate_zero]
theorem translate_translate_neg {F : PeriodicData} (hF : IsPeriodic F) (n : Fin 4 → ℤ)
    (a : F.Carrier) : F.translate n (F.translate (-n) a) = a := by
  rw [← hF.translate_add, neg_add_cancel, hF.translate_zero]
theorem fieldExtend_translate (hF : IsPeriodic F) (n : Fin 4 → ℤ) {S S' : Set F.Carrier}
    {m : ℕ} (e : Fin m ≃ S) (e' : Fin m ≃ S')
    (he : ∀ i, ((e' i : S') : F.Carrier) = F.translate n (e i : S))
    (z : Coordinates.ComplexCoordinates m) :
    fieldExtend e' z = shiftField F n (fieldExtend e z) := by
  funext x
  by_cases hx : ∃ i, ((e i : S) : F.Carrier) = F.translate (-n) x
  · obtain ⟨i, hi⟩ := hx
    have hxi : x = ((e' i : S') : F.Carrier) := by rw [he i, hi, translate_translate_neg hF]
    rw [shiftField, ← hi, fieldExtend_apply, hxi, fieldExtend_apply]
  · rw [shiftField, fieldExtend_of_not_mem_range e z _ hx, fieldExtend_of_not_mem_range e' z x]
    rintro ⟨i, hi⟩
    apply hx
    refine ⟨i, ?_⟩
    rw [← hi, he i, translate_neg_translate hF]
theorem fieldValues_shiftField (hF : IsPeriodic F) (n : Fin 4 → ℤ) {S S' : Set F.Carrier}
    {m : ℕ} (e : Fin m ≃ S) (e' : Fin m ≃ S')
    (he : ∀ i, ((e' i : S') : F.Carrier) = F.translate n (e i : S)) (u : F.Carrier → ℂ) :
    fieldValues e' (shiftField F n u) = fieldValues e u := by
  funext i
  simp only [fieldValues, shiftField, he i, translate_neg_translate hF]
theorem shiftField_deltaField (hF : IsPeriodic F) (n : Fin 4 → ℤ) (a : F.Carrier) :
    shiftField F n (deltaField a) = deltaField (F.translate n a) := by
  funext x
  have hiff : F.translate (-n) x = a ↔ x = F.translate n a := by
    constructor
    · rintro rfl
      rw [translate_translate_neg hF]
    · rintro rfl
      exact translate_neg_translate hF n a
  simp only [shiftField, deltaField]
  by_cases hx : x = F.translate n a
  · rw [if_pos hx, if_pos (hiff.mpr hx)]
  · rw [if_neg hx, if_neg fun h => hx (hiff.mp h)]
end Generalities
section Membership
variable {F J : PeriodicData}
theorem translate_mem_nearIndices (hF : IsPeriodic F) (hJ : IsPeriodic J) (n : Fin 4 → ℤ)
    {q : J.Carrier} {R : ℝ} {a : F.Carrier} (h : a ∈ nearIndices F (J.pos q) R) :
    F.translate n a ∈ nearIndices F (J.pos (J.translate n q)) R := by
  have hd : F.pos (F.translate n a) - J.pos (J.translate n q) = F.pos a - J.pos q := by
    rw [hF.pos_translate, hJ.pos_translate, add_sub_add_right_eq_sub]
  have h' : euclidNormVec (F.pos a - J.pos q) ≤ R := h
  change euclidNormVec (F.pos (F.translate n a) - J.pos (J.translate n q)) ≤ R
  rw [hd]
  exact h'
def nearIndicesTranslate (hF : IsPeriodic F) (hJ : IsPeriodic J) (n : Fin 4 → ℤ)
    (q : J.Carrier) (R : ℝ) :
    nearIndices F (J.pos q) R ≃ nearIndices F (J.pos (J.translate n q)) R where
  toFun a := ⟨F.translate n a, translate_mem_nearIndices hF hJ n a.2⟩
  invFun a := ⟨F.translate (-n) a, by
    have h := translate_mem_nearIndices hF hJ (-n) a.2
    rwa [translate_neg_translate hJ] at h⟩
  left_inv a := Subtype.ext (translate_neg_translate hF n a)
  right_inv a := Subtype.ext (translate_translate_neg hF n a)
end Membership
section Coefficients
variable {F I J : PeriodicData} {T : (F.Carrier → ℂ) → J.Carrier → I.Carrier → ℂ} {r R : ℝ}
theorem isLinearCoeffFamily_eq {q : J.Carrier} {p : I.Carrier}
    {t : nearIndices F (J.pos q) R → ℂ} (ht : IsLinearCoeffFamily F I J T R q p t)
    (a : nearIndices F (J.pos q) R) :
    t a = coeffOne F I J T (deltaField (a : F.Carrier)) q p := by
  have hoff : ∀ b : nearIndices F (J.pos q) R, b ≠ a →
      t b * deltaField (a : F.Carrier) b = 0 := by
    intro b hb
    have hne : (b : F.Carrier) ≠ a := fun h => hb (Subtype.ext h)
    simp [deltaField, hne]
  rw [ht, finsum_eq_single _ a hoff]
  simp [deltaField]
theorem isQuadraticCoeffFamily_eq {q : J.Carrier} {p : I.Carrier}
    {t₂ : nearIndices F (J.pos q) R → nearIndices F (J.pos q) R → ℂ}
    (ht : IsQuadraticCoeffFamily F I J T R q p t₂) (a c : nearIndices F (J.pos q) R) :
    t₂ a c = coeffTwo F I J T (deltaField (a : F.Carrier))
      (deltaField (c : F.Carrier)) q p := by
  have hoff : ∀ b : nearIndices F (J.pos q) R, b ≠ a →
      (∑ᶠ b' : nearIndices F (J.pos q) R,
        t₂ b b' * deltaField (a : F.Carrier) b * deltaField (c : F.Carrier) b') = 0 := by
    intro b hb
    have hne : (b : F.Carrier) ≠ a := fun h => hb (Subtype.ext h)
    simp [deltaField, hne]
  have hoff' : ∀ b' : nearIndices F (J.pos q) R, b' ≠ c →
      t₂ a b' * deltaField (a : F.Carrier) a * deltaField (c : F.Carrier) b' = 0 := by
    intro b' hb'
    have hne : (b' : F.Carrier) ≠ c := fun h => hb' (Subtype.ext h)
    simp [deltaField, hne]
  rw [ht.2, finsum_eq_single _ a hoff, finsum_eq_single _ c hoff']
  simp [deltaField]
variable (hN : ParameterIndependence.Claim) (hF : IsPeriodic F)
  (hI : IsPeriodic I) (hJ : IsPeriodic J)
  (hT : IsLocalWith F I J T r R)
include hN hF hI hJ hT
theorem linear_form_eq {q : J.Carrier} {p : I.Carrier} {m : ℕ}
    {e : Fin m ≃ nearIndices F (J.pos q) R} {L : Coordinates.ComplexCoordinates m →ₗ[ℂ] ℂ}
    {B : Coordinates.ComplexCoordinates m →ₗ[ℂ] Coordinates.ComplexCoordinates m →ₗ[ℂ] ℂ}
    (hx : IsSecondOrderExpansion (entryFun T q p e) L B) (u : F.Carrier → ℂ) :
    L (fieldValues e u) = coeffOne F I J T u q p :=
  ((hN F I J hF hI hJ T r R r R hT hT).2.1.1 u u q p).1.2.2 r R hT m e L B hx
theorem bilinear_form_eq {q : J.Carrier} {p : I.Carrier} {m : ℕ}
    {e : Fin m ≃ nearIndices F (J.pos q) R} {L : Coordinates.ComplexCoordinates m →ₗ[ℂ] ℂ}
    {B : Coordinates.ComplexCoordinates m →ₗ[ℂ] Coordinates.ComplexCoordinates m →ₗ[ℂ] ℂ}
    (hx : IsSecondOrderExpansion (entryFun T q p e) L B) (u v : F.Carrier → ℂ) :
    B (fieldValues e u) (fieldValues e v) = coeffTwo F I J T u v q p :=
  ((hN F I J hF hI hJ T r R r R hT hT).2.1.1 u v q p).2.2.2 r R hT m e L B hx
theorem exists_expansion (q : J.Carrier) (p : I.Carrier) :
    ∃ (m : ℕ) (e : Fin m ≃ nearIndices F (J.pos q) R)
      (L : Coordinates.ComplexCoordinates m →ₗ[ℂ] ℂ)
      (B : Coordinates.ComplexCoordinates m →ₗ[ℂ] Coordinates.ComplexCoordinates m →ₗ[ℂ] ℂ),
      IsSecondOrderExpansion (entryFun T q p e) L B := by
  obtain ⟨-, m, e, L, B, hx, -⟩ :=
    (((hN F I J hF hI hJ T r R r R hT hT).2.1.1 0 0 q p).1.1 _).mpr rfl
  exact ⟨m, e, L, B, hx⟩
theorem exists_linearCoeffFamily (q : J.Carrier) (p : I.Carrier) :
    ∃ t, IsLinearCoeffFamily F I J T R q p t := by
  obtain ⟨m, e, L, B, hx⟩ := exists_expansion hN hF hI hJ hT q p
  refine ⟨fun a => L (Pi.single (e.symm a) 1), fun u => ?_⟩
  rw [← linear_form_eq hN hF hI hJ hT hx u, finsum_eq_sum_equiv e, linear_eq_sum L]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [fieldValues]
theorem exists_quadraticCoeffFamily (q : J.Carrier) (p : I.Carrier) :
    ∃ t₂, IsQuadraticCoeffFamily F I J T R q p t₂ := by
  obtain ⟨m, e, L, B, hx⟩ := exists_expansion hN hF hI hJ hT q p
  refine ⟨fun a c => B (Pi.single (e.symm a) 1) (Pi.single (e.symm c) 1),
    ⟨fun a c => hx.1 _ _, fun u v => ?_⟩⟩
  rw [← bilinear_form_eq hN hF hI hJ hT hx u v, finsum_eq_sum_equiv e, bilinear_eq_sum B]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsum_eq_sum_equiv e]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [fieldValues]
theorem linearCoeffFamily_spec (q : J.Carrier) (p : I.Carrier) :
    IsLinearCoeffFamily F I J T R q p (linearCoeffFamily F I J T R q p) :=
  Classical.epsilon_spec (exists_linearCoeffFamily hN hF hI hJ hT q p)
theorem quadraticCoeffFamily_spec (q : J.Carrier) (p : I.Carrier) :
    IsQuadraticCoeffFamily F I J T R q p (quadraticCoeffFamily F I J T R q p) :=
  Classical.epsilon_spec (exists_quadraticCoeffFamily hN hF hI hJ hT q p)
theorem coeff_eq_zero_of_far {q : J.Carrier} {p : I.Carrier}
    (hd : ¬ euclidNormVec (I.pos p - J.pos q) ≤ R) (u v : F.Carrier → ℂ) :
    coeffZero F I J T q p = 0 ∧ coeffOne F I J T u q p = 0 ∧
      coeffTwo F I J T u v q p = 0 := by
  obtain ⟨m, e, -, -, -⟩ := exists_expansion hN hF hI hJ hT q p
  have hzero : IsSecondOrderExpansion (entryFun T q p e) 0 0 := by
    refine isSecondOrderExpansion_congr ?_ isSecondOrderExpansion_zero
    filter_upwards [eventually_isSupBelow e hT.radius_pos] with z hz
    exact (hT.vanish_far _ hz q p hd).symm
  refine ⟨hT.vanish_far 0 (isSupBelow_zero hT.radius_pos) q p hd, ?_, ?_⟩
  · exact (linear_form_eq hN hF hI hJ hT hzero u).symm
  · exact (bilinear_form_eq hN hF hI hJ hT hzero u v).symm
theorem coeff_shift_covariant (u v : F.Carrier → ℂ) (q : J.Carrier) (p : I.Carrier)
    (n : Fin 4 → ℤ) :
    coeffOne F I J T (shiftField F n u) (J.translate n q) (I.translate n p) =
        coeffOne F I J T u q p ∧
      coeffTwo F I J T (shiftField F n u) (shiftField F n v)
          (J.translate n q) (I.translate n p) =
        coeffTwo F I J T u v q p := by
  obtain ⟨m, e, L, B, hx⟩ := exists_expansion hN hF hI hJ hT q p
  let e' : Fin m ≃ nearIndices F (J.pos (J.translate n q)) R :=
    e.trans (nearIndicesTranslate hF hJ n q R)
  have he : ∀ i, ((e' i : nearIndices F (J.pos (J.translate n q)) R) : F.Carrier) =
      F.translate n (e i : nearIndices F (J.pos q) R) := fun i => rfl
  have hx' : IsSecondOrderExpansion (entryFun T (J.translate n q) (I.translate n p) e') L B := by
    refine isSecondOrderExpansion_congr ?_ hx
    filter_upwards [eventually_isSupBelow e hT.radius_pos] with z hz
    simp only [entryFun]
    rw [fieldExtend_translate hF n e e' he z, hT.shift_covariant _ hz n q p]
  constructor
  · rw [← linear_form_eq hN hF hI hJ hT hx u, ← linear_form_eq hN hF hI hJ hT hx',
      fieldValues_shiftField hF n e e' he]
  · rw [← bilinear_form_eq hN hF hI hJ hT hx u v, ← bilinear_form_eq hN hF hI hJ hT hx',
      fieldValues_shiftField hF n e e' he, fieldValues_shiftField hF n e e' he]
end Coefficients
section Torus
variable {I J : PeriodicData}
theorem periodSumFinite_of_vanish (hK : CovariantFiniteRange.Claim)
    (hI : IsPeriodic I) {R : ℝ} {Y : J.Carrier → I.Carrier → ℂ} {s : ℕ} (hs : 0 < s)
    (q : J.Carrier) (p : I.Carrier)
    (hY : ∀ p₂, ¬ euclidNormVec (I.pos p₂ - J.pos q) ≤ R → Y q p₂ = 0) :
    PeriodSumFinite I J Y s q p := by
  have hfin : (nearIndices I (J.pos q) R).Finite := (hK.1 I hI).1 _ _
  have hinj : Function.Injective fun n : Fin 4 → ℤ => I.translate (s • n) p := by
    intro n k hnk
    have hpos := congrArg I.pos hnk
    simp only [hI.pos_translate] at hpos
    have hreal := add_left_cancel hpos
    funext μ
    have hμ := congrFun hreal μ
    simp only [castVec, Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast] at hμ
    have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    exact_mod_cast mul_left_cancel₀ hs' hμ
  refine (hfin.preimage hinj.injOn).subset fun n hn => ?_
  by_contra hnot
  exact hn (hY _ hnot)
end Torus
theorem claim_holds (hN : ParameterIndependence.Claim)
    (hK : CovariantFiniteRange.Claim) : Claim := by
  intro F I J hF hI hJ T r R hT u v q p n
  have hlin := linearCoeffFamily_spec hN hF hI hJ hT
  have hquad := quadraticCoeffFamily_spec hN hF hI hJ hT
  have hvanish := fun {q : J.Carrier} {p : I.Carrier} hd =>
    coeff_eq_zero_of_far hN hF hI hJ hT (q := q) (p := p) hd
  have hcov := coeff_shift_covariant hN hF hI hJ hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨m, e, -, -, -⟩ := exists_expansion hN hF hI hJ hT q p
    have : Finite (nearIndices F (J.pos q) R) := Finite.of_equiv _ e
    refine ⟨Set.toFinite _, ⟨_, hlin q p, fun t ht => ?_⟩, hlin q p,
      ⟨_, hquad q p, fun t₂ ht => ?_⟩, hquad q p⟩
    · funext a
      rw [isLinearCoeffFamily_eq ht a, isLinearCoeffFamily_eq (hlin q p) a]
    · funext a c
      rw [isQuadraticCoeffFamily_eq ht a c, isQuadraticCoeffFamily_eq (hquad q p) a c]
  · refine ⟨fun hR => ?_, fun hd => hvanish hd u v⟩
    have hd := not_le.mpr hR
    refine ⟨(hvanish hd 0 0).1, fun a => ?_, fun a c => ?_⟩
    · rw [isLinearCoeffFamily_eq (hlin q p) a]
      exact (hvanish hd _ 0).2.1
    · rw [isQuadraticCoeffFamily_eq (hquad q p) a c]
      exact (hvanish hd _ _).2.2
  · refine ⟨?_, fun a => ?_, fun a c => ?_, (hcov u v q p n).1, (hcov u v q p n).2⟩
    · have hzero : shiftField F n (0 : F.Carrier → ℂ) = 0 := rfl
      have h := hT.shift_covariant 0 (isSupBelow_zero hT.radius_pos) n q p
      rw [hzero] at h
      exact h
    · refine ⟨translate_mem_nearIndices hF hJ n a.2, ?_⟩
      rw [isLinearCoeffFamily_eq (hlin _ _), isLinearCoeffFamily_eq (hlin q p) a]
      simp only []
      rw [← shiftField_deltaField hF n]
      exact (hcov _ 0 q p n).1
    · refine ⟨translate_mem_nearIndices hF hJ n a.2, translate_mem_nearIndices hF hJ n c.2, ?_⟩
      rw [isQuadraticCoeffFamily_eq (hquad _ _), isQuadraticCoeffFamily_eq (hquad q p) a c]
      simp only []
      rw [← shiftField_deltaField hF n, ← shiftField_deltaField hF n]
      exact (hcov _ _ q p n).2
  · rintro s hs Y (rfl | rfl | rfl)
    · exact periodSumFinite_of_vanish hK hI hs q p fun p₂ hd => (hvanish hd 0 0).1
    · exact periodSumFinite_of_vanish hK hI hs q p fun p₂ hd => (hvanish hd u 0).2.1
    · exact periodSumFinite_of_vanish hK hI hs q p fun p₂ hd => (hvanish hd u v).2.2
end YangMills.Construction.PeriodicOperators.LocalOpFunTaylor
end

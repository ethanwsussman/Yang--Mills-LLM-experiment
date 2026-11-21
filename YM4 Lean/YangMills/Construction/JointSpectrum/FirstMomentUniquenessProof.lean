import YangMills.Construction.EuclideanSpectral.FunctionalCalculusTransport
import YangMills.Construction.JointSpectrum.BorelFunctionalCalculus
import YangMills.Construction.JointSpectrum.FirstMomentUniqueness
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.JointSpectrum.FirstMoments
open YangMills.Construction.JointSpectrum YangMills.Construction.JointSpectrum.SpectralIntegral YangMills.Construction.FamilyPolynomials YangMills.Construction.JointSpectrum.BorelCalculus
variable {𝒦 : Type*} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
  {J : Type*} [Fintype J] [Nonempty J]
private lemma ext_of_inner_self {C D : 𝒦 →L[ℂ] 𝒦} (h : ∀ ψ, inner ℂ ψ (C ψ) = inner ℂ ψ (D ψ)) :
    C = D := by apply _root_.YangMills.Construction.EuclideanSpectral.FunctionalCalculus.ext_inner_self <;> assumption
private lemma tendsto_inner_of_tendsto_inner_self {C : ℕ → 𝒦 →L[ℂ] 𝒦} {X : 𝒦 →L[ℂ] 𝒦}
    (h : ∀ v, Tendsto (fun l => inner ℂ v (C l v)) atTop (𝓝 (inner ℂ v (X v)))) (x y : 𝒦) :
    Tendsto (fun l => inner ℂ x (C l y)) atTop (𝓝 (inner ℂ x (X y))) := by
  have hc : ∀ v, Tendsto (fun l => inner ℂ (C l v) v) atTop (𝓝 (inner ℂ (X v) v)) := fun v => by
    have := (Complex.continuous_conj.tendsto _).comp (h v)
    simpa [Function.comp_def, inner_conj_symm] using this
  have e : ∀ T : 𝒦 →L[ℂ] 𝒦, inner ℂ (T y) x =
      (inner ℂ (T (x + y)) (x + y) - inner ℂ (T (x - y)) (x - y) +
        Complex.I * inner ℂ (T (x + Complex.I • y)) (x + Complex.I • y) -
        Complex.I * inner ℂ (T (x - Complex.I • y)) (x - Complex.I • y)) / 4 :=
    fun T => inner_map_polarization (T : 𝒦 →ₗ[ℂ] 𝒦) x y
  have key : Tendsto (fun l => inner ℂ (C l y) x) atTop (𝓝 (inner ℂ (X y) x)) := by
    simp only [e]
    exact ((((hc _).sub (hc _)).add ((hc _).const_mul _)).sub ((hc _).const_mul _)).div_const _
  have := (Complex.continuous_conj.tendsto _).comp key
  simpa [Function.comp_def, inner_conj_symm] using this
private lemma measure_ext_real {μ ν : Measure (SpectralDomain J)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ∀ T, MeasurableSet T → μ.real T = ν.real T) : μ = ν := by
  ext T hT
  have := h T hT
  rwa [Measure.real, Measure.real, ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (measure_ne_top _ _)] at this
private lemma integrable_of_norm_le {f : SpectralDomain J → ℂ} (hf : Measurable f) {c : ℝ}
    (hc : ∀ p, ‖f p‖ ≤ c) (μ : Measure (SpectralDomain J)) [IsFiniteMeasure μ] :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable c (ae_of_all _ hc)
section Projections
variable (P : ProjectionValuedMeasure J 𝒦)
private def diagonalMeasure (ψ : 𝒦) : Measure (SpectralDomain J) :=
  Classical.choose (P.exists_scalarMeasure ψ)
private instance (ψ : 𝒦) : IsFiniteMeasure (diagonalMeasure P ψ) :=
  (Classical.choose_spec (P.exists_scalarMeasure ψ)).1
private lemma inner_E_self (ψ : 𝒦) (T : {T : Set (SpectralDomain J) // MeasurableSet T}) :
    inner ℂ ψ (P.E T ψ) = (((diagonalMeasure P ψ).real T.1 : ℝ) : ℂ) :=
  (Classical.choose_spec (P.exists_scalarMeasure ψ)).2 T
private lemma isDiagonalMeasure_diagonalMeasure (ψ : 𝒦) :
    IsDiagonalMeasure P ψ (diagonalMeasure P ψ) :=
  ⟨inferInstance, inner_E_self P ψ⟩
private lemma inner_E_left (T : {T : Set (SpectralDomain J) // MeasurableSet T}) (x y : 𝒦) :
    inner ℂ (P.E T x) y = inner ℂ x (P.E T y) :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (P.isStarProjection T).isSelfAdjoint) x y
private lemma E_mul_self (T : {T : Set (SpectralDomain J) // MeasurableSet T}) :
    P.E T * P.E T = P.E T :=
  (P.isStarProjection T).isIdempotentElem
private lemma E_union {T T' : Set (SpectralDomain J)} (hT : MeasurableSet T)
    (hT' : MeasurableSet T') (hd : Disjoint T T') :
    P.E ⟨T ∪ T', hT.union hT'⟩ = P.E ⟨T, hT⟩ + P.E ⟨T', hT'⟩ := by
  refine ext_of_inner_self fun ψ => ?_
  rw [add_apply, inner_add_right, inner_E_self, inner_E_self, inner_E_self]
  simp only [Measure.real]
  rw [measure_union hd hT', ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  push_cast
  rfl
private lemma E_mul_of_disjoint {T T' : Set (SpectralDomain J)} (hT : MeasurableSet T)
    (hT' : MeasurableSet T') (hd : Disjoint T T') :
    P.E ⟨T, hT⟩ * P.E ⟨T', hT'⟩ = 0 := by
  set a := P.E ⟨T, hT⟩ with ha
  set b := P.E ⟨T', hT'⟩ with hb
  have haa : a * a = a := E_mul_self P _
  have hbb : b * b = b := E_mul_self P _
  have hs : (a + b) * (a + b) = a + b := by
    rw [ha, hb, ← E_union P hT hT' hd]
    exact E_mul_self P _
  have h1 : a * b + b * a = 0 := by
    have : a * a + a * b + (b * a + b * b) = a + b := by
      rw [← hs]; noncomm_ring
    rw [haa, hbb] at this
    have h2 : a + a * b + (b * a + b) - (a + b) = a * b + b * a := by abel
    rw [← h2, this, sub_self]
  have h2 : a * b = b * a := by
    have e1 : a * (a * b + b * a) = a * b + a * b * a := by
      rw [mul_add, ← mul_assoc, haa, mul_assoc]
    have e2 : (a * b + b * a) * a = a * b * a + b * a := by
      rw [add_mul, mul_assoc b, haa]
    rw [h1, mul_zero] at e1
    rw [h1, zero_mul] at e2
    have := e1.symm.trans e2
    exact add_left_cancel (add_comm (a * b) (a * b * a) ▸ this)
  rw [← h2] at h1
  have h3 : (2 : ℂ) • (a * b) = 0 := by rw [two_smul, h1]
  exact (smul_eq_zero.1 h3).resolve_left two_ne_zero
private lemma E_mul_eq_inter {T T' : Set (SpectralDomain J)} (hT : MeasurableSet T)
    (hT' : MeasurableSet T') :
    P.E ⟨T, hT⟩ * P.E ⟨T', hT'⟩ = P.E ⟨T ∩ T', hT.inter hT'⟩ := by
  have h0 := hT.inter hT'
  have h1 := hT.diff hT'
  have h2 := hT'.diff hT
  have e1 : P.E ⟨T, hT⟩ = P.E ⟨T ∩ T', h0⟩ + P.E ⟨T \ T', h1⟩ := by
    rw [← E_union P h0 h1 (by
      rw [Set.disjoint_left]; rintro x ⟨_, hx⟩ ⟨_, hx'⟩; exact hx' hx)]
    exact congrArg P.E (Subtype.ext (Set.inter_union_sdiff T T').symm)
  have e2 : P.E ⟨T', hT'⟩ = P.E ⟨T ∩ T', h0⟩ + P.E ⟨T' \ T, h2⟩ := by
    rw [← E_union P h0 h2 (by
      rw [Set.disjoint_left]; rintro x ⟨hx, _⟩ ⟨_, hx'⟩; exact hx' hx)]
    refine congrArg P.E (Subtype.ext ?_)
    simp only
    rw [Set.inter_comm]
    exact (Set.inter_union_sdiff T' T).symm
  have z1 : P.E ⟨T ∩ T', h0⟩ * P.E ⟨T' \ T, h2⟩ = 0 := E_mul_of_disjoint P h0 h2 (by
    rw [Set.disjoint_left]; rintro x ⟨hx, _⟩ ⟨_, hx'⟩; exact hx' hx)
  have z2 : P.E ⟨T \ T', h1⟩ * P.E ⟨T ∩ T', h0⟩ = 0 := E_mul_of_disjoint P h1 h0 (by
    rw [Set.disjoint_left]; rintro x ⟨_, hx⟩ ⟨_, hx'⟩; exact hx hx')
  have z3 : P.E ⟨T \ T', h1⟩ * P.E ⟨T' \ T, h2⟩ = 0 := E_mul_of_disjoint P h1 h2 (by
    rw [Set.disjoint_left]; rintro x ⟨hx, hx'⟩ ⟨hy, hy'⟩; exact hx' hy)
  rw [e1, e2, add_mul, mul_add, mul_add, z1, z2, z3, E_mul_self]
  simp
private lemma diagonalMeasure_E (T : {T : Set (SpectralDomain J) // MeasurableSet T}) (ψ : 𝒦) :
    diagonalMeasure P (P.E T ψ) = (diagonalMeasure P ψ).restrict T.1 := by
  refine measure_ext_real fun R hR => ?_
  have h1 := inner_E_self P (P.E T ψ) ⟨R, hR⟩
  have h2 : inner ℂ (P.E T ψ) (P.E ⟨R, hR⟩ (P.E T ψ)) =
      inner ℂ ψ (P.E ⟨R ∩ T.1, hR.inter T.2⟩ ψ) := by
    rw [inner_E_left, ← E_mul_eq_inter P hR T.2]
    have : P.E T (P.E ⟨R, hR⟩ (P.E T ψ)) =
        (P.E ⟨R, hR⟩ * P.E ⟨T.1, T.2⟩) ψ := by
      have hc : P.E T * P.E ⟨R, hR⟩ = P.E ⟨R, hR⟩ * P.E T := by
        have a1 := E_mul_eq_inter P T.2 hR
        have a2 := E_mul_eq_inter P hR T.2
        have a3 : P.E ⟨T.1 ∩ R, T.2.inter hR⟩ = P.E ⟨R ∩ T.1, hR.inter T.2⟩ :=
          congrArg P.E (Subtype.ext (Set.inter_comm _ _))
        rw [show P.E T = P.E ⟨T.1, T.2⟩ from rfl, a1, a2, a3]
      have hm : P.E T * (P.E ⟨R, hR⟩ * P.E T) = P.E ⟨R, hR⟩ * P.E T := by
        rw [← mul_assoc, hc, mul_assoc, E_mul_self]
      exact congrArg (fun C : 𝒦 →L[ℂ] 𝒦 => C ψ) hm
    rw [this]
  rw [h2, inner_E_self] at h1
  have h3 := Complex.ofReal_injective h1
  rw [← h3]
  simp only [Measure.real]
  rw [Measure.restrict_apply hR]
end Projections
section Representation
variable {P : ProjectionValuedMeasure J 𝒦}
variable (P) in
private structure IsMultiplier (X : 𝒦 →L[ℂ] 𝒦) (f : SpectralDomain J → ℂ) : Prop where
  measurable : Measurable f
  bounded : ∃ c : ℝ, ∀ p, ‖f p‖ ≤ c
  inner_eq : ∀ w, inner ℂ w (X w) = ∫ p, f p ∂diagonalMeasure P w
private lemma IsMultiplier.integrable {X : 𝒦 →L[ℂ] 𝒦} {f : SpectralDomain J → ℂ}
    (h : IsMultiplier P X f) (μ : Measure (SpectralDomain J)) [IsFiniteMeasure μ] :
    Integrable f μ := by
  obtain ⟨c, hc⟩ := h.bounded
  exact integrable_of_norm_le h.measurable hc μ
private lemma IsMultiplier.inner_compress {X : 𝒦 →L[ℂ] 𝒦} {f : SpectralDomain J → ℂ}
    (h : IsMultiplier P X f) (T : {T : Set (SpectralDomain J) // MeasurableSet T}) (w : 𝒦) :
    inner ℂ (P.E T w) (X (P.E T w)) = ∫ p in T.1, f p ∂diagonalMeasure P w := by
  rw [h.inner_eq, diagonalMeasure_E]
private lemma IsMultiplier.commute_E {X : 𝒦 →L[ℂ] 𝒦} {f : SpectralDomain J → ℂ}
    (h : IsMultiplier P X f) (T : {T : Set (SpectralDomain J) // MeasurableSet T}) :
    P.E T * X = X * P.E T := by
  have hT := T.2
  have hTc := T.2.compl
  set a := P.E T with ha
  set b := P.E ⟨T.1ᶜ, hTc⟩ with hb
  have hab : a * b = 0 := E_mul_of_disjoint P hT hTc disjoint_compl_right
  have hba : b * a = 0 := E_mul_of_disjoint P hTc hT disjoint_compl_left
  have haa : a * a = a := E_mul_self P _
  have hX : X = a * X * a + b * X * b := by
    refine ext_of_inner_self fun w => ?_
    have i1 : inner ℂ w ((a * X * a) w) = inner ℂ (a w) (X (a w)) := by
      simp only [mul_apply_eq_comp]
      exact (inner_E_left P T _ _).symm
    have i2 : inner ℂ w ((b * X * b) w) = inner ℂ (b w) (X (b w)) := by
      simp only [mul_apply_eq_comp]
      exact (inner_E_left P _ _ _).symm
    rw [add_apply, inner_add_right, i1, i2, h.inner_compress T w,
      h.inner_compress ⟨T.1ᶜ, hTc⟩ w, h.inner_eq]
    exact (integral_add_compl hT (h.integrable _)).symm
  have l : a * X = a * X * a := by
    conv_lhs => rw [hX]
    rw [mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, haa, hab]
    simp
  have r : X * a = a * X * a := by
    conv_lhs => rw [hX]
    rw [add_mul, mul_assoc _ a a, haa, mul_assoc _ b a, hba]
    simp
  rw [l, r]
private lemma IsMultiplier.inner_E_apply {X : 𝒦 →L[ℂ] 𝒦} {f : SpectralDomain J → ℂ}
    (h : IsMultiplier P X f) (T : {T : Set (SpectralDomain J) // MeasurableSet T}) (w : 𝒦) :
    inner ℂ w (P.E T (X w)) = ∫ p in T.1, f p ∂diagonalMeasure P w := by
  have e : P.E T (X w) = P.E T (X (P.E T w)) := by
    have h1 : (P.E T * (P.E T * X)) w = (P.E T * (X * P.E T)) w := by rw [h.commute_E T]
    have h2 : P.E T * (P.E T * X) = P.E T * X := by rw [← mul_assoc, E_mul_self]
    rw [h2] at h1
    simpa using h1
  rw [e, ← inner_E_left]
  exact h.inner_compress T w
private lemma exists_of_simpleFunc {Y : 𝒦 →L[ℂ] 𝒦} {g : SpectralDomain J → ℂ}
    (hY : IsMultiplier P Y g) (s : SimpleFunc (SpectralDomain J) ℂ) :
    ∃ C : 𝒦 →L[ℂ] 𝒦, (∀ w, inner ℂ w (C w) = ∫ p, s p ∂diagonalMeasure P w) ∧
      ∀ w, inner ℂ w (C (Y w)) = ∫ p, s p * g p ∂diagonalMeasure P w := by
  obtain ⟨cg, hcg⟩ := hY.bounded
  induction s using SimpleFunc.induction with
  | @const c T hT =>
    refine ⟨c • P.E ⟨T, hT⟩, fun w => ?_, fun w => ?_⟩
    · have e : ∀ p, (SimpleFunc.piecewise T hT (SimpleFunc.const _ c) (SimpleFunc.const _ 0)) p =
          T.indicator (fun _ => c) p := fun p => by
        by_cases hp : p ∈ T <;> simp [SimpleFunc.piecewise_apply, hp]
      simp only [e]
      rw [integral_indicator hT, setIntegral_const, smul_apply,
        inner_smul_right, inner_E_self]
      simp [mul_comm]
    · have e : ∀ p, (SimpleFunc.piecewise T hT (SimpleFunc.const _ c) (SimpleFunc.const _ 0)) p *
          g p = T.indicator (fun p => c * g p) p := fun p => by
        by_cases hp : p ∈ T <;> simp [SimpleFunc.piecewise_apply, hp]
      simp only [e]
      rw [integral_indicator hT, integral_const_mul, smul_apply,
        inner_smul_right]
      exact congrArg (c * ·) (hY.inner_E_apply ⟨T, hT⟩ w)
  | @add s s' _ h h' =>
    obtain ⟨C, h1, h2⟩ := h
    obtain ⟨C', h1', h2'⟩ := h'
    have hint : ∀ (t : SimpleFunc (SpectralDomain J) ℂ) (w : 𝒦),
        Integrable (fun p => t p * g p) (diagonalMeasure P w) := fun t w => by
      obtain ⟨ct, hct⟩ : ∃ c : ℝ, ∀ p, ‖t p‖ ≤ c :=
        ⟨_, fun p => (t.exists_forall_norm_le).choose_spec p⟩
      refine integrable_of_norm_le (t.measurable.mul hY.measurable) (c := ct * cg) (fun p => ?_) _
      rw [Pi.mul_apply, norm_mul]
      exact mul_le_mul (hct p) (hcg p) (norm_nonneg _) ((norm_nonneg _).trans (hct p))
    refine ⟨C + C', fun w => ?_, fun w => ?_⟩
    · rw [add_apply, inner_add_right, h1, h1',
        ← integral_add (s.integrable_of_isFiniteMeasure) (s'.integrable_of_isFiniteMeasure)]
      rfl
    · rw [add_apply, inner_add_right, h2, h2', ← integral_add (hint s w) (hint s' w)]
      refine integral_congr_ae (ae_of_all _ fun p => ?_)
      simp [add_mul]
private lemma IsMultiplier.mul {X Y : 𝒦 →L[ℂ] 𝒦} {f g : SpectralDomain J → ℂ}
    (hX : IsMultiplier P X f) (hY : IsMultiplier P Y g) : IsMultiplier P (X * Y) (f * g) := by
  obtain ⟨cf, hcf⟩ := hX.bounded
  obtain ⟨cg, hcg⟩ := hY.bounded
  have hcf0 : 0 ≤ cf := (norm_nonneg _).trans (hcf 1)
  refine ⟨hX.measurable.mul hY.measurable, ⟨cf * cg, fun p => ?_⟩, fun w => ?_⟩
  · rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (hcf p) (hcg p) (norm_nonneg _) hcf0
  have hsm := hX.measurable.stronglyMeasurable
  let s : ℕ → SimpleFunc (SpectralDomain J) ℂ := hsm.approxBounded cf
  have hs_le : ∀ l p, ‖s l p‖ ≤ cf := fun l p => hsm.norm_approxBounded_le hcf0 l p
  have hs_lim : ∀ p, Tendsto (fun l => s l p) atTop (𝓝 (f p)) := fun p =>
    hsm.tendsto_approxBounded_of_norm_le (hcf p)
  choose C hC1 hC2 using fun l => exists_of_simpleFunc hY (s l)
  have hdiag : ∀ v, Tendsto (fun l => inner ℂ v (C l v)) atTop (𝓝 (inner ℂ v (X v))) := fun v => by
    simp only [hC1, hX.inner_eq]
    exact tendsto_integral_of_dominated_convergence (fun _ => cf)
      (fun l => (s l).measurable.aestronglyMeasurable) (integrable_const _)
      (fun l => ae_of_all _ (hs_le l)) (ae_of_all _ hs_lim)
  have hoff := tendsto_inner_of_tendsto_inner_self hdiag w (Y w)
  have hint : Tendsto (fun l => inner ℂ w (C l (Y w))) atTop
      (𝓝 (∫ p, (f * g) p ∂diagonalMeasure P w)) := by
    simp only [hC2]
    refine tendsto_integral_of_dominated_convergence (fun _ => cf * cg)
      (fun l => ((s l).measurable.mul hY.measurable).aestronglyMeasurable) (integrable_const _)
      (fun l => ae_of_all _ fun p => ?_) (ae_of_all _ fun p => (hs_lim p).mul_const _)
    rw [norm_mul]
    exact mul_le_mul (hs_le l p) (hcg p) (norm_nonneg _) hcf0
  exact tendsto_nhds_unique hoff hint
private lemma IsMultiplier.congr {X X' : 𝒦 →L[ℂ] 𝒦} {f f' : SpectralDomain J → ℂ}
    (h : IsMultiplier P X f) (hX : X' = X) (hf : f' = f) : IsMultiplier P X' f' :=
  hX ▸ hf ▸ h
private lemma isMultiplier_one : IsMultiplier P (1 : 𝒦 →L[ℂ] 𝒦) (1 : SpectralDomain J → ℂ) := by
  refine ⟨measurable_const, ⟨1, fun p => by simp⟩, fun w => ?_⟩
  have h := inner_E_self P w ⟨univ, MeasurableSet.univ⟩
  rw [P.E_univ] at h
  rw [h]
  simp
private lemma IsMultiplier.star {X : 𝒦 →L[ℂ] 𝒦} {f : SpectralDomain J → ℂ}
    (h : IsMultiplier P X f) : IsMultiplier P (star X) (fun p => conj (f p)) := by
  obtain ⟨c, hc⟩ := h.bounded
  refine ⟨Complex.continuous_conj.measurable.comp h.measurable, ⟨c, fun p => by simpa using hc p⟩,
    fun w => ?_⟩
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    ← inner_conj_symm, h.inner_eq]
  exact (integral_conj).symm
end Representation
section Moments
variable {P : ProjectionValuedMeasure J 𝒦} {S : CommutingFamily 𝒦 J}
private lemma measurable_radial :
    Measurable (fun p : SpectralDomain J => (((p.1 : ℝ) : ℂ))) :=
  (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).measurable
private lemma measurable_angular (α : J) :
    Measurable (fun p : SpectralDomain J => ((p.2 α : ℂ))) :=
  (continuous_subtype_val.comp ((continuous_apply α).comp continuous_snd)).measurable
private lemma isMultiplier_A (h : HasFirstMoments S P) :
    IsMultiplier P S.A (fun p => (((p.1 : ℝ) : ℂ))) := by
  refine ⟨measurable_radial, ⟨1, fun p => ?_⟩,
    fun w => (h w _ (isDiagonalMeasure_diagonalMeasure P w)).1⟩
  simpa [abs_of_nonneg p.1.2.1] using p.1.2.2
private lemma isMultiplier_B (h : HasFirstMoments S P) (α : J) :
    IsMultiplier P (S.B α : 𝒦 →L[ℂ] 𝒦) (fun p => ((p.2 α : ℂ))) :=
  ⟨measurable_angular α, ⟨1, fun _ => (Circle.norm_coe _).le⟩,
    fun w => (h w _ (isDiagonalMeasure_diagonalMeasure P w)).2 α⟩
private lemma isMultiplier_A_pow (h : HasFirstMoments S P) (n : ℕ) :
    IsMultiplier P (S.A ^ n) (fun p => (((p.1 : ℝ) : ℂ)) ^ n) := by
  induction n with
  | zero => simpa [Pi.one_def] using isMultiplier_one (P := P)
  | succ n ih =>
    refine (ih.mul (isMultiplier_A h)).congr (pow_succ _ _) ?_
    funext p
    simp [pow_succ]
private lemma isMultiplier_B_zpow (h : HasFirstMoments S P) (α : J) (k : ℤ) :
    IsMultiplier P ((S.B α ^ k : unitary (𝒦 →L[ℂ] 𝒦)) : 𝒦 →L[ℂ] 𝒦)
      (fun p => ((p.2 α : ℂ)) ^ k) := by
  have hne : ∀ p : SpectralDomain J, ((p.2 α : ℂ)) ≠ 0 := fun p => Circle.coe_ne_zero _
  induction k using Int.induction_on with
  | zero => simpa [Pi.one_def] using isMultiplier_one (P := P)
  | succ k ih =>
    refine (ih.mul (isMultiplier_B h α)).congr (by rw [zpow_add_one]; rfl) ?_
    funext p
    simp [zpow_add_one₀ (hne p)]
  | pred k ih =>
    refine (ih.mul (isMultiplier_B h α).star).congr (by rw [zpow_sub_one]; rfl) ?_
    funext p
    simp only [Pi.mul_apply]
    rw [zpow_sub_one₀ (hne p), ← Circle.coe_inv_eq_conj, Circle.coe_inv]
private lemma isMultiplier_noncommProd (h : HasFirstMoments S P) (y : J → ℤ) (s : Finset J)
    (comm : (s : Set J).Pairwise (Function.onFun Commute fun α => S.B α ^ y α)) :
    IsMultiplier P ((s.noncommProd (fun α => S.B α ^ y α) comm : unitary (𝒦 →L[ℂ] 𝒦)) :
      𝒦 →L[ℂ] 𝒦) (fun p => ∏ α ∈ s, ((p.2 α : ℂ)) ^ y α) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [Pi.one_def] using isMultiplier_one (P := P)
  | insert a s ha ih =>
    refine ((isMultiplier_B_zpow h a (y a)).mul (ih (comm.mono (by simp)))).congr
      (by rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]; rfl) ?_
    funext p
    simp [Finset.prod_insert ha]
private lemma isMultiplier_familyMonomial (h : HasFirstMoments S P) (n : ℕ) (y : J → ℤ) :
    IsMultiplier P (familyMonomial S n y) (spectralMonomial n y) :=
  (isMultiplier_A_pow h n).mul (isMultiplier_noncommProd h y Finset.univ _)
private lemma hasSystemMoments_of_hasFirstMoments (h : HasFirstMoments S P) :
    HasSystemMoments S P :=
  fun ψ => ⟨diagonalMeasure P ψ, inferInstance, inner_E_self P ψ,
    fun n y => (isMultiplier_familyMonomial h n y).inner_eq ψ⟩
private lemma hasFirstMoments_of_hasSystemMoments (h : HasSystemMoments S P) :
    HasFirstMoments S P := by
  classical
  intro ψ ρ hρ
  obtain ⟨μ, hμ, hval, hmom⟩ := h ψ
  have hρμ : ρ = μ := by
    have := hρ.1
    refine measure_ext_real fun T hT => ?_
    have h1 := hρ.2 ⟨T, hT⟩
    rw [hval] at h1
    exact (Complex.ofReal_injective h1).symm
  subst hρμ
  have hB0 : S.unitaryMonomial 0 = 1 := by
    have e := Finset.noncommProd_eq_pow_card Finset.univ (fun α => S.B α ^ (0 : J → ℤ) α)
      (fun α _ α' _ _ => S.commute_zpow_unitary 0 α α') 1 (fun α _ => by simp)
    rw [one_pow] at e
    exact congrArg (fun U : unitary (𝒦 →L[ℂ] 𝒦) => (U : 𝒦 →L[ℂ] 𝒦)) e
  have hBα : ∀ α, S.unitaryMonomial (Pi.single α 1) = (S.B α : 𝒦 →L[ℂ] 𝒦) := fun α => by
    have comm : ((Finset.univ : Finset J) : Set J).Pairwise
        (Function.onFun Commute fun β => S.B β ^ (Pi.single α 1 : J → ℤ) β) :=
      fun β _ β' _ _ => S.commute_zpow_unitary _ β β'
    have e := Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ α)
      (fun β => S.B β ^ (Pi.single α 1 : J → ℤ) β) comm
    have e1 := Finset.noncommProd_eq_pow_card (Finset.univ.erase α)
      (fun β => S.B β ^ (Pi.single α 1 : J → ℤ) β) (comm.mono (by simp)) 1
      (fun β hβ => by simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hβ)])
    rw [e1, one_pow, mul_one] at e
    simp only [Pi.single_eq_same, zpow_one] at e
    exact (congrArg (fun U : unitary (𝒦 →L[ℂ] 𝒦) => (U : 𝒦 →L[ℂ] 𝒦)) e).symm
  refine ⟨?_, fun α => ?_⟩
  · have := hmom 1 0
    simp only [familyMonomial, pow_one, hB0, mul_one] at this
    rw [this]
    simp [spectralMonomial, torusMonomial]
  · have := hmom 0 (Pi.single α 1)
    simp only [familyMonomial, pow_zero, hBα, one_mul] at this
    rw [this]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [spectralMonomial, torusMonomial, pow_zero, one_mul]
    rw [Finset.prod_eq_single α]
    · simp
    · intro β _ hβ
      simp [Pi.single_eq_of_ne hβ]
    · simp
end Moments
theorem firstMomentUniqueness (hcalc : BorelCalculusStatement) :
    FirstMomentUniquenessStatement := by
  intro 𝒦 _ _ _ J _ _ S
  obtain ⟨P, hP, hmom, huniq⟩ : ∃ P : ProjectionValuedMeasure J 𝒦,
      (∀ T, ⇑(P.E T) = jointSpectralMeasure S T.1) ∧ HasSystemMoments S P ∧
      ∀ P' : ProjectionValuedMeasure J 𝒦, HasSystemMoments S P' → P' = P := by
    obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := hcalc 𝒦 J S
    exact h
  refine ⟨⟨P, fun Δ ψ => congrFun (hP Δ) ψ, hasFirstMoments_of_hasSystemMoments hmom⟩,
    fun E' hE' Δ ψ => ?_⟩
  rw [huniq E' (hasSystemMoments_of_hasFirstMoments hE')]
  exact congrFun (hP Δ) ψ
end YangMills.Construction.JointSpectrum.FirstMoments

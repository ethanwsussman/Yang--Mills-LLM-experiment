import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction
namespace BorelSpectral
abbrev BorelSubsets (X : Type*) [MeasurableSpace X] : Type _ := Subtype (MeasurableSet : Set X → Prop)
structure SpectralMeasure {n : ℕ} (Y : Set (Fin n → ℝ)) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  one_le_dimension : 1 ≤ n
  measurableSet_carrier : MeasurableSet Y
  toFun : BorelSubsets Y → H →L[ℂ] H
  isStarProjection : ∀ S, IsStarProjection (toFun S)
  map_univ : toFun ⟨univ, MeasurableSet.univ⟩ = 1
  map_inter : ∀ S T : BorelSubsets Y,
    toFun ⟨S.1 ∩ T.1, S.2.inter T.2⟩ = toFun S * toFun T
  countablyAdditive : ∀ (v : H) (S : ℕ → BorelSubsets Y),
    (Pairwise fun k l => Disjoint (S k).1 (S l).1) →
      HasSum (fun k => ⟪v, toFun (S k) v⟫_ℂ)
        ⟪v, toFun ⟨⋃ k, (S k).1, MeasurableSet.iUnion fun k => (S k).2⟩ v⟫_ℂ
variable {n n' : ℕ} {Y : Set (Fin n → ℝ)} {Y' : Set (Fin n' → ℝ)} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace SpectralMeasure
instance : CoeFun (SpectralMeasure Y H) fun _ => BorelSubsets Y → H →L[ℂ] H := ⟨toFun⟩
theorem ext_apply {P Q : SpectralMeasure Y H} (h : ∀ S, P S = Q S) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h
theorem inner_apply_self_eq_norm_sq (P : SpectralMeasure Y H) (S : BorelSubsets Y) (v : H) :
    ⟪v, P S v⟫_ℂ = ((‖P S v‖ ^ 2 : ℝ) : ℂ) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (P.isStarProjection S).isSelfAdjoint
  have hi : P S (P S v) = P S v :=
    congrArg (fun T : H →L[ℂ] H => T v) (P.isStarProjection S).isIdempotentElem.eq
  have h₁ : ⟪v, P S v⟫_ℂ = ⟪P S v, P S v⟫_ℂ := by
    have := hs v (P S v)
    simp only [ContinuousLinearMap.coe_coe, hi] at this
    exact this.symm
  rw [h₁, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
theorem norm_sq_apply_empty (P : SpectralMeasure Y H) (v : H) :
    ‖P ⟨∅, MeasurableSet.empty⟩ v‖ ^ 2 = 0 := by
  have h := P.countablyAdditive v (fun _ => ⟨∅, MeasurableSet.empty⟩)
    (fun _ _ _ => disjoint_bot_left)
  have h₀ := h.summable.tendsto_atTop_zero
  have h₁ : ⟪v, P ⟨∅, MeasurableSet.empty⟩ v⟫_ℂ = 0 := tendsto_nhds_unique tendsto_const_nhds h₀
  rw [inner_apply_self_eq_norm_sq] at h₁
  exact_mod_cast h₁
theorem apply_empty (P : SpectralMeasure Y H) : P ⟨∅, MeasurableSet.empty⟩ = 0 := by
  ext v
  simpa using P.norm_sq_apply_empty v
def diagMeasure (P : SpectralMeasure Y H) (v : H) : Measure Y :=
  Measure.ofMeasurable (fun S hS => ENNReal.ofReal (‖P ⟨S, hS⟩ v‖ ^ 2))
    (by simp only [P.norm_sq_apply_empty v, ENNReal.ofReal_zero])
    (by
      intro f hf hd
      have h := P.countablyAdditive v (fun k => ⟨f k, hf k⟩) hd
      simp only [inner_apply_self_eq_norm_sq] at h
      have hr := Complex.hasSum_ofReal.mp h
      rw [← hr.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hr.summable])
theorem diagMeasure_apply (P : SpectralMeasure Y H) (v : H) (S : BorelSubsets Y) :
    P.diagMeasure v S.1 = ENNReal.ofReal (‖P S v‖ ^ 2) :=
  Measure.ofMeasurable_apply _ S.2
theorem diagMeasure_univ (P : SpectralMeasure Y H) (v : H) :
    P.diagMeasure v univ = ENNReal.ofReal (‖v‖ ^ 2) := by
  have h := P.diagMeasure_apply v ⟨univ, MeasurableSet.univ⟩
  rw [P.map_univ] at h
  simpa using h
instance (P : SpectralMeasure Y H) (v : H) : IsFiniteMeasure (P.diagMeasure v) :=
  ⟨by rw [diagMeasure_univ]; exact ENNReal.ofReal_lt_top⟩
theorem inner_apply_self_eq_diagMeasure (P : SpectralMeasure Y H) (v : H) (S : BorelSubsets Y) :
    ⟪v, P S v⟫_ℂ = ((P.diagMeasure v).real S.1 : ℂ) := by
  rw [inner_apply_self_eq_norm_sq, Measure.real, diagMeasure_apply,
    ENNReal.toReal_ofReal (by positivity)]
def polarizedIntegral (P : SpectralMeasure Y H) (g : Y → ℂ) (u v : H) : ℂ :=
  (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4,
    (-Complex.I) ^ k * ∫ y, g y ∂P.diagMeasure (u + Complex.I ^ k • v)
def IsCarriedBy (P : SpectralMeasure Y H) (S : BorelSubsets Y) : Prop :=
  P ⟨S.1ᶜ, S.2.compl⟩ = 0
def essSupport (P : SpectralMeasure Y H) : Set (Fin n → ℝ) :=
  (⋃₀ {O | ∃ hO : IsOpen O,
    P ⟨Subtype.val ⁻¹' O, measurable_subtype_coe hO.measurableSet⟩ = 0})ᶜ
def IsDiagonalIntegral (P : SpectralMeasure Y H) (g : Y → ℂ) (T : H →L[ℂ] H) : Prop :=
  ∀ v, ⟪v, T v⟫_ℂ = ∫ y, g y ∂P.diagMeasure v
def integralOp (P : SpectralMeasure Y H) (g : Y → ℂ) : H →L[ℂ] H :=
  Classical.epsilon (P.IsDiagonalIntegral g)
end SpectralMeasure
def truncate {X : Type*} (g : X → ℂ) (r : ℕ) : X → ℂ :=
  indicator {y | ‖g y‖ ≤ r} g
def zeroExtend {X β : Type*} [Zero β] (S : Set X) (g : S → β) : X → β :=
  open scoped Classical in fun y => if h : y ∈ S then g ⟨y, h⟩ else 0
theorem measurable_zeroExtend {X β : Type*} [MeasurableSpace X] [MeasurableSpace β] [Zero β]
    {S : Set X} (hS : MeasurableSet S) {g : S → β} (hg : Measurable g) :
    Measurable (zeroExtend S g) := by
  classical
  exact Measurable.dite hg measurable_const hS
namespace SpectralMeasure
def integralDom (P : SpectralMeasure Y H) (g : Y → ℂ) : Set H :=
  {v | ∫⁻ y, ‖g y‖ₑ ^ 2 ∂P.diagMeasure v < ∞}
def integralApply (P : SpectralMeasure Y H) (g : Y → ℂ) (v : H) : H :=
  limUnder atTop fun r : ℕ => P.integralOp (truncate g r) v
theorem integralDom_eq_univ (P : SpectralMeasure Y H) {g : Y → ℂ} {c : ℝ}
    (hc : ∀ y, ‖g y‖ ≤ c) : P.integralDom g = univ := by
  refine eq_univ_of_forall fun v => ?_
  have hle : ∀ y, ‖g y‖ₑ ^ 2 ≤ ENNReal.ofReal c ^ 2 := fun y => by
    gcongr
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hc y)
  refine (lintegral_mono hle).trans_lt ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)
theorem integralApply_eq_integralOp (P : SpectralMeasure Y H) {g : Y → ℂ} {c : ℝ}
    (hc : ∀ y, ‖g y‖ ≤ c) (v : H) : P.integralApply g v = P.integralOp g v := by
  refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  obtain ⟨r₀, hr₀⟩ := exists_nat_ge c
  filter_upwards [eventually_ge_atTop r₀] with r hr
  have : truncate g r = g := by
    refine indicator_eq_self.mpr fun y _ => ?_
    exact (hc y).trans (hr₀.trans (by exact_mod_cast hr))
  rw [this]
def integralOpOn (P : SpectralMeasure Y H) (S : BorelSubsets Y) (g : S.1 → ℂ) :
    H →L[ℂ] H :=
  P.integralOp (zeroExtend S.1 g)
def integralDomOn (P : SpectralMeasure Y H) (S : BorelSubsets Y) (g : S.1 → ℂ) : Set H :=
  P.integralDom (zeroExtend S.1 g)
def integralApplyOn (P : SpectralMeasure Y H) (S : BorelSubsets Y) (g : S.1 → ℂ) (v : H) : H :=
  P.integralApply (zeroExtend S.1 g) v
def pushforward (P : SpectralMeasure Y H) (hn' : 1 ≤ n') (hY' : MeasurableSet Y') (κ : Y → Y')
    (hκ : Measurable κ) : SpectralMeasure Y' H where
  one_le_dimension := hn'
  measurableSet_carrier := hY'
  toFun T := P ⟨κ ⁻¹' T.1, hκ T.2⟩
  isStarProjection _ := P.isStarProjection _
  map_univ := P.map_univ
  map_inter S T := P.map_inter ⟨κ ⁻¹' S.1, hκ S.2⟩ ⟨κ ⁻¹' T.1, hκ T.2⟩
  countablyAdditive v S hd := by
    have h := P.countablyAdditive v (fun k => ⟨κ ⁻¹' (S k).1, hκ (S k).2⟩)
      (fun k l hkl => (hd hkl).preimage κ)
    have hu : (⟨κ ⁻¹' ⋃ k, (S k).1, hκ (MeasurableSet.iUnion fun k => (S k).2)⟩ : BorelSubsets Y) =
        ⟨⋃ k, κ ⁻¹' (S k).1, MeasurableSet.iUnion fun k => hκ (S k).2⟩ :=
      Subtype.ext (preimage_iUnion)
    simpa only [hu] using h
def extendCarrier {Y₂ : Set (Fin n → ℝ)} (P : SpectralMeasure Y H) (hY : Y ⊆ Y₂)
    (hY₂ : MeasurableSet Y₂) : SpectralMeasure Y₂ H :=
  P.pushforward P.one_le_dimension hY₂ (inclusion hY) (measurable_subtype_coe.subtype_mk)
theorem extendCarrier_isCarriedBy {Y₂ : Set (Fin n → ℝ)} (P : SpectralMeasure Y H)
    (hY : Y ⊆ Y₂) (hY₂ : MeasurableSet Y₂) :
    (P.extendCarrier hY hY₂).IsCarriedBy
      ⟨Subtype.val ⁻¹' Y, measurable_subtype_coe P.measurableSet_carrier⟩ := by
  have hu : (⟨inclusion hY ⁻¹' (Subtype.val ⁻¹' Y)ᶜ,
      measurable_subtype_coe.subtype_mk
        (measurable_subtype_coe P.measurableSet_carrier).compl⟩ : BorelSubsets Y) =
      ⟨∅, MeasurableSet.empty⟩ := by
    refine Subtype.ext (eq_empty_of_forall_notMem fun y hy => ?_)
    exact hy y.2
  exact (congrArg P.toFun hu).trans P.apply_empty
end SpectralMeasure
def realLineSet (S : BorelSubsets ℝ) : BorelSubsets (univ : Set (Fin 1 → ℝ)) :=
  ⟨{y | y.1 0 ∈ S.1}, ((measurable_pi_apply 0).comp measurable_subtype_coe) S.2⟩
def coordLine (i : Fin n) (y : (univ : Set (Fin n → ℝ))) : (univ : Set (Fin 1 → ℝ)) :=
  ⟨fun _ => y.1 i, mem_univ _⟩
theorem measurable_coordLine (i : Fin n) : Measurable (coordLine i) := by
  refine Measurable.subtype_mk (measurable_pi_iff.mpr fun _ => ?_)
  exact (measurable_pi_apply i).comp measurable_subtype_coe
namespace SpectralMeasure
def coordMarginal (P : SpectralMeasure (univ : Set (Fin n → ℝ)) H) (i : Fin n) :
    SpectralMeasure (univ : Set (Fin 1 → ℝ)) H :=
  P.pushforward le_rfl MeasurableSet.univ (coordLine i) (measurable_coordLine i)
theorem coordMarginal_realLineSet (P : SpectralMeasure (univ : Set (Fin n → ℝ)) H) (i : Fin n)
    (S : BorelSubsets ℝ) :
    P.coordMarginal i (realLineSet S) =
      P ⟨{y | y.1 i ∈ S.1}, ((measurable_pi_apply i).comp measurable_subtype_coe) S.2⟩ :=
  rfl
end SpectralMeasure
end BorelSpectral
end YangMills.Construction

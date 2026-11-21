import YangMills.Construction.Lattice.CubesOfTwoStandardPartitionsProof
import YangMills.Construction.Weighted.LocalLipCalculus
import Mathlib
set_option autoImplicit false
open Filter YangMills.Construction.TorusMetric
open scoped ENNReal NNReal Topology
noncomputable section
namespace YangMills.Construction.Weighted.LocalLip
variable {S : ℝ}
theorem ennreal_limsup_add_le {α : Type*} {F : Filter α} (u v : α → ℝ≥0∞) :
    limsup (fun a => u a + v a) F ≤ limsup u F + limsup v F := by
  by_cases hu : limsup u F = ⊤
  · simp [hu]
  by_cases hv : limsup v F = ⊤
  · simp [hv]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hpos : ((ε / 2 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    simpa using hε.ne'
  have eu : ∀ᶠ a in F, u a < limsup u F + ((ε / 2 : ℝ≥0) : ℝ≥0∞) :=
    eventually_lt_of_limsup_lt (ENNReal.lt_add_right hu hpos)
  have ev : ∀ᶠ a in F, v a < limsup v F + ((ε / 2 : ℝ≥0) : ℝ≥0∞) :=
    eventually_lt_of_limsup_lt (ENNReal.lt_add_right hv hpos)
  refine limsup_le_of_le (h := ?_)
  filter_upwards [eu, ev] with a ha ha'
  have hhalf : ((ε / 2 : ℝ≥0) : ℝ≥0∞) + ((ε / 2 : ℝ≥0) : ℝ≥0∞) = (ε : ℝ≥0∞) := by
    rw [← ENNReal.coe_add, add_halves]
  calc u a + v a
      ≤ (limsup u F + ((ε / 2 : ℝ≥0) : ℝ≥0∞)) + (limsup v F + ((ε / 2 : ℝ≥0) : ℝ≥0∞)) :=
        add_le_add ha.le ha'.le
    _ = limsup u F + limsup v F + (((ε / 2 : ℝ≥0) : ℝ≥0∞) + ((ε / 2 : ℝ≥0) : ℝ≥0∞)) := by
        abel
    _ = limsup u F + limsup v F + ε := by rw [hhalf]
theorem torusSupNorm_eq_norm (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem torusL1Norm_nonneg (x : Torus4 S) : 0 ≤ torusL1Norm x := by
  rw [torusL1Norm_eq_sum_norm]
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _
theorem norm_le_torusL1Norm (x : Torus4 S) : ‖x‖ ≤ torusL1Norm x := by
  refine (pi_norm_le_iff_of_nonneg (torusL1Norm_nonneg x)).2 fun μ => ?_
  rw [torusL1Norm_eq_sum_norm]
  exact Finset.single_le_sum (f := fun μ => ‖x μ‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ μ)
theorem distInftyToSet_eq_infDist (A : Set (Torus4 S)) (x : Torus4 S) :
    distInftyToSet A x = Metric.infDist x A := by
  have h : setSupDist {x} A = Metric.infEDist x A := by
    simp only [setSupDist, iInf_singleton, Metric.infEDist, torusSupNorm_eq_norm]
    refine iInf_congr fun b => iInf_congr fun _ => ?_
    rw [edist_dist, dist_eq_norm]
  rw [distInftyToSet, h]
  rfl
theorem abs_distInftyToSet_sub_le (A : Set (Torus4 S)) (x x' : Torus4 S) :
    |distInftyToSet A x' - distInftyToSet A x| ≤ torusL1Norm (x' - x) := by
  rw [distInftyToSet_eq_infDist, distInftyToSet_eq_infDist]
  refine le_trans ?_ (norm_le_torusL1Norm (x' - x))
  rw [← dist_eq_norm, abs_sub_le_iff]
  constructor
  · have := Metric.infDist_le_infDist_add_dist (s := A) (x := x') (y := x)
    linarith
  · have := Metric.infDist_le_infDist_add_dist (s := A) (x := x) (y := x')
    rw [dist_comm] at this
    linarith
theorem diffQuot_le_of_lipschitz {f : Torus4 S → ℝ} {C : ℝ≥0}
    (h : ∀ x x', |f x' - f x| ≤ C * torusL1Norm (x' - x)) (x x' : Torus4 S) :
    |f x' - f x| / torusL1Norm (x' - x) ≤ C :=
  div_le_of_le_mul₀ (torusL1Norm_nonneg _) C.2 (h x x')
theorem exists_bound_of_lipschitzL1 (hS : S ≠ 0) {f : Torus4 S → ℝ} {C : ℝ≥0}
    (h : ∀ x x', |f x' - f x| ≤ C * torusL1Norm (x' - x)) :
    ∃ M : ℝ≥0, ∀ x, |f x| ≤ M := by
  have hd : ∀ x : Torus4 S, torusL1Norm x ≤ ∑ _μ : Fin 4, |S| / 2 := by
    intro x
    rw [torusL1Norm_eq_sum_norm]
    exact Finset.sum_le_sum fun μ _ => AddCircle.norm_le_half_period S hS
  refine ⟨⟨|f 0| + C * ∑ _μ : Fin 4, |S| / 2, by positivity⟩, fun x => ?_⟩
  have h₁ := h 0 x
  have h₂ : |f x| ≤ |f 0| + |f x - f 0| := by
    have := abs_add_le (f 0) (f x - f 0)
    simpa using this
  have h₃ : (C : ℝ) * torusL1Norm (x - 0) ≤ C * ∑ _μ : Fin 4, |S| / 2 :=
    mul_le_mul_of_nonneg_left (hd _) C.2
  show |f x| ≤ |f 0| + C * ∑ _μ : Fin 4, |S| / 2
  linarith
theorem abs_mul_sub_mul_le_add (a a' b b' : ℝ) :
    |a' * b' - a * b| ≤ |a'| * |b' - b| + |b| * |a' - a| := by
  have h : a' * b' - a * b = a' * (b' - b) + b * (a' - a) := by ring
  rw [h, ← abs_mul, ← abs_mul]
  exact abs_add_le _ _
theorem tendsto_ofReal_mul_abs_sub_self {f : Torus4 S → ℝ} {C : ℝ≥0}
    (h : ∀ x x', |f x' - f x| ≤ C * torusL1Norm (x' - x)) (K : ℝ) (x : Torus4 S) :
    Tendsto (fun x' => ENNReal.ofReal (K * |f x' - f x|)) (𝓝[≠] x) (𝓝 0) := by
  have hc : Continuous fun x' : Torus4 S => ∑ μ, ‖(x' - x) μ‖ := by
    fun_prop
  have hd : Tendsto (fun x' : Torus4 S => torusL1Norm (x' - x)) (𝓝 x) (𝓝 0) := by
    have := hc.tendsto x
    simpa [torusL1Norm_eq_sum_norm] using this
  have hf : Tendsto (fun x' => |f x' - f x|) (𝓝 x) (𝓝 0) := by
    refine squeeze_zero (fun _ => abs_nonneg _) (fun x' => h x x') ?_
    simpa using hd.const_mul (C : ℝ)
  have hK : Tendsto (fun x' => K * |f x' - f x|) (𝓝[≠] x) (𝓝 0) := by
    simpa using (hf.mono_left nhdsWithin_le_nhds).const_mul K
  simpa using ENNReal.tendsto_ofReal hK
theorem ennreal_limsup_eq_zero_of_tendsto {α : Type*} {F : Filter α} {u : α → ℝ≥0∞}
    (h : Tendsto u F (𝓝 0)) : limsup u F = 0 := by
  rcases F.eq_or_neBot with rfl | hF
  · simp
  · exact h.limsup_eq
theorem localLip_distInftyToSet (A : Set (Torus4 S)) :
    LipschitzL1 (distInftyToSet A) ∧ ∀ x, localLip (distInftyToSet A) x ≤ 1 := by
  refine ⟨⟨1, fun x x' => ?_⟩, fun x => ?_⟩
  · simpa using abs_distInftyToSet_sub_le A x x'
  · refine limsup_le_of_le (h := Eventually.of_forall fun x' => ?_)
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    exact div_le_one_of_le₀ (abs_distInftyToSet_sub_le A x x') (torusL1Norm_nonneg _)
theorem localLip_comp {f : Torus4 S → ℝ} (hf : LipschitzL1 f) {φ : ℝ → ℝ} {c : ℝ≥0}
    (hφ : LipschitzWith c φ) :
    LipschitzL1 (φ ∘ f) ∧
      ∀ x, localLip (φ ∘ f) x ≤ (c : ℝ≥0∞) * localLip f x := by
  have hφ' : ∀ a b : ℝ, |φ a - φ b| ≤ c * |a - b| := fun a b => by
    simpa [Real.dist_eq] using hφ.dist_le_mul a b
  obtain ⟨C, hC⟩ := hf
  refine ⟨⟨c * C, fun x x' => ?_⟩, fun x => ?_⟩
  · calc |(φ ∘ f) x' - (φ ∘ f) x| ≤ c * |f x' - f x| := hφ' _ _
      _ ≤ c * (C * torusL1Norm (x' - x)) := mul_le_mul_of_nonneg_left (hC x x') c.2
      _ = ((c * C : ℝ≥0) : ℝ) * torusL1Norm (x' - x) := by push_cast; ring
  · rw [localLip, localLip,
      ← ENNReal.limsup_const_mul_of_ne_top ENNReal.coe_ne_top]
    refine limsup_le_limsup (Eventually.of_forall fun x' => ?_)
    show ENNReal.ofReal (|φ (f x') - φ (f x)| / torusL1Norm (x' - x)) ≤
      (c : ℝ≥0∞) * ENNReal.ofReal (|f x' - f x| / torusL1Norm (x' - x))
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c.coe_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hφ' _ _) (torusL1Norm_nonneg _)
theorem localLip_eq_zero_of_locally_const {f : Torus4 S → ℝ} {x : Torus4 S}
    (h : ∃ U ∈ 𝓝 x, ∃ a : ℝ, ∀ y ∈ U, f y = a) : localLip f x = 0 := by
  obtain ⟨U, hU, a, ha⟩ := h
  refine le_antisymm (limsup_le_of_le (h := ?_)) (by simp)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU] with x' hx'
  simp [ha x' hx', ha x (mem_of_mem_nhds hU)]
theorem localLip_mul (hS : S ≠ 0) {f₁ f₂ : Torus4 S → ℝ} (h₁ : LipschitzL1 f₁)
    (h₂ : LipschitzL1 f₂) :
    LipschitzL1 (f₁ * f₂) ∧
      ∀ x, localLip (f₁ * f₂) x ≤
        ENNReal.ofReal |f₁ x| * localLip f₂ x +
          ENNReal.ofReal |f₂ x| * localLip f₁ x := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  obtain ⟨M₁, hM₁⟩ := exists_bound_of_lipschitzL1 hS hC₁
  obtain ⟨M₂, hM₂⟩ := exists_bound_of_lipschitzL1 hS hC₂
  refine ⟨⟨M₁ * C₂ + M₂ * C₁, fun x x' => ?_⟩, fun x => ?_⟩
  · have hd := torusL1Norm_nonneg (x' - x)
    calc |(f₁ * f₂) x' - (f₁ * f₂) x|
        ≤ |f₁ x'| * |f₂ x' - f₂ x| + |f₂ x| * |f₁ x' - f₁ x| := abs_mul_sub_mul_le_add _ _ _ _
      _ ≤ M₁ * (C₂ * torusL1Norm (x' - x)) + M₂ * (C₁ * torusL1Norm (x' - x)) :=
          add_le_add (mul_le_mul (hM₁ _) (hC₂ _ _) (abs_nonneg _) M₁.2)
            (mul_le_mul (hM₂ _) (hC₁ _ _) (abs_nonneg _) M₂.2)
      _ = ((M₁ * C₂ + M₂ * C₁ : ℝ≥0) : ℝ) * torusL1Norm (x' - x) := by push_cast; ring
  · set q₁ : Torus4 S → ℝ≥0∞ := fun x' =>
      ENNReal.ofReal (|f₁ x' - f₁ x| / torusL1Norm (x' - x)) with hq₁def
    set q₂ : Torus4 S → ℝ≥0∞ := fun x' =>
      ENNReal.ofReal (|f₂ x' - f₂ x| / torusL1Norm (x' - x)) with hq₂def
    set e : Torus4 S → ℝ≥0∞ := fun x' => ENNReal.ofReal ((C₂ : ℝ) * |f₁ x' - f₁ x|) with hedef
    have hpt : ∀ x', ENNReal.ofReal
        (|(f₁ * f₂) x' - (f₁ * f₂) x| / torusL1Norm (x' - x)) ≤
          (ENNReal.ofReal |f₁ x| * q₂ x' + ENNReal.ofReal |f₂ x| * q₁ x') + e x' := by
      intro x'
      have hd := torusL1Norm_nonneg (x' - x)
      have hbd : |(f₁ * f₂) x' - (f₁ * f₂) x| / torusL1Norm (x' - x) ≤
          (|f₁ x| * (|f₂ x' - f₂ x| / torusL1Norm (x' - x)) +
            |f₂ x| * (|f₁ x' - f₁ x| / torusL1Norm (x' - x))) + C₂ * |f₁ x' - f₁ x| := by
        have ha : |f₁ x'| ≤ |f₁ x| + |f₁ x' - f₁ x| := by
          simpa using abs_add_le (f₁ x) (f₁ x' - f₁ x)
        have hq := diffQuot_le_of_lipschitz hC₂ x x'
        calc |(f₁ * f₂) x' - (f₁ * f₂) x| / torusL1Norm (x' - x)
            ≤ (|f₁ x'| * |f₂ x' - f₂ x| + |f₂ x| * |f₁ x' - f₁ x|) / torusL1Norm (x' - x) :=
              div_le_div_of_nonneg_right (abs_mul_sub_mul_le_add _ _ _ _) hd
          _ = |f₁ x'| * (|f₂ x' - f₂ x| / torusL1Norm (x' - x)) +
                |f₂ x| * (|f₁ x' - f₁ x| / torusL1Norm (x' - x)) := by
              rw [add_div, mul_div_assoc, mul_div_assoc]
          _ ≤ (|f₁ x| + |f₁ x' - f₁ x|) * (|f₂ x' - f₂ x| / torusL1Norm (x' - x)) +
                |f₂ x| * (|f₁ x' - f₁ x| / torusL1Norm (x' - x)) := by
              gcongr
          _ = (|f₁ x| * (|f₂ x' - f₂ x| / torusL1Norm (x' - x)) +
                |f₂ x| * (|f₁ x' - f₁ x| / torusL1Norm (x' - x))) +
                |f₁ x' - f₁ x| * (|f₂ x' - f₂ x| / torusL1Norm (x' - x)) := by ring
          _ ≤ (|f₁ x| * (|f₂ x' - f₂ x| / torusL1Norm (x' - x)) +
                |f₂ x| * (|f₁ x' - f₁ x| / torusL1Norm (x' - x))) + C₂ * |f₁ x' - f₁ x| := by
              have := mul_le_mul_of_nonneg_left hq (abs_nonneg (f₁ x' - f₁ x))
              linarith
      refine (ENNReal.ofReal_le_ofReal hbd).trans_eq ?_
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_mul (abs_nonneg _)]
    have he0 : limsup e (𝓝[≠] x) = 0 :=
      ennreal_limsup_eq_zero_of_tendsto (tendsto_ofReal_mul_abs_sub_self hC₁ C₂ x)
    calc localLip (f₁ * f₂) x
        ≤ limsup (fun x' => (ENNReal.ofReal |f₁ x| * q₂ x' + ENNReal.ofReal |f₂ x| * q₁ x') + e x')
            (𝓝[≠] x) := limsup_le_limsup (Eventually.of_forall hpt)
      _ ≤ limsup (fun x' => ENNReal.ofReal |f₁ x| * q₂ x' + ENNReal.ofReal |f₂ x| * q₁ x')
            (𝓝[≠] x) + limsup e (𝓝[≠] x) := ennreal_limsup_add_le _ _
      _ = limsup (fun x' => ENNReal.ofReal |f₁ x| * q₂ x' + ENNReal.ofReal |f₂ x| * q₁ x')
            (𝓝[≠] x) := by rw [he0, add_zero]
      _ ≤ limsup (fun x' => ENNReal.ofReal |f₁ x| * q₂ x') (𝓝[≠] x) +
            limsup (fun x' => ENNReal.ofReal |f₂ x| * q₁ x') (𝓝[≠] x) :=
          ennreal_limsup_add_le _ _
      _ = ENNReal.ofReal |f₁ x| * localLip f₂ x +
            ENNReal.ofReal |f₂ x| * localLip f₁ x := by
          rw [ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top,
            ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
          rfl
theorem localLipRules_holds : LocalLipRules := by
  intro D
  exact ⟨fun A _ => localLip_distInftyToSet A,
    fun f hf => ⟨fun φ c hφ => localLip_comp hf hφ, fun x h => localLip_eq_zero_of_locally_const h⟩,
    fun f₁ f₂ h₁ h₂ => localLip_mul D.side_pos.ne' h₁ h₂⟩
end YangMills.Construction.Weighted.LocalLip

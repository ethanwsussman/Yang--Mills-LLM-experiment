import YangMills.Construction.ReflectionPositivity.ObservableAsAFunctionOfTheConfiguration
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.ObservableFnProof
open PeriodicLattice
variable (D : MirrorData)
theorem site_finite : Finite (PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)) := by
  have hL : (D.L : ℝ) ≠ 0 := by
    have hadm := D.isAdmissible.2
    exact_mod_cast (by omega : D.L ≠ 0)
  have hmesh : D.mesh ≠ 0 := zpow_ne_zero _ hL
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 2 * D.halfSideCount := ⟨_, rfl⟩
  have hNpos : 0 < N := by
    have hadm := D.isAdmissible.2
    have : 0 < D.halfSideCount := Nat.pow_pos (by omega)
    omega
  have hNmesh : (N : ℝ) * meshSize D.L ((D.K : ℕ) : ℤ) = torusSide D.L D.m := by
    have hq := D.side_div_mesh
    rw [div_eq_iff hmesh] at hq
    rw [hN]
    push_cast
    exact hq.symm
  have hNz : (0 : ℤ) < N := by exact_mod_cast hNpos
  let enc : (Fin 4 → Fin N) → PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ) := fun k =>
    ⟨fun μ => (((((k μ : ℕ) : ℤ) : ℝ) * meshSize D.L ((D.K : ℕ) : ℤ) : ℝ) : AddCircle (torusSide D.L D.m)),
      ⟨fun μ => ((k μ : ℕ) : ℤ), fun _ => rfl⟩⟩
  refine Finite.of_surjective enc ?_
  rintro ⟨x, n, hn⟩
  have hlt : ∀ μ, (n μ % (N : ℤ)).toNat < N := fun μ => by
    have hl := Int.emod_lt_of_pos (n μ) hNz
    have hr := Int.emod_nonneg (n μ) hNz.ne'
    omega
  refine ⟨fun μ => ⟨(n μ % (N : ℤ)).toNat, hlt μ⟩, Subtype.ext (funext fun μ => ?_)⟩
  have hwrap : (((n μ / (N : ℤ)) • torusSide D.L D.m : ℝ) : AddCircle (torusSide D.L D.m)) = 0 :=
    (AddCircle.coe_eq_zero_iff _).2 ⟨_, rfl⟩
  have hdecomp : ((n μ : ℤ) : ℝ) * meshSize D.L ((D.K : ℕ) : ℤ) =
      ((n μ % (N : ℤ) : ℤ) : ℝ) * meshSize D.L ((D.K : ℕ) : ℤ) +
        (n μ / (N : ℤ)) • torusSide D.L D.m := by
    have hcast := congrArg (Int.cast : ℤ → ℝ) (Int.emod_add_mul_ediv (n μ) (N : ℤ))
    push_cast at hcast
    rw [zsmul_eq_mul, ← hNmesh]
    linear_combination (-meshSize D.L ((D.K : ℕ) : ℤ)) * hcast
  change ((((((n μ % (N : ℤ)).toNat : ℕ) : ℤ) : ℝ) * meshSize D.L ((D.K : ℕ) : ℤ) : ℝ) :
    AddCircle (torusSide D.L D.m)) = x μ
  rw [hn μ, hdecomp, AddCircle.coe_add, hwrap, add_zero,
    Int.toNat_of_nonneg (Int.emod_nonneg _ hNz.ne')]
theorem plaquette_finite : Finite D.LatticePlaquette := by
  have := site_finite D
  exact Finite.of_injective (fun p : D.LatticePlaquette => (p.origin, p.firstAxis, p.secondAxis))
    fun p q hpq => by
      simp only [Prod.mk.injEq] at hpq
      exact Plaquette.ext hpq.1 hpq.2.1 hpq.2.2
theorem coe_inv_specialUnitary (v : Matrices.ComplexMatrix2.specialUnitary) :
    ((v⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      (v : Matrices.ComplexMatrix2)⁻¹ := by apply _root_.YangMills.Construction.InfiniteLattice.specialUnitary_coe_inv <;> assumption
theorem continuous_linkValue (b : D.LatticeBond) :
    Continuous[D.fieldTopology, inferInstance]
      fun U : D.LatticeGaugeField => U.1 b := by
  let := D.fieldTopology
  have hall : Continuous (D.linkValues {b : D.LatticeBond | b.IsPositivelyOriented}) :=
    continuous_induced_dom
  have hpos : ∀ (c : D.LatticeBond) (hc : c.IsPositivelyOriented),
      Continuous fun U : D.LatticeGaugeField =>
        D.linkValues {b : D.LatticeBond | b.IsPositivelyOriented} U ⟨c, hc⟩ := fun c hc =>
    (continuous_apply (⟨c, hc⟩ : {b : D.LatticeBond | b.IsPositivelyOriented})).comp hall
  obtain ⟨μ, hμ | hμ⟩ := b.isNeighbour
  · exact continuous_subtype_val.comp (hpos b ⟨μ, hμ⟩)
  · have hopp : b.opposite.IsPositivelyOriented := ⟨μ, by
      change b.source - b.target = _
      rw [← neg_sub, hμ, neg_neg]⟩
    have hinv : b.opposite.opposite = b := Bond.ext rfl rfl
    have hval : (fun U : D.LatticeGaugeField => U.1 b) = fun U =>
        (((D.linkValues {b : D.LatticeBond | b.IsPositivelyOriented} U ⟨b.opposite, hopp⟩)⁻¹ :
          Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) := by
      funext U
      rw [coe_inv_specialUnitary]
      have hU := U.2.2 b.opposite (mem_univ _)
      rw [hinv] at hU
      exact hU
    rw [hval]
    exact continuous_subtype_val.comp (hpos _ hopp).inv
theorem continuous_plaquetteEnergy (p : D.LatticePlaquette) :
    Continuous[D.fieldTopology, inferInstance]
      fun U : D.LatticeGaugeField => plaquetteCost U.1 p := by
  let := D.fieldTopology
  have e₁ := continuous_linkValue D (Bond.forwardFrom p.origin p.firstAxis)
  have e₂ := continuous_linkValue D
    (Bond.forwardFrom (p.origin + unitStep D.L D.m _ p.firstAxis) p.secondAxis)
  have e₃ := continuous_linkValue D
    (Bond.forwardFrom (p.origin + unitStep D.L D.m _ p.secondAxis) p.firstAxis).opposite
  have e₄ := continuous_linkValue D (Bond.forwardFrom p.origin p.secondAxis).opposite
  simp only [plaquetteCost, plaquetteHolonomy, pathHolonomy, Plaquette.boundaryBonds, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp
    (e₁.matrix_mul (e₂.matrix_mul (e₃.matrix_mul e₄))).matrix_trace))
theorem plaquetteEnergy_bounds (U : D.LatticeGaugeField) (p : D.LatticePlaquette) :
    0 ≤ plaquetteCost U.1 p ∧ plaquetteCost U.1 p ≤ 2 := by
  have hmem : plaquetteHolonomy U.1 p ∈ Matrices.ComplexMatrix2.specialUnitary := by
    apply Submonoid.list_prod_mem
    intro x hx
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
    exact U.2.1 b (mem_univ _)
  have hentry := fun i =>
    entry_norm_bound_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup hmem) i i
  have hd₀ := (Complex.abs_re_le_norm (plaquetteHolonomy U.1 p 0 0)).trans (hentry 0)
  have hd₁ := (Complex.abs_re_le_norm (plaquetteHolonomy U.1 p 1 1)).trans (hentry 1)
  have htr : |(Matrices.ComplexMatrix2.fullTrace (plaquetteHolonomy U.1 p)).re| ≤ 2 := by
    rw [Matrices.ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Complex.add_re]
    exact (abs_add_le _ _).trans (by linarith)
  have hab := abs_le.mp htr
  simp only [plaquetteCost]
  constructor <;> linarith [hab.1, hab.2]
theorem observableFn_eq_sum [Fintype D.LatticePlaquette] (f : D.Torus → ℝ)
    (U : D.LatticeGaugeField) :
    D.observableFn f U = ∑ p : D.LatticePlaquette, plaquetteCost U.1 p * f p.barycenter := by
  simp only [MirrorData.observableFn, smearedObservable, smul_eq_mul]
  exact finsum_eq_sum_of_fintype _
theorem continuous_observableFn (f : D.Torus → ℝ) :
    Continuous[D.fieldTopology, inferInstance] (D.observableFn f) := by
  let := D.fieldTopology
  have := plaquette_finite D
  let := Fintype.ofFinite D.LatticePlaquette
  have hsum : D.observableFn f = fun U =>
      ∑ p : D.LatticePlaquette, plaquetteCost U.1 p * f p.barycenter :=
    funext (observableFn_eq_sum D f)
  rw [hsum]
  exact continuous_finsetSum _ fun p _ => (continuous_plaquetteEnergy D p).mul continuous_const
theorem abs_observableFn_le (f : D.Torus → ℝ) (U : D.LatticeGaugeField) :
    |D.observableFn f U| ≤ 2 * ∑ᶠ p : D.LatticePlaquette, |f p.barycenter| := by
  have := plaquette_finite D
  let := Fintype.ofFinite D.LatticePlaquette
  rw [observableFn_eq_sum, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  have hb := plaquetteEnergy_bounds D U p
  rw [abs_mul, abs_of_nonneg hb.1]
  exact mul_le_mul_of_nonneg_right hb.2 (abs_nonneg _)
theorem measurable_of_continuous_field (F : D.LatticeGaugeField → ℝ)
    (hF : Continuous[D.fieldTopology, inferInstance] F) :
    Measurable[@borel _ D.fieldTopology] F := by
  let := D.fieldTopology
  let : MeasurableSpace D.LatticeGaugeField := borel _
  have : BorelSpace D.LatticeGaugeField := ⟨rfl⟩
  exact hF.measurable
theorem centeredProducts_boundedBorel (n : ℕ) : D.CenteredProductsBoundedBorel n := by
  intro f α
  refine ⟨measurable_of_continuous_field D _ ?_, ∏ i, (2 * ∑ᶠ p : D.LatticePlaquette,
    |f i p.barycenter| + |α i|), fun U => ?_⟩
  · let := D.fieldTopology
    exact continuous_finsetProd _ fun i _ => (continuous_observableFn D (f i)).sub continuous_const
  · rw [Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ =>
      (abs_sub _ _).trans (add_le_add (abs_observableFn_le D (f i) U) le_rfl)
theorem observableFn_linear (f g : D.Torus → ℝ) (t : ℝ) : D.ObservableLinear f g t := by
  have := plaquette_finite D
  let := Fintype.ofFinite D.LatticePlaquette
  funext U
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, observableFn_eq_sum]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring
theorem observableFnFacts_holds : ObservableFnFacts := fun D =>
  ⟨plaquette_finite D, fun f => ⟨continuous_observableFn D f, abs_observableFn_le D f⟩,
    fun f => ⟨measurable_of_continuous_field D _ (continuous_observableFn D f),
      2 * ∑ᶠ p : D.LatticePlaquette, |f p.barycenter|,
      fun U => by rw [Real.norm_eq_abs]; exact abs_observableFn_le D f U⟩,
    centeredProducts_boundedBorel D, observableFn_linear D⟩
end YangMills.Construction.ReflectionPositivity.AxisMirror.ObservableFnProof

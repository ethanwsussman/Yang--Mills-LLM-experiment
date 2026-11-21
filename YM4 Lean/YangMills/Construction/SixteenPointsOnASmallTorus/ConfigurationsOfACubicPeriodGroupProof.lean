import YangMills.Construction.ClusterExpansionOfAStep.UnitQuaternionsAreTheMatrixGroup
import YangMills.Construction.SixteenPointsOnASmallTorus.ConfigurationsOfACubicPeriodGroup
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Quaternion
namespace YangMills.Construction.SmallTorusCopies
namespace CubicPeriodFields
private structure PeriodFit (L : ℕ) (κ : ℤ) (ℓ : Fin 4 → ℝ) (m : ℕ) : Prop where
  period : ∀ μ, (m : ℝ) * PeriodicLattice.meshSize L κ = ℓ μ
  mesh_ne_zero : PeriodicLattice.meshSize L κ ≠ 0
  three_le : 3 ≤ m
variable {L : ℕ} {κ : ℤ} {ℓ : Fin 4 → ℝ} {m : ℕ}
private def circleEmbed (h : PeriodFit L κ ℓ m) (μ : Fin 4) : ZMod m →+ AddCircle (ℓ μ) :=
  ZMod.lift m ⟨zmultiplesHom _ (PeriodicLattice.meshSize L κ : AddCircle (ℓ μ)), by
    rw [zmultiplesHom_apply, ← AddCircle.coe_zsmul, zsmul_eq_mul, Int.cast_natCast, h.period μ]
    exact AddCircle.coe_period _⟩
private theorem circleEmbed_intCast (h : PeriodFit L κ ℓ m) (μ : Fin 4) (n : ℤ) :
    circleEmbed h μ (n : ZMod m) = (((n : ℝ) * PeriodicLattice.meshSize L κ : ℝ) : AddCircle (ℓ μ)) := by
  rw [circleEmbed, ZMod.lift_coe, zmultiplesHom_apply, ← AddCircle.coe_zsmul, zsmul_eq_mul]
private theorem circleEmbed_injective (h : PeriodFit L κ ℓ m) (μ : Fin 4) :
    Function.Injective (circleEmbed h μ) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  rw [← ZMod.intCast_zmod_cast x, circleEmbed_intCast] at hx
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).mp hx
  rw [zsmul_eq_mul, ← h.period μ, ← mul_assoc] at hk
  have e : (k : ℝ) * m = ((x.cast : ℤ) : ℝ) := mul_right_cancel₀ h.mesh_ne_zero hk
  have e' : k * (m : ℤ) = (x.cast : ℤ) := by exact_mod_cast e
  rw [← ZMod.intCast_zmod_cast x]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨k, by rw [← e', mul_comm]⟩
private def siteMap (h : PeriodFit L κ ℓ m) : TorusFields.TorusSite m →+ BoxTorus.GridPoint L κ ℓ where
  toFun x := ⟨fun μ => circleEmbed h μ (x μ), fun μ => ((x μ).cast : ℤ), by
    refine funext fun μ => ?_
    have e := circleEmbed_intCast h μ ((x μ).cast : ℤ)
    rw [ZMod.intCast_zmod_cast] at e
    exact e⟩
  map_zero' := Subtype.ext (funext fun μ => map_zero (circleEmbed h μ))
  map_add' x y := Subtype.ext (funext fun μ => map_add (circleEmbed h μ) (x μ) (y μ))
private theorem siteMap_apply (h : PeriodFit L κ ℓ m) (x : TorusFields.TorusSite m) (μ : Fin 4) :
    (siteMap h x : BoxTorus.Space ℓ) μ = circleEmbed h μ (x μ) := rfl
private theorem siteMap_injective (h : PeriodFit L κ ℓ m) : Function.Injective (siteMap h) := by
  intro x y hxy
  funext μ
  exact circleEmbed_injective h μ (congrFun (congrArg Subtype.val hxy) μ)
private theorem siteMap_surjective (h : PeriodFit L κ ℓ m) : Function.Surjective (siteMap h) := by
  rintro ⟨_, n, rfl⟩
  refine ⟨fun μ => (n μ : ZMod m), Subtype.ext (funext fun μ => ?_)⟩
  exact circleEmbed_intCast h μ (n μ)
private theorem circleEmbed_one (h : PeriodFit L κ ℓ m) (μ : Fin 4) :
    circleEmbed h μ (1 : ZMod m) = (PeriodicLattice.meshSize L κ : AddCircle (ℓ μ)) := by
  simpa using circleEmbed_intCast h μ 1
private theorem siteMap_unitStep (h : PeriodFit L κ ℓ m) (μ : Fin 4) :
    siteMap h (TorusFields.unitStep m μ) = BoxTorus.gridStep L κ ℓ μ := by
  refine Subtype.ext (funext fun ν => ?_)
  rw [siteMap_apply]
  change circleEmbed h ν (TorusFields.unitStep m μ ν) =
    (((PeriodicLattice.meshSize L κ • BoxTorus.basisVector μ) ν : ℝ) : AddCircle (ℓ ν))
  by_cases e : ν = μ
  · subst e
    simp [TorusFields.unitStep, BoxTorus.basisVector, circleEmbed_one]
  · simp [TorusFields.unitStep, BoxTorus.basisVector, Pi.single_eq_of_ne e]
private theorem zmod_one_ne_zero (h : PeriodFit L κ ℓ m) : (1 : ZMod m) ≠ 0 := by
  intro e
  have := (ZMod.natCast_eq_zero_iff 1 m).mp (by simpa using e)
  have := Nat.le_of_dvd one_pos this
  have := h.three_le
  omega
private theorem axis_eq_of_gridStep_eq (h : PeriodFit L κ ℓ m) {μ ν : Fin 4}
    (e : BoxTorus.gridStep L κ ℓ μ = BoxTorus.gridStep L κ ℓ ν) : ν = μ := by
  by_contra hne
  have hev : TorusFields.unitStep m ν μ = 0 := by simp [TorusFields.unitStep, Pi.single_eq_of_ne (Ne.symm hne)]
  have h1 : TorusFields.unitStep m μ μ = 1 := by simp [TorusFields.unitStep]
  rw [← siteMap_unitStep h, ← siteMap_unitStep h] at e
  have := congrFun (siteMap_injective h e) μ
  rw [hev, h1] at this
  exact zmod_one_ne_zero h this
private theorem edgeFrom_isForward (x : BoxTorus.GridPoint L κ ℓ) (μ : Fin 4) :
    (BoxTorus.edgeFrom x μ).IsForward :=
  ⟨μ, Or.inl rfl, by simp [BoxTorus.edgeFrom, BoxTorus.translate, BoxTorus.gridStep]⟩
private def forwardEdgeEquiv (h : PeriodFit L κ ℓ m) :
    TorusFields.TorusSite m × Fin 4 ≃ BoxTorus.ForwardEdge L κ ℓ :=
  Equiv.ofBijective
    (fun p => ⟨BoxTorus.edgeFrom (siteMap h p.1) p.2, edgeFrom_isForward _ _⟩)
    (by
      constructor
      · rintro ⟨x, μ⟩ ⟨y, ν⟩ e
        have e1 : BoxTorus.edgeFrom (siteMap h x) μ = BoxTorus.edgeFrom (siteMap h y) ν :=
          congrArg Subtype.val e
        have et : siteMap h x = siteMap h y := congrArg BoxTorus.DirectedEdge.source e1
        have eh : siteMap h x + BoxTorus.gridStep L κ ℓ μ = siteMap h y + BoxTorus.gridStep L κ ℓ ν :=
          congrArg BoxTorus.DirectedEdge.target e1
        rw [et] at eh
        obtain rfl := axis_eq_of_gridStep_eq h (add_left_cancel eh)
        rw [siteMap_injective h et]
      · rintro ⟨b, μ, hμ⟩
        obtain ⟨x, hx⟩ := siteMap_surjective h b.source
        refine ⟨(x, μ), Subtype.ext (BoxTorus.DirectedEdge.ext hx ?_)⟩
        change siteMap h x + BoxTorus.gridStep L κ ℓ μ = b.target
        rw [hx]
        refine Subtype.ext ?_
        rw [hμ.2]
        simp [BoxTorus.translate, BoxTorus.gridStep])
private def toTorusField (h : PeriodFit L κ ℓ m) (U : BoxTorus.GaugeConfig L κ ℓ) : TorusFields.TorusField m :=
  fun x μ => ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary.symm (U (forwardEdgeEquiv h (x, μ)))
private def toGaugeConfig (h : PeriodFit L κ ℓ m) (W : TorusFields.TorusField m) : BoxTorus.GaugeConfig L κ ℓ :=
  fun b => ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary
    (W ((forwardEdgeEquiv h).symm b).1 ((forwardEdgeEquiv h).symm b).2)
private theorem toGaugeConfig_edge (h : PeriodFit L κ ℓ m) (W : TorusFields.TorusField m)
    (x : TorusFields.TorusSite m) (μ : Fin 4) :
    toGaugeConfig h W (forwardEdgeEquiv h (x, μ)) = ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary (W x μ) := by
  simp [toGaugeConfig]
private theorem toTorusField_toGaugeConfig (h : PeriodFit L κ ℓ m) (W : TorusFields.TorusField m) :
    toTorusField h (toGaugeConfig h W) = W := by
  funext x μ
  simp [toTorusField, toGaugeConfig_edge]
private theorem measurable_unitEquiv :
    Measurable (ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary :
      BlockAverages.UnitQuaternion → Matrices.ComplexMatrix2.specialUnitary) :=
  (map_continuous ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary).measurable
private theorem measurable_unitEquiv_symm :
    Measurable (ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary.symm :
      Matrices.ComplexMatrix2.specialUnitary → BlockAverages.UnitQuaternion) :=
  (map_continuous ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary.symm).measurable
private theorem measurable_toTorusField (h : PeriodFit L κ ℓ m) : Measurable (toTorusField h) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_iff.mpr fun _ =>
    measurable_unitEquiv_symm.comp (measurable_pi_apply _)
private theorem measurable_toGaugeConfig (h : PeriodFit L κ ℓ m) : Measurable (toGaugeConfig h) :=
  measurable_pi_iff.mpr fun _ =>
    measurable_unitEquiv.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))
private theorem map_fieldHaar (h : PeriodFit L κ ℓ m) [NeZero m]
    (hU : TorusFields.haarUnit.map ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary = Matrices.ComplexMatrix2.haarProb) :
    (TorusFields.fieldHaar m).map (toGaugeConfig h) = BoxTorus.haarConfigMeasure L κ ℓ := by
  classical
  have hfin : Finite (BoxTorus.ForwardEdge L κ ℓ) := Finite.of_equiv _ (forwardEdgeEquiv h)
  let _ : Fintype (BoxTorus.ForwardEdge L κ ℓ) := Fintype.ofFinite _
  have hG : ∀ A : Set Matrices.ComplexMatrix2.specialUnitary, MeasurableSet A →
      TorusFields.haarUnit (ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary ⁻¹' A) = Matrices.ComplexMatrix2.haarProb A :=
    fun A hA => by rw [← hU, Measure.map_apply measurable_unitEquiv hA]
  unfold BoxTorus.haarConfigMeasure Matrices.ComplexMatrix2.haarPi
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  set t' : BoxTorus.ForwardEdge L κ ℓ → Set Matrices.ComplexMatrix2.specialUnitary :=
    fun b => if b ∈ s then t b else univ with ht'def
  have ht' : ∀ b, MeasurableSet (t' b) := by
    intro b
    by_cases hb : b ∈ s
    · simpa [ht'def, hb] using ht b
    · simp [ht'def, hb]
  have ebox : (s : Set (BoxTorus.ForwardEdge L κ ℓ)).pi t = univ.pi t' := by
    ext v
    simp only [Set.mem_pi, Finset.mem_coe, mem_univ, true_imp_iff]
    constructor
    · intro hv b
      by_cases hb : b ∈ s
      · simpa [ht'def, hb] using hv b hb
      · simp [ht'def, hb]
    · intro hv b hb
      simpa [ht'def, hb] using hv b
  have epre : toGaugeConfig h ⁻¹' univ.pi t' =
      univ.pi fun x : TorusFields.TorusSite m => univ.pi fun i : Fin 4 =>
        ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary ⁻¹' t' (forwardEdgeEquiv h (x, i)) := by
    ext W
    simp only [Set.mem_preimage, Set.mem_pi, mem_univ, true_imp_iff]
    constructor
    · intro hW x i
      rw [← toGaugeConfig_edge h W]
      exact hW _
    · intro hW b
      obtain ⟨⟨x, i⟩, rfl⟩ := (forwardEdgeEquiv h).surjective b
      rw [toGaugeConfig_edge h W]
      exact hW x i
  rw [ebox, Measure.map_apply (measurable_toGaugeConfig h) (MeasurableSet.univ_pi ht'), epre]
  unfold TorusFields.fieldHaar
  rw [Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  simp_rw [hG _ (ht' _)]
  rw [← Fintype.prod_prod_type' (fun (x : TorusFields.TorusSite m) (i : Fin 4) =>
    Matrices.ComplexMatrix2.haarProb (t' (forwardEdgeEquiv h (x, i))))]
  rw [Equiv.prod_comp (forwardEdgeEquiv h) (fun b => Matrices.ComplexMatrix2.haarProb (t' b))]
  rw [← Finset.prod_subset (Finset.subset_univ s) (fun b _ hb => by simp [ht'def, hb])]
  exact Finset.prod_congr rfl fun b hb => by simp [ht'def, hb]
private theorem measurePreserving_toTorusField (h : PeriodFit L κ ℓ m) [NeZero m]
    (hU : TorusFields.haarUnit.map ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary = Matrices.ComplexMatrix2.haarProb) :
    MeasurePreserving (toTorusField h) (BoxTorus.haarConfigMeasure L κ ℓ) (TorusFields.fieldHaar m) := by
  refine ⟨measurable_toTorusField h, ?_⟩
  rw [← map_fieldHaar h hU, Measure.map_map (measurable_toTorusField h) (measurable_toGaugeConfig h)]
  have e : toTorusField h ∘ toGaugeConfig h = id := funext (toTorusField_toGaugeConfig h)
  rw [e, Measure.map_id]
private theorem edgeVariable_edgeFrom (h : PeriodFit L κ ℓ m) (U : BoxTorus.GaugeConfig L κ ℓ)
    (x : TorusFields.TorusSite m) (μ : Fin 4) :
    BoxTorus.edgeVariable U (BoxTorus.edgeFrom (siteMap h x) μ) =
      ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary (toTorusField h U x μ) := by
  rw [BoxTorus.edgeVariable, dif_pos (edgeFrom_isForward _ _), toTorusField,
    ContinuousMulEquiv.apply_symm_apply]
  rfl
private theorem faceHolonomy_eq (h : PeriodFit L κ ℓ m) (U : BoxTorus.GaugeConfig L κ ℓ)
    (x : TorusFields.TorusSite m) {μ ν : Fin 4} (hμν : μ < ν) :
    BoxTorus.faceHolonomy U ⟨siteMap h x, μ, ν, hμν⟩ =
      ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary (TorusFields.holonomy (toTorusField h U) x μ ν) := by
  have e₁ : siteMap h x + BoxTorus.gridStep L κ ℓ μ = siteMap h (x + TorusFields.unitStep m μ) := by
    rw [map_add, siteMap_unitStep]
  have e₂ : siteMap h x + BoxTorus.gridStep L κ ℓ ν = siteMap h (x + TorusFields.unitStep m ν) := by
    rw [map_add, siteMap_unitStep]
  simp only [BoxTorus.faceHolonomy, e₁, e₂, edgeVariable_edgeFrom, TorusFields.holonomy, map_mul, map_inv]
private theorem faceEnergy_eq (hU : ∀ u : BlockAverages.UnitQuaternion,
      (u : ℍ[ℝ]).re = (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
        (ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary u : Matrices.ComplexMatrix2)).re)
    (h : PeriodFit L κ ℓ m) (U : BoxTorus.GaugeConfig L κ ℓ)
    (x : TorusFields.TorusSite m) {μ ν : Fin 4} (hμν : μ < ν) :
    BoxTorus.faceEnergy U ⟨siteMap h x, μ, ν, hμν⟩ =
      TorusFields.plaquetteEnergy (toTorusField h U) x μ ν := by
  rw [BoxTorus.faceEnergy, faceHolonomy_eq, TorusFields.plaquetteEnergy, hU]
private def faceEquiv (h : PeriodFit L κ ℓ m) :
    WeightedResponses.OrientedPlaquette m ≃ BoxTorus.Face L κ ℓ :=
  Equiv.ofBijective (fun p => ⟨siteMap h p.1.1, p.1.2.1, p.1.2.2, p.2⟩)
    (by
      constructor
      · rintro ⟨⟨x, μ, ν⟩, hp⟩ ⟨⟨y, μ', ν'⟩, hq⟩ e
        have e1 : siteMap h x = siteMap h y := congrArg BoxTorus.Face.corner e
        have e2 : μ = μ' := congrArg BoxTorus.Face.dir₁ e
        have e3 : ν = ν' := congrArg BoxTorus.Face.dir₂ e
        subst e2 e3
        rw [siteMap_injective h e1]
      · rintro ⟨b, μ, ν, hμν⟩
        obtain ⟨x, rfl⟩ := siteMap_surjective h b
        exact ⟨⟨(x, μ, ν), hμν⟩, rfl⟩)
private theorem wilsonAction_eq (hU : ∀ u : BlockAverages.UnitQuaternion,
      (u : ℍ[ℝ]).re = (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
        (ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary u : Matrices.ComplexMatrix2)).re)
    (h : PeriodFit L κ ℓ m) [NeZero m] (U : BoxTorus.GaugeConfig L κ ℓ) :
    BoxTorus.wilsonAction U = TorusFields.wilsonAction Finset.univ (toTorusField h U) := by
  classical
  rw [BoxTorus.wilsonAction, ← finsum_comp_equiv (faceEquiv h), finsum_eq_sum_of_fintype, TorusFields.wilsonAction,
    Finset.sum_subtype (TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite m)))
      (p := fun p : TorusFields.TorusPlaquette m => p.2.1 < p.2.2)
      (fun p => by simp [TorusFields.plaquettesIn])]
  exact Finset.sum_congr rfl fun p _ => faceEnergy_eq hU h U p.1.1 p.2
private theorem circleEmbed_add_halfMesh (h : PeriodFit L κ ℓ m) [NeZero m] (i : Fin 4) (v : ZMod m) (d : ℕ) :
    circleEmbed h i v + ((PeriodicLattice.meshSize L κ / 2 * (d : ℝ) : ℝ) : AddCircle (ℓ i)) =
      ((PeriodicLattice.meshSize L κ / 2 * ((((2 * v.val + d : ℕ) : ZMod (2 * m)).val : ℕ) : ℝ) : ℝ) :
        AddCircle (ℓ i)) := by
  have hv : circleEmbed h i v = (((v.val : ℝ) * PeriodicLattice.meshSize L κ : ℝ) : AddCircle (ℓ i)) := by
    have := circleEmbed_intCast h i (v.val : ℤ)
    simpa using this
  rw [hv, ← AddCircle.coe_add, ZMod.val_natCast]
  set c := 2 * v.val + d with hc
  have hdiv : 2 * m * (c / (2 * m)) + c % (2 * m) = c := Nat.div_add_mod _ _
  have hr : (v.val : ℝ) * PeriodicLattice.meshSize L κ + PeriodicLattice.meshSize L κ / 2 * (d : ℝ) =
      PeriodicLattice.meshSize L κ / 2 * ((c % (2 * m) : ℕ) : ℝ) + ((c / (2 * m) : ℕ) : ℝ) * ℓ i := by
    have hcr : (c : ℝ) = 2 * (m : ℝ) * ((c / (2 * m) : ℕ) : ℝ) + ((c % (2 * m) : ℕ) : ℝ) := by
      exact_mod_cast hdiv.symm
    have hcv : (c : ℝ) = 2 * (v.val : ℝ) + (d : ℝ) := by rw [hc]; push_cast; ring
    rw [← h.period i]
    have : (v.val : ℝ) * 2 + (d : ℝ) = 2 * (m : ℝ) * ((c / (2 * m) : ℕ) : ℝ) + ((c % (2 * m) : ℕ) : ℝ) := by
      rw [← hcr, hcv]; ring
    linear_combination (PeriodicLattice.meshSize L κ / 2) * this
  rw [hr, AddCircle.coe_add, ← nsmul_eq_mul, AddCircle.coe_nsmul, AddCircle.coe_period, smul_zero, add_zero]
end CubicPeriodFields
open CubicPeriodFields in
theorem cubicPeriodFieldsStatement_holds (hU : ClusterExpansionOfAStep.UnitQuaternionHaarTraceNorm) :
    cubicPeriodFieldsStatement := by
  intro D P m _ hP
  have ha : PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ) = D.mesh := rfl
  have hL : (D.L : ℝ) ≠ 0 := by
    have := D.isAdmissible.2
    have : D.L ≠ 0 := by omega
    exact_mod_cast this
  have h : PeriodFit D.L ((D.K : ℕ) : ℤ) P.sideLengths m :=
    { period := fun μ => by
        change (m : ℝ) * _ = ((P.mult μ : ℤ) : ℝ) * D.mesh
        rw [hP μ, ha]
        push_cast
        rfl
      mesh_ne_zero := zpow_ne_zero _ hL
      three_le := by
        have h4 := P.four_le_mult 0
        rw [hP 0] at h4
        have : (4 : ℕ) ≤ m := by exact_mod_cast h4
        omega }
  refine ⟨toTorusField h, faceEquiv h, measurePreserving_toTorusField h hU.1,
    fun U => wilsonAction_eq (fun u => (hU.2.1 u).1) h U,
    fun U p => ⟨faceEnergy_eq (fun u => (hU.2.1 u).1) h U p.1.1 p.2, ?_⟩⟩
  refine funext fun i => ?_
  obtain ⟨⟨x, μ, ν⟩, hμν⟩ := p
  change circleEmbed h i (x i) + (((((D.mesh / 2) • (BoxTorus.basisVector μ + BoxTorus.basisVector ν) :
      Fin 4 → ℝ)) i : ℝ) : AddCircle (P.sideLengths i)) =
    ((D.mesh / 2 * (((WeightedResponses.doubledBarycentre (x, μ, ν) i).val : ℕ) : ℝ) : ℝ) : AddCircle (P.sideLengths i))
  have e := circleEmbed_add_halfMesh h i (x i) ((if i = μ then 1 else 0) + (if i = ν then 1 else 0))
  rw [ha] at e
  have e₁ : ((((D.mesh / 2) • (BoxTorus.basisVector μ + BoxTorus.basisVector ν) : Fin 4 → ℝ)) i : ℝ) =
      D.mesh / 2 * ((((if i = μ then 1 else 0) + (if i = ν then 1 else 0) : ℕ)) : ℝ) := by
    simp only [BoxTorus.basisVector, Pi.smul_apply, Pi.add_apply, Pi.single_apply, smul_eq_mul]
    push_cast
    rfl
  have e₂ : WeightedResponses.doubledBarycentre (x, μ, ν) i =
      ((2 * (x i).val + ((if i = μ then 1 else 0) + (if i = ν then 1 else 0)) : ℕ) : ZMod (2 * m)) := by
    rw [WeightedResponses.doubledBarycentre, add_assoc]
  rw [e₁, e₂]
  exact e
end YangMills.Construction.SmallTorusCopies
end

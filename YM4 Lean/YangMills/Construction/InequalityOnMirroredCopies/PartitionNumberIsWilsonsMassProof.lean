import YangMills.Construction.ClusterExpansionOfAStep.UnitQuaternionsAreTheMatrixGroup
import YangMills.Construction.InequalityOnMirroredCopies.PartitionNumberIsWilsonsMass
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction.ReflectedCopies
open ChessboardTori
namespace TorusPartitionProof
open BoxTorus
open TorusFields (TorusSite TorusField TorusPlaquette unitStep holonomy plaquetteEnergy plaquettesIn fieldHaar
  haarUnit)
open ClusterExpansionOfAStep (unitQuaternionEquivSpecialUnitary wilsonPartition)
open TorusLumps (wilsonWeight)
open PeriodicLattice (meshSize)
variable {L : ℕ} {κ : ℤ} {ℓ : Fin 4 → ℝ} {m : ℕ}
private def gridPointOfInt (L : ℕ) (κ : ℤ) (ℓ : Fin 4 → ℝ) (p : Fin 4 → ℤ) : GridPoint L κ ℓ :=
  ⟨projection ℓ fun μ => (p μ : ℝ) * meshSize L κ, ⟨p, rfl⟩⟩
private theorem coe_intMul_eq_iff {c a : ℝ} (hc : c = (m : ℝ) * a) (ha : 0 < a) (x y : ℤ) :
    (((x : ℝ) * a : ℝ) : AddCircle c) = (((y : ℝ) * a : ℝ) : AddCircle c) ↔ (x : ZMod m) = (y : ZMod m) := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff, ← sub_eq_zero (a := (x : ZMod m)),
    ← Int.cast_sub, CharP.intCast_eq_zero_iff (ZMod m) m]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, hc] at hk
    have hmul : ((x : ℝ) - y) * a = ((m : ℝ) * k) * a := by
      rw [sub_mul, ← hk]; ring
    have hcast : ((x - y : ℤ) : ℝ) = ((m * k : ℤ) : ℝ) := by
      push_cast
      exact mul_right_cancel₀ ha.ne' hmul
    exact_mod_cast hcast
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, hc]
    have hdiff : ((x : ℝ) - y) = (m : ℝ) * k := by exact_mod_cast hk
    rw [← sub_mul, hdiff]
    ring
private theorem gridPointOfInt_eq_iff (hℓ : ∀ μ, ℓ μ = (m : ℝ) * meshSize L κ) (hs : 0 < meshSize L κ)
    (p q : Fin 4 → ℤ) :
    gridPointOfInt L κ ℓ p = gridPointOfInt L κ ℓ q ↔ ∀ μ, (p μ : ZMod m) = (q μ : ZMod m) := by
  constructor
  · intro h μ
    have h' : projection ℓ (fun μ => (p μ : ℝ) * meshSize L κ) =
        projection ℓ (fun μ => (q μ : ℝ) * meshSize L κ) := congrArg Subtype.val h
    exact (coe_intMul_eq_iff (hℓ μ) hs _ _).mp (congrFun h' μ)
  · intro h
    refine Subtype.ext ?_
    funext μ
    exact (coe_intMul_eq_iff (hℓ μ) hs _ _).mpr (h μ)
private theorem gridPointOfInt_add (p q : Fin 4 → ℤ) :
    gridPointOfInt L κ ℓ p + gridPointOfInt L κ ℓ q = gridPointOfInt L κ ℓ (p + q) := by
  refine Subtype.ext ?_
  change projection ℓ _ + projection ℓ _ = projection ℓ _
  rw [← map_add]
  congr 1
  funext μ
  simp [add_mul]
private theorem gridStep_eq (ν : Fin 4) : gridStep L κ ℓ ν = gridPointOfInt L κ ℓ (Pi.single ν 1) := by
  refine Subtype.ext ?_
  change projection ℓ _ = projection ℓ _
  congr 1
  funext μ
  by_cases h : μ = ν
  · subst h
    simp [BoxTorus.basisVector]
  · simp [BoxTorus.basisVector, Pi.single_eq_of_ne h]
private def gridPointOf (L : ℕ) (κ : ℤ) (ℓ : Fin 4 → ℝ) (x : TorusSite m) : GridPoint L κ ℓ :=
  gridPointOfInt L κ ℓ fun μ => ((x μ).cast : ℤ)
private theorem gridPointOf_add_unitStep (hℓ : ∀ μ, ℓ μ = (m : ℝ) * meshSize L κ) (hs : 0 < meshSize L κ)
    (x : TorusSite m) (ν : Fin 4) :
    gridPointOf L κ ℓ (x + unitStep m ν) = gridPointOf L κ ℓ x + gridStep L κ ℓ ν := by
  rw [gridStep_eq, gridPointOf, gridPointOf, gridPointOfInt_add, gridPointOfInt_eq_iff hℓ hs]
  intro μ
  simp only [Pi.add_apply, Int.cast_add, ZMod.intCast_zmod_cast]
  congr 1
  by_cases h : μ = ν
  · subst h
    simp [TorusFields.unitStep]
  · simp [TorusFields.unitStep, Pi.single_eq_of_ne h]
private theorem gridPointOf_injective (hℓ : ∀ μ, ℓ μ = (m : ℝ) * meshSize L κ) (hs : 0 < meshSize L κ) :
    Function.Injective (gridPointOf (m := m) L κ ℓ) := by
  intro x y h
  funext μ
  have := (gridPointOfInt_eq_iff hℓ hs _ _).mp h μ
  simpa only [ZMod.intCast_zmod_cast] using this
private theorem gridPointOf_surjective (hℓ : ∀ μ, ℓ μ = (m : ℝ) * meshSize L κ) (hs : 0 < meshSize L κ) :
    Function.Surjective (gridPointOf (m := m) L κ ℓ) := by
  rintro ⟨_, p, rfl⟩
  refine ⟨fun μ => (p μ : ZMod m), ?_⟩
  refine (gridPointOfInt_eq_iff hℓ hs _ p).mpr fun μ => ?_
  simp only [ZMod.intCast_zmod_cast]
private theorem edgeFrom_isForward (s : GridPoint L κ ℓ) (ν : Fin 4) : (edgeFrom s ν).IsForward :=
  ⟨ν, Or.inl rfl, by simp [edgeFrom, BoxTorus.translate, gridStep]⟩
private def forwardEdgeOf (L : ℕ) (κ : ℤ) (ℓ : Fin 4 → ℝ) (p : TorusSite m × Fin 4) : ForwardEdge L κ ℓ :=
  ⟨edgeFrom (gridPointOf L κ ℓ p.1) p.2, edgeFrom_isForward _ _⟩
private theorem forwardEdgeOf_bijective (hℓ : ∀ μ, ℓ μ = (m : ℝ) * meshSize L κ) (hs : 0 < meshSize L κ)
    (hm : 1 < m) : Function.Bijective (forwardEdgeOf (m := m) L κ ℓ) := by
  constructor
  · rintro ⟨x, μ⟩ ⟨y, ν⟩ h
    have hsrc : gridPointOf L κ ℓ x = gridPointOf L κ ℓ y :=
      congrArg (fun b : ForwardEdge L κ ℓ => b.1.source) h
    have htgt : gridPointOf L κ ℓ x + gridStep L κ ℓ μ = gridPointOf L κ ℓ y + gridStep L κ ℓ ν :=
      congrArg (fun b : ForwardEdge L κ ℓ => b.1.target) h
    have hx := gridPointOf_injective hℓ hs hsrc
    subst hx
    have hst : gridStep L κ ℓ μ = gridStep L κ ℓ ν := add_left_cancel htgt
    rw [gridStep_eq, gridStep_eq, gridPointOfInt_eq_iff hℓ hs] at hst
    have hμν : μ = ν := by
      by_contra hne
      have hcoord := hst μ
      have : Fact (1 < m) := ⟨hm⟩
      simp [Pi.single_eq_of_ne hne] at hcoord
    subst hμν
    rfl
  · rintro ⟨b, ν, -, hb⟩
    obtain ⟨x, hx⟩ := gridPointOf_surjective (m := m) hℓ hs b.source
    refine ⟨(x, ν), Subtype.ext (DirectedEdge.ext hx ?_)⟩
    refine Subtype.ext ?_
    change ((gridPointOf L κ ℓ x + gridStep L κ ℓ ν : GridPoint L κ ℓ) : Space ℓ) = _
    rw [hx, hb]
    simp [BoxTorus.translate, gridStep]
private def forwardEdgeEquiv (hℓ : ∀ μ, ℓ μ = (m : ℝ) * meshSize L κ) (hs : 0 < meshSize L κ) (hm : 1 < m) :
    TorusSite m × Fin 4 ≃ ForwardEdge L κ ℓ :=
  Equiv.ofBijective _ (forwardEdgeOf_bijective hℓ hs hm)
private def fieldToConfig (e : TorusSite m × Fin 4 ≃ ForwardEdge L κ ℓ) : TorusField m ≃ᵐ GaugeConfig L κ ℓ where
  toFun W b := unitQuaternionEquivSpecialUnitary (W (e.symm b).1 (e.symm b).2)
  invFun U x μ := unitQuaternionEquivSpecialUnitary.symm (U (e (x, μ)))
  left_inv W := by
    funext x μ
    simp
  right_inv U := by
    funext b
    simp
  measurable_toFun := by
    refine measurable_pi_iff.mpr fun b => ?_
    exact unitQuaternionEquivSpecialUnitary.continuous.measurable.comp
      ((measurable_pi_apply _).comp (measurable_pi_apply _))
  measurable_invFun := by
    refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun μ => ?_
    exact unitQuaternionEquivSpecialUnitary.symm.continuous.measurable.comp (measurable_pi_apply _)
private theorem fieldToConfig_apply (e : TorusSite m × Fin 4 ≃ ForwardEdge L κ ℓ) (W : TorusField m)
    (x : TorusSite m) (μ : Fin 4) :
    fieldToConfig e W (e (x, μ)) = unitQuaternionEquivSpecialUnitary (W x μ) := by
  change unitQuaternionEquivSpecialUnitary (W (e.symm (e (x, μ))).1 (e.symm (e (x, μ))).2) = _
  simp
private theorem map_fieldHaar [NeZero m]
    (hmap : haarUnit.map unitQuaternionEquivSpecialUnitary = Matrices.ComplexMatrix2.haarProb)
    (e : TorusSite m × Fin 4 ≃ ForwardEdge L κ ℓ) :
    (fieldHaar m).map (fieldToConfig e) = haarConfigMeasure L κ ℓ := by
  have : Finite (ForwardEdge L κ ℓ) := Finite.of_equiv _ e
  let : Fintype (ForwardEdge L κ ℓ) := Fintype.ofFinite _
  have hmeas : Measurable unitQuaternionEquivSpecialUnitary :=
    unitQuaternionEquivSpecialUnitary.continuous.measurable
  have hpre : ∀ A : Set Matrices.ComplexMatrix2.specialUnitary, MeasurableSet A →
      haarUnit (unitQuaternionEquivSpecialUnitary ⁻¹' A) = Matrices.ComplexMatrix2.haarProb A :=
    fun A hA => by rw [← hmap, Measure.map_apply hmeas hA]
  rw [haarConfigMeasure, Matrices.ComplexMatrix2.haarPi, Measure.infinitePi_eq_pi]
  symm
  refine Measure.pi_eq fun t ht => ?_
  rw [Measure.map_apply (fieldToConfig e).measurable (MeasurableSet.univ_pi ht)]
  have hset : (fieldToConfig e) ⁻¹' Set.pi Set.univ t = Set.pi Set.univ fun x => Set.pi Set.univ fun μ =>
      unitQuaternionEquivSpecialUnitary ⁻¹' t (e (x, μ)) := by
    ext W
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h x μ
      have := h (e (x, μ))
      rwa [fieldToConfig_apply] at this
    · intro h b
      obtain ⟨p, rfl⟩ := e.surjective b
      rw [show p = (p.1, p.2) from rfl, fieldToConfig_apply]
      exact h p.1 p.2
  rw [hset, fieldHaar, Measure.pi_pi]
  simp_rw [Measure.pi_pi, hpre _ (ht _)]
  rw [← Fintype.prod_prod_type (f := fun p : TorusSite m × Fin 4 => Matrices.ComplexMatrix2.haarProb (t (e p)))]
  exact Fintype.prod_equiv e _ _ fun _ => rfl
private theorem edgeVariable_edgeFrom (hℓ : ∀ μ, ℓ μ = (m : ℝ) * meshSize L κ) (hs : 0 < meshSize L κ)
    (hm : 1 < m) (W : TorusField m) (x : TorusSite m) (μ : Fin 4) :
    edgeVariable (fieldToConfig (forwardEdgeEquiv hℓ hs hm) W) (edgeFrom (gridPointOf L κ ℓ x) μ) =
      unitQuaternionEquivSpecialUnitary (W x μ) := by
  rw [edgeVariable, dif_pos (edgeFrom_isForward _ _)]
  exact fieldToConfig_apply (forwardEdgeEquiv hℓ hs hm) W x μ
private theorem faceHolonomy_eq (hℓ : ∀ μ, ℓ μ = (m : ℝ) * meshSize L κ) (hs : 0 < meshSize L κ)
    (hm : 1 < m) (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) (h : μ < ν) :
    faceHolonomy (fieldToConfig (forwardEdgeEquiv hℓ hs hm) W) ⟨gridPointOf L κ ℓ x, μ, ν, h⟩ =
      unitQuaternionEquivSpecialUnitary (holonomy W x μ ν) := by
  simp only [faceHolonomy]
  rw [← gridPointOf_add_unitStep hℓ hs, ← gridPointOf_add_unitStep hℓ hs, edgeVariable_edgeFrom,
    edgeVariable_edgeFrom, edgeVariable_edgeFrom, edgeVariable_edgeFrom]
  simp only [holonomy, map_mul, map_inv]
private theorem faceEnergy_eq (hq : ClusterExpansionOfAStep.UnitQuaternionHaarTraceNorm)
    (hℓ : ∀ μ, ℓ μ = (m : ℝ) * meshSize L κ) (hs : 0 < meshSize L κ)
    (hm : 1 < m) (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) (h : μ < ν) :
    faceEnergy (fieldToConfig (forwardEdgeEquiv hℓ hs hm) W) ⟨gridPointOf L κ ℓ x, μ, ν, h⟩ =
      plaquetteEnergy W x μ ν := by
  rw [faceEnergy, faceHolonomy_eq, plaquetteEnergy, (hq.2.1 _).1]
private def faceOf (L : ℕ) (κ : ℤ) (ℓ : Fin 4 → ℝ) (p : {p : TorusPlaquette m // p.2.1 < p.2.2}) :
    Face L κ ℓ :=
  ⟨gridPointOf L κ ℓ p.1.1, p.1.2.1, p.1.2.2, p.2⟩
private theorem faceOf_bijective (hℓ : ∀ μ, ℓ μ = (m : ℝ) * meshSize L κ) (hs : 0 < meshSize L κ) :
    Function.Bijective (faceOf (m := m) L κ ℓ) := by
  constructor
  · rintro ⟨⟨x, μ, ν⟩, h⟩ ⟨⟨y, μ', ν'⟩, h'⟩ e
    have hc : gridPointOf L κ ℓ x = gridPointOf L κ ℓ y := congrArg Face.corner e
    have h₁ : μ = μ' := congrArg Face.dir₁ e
    have h₂ : ν = ν' := congrArg Face.dir₂ e
    have hxy := gridPointOf_injective hℓ hs hc
    subst h₁ h₂ hxy
    rfl
  · rintro ⟨s, μ, ν, h⟩
    obtain ⟨x, rfl⟩ := gridPointOf_surjective (m := m) hℓ hs s
    exact ⟨⟨(x, μ, ν), h⟩, rfl⟩
private theorem wilsonAction_eq [NeZero m] (hq : ClusterExpansionOfAStep.UnitQuaternionHaarTraceNorm)
    (hℓ : ∀ μ, ℓ μ = (m : ℝ) * meshSize L κ) (hs : 0 < meshSize L κ) (hm : 1 < m) (W : TorusField m) :
    BoxTorus.wilsonAction (fieldToConfig (forwardEdgeEquiv hℓ hs hm) W) =
      TorusFields.wilsonAction Finset.univ W := by
  classical
  have hmem : ∀ p : TorusPlaquette m,
      p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)) ↔ p.2.1 < p.2.2 := by
    intro p
    simp [plaquettesIn]
  rw [BoxTorus.wilsonAction, ← finsum_comp_equiv (Equiv.ofBijective _ (faceOf_bijective (m := m) hℓ hs)),
    finsum_eq_sum_of_fintype, TorusFields.wilsonAction, Finset.sum_subtype _ hmem]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact faceEnergy_eq hq hℓ hs hm W p.1.1 p.1.2.1 p.1.2.2 p.2
private theorem integral_exp_neg_wilsonAction_eq [NeZero m] (hq : ClusterExpansionOfAStep.UnitQuaternionHaarTraceNorm)
    (hℓ : ∀ μ, ℓ μ = (m : ℝ) * meshSize L κ) (hs : 0 < meshSize L κ) (hm : 1 < m) (β : ℝ) :
    ∫ U : GaugeConfig L κ ℓ, Real.exp (-β * BoxTorus.wilsonAction U) ∂(haarConfigMeasure L κ ℓ) =
      wilsonPartition β m := by
  rw [← map_fieldHaar hq.1 (forwardEdgeEquiv hℓ hs hm),
    (fieldToConfig (forwardEdgeEquiv hℓ hs hm)).measurableEmbedding.integral_map, wilsonPartition]
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  change Real.exp (-β * BoxTorus.wilsonAction (fieldToConfig (forwardEdgeEquiv hℓ hs hm) W)) =
    wilsonWeight β m W
  rw [wilsonAction_eq hq, wilsonWeight, dif_neg (NeZero.ne m)]
end TorusPartitionProof
theorem torusPartition_eq_wilsonPartition (hq : ClusterExpansionOfAStep.UnitQuaternionHaarTraceNorm) :
    TorusPartitionIsWilsonPartition := by
  intro D g _ j m _ hm
  have hL : 0 < D.L := by
    have := D.isAdmissible.2
    omega
  have hs : 0 < PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ) := zpow_pos (by exact_mod_cast hL) _
  have hmult : ∀ μ, (gridPeriods g (cubicCounts D j)).mult μ = (m : ℤ) := fun μ => by
    rw [hm]
    rfl
  have hℓ : ∀ μ, (gridPeriods g (cubicCounts D j)).sideLengths μ =
      (m : ℝ) * PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ) := fun μ => by
    change (((gridPeriods g (cubicCounts D j)).mult μ : ℤ) : ℝ) * D.mesh = _
    rw [hmult]
    push_cast
    rfl
  have hm1 : 1 < m := by
    have := (gridPeriods g (cubicCounts D j)).four_le_mult 0
    rw [hmult] at this
    omega
  exact TorusPartitionProof.integral_exp_neg_wilsonAction_eq hq hℓ hs hm1 D.β
end YangMills.Construction.ReflectedCopies
end

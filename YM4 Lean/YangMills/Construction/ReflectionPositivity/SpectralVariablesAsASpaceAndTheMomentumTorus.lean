import YangMills.Construction.InfiniteLattice.ExpansionsMeetTheConditionsOfTheReconstructionProof
import YangMills.Construction.ReflectionPositivity.SpectralVariablesOfTheTwoPictures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Real
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.EnergyMomentum
open JointSpectrum (SpectralDomain)
open DirectionPictures
def supNormCoord (y : Fin 4 → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => |y i|
def orthLattice (μ : Fin 4) : AddSubgroup (Fin 4 → ℤ) where
  carrier := {w | w μ = 0}
  add_mem' := fun {a b} (ha : a μ = 0) (hb : b μ = 0) => by
    change a μ + b μ = 0
    rw [ha, hb, add_zero]
  zero_mem' := rfl
  neg_mem' := fun {a} (ha : a μ = 0) => by
    change -a μ = 0
    rw [ha, neg_zero]
theorem mem_orthLattice {μ : Fin 4} {w : Fin 4 → ℤ} :
    w ∈ orthLattice μ ↔ w μ = 0 := Iff.rfl
def orthProj (μ : Fin 4) (y : Fin 4 → ℤ) : orthLattice μ :=
  ⟨y - y μ • Pi.single μ 1, by simp [mem_orthLattice]⟩
def distTwoPiInt (u : ℝ) : ℝ := sInf (range fun k : ℤ => |u - 2 * π * k|)
theorem exists_sub_twoPiInt_mem_Ioc (u : ℝ) : ∃ k : ℤ, u - 2 * π * k ∈ Ioc (-π) π := by
  refine ⟨toIocDiv Real.two_pi_pos (-π) u, ?_⟩
  have h := toIocMod_mem_Ioc Real.two_pi_pos (-π) u
  rw [← self_sub_toIocDiv_zsmul, zsmul_eq_mul] at h
  have e : (-π + 2 * π) = π := by ring
  rw [e, mul_comm ((toIocDiv Real.two_pi_pos (-π) u : ℤ) : ℝ)] at h
  exact h
theorem abs_le_abs_sub_twoPiInt {v : ℝ} (hv : v ∈ Ioc (-π) π) (m : ℤ) :
    |v| ≤ |v - 2 * π * m| := by
  have hpi := Real.pi_pos
  have hle : |v| ≤ π := abs_le.mpr ⟨hv.1.le, hv.2⟩
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have h1 : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
    have h2 : π ≤ v - 2 * π * m := by nlinarith [hv.1]
    exact hle.trans (h2.trans (le_abs_self _))
  · simp [hm]
  · have h1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have h2 : v - 2 * π * m ≤ -π := by nlinarith [hv.2]
    exact hle.trans ((le_neg.mp h2).trans (neg_le_abs _))
theorem isLeast_distTwoPiInt (u : ℝ) :
    IsLeast (range fun k : ℤ => |u - 2 * π * k|) (distTwoPiInt u) := by
  obtain ⟨k, hk⟩ := exists_sub_twoPiInt_mem_Ioc u
  have h : IsLeast (range fun k : ℤ => |u - 2 * π * k|) |u - 2 * π * k| := by
    refine ⟨⟨k, rfl⟩, ?_⟩
    rintro _ ⟨j, rfl⟩
    have := abs_le_abs_sub_twoPiInt hk (j - k)
    have e : u - 2 * π * k - 2 * π * ((j - k : ℤ) : ℝ) = u - 2 * π * j := by
      push_cast
      ring
    simpa only [e] using this
  rw [distTwoPiInt, h.csInf_eq]
  exact h
instance fact_twoPi_pos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
theorem norm_addCircle_coe_of_mem_Ioc {v : ℝ} (hv : v ∈ Ioc (-π) π) :
    ‖(v : AddCircle (2 * π))‖ = |v| := by
  refine (AddCircle.norm_coe_eq_abs_iff (2 * π) Real.two_pi_pos.ne').mpr ?_
  rw [abs_of_pos Real.two_pi_pos, mul_div_cancel_left₀ _ two_ne_zero]
  exact abs_le.mpr ⟨hv.1.le, hv.2⟩
theorem distTwoPiInt_eq_norm (u : ℝ) :
    distTwoPiInt u = ‖(u : AddCircle (2 * π))‖ := by
  obtain ⟨k, hk⟩ := exists_sub_twoPiInt_mem_Ioc u
  have hmin : distTwoPiInt u = |u - 2 * π * k| := by
    refine le_antisymm ((isLeast_distTwoPiInt u).2 ⟨k, rfl⟩) ?_
    obtain ⟨j, hj⟩ := (isLeast_distTwoPiInt u).1
    rw [← hj]
    have := abs_le_abs_sub_twoPiInt hk (j - k)
    have e : u - 2 * π * k - 2 * π * ((j - k : ℤ) : ℝ) = u - 2 * π * j := by
      push_cast
      ring
    simpa only [e] using this
  have hcoe : ((u - 2 * π * k : ℝ) : AddCircle (2 * π)) = (u : AddCircle (2 * π)) := by
    have e : u - 2 * π * k = u - k • (2 * π) := by
      rw [zsmul_eq_mul]
      ring
    rw [e, AddCircle.coe_sub, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, sub_zero]
  rw [hmin, ← norm_addCircle_coe_of_mem_Ioc hk, hcoe]
def SpectralSpace (μ : Fin 4) : Type := ↥(variableDomain μ)
namespace SpectralSpace
variable {μ : Fin 4}
def energy (x : SpectralSpace μ) : ℝ≥0∞ := x.1.1
def momentum (x : SpectralSpace μ) : TransverseAxis μ → ℝ := x.1.2
end SpectralSpace
def chart (μ : Fin 4) :
    SpectralSpace μ ≃ SpectralDomain (TransverseAxis μ) where
  toFun x := toSpectrum μ x.1
  invFun q := ⟨fromSpectrum μ q,
    fun _ => ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩⟩
  left_inv x := Subtype.ext <| Prod.ext (energyOfUnit_expNegEnergy _)
    (funext fun i => Circle.arg_exp (x.2 i).1 (x.2 i).2)
  right_inv _ := Prod.ext (expNegEnergy_energyOfUnit _) (funext fun _ => Circle.exp_arg _)
instance instTopologicalSpaceSpectralSpace (μ : Fin 4) : TopologicalSpace (SpectralSpace μ) :=
  TopologicalSpace.induced (chart μ) inferInstance
instance instMeasurableSpaceSpectralSpace (μ : Fin 4) : MeasurableSpace (SpectralSpace μ) :=
  MeasurableSpace.comap (chart μ) inferInstance
instance instBorelSpaceSpectralSpace (μ : Fin 4) : BorelSpace (SpectralSpace μ) :=
  ⟨by
    change MeasurableSpace.comap (chart μ) _ = _
    rw [BorelSpace.measurable_eq (α := SpectralDomain (TransverseAxis μ)), borel_comap]⟩
def chartHomeomorph (μ : Fin 4) :
    SpectralSpace μ ≃ₜ SpectralDomain (TransverseAxis μ) :=
  (chart μ).toHomeomorphOfIsInducing ⟨rfl⟩
def chartMeasurableEquiv (μ : Fin 4) :
    SpectralSpace μ ≃ᵐ SpectralDomain (TransverseAxis μ) :=
  (chartHomeomorph μ).toMeasurableEquiv
theorem measurableSet_iff_measurableSet_chart_image {μ : Fin 4} {S : Set (SpectralSpace μ)} :
    MeasurableSet S ↔ MeasurableSet (chart μ '' S) :=
  ((chartMeasurableEquiv μ).measurableSet_image).symm
theorem continuous_iff_continuous_comp_chart_symm {μ : Fin 4} {f : SpectralSpace μ → ℂ} :
    Continuous f ↔ Continuous (f ∘ (chart μ).symm) :=
  ((chartHomeomorph μ).symm.comp_continuous_iff').symm
def expNegNatMulEnergy (n : ℕ) (E : ℝ≥0∞) : ℝ := ((expNegEnergy E : unitInterval) : ℝ) ^ n
theorem expNegNatMulEnergy_top {n : ℕ} (hn : 1 ≤ n) : expNegNatMulEnergy n ⊤ = 0 := by
  have h : n ≠ 0 := by omega
  simp [expNegNatMulEnergy, expNegEnergy, h]
theorem expNegNatMulEnergy_zero (E : ℝ≥0∞) : expNegNatMulEnergy 0 E = 1 := by
  simp [expNegNatMulEnergy]
abbrev DualTorus (μ : Fin 4) : Type := TransverseAxis μ → AddCircle (2 * π)
def toCircles (μ : Fin 4) : DualTorus μ ≃ₜ (TransverseAxis μ → Circle) :=
  Homeomorph.piCongrRight fun _ => AddCircle.homeomorphCircle'
def torusProj (μ : Fin 4) (η : TransverseAxis μ → ℝ) : DualTorus μ :=
  fun i => (η i : AddCircle (2 * π))
theorem toCircles_torusProj (μ : Fin 4) (η : TransverseAxis μ → ℝ) (i : TransverseAxis μ) :
    toCircles μ (torusProj μ η) i = Circle.exp (η i) := rfl
theorem continuous_torusProj (μ : Fin 4) : Continuous (torusProj μ) :=
  continuous_pi fun i => (AddCircle.continuous_mk' (2 * π)).comp (continuous_apply i)
def fundamentalBox (μ : Fin 4) : Set (TransverseAxis μ → ℝ) := {η | ∀ i, η i ∈ Ioc (-π) π}
theorem neg_pi_add_two_pi : -π + 2 * π = π := by ring
def boxRep (μ : Fin 4) (η : DualTorus μ) : TransverseAxis μ → ℝ :=
  fun i => (AddCircle.equivIoc (2 * π) (-π) (η i) : ℝ)
theorem boxRep_mem (μ : Fin 4) (η : DualTorus μ) :
    boxRep μ η ∈ fundamentalBox μ := fun i => by
  have h := (AddCircle.equivIoc (2 * π) (-π) (η i)).2
  exact ⟨h.1, h.2.trans_eq neg_pi_add_two_pi⟩
theorem torusProj_boxRep (μ : Fin 4) (η : DualTorus μ) :
    torusProj μ (boxRep μ η) = η :=
  funext fun _ => AddCircle.coe_equivIoc
theorem boxRep_torusProj {μ : Fin 4} {η : TransverseAxis μ → ℝ}
    (hη : η ∈ fundamentalBox μ) : boxRep μ (torusProj μ η) = η := by
  funext i
  have h : η i ∈ Ioc (-π) (-π + 2 * π) := by
    rw [neg_pi_add_two_pi]
    exact hη i
  exact AddCircle.equivIoc_coe_of_mem h
def torusMeasure (μ : Fin 4) : Measure (DualTorus μ) :=
  (volume.restrict (fundamentalBox μ)).map (torusProj μ)
theorem card_transverseAxis (μ : Fin 4) : Fintype.card (TransverseAxis μ) = 3 := by apply _root_.YangMills.Construction.LatticeConventions.MirrorExpansionsProof.card_ne_direction <;> assumption
theorem torusMeasure_univ (μ : Fin 4) :
    torusMeasure μ univ = ENNReal.ofReal ((2 * π) ^ 3) := by
  have hbox : fundamentalBox μ = Set.pi univ fun _ => Ioc (-π) π := by
    ext η
    simp [fundamentalBox, Set.mem_pi]
  rw [torusMeasure, Measure.map_apply (continuous_torusProj μ).measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, hbox, Real.volume_pi_Ioc]
  rw [Finset.prod_const, Finset.card_univ, card_transverseAxis,
    ← ENNReal.ofReal_pow (by linarith [Real.pi_pos])]
  congr 2
  ring
def torusSupNorm (μ : Fin 4) (η : DualTorus μ) : ℝ :=
  angleSupNorm μ (boxRep μ η)
theorem abs_boxRep (μ : Fin 4) (η : DualTorus μ) (i : TransverseAxis μ) :
    |boxRep μ η i| = ‖η i‖ := by
  rw [← norm_addCircle_coe_of_mem_Ioc (boxRep_mem μ η i)]
  exact congrArg norm (AddCircle.coe_equivIoc (a := -π) (y := η i))
theorem torusSupNorm_eq_norm (μ : Fin 4) (η : DualTorus μ) : torusSupNorm μ η = ‖η‖ := by
  have hle : ∀ i, |boxRep μ η i| ≤ torusSupNorm μ η := fun i =>
    Finset.le_sup' (fun i => |boxRep μ η i|) (Finset.mem_univ i)
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le Finset.univ_nonempty _ fun i _ => ?_
    rw [abs_boxRep]
    exact norm_le_pi_norm η i
  · refine (pi_norm_le_iff_of_nonneg ?_).mpr fun i => ?_
    · exact (abs_nonneg _).trans (hle (Classical.arbitrary _))
    · rw [← abs_boxRep]
      exact hle i
theorem torusSupNorm_torusProj_of_mem {μ : Fin 4} {η : TransverseAxis μ → ℝ}
    (hη : η ∈ fundamentalBox μ) : torusSupNorm μ (torusProj μ η) = angleSupNorm μ η := by
  rw [torusSupNorm, boxRep_torusProj hη]
theorem continuous_torusSupNorm (μ : Fin 4) : Continuous (torusSupNorm μ) := by
  have h : torusSupNorm μ = fun η => ‖η‖ := funext (torusSupNorm_eq_norm μ)
  rw [h]
  exact continuous_norm
end YangMills.Construction.ReflectionPositivity.EnergyMomentum

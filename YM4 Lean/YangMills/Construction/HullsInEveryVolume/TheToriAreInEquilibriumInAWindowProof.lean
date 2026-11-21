import YangMills.Construction.HullsInEveryVolume.KernelOfAWindowIsContinuousAndBounded
import YangMills.Construction.HullsInEveryVolume.TheToriAreInEquilibriumInAWindow
import YangMills.Construction.InfiniteLattice.WilsonKernelOfBondsWithOneOrientation
import YangMills.Construction.InfiniteLattice.WindowsKernelOperatorAndDensitiesAtOneSpacing
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import YangMills.Construction.Lattice.ConfigurationsAreACompactProductOfCopiesOfTheGroup
import YangMills.Construction.Lattice.WilsonActionAsAPlaquetteSumAndSymmetriesOfProductHaar
import YangMills.Construction.Matrices.FiniteProductOfSpecialUnitary
import YangMills.Construction.Matrices.UnitaryLogarithmClosedForm
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.HullsInEveryVolume
open InfiniteLattice Matrices
namespace WindowEquilibrium
attribute [local instance] WilsonOperator.secondCountable_specialUnitary
private theorem secondCountable_gaugeField {a : ℝ} : SecondCountableTopology (GaugeField a) := by
  have := WilsonOperator.countable_link (a := a)
  have : SecondCountableTopology (Link a → ComplexMatrix2.specialUnitary) := inferInstance
  exact TopologicalSpace.Subtype.secondCountableTopology
    {U : Link a → ComplexMatrix2.specialUnitary | ∀ b, U b.opposite = (U b)⁻¹}
private theorem isProbabilityMeasure_haarProd {a : ℝ} (W : LinkWindow a) :
    IsProbabilityMeasure W.haarProd := by
  unfold LinkWindow.haarProd ComplexMatrix2.haarPi
  infer_instance
section Resampling
variable {S P : Type} [Finite S] [Finite P]
private theorem integral_resample_image (hProd : ComplexMatrix2.FiniteProductGroupStatement)
    {ι : S → P} (hι : Function.Injective ι) {h : (P → ComplexMatrix2.specialUnitary) → ℝ}
    (hm : Measurable h) {C : ℝ} (hb : ∀ v, ‖h v‖ ≤ C) :
    ∫ v, (∫ V, h (Function.extend ι V v) ∂ComplexMatrix2.haarPi S) ∂ComplexMatrix2.haarPi P =
      ∫ v, h v ∂ComplexMatrix2.haarPi P := by
  classical
  obtain ⟨-, -, hSp, -, hSr⟩ := hProd.2.1 S
  obtain ⟨-, -, hPp, hPl, -⟩ := hProd.2.1 P
  set e : (S → ComplexMatrix2.specialUnitary) → (P → ComplexMatrix2.specialUnitary) :=
    fun V => Function.extend ι V 1 with he
  have hupd : ∀ (v : P → ComplexMatrix2.specialUnitary) (V : S → ComplexMatrix2.specialUnitary),
      Function.extend ι V v = e (V * (v ∘ ι)⁻¹) * v := by
    intro v V
    funext p
    by_cases hp : ∃ s, ι s = p
    · obtain ⟨s, rfl⟩ := hp
      simp [he, hι.extend_apply]
    · simp [he, Function.extend_apply' _ _ _ hp]
  have hin : ∀ v : P → ComplexMatrix2.specialUnitary,
      ∫ V, h (Function.extend ι V v) ∂ComplexMatrix2.haarPi S =
        ∫ V, h (e V * v) ∂ComplexMatrix2.haarPi S := by
    intro v
    simp only [hupd]
    exact integral_mul_right_eq_self (fun V => h (e V * v)) ((v ∘ ι)⁻¹)
  simp only [hin]
  have hjoint : Measurable fun q : (P → ComplexMatrix2.specialUnitary) ×
      (S → ComplexMatrix2.specialUnitary) => e q.2 * q.1 := by
    refine measurable_pi_iff.2 fun p => ?_
    by_cases hp : ∃ s, ι s = p
    · obtain ⟨s, rfl⟩ := hp
      simp only [he, Pi.mul_apply, hι.extend_apply]
      exact ((measurable_pi_apply s).comp measurable_snd).mul
        ((measurable_pi_apply (ι s)).comp measurable_fst)
    · simp only [he, Pi.mul_apply, Function.extend_apply' _ _ _ hp]
      simp only [Pi.one_apply, one_mul]
      exact (measurable_pi_apply p).comp measurable_fst
  have hint : Integrable (Function.uncurry fun (v : P → ComplexMatrix2.specialUnitary)
      (V : S → ComplexMatrix2.specialUnitary) => h (e V * v))
      ((ComplexMatrix2.haarPi P).prod (ComplexMatrix2.haarPi S)) :=
    Integrable.of_bound (hm.comp hjoint).aestronglyMeasurable C (ae_of_all _ fun q => hb _)
  rw [integral_integral_swap hint]
  simp only [integral_mul_left_eq_self (μ := ComplexMatrix2.haarPi P) h]
  simp
end Resampling
section Values
variable {L m : ℕ} {j : ℤ}
private theorem measurable_gaugeFieldOfPositive :
    Measurable (PeriodicLattice.gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) →
        PeriodicLattice.Bond L m j → ComplexMatrix2) := by
  have hval : Measurable fun g : ComplexMatrix2.specialUnitary => (g : ComplexMatrix2) :=
    continuous_subtype_val.measurable
  have hinv : Measurable fun g : ComplexMatrix2.specialUnitary => (g : ComplexMatrix2)⁻¹ := by
    have e : (fun g : ComplexMatrix2.specialUnitary => (g : ComplexMatrix2)⁻¹) =
        fun g => ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) :=
      funext fun g => (specialUnitary_coe_inv g).symm
    rw [e]
    exact (continuous_subtype_val.comp continuous_inv).measurable
  refine measurable_pi_iff.2 fun b => ?_
  unfold PeriodicLattice.gaugeFieldOfPositive
  by_cases h : b.IsPositivelyOriented
  · simp only [dif_pos h]
    exact hval.comp (measurable_pi_apply _)
  · by_cases h' : b.opposite.IsPositivelyOriented
    · simp only [dif_neg h, dif_pos h']
      exact hinv.comp (measurable_pi_apply _)
    · simp only [dif_neg h, dif_neg h']
      exact measurable_const
private theorem continuous_plaquetteCost (p : PeriodicLattice.Plaquette L m j) :
    Continuous fun U : PeriodicLattice.Bond L m j → ComplexMatrix2 =>
      PeriodicLattice.plaquetteCost U p := by
  have hb : ∀ b : PeriodicLattice.Bond L m j,
      Continuous fun U : PeriodicLattice.Bond L m j → ComplexMatrix2 => U b :=
    fun b => continuous_apply b
  have hh : Continuous fun U : PeriodicLattice.Bond L m j → ComplexMatrix2 =>
      PeriodicLattice.plaquetteHolonomy U p := by
    simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
      PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil]
    exact (hb _).matrix_mul ((hb _).matrix_mul ((hb _).matrix_mul ((hb _).matrix_mul
      continuous_const)))
  unfold PeriodicLattice.plaquetteCost
  exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp hh.matrix_trace))
private theorem measurable_boltzmannWeight [Finite (PeriodicLattice.Plaquette L m j)] (β : ℝ) :
    Measurable (PeriodicLattice.boltzmannWeight β :
      (PeriodicLattice.Bond L m j → ComplexMatrix2) → ℝ) := by
  have : SecondCountableTopology ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : BorelSpace (PeriodicLattice.Bond L m j → ComplexMatrix2) := Pi.borelSpace
  have hA : Continuous (PeriodicLattice.wilsonAction :
      (PeriodicLattice.Bond L m j → ComplexMatrix2) → ℝ) := by
    have := Fintype.ofFinite (PeriodicLattice.Plaquette L m j)
    unfold PeriodicLattice.wilsonAction
    simp only [finsum_eq_sum_of_fintype]
    exact continuous_finsetSum _ fun p _ => continuous_plaquetteCost p
  have hc : Continuous (PeriodicLattice.boltzmannWeight β :
      (PeriodicLattice.Bond L m j → ComplexMatrix2) → ℝ) := by
    unfold PeriodicLattice.boltzmannWeight
    exact Real.continuous_exp.comp (continuous_const.mul hA)
  exact hc.measurable
end Values
private theorem integral_liftedWilsonMeasure {L m K : ℕ}
    [Finite (PeriodicLattice.Plaquette L m (K : ℤ))] {β : ℝ}
    {G : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℝ} (hG : Measurable G) :
    ∫ U, G U ∂liftedWilsonMeasure L m K β =
      (ENNReal.ofReal (PeriodicLattice.partitionFunction L m K β))⁻¹.toReal •
        ∫ v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary,
          PeriodicLattice.boltzmannWeight β (PeriodicLattice.gaugeFieldOfPositive v) *
            G (liftField L m (K : ℤ) (PeriodicLattice.gaugeFieldOfPositive v))
          ∂ComplexMatrix2.haarPi (PeriodicLattice.PositivelyOrientedBond L m (K : ℤ)) := by
  have hp := measurable_liftField L m (K : ℤ)
  have hc := measurable_gaugeFieldOfPositive (L := L) (m := m) (j := (K : ℤ))
  have hb := measurable_boltzmannWeight (L := L) (m := m) (j := (K : ℤ)) β
  have hGp : Measurable fun U => G (liftField L m (K : ℤ) U) := hG.comp hp
  have e₁ : ∫ U, G U ∂liftedWilsonMeasure L m K β =
      ∫ U, G (liftField L m (K : ℤ) U) ∂PeriodicLattice.wilsonGibbsMeasure L m K β :=
    integral_map hp.aemeasurable hG.aestronglyMeasurable
  rw [e₁, PeriodicLattice.wilsonGibbsMeasure, integral_smul_measure]
  congr 1
  rw [integral_withDensity_eq_integral_toReal_smul hb.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hnn : ∀ U : PeriodicLattice.Bond L m (K : ℤ) → ComplexMatrix2,
      0 ≤ PeriodicLattice.boltzmannWeight β U := fun U => (Real.exp_pos _).le
  simp only [ENNReal.toReal_ofReal (hnn _), smul_eq_mul]
  exact integral_map hc.aemeasurable (hb.mul hGp).aestronglyMeasurable
section Covering
variable {L m : ℕ} {j : ℤ}
private theorem projectPoint_add (x y : LatticePoint (PeriodicLattice.meshSize L j)) :
    projectPoint L m j (x + y) = projectPoint L m j x + projectPoint L m j y := by
  refine Subtype.ext (funext fun μ => ?_)
  simp [projectPoint, TorusMetric.torusProj]
private theorem projectPoint_zero :
    projectPoint L m j (0 : LatticePoint (PeriodicLattice.meshSize L j)) = 0 := by
  refine Subtype.ext (funext fun μ => ?_)
  simp [projectPoint, TorusMetric.torusProj]
private theorem projectPoint_eq_imp (x x' : LatticePoint (PeriodicLattice.meshSize L j))
    (h : projectPoint L m j x = projectPoint L m j x') :
    ∃ n : Fin 4 → ℤ, ∀ μ, (x : AmbientSpace) μ - (x' : AmbientSpace) μ =
      (n μ : ℝ) * PeriodicLattice.torusSide L m := by
  have key : ∀ μ, ∃ n : ℤ, n • PeriodicLattice.torusSide L m =
      (x : AmbientSpace) μ - (x' : AmbientSpace) μ := by
    intro μ
    refine (AddCircle.coe_eq_zero_iff _).mp ?_
    have h' : (((x : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) =
        (((x' : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) :=
      congrFun (congrArg Subtype.val h) μ
    rw [AddCircle.coe_sub, h', sub_self]
  choose n hn using key
  refine ⟨n, fun μ => ?_⟩
  have e := hn μ
  rw [zsmul_eq_mul] at e
  exact e.symm
private theorem projectLink_forwardFrom (x : LatticePoint (PeriodicLattice.meshSize L j))
    (κ : Fin 4) :
    projectLink L m j (Link.forwardFrom x κ) =
      PeriodicLattice.Bond.forwardFrom (projectPoint L m j x) κ :=
  PeriodicLattice.Bond.ext rfl (by
    show projectPoint L m j (x + axisStep _ κ) =
      projectPoint L m j x + PeriodicLattice.unitStep L m j κ
    rw [projectPoint_add, projectPoint_axisStep])
private theorem exists_projectPoint_eq (y : PeriodicLattice.Site L m j) :
    ∃ x : LatticePoint (PeriodicLattice.meshSize L j), projectPoint L m j x = y := by
  obtain ⟨n, hn⟩ := y.2
  exact ⟨⟨fun μ => (n μ : ℝ) * PeriodicLattice.meshSize L j, n, fun _ => rfl⟩,
    Subtype.ext (funext fun μ => (hn μ).symm)⟩
private theorem projectLink_isPositivelyOriented {b : Link (PeriodicLattice.meshSize L j)}
    (hb : b.IsPositivelyOriented) : (projectLink L m j b).IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := hb
  refine ⟨μ, ?_⟩
  show projectPoint L m j b.terminal - projectPoint L m j b.initial =
    PeriodicLattice.unitStep L m j μ
  rw [← projectPoint_sub, hμ, projectPoint_axisStep]
private def projectFace (p : ElementaryPlaquette (PeriodicLattice.meshSize L j)) :
    PeriodicLattice.Plaquette L m j :=
  ⟨projectPoint L m j p.corner, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
private theorem faceEnergy_liftCompactField (U : PeriodicLattice.CompactGaugeField L m j)
    (p : ElementaryPlaquette (PeriodicLattice.meshSize L j)) :
    faceEnergy (liftCompactField U) p = PeriodicLattice.plaquetteCost U.1 (projectFace p) := by
  have e : ∀ (x : LatticePoint (PeriodicLattice.meshSize L j)) (κ : Fin 4),
      liftCompactField U (Link.forwardFrom x κ) =
        U.linkValue (PeriodicLattice.Bond.forwardFrom (projectPoint L m j x) κ) := fun x κ => by
    rw [liftCompactField_apply, projectLink_forwardFrom]
  have hv : ((faceHolonomy (liftCompactField U) p : ComplexMatrix2.specialUnitary) :
      ComplexMatrix2) = PeriodicLattice.plaquetteHolonomy U.1 (projectFace p) := by
    have hr : ∀ b : PeriodicLattice.Bond L m j,
        (((U.linkValue b)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
          U.1 b.opposite := fun b => by
      rw [← U.linkValue_opposite b]
      rfl
    simp only [faceHolonomy, e, projectPoint_add, projectPoint_axisStep,
      PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
      PeriodicLattice.Plaquette.boundaryBonds, projectFace, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, Submonoid.coe_mul, hr]
    simp only [mul_assoc]
    rfl
  simp only [faceEnergy, PeriodicLattice.plaquetteCost, hv]
end Covering
section Steps
variable {L m K : ℕ}
private theorem meshSize_pos (hL : 1 < L) (K : ℕ) : 0 < PeriodicLattice.meshSize L (K : ℤ) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  unfold PeriodicLattice.meshSize
  exact zpow_pos hL0 _
private theorem torusSide_eq (hL : 1 < L) (m K : ℕ) :
    PeriodicLattice.torusSide L m =
      (2 * (L : ℝ) ^ (m + K)) * PeriodicLattice.meshSize L (K : ℤ) := by
  unfold PeriodicLattice.torusSide PeriodicLattice.meshSize
  rw [zpow_neg, zpow_natCast, pow_add]
  field_simp
private theorem eq_of_unitStep_eq (hL : 1 < L) {μ ν : Fin 4}
    (h : PeriodicLattice.unitStep L m (K : ℤ) μ = PeriodicLattice.unitStep L m (K : ℤ) ν) :
    μ = ν := by
  by_contra hne
  rw [← projectPoint_axisStep, ← projectPoint_axisStep] at h
  obtain ⟨n, hn⟩ := projectPoint_eq_imp _ _ h
  have ha := meshSize_pos hL K
  have h1 : PeriodicLattice.meshSize L (K : ℤ) = (n μ : ℝ) * PeriodicLattice.torusSide L m := by
    have e := hn μ
    simpa [axisStep, Pi.single_eq_of_ne hne] using e
  rw [torusSide_eq hL m K] at h1
  have h2 : (1 : ℝ) = (n μ : ℝ) * (2 * (L : ℝ) ^ (m + K)) :=
    mul_right_cancel₀ ha.ne' (by rw [one_mul, mul_assoc]; exact h1)
  have h3 : (1 : ℤ) = n μ * (2 * (L : ℤ) ^ (m + K)) := by exact_mod_cast h2
  have h4 : (2 : ℤ) ∣ 1 := ⟨n μ * (L : ℤ) ^ (m + K), by rw [h3]; ring⟩
  exact absurd h4 (by decide)
private theorem exists_lift_of_forwardFrom (hL : 1 < L) (y : PeriodicLattice.Site L m (K : ℤ))
    (δ : LatticePoint (PeriodicLattice.meshSize L (K : ℤ))) (κ : Fin 4)
    {b : Link (PeriodicLattice.meshSize L (K : ℤ))} (hb : b.IsPositivelyOriented)
    (h : PeriodicLattice.Bond.forwardFrom (y + projectPoint L m (K : ℤ) δ) κ =
      projectLink L m (K : ℤ) b) :
    ∃ x : LatticePoint (PeriodicLattice.meshSize L (K : ℤ)), projectPoint L m (K : ℤ) x = y ∧
      b = Link.forwardFrom (x + δ) κ := by
  obtain ⟨μ, hμ⟩ := hb
  have hb' : Link.forwardFrom b.initial μ = b := Link.ext rfl (by
    show b.initial + axisStep _ μ = b.terminal
    rw [← hμ]
    abel)
  have h' : PeriodicLattice.Bond.forwardFrom (y + projectPoint L m (K : ℤ) δ) κ =
      PeriodicLattice.Bond.forwardFrom (projectPoint L m (K : ℤ) b.initial) μ := by
    rw [h, ← projectLink_forwardFrom, hb']
  have ht : y + projectPoint L m (K : ℤ) δ = projectPoint L m (K : ℤ) b.initial :=
    congrArg PeriodicLattice.Bond.source h'
  have hh : y + projectPoint L m (K : ℤ) δ + PeriodicLattice.unitStep L m (K : ℤ) κ =
      projectPoint L m (K : ℤ) b.initial + PeriodicLattice.unitStep L m (K : ℤ) μ :=
    congrArg PeriodicLattice.Bond.target h'
  rw [ht] at hh
  have hκ : κ = μ := eq_of_unitStep_eq hL (add_left_cancel hh)
  refine ⟨b.initial - δ, ?_, ?_⟩
  · rw [projectPoint_sub, ← ht]
    abel
  · rw [hκ, sub_add_cancel, hb']
private theorem exists_injOn_projectLink (hL : 1 < L)
    {S : Set (Link (PeriodicLattice.meshSize L (K : ℤ)))} (hS : S.Finite) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → InjOn (projectLink L m (K : ℤ)) S := by
  let g : Link (PeriodicLattice.meshSize L (K : ℤ)) → ℝ := fun b =>
    ∑ μ, (|(b.initial : AmbientSpace) μ| + |(b.terminal : AmbientSpace) μ|)
  obtain ⟨D, hD⟩ := (hS.image g).bddAbove
  have hle : ∀ b ∈ S, ∀ μ, |(b.initial : AmbientSpace) μ| + |(b.terminal : AmbientSpace) μ| ≤ D :=
    fun b hb μ =>
      (Finset.single_le_sum
        (f := fun μ => |(b.initial : AmbientSpace) μ| + |(b.terminal : AmbientSpace) μ|)
        (fun _ _ => by positivity) (Finset.mem_univ μ)).trans (hD ⟨b, hb, rfl⟩)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt D hL1
  refine ⟨m₀, fun m hm b hb b' hb' h => ?_⟩
  have hside : 2 * D < PeriodicLattice.torusSide L m := by
    have : (L : ℝ) ^ m₀ ≤ (L : ℝ) ^ m := pow_le_pow_right₀ hL1.le hm
    unfold PeriodicLattice.torusSide
    linarith
  have key : ∀ x x' : LatticePoint (PeriodicLattice.meshSize L (K : ℤ)),
      (∀ μ, |(x : AmbientSpace) μ| ≤ D) → (∀ μ, |(x' : AmbientSpace) μ| ≤ D) →
      projectPoint L m (K : ℤ) x = projectPoint L m (K : ℤ) x' → x = x' := by
    intro x x' hx hx' e
    obtain ⟨n, hn⟩ := projectPoint_eq_imp x x' e
    refine Subtype.ext (funext fun μ => ?_)
    have hn0 : n μ = 0 := by
      by_contra h0
      have h1 : (1 : ℝ) ≤ |(n μ : ℝ)| := by exact_mod_cast Int.one_le_abs h0
      have hpos : 0 < PeriodicLattice.torusSide L m :=
        lt_of_le_of_lt (by linarith [(abs_nonneg _).trans (hx μ)]) hside
      have h2 : |(x : AmbientSpace) μ - (x' : AmbientSpace) μ| ≤ 2 * D :=
        abs_le.mpr ⟨by linarith [(abs_le.mp (hx μ)).1, (abs_le.mp (hx' μ)).2],
          by linarith [(abs_le.mp (hx μ)).2, (abs_le.mp (hx' μ)).1]⟩
      rw [hn μ, abs_mul, abs_of_pos hpos] at h2
      nlinarith
    have := hn μ
    rw [hn0] at this
    simp only [Int.cast_zero, zero_mul] at this
    linarith
  have ht : projectPoint L m (K : ℤ) b.initial = projectPoint L m (K : ℤ) b'.initial :=
    congrArg PeriodicLattice.Bond.source h
  have hh : projectPoint L m (K : ℤ) b.terminal = projectPoint L m (K : ℤ) b'.terminal :=
    congrArg PeriodicLattice.Bond.target h
  have bt : ∀ c ∈ S, ∀ μ, |(c.initial : AmbientSpace) μ| ≤ D := fun c hc μ => by
    linarith [hle c hc μ, abs_nonneg ((c.terminal : AmbientSpace) μ)]
  have bh : ∀ c ∈ S, ∀ μ, |(c.terminal : AmbientSpace) μ| ≤ D := fun c hc μ => by
    linarith [hle c hc μ, abs_nonneg ((c.initial : AmbientSpace) μ)]
  exact Link.ext (key _ _ (bt b hb) (bt b' hb') ht) (key _ _ (bh b hb) (bh b' hb') hh)
end Steps
section Fields
variable {L m K : ℕ}
private def fieldOfPositive
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary) :
    GaugeField (PeriodicLattice.meshSize L (K : ℤ)) :=
  liftField L m (K : ℤ) (PeriodicLattice.gaugeFieldOfPositive v)
private theorem gaugeFieldOfPositive_of_pos
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary)
    {b : PeriodicLattice.Bond L m (K : ℤ)} (h : b.IsPositivelyOriented) :
    PeriodicLattice.gaugeFieldOfPositive v b = (v ⟨b, h⟩ : ComplexMatrix2) :=
  dif_pos h
private theorem gaugeFieldOfPositive_mem (hL : 2 ≤ L) (hm : 1 ≤ m)
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary) :
    PeriodicLattice.gaugeFieldOfPositive v ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ) := by
  have hj : -(m : ℤ) < (K : ℤ) := by omega
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL hj b with
      ⟨h, -⟩ | ⟨h, h'⟩
    · rw [gaugeFieldOfPositive_of_pos v h]
      exact (v _).2
    · have e : PeriodicLattice.gaugeFieldOfPositive v b =
          ((v ⟨b.opposite, h⟩ : ComplexMatrix2))⁻¹ := by
        unfold PeriodicLattice.gaugeFieldOfPositive
        rw [dif_neg h', dif_pos h]
      rw [e, ← specialUnitary_coe_inv]
      exact ((v ⟨b.opposite, h⟩)⁻¹).2
  · rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL hj b with
      ⟨h, h'⟩ | ⟨h, h'⟩
    · have e₂ : PeriodicLattice.gaugeFieldOfPositive v b.opposite =
          ((v ⟨b, h⟩ : ComplexMatrix2))⁻¹ := by
        unfold PeriodicLattice.gaugeFieldOfPositive
        rw [dif_neg h', dif_pos (show b.opposite.opposite.IsPositivelyOriented from h)]
        rfl
      rw [gaugeFieldOfPositive_of_pos v h, e₂]
    · have e₂ : PeriodicLattice.gaugeFieldOfPositive v b =
          ((v ⟨b.opposite, h⟩ : ComplexMatrix2))⁻¹ := by
        unfold PeriodicLattice.gaugeFieldOfPositive
        rw [dif_neg h', dif_pos h]
      rw [gaugeFieldOfPositive_of_pos v h, e₂, ← specialUnitary_coe_inv,
        ← specialUnitary_coe_inv, inv_inv]
private theorem fieldOfPositive_apply (hL : 2 ≤ L) (hm : 1 ≤ m)
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary)
    {b : Link (PeriodicLattice.meshSize L (K : ℤ))} (hb : b.IsPositivelyOriented) :
    fieldOfPositive v b = v ⟨projectLink L m (K : ℤ) b, projectLink_isPositivelyOriented hb⟩ :=
  Subtype.ext ((liftField_apply_of_mem (gaugeFieldOfPositive_mem hL hm v) b).trans
    (gaugeFieldOfPositive_of_pos v _))
private theorem faceEnergy_mem_Icc {a : ℝ} (hLog : ComplexMatrix2.UnitaryLogarithmProperties)
    (U : GaugeField a) (p : ElementaryPlaquette a) : faceEnergy U p ∈ Set.Icc (0 : ℝ) 2 := by
  obtain ⟨t, ⟨h₁, h₂⟩, ht⟩ := (hLog.2.1 _ (faceHolonomy U p).2).1
  have h : (1 / 2) * (ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2)).re = t := by
    have := congrArg Complex.re ht
    simpa [ComplexMatrix2.halfTrace, Complex.mul_re] using this
  unfold faceEnergy
  rw [h]
  constructor <;> linarith
private theorem plaquetteCost_projectFace (hL : 2 ≤ L) (hm : 1 ≤ m)
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary)
    (p : ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ))) :
    PeriodicLattice.plaquetteCost (PeriodicLattice.gaugeFieldOfPositive v) (projectFace p) =
      faceEnergy (fieldOfPositive v) p :=
  (faceEnergy_liftCompactField (⟨_, gaugeFieldOfPositive_mem hL hm v⟩ :
    PeriodicLattice.CompactGaugeField L m (K : ℤ)) p).symm
private theorem plaquetteCost_nonneg (hLog : ComplexMatrix2.UnitaryLogarithmProperties)
    (hL : 2 ≤ L) (hm : 1 ≤ m)
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary)
    (P : PeriodicLattice.Plaquette L m (K : ℤ)) :
    0 ≤ PeriodicLattice.plaquetteCost (PeriodicLattice.gaugeFieldOfPositive v) P := by
  obtain ⟨x, hx⟩ := exists_projectPoint_eq P.origin
  have hP : projectFace (⟨x, P.firstAxis, P.secondAxis, P.firstAxis_lt_secondAxis⟩ :
      ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ))) = P :=
    PeriodicLattice.Plaquette.ext hx rfl rfl
  rw [← hP, plaquetteCost_projectFace hL hm]
  exact (faceEnergy_mem_Icc hLog _ _).1
private theorem boltzmannWeight_le_one (hLog : ComplexMatrix2.UnitaryLogarithmProperties)
    (hL : 2 ≤ L) (hm : 1 ≤ m) {β : ℝ} (hβ : 0 < β)
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary) :
    PeriodicLattice.boltzmannWeight β (PeriodicLattice.gaugeFieldOfPositive v) ≤ 1 := by
  have h0 : 0 ≤ PeriodicLattice.wilsonAction (PeriodicLattice.gaugeFieldOfPositive v) :=
    finsum_nonneg fun P => plaquetteCost_nonneg hLog hL hm v P
  unfold PeriodicLattice.boltzmannWeight
  exact Real.exp_le_one_iff.mpr (by nlinarith)
private theorem isProbabilityMeasure_liftedWilsonMeasure
    (hProd : ComplexMatrix2.FiniteProductGroupStatement)
    (hLog : ComplexMatrix2.UnitaryLogarithmProperties) (hL : 2 ≤ L) (hm : 1 ≤ m)
    [Finite (PeriodicLattice.Plaquette L m (K : ℤ))]
    [Finite (PeriodicLattice.PositivelyOrientedBond L m (K : ℤ))]
    {β : ℝ} (hβ : 0 < β) : IsProbabilityMeasure (liftedWilsonMeasure L m K β) := by
  obtain ⟨-, -, hPp, -, -⟩ := hProd.2.1 (PeriodicLattice.PositivelyOrientedBond L m (K : ℤ))
  have hc := measurable_gaugeFieldOfPositive (L := L) (m := m) (j := (K : ℤ))
  have hρ := measurable_boltzmannWeight (L := L) (m := m) (j := (K : ℤ)) β
  have hint : Integrable (fun v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) →
      ComplexMatrix2.specialUnitary =>
      PeriodicLattice.boltzmannWeight β (PeriodicLattice.gaugeFieldOfPositive v))
      (ComplexMatrix2.haarPi (PeriodicLattice.PositivelyOrientedBond L m (K : ℤ))) := by
    refine Integrable.of_bound (hρ.comp hc).aestronglyMeasurable 1 (ae_of_all _ fun v => ?_)
    have hp : 0 < PeriodicLattice.boltzmannWeight β (PeriodicLattice.gaugeFieldOfPositive v) :=
      Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_pos hp]
    exact boltzmannWeight_le_one hLog hL hm hβ v
  have hZ : PeriodicLattice.partitionFunction L m K β =
      ∫ v, PeriodicLattice.boltzmannWeight β (PeriodicLattice.gaugeFieldOfPositive v)
        ∂ComplexMatrix2.haarPi (PeriodicLattice.PositivelyOrientedBond L m (K : ℤ)) :=
    integral_map hc.aemeasurable hρ.aestronglyMeasurable
  have hpos : 0 < PeriodicLattice.partitionFunction L m K β := by
    rw [hZ]
    refine (integral_pos_iff_support_of_nonneg (fun v => (Real.exp_pos _).le) hint).mpr ?_
    rw [show Function.support _ = Set.univ from
      Set.eq_univ_of_forall fun v => (Real.exp_pos _).ne']
    simp
  have hint' : Integrable (PeriodicLattice.boltzmannWeight β)
      (PeriodicLattice.productHaarMeasure L m (K : ℤ)) :=
    (integrable_map_measure hρ.aestronglyMeasurable hc.aemeasurable).mpr hint
  have hI : ∫⁻ U, ENNReal.ofReal (PeriodicLattice.boltzmannWeight β U)
      ∂PeriodicLattice.productHaarMeasure L m (K : ℤ) =
        ENNReal.ofReal (PeriodicLattice.partitionFunction L m K β) :=
    (ofReal_integral_eq_lintegral_ofReal hint' (ae_of_all _ fun _ => (Real.exp_pos _).le)).symm
  refine ⟨?_⟩
  unfold liftedWilsonMeasure
  rw [Measure.map_apply (measurable_liftField L m (K : ℤ)) MeasurableSet.univ, preimage_univ]
  unfold PeriodicLattice.wilsonGibbsMeasure
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, hI]
  exact ENNReal.inv_mul_cancel (by simpa using hpos) ENNReal.ofReal_ne_top
end Fields
section Equation
variable {L m K : ℕ} (W : LinkWindow (PeriodicLattice.meshSize L (K : ℤ)))
private def imageLink (b : W.links) : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) :=
  ⟨projectLink L m (K : ℤ) b, projectLink_isPositivelyOriented (W.isPositive b b.2)⟩
variable {W}
private theorem imageLink_injective
    (hinj : InjOn (projectLink L m (K : ℤ)) ((W.links : Set _) ∪ W.rim)) :
    Function.Injective (imageLink (L := L) (m := m) W) := fun b b' h => Subtype.ext
  (hinj (Or.inl (Finset.mem_coe.2 b.2)) (Or.inl (Finset.mem_coe.2 b'.2)) (congrArg Subtype.val h))
private theorem isPositivelyOriented_of_mem {b : Link (PeriodicLattice.meshSize L (K : ℤ))}
    (hb : b ∈ (W.links : Set _) ∪ W.rim) : b.IsPositivelyOriented := by
  rcases hb with h | h
  · exact W.isPositive b (Finset.mem_coe.1 h)
  · exact InfiniteLattice.mem_positiveLinks_iff.mp (W.rim_subset_positiveLinks h)
private theorem fieldOfPositive_extend_of_not_mem (hL : 2 ≤ L) (hm : 1 ≤ m)
    (hinj : InjOn (projectLink L m (K : ℤ)) ((W.links : Set _) ∪ W.rim)) (V : W.Assignments)
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary)
    {b : Link (PeriodicLattice.meshSize L (K : ℤ))}
    (hb : b ∈ (W.links : Set _) ∪ W.rim) (hbW : b ∉ W.links) :
    fieldOfPositive (Function.extend (imageLink W) V v) b = fieldOfPositive v b := by
  rw [fieldOfPositive_apply hL hm _ (isPositivelyOriented_of_mem hb),
    fieldOfPositive_apply hL hm v (isPositivelyOriented_of_mem hb)]
  refine Function.extend_apply' _ _ _ ?_
  rintro ⟨s, hs⟩
  have e : (s : Link _) = b :=
    hinj (Or.inl (Finset.mem_coe.2 s.2)) hb (congrArg Subtype.val hs)
  exact hbW (e ▸ s.2)
private theorem fieldOfPositive_extend_inside (hL : 2 ≤ L) (hm : 1 ≤ m)
    (hinj : InjOn (projectLink L m (K : ℤ)) ((W.links : Set _) ∪ W.rim)) (V : W.Assignments)
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary)
    (b : W.links) :
    fieldOfPositive (Function.extend (imageLink W) V v) b = V b := by
  rw [fieldOfPositive_apply hL hm _ (W.isPositive b b.2)]
  exact (imageLink_injective hinj).extend_apply V v b
private theorem fieldOfPositive_extend_eq_glue (hL : 2 ≤ L) (hm : 1 ≤ m)
    (ha : 0 < PeriodicLattice.meshSize L (K : ℤ))
    (hinj : InjOn (projectLink L m (K : ℤ)) ((W.links : Set _) ∪ W.rim)) (V : W.Assignments)
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary)
    {b : Link (PeriodicLattice.meshSize L (K : ℤ))} (hb : b ∈ (W.links : Set _) ∪ W.rim) :
    fieldOfPositive (Function.extend (imageLink W) V v) b =
      W.glue ha V (fieldOfPositive v) b := by
  classical
  by_cases hbW : b ∈ W.links
  · rw [fieldOfPositive_extend_inside hL hm hinj V v ⟨b, hbW⟩]
    simp [LinkWindow.glue, hbW]
  · have hrev : b.opposite ∉ W.links := fun h' =>
      Link.opposite_not_isPositivelyOriented ha (isPositivelyOriented_of_mem hb)
        (W.isPositive _ h')
    rw [fieldOfPositive_extend_of_not_mem hL hm hinj V v hb hbW]
    simp [LinkWindow.glue, hbW, hrev]
private theorem mem_links_union_rim_of_mem_edges
    {p : ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ))}
    (hp : p ∈ W.faces) {b : Link (PeriodicLattice.meshSize L (K : ℤ))} (hb : b ∈ p.edges) :
    b ∈ (W.links : Set _) ∪ W.rim := by
  by_cases hbW : b ∈ W.links
  · exact Or.inl (Finset.mem_coe.2 hbW)
  · exact Or.inr ⟨⟨p, hp, hb⟩, hbW⟩
private theorem projectFace_injOn
    (hinj : InjOn (projectLink L m (K : ℤ)) ((W.links : Set _) ∪ W.rim)) :
    InjOn (projectFace (L := L) (m := m) (j := (K : ℤ))) W.faces := by
  intro p hp p' hp' h
  have hf' : p.lowAxis = p'.lowAxis := congrArg PeriodicLattice.Plaquette.firstAxis h
  have hs : p.highAxis = p'.highAxis := congrArg PeriodicLattice.Plaquette.secondAxis h
  have hbase : projectPoint L m (K : ℤ) p.corner = projectPoint L m (K : ℤ) p'.corner :=
    congrArg PeriodicLattice.Plaquette.origin h
  have e1 : projectLink L m (K : ℤ) (Link.forwardFrom p.corner p.lowAxis) =
      projectLink L m (K : ℤ) (Link.forwardFrom p'.corner p'.lowAxis) := by
    rw [projectLink_forwardFrom, projectLink_forwardFrom, hbase, hf']
  have e2 := hinj (mem_links_union_rim_of_mem_edges hp (by simp [ElementaryPlaquette.edges]))
    (mem_links_union_rim_of_mem_edges hp' (by simp [ElementaryPlaquette.edges])) e1
  exact ElementaryPlaquette.ext (congrArg Link.initial e2) hf' hs
private theorem mem_image_projectFace (hL : 1 < L) (P : PeriodicLattice.Plaquette L m (K : ℤ))
    {l : PeriodicLattice.Bond L m (K : ℤ)} (hl : l ∈ WilsonOperator.periodicEdgeList P)
    {b : Link (PeriodicLattice.meshSize L (K : ℤ))} (hbW : b ∈ W.links)
    (hlb : l = projectLink L m (K : ℤ) b) : P ∈ projectFace '' W.faces := by
  have hb := W.isPositive b hbW
  simp only [WilsonOperator.periodicEdgeList, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h | h | h | h
  · obtain ⟨x, hx, hbx⟩ := exists_lift_of_forwardFrom hL P.origin 0 P.firstAxis hb
      (by rw [projectPoint_zero, add_zero, ← h, hlb])
    rw [add_zero] at hbx
    refine ⟨⟨x, P.firstAxis, P.secondAxis, P.firstAxis_lt_secondAxis⟩, ⟨b, ?_, hbW⟩,
      PeriodicLattice.Plaquette.ext hx rfl rfl⟩
    rw [hbx]
    simp [ElementaryPlaquette.edges]
  · obtain ⟨x, hx, hbx⟩ := exists_lift_of_forwardFrom hL P.origin (axisStep _ P.firstAxis)
      P.secondAxis hb (by rw [projectPoint_axisStep, ← h, hlb])
    refine ⟨⟨x, P.firstAxis, P.secondAxis, P.firstAxis_lt_secondAxis⟩, ⟨b, ?_, hbW⟩,
      PeriodicLattice.Plaquette.ext hx rfl rfl⟩
    rw [hbx]
    simp [ElementaryPlaquette.edges]
  · obtain ⟨x, hx, hbx⟩ := exists_lift_of_forwardFrom hL P.origin (axisStep _ P.secondAxis)
      P.firstAxis hb (by rw [projectPoint_axisStep, ← h, hlb])
    refine ⟨⟨x, P.firstAxis, P.secondAxis, P.firstAxis_lt_secondAxis⟩, ⟨b, ?_, hbW⟩,
      PeriodicLattice.Plaquette.ext hx rfl rfl⟩
    rw [hbx]
    simp [ElementaryPlaquette.edges]
  · obtain ⟨x, hx, hbx⟩ := exists_lift_of_forwardFrom hL P.origin 0 P.secondAxis hb
      (by rw [projectPoint_zero, add_zero, ← h, hlb])
    rw [add_zero] at hbx
    refine ⟨⟨x, P.firstAxis, P.secondAxis, P.firstAxis_lt_secondAxis⟩, ⟨b, ?_, hbW⟩,
      PeriodicLattice.Plaquette.ext hx rfl rfl⟩
    rw [hbx]
    simp [ElementaryPlaquette.edges]
private def exteriorEnergy (W : LinkWindow (PeriodicLattice.meshSize L (K : ℤ)))
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary) : ℝ :=
  ∑ᶠ P ∈ (univ \ (projectFace '' W.faces : Set (PeriodicLattice.Plaquette L m (K : ℤ)))),
    PeriodicLattice.plaquetteCost (PeriodicLattice.gaugeFieldOfPositive v) P
private theorem boltzmannWeight_split (hL : 2 ≤ L) (hm : 1 ≤ m)
    [Finite (PeriodicLattice.Plaquette L m (K : ℤ))]
    (hinj : InjOn (projectLink L m (K : ℤ)) ((W.links : Set _) ∪ W.rim)) (β : ℝ)
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary) :
    PeriodicLattice.boltzmannWeight β (PeriodicLattice.gaugeFieldOfPositive v) =
      Real.exp (-β * ∑ᶠ p ∈ W.faces, faceEnergy (fieldOfPositive v) p) *
        Real.exp (-β * exteriorEnergy W v) := by
  have h₁ : PeriodicLattice.wilsonAction (PeriodicLattice.gaugeFieldOfPositive v) =
      (∑ᶠ P ∈ (projectFace '' W.faces : Set (PeriodicLattice.Plaquette L m (K : ℤ))),
        PeriodicLattice.plaquetteCost (PeriodicLattice.gaugeFieldOfPositive v) P) +
        exteriorEnergy W v := by
    have e := finsum_mem_add_sdiff
      (subset_univ (projectFace '' W.faces : Set (PeriodicLattice.Plaquette L m (K : ℤ))))
      finite_univ
      (f := fun P => PeriodicLattice.plaquetteCost (PeriodicLattice.gaugeFieldOfPositive v) P)
    rw [finsum_mem_univ] at e
    exact e.symm
  have h₂ : ∑ᶠ P ∈ (projectFace '' W.faces : Set (PeriodicLattice.Plaquette L m (K : ℤ))),
      PeriodicLattice.plaquetteCost (PeriodicLattice.gaugeFieldOfPositive v) P =
      ∑ᶠ p ∈ W.faces, faceEnergy (fieldOfPositive v) p := by
    rw [finsum_mem_image (projectFace_injOn hinj)]
    exact finsum_mem_congr rfl fun p _ => plaquetteCost_projectFace hL hm v p
  rw [PeriodicLattice.boltzmannWeight, h₁, h₂, ← Real.exp_add]
  congr 1
  ring
private theorem exteriorEnergy_extend (hL : 2 ≤ L) (hm : 1 ≤ m) (V : W.Assignments)
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary) :
    exteriorEnergy W (Function.extend (imageLink W) V v) = exteriorEnergy W v := by
  refine finsum_mem_congr rfl fun P hP => WilsonOperator.periodic_plaquetteEnergy_congr
    (gaugeFieldOfPositive_mem hL hm _) (gaugeFieldOfPositive_mem hL hm _) P fun l hl => ?_
  have hlpos : l.IsPositivelyOriented := by
    simp only [WilsonOperator.periodicEdgeList, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;>
      exact PeriodicLattice.mem_positiveBonds_iff.1 ⟨_, _, rfl⟩
  rw [gaugeFieldOfPositive_of_pos _ hlpos, gaugeFieldOfPositive_of_pos _ hlpos]
  refine congrArg Subtype.val (Function.extend_apply' _ _ _ ?_)
  rintro ⟨s, hs⟩
  exact hP.2 (mem_image_projectFace (by omega) P hl s.2 (congrArg Subtype.val hs).symm)
private theorem boltzmannWeight_extend (hL : 2 ≤ L) (hm : 1 ≤ m)
    [Finite (PeriodicLattice.Plaquette L m (K : ℤ))]
    (ha : 0 < PeriodicLattice.meshSize L (K : ℤ))
    (hinj : InjOn (projectLink L m (K : ℤ)) ((W.links : Set _) ∪ W.rim)) (β : ℝ)
    (V : W.Assignments)
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary) :
    PeriodicLattice.boltzmannWeight β
        (PeriodicLattice.gaugeFieldOfPositive (Function.extend (imageLink W) V v)) =
      W.boltzmannWeight ha β V (fieldOfPositive v) * Real.exp (-β * exteriorEnergy W v) := by
  have e : ∑ᶠ p ∈ W.faces,
      faceEnergy (fieldOfPositive (Function.extend (imageLink W) V v)) p =
      ∑ᶠ p ∈ W.faces, faceEnergy (W.glue ha V (fieldOfPositive v)) p := by
    refine finsum_mem_congr rfl fun p hp => ?_
    have key : ∀ b ∈ p.edges, fieldOfPositive (Function.extend (imageLink W) V v) b =
        W.glue ha V (fieldOfPositive v) b := fun b hb =>
      fieldOfPositive_extend_eq_glue hL hm ha hinj V v (mem_links_union_rim_of_mem_edges hp hb)
    simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at key
    obtain ⟨h1, h2, h3, h4⟩ := key
    simp only [faceEnergy, faceHolonomy, h1, h2, h3, h4]
  rw [boltzmannWeight_split hL hm hinj, exteriorEnergy_extend hL hm, e]
  rfl
private theorem inner_integral_eq (hL : 2 ≤ L) (hm : 1 ≤ m)
    [Finite (PeriodicLattice.Plaquette L m (K : ℤ))]
    (ha : 0 < PeriodicLattice.meshSize L (K : ℤ))
    (hinj : InjOn (projectLink L m (K : ℤ)) ((W.links : Set _) ∪ W.rim)) {β : ℝ}
    (hk1 : ∀ U : GaugeField (PeriodicLattice.meshSize L (K : ℤ)),
      ∫ V, W.densityKernel ha β V U ∂W.haarProd = 1)
    (f : W.Assignments → ℝ)
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary) :
    ∫ V, PeriodicLattice.boltzmannWeight β
        (PeriodicLattice.gaugeFieldOfPositive (Function.extend (imageLink W) V v)) *
        f (W.restrictInside (fieldOfPositive (Function.extend (imageLink W) V v))) ∂W.haarProd =
      ∫ V, PeriodicLattice.boltzmannWeight β
        (PeriodicLattice.gaugeFieldOfPositive (Function.extend (imageLink W) V v)) *
        (∫ V', f V' * W.densityKernel ha β V'
          (fieldOfPositive (Function.extend (imageLink W) V v)) ∂W.haarProd)
        ∂W.haarProd := by
  have hrest : ∀ V : W.Assignments,
      W.restrictInside (fieldOfPositive (Function.extend (imageLink W) V v)) = V :=
    fun V => funext fun b => fieldOfPositive_extend_inside hL hm hinj V v b
  have hbdry : ∀ V : W.Assignments,
      W.restrictRim (fieldOfPositive (Function.extend (imageLink W) V v)) =
        W.restrictRim (fieldOfPositive v) :=
    fun V => funext fun b => fieldOfPositive_extend_of_not_mem hL hm hinj V v (Or.inr b.2) b.2.2
  have hkerK : ∀ (V' V : W.Assignments),
      W.densityKernel ha β V' (fieldOfPositive (Function.extend (imageLink W) V v)) =
        W.densityKernel ha β V' (fieldOfPositive v) := by
    intro V' V
    have hw : ∀ V'' : W.Assignments,
        W.boltzmannWeight ha β V'' (fieldOfPositive (Function.extend (imageLink W) V v)) =
          W.boltzmannWeight ha β V'' (fieldOfPositive v) :=
      fun V'' => W.boltzmannWeight_congr ha β V'' (hbdry V)
    simp only [LinkWindow.densityKernel, hw]
  set z : ℝ := ∫ V, W.boltzmannWeight ha β V (fieldOfPositive v) ∂W.haarProd with hzdef
  have hk : ∀ V : W.Assignments, W.densityKernel ha β V (fieldOfPositive v) =
      W.boltzmannWeight ha β V (fieldOfPositive v) / z :=
    fun V => rfl
  have hz : z ≠ 0 := by
    intro h0
    have h1 := hk1 (fieldOfPositive v)
    simp only [hk, h0, div_zero, integral_zero] at h1
    exact zero_ne_one h1
  have hΨ : ∫ V, f V * W.densityKernel ha β V (fieldOfPositive v) ∂W.haarProd =
      (∫ V, f V * W.boltzmannWeight ha β V (fieldOfPositive v) ∂W.haarProd) / z := by
    rw [← integral_div]
    refine integral_congr_ae (ae_of_all _ fun V => ?_)
    simp only [hk, mul_div_assoc]
  have e₁ : ∀ V : W.Assignments, PeriodicLattice.boltzmannWeight β
      (PeriodicLattice.gaugeFieldOfPositive (Function.extend (imageLink W) V v)) *
        f (W.restrictInside (fieldOfPositive (Function.extend (imageLink W) V v))) =
      f V * W.boltzmannWeight ha β V (fieldOfPositive v) * Real.exp (-β * exteriorEnergy W v) :=
    fun V => by
      rw [boltzmannWeight_extend hL hm ha hinj, hrest]
      ring
  have e₂ : ∀ V : W.Assignments, PeriodicLattice.boltzmannWeight β
      (PeriodicLattice.gaugeFieldOfPositive (Function.extend (imageLink W) V v)) *
        (∫ V', f V' * W.densityKernel ha β V'
          (fieldOfPositive (Function.extend (imageLink W) V v)) ∂W.haarProd) =
      W.boltzmannWeight ha β V (fieldOfPositive v) *
        (Real.exp (-β * exteriorEnergy W v) *
          ∫ V', f V' * W.densityKernel ha β V' (fieldOfPositive v) ∂W.haarProd) :=
    fun V => by
      rw [boltzmannWeight_extend hL hm ha hinj]
      simp only [hkerK]
      ring
  simp only [e₁, e₂]
  rw [integral_mul_const, integral_mul_const, ← hzdef, hΨ]
  field_simp
private theorem measurable_and_bounded_kernelMean {a : ℝ} (W : LinkWindow a)
    {k : W.Assignments → GaugeField a → ℝ}
    (hk : Continuous fun x : W.Assignments × GaugeField a => k x.1 x.2) {B : ℝ}
    (hk0 : ∀ V U, 0 ≤ k V U) (hkB : ∀ V U, k V U ≤ B) {f : W.Assignments → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ V, |f V| ≤ C) :
    Measurable (fun U => ∫ V, f V * k V U ∂W.haarProd) ∧
      ∀ U, ‖∫ V, f V * k V U ∂W.haarProd‖ ≤ C * B := by
  have := secondCountable_gaugeField (a := a)
  have := isProbabilityMeasure_haarProd W
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 1)
  have hkm : Measurable fun q : GaugeField a × W.Assignments => f q.2 * k q.2 q.1 :=
    (hf.comp measurable_snd).mul (hk.measurable.comp measurable_swap)
  refine ⟨(hkm.stronglyMeasurable.integral_prod_right' (ν := W.haarProd)).measurable,
    fun U => ?_⟩
  have h := norm_integral_le_of_norm_le_const (μ := W.haarProd)
    (f := fun V => f V * k V U) (C := C * B)
    (ae_of_all _ fun V => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hk0 V U)]
      exact mul_le_mul (hC V) (hkB V U) (hk0 V U) hC0)
  simpa using h
private theorem integral_restrictInside_eq (hProd : ComplexMatrix2.FiniteProductGroupStatement)
    (hKer : windowKernelContinuousBounded) (hLog : ComplexMatrix2.UnitaryLogarithmProperties)
    (hL : 2 ≤ L) (hm : 1 ≤ m) [Finite (PeriodicLattice.Plaquette L m (K : ℤ))]
    [Finite (PeriodicLattice.PositivelyOrientedBond L m (K : ℤ))] {β : ℝ} (hβ : 0 < β)
    (ha : 0 < PeriodicLattice.meshSize L (K : ℤ))
    (hinj : InjOn (projectLink L m (K : ℤ)) ((W.links : Set _) ∪ W.rim))
    {f : W.Assignments → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ V, |f V| ≤ C) :
    ∫ U, f (W.restrictInside U) ∂liftedWilsonMeasure L m K β =
      ∫ U, (∫ V, f V * W.densityKernel ha β V U ∂W.haarProd) ∂liftedWilsonMeasure L m K β := by
  obtain ⟨hkc, hkb, hk1⟩ := hKer _ ha β hβ W
  have := secondCountable_gaugeField (a := PeriodicLattice.meshSize L (K : ℤ))
  have := isProbabilityMeasure_haarProd W
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 1)
  have hcr : Continuous W.restrictInside :=
    continuous_pi fun _ => continuous_gaugeField_eval _
  have hG₁ : Measurable fun U => f (W.restrictInside U) := hf.comp hcr.measurable
  have hB0 : 0 ≤ Real.exp (2 * β * W.faceCount) := (Real.exp_pos _).le
  obtain ⟨hG₂, hG₂b⟩ := measurable_and_bounded_kernelMean W (k := W.densityKernel ha β) hkc
    (fun V U => (Real.exp_pos _).le.trans (hkb V U).1) (fun V U => (hkb V U).2) hf hC
  have hcfg := measurable_gaugeFieldOfPositive (L := L) (m := m) (j := (K : ℤ))
  have hper := measurable_liftField L m (K : ℤ)
  have hden := measurable_boltzmannWeight (L := L) (m := m) (j := (K : ℤ)) β
  have hTm : Measurable (fieldOfPositive (L := L) (m := m) (K := K)) := hper.comp hcfg
  have hρm : Measurable fun v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) →
      ComplexMatrix2.specialUnitary =>
      PeriodicLattice.boltzmannWeight β (PeriodicLattice.gaugeFieldOfPositive v) :=
    hden.comp hcfg
  have hbound : ∀ {D : ℝ} {G : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℝ}, 0 ≤ D →
      (∀ U, ‖G U‖ ≤ D) → ∀ v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) →
        ComplexMatrix2.specialUnitary,
        ‖PeriodicLattice.boltzmannWeight β (PeriodicLattice.gaugeFieldOfPositive v) *
          G (fieldOfPositive v)‖ ≤ D := by
    intro D G hD hG v
    have hp : 0 < PeriodicLattice.boltzmannWeight β (PeriodicLattice.gaugeFieldOfPositive v) :=
      Real.exp_pos _
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos hp]
    calc _ ≤ 1 * D :=
          mul_le_mul (boltzmannWeight_le_one hLog hL hm hβ v) (hG _) (norm_nonneg _) zero_le_one
      _ = D := one_mul D
  rw [integral_liftedWilsonMeasure hG₁, integral_liftedWilsonMeasure hG₂]
  congr 1
  have r₁ := integral_resample_image hProd (imageLink_injective hinj)
    (h := fun v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) →
      ComplexMatrix2.specialUnitary =>
      PeriodicLattice.boltzmannWeight β (PeriodicLattice.gaugeFieldOfPositive v) *
        f (W.restrictInside (fieldOfPositive v))) (hρm.mul (hG₁.comp hTm))
    (hbound (G := fun U => f (W.restrictInside U)) hC0
      (fun U => by rw [Real.norm_eq_abs]; exact hC _))
  have r₂ := integral_resample_image hProd (imageLink_injective hinj)
    (h := fun v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) →
      ComplexMatrix2.specialUnitary =>
      PeriodicLattice.boltzmannWeight β (PeriodicLattice.gaugeFieldOfPositive v) *
        ∫ V, f V * W.densityKernel ha β V (fieldOfPositive v) ∂W.haarProd)
    (hρm.mul (hG₂.comp hTm))
    (hbound (G := fun U => ∫ V, f V * W.densityKernel ha β V U ∂W.haarProd)
      (mul_nonneg hC0 hB0) hG₂b)
  refine r₁.symm.trans (Eq.trans ?_ r₂)
  exact integral_congr_ae (ae_of_all _ fun v => inner_integral_eq hL hm ha hinj hk1 f v)
end Equation
end WindowEquilibrium
open WindowEquilibrium in
theorem torusMeasuresSatisfyWindowEquilibrium_of_inputs
    (hProd : ComplexMatrix2.FiniteProductGroupStatement)
    (hKer : windowKernelContinuousBounded) (hLog : ComplexMatrix2.UnitaryLogarithmProperties)
    (hAct : PeriodicLattice.WilsonActionPlaquetteSumAndHaarSymmetry)
    (hCpt : PeriodicLattice.GaugeFieldsCompactProduct.Statement) :
    torusMeasuresSatisfyWindowEquilibrium := by
  intro L K β ha W hL hβ
  have hS : ((W.links : Set (Link (PeriodicLattice.meshSize L (K : ℤ)))) ∪ W.rim).Finite := by
    refine W.links.finite_toSet.union ?_
    refine (WilsonOperator.thickenedLinks_finite W.links).subset ?_
    rintro b ⟨⟨p, hp, hb⟩, -⟩
    exact Or.inr (Set.mem_biUnion hp hb)
  obtain ⟨m₀, hm₀⟩ := exists_injOn_projectLink hL hS
  refine ⟨m₀ + 1, fun m hm => ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hL2 : 2 ≤ L := hL
  have hP : Finite (PeriodicLattice.Plaquette L m (K : ℤ)) :=
    (hAct L m (K : ℤ) hL (by omega) (by omega)).2.1
  have hB : Finite (PeriodicLattice.Bond L m (K : ℤ)) :=
    (hCpt L m (K : ℤ) (by omega) (by omega)).1
  have hPos : Finite (PeriodicLattice.PositivelyOrientedBond L m (K : ℤ)) := Subtype.finite
  exact ⟨isProbabilityMeasure_liftedWilsonMeasure hProd hLog hL2 hm1 hβ, fun f hf ⟨C, hCf⟩ =>
    integral_restrictInside_eq hProd hKer hLog hL2 hm1 hβ ha (hm₀ m (by omega)) hf hCf⟩
end YangMills.Construction.HullsInEveryVolume
end

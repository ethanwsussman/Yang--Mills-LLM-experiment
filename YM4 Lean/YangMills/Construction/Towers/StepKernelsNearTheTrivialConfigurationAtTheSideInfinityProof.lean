import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyProof
import YangMills.Construction.Lattice.AverageOfAConfigurationTrivialInsideTwoBlocksProof
import YangMills.Construction.Towers.ComplexAverageLiesInTheComplexGroupProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.StepKernelsAreHolomorphicAtTheSideInfinity
import YangMills.Construction.Towers.StepKernelsNearOneOnASideProof
import YangMills.Construction.Towers.StepKernelsNearTheTrivialConfigurationAtTheSideInfinity
import YangMills.Construction.Towers.TransposesAndRelationsOfTheScaledPicture
import Mathlib
set_option autoImplicit false
open Set Metric
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.StepKernelsNearIdentity
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.DoubleBlockPolydisc.Infinite (polydiscPositive positiveDoubleBlockBonds)
section Curve
variable {σ : Type}
def expCurve (Λ : σ → ComplexMatrix2) (z : ℂ) : σ ⊕ Empty → ComplexMatrix2 :=
  Sum.elim (fun s => ComplexMatrix2.matExp (z • Λ s)) fun e => e.elim
def curveDirection (Λ : σ → ComplexMatrix2) : σ ⊕ Empty → ComplexMatrix2 := Sum.elim Λ fun e => e.elim
theorem matExp_smul_mul_matExp_smul (Y : ComplexMatrix2) (w z : ℂ) :
    ComplexMatrix2.matExp (w • Y) * ComplexMatrix2.matExp (z • Y) = ComplexMatrix2.matExp ((w + z) • Y) := by apply _root_.YangMills.Construction.Tower.NearIdentityStepKernels.matExp_smul_mul_matExp_smul <;> assumption
theorem expChartAt_expCurve (Λ : σ → ComplexMatrix2) (z₀ z : ℂ) :
    GroupLieProduct.expChartAt (expCurve Λ z₀) ((z - z₀) • curveDirection Λ) = expCurve Λ z := by
  funext i
  rcases i with s | e
  · show ComplexMatrix2.matExp ((z - z₀) • Λ s) * ComplexMatrix2.matExp (z₀ • Λ s) = ComplexMatrix2.matExp (z • Λ s)
    rw [matExp_smul_mul_matExp_smul, sub_add_cancel]
  · exact e.elim
theorem exists_tupleOfCoords_smul {τ : Type} [Fintype τ] (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : τ ≃ Fin (Fintype.card τ)) {A : τ → ComplexMatrix2} (hA : ∀ i, A i ∈ ComplexMatrix2.traceless) :
    ∃ w, ∀ t : ℂ, GroupLieProduct.tupleOfCoords β ν (t • w) = t • A := by
  refine ⟨fun m => β.repr ⟨A (ν.symm (finProdFinEquiv.symm m).1), hA _⟩ (finProdFinEquiv.symm m).2,
    fun t => ?_⟩
  funext i
  have h := congrArg Subtype.val (β.sum_repr ⟨A i, hA i⟩)
  have h' : ∑ c : Fin 3, (β.repr ⟨A i, hA i⟩ c) • (β c : ComplexMatrix2) = A i := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
  show ∑ c : Fin 3, (t • fun m => β.repr ⟨A (ν.symm (finProdFinEquiv.symm m).1), hA _⟩
      (finProdFinEquiv.symm m).2) (finProdFinEquiv (ν i, c)) • (β c : ComplexMatrix2) = t • A i
  simp only [Pi.smul_apply, Equiv.symm_apply_apply, smul_eq_mul, Equiv.symm_apply_apply]
  refine Eq.trans ?_ (congrArg (t • ·) h')
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun c _ => mul_smul _ _ _
theorem differentiableAt_comp_expCurve [Fintype σ]
    (hD : Coordinates.ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {W : Set (σ ⊕ Empty → ComplexMatrix2)}
    {Φ : (σ ⊕ Empty → ComplexMatrix2) → ℂ}
    (hΦ : GroupLieProduct.IsHolomorphicToCoords β LeftChartFields.scalarCoords W Φ)
    {Λ : σ → ComplexMatrix2} (hΛ : ∀ s, Λ s ∈ ComplexMatrix2.traceless) {z₀ : ℂ} (hz₀ : expCurve Λ z₀ ∈ W) :
    DifferentiableAt ℂ (fun z => Φ (expCurve Λ z)) z₀ := by
  obtain ⟨-, -, hp⟩ := hΦ
  obtain ⟨O, h0, -, -, hhol⟩ := hp _ hz₀
  have hA : ∀ i, curveDirection Λ i ∈ ComplexMatrix2.traceless := by
    rintro (s | e)
    · exact hΛ s
    · exact e.elim
  obtain ⟨w, hw⟩ := exists_tupleOfCoords_smul β (Fintype.equivFin (σ ⊕ Empty)) hA
  have hh := hhol (Fintype.equivFin (σ ⊕ Empty))
  have hdiff := (hD _ _ _ _ hh.1).1 hh
  have hT0 : GroupLieProduct.tupleOfCoords β (Fintype.equivFin (σ ⊕ Empty)) 0 = 0 := by
    simpa using hw 0
  have hmem : (0 : Coordinates.ComplexCoordinates _) ∈
      GroupLieProduct.tupleOfCoords β (Fintype.equivFin (σ ⊕ Empty)) ⁻¹' O := by
    show GroupLieProduct.tupleOfCoords β (Fintype.equivFin (σ ⊕ Empty)) 0 ∈ O
    rw [hT0]
    exact h0
  have hd0 := hdiff.differentiableAt (hh.1.mem_nhds hmem)
  have hline : DifferentiableAt ℂ (fun z : ℂ => (z - z₀) • w) z₀ := by fun_prop
  have hcomp := DifferentiableAt.comp z₀ (by simp only [sub_self, zero_smul]; exact hd0) hline
  have hcoord := DifferentiableAt.comp z₀
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).differentiableAt hcomp
  refine hcoord.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  show Φ (expCurve Λ z) = LeftChartFields.scalarCoords (Φ (GroupLieProduct.expChartAt (expCurve Λ z₀)
    (GroupLieProduct.tupleOfCoords β (Fintype.equivFin (σ ⊕ Empty)) ((z - z₀) • w)))) 0
  rw [hw, expChartAt_expCurve]
  rfl
theorem norm_sub_le_of_norm_le_on_ball {g : ℂ → ComplexMatrix2} {R M : ℝ} (hR : 1 < R)
    (hd : DifferentiableOn ℂ g (ball 0 R)) (hb : ∀ z ∈ ball (0 : ℂ) R, ‖g z‖ ≤ M) :
    ‖g 1 - g 0‖ ≤ 2 * M / R := by apply _root_.YangMills.Construction.Tower.NearIdentityStepKernels.norm_sub_le_of_differentiableOn_ball <;> assumption
end Curve
section Exponentials
theorem real_exp_sub_one_lt_three_quarters {x r : ℝ} (h0 : 0 ≤ x) (hx : x < r / 2) (hr : r ≤ 1) :
    Real.exp x - 1 < 3 / 4 * r := by
  have h1 : |x| ≤ 1 := by
    rw [abs_of_nonneg h0]
    linarith
  have h2 := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le h1)).2
  nlinarith
theorem matExp_sub_one_lt (hX : ComplexMatrix2.ExpLogEstimates) {Y : ComplexMatrix2} {r : ℝ}
    (hY : ComplexMatrix2.operatorNorm Y < r / 2) (hr : r ≤ 1) :
    ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp Y - 1) < 3 / 4 * r :=
  ((hX.1 Y).2).trans_lt (real_exp_sub_one_lt_three_quarters (norm_nonneg _) hY hr)
theorem inv_matExp_sub_one_lt (hX : ComplexMatrix2.ExpLogEstimates) {Y : ComplexMatrix2} {r : ℝ}
    (hY : ComplexMatrix2.operatorNorm Y < r / 2) (hr : r ≤ 1) :
    ComplexMatrix2.operatorNorm ((ComplexMatrix2.matExp Y)⁻¹ - 1) < 3 / 4 * r := by
  have e : (ComplexMatrix2.matExp Y)⁻¹ = ComplexMatrix2.matExp (-Y) := (Matrix.exp_neg Y).symm
  rw [e]
  exact matExp_sub_one_lt hX (by simpa using hY) hr
theorem matExp_mem_complexGaugeGroup (hX : ComplexMatrix2.ExpLogEstimates) {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.traceless) : ComplexMatrix2.matExp Y ∈ PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.ComplexMeanMembership.matExp_mem <;> assumption
theorem logSeries_props (hX : ComplexMatrix2.ExpLogEstimates) {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.complexGaugeGroup) {s : ℝ} (hs : ComplexMatrix2.operatorNorm (g - 1) ≤ s)
    (hs' : s ≤ 1 / 8) :
    ComplexMatrix2.logSeries g ∈ ComplexMatrix2.traceless ∧
      ComplexMatrix2.operatorNorm (ComplexMatrix2.logSeries g) ≤ 2 * s ∧
      ComplexMatrix2.matExp (ComplexMatrix2.logSeries g) = g := by
  have hn : ComplexMatrix2.operatorNorm (g - 1) < 1 := by linarith
  have h0 : 0 ≤ ComplexMatrix2.operatorNorm (g - 1) := norm_nonneg _
  have e : 1 + (g - 1) = g := add_sub_cancel _ _
  obtain ⟨h1, h2, -, -, h3⟩ := hX.2.2.2.1 (g - 1) hn
  rw [e] at h1 h3
  refine ⟨(hX.2.2.2.2.2.2.1 g hg (by linarith)).2, ?_, h3⟩
  have h4 : ComplexMatrix2.operatorNorm (g - 1) / (1 - ComplexMatrix2.operatorNorm (g - 1)) ≤ 2 * s := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith
end Exponentials
section Bonds
variable {a : ℝ}
theorem isPositivelyOriented_or_opposite (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem not_isPositivelyOriented_opposite (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
end Bonds
theorem inv_inv_of_mem_complexGaugeGroup {X : ComplexMatrix2} (h : X ∈ PeriodicLattice.complexGaugeGroup) :
    X⁻¹⁻¹ = X := by apply _root_.YangMills.SharedProofs.p6288 <;> assumption
theorem inv_mem_complexGaugeGroup {X : ComplexMatrix2} (h : X ∈ PeriodicLattice.complexGaugeGroup) :
    X⁻¹ ∈ PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
section Values
variable {L k j : ℕ} {c : Edge L k (j + 1)}
abbrev extendByOne (c : Edge L k (j + 1)) (v : positiveDoubleBlockBonds L k j c → ComplexMatrix2) :
    Edge L k j → ComplexMatrix2 :=
  DoubleBlockPolydisc.Infinite.fieldOfValues L k j c v
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem opposite_mem_doubleCubeLinks {b : Edge L k j}
    (hb : b ∈ doubleCubeLinks L (meshAt L k j) c) :
    b.opposite ∈ doubleCubeLinks L (meshAt L k j) c := ⟨hb.2, hb.1⟩
theorem extendByOne_positive (v : positiveDoubleBlockBonds L k j c → ComplexMatrix2)
    (b : positiveDoubleBlockBonds L k j c) : extendByOne c v b.1 = v b := by
  show extendFromPositive _ v b.1 = v b
  unfold extendFromPositive
  exact dif_pos b.2
theorem extendByOne_opposite (ha : 0 < meshAt L k j) (v : positiveDoubleBlockBonds L k j c → ComplexMatrix2)
    (b : positiveDoubleBlockBonds L k j c) : extendByOne c v b.1.opposite = (v b)⁻¹ := by
  show extendFromPositive _ v b.1.opposite = (v b)⁻¹
  unfold extendFromPositive
  rw [dif_neg fun h => not_isPositivelyOriented_opposite ha b.2.2 h.2]
  exact dif_pos b.2
theorem extendByOne_of_not_mem (v : positiveDoubleBlockBonds L k j c → ComplexMatrix2) {b : Edge L k j}
    (hb : b ∉ doubleCubeLinks L (meshAt L k j) c) :
    extendByOne c v b = 1 := by
  show extendFromPositive _ v b = 1
  unfold extendFromPositive
  rw [dif_neg fun h => hb h.1, dif_neg fun h => hb (opposite_mem_doubleCubeLinks h.1)]
theorem extendByOne_one :
    extendByOne c (fun _ => 1) = fun _ => 1 := by
  funext b
  show extendFromPositive _ _ b = 1
  unfold extendFromPositive
  split_ifs <;> simp
def IsNearOne (r : ℝ) (W : Edge L k j → ComplexMatrix2) : Prop :=
  W ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup ∧
    ∀ b, ComplexMatrix2.operatorNorm (W b - 1) < r
theorem edge_trichotomy (b : Edge L k j) :
    (∃ p : positiveDoubleBlockBonds L k j c, b = p.1) ∨
      (∃ p : positiveDoubleBlockBonds L k j c, b = p.1.opposite) ∨
      (b ∉ doubleCubeLinks L (meshAt L k j) c ∧
        b.opposite ∉ doubleCubeLinks L (meshAt L k j) c) := by
  by_cases hb : b ∈ doubleCubeLinks L (meshAt L k j) c
  · rcases isPositivelyOriented_or_opposite b with hp | hp
    · exact Or.inl ⟨⟨b, hb, hp⟩, rfl⟩
    · exact Or.inr (Or.inl ⟨⟨b.opposite, opposite_mem_doubleCubeLinks hb, hp⟩, rfl⟩)
  · exact Or.inr (Or.inr ⟨hb, fun h => hb (opposite_mem_doubleCubeLinks h)⟩)
theorem isNearOne_extendByOne (ha : 0 < meshAt L k j) {r : ℝ} (hr : 0 < r)
    {v : positiveDoubleBlockBonds L k j c → ComplexMatrix2}
    (hG : ∀ b, v b ∈ PeriodicLattice.complexGaugeGroup)
    (hv : ∀ b, ComplexMatrix2.operatorNorm (v b - 1) < r)
    (hv' : ∀ b, ComplexMatrix2.operatorNorm ((v b)⁻¹ - 1) < r) :
    IsNearOne r (extendByOne c v) := by
  refine ⟨⟨fun b => ?_, fun b => ?_⟩, fun b => ?_⟩
  · rcases edge_trichotomy (c := c) b with ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨h, -⟩
    · rw [extendByOne_positive]
      exact hG p
    · rw [extendByOne_opposite ha]
      exact inv_mem_complexGaugeGroup (hG p)
    · rw [extendByOne_of_not_mem _ h]
      show Matrix.det (1 : ComplexMatrix2) = 1
      exact Matrix.det_one
  · rcases edge_trichotomy (c := c) b with ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨h, h'⟩
    · rw [extendByOne_positive, extendByOne_opposite ha]
    · rw [extendByOne_opposite ha]
      show extendByOne c v p.1 = _
      rw [extendByOne_positive, inv_inv_of_mem_complexGaugeGroup (hG p)]
    · rw [extendByOne_of_not_mem _ h, extendByOne_of_not_mem _ h', inv_one]
  · rcases edge_trichotomy (c := c) b with ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨h, -⟩
    · rw [extendByOne_positive]
      exact hv p
    · rw [extendByOne_opposite ha]
      exact hv' p
    · rw [extendByOne_of_not_mem _ h, sub_self]
      simpa using hr
theorem mem_polydiscPositive_of_isNearOne {r : ℝ} {v : positiveDoubleBlockBonds L k j c → ComplexMatrix2}
    (hW : IsNearOne r (extendByOne c v)) : v ∈ polydiscPositive L k j r c :=
  ⟨_, ⟨extendByOne c v,
    ⟨⟨fun b _ => hW.1.1 b, fun b _ => hW.1.2 b⟩, fun b _ => hW.2 b⟩, rfl⟩,
    funext fun b => extendByOne_positive v b⟩
end Values
theorem pauliFamily_mem_traceless (a : Fin 3) : ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
section Expansion
variable {α : Type}
def pauliExpansion (F : α → ComplexMatrix2 → ComplexMatrix2) (X : ComplexMatrix2) (W : α) : ComplexMatrix2 :=
  ∑ a', (∑ a, pauliCoeff a X * pauliCoeff a' (F W (ComplexMatrix2.pauliFamily a))) •
    ComplexMatrix2.pauliFamily a'
theorem eq_pauliExpansion {F : α → ComplexMatrix2 → ComplexMatrix2} {C : ℝ} {W : α}
    (hW : StepKernels.IsBoundedTracelessEndo (F W) C) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    F W X = pauliExpansion F X W := by
  obtain ⟨T, hT, -⟩ := hW
  have hXs : (⟨X, hX⟩ : ↥ComplexMatrix2.traceless) =
      ∑ a, pauliCoeff a X •
        (⟨ComplexMatrix2.pauliFamily a, pauliFamily_mem_traceless a⟩ : ↥ComplexMatrix2.traceless) :=
    Subtype.ext (by
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using (sum_pauliCoeff_smul hX).symm)
  have h1 : F W X = ∑ a, pauliCoeff a X • F W (ComplexMatrix2.pauliFamily a) := by
    have e := hT ⟨X, hX⟩
    simp only at e
    rw [← e, hXs, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, Submodule.coe_smul, hT]
  have h2 : ∀ a, ∑ a', pauliCoeff a' (F W (ComplexMatrix2.pauliFamily a)) • ComplexMatrix2.pauliFamily a' =
      F W (ComplexMatrix2.pauliFamily a) := fun a => by
    have hm : F W (ComplexMatrix2.pauliFamily a) ∈ ComplexMatrix2.traceless := by
      have e := hT ⟨ComplexMatrix2.pauliFamily a, pauliFamily_mem_traceless a⟩
      simp only at e
      rw [← e]
      exact (T _).2
    exact sum_pauliCoeff_smul hm
  rw [h1]
  unfold pauliExpansion
  have h3 : ∀ a, pauliCoeff a X • F W (ComplexMatrix2.pauliFamily a) =
      ∑ a', (pauliCoeff a X * pauliCoeff a' (F W (ComplexMatrix2.pauliFamily a))) •
        ComplexMatrix2.pauliFamily a' :=
    fun a => by
      conv_lhs => rw [← h2 a]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun a' _ => smul_smul _ _ _
  simp only [h3, Finset.sum_smul]
  exact Finset.sum_comm
end Expansion
section Difference
variable {L k j : ℕ} {c : Edge L k (j + 1)} {F : (Edge L k j → ComplexMatrix2) → ComplexMatrix2 → ComplexMatrix2}
theorem norm_sub_at_one_le
    (hD : Coordinates.ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    (hX : ComplexMatrix2.ExpLogEstimates) (ha : 0 < meshAt L k j)
    (hρ0 : 0 < polydiscRadius L) (hρ1 : polydiscRadius L ≤ 1)
    (hne : (positiveDoubleBlockBonds L k j c).Nonempty)
    (hend : ∀ W, IsNearOne (3 / 4 * polydiscRadius L) W →
      StepKernels.IsBoundedTracelessEndo (F W) (80 * (polydiscRadius L)⁻¹))
    (hhol : ∀ a a', StepKernelHolomorphy.IsHolomorphicInValues (3 / 4 * polydiscRadius L) c
      fun W => pauliCoeff a' (F W (ComplexMatrix2.pauliFamily a)))
    (hread : ∀ a a', StepKernelHolomorphy.DependsOnlyOnDoubleBlock (3 / 4 * polydiscRadius L) c
      fun W => pauliCoeff a' (F W (ComplexMatrix2.pauliFamily a)))
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hsm : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L / 2) {s : ℝ}
    (hs : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, ComplexMatrix2.operatorNorm (V b - 1) ≤ s)
    {X : ComplexMatrix2} (hXm : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.operatorNorm (F V X - F (fun _ => 1) X) ≤
      1280 * (polydiscRadius L)⁻¹ ^ 2 * s * ComplexMatrix2.operatorNorm X := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = polydiscRadius L := ⟨_, rfl⟩
  rw [← hρ] at hρ0 hρ1 hend hhol hread hsm ⊢
  have hr : 0 < 3 / 4 * ρ := by linarith
  have hV34 : IsNearOne (3 / 4 * ρ) V := ⟨hV, fun b => (hsm b).trans (by linarith)⟩
  have hone : IsNearOne (3 / 4 * ρ) (fun _ : Edge L k j => (1 : ComplexMatrix2)) := by
    refine ⟨⟨fun _ => ?_, fun _ => by simp⟩, fun _ => by simpa using hr⟩
    show Matrix.det (1 : ComplexMatrix2) = 1
    exact Matrix.det_one
  have bound : ∀ W, IsNearOne (3 / 4 * ρ) W →
      ComplexMatrix2.operatorNorm (F W X) ≤ 80 * ρ⁻¹ * ComplexMatrix2.operatorNorm X := fun W hW => by
    obtain ⟨T, hT, hb⟩ := hend W hW
    have h := hb ⟨X, hXm⟩
    rwa [hT] at h
  have hs0 : 0 ≤ s := by
    obtain ⟨b, hb⟩ := hne
    exact (norm_nonneg _).trans (hs b hb.1)
  have hX0 : 0 ≤ ComplexMatrix2.operatorNorm X := norm_nonneg _
  have hexpV := eq_pauliExpansion (hend V hV34) hXm
  have hexp1 := eq_pauliExpansion (hend _ hone) hXm
  have hVpoly : V ∈ nearIdentityPolydisc L k j (3 / 4 * ρ) c :=
    ⟨⟨fun b _ => hV.1 b, fun b _ => hV.2 b⟩, fun b _ => hV34.2 b⟩
  have hVs : V ∈ smallComplexFields L k j :=
    ⟨hV, fun b => by rw [← hρ]; exact (hsm b).trans (by linarith)⟩
  have hreadV : pauliExpansion F X V = pauliExpansion F X (extendByOne c fun b => V b.1) := by
    unfold pauliExpansion
    refine Finset.sum_congr rfl fun a' _ => ?_
    refine congrArg (· • ComplexMatrix2.pauliFamily a') (Finset.sum_congr rfl fun a _ => ?_)
    have e : pauliCoeff a' (F V (ComplexMatrix2.pauliFamily a)) =
        pauliCoeff a' (F (extendByOne c fun b => V b.1) (ComplexMatrix2.pauliFamily a)) :=
      hread a a' V hVs hVpoly
    rw [e]
  rcases hs0.eq_or_lt with h0 | hpos
  · have hval : (fun b : positiveDoubleBlockBonds L k j c => V b.1) = fun _ => 1 := funext fun b => by
      have h := hs b.1 b.2.1
      rw [← h0] at h
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h)
    rw [hexpV, hexp1, hreadV, hval, extendByOne_one, sub_self]
    simp only [norm_zero]
    positivity
  by_cases hbig : ρ / 8 < s
  · have h1 := bound V hV34
    have h2 := bound _ hone
    have h3 := norm_sub_le (F V X) (F (fun _ => 1) X)
    have h4 : 160 * ρ⁻¹ ≤ 1280 * ρ⁻¹ ^ 2 * s := by
      have e : 160 * ρ⁻¹ = 1280 * ρ⁻¹ ^ 2 * (ρ / 8) := by
        field_simp
        norm_num
      rw [e]
      exact mul_le_mul_of_nonneg_left hbig.le (by positivity)
    have h5 := mul_le_mul_of_nonneg_right h4 hX0
    show ‖F V X - F (fun _ => 1) X‖ ≤ _
    linarith
  rw [not_lt] at hbig
  have hs8 : s ≤ 1 / 8 := by linarith
  have hlog : ∀ b : positiveDoubleBlockBonds L k j c, ComplexMatrix2.logSeries (V b.1) ∈ ComplexMatrix2.traceless ∧
      ComplexMatrix2.operatorNorm (ComplexMatrix2.logSeries (V b.1)) ≤ 2 * s ∧
      ComplexMatrix2.matExp (ComplexMatrix2.logSeries (V b.1)) = V b.1 :=
    fun b => logSeries_props hX (hV.1 b.1) (hs b.1 b.2.1) hs8
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : positiveDoubleBlockBonds L k j c → ComplexMatrix2,
      Λ = fun b => ComplexMatrix2.logSeries (V b.1) := ⟨_, rfl⟩
  have hlogΛ : ∀ b, Λ b ∈ ComplexMatrix2.traceless ∧ ComplexMatrix2.operatorNorm (Λ b) ≤ 2 * s ∧
      ComplexMatrix2.matExp (Λ b) = V b.1 :=
    fun b => by rw [hΛ]; exact hlog b
  obtain ⟨R, hRdef⟩ : ∃ R, R = ρ / (4 * s) := ⟨_, rfl⟩
  have hR2 : 2 ≤ R := by
    rw [hRdef, le_div_iff₀ (by positivity)]
    linarith
  have hR : 1 < R := by linarith
  have hRs : R * (2 * s) = ρ / 2 := by
    rw [hRdef]
    field_simp
    norm_num
  have hsmallz : ∀ z ∈ ball (0 : ℂ) R,
      IsNearOne (3 / 4 * ρ) (extendByOne c (DoubleBlockPolydisc.leftComponents (expCurve Λ z))) := by
    intro z hz
    have hz' : ‖z‖ < R := by simpa using hz
    have hnorm : ∀ b, ComplexMatrix2.operatorNorm (z • Λ b) < ρ / 2 := fun b => by
      have e : ComplexMatrix2.operatorNorm (z • Λ b) = ‖z‖ * ComplexMatrix2.operatorNorm (Λ b) := norm_smul _ _
      rw [e, ← hRs]
      calc ‖z‖ * ComplexMatrix2.operatorNorm (Λ b) ≤ ‖z‖ * (2 * s) :=
            mul_le_mul_of_nonneg_left (hlogΛ b).2.1 (norm_nonneg _)
        _ < R * (2 * s) := mul_lt_mul_of_pos_right hz' (by positivity)
    exact isNearOne_extendByOne ha hr
      (fun b => matExp_mem_complexGaugeGroup hX (Submodule.smul_mem _ _ (hlogΛ b).1))
      (fun b => matExp_sub_one_lt hX (hnorm b) hρ1) (fun b => inv_matExp_sub_one_lt hX (hnorm b) hρ1)
  have hd : DifferentiableOn ℂ (fun z => pauliExpansion F X
      (extendByOne c (DoubleBlockPolydisc.leftComponents (expCurve Λ z)))) (ball 0 R) := by
    intro z hz
    have hent : ∀ a a', DifferentiableAt ℂ (fun z => pauliCoeff a'
        (F (extendByOne c (DoubleBlockPolydisc.leftComponents (expCurve Λ z)))
          (ComplexMatrix2.pauliFamily a))) z := by
      intro a a'
      obtain ⟨inst, hb⟩ := hhol a a'
      exact differentiableAt_comp_expCurve hD OneLoop.pauliBasis
        (hb OneLoop.pauliBasis) (fun b => (hlogΛ b).1)
        (mem_polydiscPositive_of_isNearOne (hsmallz z hz))
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold pauliExpansion
    refine DifferentiableAt.fun_sum fun a' _ => DifferentiableAt.smul_const ?_ _
    exact DifferentiableAt.fun_sum fun a _ => (hent a a').const_mul _
  have hb : ∀ z ∈ ball (0 : ℂ) R, ‖pauliExpansion F X
      (extendByOne c (DoubleBlockPolydisc.leftComponents (expCurve Λ z)))‖ ≤
        80 * ρ⁻¹ * ComplexMatrix2.operatorNorm X := fun z hz => by
    rw [← eq_pauliExpansion (hend _ (hsmallz z hz)) hXm]
    exact bound _ (hsmallz z hz)
  have hsch := norm_sub_le_of_norm_le_on_ball hR hd hb
  have hat1 : DoubleBlockPolydisc.leftComponents (expCurve Λ 1) =
      fun b : positiveDoubleBlockBonds L k j c => V b.1 := funext fun b => by
    show ComplexMatrix2.matExp ((1 : ℂ) • Λ b) = V b.1
    rw [one_smul]
    exact (hlogΛ b).2.2
  have hat0 : DoubleBlockPolydisc.leftComponents (expCurve Λ 0) =
      fun _ : positiveDoubleBlockBonds L k j c => (1 : ComplexMatrix2) := funext fun b => by
    show ComplexMatrix2.matExp ((0 : ℂ) • Λ b) = 1
    rw [zero_smul]
    exact NormedSpace.exp_zero
  simp only [hat1, hat0] at hsch
  rw [extendByOne_one, ← hreadV, ← hexpV, ← hexp1] at hsch
  refine hsch.trans ?_
  have e : 2 * (80 * ρ⁻¹ * ComplexMatrix2.operatorNorm X) / R =
      640 * ρ⁻¹ ^ 2 * s * ComplexMatrix2.operatorNorm X := by
    rw [hRdef]
    field_simp
    ring
  rw [e]
  have h6 : 0 ≤ ρ⁻¹ ^ 2 * s * ComplexMatrix2.operatorNorm X := by positivity
  nlinarith
end Difference
theorem claim_holds (hK : StepKernels.StepKernelBounds)
    (hH : StepKernelHolomorphy.KernelsHolomorphic)
    (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hT : RescaledConditions.Holds)
    (hD : Coordinates.ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    (hX : ComplexMatrix2.ExpLogEstimates) : Claim := by
  intro L hL k j hj c hc V hV hsm s hs
  have hρ0 := (hS.1 L hL).2.2.pos
  have hρ1 := (hS.1 L hL).2.2.le_one
  have ha := meshAt_pos hL k j
  have hne : (positiveDoubleBlockBonds L k j c).Nonempty :=
    ((hP L hL k j hj).2 c hc).finite_open.positive_nonempty
  have hH' := hH L hL k j hj c hc
  have hk : 1 ≤ k := by omega
  refine ⟨fun b hb X => ?_, fun y hy x hx X => ?_⟩
  · exact norm_sub_at_one_le (F := fun W Y => covariantSmoothingDeriv W (StepKernels.singleLinkForm b Y) c)
      hD hX ha hρ0 hρ1 hne
      (fun W hW => (hK L hL k j hj c hc W hW.1 hW.2).kernel_bound b hb)
      (fun a a' => hH'.holomorphic_kernel ⟨b, hb.2⟩ hb.1 a a')
      (fun a a' => hH'.local_kernel ⟨b, hb.2⟩ hb.1 a a') hV hsm hs X.2
  · have h1 := norm_sub_at_one_le (c := c)
      (F := fun W Y => ComplexMatrix2.conjugateBy (complexContourMean L W y x) Y)
      hD hX ha hρ0 hρ1 hne
      (fun W hW => by
        obtain ⟨T, hT', hb⟩ := (hK L hL k j hj c hc W hW.1 hW.2).conj_bound y hy x hx
        refine ⟨T, hT', fun Y => (hb Y).trans ?_⟩
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have h2 : 1 ≤ (polydiscRadius L)⁻¹ := (one_le_inv₀ hρ0).2 hρ1
        linarith)
      (fun a a' => hH'.holomorphic_conj y hy x hx a a')
      (fun a a' => hH'.local_conj y hy x hx a a') hV hsm hs X.2
    have h3 : complexContourMean L (fun _ => 1) y x = 1 :=
      (((hT L hL k hk).2.2.2.2.2.1 j hj).2.1) y x hx
    have h4 : ComplexMatrix2.conjugateBy (complexContourMean L (fun _ => 1) y x) (X : ComplexMatrix2) = X := by
      rw [h3]
      simp [ComplexMatrix2.conjugateBy]
    simp only [h4] at h1
    exact h1
end YangMills.Construction.Tower.FullSpace.StepKernelsNearIdentity
end

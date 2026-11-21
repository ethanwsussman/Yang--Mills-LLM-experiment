import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import YangMills.Construction.Matrices.UnimodularArgumentHolomorphyProof
import YangMills.Construction.Towers.CovariantAveragesAsDifferentialsProof
import YangMills.Construction.Towers.EvaluationOfARealAnalyticMapAtAPointProof
import YangMills.Construction.Towers.TaylorCoefficientsInTheLeftChartAreRealAnalytic
import Mathlib
set_option autoImplicit false
open Set Filter
open YangMills.Construction.Coordinates YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus YangMills.Construction.Matrices.GroupLieProduct.Subspaces.LocalAnalyticity
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.LeftChartTaylor
section Coordinates
open YangMills.Construction.Coordinates.ComplexCoordinates
variable {N N' : ℕ}
theorem differentiableOn_of_isHolomorphicIn
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties) {O : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates N'} (hf : IsHolomorphicIn O f) :
    DifferentiableOn ℂ f O := by
  intro b hb
  obtain ⟨L, hL⟩ := ((hP.1 N O hf.1).1 N' f hf).2.2.1 b hb
  exact (hasFDerivAt_of_restrictScalars ℝ hL rfl).differentiableAt.differentiableWithinAt
theorem isHolomorphicIn_of_differentiableOn {O : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates N'} (hO : IsOpen O) (hf : DifferentiableOn ℂ f O) :
    IsHolomorphicIn O f := by apply _root_.YangMills.SharedProofs.p1029 <;> assumption
theorem isHolomorphicIn_fderiv_apply
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties) {O : Set (ComplexCoordinates N)}
    {g : ComplexCoordinates N → ComplexCoordinates N'} (hg : IsHolomorphicIn O g)
    (v : ComplexCoordinates N) : IsHolomorphicIn O fun z => fderiv ℝ g z v := by
  have hO := hg.1
  have hall := (hP.1 N O hO).1 N' g hg
  have hsmooth : ∀ z ∈ O, ContDiffAt ℝ ∞ g z := fun z hz =>
    hall.2.1.contDiffAt (hO.mem_nhds hz)
  have hlin : ∀ z ∈ O, ∀ u, fderiv ℝ g z (Complex.I • u) = Complex.I • fderiv ℝ g z u := by
    intro z hz u
    obtain ⟨L, hL⟩ := hall.2.2.1 z hz
    rw [hL.fderiv]
    simp
  refine isHolomorphicIn_of_differentiableOn hO fun z hz => ?_
  have h2 : ContDiffAt ℝ (2 : ℕ) g z := contDiffAt_infty.1 (hsmooth z hz) 2
  have hC1 : ContDiffAt ℝ 1 (fderiv ℝ g) z := h2.fderiv_right (m := 1) (by norm_num)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ g) z := hC1.differentiableAt (by simp)
  set D := fderiv ℝ (fderiv ℝ g) z with hD
  have hT : ∀ y, HasFDerivAt (fun w => fderiv ℝ g w y) (D.flip y) z := by
    intro y
    have := hdiff.hasFDerivAt.clm_apply (hasFDerivAt_const y z)
    simpa [ContinuousLinearMap.flip] using this
  have hsym : IsSymmSndFDerivAt ℝ g z :=
    h2.isSymmSndFDerivAt (by simp)
  have hI : ∀ x u, D x (Complex.I • u) = Complex.I • D x u := by
    intro x u
    have e : (fun w => fderiv ℝ g w (Complex.I • u)) =ᶠ[𝓝 z]
        fun w => Complex.I • fderiv ℝ g w u := by
      filter_upwards [hO.mem_nhds hz] with w hw using hlin w hw u
    have h1 := (hT (Complex.I • u)).congr_of_eventuallyEq e.symm
    have h2 : HasFDerivAt (fun w => Complex.I • fderiv ℝ g w u)
        ((Complex.I • (D.flip u)) : ComplexCoordinates N →L[ℝ] ComplexCoordinates N') z :=
      (hT u).const_smul Complex.I
    have := h1.unique h2
    simpa using DFunLike.congr_fun this x
  have hJ : ∀ u, D (Complex.I • u) v = Complex.I • D u v := by
    intro u
    rw [hsym _ v, hI, hsym v u]
  let A : ComplexCoordinates N →ₗ[ℂ] ComplexCoordinates N' :=
    { toFun := fun u => D u v
      map_add' := fun a b => by simp
      map_smul' := fun c u => by
        have hc : c • u = (c.re : ℝ) • u + (c.im : ℝ) • (Complex.I • u) := by
          conv_lhs => rw [← Complex.re_add_im c]
          rw [add_smul, mul_smul]
          simp [Complex.coe_smul]
        have hc' : c • D u v = (c.re : ℝ) • D u v + (c.im : ℝ) • (Complex.I • D u v) := by
          conv_lhs => rw [← Complex.re_add_im c]
          rw [add_smul, mul_smul]
          simp [Complex.coe_smul]
        simp only [RingHom.id_apply]
        rw [hc, hc']
        simp [hJ] }
  have hA : HasFDerivAt (fun w => fderiv ℝ g w v)
      ((LinearMap.toContinuousLinearMap A).restrictScalars ℝ) z := by
    have e : ((LinearMap.toContinuousLinearMap A).restrictScalars ℝ) = D.flip v := by
      ext u
      simp [A]
    rw [e]
    exact hT v
  exact (hasFDerivAt_of_restrictScalars ℝ hA rfl).differentiableAt.differentiableWithinAt
theorem deriv_real_line_eq_fderiv {U : Set (ComplexCoordinates N)}
    {g h : ComplexCoordinates N → ComplexCoordinates N'} {z₀ v : ComplexCoordinates N} (hU : IsOpen U)
    (hd : DifferentiableAt ℝ h z₀)
    (heq : EqOn h g (U ∩ realLocus N)) (hz : z₀ ∈ U ∩ realLocus N) (hv : v ∈ realLocus N) :
    deriv (fun t : ℝ => g (z₀ + (t : ℂ) • v)) 0 = fderiv ℝ h z₀ v := by
  have hline : HasDerivAt (fun t : ℝ => z₀ + (t : ℂ) • v) v 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
    simpa using (h1.smul_const v).const_add z₀
  have h0 : z₀ + ((0 : ℝ) : ℂ) • v = z₀ := by simp
  have hcomp : HasDerivAt (fun t : ℝ => h (z₀ + (t : ℂ) • v)) (fderiv ℝ h z₀ v) 0 := by
    have hf : HasFDerivAt h (fderiv ℝ h z₀) (z₀ + ((0 : ℝ) : ℂ) • v) := by
      rw [h0]
      exact hd.hasFDerivAt
    exact hf.comp_hasDerivAt (0 : ℝ) hline
  have hev : ∀ᶠ t : ℝ in 𝓝 0, z₀ + (t : ℂ) • v ∈ U :=
    hline.continuousAt.eventually_mem (by rw [h0]; exact hU.mem_nhds hz.1)
  refine (hcomp.congr_of_eventuallyEq ?_).deriv
  filter_upwards [hev] with t ht
  refine (heq ⟨ht, fun j => ?_⟩).symm
  have := hz.2 j
  have hvj := hv j
  simp [this, hvj]
end Coordinates
section Products
variable {S R : Type}
def shiftAlgebra (q : R ⊕ S → ComplexMatrix2) (x : S → ComplexMatrix2) : R ⊕ S → ComplexMatrix2 :=
  ofParts (groupComponent q) (algebraComponent q + x)
def realParamVector [Fintype R] {n : ℕ} (c : Fin n → ℝ) : ParamSpace n R :=
  Fin.addCases (fun i => (c i : ℂ)) fun _ => 0
theorem realParamVector_mem_realLocus [Fintype R] {n : ℕ} (c : Fin n → ℝ) :
    realParamVector (R := R) c ∈ ComplexCoordinates.realLocus (n + 3 * Fintype.card R) := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [realParamVector]
theorem ofReal_smul_eq_smul (r : ℝ) (M : S → ComplexMatrix2) : (r : ℂ) • M = r • M := by apply _root_.YangMills.Construction.Tower.AsDifferentials.ofReal_smul_pi <;> assumption
theorem basisExpChart_add_real_line [Fintype R] {n : ℕ} {E : Submodule ℝ (S → ComplexMatrix2)}
    (e : Module.Basis (Fin n) ℝ E) (ν : IndexEnum R) (w₀ : R ⊕ S → ComplexMatrix2) (c : Fin n → ℝ)
    (z : ParamSpace n R) (t : ℝ) :
    basisExpChart e ν w₀ (z + (t : ℂ) • realParamVector c) =
      shiftAlgebra (basisExpChart e ν w₀ z) (t • ∑ i, c i • ((e i : E) : S → ComplexMatrix2)) := by
  have hg : angularPart ν (z + (t : ℂ) • realParamVector (R := R) c) = angularPart ν z := by
    funext ρ a
    simp [angularPart, realParamVector]
  have hl : ∀ i, linearPart (z + (t : ℂ) • realParamVector (R := R) c) i =
      linearPart z i + (t : ℂ) * (c i : ℂ) := by
    intro i
    simp [linearPart, realParamVector]
  unfold shiftAlgebra basisExpChart
  congr 1
  · rw [hg]
    rfl
  · change algebraComponent w₀ + ∑ i, _ = (algebraComponent w₀ + ∑ i, linearPart z i • _) + _
    rw [add_assoc]
    congr 1
    simp only [hl, add_smul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul, ofReal_smul_eq_smul, ofReal_smul_eq_smul]
theorem analytic_deriv_shiftAlgebra [Fintype S] [Fintype R]
    (hL : AnalyticCalculusStatement)
    (hRs : LocalAnalyticityStatement)
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {E : Submodule ℝ (S → ComplexMatrix2)} (hE : E ≤ hermitianTracelessFunctions S)
    {W : Set (R ⊕ S → ComplexMatrix2)} {l : ℕ}
    {f : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates l} (hf : IsSubspaceAnalyticToCoords E W f)
    {v : S → ComplexMatrix2} (hv : v ∈ E) :
    IsSubspaceAnalyticToCoords E W fun q => deriv (fun t : ℝ => f (shiftAlgebra q (t • v))) 0 := by
  classical
  have ν : IndexEnum R := Fintype.equivFinOfCardEq (by simp [Fintype.card_prod, mul_comm])
  have : FiniteDimensional ℝ E := (hL S R S R).1 E hE
  let e := Module.finBasis ℝ E
  have hall := hRs S R S R E E hE hE W hf.1
  refine (hall.2.2.2 ν).2 l _ fun w₀ hw₀ => ?_
  have hw₀' : w₀ ∈ subspaceTimesGroup E R := by
    obtain ⟨O, -, hO⟩ := hf.1.2
    rw [hO] at hw₀
    exact hw₀.2
  obtain ⟨hcarry, hread⟩ := (hall.2.2.2 ν).1 _ e w₀ hw₀'
  obtain ⟨T, hT, h0, hsub⟩ := (hcarry.2.2.2.2 hw₀).2
  obtain ⟨-, -, hrd, -⟩ := hread hw₀ T hT h0 hsub
  obtain ⟨-, hg⟩ := hrd l f hf
  refine ⟨_, e, T, hT, h0, hsub, hg.2.2.1, fun a ha => ?_⟩
  obtain ⟨U, hU, haU, -, h, hh, heq⟩ := hg.1 a ha
  have haR : a ∈ ComplexCoordinates.realLocus _ := by
    obtain ⟨O, -, hO⟩ := hT
    rw [hO] at ha
    exact ha.2.1
  set c : Fin _ → ℝ := fun i => e.repr ⟨v, hv⟩ i with hc
  have hvsum : ∑ i, c i • ((e i : E) : S → ComplexMatrix2) = v := by
    have h1 : ((∑ i, e.repr ⟨v, hv⟩ i • e i : E) : S → ComplexMatrix2) = v := by rw [e.sum_repr]
    push_cast at h1
    exact h1
  have hdir := isHolomorphicIn_fderiv_apply hP hh (realParamVector c)
  obtain ⟨co, hco⟩ := ((hP.1 _ U hU).1 _ _ hdir).2.2.2.2.2 a ⟨haU, haR⟩
  refine ⟨co, ?_⟩
  filter_upwards [hco, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds haU), self_mem_nhdsWithin]
    with z hz hzU hzR
  have hval : ((fun q => deriv (fun t : ℝ => f (shiftAlgebra q (t • v))) 0) ∘ basisExpChart e ν w₀) z =
      fderiv ℝ h z (realParamVector c) := by
    have hd : DifferentiableAt ℝ h z :=
      ((differentiableOn_of_isHolomorphicIn hP hh).differentiableAt
        (hU.mem_nhds hzU)).restrictScalars ℝ
    rw [← deriv_real_line_eq_fderiv (g := f ∘ basisExpChart e ν w₀) hU hd heq ⟨hzU, hzR⟩
      (realParamVector_mem_realLocus c)]
    simp only [Function.comp_apply, basisExpChart_add_real_line, hvsum]
  rw [hval]
  exact hz
end Products
section Matrices
open YangMills.Construction.Coordinates.ComplexCoordinates
variable {σ ι κ : Type}
theorem differentiableAt_of_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {f : X → ComplexMatrix2} {x : X} (h : ∀ r s, DifferentiableAt ℂ (fun y => f y r s) x) :
    DifferentiableAt ℂ f x := by
  have e : f = fun t => ∑ r, ∑ s, f t r s • (Matrix.single r s (1 : ℂ)) := by
    funext t
    ext i j
    simp [Matrix.sum_apply, Matrix.single_apply]
    fin_cases i <;> fin_cases j <;> simp
  rw [e]
  exact DifferentiableAt.fun_sum fun r _ => DifferentiableAt.fun_sum fun s _ =>
    (h r s).smul_const _
theorem differentiable_matrix_entry (r s : Fin 2) :
    Differentiable ℂ fun X : ComplexMatrix2 => X r s :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ r s)).differentiable
theorem differentiable_matrixEquiv :
    Differentiable ℂ (matrixEquiv : ComplexMatrix2 → ComplexCoordinates 4) :=
  differentiable_pi.2 fun _ => differentiable_matrix_entry _ _
theorem differentiableOn_of_isHolomorphicVia
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties) {D : Set ComplexMatrix2}
    {f : ComplexMatrix2 → ComplexMatrix2} (h : IsHolomorphicVia matrixEquiv matrixEquiv D f) :
    DifferentiableOn ℂ f D := by apply _root_.YangMills.SharedProofs.p53137 <;> assumption
theorem exists_index_of_entry {k : ℕ} (ν : σ ≃ Fin k) (i : σ) (r s : Fin 2) :
    ∃ j, ∀ X : σ → ComplexMatrix2, matrixPiEquiv ν X j = X i r s := by apply _root_.YangMills.Construction.Tower.AnalyticRepresentation.exists_index_eq_entry <;> assumption
theorem differentiable_matrixPiEquiv_symm [Fintype σ] {k : ℕ} (ν : σ ≃ Fin k) :
    Differentiable ℂ (matrixPiEquiv ν).symm := by
  refine differentiable_pi.2 fun i _ => differentiableAt_of_entry fun r s => ?_
  obtain ⟨j, hj⟩ := exists_index_of_entry ν i r s
  have e : (fun z => (matrixPiEquiv ν).symm z i r s) = fun z => z j := by
    funext z
    have h1 := hj ((matrixPiEquiv ν).symm z)
    rw [Equiv.apply_symm_apply] at h1
    exact h1.symm
  rw [e]
  exact (differentiable_apply j).differentiableAt
theorem isHolomorphicVia_of_differentiableOn [Fintype σ] {T : Type} {l k : ℕ}
    (e : T ≃ ComplexCoordinates l) (ν : σ ≃ Fin k) {O : Set (σ → ComplexMatrix2)} (hO : IsOpen O)
    {Φ : (σ → ComplexMatrix2) → T} (hΦ : DifferentiableOn ℂ (e ∘ Φ) O) :
    IsHolomorphicVia (matrixPiEquiv ν) e O Φ := by
  have hs := differentiable_matrixPiEquiv_symm ν
  have himg : matrixPiEquiv ν '' O = (matrixPiEquiv ν).symm ⁻¹' O :=
    (matrixPiEquiv ν).image_eq_preimage_symm O
  unfold IsHolomorphicVia
  rw [himg]
  exact isHolomorphicIn_of_differentiableOn (hO.preimage hs.continuous)
    (hΦ.comp hs.differentiableOn fun _ h => h)
theorem isHolomorphicToCoords_of_differentiableOn [Fintype ι] [Fintype κ]
    (hX : ExpChartHolomorphy.ExpChartTheory) {T : Type} {l : ℕ}
    (e : T ≃ ComplexCoordinates l) {O : Set (ι ⊕ κ → ComplexMatrix2)} (hO : IsOpen O)
    {Φ : (ι ⊕ κ → ComplexMatrix2) → T} (hΦ : DifferentiableOn ℂ (e ∘ Φ) O)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    IsHolomorphicToCoords b e (O ∩ GroupLieProduct ι κ) Φ :=
  ((hX.2.2.2.1 ι κ).2.2 T l _ e (Fintype.equivFin (ι ⊕ κ)) O Φ
    (isHolomorphicVia_of_differentiableOn e _ hO hΦ)).2 b
theorem isHolomorphicToUnimodular_of_differentiableOn [Fintype ι] [Fintype κ]
    (hX : ExpChartHolomorphy.ExpChartTheory) {O : Set (ι ⊕ κ → ComplexMatrix2)} (hO : IsOpen O)
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2} (hΦ : DifferentiableOn ℂ Φ O)
    (hm : MapsTo Φ (O ∩ GroupLieProduct ι κ) ComplexMatrix2.unitDeterminant)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    IsHolomorphicToUnimodular b (O ∩ GroupLieProduct ι κ) Φ :=
  ((hX.2.2.2.1 ι κ).2.1 b _ Φ ⟨O, hO, rfl⟩ hm).2
    (isHolomorphicToCoords_of_differentiableOn hX matrixEquiv hO
      (differentiable_matrixEquiv.comp_differentiableOn hΦ) b)
end Matrices
section Slices
open YangMills.Construction.Coordinates.ComplexCoordinates
variable {S R : Type}
theorem subspaceTimesGroup_subset {E : Submodule ℝ (S → ComplexMatrix2)}
    (hE : E ≤ hermitianTracelessFunctions S) :
    subspaceTimesGroup E R ⊆ GroupLieProduct R S := by apply _root_.YangMills.SharedProofs.p6041 <;> assumption
def zeroSection (q : R ⊕ Empty → ComplexMatrix2) : R ⊕ S → ComplexMatrix2 :=
  ofParts (groupComponent q) 0
theorem zeroSection_analytic [Fintype R] [Fintype S]
    (hX : ExpChartHolomorphy.ExpChartTheory) {E : Submodule ℝ (S → ComplexMatrix2)}
    (hE : E ≤ hermitianTracelessFunctions S) :
    IsSubspaceAnalyticToProduct (S := Empty) (R := R) (S' := S) (R' := R) ⊥ E
      (subspaceTimesGroup ⊥ R) zeroSection := by
  refine ⟨⟨bot_le, univ, isOpen_univ, (univ_inter _).symm⟩, hE,
    fun q hq => ⟨E.zero_mem, hq.2⟩, fun p hp => ?_⟩
  refine ⟨univ ∩ GroupLieProduct R Empty, ⟨mem_univ _, subspaceTimesGroup_subset bot_le hp⟩,
    ⟨univ, isOpen_univ, (univ_inter _).symm ▸ rfl⟩, ?_, zeroSection, fun b => ?_, fun _ _ => rfl⟩
  · exact inter_subset_right
  · refine ⟨⟨univ, isOpen_univ, rfl⟩, fun r => ?_, fun s => ?_⟩
    · exact isHolomorphicToUnimodular_of_differentiableOn hX isOpen_univ
        (differentiable_apply (Sum.inl r : R ⊕ Empty)).differentiableOn
        (fun q hq => hq.2 (.inl r)) b
    · have e : (matrixEquiv ∘ fun p : R ⊕ Empty → ComplexMatrix2 =>
          zeroSection (S := S) p (.inr s)) = fun _ => matrixEquiv (0 : ComplexMatrix2) := rfl
      exact ⟨fun _ _ => ComplexMatrix2.traceless.zero_mem,
        isHolomorphicToCoords_of_differentiableOn hX matrixEquiv
          isOpen_univ (e ▸ differentiableOn_const _) b⟩
def expTwistPoint (q : R ⊕ R → ComplexMatrix2) : R ⊕ Empty → ComplexMatrix2 :=
  ofParts (fun r => ComplexMatrix2.matExp (Complex.I • q (.inr r)) * q (.inl r)) Empty.elim
theorem expTwistPoint_analytic [Fintype R]
    (hX : ExpChartHolomorphy.ExpChartTheory)
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hC : ComplexMatrix2.ExpSurjectivityAndComplexification) :
    IsSubspaceAnalyticToProduct (S := R) (R := R) (S' := Empty) (R' := R)
      (hermitianTracelessFunctions R) ⊥
      (subspaceTimesGroup (hermitianTracelessFunctions R) R) expTwistPoint := by
  refine ⟨⟨le_rfl, univ, isOpen_univ, (univ_inter _).symm⟩, bot_le, fun q hq =>
    ⟨(Submodule.mem_bot ℝ).2 (Subsingleton.elim _ _), fun r => ?_⟩, fun p hp => ?_⟩
  · exact Submonoid.mul_mem _ (hC.1 _ (hq.1 r (mem_univ r))) (hq.2 r)
  refine ⟨univ ∩ GroupLieProduct R R, ⟨mem_univ _, subspaceTimesGroup_subset le_rfl hp⟩,
    ⟨univ, isOpen_univ, rfl⟩, inter_subset_right, expTwistPoint, fun b => ?_, fun _ _ => rfl⟩
  refine ⟨⟨univ, isOpen_univ, rfl⟩, fun r => ?_, fun s => s.elim⟩
  have hexp : Differentiable ℂ ComplexMatrix2.matExp := fun X =>
    (differentiableOn_of_isHolomorphicVia hP hP.2.2.2.2.1).differentiableAt
      (by simp)
  have hd : Differentiable ℂ fun q : R ⊕ R → ComplexMatrix2 =>
      ComplexMatrix2.matExp (Complex.I • q (.inr r)) * q (.inl r) :=
    (hexp.comp ((differentiable_apply (Sum.inr r : R ⊕ R)).const_smul Complex.I)).mul
      (differentiable_apply (Sum.inl r : R ⊕ R))
  refine isHolomorphicToUnimodular_of_differentiableOn hX isOpen_univ hd.differentiableOn
    (fun q hq => ?_) b
  have hmaps := ((hX.2.2.2.1 R R).1 q hq.2).2.2.1
  have hA : (Sum.elim (fun r => Complex.I • q (.inr r)) fun _ => 0 : R ⊕ R → ComplexMatrix2) ∈
      tracelessPi (R ⊕ R) := by
    rintro (r | s)
    · exact ComplexMatrix2.traceless.smul_mem _ (hq.2 (.inr r))
    · exact ComplexMatrix2.traceless.zero_mem
  exact hmaps hA (.inl r)
theorem analytic_comp_zeroSection [Fintype R] [Fintype S]
    (hL : AnalyticCalculusStatement)
    (hX : ExpChartHolomorphy.ExpChartTheory) {E : Submodule ℝ (S → ComplexMatrix2)}
    (hE : E ≤ hermitianTracelessFunctions S) {W : Set (R ⊕ S → ComplexMatrix2)} {l : ℕ}
    {f : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates l} (hf : IsSubspaceAnalyticToCoords E W f) :
    IsSubspaceAnalyticToCoords (S := Empty) (R := R) ⊥
      (subspaceTimesGroup ⊥ R ∩ zeroSection ⁻¹' W) (f ∘ zeroSection) :=
  ((((hL Empty R S R).2.2.2 ⊥ E bot_le hE).2.2.1 (subspaceTimesGroup ⊥ R)
    ⟨bot_le, univ, isOpen_univ, (univ_inter _).symm⟩).2.2.1 zeroSection
      (zeroSection_analytic hX hE)).2 W hf.1 |>.2.1 l f hf
theorem shiftAlgebra_ofParts (V : R → ComplexMatrix2) (Z x : S → ComplexMatrix2) :
    shiftAlgebra (ofParts V Z) x = ofParts V (Z + x) := rfl
theorem analyticToCoords_congr [Fintype R] [Fintype S] {E : Submodule ℝ (S → ComplexMatrix2)}
    {W : Set (R ⊕ S → ComplexMatrix2)} {l : ℕ} {f g : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates l}
    (hf : IsSubspaceAnalyticToCoords E W f) (heq : EqOn f g W) :
    IsSubspaceAnalyticToCoords E W g := by
  refine ⟨hf.1, fun p hp => ?_⟩
  obtain ⟨X, h1, h2, h3, Φ, h4, h5⟩ := hf.2 p hp
  exact ⟨X, h1, h2, h3, Φ, h4, fun x hx => (h5 hx).trans (heq (h3 hx))⟩
theorem analytic_firstDeriv_at_zero [Fintype R] [Fintype S]
    (hL : AnalyticCalculusStatement)
    (hRs : LocalAnalyticityStatement)
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hX : ExpChartHolomorphy.ExpChartTheory) {E : Submodule ℝ (S → ComplexMatrix2)}
    (hE : E ≤ hermitianTracelessFunctions S) {W : Set (R ⊕ S → ComplexMatrix2)}
    {W' : Set (R ⊕ Empty → ComplexMatrix2)} {l : ℕ}
    {f : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates l} (hf : IsSubspaceAnalyticToCoords E W f)
    (hop : IsOpenInSubspaceTimesGroup (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) W')
    (hsub : ∀ q ∈ W', zeroSection (S := S) q ∈ W) {v : S → ComplexMatrix2} (hv : v ∈ E) :
    IsSubspaceAnalyticToCoords (S := Empty) (R := R) ⊥ W'
      fun q => deriv (fun t : ℝ => f (ofParts (groupComponent q) (t • v))) 0 := by
  have h1 := analytic_comp_zeroSection hL hX hE (analytic_deriv_shiftAlgebra hL hRs hP hE hf hv)
  have hsp : W' ⊆ subspaceTimesGroup ⊥ R := by
    obtain ⟨O, -, hO⟩ := hop.2
    rw [hO]
    exact inter_subset_right
  have h2 := ((hRs Empty R Empty R ⊥ ⊥ bot_le bot_le _ h1.1).1 W'
    (fun q hq => ⟨hsp hq, hsub q hq⟩) hop.2).1 l _ h1
  refine analyticToCoords_congr h2 fun q _ => ?_
  simp only [Function.comp_apply, zeroSection, shiftAlgebra_ofParts, zero_add]
theorem analytic_secondDeriv_at_zero [Fintype R] [Fintype S]
    (hL : AnalyticCalculusStatement)
    (hRs : LocalAnalyticityStatement)
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hX : ExpChartHolomorphy.ExpChartTheory) {E : Submodule ℝ (S → ComplexMatrix2)}
    (hE : E ≤ hermitianTracelessFunctions S) {W : Set (R ⊕ S → ComplexMatrix2)}
    {W' : Set (R ⊕ Empty → ComplexMatrix2)} {l : ℕ}
    {f : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates l} (hf : IsSubspaceAnalyticToCoords E W f)
    (hop : IsOpenInSubspaceTimesGroup (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) W')
    (hsub : ∀ q ∈ W', zeroSection (S := S) q ∈ W) {v v' : S → ComplexMatrix2} (hv : v ∈ E)
    (hv' : v' ∈ E) :
    IsSubspaceAnalyticToCoords (S := Empty) (R := R) ⊥ W' fun q =>
      deriv (fun s : ℝ => deriv (fun t : ℝ => f (ofParts (groupComponent q) (s • v + t • v'))) 0)
        0 := by
  have h1 := analytic_firstDeriv_at_zero hL hRs hP hX hE
    (analytic_deriv_shiftAlgebra hL hRs hP hE hf hv') hop hsub hv
  refine analyticToCoords_congr h1 fun q _ => ?_
  simp only [shiftAlgebra_ofParts]
end Slices
section Values
open YangMills.Construction.Coordinates.ComplexCoordinates
variable {S R R' : Type}
theorem analytic_realLinear_comp [Fintype S] [Fintype R]
    (hL : AnalyticCalculusStatement)
    (hRs : LocalAnalyticityStatement)
    {E : Submodule ℝ (S → ComplexMatrix2)} (hE : E ≤ hermitianTracelessFunctions S)
    {W : Set (R ⊕ S → ComplexMatrix2)} {l : ℕ}
    {f : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates l} (hf : IsSubspaceAnalyticToCoords E W f)
    (Λ : ComplexCoordinates l →ₗ[ℝ] ℝ) :
    IsSubspaceAnalyticToCoords (l := 1) E W fun q _ => ((Λ (f q) : ℝ) : ℂ) := by
  classical
  have ν : IndexEnum R := Fintype.equivFinOfCardEq (by simp [Fintype.card_prod, mul_comm])
  have : FiniteDimensional ℝ E := (hL S R S R).1 E hE
  let e := Module.finBasis ℝ E
  have hall := hRs S R S R E E hE hE W hf.1
  refine (hall.2.2.2 ν).2 1 _ fun w₀ hw₀ => ?_
  have hw₀' : w₀ ∈ subspaceTimesGroup E R := by
    obtain ⟨O, -, hO⟩ := hf.1.2
    rw [hO] at hw₀
    exact hw₀.2
  obtain ⟨hcarry, hread⟩ := (hall.2.2.2 ν).1 _ e w₀ hw₀'
  obtain ⟨T, hT, h0, hsub⟩ := (hcarry.2.2.2.2 hw₀).2
  obtain ⟨-, -, hrd, -⟩ := hread hw₀ T hT h0 hsub
  obtain ⟨-, hg⟩ := hrd l f hf
  refine ⟨_, e, T, hT, h0, hsub, ⟨hg.2.2.1, fun a ha => ?_⟩⟩
  have haR : a ∈ realLocus _ := by
    obtain ⟨O, -, hO⟩ := hT
    rw [hO] at ha
    exact ha.2.1
  obtain ⟨co, hco⟩ := hg.2.2.2 a ha
  let Λ₀ : ComplexCoordinates l →ₗ[ℝ] ComplexCoordinates 1 :=
    { toFun := fun x _ => ((Λ x : ℝ) : ℂ)
      map_add' := fun x y => by
        funext _
        simp
      map_smul' := fun r x => by
        funext _
        simp }
  let Λ' : ComplexCoordinates l →L[ℝ] ComplexCoordinates 1 := LinearMap.toContinuousLinearMap Λ₀
  refine ⟨fun m => Λ' (co m), ?_⟩
  filter_upwards [hco, self_mem_nhdsWithin] with z hz hzR
  have h1 := Λ'.hasSum hz
  have hterm : (fun m => (∏ j, (z j - a j) ^ m j) • Λ' (co m)) =
      fun m => Λ' ((∏ j, (z j - a j) ^ m j) • co m) := by
    funext m
    have hreal : ∀ j, z j - a j = (((z j).re - (a j).re : ℝ) : ℂ) := by
      intro j
      apply Complex.ext <;> simp [hzR j, haR j]
    have hprod : (∏ j, (z j - a j) ^ m j) = ((∏ j, ((z j).re - (a j).re) ^ m j : ℝ) : ℂ) := by
      push_cast
      exact Finset.prod_congr rfl fun j _ => by rw [hreal j]; push_cast; rfl
    have hsm : ∀ (r : ℝ) (x : ComplexCoordinates l), (r : ℂ) • x = r • x := by
      intro r x
      funext i
      simp
    have hsm1 : ∀ (r : ℝ) (x : ComplexCoordinates 1), (r : ℂ) • x = r • x := by
      intro r x
      funext i
      simp
    rw [hprod, hsm, hsm1, map_smul]
  rw [hterm]
  exact h1
theorem deriv_ofReal_const_fun (h : ℝ → ℝ) (x : ℝ) :
    deriv (fun t => (fun _ : Fin 1 => ((h t : ℝ) : ℂ))) x = fun _ => ((deriv h x : ℝ) : ℂ) := by
  by_cases hd : DifferentiableAt ℝ h x
  · have h1 : HasDerivAt (fun t => ((h t : ℝ) : ℂ)) ((deriv h x : ℝ) : ℂ) x :=
      hd.hasDerivAt.ofReal_comp
    exact (hasDerivAt_pi.2 fun _ => h1).deriv
  · have hn : ¬ DifferentiableAt ℝ (fun t => (fun _ : Fin 1 => ((h t : ℝ) : ℂ))) x := by
      intro hc
      apply hd
      have h1 := (differentiableAt_pi.1 hc) 0
      have h2 := Complex.reCLM.differentiableAt.comp x h1
      simpa [Function.comp_def] using h2
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hn]
    funext _
    simp
def matrixLinearEquiv : ComplexMatrix2 ≃ₗ[ℝ] ComplexCoordinates 4 :=
  { matrixEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun r X => by
      funext k
      simp [matrixEquiv] }
theorem deriv_matrixEquiv (γ : ℝ → ComplexMatrix2) (x : ℝ) :
    deriv (fun t => matrixEquiv (γ t)) x = matrixEquiv (deriv γ x) := by
  let C : ComplexMatrix2 ≃L[ℝ] ComplexCoordinates 4 := matrixLinearEquiv.toContinuousLinearEquiv
  have hC : ∀ X, C X = matrixEquiv X := fun _ => rfl
  by_cases hd : DifferentiableAt ℝ γ x
  · have h1 := (C : ComplexMatrix2 →L[ℝ] ComplexCoordinates 4).hasFDerivAt.comp_hasDerivAt x
      hd.hasDerivAt
    exact h1.deriv
  · have hn : ¬ DifferentiableAt ℝ (fun t => matrixEquiv (γ t)) x := fun hc =>
      hd (C.comp_differentiableAt_iff.1 hc)
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hn, ← hC,
      map_zero]
theorem differentiable_adjugate_two :
    Differentiable ℂ (Matrix.adjugate : ComplexMatrix2 → ComplexMatrix2) := fun X =>
  differentiableAt_of_entry fun r s => by
    simp only [Matrix.adjugate_fin_two]
    fin_cases r <;> fin_cases s <;> simp
    · exact (differentiable_matrix_entry 1 1).differentiableAt
    · exact (differentiable_matrix_entry 0 1).differentiableAt
    · exact (differentiable_matrix_entry 1 0).differentiableAt
    · exact (differentiable_matrix_entry 0 0).differentiableAt
def quotientLogCoords (c : R') (x : (R' ⊕ R') ⊕ (Empty ⊕ Empty) → ComplexMatrix2) :
    ComplexCoordinates 4 :=
  matrixEquiv (Complex.I⁻¹ •
    ComplexMatrix2.logSeries (x (.inl (.inl c)) * (x (.inl (.inr c))).adjugate))
def quotientLogDomain (c : R') : Set ((R' ⊕ R') ⊕ (Empty ⊕ Empty) → ComplexMatrix2) :=
  {x | x (.inl (.inl c)) * (x (.inl (.inr c))).adjugate ∈ ComplexMatrix2.logBall}
theorem sumSubmodule_bot_le :
    sumSubmodule (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) ≤
      hermitianTracelessFunctions (Empty ⊕ Empty) := by
  intro x _ i _
  rcases i with e | e <;> exact e.elim
theorem quotientLogCoords_analytic [Fintype R']
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hX : ExpChartHolomorphy.ExpChartTheory) (c : R') :
    IsSubspaceAnalyticToCoords (sumSubmodule ⊥ ⊥)
      (quotientLogDomain c ∩ subspaceTimesGroup (sumSubmodule ⊥ ⊥) (R' ⊕ R'))
      (quotientLogCoords c) := by
  have hQ : Differentiable ℂ fun x : (R' ⊕ R') ⊕ (Empty ⊕ Empty) → ComplexMatrix2 =>
      x (.inl (.inl c)) * (x (.inl (.inr c))).adjugate :=
    (differentiable_apply _).mul (differentiable_adjugate_two.comp (differentiable_apply _))
  have hdom : IsOpen (ComplexMatrix2.logBall) := by
    have : Continuous fun X : ComplexMatrix2 => ComplexMatrix2.operatorNorm (X - 1) := by
      unfold ComplexMatrix2.operatorNorm
      fun_prop
    exact isOpen_lt this continuous_const
  have hopen : IsOpen (quotientLogDomain (R' := R') c) := hdom.preimage hQ.continuous
  have hlog := differentiableOn_of_isHolomorphicVia hP hP.2.2.2.2.2
  have hd : DifferentiableOn ℂ (quotientLogCoords c) (quotientLogDomain c) := by
    intro x hx
    have h1 : DifferentiableAt ℂ ComplexMatrix2.logSeries _ := hlog.differentiableAt (hdom.mem_nhds hx)
    have h2 := h1.comp x (hQ x)
    have h3 := (h2.const_smul Complex.I⁻¹)
    exact (differentiable_matrixEquiv.differentiableAt.comp x h3).differentiableWithinAt
  refine ⟨⟨sumSubmodule_bot_le, quotientLogDomain c, hopen, rfl⟩, fun p hp =>
    ⟨quotientLogDomain c ∩ GroupLieProduct (R' ⊕ R') (Empty ⊕ Empty),
      ⟨hp.1, subspaceTimesGroup_subset sumSubmodule_bot_le hp.2⟩, ⟨_, hopen, rfl⟩, ?_,
      quotientLogCoords c, fun b => ?_, fun _ _ => rfl⟩⟩
  · rintro x ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · exact isHolomorphicToCoords_of_differentiableOn hX (Equiv.refl _) hopen hd b
theorem expTwistPoint_zeroSection (q : R ⊕ Empty → ComplexMatrix2) :
    expTwistPoint (zeroSection q) = q := by
  funext i
  rcases i with r | e
  · simp [expTwistPoint, zeroSection, ofParts, groupComponent]
  · exact e.elim
theorem ofParts_groupComponent_elim (q : R ⊕ Empty → ComplexMatrix2) :
    ofParts (groupComponent q) Empty.elim = q := by apply _root_.YangMills.DeltaSharedProofs.p4358 <;> assumption
theorem isRelativelyOpen_inter {T : Type} [TopologicalSpace T] {P D₁ D₂ : Set T}
    (h₁ : ComplexMatrix2.IsRelativelyOpen P D₁) (h₂ : ComplexMatrix2.IsRelativelyOpen P D₂) :
    ComplexMatrix2.IsRelativelyOpen P (D₁ ∩ D₂) := by apply _root_.YangMills.SharedProofs.p7081 <;> assumption
theorem analytic_quotientLog_expTwist [Fintype R] [Fintype R']
    (hL : AnalyticCalculusStatement)
    (hRs : LocalAnalyticityStatement)
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hX : ExpChartHolomorphy.ExpChartTheory)
    (hC : ComplexMatrix2.ExpSurjectivityAndComplexification)
    {W' : Set (R ⊕ Empty → ComplexMatrix2)} {M : (R ⊕ Empty → ComplexMatrix2) → R' ⊕ Empty → ComplexMatrix2}
    (hM : IsSubspaceAnalyticToProduct (R := R) (S := Empty) (R' := R') (S' := Empty) ⊥ ⊥ W' M)
    (c : R') :
    ∃ W₂ : Set (R ⊕ R → ComplexMatrix2),
      IsSubspaceAnalyticToCoords (hermitianTracelessFunctions R) W₂ (fun q => quotientLogCoords c
        (pairPoint (M (expTwistPoint q)) (M (ofParts (groupComponent q) Empty.elim)))) ∧
      ∀ q ∈ W', zeroSection q ∈ W₂ := by
  have hsp : IsOpenInSubspaceTimesGroup (hermitianTracelessFunctions R)
      (subspaceTimesGroup (hermitianTracelessFunctions R) R) :=
    ⟨le_rfl, univ, isOpen_univ, (univ_inter _).symm⟩
  have hbase := (hL R R Empty R).2.2.2 (hermitianTracelessFunctions R) ⊥ le_rfl bot_le
  have hA := expTwistPoint_analytic (R := R) hX hP hC
  have hπ := hbase.2.1.2
  have hcomp := hbase.2.2.1 _ hsp
  have hcA := (hcomp.2.2.1 _ hA).2 W' hM.1
  have hcπ := (hcomp.2.2.1 _ hπ).2 W' hM.1
  have h₁ := hcA.2.2 Empty R' ⊥ M hM
  have h₂ := hcπ.2.2 Empty R' ⊥ M hM
  set Wa := subspaceTimesGroup (hermitianTracelessFunctions R) R ∩ expTwistPoint ⁻¹' W' with hWa
  set Wp := subspaceTimesGroup (hermitianTracelessFunctions R) R ∩
    (fun q : R ⊕ R → ComplexMatrix2 => ofParts (groupComponent q) Empty.elim) ⁻¹' W' with hWp
  have hop₁ : ComplexMatrix2.IsRelativelyOpen
      (subspaceTimesGroup (hermitianTracelessFunctions R) R) (Wa ∩ Wp) :=
    isRelativelyOpen_inter hcA.1 hcπ.1
  have hr₁ := ((hRs R R Empty R' (hermitianTracelessFunctions R) ⊥ le_rfl bot_le Wa
    ⟨le_rfl, hcA.1⟩).1 (Wa ∩ Wp) inter_subset_left hop₁).2 _ h₁
  have hr₂ := ((hRs R R Empty R' (hermitianTracelessFunctions R) ⊥ le_rfl bot_le Wp
    ⟨le_rfl, hcπ.1⟩).1 (Wa ∩ Wp) inter_subset_right hop₁).2 _ h₂
  have hpair := ((hL R R Empty R').2.2.2 (hermitianTracelessFunctions R) ⊥ le_rfl bot_le).2.2.1
    (Wa ∩ Wp) ⟨le_rfl, hop₁⟩ |>.2.1 Empty Empty R' R' ⊥ ⊥ _ _ hr₁ hr₂
  have hΘ := quotientLogCoords_analytic (R' := R') hP hX c
  have hfin := ((((hL R R (Empty ⊕ Empty) (R' ⊕ R')).2.2.2 (hermitianTracelessFunctions R)
    (sumSubmodule ⊥ ⊥) le_rfl sumSubmodule_bot_le).2.2.1 (Wa ∩ Wp) ⟨le_rfl, hop₁⟩).2.2.1 _
      hpair).2 _ hΘ.1
  refine ⟨_, hfin.2.1 4 _ hΘ, fun q hq => ?_⟩
  have hsp₀ : q ∈ subspaceTimesGroup (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) R := by
    obtain ⟨O, -, hO⟩ := hM.1.2
    rw [hO] at hq
    exact hq.2
  have hι : zeroSection q ∈ subspaceTimesGroup (hermitianTracelessFunctions R) R :=
    ⟨(hermitianTracelessFunctions R).zero_mem, hsp₀.2⟩
  have hπq : ofParts (groupComponent (zeroSection (S := R) q)) Empty.elim = q :=
    ofParts_groupComponent_elim q
  have hmem : zeroSection q ∈ Wa ∩ Wp := by
    refine ⟨⟨hι, ?_⟩, ⟨hι, ?_⟩⟩
    · change expTwistPoint (zeroSection q) ∈ W'
      rwa [expTwistPoint_zeroSection]
    · change ofParts (groupComponent (zeroSection (S := R) q)) Empty.elim ∈ W'
      rwa [hπq]
  refine ⟨hmem, ?_, hpair.2.2.1 hmem⟩
  change pairPoint (M (expTwistPoint (zeroSection q)))
    (M (ofParts (groupComponent (zeroSection (S := R) q)) Empty.elim)) ∈ quotientLogDomain c
  rw [expTwistPoint_zeroSection, hπq]
  have hdet : (M q (.inl c)).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.1 ((hM.2.2.1 hq).2 c)).2
  have hone : M q (.inl c) * (M q (.inl c)).adjugate = 1 := by
    rw [Matrix.mul_adjugate, hdet, one_smul]
  change M q (.inl c) * (M q (.inl c)).adjugate ∈ ComplexMatrix2.logBall
  rw [hone]
  simp [ComplexMatrix2.logBall]
end Values
section OnTower
variable {L n k j j' : ℕ}
theorem isPositivelyOriented_or_opposite (c : Edge L n k j) :
    c.IsPositivelyOriented ∨ c.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem fieldOfPositiveValues_expTwistPoint (w x : PositiveEdge L n k j → ComplexMatrix2)
    (X : Edge L n k j → ComplexMatrix2) (hx : ∀ r, x r = X r.1) :
    fieldOfPositiveValues (groupComponent (expTwistPoint (ofParts w x))) =
      PeriodicLattice.expTwist X (fieldOfPositiveValues w) := by
  funext c
  by_cases hc : c.IsPositivelyOriented
  · simp only [fieldOfPositiveValues, dif_pos hc, PeriodicLattice.expTwist, if_pos hc]
    change ComplexMatrix2.matExp (Complex.I • x ⟨c, hc⟩) * w ⟨c, hc⟩ = _
    rw [hx]
  · have hr := (isPositivelyOriented_or_opposite c).resolve_left hc
    simp only [fieldOfPositiveValues, dif_neg hc, dif_pos hr, PeriodicLattice.expTwist, if_neg hc]
    change (ComplexMatrix2.matExp (Complex.I • x ⟨c.opposite, hr⟩) * w ⟨c.opposite, hr⟩)⁻¹ = _
    rw [hx]
theorem restrictToPositiveEdges_mem {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) :
    restrictToPositiveEdges B ∈ hermitianTracelessFunctions (PositiveEdge L n k j) :=
  fun r _ => hB.1 r.1 r.2
theorem smul_restrictToPositiveEdges (t : ℝ) (B : Edge L n k j → ComplexMatrix2)
    (r : PositiveEdge L n k j) :
    (t • restrictToPositiveEdges B) r = ((t : ℂ) • B) r.1 := by
  ext a b
  simp [restrictToPositiveEdges]
variable (hL : AnalyticCalculusStatement)
  (hRs : LocalAnalyticityStatement)
  (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
  (hX : ExpChartHolomorphy.ExpChartTheory)
  (hC : ComplexMatrix2.ExpSurjectivityAndComplexification)
include hL hRs hP hX hC
theorem analytic_leftDerivs {U : Set (Edge L n k j → ComplexMatrix2)}
    {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (hF : IsAnalyticFieldFunction U F) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) :
    IsAnalyticFieldFunction U (fun V => leftDeriv F V B) ∧
      ∀ B' ∈ edgeFormSpace L n k j, IsAnalyticFieldFunction U fun V => leftSecondDeriv F V B B' := by
  obtain ⟨hop, inst, hF'⟩ := hF
  have hsp : IsOpenInSubspaceTimesGroup (hermitianTracelessFunctions (PositiveEdge L n k j))
      (subspaceTimesGroup (hermitianTracelessFunctions (PositiveEdge L n k j))
        (PositiveEdge L n k j)) :=
    ⟨le_rfl, univ, isOpen_univ, (univ_inter _).symm⟩
  have hbase := (hL (PositiveEdge L n k j) (PositiveEdge L n k j) Empty
    (PositiveEdge L n k j)).2.2.2 (hermitianTracelessFunctions _) ⊥ le_rfl bot_le
  have hA := expTwistPoint_analytic (R := PositiveEdge L n k j) hX hP hC
  have hcomp := (((hbase.2.2.1 _ hsp).2.2.1 _ hA).2 _ hF'.1).2.1 1 _ hF'
  have hsub : ∀ q ∈ {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
      fieldOfPositiveValues (groupComponent q) ∈ U},
      zeroSection (S := PositiveEdge L n k j) q ∈
        subspaceTimesGroup (hermitianTracelessFunctions (PositiveEdge L n k j))
          (PositiveEdge L n k j) ∩
          expTwistPoint ⁻¹' {q | fieldOfPositiveValues (groupComponent q) ∈ U} := by
    intro q hq
    have hsp₀ : q ∈ subspaceTimesGroup (⊥ : Submodule ℝ (Empty → ComplexMatrix2))
        (PositiveEdge L n k j) := by
      obtain ⟨O, -, hO⟩ := hF'.1.2
      rw [hO] at hq
      exact hq.2
    refine ⟨⟨Submodule.zero_mem _, hsp₀.2⟩, ?_⟩
    rw [mem_preimage, expTwistPoint_zeroSection]
    exact hq
  have hv := restrictToPositiveEdges_mem hB
  refine ⟨⟨hop, inst, analyticToCoords_congr
    (analytic_firstDeriv_at_zero hL hRs hP hX le_rfl hcomp hF'.1 hsub hv) fun q _ => ?_⟩,
    fun B' hB' => ⟨hop, inst, analyticToCoords_congr
      (analytic_secondDeriv_at_zero hL hRs hP hX le_rfl hcomp hF'.1 hsub hv
        (restrictToPositiveEdges_mem hB')) fun q _ => ?_⟩⟩
  · have e : ∀ t : ℝ, ((fun (q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) (_ : Fin 1) =>
        ((F (fieldOfPositiveValues (groupComponent q)) : ℝ) : ℂ)) ∘ expTwistPoint)
        (ofParts (groupComponent q) (t • restrictToPositiveEdges B)) = fun _ =>
        ((F (PeriodicLattice.expTwist ((t : ℂ) • B) (fieldOfPositiveValues (groupComponent q))) :
          ℝ) : ℂ) := fun t => by
      simp only [Function.comp_apply]
      rw [fieldOfPositiveValues_expTwistPoint _ _ ((t : ℂ) • B) (smul_restrictToPositiveEdges t B)]
    simp only [e]
    exact deriv_ofReal_const_fun (fun t : ℝ =>
      F (PeriodicLattice.expTwist ((t : ℂ) • B) (fieldOfPositiveValues (groupComponent q)))) 0
  · have e : ∀ s t : ℝ, ((fun (q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) (_ : Fin 1) =>
        ((F (fieldOfPositiveValues (groupComponent q)) : ℝ) : ℂ)) ∘ expTwistPoint)
        (ofParts (groupComponent q) (s • restrictToPositiveEdges B + t • restrictToPositiveEdges B')) =
        fun _ => ((F (PeriodicLattice.expTwist ((s : ℂ) • B + (t : ℂ) • B')
          (fieldOfPositiveValues (groupComponent q))) : ℝ) : ℂ) := fun s t => by
      simp only [Function.comp_apply]
      rw [fieldOfPositiveValues_expTwistPoint _ _ ((s : ℂ) • B + (t : ℂ) • B') fun r => by
        rw [Pi.add_apply, Pi.add_apply, smul_restrictToPositiveEdges, smul_restrictToPositiveEdges]]
    simp only [e]
    have h1 : (fun s : ℝ => deriv (fun t : ℝ => (fun _ : Fin 1 =>
        ((F (PeriodicLattice.expTwist ((s : ℂ) • B + (t : ℂ) • B')
          (fieldOfPositiveValues (groupComponent q))) : ℝ) : ℂ))) 0) = fun s : ℝ => fun _ =>
        ((deriv (fun t : ℝ => F (PeriodicLattice.expTwist ((s : ℂ) • B + (t : ℂ) • B')
          (fieldOfPositiveValues (groupComponent q)))) 0 : ℝ) : ℂ) :=
      funext fun s => deriv_ofReal_const_fun _ 0
    rw [h1]
    exact deriv_ofReal_const_fun (fun s : ℝ => deriv (fun t : ℝ =>
      F (PeriodicLattice.expTwist ((s : ℂ) • B + (t : ℂ) • B')
        (fieldOfPositiveValues (groupComponent q)))) 0) 0
theorem analytic_lineLogarithm_derivs {U : Set (Edge L n k j → ComplexMatrix2)}
    {m : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (hm : IsAnalyticFieldMap U m)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j) (c : PositiveEdge L n k j')
    (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) :
    (IsAnalyticFieldFunction U fun V => φ (deriv (lineLogarithm m V B c) 0)) ∧
      IsAnalyticFieldFunction U fun V => φ (iteratedDeriv 2 (lineLogarithm m V B c) 0) := by
  obtain ⟨hop, hmaps, i₁, i₂, hM⟩ := hm
  obtain ⟨W₂, h₂, hsub⟩ := analytic_quotientLog_expTwist hL hRs hP hX hC hM c
  have hv := restrictToPositiveEdges_mem hB
  let Λ : ComplexCoordinates 4 →ₗ[ℝ] ℝ := φ ∘ₗ matrixLinearEquiv.symm.toLinearMap
  have hΛ : ∀ Y, Λ (ComplexCoordinates.matrixEquiv Y) = φ Y := fun Y => by
    change φ (matrixLinearEquiv.symm (matrixLinearEquiv Y)) = φ Y
    simp
  have hline : ∀ q ∈ {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
      fieldOfPositiveValues (groupComponent q) ∈ U}, ∀ (x : PositiveEdge L n k j → ComplexMatrix2)
      (τ : ℝ), (∀ r, x r = ((τ : ℂ) • B) r.1) →
      quotientLogCoords c (pairPoint
        (ofParts (restrictToPositiveEdges (m (fieldOfPositiveValues
          (groupComponent (expTwistPoint (ofParts (groupComponent q) x)))))) Empty.elim)
        (ofParts (restrictToPositiveEdges (m (fieldOfPositiveValues (groupComponent q)))) Empty.elim)) =
      ComplexCoordinates.matrixEquiv
        (lineLogarithm m (fieldOfPositiveValues (groupComponent q)) B c τ) := by
    intro q hq x τ hx
    have hdet : (m (fieldOfPositiveValues (groupComponent q)) c).det = 1 :=
      (Matrix.mem_specialUnitaryGroup_iff.1 ((hmaps hq).1 c.1 (mem_univ _))).2
    have hinv : (m (fieldOfPositiveValues (groupComponent q)) c).adjugate =
        (m (fieldOfPositiveValues (groupComponent q)) c)⁻¹ := by
      rw [Matrix.inv_def, hdet]
      simp
    rw [fieldOfPositiveValues_expTwistPoint _ _ _ hx]
    change ComplexCoordinates.matrixEquiv (Complex.I⁻¹ • ComplexMatrix2.logSeries
      (m (PeriodicLattice.expTwist ((τ : ℂ) • B) (fieldOfPositiveValues (groupComponent q))) c *
        (m (fieldOfPositiveValues (groupComponent q)) c).adjugate)) = _
    rw [hinv]
    rfl
  let G : (PositiveEdge L n k j ⊕ PositiveEdge L n k j → ComplexMatrix2) → ComplexCoordinates 4 :=
    fun q => quotientLogCoords c (pairPoint
      (ofParts (restrictToPositiveEdges (m (fieldOfPositiveValues (groupComponent (expTwistPoint q)))))
        Empty.elim)
      (ofParts (restrictToPositiveEdges (m (fieldOfPositiveValues
        (groupComponent (ofParts (groupComponent q) Empty.elim :
          PositiveEdge L n k j ⊕ Empty → ComplexMatrix2)))))
        Empty.elim))
  have hG : IsSubspaceAnalyticToCoords (hermitianTracelessFunctions (PositiveEdge L n k j)) W₂ G := h₂
  refine ⟨⟨hop, i₁, analyticToCoords_congr (analytic_realLinear_comp hL hRs bot_le
      (analytic_firstDeriv_at_zero hL hRs hP hX le_rfl hG hM.1 hsub hv) Λ) fun q hq => ?_⟩,
    ⟨hop, i₁, analyticToCoords_congr (analytic_realLinear_comp hL hRs bot_le
      (analytic_secondDeriv_at_zero hL hRs hP hX le_rfl hG hM.1 hsub hv hv) Λ) fun q hq => ?_⟩⟩
  · have hD : (fun t : ℝ => G (ofParts (groupComponent q) (t • restrictToPositiveEdges B))) =
        fun t => ComplexCoordinates.matrixEquiv
          (lineLogarithm m (fieldOfPositiveValues (groupComponent q)) B c t) :=
      funext fun t => hline q hq _ t (smul_restrictToPositiveEdges t B)
    funext _
    rw [hD, deriv_matrixEquiv, hΛ]
  · have hD : ∀ s : ℝ, (fun t : ℝ => G (ofParts (groupComponent q)
        (s • restrictToPositiveEdges B + t • restrictToPositiveEdges B))) =
        fun t => ComplexCoordinates.matrixEquiv
          (lineLogarithm m (fieldOfPositiveValues (groupComponent q)) B c (s + t)) :=
      fun s => funext fun t => hline q hq _ (s + t) fun r => by
        rw [Pi.add_apply, smul_restrictToPositiveEdges, smul_restrictToPositiveEdges]
        push_cast
        rw [add_smul]
        rfl
    have hD2 : (fun s : ℝ => deriv (fun t : ℝ => G (ofParts (groupComponent q)
        (s • restrictToPositiveEdges B + t • restrictToPositiveEdges B))) 0) =
        fun s => ComplexCoordinates.matrixEquiv
          (deriv (lineLogarithm m (fieldOfPositiveValues (groupComponent q)) B c) s) :=
      funext fun s => by
        rw [hD s, deriv_matrixEquiv (fun t => lineLogarithm m
          (fieldOfPositiveValues (groupComponent q)) B c (s + t)) 0, deriv_comp_const_add, add_zero]
    funext _
    have h2 : iteratedDeriv 2 (lineLogarithm m (fieldOfPositiveValues (groupComponent q)) B c) 0 =
        deriv (deriv (lineLogarithm m (fieldOfPositiveValues (groupComponent q)) B c)) 0 := by
      rw [iteratedDeriv_eq_iterate]
      rfl
    change _ = ((φ (iteratedDeriv 2 (lineLogarithm m (fieldOfPositiveValues (groupComponent q)) B c)
      0) : ℝ) : ℂ)
    rw [hD2, deriv_matrixEquiv, hΛ, h2]
end OnTower
theorem leftChartTaylorCoefficientsAnalytic_proof (hL : AnalyticCalculusStatement)
    (hRs : LocalAnalyticityStatement)
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hX : ExpChartHolomorphy.ExpChartTheory)
    (hC : ComplexMatrix2.ExpSurjectivityAndComplexification) :
    LeftChartTaylorCoefficientsAnalytic := by
  intro L n k j j' _ _ _ _
  refine ⟨fun U F hF B hB => analytic_leftDerivs hL hRs hP hX hC hF hB,
    fun U m hm B hB c φ => analytic_lineLogarithm_derivs hL hRs hP hX hC hm hB c φ⟩
end YangMills.Construction.Tower.LeftChartTaylor
end

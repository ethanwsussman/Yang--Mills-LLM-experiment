import YangMills.Construction.Lattice.LatticesOfATorusAndTheProductTopologyOfConfigurations
import YangMills.Construction.Matrices.ImplicitFunctionOnTheRealFormProof
import YangMills.Construction.RunningCouplingSlope.CellsOfNeighbouringFineSites
import YangMills.Construction.RunningCouplingSlope.CoordinateFamiliesAreLocalProof
import YangMills.Construction.RunningCouplingSlope.FamiliesThatReadNearCellsAreLocal
import YangMills.Construction.RunningCouplingSlope.ResponseOfAUnitFormDecays
import YangMills.Construction.Towers.PolydiscServesAtTheSideInfinityProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator Topology ENNReal
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.NearCellLocality
open Tower
section Matrices
variable {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
private lemma cauchy_estimates_matrix {B : ℂ → ℂ → Matrix ι' ι ℂ} {T : ℝ → ℝ → Matrix ι' ι ℂ} {R₁ R₂ C : ℝ}
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (h₁ : ∀ p q σ τ, ‖σ‖ < R₁ → ‖τ‖ < R₂ → DifferentiableAt ℂ (fun σ' => B σ' τ p q) σ)
    (h₂ : ∀ p q σ τ, ‖σ‖ < R₁ → ‖τ‖ < R₂ → DifferentiableAt ℂ (fun τ' => B σ τ' p q) τ)
    (hb : ∀ σ τ, ‖σ‖ < R₁ → ‖τ‖ < R₂ → ‖B σ τ‖ ≤ C)
    (heq : ∀ᶠ w : ℝ × ℝ in 𝓝 (0, 0), T w.1 w.2 = B w.1 w.2)
    (hsm : ∀ p q, ContDiffAt ℝ 2 (fun w : ℝ × ℝ => T w.1 w.2 p q) 0) :
    ‖T 0 0‖ ≤ C ∧ ‖derivFirst T‖ ≤ 2 * C / R₁ ∧ ‖derivSecond T‖ ≤ 2 * C / R₂ ∧
      ‖derivMixed T‖ ≤ 8 * C / (R₁ * R₂) := by apply _root_.YangMills.SharedProofs.p47968 <;> assumption
end Matrices
section Plane
open Matrices.GroupLieProduct Coordinates.ComplexCoordinates
open Tower.IteratedSmallFieldMeans (HolomorphicInEntries)
open Tower.LeftChartFields (scalarCoords)
private lemma isHolomorphicIn_congr {N N' : ℕ} {O : Set (Coordinates.ComplexCoordinates N)}
    {f g : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates N'} (hf : IsHolomorphicIn O f)
    (h : Set.EqOn f g O) : IsHolomorphicIn O g := by apply _root_.YangMills.Construction.Tower.InfiniteSideAdmissibility.isHolomorphicIn_congr <;> assumption
private lemma differentiableAt_first_coord {N' : ℕ} {O : Set (Coordinates.ComplexCoordinates 2)}
    {h : Coordinates.ComplexCoordinates 2 → Coordinates.ComplexCoordinates N'} (hh : IsHolomorphicIn O h) {σ τ : ℂ}
    (hm : ![σ, τ] ∈ O) : DifferentiableAt ℂ (fun σ' => h ![σ', τ]) σ := by
  have h0 := (hh.2.2 _ hm 0).self_of_nhds
  have e : (fun σ' : ℂ => h ![σ', τ]) =
      (fun ζ : ℂ => h (![σ, τ] + ζ • stdBasisVector 0)) ∘ fun σ' => σ' - σ := by
    funext σ'
    simp only [Function.comp]
    congr 1
    funext i
    fin_cases i <;> simp [stdBasisVector]
  rw [e]
  have h1 : DifferentiableAt ℂ (fun σ' : ℂ => σ' - σ) σ := by fun_prop
  exact DifferentiableAt.comp σ (by simpa using h0) h1
private lemma differentiableAt_second_coord {N' : ℕ} {O : Set (Coordinates.ComplexCoordinates 2)}
    {h : Coordinates.ComplexCoordinates 2 → Coordinates.ComplexCoordinates N'} (hh : IsHolomorphicIn O h) {σ τ : ℂ}
    (hm : ![σ, τ] ∈ O) : DifferentiableAt ℂ (fun τ' => h ![σ, τ']) τ := by
  have h0 := (hh.2.2 _ hm 1).self_of_nhds
  have e : (fun τ' : ℂ => h ![σ, τ']) =
      (fun ζ : ℂ => h (![σ, τ] + ζ • stdBasisVector 1)) ∘ fun τ' => τ' - τ := by
    funext τ'
    simp only [Function.comp]
    congr 1
    funext i
    fin_cases i <;> simp [stdBasisVector]
  rw [e]
  have h1 : DifferentiableAt ℂ (fun τ' : ℂ => τ' - τ) τ := by fun_prop
  exact DifferentiableAt.comp τ (by simpa using h0) h1
private lemma isHolomorphicIn_plane (hP : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hBas : Nonempty (Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)) {β : Type}
    {S : Set (β → Matrices.ComplexMatrix2)}
    {g : (β → Matrices.ComplexMatrix2) → ℂ} {ρ : ℝ} (hg : HolomorphicInEntries scalarCoords S ρ g)
    {A₁ A₂ : β → Matrices.ComplexMatrix2} (hA₁ : ∀ b, A₁ b ∈ Matrices.ComplexMatrix2.traceless)
    (hA₂ : ∀ b, A₂ b ∈ Matrices.ComplexMatrix2.traceless) {K₁ K₂ : ℝ}
    (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂) (hK₁ : ∀ b, Matrices.ComplexMatrix2.operatorNorm (A₁ b) ≤ K₁)
    (hK₂ : ∀ b, Matrices.ComplexMatrix2.operatorNorm (A₂ b) ≤ K₂)
    (hS : ∀ w : Coordinates.ComplexCoordinates 2, w 0 • A₁ + w 1 • A₂ ∈ S) :
    IsHolomorphicIn {w : Coordinates.ComplexCoordinates 2 | ‖w 0‖ * K₁ + ‖w 1‖ * K₂ < ρ}
      (fun w => scalarCoords (g (w 0 • A₁ + w 1 • A₂))) := by
  obtain ⟨F, f, hf, hfe⟩ := hg
  obtain ⟨b⟩ := hBas
  let ν := Fintype.equivFin F
  obtain ⟨-, hν⟩ := hf b
  have hc := hν ν
  have hcoord : ∀ A : β → Matrices.ComplexMatrix2, (∀ x, A x ∈ Matrices.ComplexMatrix2.traceless) →
      ∃ c : Coordinates.ComplexCoordinates (Fintype.card F * 3), ∀ i : F,
        ∑ a : Fin 3, c (finProdFinEquiv (ν i, a)) • (b a : Matrices.ComplexMatrix2) = A i := by
    intro A hA
    refine ⟨fun m => b.repr ⟨A (ν.symm (finProdFinEquiv.symm m).1).1, hA _⟩
      (finProdFinEquiv.symm m).2, fun i => ?_⟩
    simp only [Equiv.symm_apply_apply]
    have h3 : (((∑ a, b.repr ⟨A i.1, hA _⟩ a • b a : Matrices.ComplexMatrix2.traceless)) :
        Matrices.ComplexMatrix2) = A i.1 := by
      rw [b.sum_repr]
    refine Eq.trans ?_ h3
    simp only [AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul]
  obtain ⟨c₁, e₁⟩ := hcoord A₁ hA₁
  obtain ⟨c₂, e₂⟩ := hcoord A₂ hA₂
  let Φ : Coordinates.ComplexCoordinates 2 → Coordinates.ComplexCoordinates (Fintype.card F * 3) :=
    fun w => w 0 • c₁ + w 1 • c₂
  have hΦt : ∀ w (i : F), Matrices.GroupLieProduct.tupleOfCoords b ν (Φ w) i = (w 0 • A₁ + w 1 • A₂) i.1 := by
    intro w i
    simp only [Matrices.GroupLieProduct.tupleOfCoords, tracelessTuple, Φ, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, e₁, e₂]
  have hO : IsOpen {w : Coordinates.ComplexCoordinates 2 | ‖w 0‖ * K₁ + ‖w 1‖ * K₂ < ρ} :=
    isOpen_lt (by fun_prop) continuous_const
  have hΦ : IsHolomorphicIn {w : Coordinates.ComplexCoordinates 2 | ‖w 0‖ * K₁ + ‖w 1‖ * K₂ < ρ} Φ := by
    refine ⟨hO, Continuous.continuousOn (by fun_prop), fun a _ j => ?_⟩
    refine Filter.Eventually.of_forall fun ζ => ?_
    simp only [Φ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hbound : ∀ w : Coordinates.ComplexCoordinates 2, ∀ x : β,
      Matrices.ComplexMatrix2.operatorNorm ((w 0 • A₁ + w 1 • A₂) x) ≤ ‖w 0‖ * K₁ + ‖w 1‖ * K₂ := by
    intro w x
    simp only [Pi.add_apply, Pi.smul_apply]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hK₁ x) (norm_nonneg _)
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hK₂ x) (norm_nonneg _)
  have hmaps : Set.MapsTo Φ {w : Coordinates.ComplexCoordinates 2 | ‖w 0‖ * K₁ + ‖w 1‖ * K₂ < ρ}
      (Matrices.GroupLieProduct.tupleOfCoords b ν ⁻¹' Matrices.GroupLieProduct.supBall F ρ) := by
    intro w hw
    refine ⟨fun i => ?_, ?_⟩
    · rw [hΦt]
      exact Matrices.ComplexMatrix2.traceless.add_mem
        (Matrices.ComplexMatrix2.traceless.smul_mem _ (hA₁ _))
        (Matrices.ComplexMatrix2.traceless.smul_mem _ (hA₂ _))
    · have hX : 0 ≤ ‖w 0‖ * K₁ + ‖w 1‖ * K₂ := by positivity
      refine lt_of_le_of_lt (Real.iSup_le (fun i => ?_) hX) hw
      rw [hΦt]
      exact hbound w _
  have hcomp := ((hP.1 _ _ hc.1).1 _ _ hc).2.2.2.1 2 _ Φ hΦ hmaps
  refine isHolomorphicIn_congr hcomp fun w hw => ?_
  have e : Matrices.GroupLieProduct.tupleOfCoords b ν (Φ w) = fun i : F => (w 0 • A₁ + w 1 • A₂) i.1 :=
    funext (hΦt w)
  simp only [Function.comp, e]
  rw [hfe _ (hS w)]
  have hρ : 0 < ρ := lt_of_le_of_lt (by positivity) hw
  refine lt_of_le_of_lt (iSup_le fun x => ENNReal.ofReal_le_ofReal (hbound w x)) ?_
  exact (ENNReal.ofReal_lt_ofReal_iff hρ).2 hw
end Plane
section Main
open Tower.IteratedSmallFieldMeans (HolomorphicInEntries smallFormBall)
open Tower.LeftChartFields (scalarCoords)
open Tower.CriticalBranchResponse
variable {L n k : ℕ} {ι ι' : Type}
private lemma norm_blockBetween_le [Fintype ι] [Fintype ι'] [DecidableEq ι] (c : ι → Vertex L n k k)
    (c' : ι' → Vertex L n k k) (A : Matrix ι' ι ℂ) (y' y : Vertex L n k k) :
    ‖blockBetween c c' A y' y‖ ≤ ‖A‖ := by
  classical
  have e : blockBetween c c' A y' y =
      Matrix.diagonal (fun p => if c' p = y' then (1 : ℂ) else 0) * A *
        Matrix.diagonal (fun q => if c q = y then (1 : ℂ) else 0) := by
    ext p q
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [blockBetween]
    by_cases h1 : c' p = y' <;> by_cases h2 : c q = y <;> simp [h1, h2]
  have d : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (P : κ → Prop) [DecidablePred P],
      ‖(Matrix.diagonal (fun p => if P p then (1 : ℂ) else 0) : Matrix κ κ ℂ)‖ ≤ 1 := by
    intro κ _ _ P _
    rw [Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
    split_ifs <;> simp
  rw [e]
  calc _ ≤ ‖Matrix.diagonal (fun p => if c' p = y' then (1 : ℂ) else 0) * A‖ *
        ‖(Matrix.diagonal (fun q => if c q = y then (1 : ℂ) else 0) : Matrix ι ι ℂ)‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(Matrix.diagonal (fun p => if c' p = y' then (1 : ℂ) else 0) : Matrix ι' ι' ℂ)‖ * ‖A‖) * 1 :=
        mul_le_mul (Matrix.l2_opNorm_mul _ _) (d _) (norm_nonneg _) (by positivity)
    _ ≤ (1 * ‖A‖) * 1 := by gcongr; exact d _
    _ = ‖A‖ := by ring
private def restrictToEdges (N : Set (Edge L n k 0)) (h : Edge L n k 0 → Matrices.ComplexMatrix2) :
    Edge L n k 0 → Matrices.ComplexMatrix2 :=
  open Classical in fun b => if b ∈ N then h b else 0
private lemma mem_traceless_of_mem_forms {h : Edge L n k 0 → Matrices.ComplexMatrix2}
    (hh : h ∈ complexEdgeForms L n k 0) (b : Edge L n k 0) : h b ∈ Matrices.ComplexMatrix2.traceless := by
  rcases PeriodicLattice.Bond.positive_or_opposite_positive b with hb | hb
  · exact hh.1 b hb
  · have h1 := hh.1 _ hb
    have h2 : h b.opposite = -h b := hh.2 b
    rw [h2] at h1
    simpa using Matrices.ComplexMatrix2.traceless.neg_mem h1
private lemma restrictToEdges_mem {r : ℝ} {y : Vertex L n k k} {h : Edge L n k 0 → Matrices.ComplexMatrix2}
    (hh : h ∈ complexEdgeForms L n k 0) :
    restrictToEdges (edgesNearCell r y) h ∈ complexEdgeForms L n k 0 := by
  refine ⟨fun b _ => ?_, fun b => ?_⟩
  · unfold restrictToEdges
    split_ifs
    · exact mem_traceless_of_mem_forms hh b
    · exact Matrices.ComplexMatrix2.traceless.zero_mem
  · have hm : b.opposite ∈ edgesNearCell r y ↔ b ∈ edgesNearCell r y := by
      show (cellDist (fineVertexCell b.target) y ≤ r ∧
        cellDist (fineVertexCell b.source) y ≤ r) ↔ _
      exact and_comm
    unfold restrictToEdges
    by_cases hb : b ∈ edgesNearCell r y
    · rw [if_pos hb, if_pos (hm.2 hb)]
      exact hh.2 b
    · rw [if_neg hb, if_neg fun h' => hb (hm.1 h')]
      simp
private lemma traceless_basis_nonempty : Nonempty (Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless) := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.Subspaces.RealForm.traceless_basis_nonempty <;> assumption
private lemma cellDist_nonneg (y y' : Vertex L n k k) : 0 ≤ cellDist y y' := by apply _root_.YangMills.SharedProofs.p2231 <;> assumption
private lemma plane_mem_forms {A₁ A₂ : Edge L n k 0 → Matrices.ComplexMatrix2} (h₁ : A₁ ∈ complexEdgeForms L n k 0)
    (h₂ : A₂ ∈ complexEdgeForms L n k 0) (σ τ : ℂ) : σ • A₁ + τ • A₂ ∈ complexEdgeForms L n k 0 :=
  (complexEdgeForms L n k 0).add_mem ((complexEdgeForms L n k 0).smul_mem _ h₁)
    ((complexEdgeForms L n k 0).smul_mem _ h₂)
private lemma plane_mem_smallFormBall {A₁ A₂ : Edge L n k 0 → Matrices.ComplexMatrix2}
    (h₁ : A₁ ∈ complexEdgeForms L n k 0)
    (h₂ : A₂ ∈ complexEdgeForms L n k 0) {K₁ K₂ ρ : ℝ}
    (b₁ : ∀ b, Matrices.ComplexMatrix2.operatorNorm (A₁ b) ≤ K₁)
    (b₂ : ∀ b, Matrices.ComplexMatrix2.operatorNorm (A₂ b) ≤ K₂) {σ τ : ℂ} (hs : ‖σ‖ * K₁ + ‖τ‖ * K₂ < ρ) :
    σ • A₁ + τ • A₂ ∈ smallFormBall L n k ρ := by
  refine ⟨plane_mem_forms h₁ h₂ σ τ, iSup_le fun b => ENNReal.ofReal_le_ofReal ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply]
  refine ((norm_add_le _ _).trans (add_le_add ?_ ?_)).trans hs.le
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (b₁ b) (norm_nonneg _)
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (b₂ b) (norm_nonneg _)
private lemma isHolomorphicIn_plane_entry (hP : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {g : (Edge L n k 0 → Matrices.ComplexMatrix2) → ℂ} {ρ : ℝ}
    (hg : HolomorphicInEntries scalarCoords
      (complexEdgeForms L n k 0 : Set (Edge L n k 0 → Matrices.ComplexMatrix2)) ρ g)
    {A₁ A₂ : Edge L n k 0 → Matrices.ComplexMatrix2}
    (h₁ : A₁ ∈ complexEdgeForms L n k 0) (h₂ : A₂ ∈ complexEdgeForms L n k 0) {K₁ K₂ : ℝ}
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (b₁ : ∀ b, Matrices.ComplexMatrix2.operatorNorm (A₁ b) ≤ K₁)
    (b₂ : ∀ b, Matrices.ComplexMatrix2.operatorNorm (A₂ b) ≤ K₂) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn
      {w : Coordinates.ComplexCoordinates 2 | ‖w 0‖ * K₁ + ‖w 1‖ * K₂ < ρ}
      (fun w => scalarCoords (g (w 0 • A₁ + w 1 • A₂))) :=
  isHolomorphicIn_plane hP traceless_basis_nonempty hg (mem_traceless_of_mem_forms h₁)
    (mem_traceless_of_mem_forms h₂) hK₁ hK₂ b₁ b₂ fun w => plane_mem_forms h₁ h₂ _ _
private lemma contDiffAt_real_plane (hP : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {g : (Edge L n k 0 → Matrices.ComplexMatrix2) → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : HolomorphicInEntries scalarCoords
      (complexEdgeForms L n k 0 : Set (Edge L n k 0 → Matrices.ComplexMatrix2)) ρ g)
    {A₁ A₂ : Edge L n k 0 → Matrices.ComplexMatrix2}
    (h₁ : A₁ ∈ complexEdgeForms L n k 0) (h₂ : A₂ ∈ complexEdgeForms L n k 0) {K : ℝ} (hK : 0 ≤ K)
    (b₁ : ∀ b, Matrices.ComplexMatrix2.operatorNorm (A₁ b) ≤ K)
    (b₂ : ∀ b, Matrices.ComplexMatrix2.operatorNorm (A₂ b) ≤ K) :
    ContDiffAt ℝ 2 (fun w : ℝ × ℝ => g ((w.1 : ℂ) • A₁ + (w.2 : ℂ) • A₂)) 0 := by
  have hh := isHolomorphicIn_plane_entry hP hg h₁ h₂ hK hK b₁ b₂
  have hsm := ((hP.1 _ _ hh.1).1 _ _ hh).2.1
  have h0 : (![0, 0] : Coordinates.ComplexCoordinates 2) ∈
      {w : Coordinates.ComplexCoordinates 2 | ‖w 0‖ * K + ‖w 1‖ * K < ρ} := by
    simpa using hρ
  have hat : ContDiffAt ℝ 2 (fun w : Coordinates.ComplexCoordinates 2 =>
      scalarCoords (g (w 0 • A₁ + w 1 • A₂))) ![0, 0] :=
    ((hsm _ h0).contDiffAt (hh.1.mem_nhds h0)).of_le (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
      WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hem : ContDiffAt ℝ 2
      (fun w : ℝ × ℝ => (![(w.1 : ℂ), (w.2 : ℂ)] : Coordinates.ComplexCoordinates 2)) 0 := by
    refine contDiffAt_pi.2 fun i => ?_
    fin_cases i
    · exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).contDiffAt
    · exact (Complex.ofRealCLM.contDiff.comp contDiff_snd).contDiffAt
  have h00 : (fun w : ℝ × ℝ => (![(w.1 : ℂ), (w.2 : ℂ)] : Coordinates.ComplexCoordinates 2)) 0 =
      ![0, 0] := by
    simp
  have hc := ContDiffAt.comp (0 : ℝ × ℝ) (h00 ▸ hat) hem
  have hp := (contDiffAt_pi.1 hc) 0
  simpa [Function.comp_def, scalarCoords] using hp
private lemma blockBetween_estimates (hP : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] {ρ C r : ℝ} (hρ : 0 < ρ)
    (hC : 0 ≤ C) {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k}
    {F : (Edge L n k 0 → Matrices.ComplexMatrix2) → Matrix ι' ι ℂ} (hF : IsLocalNearCells c c' F ρ C r)
    {H₁ H₂ : Edge L n k 0 → Matrices.ComplexMatrix2} (hH₁ : H₁ ∈ complexEdgeForms L n k 0)
    (hH₂ : H₂ ∈ complexEdgeForms L n k 0) {Ch : ℝ} (hCh : 0 < Ch)
    (hb₁ : ∀ b, Matrices.ComplexMatrix2.operatorNorm (H₁ b) ≤ Ch)
    (hb₂ : ∀ b, Matrices.ComplexMatrix2.operatorNorm (H₂ b) ≤ Ch)
    (y' y : Vertex L n k k) {K₁ K₂ : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hN₁ : ∀ b ∈ edgesNearCell r y', Matrices.ComplexMatrix2.operatorNorm (H₁ b) ≤ K₁)
    (hN₂ : ∀ b ∈ edgesNearCell r y', Matrices.ComplexMatrix2.operatorNorm (H₂ b) ≤ K₂) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hCbC : cellDist y' y ≤ r → C ≤ Cb) :
    ‖blockBetween c c' (F ((((0 : ℝ) : ℂ)) • H₁ + (((0 : ℝ) : ℂ)) • H₂)) y' y‖ ≤ Cb ∧
    ‖blockBetween c c' (derivFirst fun s t : ℝ => F ((s : ℂ) • H₁ + (t : ℂ) • H₂)) y' y‖ ≤
      2 * Cb / (ρ / (4 * K₁)) ∧
    ‖blockBetween c c' (derivSecond fun s t : ℝ => F ((s : ℂ) • H₁ + (t : ℂ) • H₂)) y' y‖ ≤
      2 * Cb / (ρ / (4 * K₂)) ∧
    ‖blockBetween c c' (derivMixed fun s t : ℝ => F ((s : ℂ) • H₁ + (t : ℂ) • H₂)) y' y‖ ≤
      8 * Cb / ((ρ / (4 * K₁)) * (ρ / (4 * K₂))) := by
  classical
  set N := edgesNearCell r y' with hN
  set A₁ := restrictToEdges N H₁ with hA₁
  set A₂ := restrictToEdges N H₂ with hA₂
  have fA₁ : A₁ ∈ complexEdgeForms L n k 0 := restrictToEdges_mem hH₁
  have fA₂ : A₂ ∈ complexEdgeForms L n k 0 := restrictToEdges_mem hH₂
  have bA₁ : ∀ b, Matrices.ComplexMatrix2.operatorNorm (A₁ b) ≤ K₁ := by
    intro b
    simp only [hA₁, restrictToEdges]
    split_ifs with h
    · exact hN₁ b h
    · simpa using hK₁.le
  have bA₂ : ∀ b, Matrices.ComplexMatrix2.operatorNorm (A₂ b) ≤ K₂ := by
    intro b
    simp only [hA₂, restrictToEdges]
    split_ifs with h
    · exact hN₂ b h
    · simpa using hK₂.le
  set R₁ := ρ / (4 * K₁) with hR₁
  set R₂ := ρ / (4 * K₂) with hR₂
  have pR₁ : 0 < R₁ := by positivity
  have pR₂ : 0 < R₂ := by positivity
  have inO : ∀ σ τ : ℂ, ‖σ‖ < R₁ → ‖τ‖ < R₂ → ‖σ‖ * K₁ + ‖τ‖ * K₂ < ρ := by
    intro σ τ hσ hτ
    have e₁ : ‖σ‖ * K₁ < ρ / 4 := by
      have := mul_lt_mul_of_pos_right hσ hK₁
      calc ‖σ‖ * K₁ < R₁ * K₁ := this
        _ = ρ / 4 := by rw [hR₁]; field_simp
    have e₂ : ‖τ‖ * K₂ < ρ / 4 := by
      have := mul_lt_mul_of_pos_right hτ hK₂
      calc ‖τ‖ * K₂ < R₂ * K₂ := this
        _ = ρ / 4 := by rw [hR₂]; field_simp
    linarith
  set B : ℂ → ℂ → Matrix ι' ι ℂ := fun σ τ => blockBetween c c' (F (σ • A₁ + τ • A₂)) y' y with hB
  have hol : ∀ p q, Coordinates.ComplexCoordinates.IsHolomorphicIn
      {w : Coordinates.ComplexCoordinates 2 | ‖w 0‖ * K₁ + ‖w 1‖ * K₂ < ρ}
      (fun w => scalarCoords (F (w 0 • A₁ + w 1 • A₂) p q)) := fun p q =>
    isHolomorphicIn_plane_entry hP (hF.holomorphic p q) fA₁ fA₂ hK₁.le hK₂.le bA₁ bA₂
  have entry : ∀ p q (σ τ : ℂ), B σ τ p q =
      if c' p = y' ∧ c q = y then F (σ • A₁ + τ • A₂) p q else 0 := by
    intro p q σ τ
    simp only [hB, blockBetween]
    split_ifs <;> rfl
  have d₁ : ∀ p q σ τ, ‖σ‖ < R₁ → ‖τ‖ < R₂ → DifferentiableAt ℂ (fun σ' => B σ' τ p q) σ := by
    intro p q σ τ hσ hτ
    simp only [entry]
    split_ifs
    · have hm : (![σ, τ] : Coordinates.ComplexCoordinates 2) ∈
          {w : Coordinates.ComplexCoordinates 2 | ‖w 0‖ * K₁ + ‖w 1‖ * K₂ < ρ} := by
        simpa using inO σ τ hσ hτ
      have := differentiableAt_pi.1 (differentiableAt_first_coord (hol p q) hm) 0
      simpa [scalarCoords] using this
    · exact differentiableAt_const _
  have d₂ : ∀ p q σ τ, ‖σ‖ < R₁ → ‖τ‖ < R₂ → DifferentiableAt ℂ (fun τ' => B σ τ' p q) τ := by
    intro p q σ τ hσ hτ
    simp only [entry]
    split_ifs
    · have hm : (![σ, τ] : Coordinates.ComplexCoordinates 2) ∈
          {w : Coordinates.ComplexCoordinates 2 | ‖w 0‖ * K₁ + ‖w 1‖ * K₂ < ρ} := by
        simpa using inO σ τ hσ hτ
      have := differentiableAt_pi.1 (differentiableAt_second_coord (hol p q) hm) 0
      simpa [scalarCoords] using this
    · exact differentiableAt_const _
  have bd : ∀ σ τ, ‖σ‖ < R₁ → ‖τ‖ < R₂ → ‖B σ τ‖ ≤ Cb := by
    intro σ τ hσ hτ
    have hs : σ • A₁ + τ • A₂ ∈ smallFormBall L n k ρ :=
      plane_mem_smallFormBall fA₁ fA₂ bA₁ bA₂ (inO σ τ hσ hτ)
    by_cases hd : cellDist y' y ≤ r
    · exact (norm_blockBetween_le c c' _ y' y).trans ((hF.norm_le _ hs).trans (hCbC hd))
    · have : B σ τ = 0 := by
        ext p q
        rw [entry]
        split_ifs with h
        · exact hF.eq_zero_of_far _ hs p q (by rw [h.1, h.2]; exact not_le.1 hd)
        · rfl
      rw [this, norm_zero]
      exact hCb
  set T : ℝ → ℝ → Matrix ι' ι ℂ := fun s t => F ((s : ℂ) • H₁ + (t : ℂ) • H₂) with hT
  have smallNear : ∀ᶠ w : ℝ × ℝ in 𝓝 (0, 0),
      ‖(w.1 : ℂ)‖ * Ch + ‖(w.2 : ℂ)‖ * Ch < ρ ∧ ‖(w.1 : ℂ)‖ * K₁ + ‖(w.2 : ℂ)‖ * K₂ < ρ := by
    have c₁ : ContinuousAt (fun w : ℝ × ℝ => ‖(w.1 : ℂ)‖ * Ch + ‖(w.2 : ℂ)‖ * Ch) (0, 0) := by
      fun_prop
    have c₂ : ContinuousAt (fun w : ℝ × ℝ => ‖(w.1 : ℂ)‖ * K₁ + ‖(w.2 : ℂ)‖ * K₂) (0, 0) := by
      fun_prop
    exact (c₁.eventually (gt_mem_nhds (by simpa using hρ))).and
      (c₂.eventually (gt_mem_nhds (by simpa using hρ)))
  have heq : ∀ᶠ w : ℝ × ℝ in 𝓝 (0, 0),
      blockBetween c c' (T w.1 w.2) y' y = B w.1 w.2 := by
    filter_upwards [smallNear] with w hw
    have s₁ : (w.1 : ℂ) • H₁ + (w.2 : ℂ) • H₂ ∈ smallFormBall L n k ρ :=
      plane_mem_smallFormBall hH₁ hH₂ hb₁ hb₂ hw.1
    have s₂ : (w.1 : ℂ) • A₁ + (w.2 : ℂ) • A₂ ∈ smallFormBall L n k ρ :=
      plane_mem_smallFormBall fA₁ fA₂ bA₁ bA₂ hw.2
    ext p q
    rw [entry]
    simp only [blockBetween, hT]
    split_ifs with h
    · refine hF.eq_of_eqOn p q _ s₁ _ s₂ fun b hb => ?_
      have hbN : b ∈ N := by rw [hN, ← h.1]; exact hb
      simp [hA₁, hA₂, restrictToEdges, hbN]
    · rfl
  have smT : ∀ p q, ContDiffAt ℝ 2 (fun w : ℝ × ℝ => T w.1 w.2 p q) 0 := fun p q =>
    contDiffAt_real_plane hP hρ (hF.holomorphic p q) hH₁ hH₂ hCh.le hb₁ hb₂
  have smB : ∀ p q, ContDiffAt ℝ 2
      (fun w : ℝ × ℝ => blockBetween c c' (T w.1 w.2) y' y p q) 0 := by
    intro p q
    simp only [blockBetween]
    split_ifs
    · exact smT p q
    · exact contDiffAt_const
  obtain ⟨v₀, v₁, v₂, v₃⟩ := cauchy_estimates_matrix (T := fun s t => blockBetween c c' (T s t) y' y)
    pR₁ pR₂ d₁ d₂ bd heq smB
  refine ⟨v₀, ?_, ?_, ?_⟩
  · refine le_of_eq_of_le (congrArg norm ?_) v₁
    ext p q
    simp only [blockBetween, derivFirst]
    split_ifs <;> simp
  · refine le_of_eq_of_le (congrArg norm ?_) v₂
    ext p q
    simp only [blockBetween, derivSecond]
    split_ifs <;> simp
  · refine le_of_eq_of_le (congrArg norm ?_) v₃
    ext p q
    simp only [blockBetween, derivMixed]
    split_ifs <;> simp
private lemma mem_complexEdgeForms_of_real (h : edgeFormSpace L n k 0) :
    (h : Edge L n k 0 → Matrices.ComplexMatrix2) ∈ complexEdgeForms L n k 0 :=
  ⟨fun b hb => (h.2.1 b hb).2, h.2.2⟩
theorem nearCellFamiliesAreLocal (hResp : UnitFormResponseDecays)
    (hCells : NeighbouringFineVertexCells)
    (hP : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    NearCellFamiliesAreLocal := by
  intro L hL ρ C r hρ hC hr
  obtain ⟨Ch, θ, hCh, hθ, hR⟩ := hResp L hL
  set E := Real.exp (θ * r) with hE
  have pE : 0 < E := Real.exp_pos _
  set K := Ch * E with hK
  have pK : 0 < K := by positivity
  refine ⟨C * E * (1 + 8 * K / ρ + 128 * K ^ 2 / ρ ^ 2) + 1, θ, by positivity, hθ, fun k hk => ?_⟩
  obtain ⟨n₀, h₀⟩ := hR k hk
  refine ⟨n₀, fun n hn hn0 => ?_⟩
  intro ι ι' _ _ _ c c' F hF z
  classical
  obtain ⟨hsymm, htri, -, -⟩ := hCells L hL n k
  obtain ⟨dec₁, -, -⟩ := h₀ n hn hn0 0
  obtain ⟨dec₂, -, -⟩ := h₀ n hn hn0 z
  set H₁ : Edge L n k 0 → Matrices.ComplexMatrix2 :=
    Subtype.val (periodicResponse L n k (pauliUnitForm L n k 0)) with hH₁
  set H₂ : Edge L n k 0 → Matrices.ComplexMatrix2 :=
    Subtype.val (periodicResponse L n k (pauliUnitForm L n k z)) with hH₂
  have fH₁ : H₁ ∈ complexEdgeForms L n k 0 := mem_complexEdgeForms_of_real _
  have fH₂ : H₂ ∈ complexEdgeForms L n k 0 := mem_complexEdgeForms_of_real _
  have le_exp : ∀ x : ℝ, 0 ≤ x → Real.exp (-(θ * x)) ≤ 1 := fun x hx =>
    Real.exp_le_one_iff.2 (by nlinarith)
  have bH₁ : ∀ b, Matrices.ComplexMatrix2.operatorNorm (H₁ b) ≤ Ch := fun b => (dec₁ b).trans (by
    have := le_exp _ (cellDist_nonneg (fineVertexCell b.source) (cellOfCoords L n k 0))
    nlinarith)
  have bH₂ : ∀ b, Matrices.ComplexMatrix2.operatorNorm (H₂ b) ≤ Ch := fun b => (dec₂ b).trans (by
    have := le_exp _ (cellDist_nonneg (fineVertexCell b.source) (cellOfCoords L n k z))
    nlinarith)
  have near : ∀ (c₀ y' : Vertex L n k k) (H : Edge L n k 0 → Matrices.ComplexMatrix2),
      (∀ b, Matrices.ComplexMatrix2.operatorNorm (H b) ≤
        Ch * Real.exp (-(θ * cellDist (fineVertexCell b.source) c₀))) →
      ∀ b ∈ edgesNearCell r y', Matrices.ComplexMatrix2.operatorNorm (H b) ≤ K * cellDecayWeight θ c₀ y' := by
    intro c₀ y' H hH b hb
    refine (hH b).trans ?_
    have t1 : cellDist y' c₀ ≤ cellDist y' (fineVertexCell b.source) +
        cellDist (fineVertexCell b.source) c₀ := htri _ _ _
    have t2 : cellDist y' (fineVertexCell b.source) ≤ r := by
      rw [hsymm]
      exact hb.1
    have t3 : Real.exp (-(θ * cellDist (fineVertexCell b.source) c₀)) ≤
        E * cellDecayWeight θ c₀ y' := by
      rw [hE, cellDecayWeight, ← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith
    calc _ ≤ Ch * (E * cellDecayWeight θ c₀ y') := by gcongr
      _ = K * cellDecayWeight θ c₀ y' := by rw [hK]; ring
  have pW : ∀ c₀ y' : Vertex L n k k, 0 < cellDecayWeight θ c₀ y' := fun _ _ => Real.exp_pos _
  have main := fun (y' y : Vertex L n k k) => blockBetween_estimates hP hρ hC hF fH₁ fH₂ hCh bH₁ bH₂ y' y
    (mul_pos pK (pW (cellOfCoords L n k 0) y')) (mul_pos pK (pW (cellOfCoords L n k z) y'))
    (near _ y' H₁ dec₁) (near _ y' H₂ dec₂)
    (Cb := C * E * Real.exp (-(θ * cellDist y' y))) (by positivity) (fun hd => by
      have : (1 : ℝ) ≤ E * Real.exp (-(θ * cellDist y' y)) := by
        rw [hE, ← Real.exp_add]
        exact Real.one_le_exp (by nlinarith)
      nlinarith)
  set G := C * E with hG
  have pG : 0 ≤ G := by positivity
  have pa : 0 ≤ 8 * K / ρ := by positivity
  have pb : 0 ≤ 128 * K ^ 2 / ρ ^ 2 := by positivity
  have m₀ : G ≤ G * (1 + 8 * K / ρ + 128 * K ^ 2 / ρ ^ 2) + 1 := by
    nlinarith [mul_nonneg pG pa, mul_nonneg pG pb]
  have m₁ : G * (8 * K / ρ) ≤ G * (1 + 8 * K / ρ + 128 * K ^ 2 / ρ ^ 2) + 1 := by
    nlinarith [mul_nonneg pG pb]
  have m₂ : G * (128 * K ^ 2 / ρ ^ 2) ≤ G * (1 + 8 * K / ρ + 128 * K ^ 2 / ρ ^ 2) + 1 := by
    nlinarith [mul_nonneg pG pa]
  refine ⟨fun p q => contDiffAt_real_plane hP hρ (hF.holomorphic p q) fH₁ fH₂ hCh.le bH₁ bH₂,
    fun y' y => ?_, fun y' y => ?_, fun y' y => ?_, fun y' y => ?_⟩
  · refine (main y' y).1.trans ?_
    have hX := Real.exp_pos (-(θ * cellDist y' y))
    calc G * Real.exp (-(θ * cellDist y' y))
        ≤ (G * (1 + 8 * K / ρ + 128 * K ^ 2 / ρ ^ 2) + 1) * Real.exp (-(θ * cellDist y' y)) :=
          mul_le_mul_of_nonneg_right m₀ hX.le
      _ = _ := by ring
  · refine (main y' y).2.1.trans ?_
    have hX := Real.exp_pos (-(θ * cellDist y' y))
    have hw := pW (cellOfCoords L n k 0) y'
    have e : 2 * (G * Real.exp (-(θ * cellDist y' y))) /
        (ρ / (4 * (K * cellDecayWeight θ (cellOfCoords L n k 0) y'))) =
        G * (8 * K / ρ) * Real.exp (-(θ * cellDist y' y)) *
          cellDecayWeight θ (cellOfCoords L n k 0) y' := by
      field_simp
      ring
    rw [e]
    gcongr
  · refine (main y' y).2.2.1.trans ?_
    have hX := Real.exp_pos (-(θ * cellDist y' y))
    have hw := pW (cellOfCoords L n k z) y'
    have e : 2 * (G * Real.exp (-(θ * cellDist y' y))) /
        (ρ / (4 * (K * cellDecayWeight θ (cellOfCoords L n k z) y'))) =
        G * (8 * K / ρ) * Real.exp (-(θ * cellDist y' y)) *
          cellDecayWeight θ (cellOfCoords L n k z) y' := by
      field_simp
      ring
    rw [e]
    gcongr
  · refine (main y' y).2.2.2.trans ?_
    have hX := Real.exp_pos (-(θ * cellDist y' y))
    have hw₁ := pW (cellOfCoords L n k 0) y'
    have hw₂ := pW (cellOfCoords L n k z) y'
    have e : 8 * (G * Real.exp (-(θ * cellDist y' y))) /
        ((ρ / (4 * (K * cellDecayWeight θ (cellOfCoords L n k 0) y'))) *
          (ρ / (4 * (K * cellDecayWeight θ (cellOfCoords L n k z) y')))) =
        G * (128 * K ^ 2 / ρ ^ 2) * Real.exp (-(θ * cellDist y' y)) *
          (cellDecayWeight θ (cellOfCoords L n k 0) y' * cellDecayWeight θ (cellOfCoords L n k z) y') := by
      field_simp
      ring
    rw [e]
    gcongr
end Main
end YangMills.Construction.RunningCouplingSlope.NearCellLocality
end

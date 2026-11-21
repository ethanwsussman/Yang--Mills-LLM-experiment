import YangMills.Construction.InfiniteLattice.BondsPlaquettesCircuitsAndConfigurationsOfTheLatticeOfACutoffProof
import YangMills.Construction.InfiniteLattice.PlaquetteFunctionAndActionOfTheIsometriesProof
import YangMills.Construction.SourcesAndGluing.CumulantsOfBoundedVariablesProof
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.InequalityOnMirroredCopies.ChessboardValueFallsToTheLeastTorusProof
import YangMills.Construction.Lattice.CellGridPropertiesProofs
import YangMills.Construction.Lattice.FaceBoundaryHolonomy
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.BoxTorus
open YangMills.Construction.PeriodicLattice (meshSize)
noncomputable section
namespace YangMills.Construction.BoxTorus.FaceBoundary
def realTrace (g : Conventions.StandingParameters.gaugeGroup) : ℝ :=
  (Matrices.ComplexMatrix2.fullTrace (g : Matrices.ComplexMatrix2)).re
theorem realTrace_rotate (a b c e : Conventions.StandingParameters.gaugeGroup) :
    realTrace (b * c * e * a) = realTrace (a * b * c * e) := by apply _root_.YangMills.Construction.InfiniteLattice.FaceEnergyAndMotions.reTraceLoop_rotate <;> assumption
theorem realTrace_inv (g : Conventions.StandingParameters.gaugeGroup) :
    realTrace g⁻¹ = realTrace g := by apply _root_.YangMills.Construction.RefinedLatticeSymmetries.re_fullTrace_inv <;> assumption
theorem abs_realTrace_le_two (g : Conventions.StandingParameters.gaugeGroup) :
    |realTrace g| ≤ 2 := by apply _root_.YangMills.Construction.SourcesAndGluing.BoundedCumulants.abs_re_fullTrace_le <;> assumption
theorem fin_four_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by apply _root_.YangMills.Construction.GaugeFixing.fin_four_cases <;> assumption
theorem realTrace_cyclic (t : Fin 4 → Conventions.StandingParameters.gaugeGroup) (k : Fin 4) :
    realTrace (t k * t (k + 1) * t (k + 2) * t (k + 3)) = realTrace (t 0 * t 1 * t 2 * t 3) := by
  rcases fin_four_cases k with rfl | rfl | rfl | rfl
  · rfl
  · exact realTrace_rotate (t 0) (t 1) (t 2) (t 3)
  · exact (realTrace_rotate (t 1) (t 2) (t 3) (t 0)).trans (realTrace_rotate (t 0) (t 1) (t 2) (t 3))
  · exact (realTrace_rotate (t 2) (t 3) (t 0) (t 1)).trans
      ((realTrace_rotate (t 1) (t 2) (t 3) (t 0)).trans (realTrace_rotate (t 0) (t 1) (t 2) (t 3)))
theorem realTrace_cyclic_inv (t : Fin 4 → Conventions.StandingParameters.gaugeGroup) (k : Fin 4) :
    realTrace ((t (k - 1))⁻¹ * (t (k - 2))⁻¹ * (t (k - 3))⁻¹ * (t k)⁻¹) =
      realTrace (t 0 * t 1 * t 2 * t 3) := by
  have e : k - 1 = k + 3 ∧ k - 2 = k + 2 ∧ k - 3 = k + 1 := by
    revert k
    decide
  rw [e.1, e.2.1, e.2.2, ← realTrace_cyclic t k,
    ← realTrace_inv (t k * t (k + 1) * t (k + 2) * t (k + 3))]
  simp only [mul_inv_rev, mul_assoc]
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
theorem fin_four_walk_rotation_or_reflection (s₀ s₁ s₂ s₃ : Fin 4) :
    s₀ ≠ s₁ → s₀ ≠ s₂ → s₀ ≠ s₃ → s₁ ≠ s₂ → s₁ ≠ s₃ → s₂ ≠ s₃ →
    s₁ ≠ s₀ + 2 → s₂ ≠ s₁ + 2 → s₃ ≠ s₂ + 2 →
    (s₁ = s₀ + 1 ∧ s₂ = s₀ + 2 ∧ s₃ = s₀ + 3) ∨ (s₁ = s₀ - 1 ∧ s₂ = s₀ - 2 ∧ s₃ = s₀ - 3) := by
  revert s₀ s₁ s₂ s₃
  decide
variable {L : ℕ} {κ : ℤ}
theorem meshSize_pos (d : CellGrid L κ) : 0 < meshSize L κ := by apply _root_.YangMills.Construction.GridLattice.meshSize_pos <;> assumption
def diagonalVector (a : ℝ) (ν ν' : Fin 4) (τ τ' : ℝ) : Fin 4 → ℝ :=
  (τ * a) • basisVector ν + (τ' * a) • basisVector ν'
theorem abs_signed_basis_le {a s : ℝ} (ha : 0 < a) (hs : s = 1 ∨ s = -1) (μ i : Fin 4) :
    |((s * a) • basisVector μ) i| ≤ a := by
  by_cases h : i = μ
  · subst h
    rcases hs with rfl | rfl <;> simp [basisVector, abs_of_pos ha]
  · simp [basisVector, Pi.single_eq_of_ne h, ha.le]
theorem projection_diagonal_ne (d : CellGrid L κ)
    (hs : ∀ w w' : Fin 4 → ℝ, projection d.sideLengths w = projection d.sideLengths w' →
      (∀ μ, |w μ - w' μ| ≤ 3 * meshSize L κ) → w = w')
    {ν ν' : Fin 4} (hne : ν ≠ ν') {τ τ' σ : ℝ} (hτ : τ = 1 ∨ τ = -1) (hτ' : τ' = 1 ∨ τ' = -1)
    (hσ : σ = 1 ∨ σ = -1) (μ : Fin 4) :
    projection d.sideLengths (diagonalVector (meshSize L κ) ν ν' τ τ') ≠
      projection d.sideLengths ((σ * meshSize L κ) • basisVector μ) := by
  intro e
  have ha := meshSize_pos d
  have w := hs _ _ e fun i => by
    have h1 := abs_signed_basis_le ha hτ ν i
    have h2 := abs_signed_basis_le ha hτ' ν' i
    have h3 := abs_signed_basis_le ha hσ μ i
    have h4 := abs_sub (diagonalVector (meshSize L κ) ν ν' τ τ' i)
      (((σ * meshSize L κ) • basisVector μ) i)
    have h5 : |diagonalVector (meshSize L κ) ν ν' τ τ' i| ≤ _ :=
      abs_add_le (((τ * meshSize L κ) • basisVector ν) i) (((τ' * meshSize L κ) • basisVector ν') i)
    linarith
  have c₁ := congrFun w ν
  have c₂ := congrFun w ν'
  have hτ0 : τ * meshSize L κ ≠ 0 :=
    mul_ne_zero (by rcases hτ with rfl | rfl <;> norm_num) ha.ne'
  have hτ0' : τ' * meshSize L κ ≠ 0 :=
    mul_ne_zero (by rcases hτ' with rfl | rfl <;> norm_num) ha.ne'
  simp only [diagonalVector, basisVector, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_eq_same, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm, mul_one, mul_zero,
    add_zero, zero_add] at c₁ c₂
  by_cases h : ν = μ
  · subst h
    rw [Pi.single_eq_of_ne hne.symm, mul_zero] at c₂
    exact hτ0' c₂
  · rw [Pi.single_eq_of_ne h, mul_zero] at c₁
    exact hτ0 c₁
theorem no_edge_across_diagonal (d : CellGrid L κ)
    (hs : ∀ w w' : Fin 4 → ℝ, projection d.sideLengths w = projection d.sideLengths w' →
      (∀ μ, |w μ - w' μ| ≤ 3 * meshSize L κ) → w = w')
    {ν ν' : Fin 4} (hne : ν ≠ ν') {τ τ' : ℝ} (hτ : τ = 1 ∨ τ = -1) (hτ' : τ' = 1 ∨ τ' = -1)
    (x x' : d.GridPoint)
    (hx : (x' : d.Space) =
      (x : d.Space) + projection d.sideLengths (diagonalVector (meshSize L κ) ν ν' τ τ')) :
    ¬ ∃ b : d.DirectedEdge, b.ends = {x, x'} := by
  rintro ⟨b, hb⟩
  obtain ⟨μ, σ, hσ, hstep⟩ := b.isNeighbour
  rcases Set.pair_eq_pair_iff.mp hb with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂, hx, translate] at hstep
    exact projection_diagonal_ne d hs hne hτ hτ' hσ μ (add_left_cancel hstep)
  · rw [h₁, h₂, translate, hx, add_assoc] at hstep
    have h0 := left_eq_add.mp hstep
    refine projection_diagonal_ne d hs hne hτ hτ' (σ := -σ)
      (hσ.symm.imp (fun e => by simp [e]) (fun e => by simp [e])) μ ?_
    rw [neg_mul, neg_smul, map_neg]
    exact eq_neg_of_add_eq_zero_left h0
variable {ℓ : Fin 4 → ℝ}
theorem projection_basis_one (ν : Fin 4) :
    projection ℓ (((1 : ℝ) * meshSize L κ) • basisVector ν) = (gridStep L κ ℓ ν : Space ℓ) := by
  rw [one_mul]
  rfl
theorem projection_basis_neg_one (ν : Fin 4) :
    projection ℓ (((-1 : ℝ) * meshSize L κ) • basisVector ν) = -(gridStep L κ ℓ ν : Space ℓ) := by
  rw [neg_mul, neg_smul, map_neg, one_mul]
  rfl
theorem cornerCycle_opposite (p : Face L κ ℓ) (i : Fin 4) :
    ∃ τ τ' : ℝ, (τ = 1 ∨ τ = -1) ∧ (τ' = 1 ∨ τ' = -1) ∧
      (cornerCycle p (i + 2) : Space ℓ) =
        (cornerCycle p i : Space ℓ) +
          projection ℓ (diagonalVector (meshSize L κ) p.dir₁ p.dir₂ τ τ') := by
  rcases fin_four_cases i with rfl | rfl | rfl | rfl
  · refine ⟨1, 1, Or.inl rfl, Or.inl rfl, ?_⟩
    rw [diagonalVector, map_add, projection_basis_one, projection_basis_one]
    show ((p.corner + gridStep L κ ℓ p.dir₁ + gridStep L κ ℓ p.dir₂ : GridPoint L κ ℓ) : Space ℓ) =
      (p.corner : Space ℓ) + _
    simp only [AddSubgroup.coe_add]
    abel
  · refine ⟨-1, 1, Or.inr rfl, Or.inl rfl, ?_⟩
    rw [diagonalVector, map_add, projection_basis_one, projection_basis_neg_one]
    show ((p.corner + gridStep L κ ℓ p.dir₂ : GridPoint L κ ℓ) : Space ℓ) =
      ((p.corner + gridStep L κ ℓ p.dir₁ : GridPoint L κ ℓ) : Space ℓ) + _
    simp only [AddSubgroup.coe_add]
    abel
  · refine ⟨-1, -1, Or.inr rfl, Or.inr rfl, ?_⟩
    rw [diagonalVector, map_add, projection_basis_neg_one, projection_basis_neg_one]
    show (p.corner : Space ℓ) =
      ((p.corner + gridStep L κ ℓ p.dir₁ + gridStep L κ ℓ p.dir₂ : GridPoint L κ ℓ) : Space ℓ) + _
    simp only [AddSubgroup.coe_add]
    abel
  · refine ⟨1, -1, Or.inl rfl, Or.inr rfl, ?_⟩
    rw [diagonalVector, map_add, projection_basis_one, projection_basis_neg_one]
    show ((p.corner + gridStep L κ ℓ p.dir₁ : GridPoint L κ ℓ) : Space ℓ) =
      ((p.corner + gridStep L κ ℓ p.dir₂ : GridPoint L κ ℓ) : Space ℓ) + _
    simp only [AddSubgroup.coe_add]
    abel
def boundaryCycle (p : Face L κ ℓ) : Fin 4 → DirectedEdge L κ ℓ :=
  ![edgeFrom p.corner p.dir₁, edgeFrom (p.corner + gridStep L κ ℓ p.dir₁) p.dir₂,
    (edgeFrom (p.corner + gridStep L κ ℓ p.dir₂) p.dir₁).flip,
    (edgeFrom p.corner p.dir₂).flip]
theorem boundaryCycle_joins (p : Face L κ ℓ) : EdgesJoinCycle (cornerCycle p) (boundaryCycle p) := by
  intro i
  rcases fin_four_cases i with rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨add_right_comm _ _ _, rfl⟩
  · exact ⟨rfl, rfl⟩
theorem eq_of_edgesJoinCycle {z : Fin 4 → GridPoint L κ ℓ} {b b' : Fin 4 → DirectedEdge L κ ℓ}
    (h : EdgesJoinCycle z b) (h' : EdgesJoinCycle z b') : b = b' :=
  funext fun i => DirectedEdge.ext ((h i).1.trans (h' i).1.symm) ((h i).2.trans (h' i).2.symm)
theorem faceHolonomy_eq_boundaryCycle (U : GaugeConfig L κ ℓ) (p : Face L κ ℓ)
    (hinv : ∀ b : DirectedEdge L κ ℓ, edgeVariable U b.flip = (edgeVariable U b)⁻¹) :
    faceHolonomy U p = cycleProduct U (boundaryCycle p) := by
  have r₂ : edgeVariable U (boundaryCycle p 2) =
      (edgeVariable U (edgeFrom (p.corner + gridStep L κ ℓ p.dir₂) p.dir₁))⁻¹ := hinv _
  have r₃ : edgeVariable U (boundaryCycle p 3) =
      (edgeVariable U (edgeFrom p.corner p.dir₂))⁻¹ := hinv _
  simp only [cycleProduct, faceHolonomy, r₂, r₃]
  rfl
theorem faceEnergy_eq (U : GaugeConfig L κ ℓ) (p : Face L κ ℓ) :
    faceEnergy U p = 1 - (1 / 2) * realTrace (faceHolonomy U p) := rfl
theorem edgeFrom_isForward (x : GridPoint L κ ℓ) (ν : Fin 4) : (edgeFrom x ν).IsForward :=
  ⟨ν, Or.inl rfl, by
    show ((x + gridStep L κ ℓ ν : GridPoint L κ ℓ) : Space ℓ) = translate (x : Space ℓ) _
    simp [translate, gridStep]⟩
theorem continuous_faceEnergy (p : Face L κ ℓ) :
    Continuous fun U : GaugeConfig L κ ℓ => faceEnergy U p := by apply _root_.YangMills.SharedProofs.p4767 <;> assumption
theorem faceEnergy_mem_Icc (U : GaugeConfig L κ ℓ) (p : Face L κ ℓ) :
    faceEnergy U p ∈ Set.Icc (0 : ℝ) 2 := by
  have h := abs_le.mp (abs_realTrace_le_two (faceHolonomy U p))
  rw [faceEnergy_eq]
  exact ⟨by linarith [h.2], by linarith [h.1]⟩
open Classical in
def extendByOne (E : Set (DirectedEdge L κ ℓ))
    (u : ↥(forwardPart E) → Conventions.StandingParameters.gaugeGroup) : GaugeConfig L κ ℓ :=
  fun c => if h : c ∈ forwardPart E then u ⟨c, h⟩ else 1
theorem measurable_extendByOne (E : Set (DirectedEdge L κ ℓ)) :
    Measurable (extendByOne E) := by
  refine measurable_pi_iff.mpr fun c => ?_
  by_cases h : c ∈ forwardPart E
  · simp only [extendByOne, dif_pos h]
    exact measurable_pi_apply _
  · simp only [extendByOne, dif_neg h]
    exact measurable_const
theorem edgeVariable_extendByOne (E : Set (DirectedEdge L κ ℓ)) (U : GaugeConfig L κ ℓ)
    (x : GridPoint L κ ℓ) (ν : Fin 4)
    (h : edgeFrom x ν ∈ E ∨ (edgeFrom x ν).flip ∈ E) :
    edgeVariable (extendByOne E fun b => U b.1) (edgeFrom x ν) = edgeVariable U (edgeFrom x ν) := by
  have hp := edgeFrom_isForward x ν
  have hm : (⟨edgeFrom x ν, hp⟩ : ForwardEdge L κ ℓ) ∈ forwardPart E := h
  simp only [edgeVariable, dif_pos hp, extendByOne, dif_pos hm]
theorem faceHolonomy_extendByOne (U : GaugeConfig L κ ℓ) (p : Face L κ ℓ) :
    faceHolonomy (extendByOne (boundaryEdges p) fun b => U b.1) p = faceHolonomy U p := by
  have h₀ := edgeVariable_extendByOne (boundaryEdges p) U p.corner p.dir₁ (Or.inl ⟨0, rfl, rfl⟩)
  have h₁ := edgeVariable_extendByOne (boundaryEdges p) U (p.corner + gridStep L κ ℓ p.dir₁) p.dir₂
    (Or.inl ⟨1, rfl, rfl⟩)
  have h₂ := edgeVariable_extendByOne (boundaryEdges p) U (p.corner + gridStep L κ ℓ p.dir₂) p.dir₁
    (Or.inr ⟨2, add_right_comm _ _ _, rfl⟩)
  have h₃ := edgeVariable_extendByOne (boundaryEdges p) U p.corner p.dir₂ (Or.inr ⟨3, rfl, rfl⟩)
  simp only [faceHolonomy, h₀, h₁, h₂, h₃]
theorem faceEnergy_isBoundedBorel (p : Face L κ ℓ) :
    IsBoundedBorelOfEdges (boundaryEdges p)
      (fun U : GaugeConfig L κ ℓ => ((faceEnergy U p : ℝ) : ℂ)) := by
  have hF : Continuous fun U : GaugeConfig L κ ℓ => ((faceEnergy U p : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_faceEnergy p)
  refine ⟨fun u => ((faceEnergy (extendByOne (boundaryEdges p) u) p : ℝ) : ℂ),
    hF.measurable.comp (measurable_extendByOne _), ⟨2, fun u => ?_⟩, fun U => ?_⟩
  · have h := faceEnergy_mem_Icc (extendByOne (boundaryEdges p) u) p
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  · simp only [faceEnergy, faceHolonomy_extendByOne]
theorem realTrace_cycleProduct (d : CellGrid L κ)
    (hs : ∀ w w' : Fin 4 → ℝ, projection d.sideLengths w = projection d.sideLengths w' →
      (∀ μ, |w μ - w' μ| ≤ 3 * meshSize L κ) → w = w')
    (p : d.Face) (U : d.GaugeConfig)
    (hinv : ∀ b : d.DirectedEdge, edgeVariable U b.flip = (edgeVariable U b)⁻¹)
    (z : Fin 4 → d.GridPoint) (b : Fin 4 → d.DirectedEdge)
    (hz : Function.Injective z) (hr : Set.range z = p.vertexSet) (hb : EdgesJoinCycle z b) :
    realTrace (cycleProduct U b) = realTrace (faceHolonomy U p) := by
  have hy : ∀ i, ∃ j, z i = cornerCycle p j := by
    intro i
    have hi : z i ∈ p.vertexSet := hr ▸ Set.mem_range_self i
    simp only [Face.vertexSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  choose s hsz using hy
  have sinj : Function.Injective s := fun i j h => hz (by rw [hsz, hsz, h])
  have hopp : ∀ i, s (i + 1) ≠ s i + 2 := by
    intro i e
    obtain ⟨τ, τ', hτ, hτ', hc⟩ := cornerCycle_opposite p (s i)
    refine no_edge_across_diagonal d hs p.dir₁_lt_dir₂.ne hτ hτ' _ _ hc ⟨b i, ?_⟩
    rw [← e, ← hsz, ← hsz]
    show ({(b i).source, (b i).target} : Set d.GridPoint) = _
    rw [(hb i).1, (hb i).2]
  have hne : ∀ {i j : Fin 4}, i ≠ j → s i ≠ s j := fun h e => h (sinj e)
  set R := boundaryCycle p with hR
  have hRj : EdgesJoinCycle (cornerCycle p) R := boundaryCycle_joins p
  set t : Fin 4 → Conventions.StandingParameters.gaugeGroup := fun j => edgeVariable U (R j) with ht
  have hP : faceHolonomy U p = t 0 * t 1 * t 2 * t 3 := faceHolonomy_eq_boundaryCycle U p hinv
  rw [hP]
  rcases fin_four_walk_rotation_or_reflection (s 0) (s 1) (s 2) (s 3) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hopp 0) (hopp 1) (hopp 2) with
    ⟨e₁, e₂, e₃⟩ | ⟨e₁, e₂, e₃⟩
  · have hsi : ∀ i, s i = s 0 + i := by
      intro i
      rcases fin_four_cases i with rfl | rfl | rfl | rfl
      · exact (add_zero _).symm
      · exact e₁
      · exact e₂
      · exact e₃
    have hbi : ∀ i, b i = R (s 0 + i) := fun i => DirectedEdge.ext
      (by rw [(hb i).1, hsz, hsi i, (hRj _).1])
      (by rw [(hb i).2, hsz, hsi (i + 1), (hRj _).2, add_assoc])
    have hprod : cycleProduct U b = t (s 0) * t (s 0 + 1) * t (s 0 + 2) * t (s 0 + 3) := by
      simp only [cycleProduct, hbi, ht, add_zero]
    rw [hprod, realTrace_cyclic]
  · have hsi : ∀ i, s i = s 0 - i := by
      intro i
      rcases fin_four_cases i with rfl | rfl | rfl | rfl
      · exact (sub_zero _).symm
      · exact e₁
      · exact e₂
      · exact e₃
    have hbi : ∀ i, b i = (R (s 0 - i - 1)).flip := fun i => DirectedEdge.ext
      (by
        show (b i).source = (R (s 0 - i - 1)).target
        rw [(hb i).1, hsz, hsi i, (hRj _).2, sub_add_cancel])
      (by
        show (b i).target = (R (s 0 - i - 1)).source
        rw [(hb i).2, hsz, hsi (i + 1), (hRj _).1, sub_sub])
    have e : ∀ k : Fin 4,
        k - 0 - 1 = k - 1 ∧ k - 1 - 1 = k - 2 ∧ k - 2 - 1 = k - 3 ∧ k - 3 - 1 = k := by
      decide
    obtain ⟨f₀, f₁, f₂, f₃⟩ := e (s 0)
    have hprod : cycleProduct U b =
        (t (s 0 - 1))⁻¹ * (t (s 0 - 2))⁻¹ * (t (s 0 - 3))⁻¹ * (t (s 0))⁻¹ := by
      simp only [cycleProduct, hbi, hinv, ht, f₀, f₁, f₂, f₃]
    rw [hprod, realTrace_cyclic_inv]
theorem faceBoundaryProperty_holds (h : GridLattice.Properties) : FaceBoundaryProperty := by
  intro L κ d p
  obtain ⟨hsl, -, hc, -, -⟩ := h L κ d
  have hs := hsl.2.1
  have hinv := hc.1
  refine ⟨⟨fun i => ⟨boundaryCycle p i, boundaryCycle_joins p i⟩, fun i => ?_, fun b hb U => ?_⟩,
    fun z b hz hr hb U => ?_, continuous_faceEnergy p, fun U => faceEnergy_mem_Icc U p,
    faceEnergy_isBoundedBorel p⟩
  · obtain ⟨τ, τ', hτ, hτ', hcn⟩ := cornerCycle_opposite p i
    exact no_edge_across_diagonal d hs p.dir₁_lt_dir₂.ne hτ hτ' _ _ hcn
  · rw [eq_of_edgesJoinCycle hb (boundaryCycle_joins p)]
    exact faceHolonomy_eq_boundaryCycle U p (hinv U)
  · have := realTrace_cycleProduct d hs p U (hinv U) z b hz hr hb
    rw [faceEnergy_eq, ← this]
    rfl
end YangMills.Construction.BoxTorus.FaceBoundary
end

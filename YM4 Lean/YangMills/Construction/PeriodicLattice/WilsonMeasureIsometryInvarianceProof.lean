import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.IsometryInvarianceOfWilsonMeasure
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace IsometryInvariance
open TorusMetric Matrices
variable {L m : ℕ} {j : ℤ} {N : ℕ}
theorem torusEuclidNorm_eq_sqrt_sum {S : ℝ} (x : Torus4 S) :
    torusEuclidNorm x = Real.sqrt (∑ μ, ‖x μ‖ ^ 2) := by apply _root_.YangMills.Construction.AmbientPoints.torusEuclidNorm_eq_sqrt <;> assumption
def AdmissibleMesh (L m : ℕ) (j : ℤ) (N : ℕ) : Prop :=
  0 < meshSize L j ∧ torusSide L m = (N : ℝ) * meshSize L j ∧ 8 ≤ N
theorem admissibleMesh_of (hL : 1 < L) (hm : 0 < m) {K : ℕ} (hK : 0 < K) :
    AdmissibleMesh L m (K : ℤ) (2 * L ^ (m + K)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  refine ⟨zpow_pos hL0 _, ?_, ?_⟩
  · simp only [torusSide, meshSize]
    push_cast
    rw [pow_add, zpow_neg, zpow_natCast]
    field_simp
  · have h₁ : 2 ^ (m + K) ≤ L ^ (m + K) := Nat.pow_le_pow_left hL _
    have h₂ : 2 ^ 2 ≤ 2 ^ (m + K) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
def siteOfCoords (w : Fin 4 → ℤ) : Site L m j :=
  ⟨fun μ => (((w μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)), ⟨w, fun _ => rfl⟩⟩
theorem siteOfCoords_add (w w' : Fin 4 → ℤ) :
    (siteOfCoords (w + w') : Site L m j) = siteOfCoords w + siteOfCoords w' := by
  refine Subtype.ext (funext fun μ => ?_)
  simp [siteOfCoords, add_mul]
theorem siteOfCoords_neg (w : Fin 4 → ℤ) : (siteOfCoords (-w) : Site L m j) = -siteOfCoords w := by
  refine Subtype.ext (funext fun μ => ?_)
  simp [siteOfCoords]
theorem siteOfCoords_sub (w w' : Fin 4 → ℤ) :
    (siteOfCoords (w - w') : Site L m j) = siteOfCoords w - siteOfCoords w' := by
  rw [sub_eq_add_neg, siteOfCoords_add, siteOfCoords_neg, sub_eq_add_neg]
theorem siteOfCoords_single (a : Fin 4) :
    (siteOfCoords (Pi.single a 1) : Site L m j) = unitStep L m j a := by
  refine Subtype.ext (funext fun ν => ?_)
  by_cases h : ν = a
  · subst h
    simp [siteOfCoords, unitStep, pointOnAxis]
  · simp [siteOfCoords, unitStep, pointOnAxis, Pi.single_eq_of_ne h]
theorem exists_siteOfCoords (x : Site L m j) : ∃ n : Fin 4 → ℤ, x = siteOfCoords n := by
  obtain ⟨x, n, hn⟩ := x
  exact ⟨n, Subtype.ext (funext hn)⟩
theorem exists_reduced_coord (h : AdmissibleMesh L m j N) (n : ℤ) :
    ∃ r : ℤ, (((n : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) =
        (((r : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) ∧
      ‖(((n : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m))‖ = |(r : ℝ)| * meshSize L j := by
  obtain ⟨hξ, hS, -⟩ := h
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = round ((torusSide L m)⁻¹ * ((n : ℝ) * meshSize L j)) := ⟨_, rfl⟩
  have hk' : (n : ℝ) * meshSize L j - k * torusSide L m = ((n - k * N : ℤ) : ℝ) * meshSize L j := by
    rw [hS]
    push_cast
    ring
  refine ⟨n - k * N, ?_, ?_⟩
  · rw [← hk', AddCircle.coe_sub]
    have h0 : (((k : ℝ) * torusSide L m : ℝ) : AddCircle (torusSide L m)) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨k, by simp⟩
    rw [h0, sub_zero]
  · rw [AddCircle.norm_eq, ← hk, hk', abs_mul, abs_of_pos hξ]
theorem norm_coe_small_coord (h : AdmissibleMesh L m j N) (w : ℤ) (hw : |w| ≤ 4) :
    ‖(((w : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m))‖ = |(w : ℝ)| * meshSize L j := by
  obtain ⟨hξ, hS, hN⟩ := h
  have hN' : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hw' : |(w : ℝ)| ≤ 4 := by exact_mod_cast hw
  have hS0 : 0 < torusSide L m := by
    rw [hS]
    positivity
  have := (AddCircle.norm_coe_eq_abs_iff (torusSide L m) (x := (w : ℝ) * meshSize L j) hS0.ne').2 (by
    rw [abs_mul, abs_of_pos hξ, abs_of_pos hS0, hS]
    nlinarith)
  rw [this, abs_mul, abs_of_pos hξ]
theorem torusEuclidNorm_siteOfCoords (h : AdmissibleMesh L m j N) (w : Fin 4 → ℤ)
    (hw : ∀ μ, |w μ| ≤ 4) :
    torusEuclidNorm ((siteOfCoords w : Site L m j) : FourTorus L m) =
      meshSize L j * Real.sqrt (∑ μ, (w μ : ℝ) ^ 2) := by
  have hξ := h.1
  rw [torusEuclidNorm_eq_sqrt_sum]
  have e : ∀ μ, ‖((siteOfCoords w : Site L m j) : FourTorus L m) μ‖ ^ 2 =
      (w μ : ℝ) ^ 2 * meshSize L j ^ 2 := by
    intro μ
    change ‖(((w μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m))‖ ^ 2 = _
    rw [norm_coe_small_coord h _ (hw μ), mul_pow, sq_abs]
  simp only [e]
  rw [← Finset.sum_mul, Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sqrt_sq hξ.le, mul_comm]
theorem exists_reduced_coords (h : AdmissibleMesh L m j N) (x : Site L m j) :
    ∃ r : Fin 4 → ℤ, x = siteOfCoords r ∧
      torusEuclidNorm (x : FourTorus L m) = meshSize L j * Real.sqrt (∑ μ, (r μ : ℝ) ^ 2) := by
  have hξ := h.1
  obtain ⟨n, rfl⟩ := exists_siteOfCoords x
  choose r hr hr' using fun μ => exists_reduced_coord h (n μ)
  refine ⟨r, Subtype.ext (funext hr), ?_⟩
  rw [torusEuclidNorm_eq_sqrt_sum]
  have e : ∀ μ, ‖((siteOfCoords n : Site L m j) : FourTorus L m) μ‖ ^ 2 =
      (r μ : ℝ) ^ 2 * meshSize L j ^ 2 := by
    intro μ
    change ‖(((n μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m))‖ ^ 2 = _
    rw [hr', mul_pow, sq_abs]
  simp only [e]
  rw [← Finset.sum_mul, Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sqrt_sq hξ.le, mul_comm]
theorem coords_eq_zero_of_siteOfCoords_eq_zero (h : AdmissibleMesh L m j N) {w : Fin 4 → ℤ}
    (hz : (siteOfCoords w : Site L m j) = 0) (hw : ∀ μ, |w μ| < N) : w = 0 := by
  obtain ⟨hξ, hS, hN⟩ := h
  funext μ
  have e : (((w μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 :=
    congrFun (congrArg Subtype.val hz) μ
  rw [AddCircle.coe_eq_zero_iff] at e
  obtain ⟨k, hk⟩ := e
  rw [hS, zsmul_eq_mul, ← mul_assoc] at hk
  have hk' : (k : ℝ) * N = w μ := mul_right_cancel₀ hξ.ne' hk
  have hk'' : k * (N : ℤ) = w μ := by exact_mod_cast hk'
  exact Int.eq_zero_of_abs_lt_dvd ⟨k, by rw [← hk'', mul_comm]⟩ (hw μ)
theorem eq_single_of_sum_sq_eq_one {r : Fin 4 → ℤ} (h : ∑ μ, r μ ^ 2 = 1) :
    ∃ a, r = Pi.single a 1 ∨ r = -Pi.single a 1 := by apply _root_.YangMills.Construction.InfiniteLattice.int_vec_unit_of_sum_sq_eq_one <;> assumption
theorem abs_single_one_le (a : Fin 4) (μ : Fin 4) : |(Pi.single a 1 : Fin 4 → ℤ) μ| ≤ 1 := by
  by_cases h : μ = a
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]
theorem sum_sq_single_one (a : Fin 4) :
    ∑ μ, (((Pi.single a 1 : Fin 4 → ℤ) μ : ℤ) : ℝ) ^ 2 = 1 := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp
theorem torusEuclidNorm_unitStep (h : AdmissibleMesh L m j N) (a : Fin 4) :
    torusEuclidNorm ((unitStep L m j a : Site L m j) : FourTorus L m) = meshSize L j := by
  rw [← siteOfCoords_single,
    torusEuclidNorm_siteOfCoords h _ (fun μ => (abs_single_one_le a μ).trans (by norm_num)),
    sum_sq_single_one]
  simp
theorem torusEuclidNorm_neg {S : ℝ} (x : Torus4 S) : torusEuclidNorm (-x) = torusEuclidNorm x := by
  simp [torusEuclidNorm_eq_sqrt_sum]
theorem eq_siteOfCoords_single_of_norm (h : AdmissibleMesh L m j N) {d : Site L m j}
    (hd : torusEuclidNorm (d : FourTorus L m) = meshSize L j) :
    ∃ a, d = siteOfCoords (Pi.single a 1) ∨ d = siteOfCoords (-Pi.single a 1) := by
  have hξ := h.1
  obtain ⟨r, rfl, hr⟩ := exists_reduced_coords h d
  rw [hd] at hr
  have h1 : Real.sqrt (∑ μ, (r μ : ℝ) ^ 2) = 1 := by
    have := mul_left_cancel₀ hξ.ne' (hr.symm.trans (mul_one _).symm)
    exact this
  have h2 : ∑ μ, (r μ : ℝ) ^ 2 = 1 := by
    have hnn : 0 ≤ ∑ μ, (r μ : ℝ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have := Real.sq_sqrt hnn
    rw [h1] at this
    linarith
  have h3 : ∑ μ, r μ ^ 2 = 1 := by exact_mod_cast h2
  obtain ⟨a, rfl | rfl⟩ := eq_single_of_sum_sq_eq_one h3
  · exact ⟨a, Or.inl rfl⟩
  · exact ⟨a, Or.inr rfl⟩
variable {σ : FourTorus L m ≃ FourTorus L m}
theorem isSublatticeIsometry_symm (h : IsSublatticeIsometry j σ) : IsSublatticeIsometry j σ.symm := by
  refine ⟨fun x y => ?_, ?_⟩
  · have := h.1 (σ.symm x) (σ.symm y)
    simpa using this.symm
  · conv_lhs => rw [← h.2]
    exact σ.symm_image_image _
theorem mem_sublattice_iff_apply_mem (h : IsSublatticeIsometry j σ) (x : FourTorus L m) :
    x ∈ sublattice L m j ↔ σ x ∈ sublattice L m j := by
  constructor
  · intro hx
    have h' : σ x ∈ σ '' (sublattice L m j : Set (FourTorus L m)) := ⟨x, hx, rfl⟩
    rw [h.2] at h'
    exact h'
  · intro hx
    have h' : σ x ∈ σ '' (sublattice L m j : Set (FourTorus L m)) := by
      rw [h.2]
      exact hx
    obtain ⟨y, hy, e⟩ := h'
    rwa [← σ.injective e]
def sitePerm (h : IsSublatticeIsometry j σ) : Site L m j ≃ Site L m j :=
  σ.subtypeEquiv (mem_sublattice_iff_apply_mem h)
theorem coe_sitePerm (h : IsSublatticeIsometry j σ) (x : Site L m j) :
    ((sitePerm h x : Site L m j) : FourTorus L m) = σ x := rfl
theorem torusEuclidNorm_sitePerm_sub (h : IsSublatticeIsometry j σ) (x y : Site L m j) :
    torusEuclidNorm ((sitePerm h y - sitePerm h x : Site L m j) : FourTorus L m) =
      torusEuclidNorm ((y - x : Site L m j) : FourTorus L m) :=
  h.1 y x
theorem exists_bond_of_norm_eq (hF : AdmissibleMesh L m j N) {x y : Site L m j}
    (hd : torusEuclidNorm ((y - x : Site L m j) : FourTorus L m) = meshSize L j) :
    ∃ b : Bond L m j, b.source = x ∧ b.target = y := by
  obtain ⟨a, h | h⟩ := eq_siteOfCoords_single_of_norm hF hd
  · exact ⟨⟨x, y, a, Or.inl (by rw [h, siteOfCoords_single])⟩, rfl, rfl⟩
  · exact ⟨⟨x, y, a, Or.inr (by rw [h, siteOfCoords_neg, siteOfCoords_single])⟩, rfl, rfl⟩
theorem torusEuclidNorm_neg_unitStep (hF : AdmissibleMesh L m j N) (a : Fin 4) :
    torusEuclidNorm ((-unitStep L m j a : Site L m j) : FourTorus L m) = meshSize L j := by
  rw [AddSubgroup.coe_neg, torusEuclidNorm_neg, torusEuclidNorm_unitStep hF]
theorem torusEuclidNorm_bond (hF : AdmissibleMesh L m j N) (b : Bond L m j) :
    torusEuclidNorm ((b.target - b.source : Site L m j) : FourTorus L m) = meshSize L j := by
  obtain ⟨a, h | h⟩ := b.isNeighbour
  · rw [h, torusEuclidNorm_unitStep hF]
  · rw [h, torusEuclidNorm_neg_unitStep hF]
theorem bondPreimage_endpoints (hF : AdmissibleMesh L m j N) (hσ : IsSublatticeIsometry j σ)
    (b : Bond L m j) :
    (bondPreimage σ b).source = sitePerm (isSublatticeIsometry_symm hσ) b.source ∧
      (bondPreimage σ b).target = sitePerm (isSublatticeIsometry_symm hσ) b.target := by
  have hb : ∃ b' : Bond L m j, (b'.source : FourTorus L m) = σ.symm b.source ∧
      (b'.target : FourTorus L m) = σ.symm b.target := by
    obtain ⟨b', h1, h2⟩ := exists_bond_of_norm_eq hF
      (x := sitePerm (isSublatticeIsometry_symm hσ) b.source)
      (y := sitePerm (isSublatticeIsometry_symm hσ) b.target)
      (by rw [torusEuclidNorm_sitePerm_sub]; exact torusEuclidNorm_bond hF b)
    exact ⟨b', by rw [h1]; rfl, by rw [h2]; rfl⟩
  have hs := hb.choose_spec
  unfold bondPreimage
  rw [dif_pos hb]
  exact ⟨Subtype.ext hs.1, Subtype.ext hs.2⟩
theorem bondPreimage_opposite (hF : AdmissibleMesh L m j N) (hσ : IsSublatticeIsometry j σ)
    (b : Bond L m j) : bondPreimage σ b.opposite = (bondPreimage σ b).opposite :=
  Bond.ext ((bondPreimage_endpoints hF hσ b.opposite).1.trans (bondPreimage_endpoints hF hσ b).2.symm)
    ((bondPreimage_endpoints hF hσ b.opposite).2.trans (bondPreimage_endpoints hF hσ b).1.symm)
theorem bondPreimage_symm_bondPreimage (hF : AdmissibleMesh L m j N) (hσ : IsSublatticeIsometry j σ)
    (b : Bond L m j) : bondPreimage σ.symm (bondPreimage σ b) = b := by
  have hσ' := isSublatticeIsometry_symm hσ
  refine Bond.ext ?_ ?_
  · rw [(bondPreimage_endpoints hF hσ' _).1, (bondPreimage_endpoints hF hσ b).1]
    exact Subtype.ext (by simp [coe_sitePerm])
  · rw [(bondPreimage_endpoints hF hσ' _).2, (bondPreimage_endpoints hF hσ b).2]
    exact Subtype.ext (by simp [coe_sitePerm])
theorem transportGaugeField_mem (hF : AdmissibleMesh L m j N) (hσ : IsSublatticeIsometry j σ)
    {U : Bond L m j → ComplexMatrix2} (hU : U ∈ compactGaugeFields L m j) :
    transportGaugeField σ U ∈ compactGaugeFields L m j :=
  ⟨fun _ _ => hU.1 _ (mem_univ _), fun b _ => by
    change U (bondPreimage σ b.opposite) = (U (bondPreimage σ b))⁻¹
    rw [bondPreimage_opposite hF hσ]
    exact hU.2 _ (mem_univ _)⟩
def linkValue (U : Bond L m j → ComplexMatrix2) (x y : Site L m j) : ComplexMatrix2 :=
  open Classical in
  if h : ∃ b : Bond L m j, b.source = x ∧ b.target = y then U h.choose else 1
theorem linkValue_bond (U : Bond L m j → ComplexMatrix2) (b : Bond L m j) :
    linkValue U b.source b.target = U b := by
  have h : ∃ b' : Bond L m j, b'.source = b.source ∧ b'.target = b.target := ⟨b, rfl, rfl⟩
  unfold linkValue
  rw [dif_pos h]
  congr 1
  exact Bond.ext h.choose_spec.1 h.choose_spec.2
theorem linkValue_of_bond (U : Bond L m j → ComplexMatrix2) {x y : Site L m j} (b : Bond L m j)
    (h₁ : b.source = x) (h₂ : b.target = y) : linkValue U x y = U b := by
  subst h₁ h₂
  exact linkValue_bond U b
theorem inv_eq_star_of_mem {X : ComplexMatrix2} (hX : X ∈ compactGaugeGroup) : X⁻¹ = star X :=
  Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.1 (Matrix.mem_specialUnitaryGroup_iff.1 hX).1)
theorem linkValue_swap {U : Bond L m j → ComplexMatrix2} (hU : U ∈ compactGaugeFields L m j)
    (x y : Site L m j) : linkValue U y x = star (linkValue U x y) := by
  by_cases h : ∃ b : Bond L m j, b.source = x ∧ b.target = y
  · obtain ⟨b, rfl, rfl⟩ := h
    rw [linkValue_bond, linkValue_of_bond U (x := b.target) (y := b.source) b.opposite rfl rfl,
      hU.2 b (mem_univ _)]
    exact inv_eq_star_of_mem (hU.1 b (mem_univ _))
  · have h' : ¬ ∃ b : Bond L m j, b.source = y ∧ b.target = x :=
      fun ⟨b, h₁, h₂⟩ => h ⟨b.opposite, h₂, h₁⟩
    simp [linkValue, h, h']
def squareLoopTrace (U : Bond L m j → ComplexMatrix2) (y₀ y₁ y₂ y₃ : Site L m j) : ℝ :=
  (ComplexMatrix2.fullTrace (linkValue U y₀ y₁ * linkValue U y₁ y₂ * linkValue U y₂ y₃ *
    linkValue U y₃ y₀)).re
theorem squareLoopTrace_rotate (U : Bond L m j → ComplexMatrix2) (y₀ y₁ y₂ y₃ : Site L m j) :
    squareLoopTrace U y₁ y₂ y₃ y₀ = squareLoopTrace U y₀ y₁ y₂ y₃ := by
  have h : ∀ A B C D : ComplexMatrix2, ComplexMatrix2.fullTrace (B * C * D * A) =
      ComplexMatrix2.fullTrace (A * B * C * D) := fun A B C D => by
    simp only [ComplexMatrix2.fullTrace]
    rw [Matrix.trace_mul_comm (B * C * D) A]
    simp only [mul_assoc]
  simp only [squareLoopTrace, h]
theorem squareLoopTrace_reverse {U : Bond L m j → ComplexMatrix2} (hU : U ∈ compactGaugeFields L m j)
    (y₀ y₁ y₂ y₃ : Site L m j) : squareLoopTrace U y₀ y₃ y₂ y₁ = squareLoopTrace U y₀ y₁ y₂ y₃ := by
  unfold squareLoopTrace
  rw [linkValue_swap hU y₃ y₀, linkValue_swap hU y₂ y₃, linkValue_swap hU y₁ y₂,
    linkValue_swap hU y₀ y₁]
  have h : ∀ A B C D : ComplexMatrix2, star D * star C * star B * star A = star (A * B * C * D) :=
    fun A B C D => by simp only [star_mul, mul_assoc]
  rw [h, Matrix.star_eq_conjTranspose, ComplexMatrix2.fullTrace, Matrix.trace_conjTranspose]
  simp
def plaquetteReTrace (U : Bond L m j → ComplexMatrix2) (p : Plaquette L m j) : ℝ :=
  squareLoopTrace U p.origin (p.origin + unitStep L m j p.firstAxis)
    (p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis)
    (p.origin + unitStep L m j p.secondAxis)
theorem add_unitStep_comm_corner (p : Plaquette L m j) :
    p.origin + unitStep L m j p.secondAxis + unitStep L m j p.firstAxis =
      p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis := by abel
theorem plaquetteHolonomy_eq_linkValue (V : Bond L m j → ComplexMatrix2) (p : Plaquette L m j) :
    plaquetteHolonomy V p = linkValue V p.origin (p.origin + unitStep L m j p.firstAxis) *
      linkValue V (p.origin + unitStep L m j p.firstAxis)
        (p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis) *
      linkValue V (p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis)
        (p.origin + unitStep L m j p.secondAxis) *
      linkValue V (p.origin + unitStep L m j p.secondAxis) p.origin := by
  rw [linkValue_of_bond V (x := p.origin) (y := p.origin + unitStep L m j p.firstAxis)
      (Bond.forwardFrom p.origin p.firstAxis) rfl rfl,
    linkValue_of_bond V (x := p.origin + unitStep L m j p.firstAxis)
      (y := p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis)
      (Bond.forwardFrom (p.origin + unitStep L m j p.firstAxis) p.secondAxis) rfl rfl,
    linkValue_of_bond V (x := p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis)
      (y := p.origin + unitStep L m j p.secondAxis)
      (Bond.forwardFrom (p.origin + unitStep L m j p.secondAxis) p.firstAxis).opposite
      (add_unitStep_comm_corner p) rfl,
    linkValue_of_bond V (x := p.origin + unitStep L m j p.secondAxis) (y := p.origin)
      (Bond.forwardFrom p.origin p.secondAxis).opposite rfl rfl]
  simp [plaquetteHolonomy, pathHolonomy, Plaquette.boundaryBonds, mul_assoc]
theorem plaquetteEnergy_eq (V : Bond L m j → ComplexMatrix2) (p : Plaquette L m j) :
    plaquetteCost V p = 1 - (1 / 2) * plaquetteReTrace V p := by
  rw [plaquetteCost, plaquetteHolonomy_eq_linkValue]
  rfl
theorem linkValue_transport (hF : AdmissibleMesh L m j N) (hσ : IsSublatticeIsometry j σ)
    (U : Bond L m j → ComplexMatrix2) {x y : Site L m j} (b : Bond L m j) (h₁ : b.source = x)
    (h₂ : b.target = y) :
    linkValue (transportGaugeField σ U) x y =
      linkValue U (sitePerm (isSublatticeIsometry_symm hσ) x)
        (sitePerm (isSublatticeIsometry_symm hσ) y) := by
  subst h₁ h₂
  rw [linkValue_bond]
  exact (linkValue_of_bond U (bondPreimage σ b) (bondPreimage_endpoints hF hσ b).1
    (bondPreimage_endpoints hF hσ b).2).symm
theorem plaquetteReTrace_transport (hF : AdmissibleMesh L m j N) (hσ : IsSublatticeIsometry j σ)
    (U : Bond L m j → ComplexMatrix2) (p : Plaquette L m j) :
    plaquetteReTrace (transportGaugeField σ U) p =
      squareLoopTrace U (sitePerm (isSublatticeIsometry_symm hσ) p.origin)
        (sitePerm (isSublatticeIsometry_symm hσ) (p.origin + unitStep L m j p.firstAxis))
        (sitePerm (isSublatticeIsometry_symm hσ)
          (p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis))
        (sitePerm (isSublatticeIsometry_symm hσ) (p.origin + unitStep L m j p.secondAxis)) := by
  unfold plaquetteReTrace squareLoopTrace
  rw [linkValue_transport hF hσ U (x := p.origin) (y := p.origin + unitStep L m j p.firstAxis)
      (Bond.forwardFrom p.origin p.firstAxis) rfl rfl,
    linkValue_transport hF hσ U (x := p.origin + unitStep L m j p.firstAxis)
      (y := p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis)
      (Bond.forwardFrom (p.origin + unitStep L m j p.firstAxis) p.secondAxis) rfl rfl,
    linkValue_transport hF hσ U
      (x := p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis)
      (y := p.origin + unitStep L m j p.secondAxis)
      (Bond.forwardFrom (p.origin + unitStep L m j p.secondAxis) p.firstAxis).opposite
      (add_unitStep_comm_corner p) rfl,
    linkValue_transport hF hσ U (x := p.origin + unitStep L m j p.secondAxis) (y := p.origin)
      (Bond.forwardFrom p.origin p.secondAxis).opposite rfl rfl]
def BoundsPlaquette (y₀ y₁ y₂ y₃ : Site L m j) : Prop :=
  ∃ p : Plaquette L m j, p.vertices = {y₀, y₁, y₂, y₃} ∧
    ∀ U ∈ compactGaugeFields L m j, plaquetteReTrace U p = squareLoopTrace U y₀ y₁ y₂ y₃
theorem BoundsPlaquette.of_rotate {y₀ y₁ y₂ y₃ : Site L m j} (h : BoundsPlaquette y₁ y₂ y₃ y₀) :
    BoundsPlaquette y₀ y₁ y₂ y₃ := by
  obtain ⟨p, hc, hq⟩ := h
  refine ⟨p, ?_, fun U hU => (hq U hU).trans (squareLoopTrace_rotate U _ _ _ _)⟩
  rw [hc]
  ext x
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto
theorem BoundsPlaquette.of_reverse {y₀ y₁ y₂ y₃ : Site L m j} (h : BoundsPlaquette y₀ y₃ y₂ y₁) :
    BoundsPlaquette y₀ y₁ y₂ y₃ := by
  obtain ⟨p, hc, hq⟩ := h
  refine ⟨p, ?_, fun U hU => (hq U hU).trans (squareLoopTrace_reverse hU _ _ _ _)⟩
  rw [hc]
  ext x
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto
theorem boundsPlaquette_unitSteps {a b : Fin 4} (hab : a ≠ b) (y : Site L m j) :
    BoundsPlaquette y (y + unitStep L m j a) (y + unitStep L m j a + unitStep L m j b)
      (y + unitStep L m j b) := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨⟨y, a, b, h⟩, rfl, fun _ _ => rfl⟩
  · apply BoundsPlaquette.of_reverse
    have e : y + unitStep L m j a + unitStep L m j b = y + unitStep L m j b + unitStep L m j a := by
      abel
    rw [e]
    exact ⟨⟨y, b, a, h⟩, rfl, fun _ _ => rfl⟩
theorem boundsPlaquette_square {a b : Fin 4} (hab : a ≠ b) (y s t : Site L m j)
    (hs : s = unitStep L m j a ∨ s = -unitStep L m j a)
    (ht : t = unitStep L m j b ∨ t = -unitStep L m j b) :
    BoundsPlaquette y (y + s) (y + s + t) (y + t) := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact boundsPlaquette_unitSteps hab y
  · apply BoundsPlaquette.of_reverse
    apply BoundsPlaquette.of_rotate
    have h := boundsPlaquette_unitSteps hab (y + -unitStep L m j b)
    convert h using 1 <;> abel
  · apply BoundsPlaquette.of_reverse
    apply BoundsPlaquette.of_rotate
    apply BoundsPlaquette.of_rotate
    apply BoundsPlaquette.of_rotate
    have h := boundsPlaquette_unitSteps hab (y + -unitStep L m j a)
    convert h using 1 <;> abel
  · apply BoundsPlaquette.of_rotate
    apply BoundsPlaquette.of_rotate
    have h := boundsPlaquette_unitSteps hab (y + -unitStep L m j a + -unitStep L m j b)
    convert h using 1 <;> abel
def IsSignedBasisVector (w : Fin 4 → ℤ) : Prop := ∃ a, w = Pi.single a 1 ∨ w = -Pi.single a 1
theorem IsSignedBasisVector.sum_sq {w : Fin 4 → ℤ} (h : IsSignedBasisVector w) :
    ∑ μ, w μ ^ 2 = 1 := by
  obtain ⟨a, rfl | rfl⟩ := h
  · rw [Finset.sum_eq_single a] <;> simp +contextual [Pi.single_eq_of_ne]
  · rw [Finset.sum_eq_single a] <;> simp +contextual [Pi.single_eq_of_ne]
theorem IsSignedBasisVector.abs_le {w : Fin 4 → ℤ} (h : IsSignedBasisVector w) (μ : Fin 4) :
    |w μ| ≤ 1 := by
  obtain ⟨a, rfl | rfl⟩ := h
  · exact abs_single_one_le a μ
  · simpa using abs_single_one_le a μ
theorem exists_signedBasisVector_of_norm (h : AdmissibleMesh L m j N) {d : Site L m j}
    (hd : torusEuclidNorm (d : FourTorus L m) = meshSize L j) :
    ∃ w, IsSignedBasisVector w ∧ d = siteOfCoords w := by
  obtain ⟨a, e | e⟩ := eq_siteOfCoords_single_of_norm h hd
  · exact ⟨_, ⟨a, Or.inl rfl⟩, e⟩
  · exact ⟨_, ⟨a, Or.inr rfl⟩, e⟩
theorem sum_sq_eq_two_of_norm (h : AdmissibleMesh L m j N) {w : Fin 4 → ℤ} (hw : ∀ μ, |w μ| ≤ 4)
    (hd : torusEuclidNorm ((siteOfCoords w : Site L m j) : FourTorus L m) =
      meshSize L j * Real.sqrt 2) :
    ∑ μ, w μ ^ 2 = 2 := by
  rw [torusEuclidNorm_siteOfCoords h w hw] at hd
  have h1 := mul_left_cancel₀ h.1.ne' hd
  have h2 : ∑ μ, (w μ : ℝ) ^ 2 = 2 :=
    (Real.sqrt_inj (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)).1 h1
  exact_mod_cast h2
theorem square_eq_of_norms (hF : AdmissibleMesh L m j N) {y₀ y₁ y₂ y₃ : Site L m j}
    (h₀₁ : torusEuclidNorm ((y₁ - y₀ : Site L m j) : FourTorus L m) = meshSize L j)
    (h₁₂ : torusEuclidNorm ((y₂ - y₁ : Site L m j) : FourTorus L m) = meshSize L j)
    (h₂₃ : torusEuclidNorm ((y₃ - y₂ : Site L m j) : FourTorus L m) = meshSize L j)
    (h₃₀ : torusEuclidNorm ((y₀ - y₃ : Site L m j) : FourTorus L m) = meshSize L j)
    (h₀₂ : torusEuclidNorm ((y₂ - y₀ : Site L m j) : FourTorus L m) = meshSize L j * Real.sqrt 2)
    (h₁₃ : torusEuclidNorm ((y₃ - y₁ : Site L m j) : FourTorus L m) = meshSize L j * Real.sqrt 2) :
    ∃ (a b : Fin 4) (s t : Site L m j), a ≠ b ∧
      (s = unitStep L m j a ∨ s = -unitStep L m j a) ∧
      (t = unitStep L m j b ∨ t = -unitStep L m j b) ∧
      y₁ = y₀ + s ∧ y₂ = y₀ + s + t ∧ y₃ = y₀ + t := by
  obtain ⟨w₁, u₁, e₁⟩ := exists_signedBasisVector_of_norm hF h₀₁
  obtain ⟨w₂, u₂, e₂⟩ := exists_signedBasisVector_of_norm hF h₁₂
  obtain ⟨w₃, u₃, e₃⟩ := exists_signedBasisVector_of_norm hF h₂₃
  obtain ⟨w₄, u₄, e₄⟩ := exists_signedBasisVector_of_norm hF h₃₀
  have b₁ := u₁.abs_le
  have b₂ := u₂.abs_le
  have b₃ := u₃.abs_le
  have b₄ := u₄.abs_le
  have d₀₂ : y₂ - y₀ = siteOfCoords (w₁ + w₂) := by
    rw [siteOfCoords_add, ← e₁, ← e₂]
    abel
  have d₁₃ : y₃ - y₁ = siteOfCoords (w₂ + w₃) := by
    rw [siteOfCoords_add, ← e₂, ← e₃]
    abel
  have s₁₂ : ∑ μ, (w₁ + w₂) μ ^ 2 = 2 := by
    refine sum_sq_eq_two_of_norm hF (fun μ => ?_) (d₀₂ ▸ h₀₂)
    have := abs_add_le (w₁ μ) (w₂ μ)
    have := b₁ μ
    have := b₂ μ
    simp only [Pi.add_apply]
    omega
  have s₂₃ : ∑ μ, (w₂ + w₃) μ ^ 2 = 2 := by
    refine sum_sq_eq_two_of_norm hF (fun μ => ?_) (d₁₃ ▸ h₁₃)
    have := abs_add_le (w₂ μ) (w₃ μ)
    have := b₂ μ
    have := b₃ μ
    simp only [Pi.add_apply]
    omega
  have hz : w₁ + w₂ + w₃ + w₄ = 0 := by
    refine coords_eq_zero_of_siteOfCoords_eq_zero hF (L := L) (m := m) (j := j) ?_ (fun μ => ?_)
    · rw [siteOfCoords_add, siteOfCoords_add, siteOfCoords_add, ← e₁, ← e₂, ← e₃, ← e₄]
      abel
    · have hN := hF.2.2
      have h₁ := abs_add_le (w₁ μ + w₂ μ + w₃ μ) (w₄ μ)
      have h₂ := abs_add_le (w₁ μ + w₂ μ) (w₃ μ)
      have h₃ := abs_add_le (w₁ μ) (w₂ μ)
      have := b₁ μ
      have := b₂ μ
      have := b₃ μ
      have := b₄ μ
      simp only [Pi.add_apply]
      omega
  have hz' : ∀ μ, w₄ μ = -(w₁ μ + w₂ μ + w₃ μ) := fun μ => by
    have := congrFun hz μ
    simp only [Pi.add_apply, Pi.zero_apply] at this
    omega
  have q₁ := u₁.sum_sq
  have q₂ := u₂.sum_sq
  have q₃ := u₃.sum_sq
  have q₄ := u₄.sum_sq
  have hs : ∑ μ, (w₁ μ + w₃ μ) ^ 2 = 0 := by
    simp only [hz'] at q₄
    simp only [Fin.sum_univ_four, Pi.add_apply] at *
    linear_combination q₄ - s₁₂ - s₂₃ + q₁ + q₂ + q₃
  have h13 : ∀ μ, w₃ μ = -w₁ μ := fun μ => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 hs μ (Finset.mem_univ μ)
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    omega
  have h24 : ∀ μ, w₄ μ = -w₂ μ := fun μ => by
    have := h13 μ
    have := hz' μ
    omega
  obtain ⟨a, ha⟩ := u₁
  obtain ⟨b, hb⟩ := u₂
  have hab : a ≠ b := by
    rintro rfl
    have hsame : w₂ = w₁ ∨ w₂ = -w₁ := by
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
    rcases hsame with rfl | rfl
    · have h4 : ∑ μ, (w₂ + w₂) μ ^ 2 = 4 * ∑ μ, w₂ μ ^ 2 := by
        simp only [Fin.sum_univ_four, Pi.add_apply]
        ring
      rw [h4, q₁] at s₁₂
      omega
    · simp at s₁₂
  have stepOf : ∀ (w : Fin 4 → ℤ) (c : Fin 4), (w = Pi.single c 1 ∨ w = -Pi.single c 1) →
      ((siteOfCoords w : Site L m j) = unitStep L m j c ∨
        (siteOfCoords w : Site L m j) = -unitStep L m j c) := by
    rintro w c (rfl | rfl)
    · exact Or.inl (siteOfCoords_single c)
    · exact Or.inr (by rw [siteOfCoords_neg, siteOfCoords_single])
  have e₃' : y₃ - y₂ = -siteOfCoords w₁ := by
    rw [e₃, ← siteOfCoords_neg]
    congr 1
    exact funext h13
  have e₄' : y₀ - y₃ = -siteOfCoords w₂ := by
    rw [e₄, ← siteOfCoords_neg]
    congr 1
    exact funext h24
  refine ⟨a, b, siteOfCoords w₁, siteOfCoords w₂, hab, stepOf _ _ ha, stepOf _ _ hb, ?_, ?_, ?_⟩
  · rw [← e₁]
    abel
  · rw [← e₁, ← e₂]
    abel
  · rw [← e₂]
    have : y₃ = y₀ + siteOfCoords w₂ := by
      have := e₄'
      rw [sub_eq_iff_eq_add] at this
      rw [this]
      abel
    rw [this, e₂]
theorem sum_sq_single_add_single {a b : Fin 4} (hab : a ≠ b) :
    ∑ μ, ((Pi.single a 1 + Pi.single b 1 : Fin 4 → ℤ) μ) ^ 2 = 2 := by
  revert a b
  decide
theorem sum_sq_single_sub_single {a b : Fin 4} (hab : a ≠ b) :
    ∑ μ, ((Pi.single b 1 - Pi.single a 1 : Fin 4 → ℤ) μ) ^ 2 = 2 := by
  revert a b
  decide
theorem torusEuclidNorm_of_sum_sq_eq_two (hF : AdmissibleMesh L m j N) {w : Fin 4 → ℤ}
    (hw : ∀ μ, |w μ| ≤ 4) (hs : ∑ μ, w μ ^ 2 = 2) :
    torusEuclidNorm ((siteOfCoords w : Site L m j) : FourTorus L m) = meshSize L j * Real.sqrt 2 := by
  rw [torusEuclidNorm_siteOfCoords hF w hw]
  congr 2
  exact_mod_cast hs
theorem torusEuclidNorm_unitStep_add (hF : AdmissibleMesh L m j N) {a b : Fin 4} (hab : a ≠ b) :
    torusEuclidNorm ((unitStep L m j a + unitStep L m j b : Site L m j) : FourTorus L m) =
      meshSize L j * Real.sqrt 2 := by
  rw [← siteOfCoords_single, ← siteOfCoords_single, ← siteOfCoords_add]
  refine torusEuclidNorm_of_sum_sq_eq_two hF (fun μ => ?_) (sum_sq_single_add_single hab)
  have h₁ := abs_add_le ((Pi.single a 1 : Fin 4 → ℤ) μ) ((Pi.single b 1 : Fin 4 → ℤ) μ)
  have h₂ := abs_single_one_le a μ
  have h₃ := abs_single_one_le b μ
  simp only [Pi.add_apply]
  omega
theorem torusEuclidNorm_unitStep_sub (hF : AdmissibleMesh L m j N) {a b : Fin 4} (hab : a ≠ b) :
    torusEuclidNorm ((unitStep L m j b - unitStep L m j a : Site L m j) : FourTorus L m) =
      meshSize L j * Real.sqrt 2 := by
  rw [← siteOfCoords_single, ← siteOfCoords_single, ← siteOfCoords_sub]
  refine torusEuclidNorm_of_sum_sq_eq_two hF (fun μ => ?_) (sum_sq_single_sub_single hab)
  have h₁ := abs_sub ((Pi.single b 1 : Fin 4 → ℤ) μ) ((Pi.single a 1 : Fin 4 → ℤ) μ)
  have h₂ := abs_single_one_le a μ
  have h₃ := abs_single_one_le b μ
  simp only [Pi.sub_apply]
  omega
theorem exists_plaquette_transport (hF : AdmissibleMesh L m j N) (hσ : IsSublatticeIsometry j σ)
    (p : Plaquette L m j) :
    ∃ p' : Plaquette L m j, p'.vertices = sitePerm (isSublatticeIsometry_symm hσ) '' p.vertices ∧
      ∀ U ∈ compactGaugeFields L m j,
        plaquetteReTrace (transportGaugeField σ U) p = plaquetteReTrace U p' := by
  have hd := torusEuclidNorm_sitePerm_sub (isSublatticeIsometry_symm hσ)
  obtain ⟨a, b, s, t, hab, hs, ht, e₁, e₂, e₃⟩ := square_eq_of_norms hF
    (y₀ := sitePerm (isSublatticeIsometry_symm hσ) p.origin)
    (y₁ := sitePerm (isSublatticeIsometry_symm hσ) (p.origin + unitStep L m j p.firstAxis))
    (y₂ := sitePerm (isSublatticeIsometry_symm hσ)
      (p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis))
    (y₃ := sitePerm (isSublatticeIsometry_symm hσ) (p.origin + unitStep L m j p.secondAxis))
    (by
      rw [hd, show p.origin + unitStep L m j p.firstAxis - p.origin =
        unitStep L m j p.firstAxis by abel]
      exact torusEuclidNorm_unitStep hF _)
    (by
      rw [hd, show p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis -
        (p.origin + unitStep L m j p.firstAxis) = unitStep L m j p.secondAxis by abel]
      exact torusEuclidNorm_unitStep hF _)
    (by
      rw [hd, show p.origin + unitStep L m j p.secondAxis -
        (p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis) =
          -unitStep L m j p.firstAxis by abel]
      exact torusEuclidNorm_neg_unitStep hF _)
    (by
      rw [hd, show p.origin - (p.origin + unitStep L m j p.secondAxis) =
        -unitStep L m j p.secondAxis by abel]
      exact torusEuclidNorm_neg_unitStep hF _)
    (by
      rw [hd, show p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis - p.origin =
        unitStep L m j p.firstAxis + unitStep L m j p.secondAxis by abel]
      exact torusEuclidNorm_unitStep_add hF p.firstAxis_lt_secondAxis.ne)
    (by
      rw [hd, show p.origin + unitStep L m j p.secondAxis -
        (p.origin + unitStep L m j p.firstAxis) =
          unitStep L m j p.secondAxis - unitStep L m j p.firstAxis by abel]
      exact torusEuclidNorm_unitStep_sub hF p.firstAxis_lt_secondAxis.ne)
  have g := boundsPlaquette_square hab (sitePerm (isSublatticeIsometry_symm hσ) p.origin) s t hs ht
  rw [← e₂, ← e₁, ← e₃] at g
  obtain ⟨p', hc, hq⟩ := g
  refine ⟨p', ?_, fun U hU => by rw [plaquetteReTrace_transport hF hσ, hq U hU]⟩
  rw [hc, Plaquette.vertices]
  simp only [image_insert_eq, image_singleton]
theorem siteOfCoords_zero : (siteOfCoords 0 : Site L m j) = 0 := by
  refine Subtype.ext (funext fun μ => ?_)
  simp [siteOfCoords]
theorem exists_coords_of_mem_vertices {p : Plaquette L m j} {c : Site L m j} (h : c ∈ p.vertices) :
    ∃ i k : ℤ, (i = 0 ∨ i = 1) ∧ (k = 0 ∨ k = 1) ∧
      c = p.origin + siteOfCoords (i • Pi.single p.firstAxis 1 + k • Pi.single p.secondAxis 1) := by
  simp only [Plaquette.vertices, mem_insert_iff, mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨0, 0, by simp, by simp, by simp [siteOfCoords_zero]⟩
  · exact ⟨1, 0, by simp, by simp, by simp [siteOfCoords_single]⟩
  · exact ⟨1, 1, by simp, by simp, by simp [siteOfCoords_add, siteOfCoords_single, add_assoc]⟩
  · exact ⟨0, 1, by simp, by simp, by simp [siteOfCoords_single]⟩
theorem sum_single_one (a : Fin 4) : ∑ α, (Pi.single a 1 : Fin 4 → ℤ) α = 1 := by
  revert a
  decide
theorem single_one_bounds (a α : Fin 4) :
    0 ≤ (Pi.single a 1 : Fin 4 → ℤ) α ∧ (Pi.single a 1 : Fin 4 → ℤ) α ≤ 1 := by
  revert a α
  decide
theorem axis_pair_unique : ∀ μ ν μ' ν' : Fin 4, μ < ν → μ' < ν' →
    (∀ α, (Pi.single μ' 1 : Fin 4 → ℤ) α + (Pi.single ν' 1 : Fin 4 → ℤ) α =
      (Pi.single μ 1 : Fin 4 → ℤ) α + (Pi.single ν 1 : Fin 4 → ℤ) α) → μ = μ' ∧ ν = ν' := by
  decide
theorem vertices_injective (hF : AdmissibleMesh L m j N) {p p' : Plaquette L m j}
    (h : p.vertices = p'.vertices) : p = p' := by
  have m₀ : p'.origin ∈ p.vertices := by
    rw [h]
    simp [Plaquette.vertices]
  have m₂ : p'.origin + unitStep L m j p'.firstAxis + unitStep L m j p'.secondAxis ∈ p.vertices := by
    rw [h]
    simp [Plaquette.vertices]
  obtain ⟨i, k, hi, hk, e⟩ := exists_coords_of_mem_vertices m₀
  obtain ⟨i', k', hi', hk', e'⟩ := exists_coords_of_mem_vertices m₂
  have h₂ : (siteOfCoords (i • Pi.single p.firstAxis 1 + k • Pi.single p.secondAxis 1) :
      Site L m j) + unitStep L m j p'.firstAxis + unitStep L m j p'.secondAxis =
      siteOfCoords (i' • Pi.single p.firstAxis 1 + k' • Pi.single p.secondAxis 1) := by
    apply add_left_cancel (a := p.origin)
    rw [← e', ← add_assoc, ← add_assoc, ← e]
  have hz : (siteOfCoords ((i • Pi.single p.firstAxis 1 + k • Pi.single p.secondAxis 1) +
      Pi.single p'.firstAxis 1 + Pi.single p'.secondAxis 1 -
        (i' • Pi.single p.firstAxis 1 + k' • Pi.single p.secondAxis 1)) : Site L m j) = 0 := by
    rw [siteOfCoords_sub, siteOfCoords_add, siteOfCoords_add, siteOfCoords_single,
      siteOfCoords_single, h₂, sub_self]
  have hw := coords_eq_zero_of_siteOfCoords_eq_zero hF hz (fun α => by
    have hN := hF.2.2
    have c₁ := single_one_bounds p.firstAxis α
    have c₂ := single_one_bounds p.secondAxis α
    have c₃ := single_one_bounds p'.firstAxis α
    have c₄ := single_one_bounds p'.secondAxis α
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [abs_lt]
    rcases hi with rfl | rfl <;> rcases hk with rfl | rfl <;> rcases hi' with rfl | rfl <;>
      rcases hk' with rfl | rfl <;> constructor <;> omega)
  have hs := congrArg (fun f : Fin 4 → ℤ => ∑ α, f α) hw
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_single_one,
    Finset.sum_const_zero] at hs
  obtain ⟨rfl, rfl, rfl, rfl⟩ : i = 0 ∧ k = 0 ∧ i' = 1 ∧ k' = 1 := by
    rcases hi with rfl | rfl <;> rcases hk with rfl | rfl <;> rcases hi' with rfl | rfl <;>
      rcases hk' with rfl | rfl <;> omega
  have hc : ∀ α, (Pi.single p'.firstAxis 1 : Fin 4 → ℤ) α +
      (Pi.single p'.secondAxis 1 : Fin 4 → ℤ) α =
      (Pi.single p.firstAxis 1 : Fin 4 → ℤ) α + (Pi.single p.secondAxis 1 : Fin 4 → ℤ) α :=
    fun α => by
      have := congrFun hw α
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      omega
  obtain ⟨f₁, f₂⟩ := axis_pair_unique _ _ _ _ p.firstAxis_lt_secondAxis
    p'.firstAxis_lt_secondAxis hc
  have hb : p'.origin = p.origin := by
    rw [e]
    simp [siteOfCoords_zero]
  exact Plaquette.ext hb.symm f₁ f₂
theorem exists_plaquette_equiv (hF : AdmissibleMesh L m j N) (hσ : IsSublatticeIsometry j σ) :
    ∃ e : Plaquette L m j ≃ Plaquette L m j, ∀ U ∈ compactGaugeFields L m j, ∀ p,
      plaquetteReTrace (transportGaugeField σ U) p = plaquetteReTrace U (e p) := by
  choose φ hφ hφ' using exists_plaquette_transport hF hσ
  choose ψ hψ hψ' using exists_plaquette_transport hF (isSublatticeIsometry_symm hσ)
  have i₁ : (sitePerm (isSublatticeIsometry_symm (isSublatticeIsometry_symm hσ))) ∘
      (sitePerm (isSublatticeIsometry_symm hσ)) = id :=
    funext fun x => Subtype.ext (by simp [coe_sitePerm])
  have i₂ : (sitePerm (isSublatticeIsometry_symm hσ)) ∘
      (sitePerm (isSublatticeIsometry_symm (isSublatticeIsometry_symm hσ))) = id :=
    funext fun x => Subtype.ext (by simp [coe_sitePerm])
  refine ⟨⟨φ, ψ, fun p => vertices_injective hF ?_, fun p => vertices_injective hF ?_⟩,
    fun U hU p => hφ' p U hU⟩
  · rw [hψ, hφ, ← image_comp, i₁, image_id]
  · rw [hφ, hψ, ← image_comp, i₂, image_id]
theorem wilsonAction_transport (hF : AdmissibleMesh L m j N) (hσ : IsSublatticeIsometry j σ)
    {U : Bond L m j → ComplexMatrix2} (hU : U ∈ compactGaugeFields L m j) :
    wilsonAction (transportGaugeField σ U) = wilsonAction U := by
  obtain ⟨e, he⟩ := exists_plaquette_equiv hF hσ
  unfold wilsonAction
  refine (finsum_congr fun p => ?_).trans (finsum_comp_equiv e)
  rw [plaquetteEnergy_eq, plaquetteEnergy_eq, he U hU]
theorem translateBy_isSublatticeIsometry (v : Site L m j) : IsSublatticeIsometry j (translateBy v) := by
  refine ⟨fun x y => ?_, ?_⟩
  · simp [translateBy]
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact add_mem hy v.2
    · intro hx
      exact ⟨x - v, sub_mem hx v.2, by simp [translateBy]⟩
theorem signedCoordinatePerm_isFlatIsometry (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) :
    IsFlatIsometry (signedCoordinatePerm L m π s) := by
  intro x y
  rw [torusEuclidNorm_eq_sqrt_sum, torusEuclidNorm_eq_sqrt_sum]
  congr 1
  have h : ∀ μ, ‖(signedCoordinatePerm L m π s x - signedCoordinatePerm L m π s y) μ‖ ^ 2 =
      ‖(x - y) (π μ)‖ ^ 2 := by
    intro μ
    have e : (signedCoordinatePerm L m π s x - signedCoordinatePerm L m π s y) μ =
        ((s μ : ℤˣ) : ℤ) • (x - y) (π μ) := by
      simp [signedCoordinatePerm, smul_sub]
    rw [e]
    rcases Int.units_eq_one_or (s μ) with h | h
    · simp [h]
    · rw [h]
      simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, norm_neg]
  simp only [h]
  exact Equiv.sum_comp π fun ν => ‖(x - y) ν‖ ^ 2
theorem signedCoordinatePerm_mem_sublattice (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ)
    {x : FourTorus L m} (hx : x ∈ sublattice L m j) :
    signedCoordinatePerm L m π s x ∈ sublattice L m j := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨fun μ => ((s μ : ℤˣ) : ℤ) * n (π μ), fun μ => ?_⟩
  change ((s μ : ℤˣ) : ℤ) • x (π μ) = _
  rw [hn]
  rcases Int.units_eq_one_or (s μ) with h | h <;> simp [h]
theorem isSublatticeIsometry_of_mem_hyperoctahedralGroup {σ : Equiv.Perm (FourTorus L m)}
    (h : σ ∈ hyperoctahedralGroup L m) : IsSublatticeIsometry j σ := by
  obtain ⟨π', s', h'⟩ := (hyperoctahedralGroup L m).inv_mem h
  obtain ⟨π, s, rfl⟩ := h
  refine ⟨signedCoordinatePerm_isFlatIsometry π s, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact signedCoordinatePerm_mem_sublattice π s hy
  · intro hx
    refine ⟨(signedCoordinatePerm L m π s)⁻¹ x, ?_, by simp⟩
    rw [h']
    exact signedCoordinatePerm_mem_sublattice π' s' hx
instance instIsHaarMeasureHaarProb : Measure.IsHaarMeasure ComplexMatrix2.haarProb := by
  unfold ComplexMatrix2.haarProb
  infer_instance
theorem eq_haarProb_of_isMulLeftInvariant (ρ : Measure ComplexMatrix2.specialUnitary)
    [IsProbabilityMeasure ρ] [ρ.IsMulLeftInvariant] : ρ = ComplexMatrix2.haarProb := by
  have hc := Measure.isMulInvariant_eq_smul_of_compactSpace ρ ComplexMatrix2.haarProb
  have hu := congrArg (fun μ : Measure ComplexMatrix2.specialUnitary => μ univ) hc
  simp only [Measure.smul_apply, measure_univ] at hu
  have h1 : Measure.haarScalarFactor ρ ComplexMatrix2.haarProb = 1 := by
    have : ((1 : NNReal) : ENNReal) =
        (Measure.haarScalarFactor ρ ComplexMatrix2.haarProb : ENNReal) := by
      simpa [ENNReal.smul_def] using hu
    exact_mod_cast this.symm
  rw [h1, one_smul] at hc
  exact hc
theorem haarProb_map_mul_right (g : ComplexMatrix2.specialUnitary) :
    Measure.map (· * g) ComplexMatrix2.haarProb = ComplexMatrix2.haarProb := by
  have hm : Measurable fun x : ComplexMatrix2.specialUnitary => x * g :=
    (continuous_mul_const g).measurable
  have : IsProbabilityMeasure (Measure.map (· * g) ComplexMatrix2.haarProb) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  have : (Measure.map (· * g) ComplexMatrix2.haarProb).IsMulLeftInvariant := ⟨fun h => by
    have hl : Measurable fun x : ComplexMatrix2.specialUnitary => h * x :=
      (continuous_const_mul h).measurable
    rw [Measure.map_map hl hm]
    have e : (fun x : ComplexMatrix2.specialUnitary => h * x) ∘ (fun x => x * g) =
        (fun x => x * g) ∘ (fun x => h * x) := funext fun x => (mul_assoc h x g).symm
    rw [e, ← Measure.map_map hm hl, map_mul_left_eq_self]⟩
  exact eq_haarProb_of_isMulLeftInvariant _
theorem haarProb_map_inv : Measure.map Inv.inv ComplexMatrix2.haarProb = ComplexMatrix2.haarProb := by
  have hi : Measurable fun x : ComplexMatrix2.specialUnitary => x⁻¹ := continuous_inv.measurable
  have : IsProbabilityMeasure (Measure.map Inv.inv ComplexMatrix2.haarProb) :=
    Measure.isProbabilityMeasure_map hi.aemeasurable
  have : (Measure.map Inv.inv ComplexMatrix2.haarProb).IsMulLeftInvariant := ⟨fun h => by
    have hl : Measurable fun x : ComplexMatrix2.specialUnitary => h * x :=
      (continuous_const_mul h).measurable
    have hr : Measurable fun x : ComplexMatrix2.specialUnitary => x * h⁻¹ :=
      (continuous_mul_const h⁻¹).measurable
    rw [Measure.map_map hl hi]
    have e : (fun x : ComplexMatrix2.specialUnitary => h * x) ∘ Inv.inv =
        Inv.inv ∘ (fun x => x * h⁻¹) :=
      funext fun x => by simp
    rw [e, ← Measure.map_map hi hr, haarProb_map_mul_right]⟩
  exact eq_haarProb_of_isMulLeftInvariant _
theorem haarPi_map_reindex {ι : Type} [Countable ι] (e : ι ≃ ι)
    (g : ι → ComplexMatrix2.specialUnitary → ComplexMatrix2.specialUnitary)
    (hg : ∀ i, g i = id ∨ g i = Inv.inv) :
    (ComplexMatrix2.haarPi ι).map (fun v i => g i (v (e i))) = ComplexMatrix2.haarPi ι := by
  have hgm : ∀ i, Measurable (g i) := fun i => by
    rcases hg i with h | h <;> rw [h]
    · exact measurable_id
    · exact continuous_inv.measurable
  have hgh : ∀ i, ComplexMatrix2.haarProb.map (g i) = ComplexMatrix2.haarProb := fun i => by
    rcases hg i with h | h <;> rw [h]
    · exact Measure.map_id
    · exact haarProb_map_inv
  have hR : (fun (v : ι → ComplexMatrix2.specialUnitary) i => v (e i)) =
      MeasurableEquiv.piCongrLeft (fun _ : ι => ComplexMatrix2.specialUnitary) e.symm := by
    funext v i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have h₁ : (ComplexMatrix2.haarPi ι).map (fun (v : ι → ComplexMatrix2.specialUnitary) i =>
      v (e i)) = ComplexMatrix2.haarPi ι := by
    rw [hR]
    exact Measure.infinitePi_map_piCongrLeft (μ := fun _ : ι => ComplexMatrix2.haarProb) e.symm
  have hRm : Measurable fun (v : ι → ComplexMatrix2.specialUnitary) i => v (e i) := by fun_prop
  have hGm : Measurable fun (v : ι → ComplexMatrix2.specialUnitary) i => g i (v i) :=
    measurable_pi_iff.2 fun i => (hgm i).comp (measurable_pi_apply i)
  have h₂ : (ComplexMatrix2.haarPi ι).map (fun (v : ι → ComplexMatrix2.specialUnitary) i =>
      g i (v i)) = ComplexMatrix2.haarPi ι := by
    have := Measure.infinitePi_map_pi (μ := fun _ : ι => ComplexMatrix2.haarProb) hgm
    simp only [hgh] at this
    exact this
  have hc : (fun (v : ι → ComplexMatrix2.specialUnitary) i => g i (v (e i))) =
      (fun (v : ι → ComplexMatrix2.specialUnitary) i => g i (v i)) ∘
        (fun (v : ι → ComplexMatrix2.specialUnitary) i => v (e i)) := rfl
  rw [hc, ← Measure.map_map hGm hRm, h₁, h₂]
theorem not_isPositivelyOriented_and_opposite (hF : AdmissibleMesh L m j N) (b : Bond L m j) :
    ¬ (b.IsPositivelyOriented ∧ b.opposite.IsPositivelyOriented) := by
  rintro ⟨⟨a, ha⟩, ⟨c, hc⟩⟩
  have hz : (siteOfCoords (Pi.single a 1 + Pi.single c 1) : Site L m j) = 0 := by
    rw [siteOfCoords_add, siteOfCoords_single, siteOfCoords_single, ← ha, ← hc]
    simp only [Bond.opposite]
    abel
  have hw := coords_eq_zero_of_siteOfCoords_eq_zero hF hz (fun α => by
    have hN := hF.2.2
    have c₁ := single_one_bounds a α
    have c₂ := single_one_bounds c α
    simp only [Pi.add_apply]
    rw [abs_lt]
    constructor <;> omega)
  have := congrFun hw a
  have c₂ := single_one_bounds c a
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at this
  omega
theorem isPositivelyOriented_or_opposite (b : Bond L m j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
theorem opposite_opposite (b : Bond L m j) : b.opposite.opposite = b := Bond.ext rfl rfl
theorem coe_specialUnitary_inv (g : ComplexMatrix2.specialUnitary) :
    ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) = (g : ComplexMatrix2)⁻¹ := by apply _root_.YangMills.Construction.InfiniteLattice.specialUnitary_coe_inv <;> assumption
theorem gaugeFieldOfPositive_mem (hF : AdmissibleMesh L m j N)
    (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) :
    gaugeFieldOfPositive v ∈ compactGaugeFields L m j := by
  classical
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases h : b.IsPositivelyOriented
    · simp only [gaugeFieldOfPositive, dif_pos h]
      exact (v ⟨b, h⟩).2
    · have h' := (isPositivelyOriented_or_opposite b).resolve_left h
      simp only [gaugeFieldOfPositive, dif_neg h, dif_pos h']
      rw [← coe_specialUnitary_inv]
      exact (v ⟨b.opposite, h'⟩)⁻¹.2
  · by_cases h : b.IsPositivelyOriented
    · have h' : ¬ b.opposite.IsPositivelyOriented := fun h' =>
        not_isPositivelyOriented_and_opposite hF b ⟨h, h'⟩
      have h'' : b.opposite.opposite.IsPositivelyOriented := by rwa [opposite_opposite]
      have e : (⟨b.opposite.opposite, h''⟩ : PositivelyOrientedBond L m j) = ⟨b, h⟩ :=
        Subtype.ext (opposite_opposite b)
      simp only [gaugeFieldOfPositive, dif_neg h', dif_pos h'', dif_pos h, e]
    · have h' := (isPositivelyOriented_or_opposite b).resolve_left h
      simp only [gaugeFieldOfPositive, dif_neg h, dif_pos h']
      rw [← coe_specialUnitary_inv, ← coe_specialUnitary_inv, inv_inv]
theorem compactGaugeFields_ext {U U' : Bond L m j → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j) (hU' : U' ∈ compactGaugeFields L m j)
    (h : ∀ b : Bond L m j, b.IsPositivelyOriented → U b = U' b) : U = U' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact h b hb
  · have h' := (isPositivelyOriented_or_opposite b).resolve_left hb
    have e₁ := hU.2 b.opposite (mem_univ _)
    have e₂ := hU'.2 b.opposite (mem_univ _)
    rw [opposite_opposite] at e₁ e₂
    rw [e₁, e₂, h _ h']
theorem exists_positiveBond_reindex (hF : AdmissibleMesh L m j N) (hσ : IsSublatticeIsometry j σ) :
    ∃ (e : PositivelyOrientedBond L m j ≃ PositivelyOrientedBond L m j)
      (g : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary →
        ComplexMatrix2.specialUnitary),
      (∀ b, g b = id ∨ g b = Inv.inv) ∧
      ∀ v, transportGaugeField σ (gaugeFieldOfPositive v) =
        gaugeFieldOfPositive (fun b => g b (v (e b))) := by
  classical
  have hinj : ∀ b b' : Bond L m j, bondPreimage σ b = bondPreimage σ b' → b = b' := by
    intro b b' h
    rw [← bondPreimage_symm_bondPreimage hF hσ b, h, bondPreimage_symm_bondPreimage hF hσ b']
  have hright : ∀ c : Bond L m j, bondPreimage σ (bondPreimage σ.symm c) = c := by
    intro c
    have := bondPreimage_symm_bondPreimage hF (isSublatticeIsometry_symm hσ) c
    simpa using this
  let fold : Bond L m j → PositivelyOrientedBond L m j := fun b =>
    if h : b.IsPositivelyOriented then ⟨b, h⟩
    else ⟨b.opposite, (isPositivelyOriented_or_opposite b).resolve_left h⟩
  have fold_pos : ∀ b (h : b.IsPositivelyOriented), fold b = ⟨b, h⟩ := fun b h => dif_pos h
  have fold_neg : ∀ b (h : ¬ b.IsPositivelyOriented),
      fold b = ⟨b.opposite, (isPositivelyOriented_or_opposite b).resolve_left h⟩ :=
    fun b h => dif_neg h
  let ρ : PositivelyOrientedBond L m j → PositivelyOrientedBond L m j :=
    fun b => fold (bondPreimage σ b.1)
  have hρ : Function.Bijective ρ := by
    constructor
    · rintro ⟨b, hb⟩ ⟨b', hb'⟩ h
      simp only [ρ] at h
      by_cases h₁ : (bondPreimage σ b).IsPositivelyOriented <;>
        by_cases h₂ : (bondPreimage σ b').IsPositivelyOriented
      · rw [fold_pos _ h₁, fold_pos _ h₂] at h
        exact Subtype.ext (hinj _ _ (congrArg Subtype.val h))
      · rw [fold_pos _ h₁, fold_neg _ h₂] at h
        have e := congrArg Subtype.val h
        simp only at e
        rw [← bondPreimage_opposite hF hσ] at e
        have e' := hinj _ _ e
        exact absurd ⟨hb', e' ▸ hb⟩ (not_isPositivelyOriented_and_opposite hF b')
      · rw [fold_neg _ h₁, fold_pos _ h₂] at h
        have e := congrArg Subtype.val h
        simp only at e
        rw [← bondPreimage_opposite hF hσ] at e
        have e' := hinj _ _ e
        exact absurd ⟨hb, e' ▸ hb'⟩ (not_isPositivelyOriented_and_opposite hF b)
      · rw [fold_neg _ h₁, fold_neg _ h₂] at h
        have e := congrArg Subtype.val h
        simp only at e
        rw [← bondPreimage_opposite hF hσ, ← bondPreimage_opposite hF hσ] at e
        have e' := hinj _ _ e
        have e'' : b = b' := by rw [← opposite_opposite b, e', opposite_opposite]
        exact Subtype.ext e''
    · rintro ⟨c, hc⟩
      by_cases hd : (bondPreimage σ.symm c).IsPositivelyOriented
      · refine ⟨⟨_, hd⟩, ?_⟩
        simp only [ρ]
        rw [fold_pos _ (by rw [hright]; exact hc)]
        exact Subtype.ext (hright c)
      · have hd' := (isPositivelyOriented_or_opposite _).resolve_left hd
        refine ⟨⟨_, hd'⟩, ?_⟩
        have hn : ¬ (bondPreimage σ (bondPreimage σ.symm c).opposite).IsPositivelyOriented := by
          rw [bondPreimage_opposite hF hσ, hright]
          exact fun h => not_isPositivelyOriented_and_opposite hF c ⟨hc, h⟩
        simp only [ρ]
        rw [fold_neg _ hn]
        refine Subtype.ext ?_
        simp only
        rw [bondPreimage_opposite hF hσ, hright, opposite_opposite]
  refine ⟨Equiv.ofBijective ρ hρ,
    fun b => if (bondPreimage σ b.1).IsPositivelyOriented then id else Inv.inv,
    fun b => ?_, fun v => ?_⟩
  · by_cases h : (bondPreimage σ b.1).IsPositivelyOriented
    · exact Or.inl (if_pos h)
    · exact Or.inr (if_neg h)
  · refine compactGaugeFields_ext (transportGaugeField_mem hF hσ (gaugeFieldOfPositive_mem hF v))
      (gaugeFieldOfPositive_mem hF _) fun b hb => ?_
    have hR : gaugeFieldOfPositive (fun b : PositivelyOrientedBond L m j =>
        (if (bondPreimage σ b.1).IsPositivelyOriented then id else Inv.inv)
          (v ((Equiv.ofBijective ρ hρ) b))) b =
        (((if (bondPreimage σ b).IsPositivelyOriented then id else Inv.inv)
          (v (ρ ⟨b, hb⟩)) : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := by
      simp only [gaugeFieldOfPositive, dif_pos hb]
      rfl
    rw [hR]
    change gaugeFieldOfPositive v (bondPreimage σ b) = _
    by_cases h : (bondPreimage σ b).IsPositivelyOriented
    · simp only [ρ, if_pos h, fold_pos _ h, gaugeFieldOfPositive, dif_pos h, id]
    · have h' := (isPositivelyOriented_or_opposite _).resolve_left h
      simp only [ρ, if_neg h, fold_neg _ h, gaugeFieldOfPositive, dif_neg h, dif_pos h']
      rw [coe_specialUnitary_inv]
theorem measurable_gaugeFieldOfPositive :
    Measurable (gaugeFieldOfPositive :
      (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) →
        Bond L m j → ComplexMatrix2) := by
  classical
  refine measurable_pi_iff.2 fun b => ?_
  have hval : Measurable fun g : ComplexMatrix2.specialUnitary => (g : ComplexMatrix2) :=
    continuous_subtype_val.measurable
  have hinv : Measurable fun g : ComplexMatrix2.specialUnitary =>
      ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) :=
    hval.comp continuous_inv.measurable
  by_cases h : b.IsPositivelyOriented
  · simp only [gaugeFieldOfPositive, dif_pos h]
    exact hval.comp (measurable_pi_apply _)
  · have h' := (isPositivelyOriented_or_opposite b).resolve_left h
    simp only [gaugeFieldOfPositive, dif_neg h, dif_pos h', ← coe_specialUnitary_inv]
    exact hinv.comp (measurable_pi_apply _)
theorem measurable_transportGaugeField (σ : FourTorus L m ≃ FourTorus L m) :
    Measurable (transportGaugeField (j := j) σ) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _
theorem productHaarMeasure_map_transport (hF : AdmissibleMesh L m j N)
    (hσ : IsSublatticeIsometry j σ) :
    (productHaarMeasure L m j).map (transportGaugeField σ) = productHaarMeasure L m j := by
  obtain ⟨e, g, hg, hv⟩ := exists_positiveBond_reindex hF hσ
  have hgm : ∀ i, Measurable (g i) := fun i => by
    rcases hg i with h | h <;> rw [h]
    · exact measurable_id
    · exact continuous_inv.measurable
  have hΦ : Measurable fun (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) b =>
      g b (v (e b)) :=
    measurable_pi_iff.2 fun i => (hgm i).comp (measurable_pi_apply _)
  unfold productHaarMeasure gaugeFieldHaar
  rw [Measure.map_map (measurable_transportGaugeField σ) measurable_gaugeFieldOfPositive]
  have hc : transportGaugeField σ ∘ gaugeFieldOfPositive =
      (gaugeFieldOfPositive : (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) →
        Bond L m j → ComplexMatrix2) ∘ (fun v b => g b (v (e b))) := funext hv
  rw [hc, ← Measure.map_map measurable_gaugeFieldOfPositive hΦ, haarPi_map_reindex e g hg]
def compactGaugeFieldSet (L m : ℕ) (j : ℤ) : Set (Bond L m j → ComplexMatrix2) :=
  ⋂ b : Bond L m j, {U | U b ∈ compactGaugeGroup ∧ U b.opposite * U b = 1}
theorem compactGaugeFieldSet_subset : compactGaugeFieldSet L m j ⊆ compactGaugeFields L m j := by
  intro U hU
  have h : ∀ b, U b ∈ compactGaugeGroup ∧ U b.opposite * U b = 1 := mem_iInter.1 hU
  exact ⟨fun b _ => (h b).1, fun b _ => (Matrix.inv_eq_left_inv (h b).2).symm⟩
theorem measurableSet_compactGaugeFieldSet : MeasurableSet (compactGaugeFieldSet L m j) := by
  have hclosed : IsClosed (compactGaugeGroup : Set ComplexMatrix2) := by
    have h₁ : IsClosed {A : ComplexMatrix2 | A * star A = 1} :=
      isClosed_eq (continuous_id.mul (Continuous.matrix_conjTranspose continuous_id))
        continuous_const
    have h₂ : IsClosed {A : ComplexMatrix2 | A.det = 1} :=
      isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
    convert h₁.inter h₂ using 1
    ext A
    simp [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  have : SecondCountableTopology ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hone : IsClosed {p : ComplexMatrix2 × ComplexMatrix2 | p.1 * p.2 = 1} :=
    isClosed_eq (continuous_fst.mul continuous_snd) continuous_const
  refine MeasurableSet.iInter fun b => ?_
  refine MeasurableSet.inter ((measurable_pi_apply b) hclosed.measurableSet) ?_
  have hmeas : Measurable fun U : Bond L m j → ComplexMatrix2 => (U b.opposite, U b) :=
    (measurable_pi_apply b.opposite).prodMk (measurable_pi_apply b)
  exact measurableSet_preimage hmeas hone.measurableSet
theorem ae_mem_compactGaugeFields (hF : AdmissibleMesh L m j N) :
    ∀ᵐ U ∂productHaarMeasure L m j, U ∈ compactGaugeFields L m j := by
  have hm : ∀ᵐ U ∂productHaarMeasure L m j, U ∈ compactGaugeFieldSet L m j := by
    unfold productHaarMeasure
    refine (ae_map_iff measurable_gaugeFieldOfPositive.aemeasurable
      measurableSet_compactGaugeFieldSet).2 (ae_of_all _ fun v => ?_)
    have hv := gaugeFieldOfPositive_mem hF v
    refine mem_iInter.2 fun b => ⟨hv.1 b (mem_univ _), ?_⟩
    rw [hv.2 b (mem_univ _)]
    exact Matrix.nonsing_inv_mul _ (by
      have := (Matrix.mem_specialUnitaryGroup_iff.1 (hv.1 b (mem_univ _))).2
      simp [this])
  exact hm.mono fun U hU => compactGaugeFieldSet_subset hU
theorem transport_symm_transport (hF : AdmissibleMesh L m j N) (hσ : IsSublatticeIsometry j σ)
    (U : Bond L m j → ComplexMatrix2) :
    transportGaugeField σ.symm (transportGaugeField σ U) = U := by
  funext b
  change U (bondPreimage σ (bondPreimage σ.symm b)) = U b
  have := bondPreimage_symm_bondPreimage hF (isSublatticeIsometry_symm hσ) b
  rw [Equiv.symm_symm] at this
  rw [this]
def transportMeasurableEquiv (hF : AdmissibleMesh L m j N) (hσ : IsSublatticeIsometry j σ) :
    (Bond L m j → ComplexMatrix2) ≃ᵐ (Bond L m j → ComplexMatrix2) where
  toFun := transportGaugeField σ
  invFun := transportGaugeField σ.symm
  left_inv := transport_symm_transport hF hσ
  right_inv U := by
    have := transport_symm_transport hF (isSublatticeIsometry_symm hσ) U
    rwa [Equiv.symm_symm] at this
  measurable_toFun := measurable_transportGaugeField σ
  measurable_invFun := measurable_transportGaugeField σ.symm
theorem wilsonGibbsMeasure_map_transport {K : ℕ} (hF : AdmissibleMesh L m (K : ℤ) N)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : IsSublatticeIsometry (K : ℤ) σ) (β : ℝ) :
    (wilsonGibbsMeasure L m K β).map (transportGaugeField σ) = wilsonGibbsMeasure L m K β := by
  unfold wilsonGibbsMeasure
  rw [Measure.map_smul]
  congr 1
  have hp : MeasurePreserving (transportMeasurableEquiv hF hσ) (productHaarMeasure L m (K : ℤ))
      (productHaarMeasure L m (K : ℤ)) :=
    ⟨(transportMeasurableEquiv hF hσ).measurable, productHaarMeasure_map_transport hF hσ⟩
  ext s hs
  have hT : Measurable (transportGaugeField (j := (K : ℤ)) σ) := measurable_transportGaugeField σ
  rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs), withDensity_apply _ hs,
    ← hp.setLIntegral_comp_preimage_emb (transportMeasurableEquiv hF hσ).measurableEmbedding
      (fun U => ENNReal.ofReal (boltzmannWeight β U)) s]
  change ∫⁻ a in (transportMeasurableEquiv hF hσ) ⁻¹' s, _ ∂_ = _
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [ae_mem_compactGaugeFields hF] with U hU
  have : wilsonAction (transportMeasurableEquiv hF hσ U) = wilsonAction U :=
    wilsonAction_transport hF hσ hU
  simp only [boltzmannWeight, this]
theorem wilsonGibbsMeasure_isometry_invariant : WilsonMeasureIsometryInvariant := by
  intro L m K β hL hm hK
  have hF := admissibleMesh_of hL hm hK
  refine ⟨fun v => translateBy_isSublatticeIsometry v,
    fun σ h => isSublatticeIsometry_of_mem_hyperoctahedralGroup h, fun σ hσ =>
    ⟨fun b => ⟨?_, ?_⟩, fun U hU => transportGaugeField_mem hF hσ hU,
      wilsonGibbsMeasure_map_transport hF hσ β⟩⟩
  · exact congrArg Subtype.val (bondPreimage_endpoints hF hσ b).1
  · exact congrArg Subtype.val (bondPreimage_endpoints hF hσ b).2
end IsometryInvariance
end PeriodicLattice
end YangMills.Construction

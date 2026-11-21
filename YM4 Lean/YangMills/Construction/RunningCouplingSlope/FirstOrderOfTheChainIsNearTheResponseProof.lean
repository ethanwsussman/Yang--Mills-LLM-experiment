import YangMills.Construction.RunningCouplingSlope.SecondDerivativeOfTheChainIsTheHessianProof
import YangMills.Construction.RunningCouplingSlope.TheChainIsItsFunctionAtTheResponseProof
import YangMills.Construction.RunningCouplingSlope.TheMapsOfTheFirstOrderAreBounded
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FirstVariationNearResponseProof
open YangMills.Construction.Matrices YangMills.Construction.Tower YangMills.Construction.Tower.CriticalBranchResponse
variable {L n k : ℕ}
private theorem exists_orthonormal_coords (hc : PauliCoordsOrthonormal)
    (hp : FaceSums.FacesAndPairings) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {m : ℕ} (hm : m ≤ k) : ∃ (ι : Type) (_ : Fintype ι) (Ψ : edgeFormSpace L n k m ≃ₗ[ℝ] (ι → ℝ)),
      ∀ f g : edgeFormSpace L n k m,
        (edgeFormPairing (f : Edge L n k m → ComplexMatrix2) (g : Edge L n k m → ComplexMatrix2)).re =
        ∑ i, Ψ f i * Ψ g i := by apply _root_.YangMills.SharedProofs.p44870 <;> assumption
private theorem normSq_nonneg (hc : PauliCoordsOrthonormal)
    (hp : FaceSums.FacesAndPairings) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {m : ℕ} (hm : m ≤ k) (f : edgeFormSpace L n k m) :
    0 ≤ (edgeFormPairing (f : Edge L n k m → ComplexMatrix2)
      (f : Edge L n k m → ComplexMatrix2)).re := by
  obtain ⟨ι, _, Ψ, h⟩ := exists_orthonormal_coords hc hp hL hn hm
  rw [h]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
private theorem pairing_smul_right (hc : PauliCoordsOrthonormal)
    (hp : FaceSums.FacesAndPairings) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {m : ℕ} (hm : m ≤ k) (r : ℝ) (f g : edgeFormSpace L n k m) :
    (edgeFormPairing (f : Edge L n k m → ComplexMatrix2)
      ((r • g : edgeFormSpace L n k m) : Edge L n k m → ComplexMatrix2)).re =
      r * (edgeFormPairing (f : Edge L n k m → ComplexMatrix2)
        (g : Edge L n k m → ComplexMatrix2)).re := by
  obtain ⟨ι, _, Ψ, h⟩ := exists_orthonormal_coords hc hp hL hn hm
  rw [h, h, map_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
private theorem normSq_smul (hc : PauliCoordsOrthonormal)
    (hp : FaceSums.FacesAndPairings) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {m : ℕ} (hm : m ≤ k) (r : ℝ) (f : edgeFormSpace L n k m) :
    (edgeFormPairing ((r • f : edgeFormSpace L n k m) : Edge L n k m → ComplexMatrix2)
      ((r • f : edgeFormSpace L n k m) : Edge L n k m → ComplexMatrix2)).re =
      r ^ 2 * (edgeFormPairing (f : Edge L n k m → ComplexMatrix2)
        (f : Edge L n k m → ComplexMatrix2)).re := by
  obtain ⟨ι, _, Ψ, h⟩ := exists_orthonormal_coords hc hp hL hn hm
  rw [h, h, map_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
private theorem pairing_zero_right (hc : PauliCoordsOrthonormal)
    (hp : FaceSums.FacesAndPairings) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {m : ℕ} (hm : m ≤ k) (f : edgeFormSpace L n k m) :
    (edgeFormPairing (f : Edge L n k m → ComplexMatrix2)
      ((0 : edgeFormSpace L n k m) : Edge L n k m → ComplexMatrix2)).re = 0 := by
  obtain ⟨ι, _, Ψ, h⟩ := exists_orthonormal_coords hc hp hL hn hm
  rw [h, map_zero]
  simp
private theorem pairing_le_sqrt_mul_sqrt (hc : PauliCoordsOrthonormal)
    (hp : FaceSums.FacesAndPairings) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {m : ℕ} (hm : m ≤ k) (f g : edgeFormSpace L n k m) :
    (edgeFormPairing (f : Edge L n k m → ComplexMatrix2) (g : Edge L n k m → ComplexMatrix2)).re ≤
      Real.sqrt (edgeFormPairing (f : Edge L n k m → ComplexMatrix2)
          (f : Edge L n k m → ComplexMatrix2)).re *
        Real.sqrt (edgeFormPairing (g : Edge L n k m → ComplexMatrix2)
          (g : Edge L n k m → ComplexMatrix2)).re := by
  obtain ⟨ι, _, Ψ, h⟩ := exists_orthonormal_coords hc hp hL hn hm
  rw [h, h f f, h g g]
  simp only [← sq]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
private theorem levelFormsNormSq_mk (x : edgeFormSpace L n k 0)
    (N : (i : Fin k) → edgeFormSpace L n k ((i : ℕ) + 1)) :
    levelFormsNormSq ((x, N) : LevelForms L n k) =
      (edgeFormPairing (x : Edge L n k 0 → ComplexMatrix2) (x : Edge L n k 0 → ComplexMatrix2)).re +
        ∑ i : Fin k, (edgeFormPairing (N i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)
          (N i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)).re := rfl
private theorem levelFormsNormSq_nonneg (hc : PauliCoordsOrthonormal)
    (hp : FaceSums.FacesAndPairings) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (ξ : LevelForms L n k) : 0 ≤ levelFormsNormSq ξ := by
  obtain ⟨x, N⟩ := ξ
  rw [levelFormsNormSq_mk]
  exact add_nonneg (normSq_nonneg hc hp hL hn (Nat.zero_le _) _)
    (Finset.sum_nonneg fun i _ => normSq_nonneg hc hp hL hn i.2 _)
private theorem normSq_neg (hc : PauliCoordsOrthonormal)
    (hp : FaceSums.FacesAndPairings) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {m : ℕ} (hm : m ≤ k) (f : edgeFormSpace L n k m) :
    (edgeFormPairing ((-f : edgeFormSpace L n k m) : Edge L n k m → ComplexMatrix2)
      ((-f : edgeFormSpace L n k m) : Edge L n k m → ComplexMatrix2)).re =
      (edgeFormPairing (f : Edge L n k m → ComplexMatrix2)
        (f : Edge L n k m → ComplexMatrix2)).re := by
  obtain ⟨ι, _, Ψ, h⟩ := exists_orthonormal_coords hc hp hL hn hm
  rw [h, h, map_neg]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
private theorem curvatureNormSq_response_eq (hm : ResponseMaps.ResponseMapsHold)
    (hr : TorusResponseRelations.statement) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (hn : 0 < n) (B : edgeFormSpace L n k k) :
    backgroundCurvatureNormSq (meshScaledResponse L n k B) =
      (edgeFormPairing (periodicDefect L n k B : Edge L n k k → ComplexMatrix2)
        (B : Edge L n k k → ComplexMatrix2)).re := by apply _root_.YangMills.SharedProofs.p4981 <;> assumption
private theorem curvatureNormSq_nonneg (hp : FaceSums.FacesAndPairings)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (A : edgeFormSpace L n k 0) :
    0 ≤ backgroundCurvatureNormSq A := by
  have hI := (((hp L hL k 0 (Nat.zero_le _)).1 n hn).2.2.2 Set.univ).1
  obtain ⟨c, hc⟩ := hI.2
  let g : Face L n k 0 → ComplexMatrix2 := (formCoboundary L n k A : Face L n k 0 → ComplexMatrix2)
  have hg : ∀ i, g i ∈ ComplexMatrix2.hermitianTraceless :=
    fun i => (formCoboundary L n k A).2 i (Set.mem_univ i)
  have hfin : Finite (Face L n k 0) :=
    Set.finite_univ_iff.mp ((((hp L hL k 0 (Nat.zero_le _)).1 n hn).2.2.2 Set.univ).2.1)
  let f : FaceSums.finSuppLieFields ↥(Set.univ : Set (Face L n k 0)) :=
    ⟨fun p => g p.1, fun p => hg p.1, Set.toFinite _⟩
  have e := hc f f
  have e' : traceFinsumPairing (f : ↥(Set.univ : Set (Face L n k 0)) → ComplexMatrix2)
      (f : ↥(Set.univ : Set (Face L n k 0)) → ComplexMatrix2) = traceFinsumPairing g g := by
    unfold YangMills.Construction.Tower.traceFinsumPairing
    exact finsum_comp_equiv (Equiv.Set.univ (Face L n k 0))
      (f := fun b => ComplexMatrix2.halfTrace (g b * g b))
  rw [e'] at e
  have hre : (traceFinsumPairing g g).re = c.inner f f := by rw [← e]; simp
  change 0 ≤ (traceFinsumPairing g g).re
  rw [hre]
  exact c.re_inner_nonneg f
private theorem le_of_div_le_mul_sqrt {a c r Z G : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hZ : 0 ≤ Z) (hG : G ≤ c * (Z / a ^ 2)) (h : Z / a ≤ r * Real.sqrt G) : Z ≤ c * r ^ 2 := by
  set y := Real.sqrt Z with hy
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y * y = Z := Real.mul_self_sqrt hZ
  set q := Real.sqrt c with hq
  have hq2 : q * q = c := Real.mul_self_sqrt hc
  have h1 : Real.sqrt G ≤ q * y / a := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc G ≤ c * (Z / a ^ 2) := hG
      _ = (q * y / a) ^ 2 := by rw [← hq2, ← hy2]; field_simp
  have h2 : Z / a ≤ r * (q * y / a) := h.trans (mul_le_mul_of_nonneg_left h1 hr)
  have h3 : Z ≤ r * q * y := by
    have := mul_le_mul_of_nonneg_right h2 ha.le
    have e1 : Z / a * a = Z := by field_simp
    have e2 : r * (q * y / a) * a = r * q * y := by field_simp
    rwa [e1, e2] at this
  have h4 : y ≤ r * q := by
    by_contra hcon
    rw [not_le] at hcon
    have hypos : 0 < y := lt_of_le_of_lt (by positivity) hcon
    nlinarith
  calc Z = y * y := hy2.symm
    _ ≤ (r * q) * (r * q) := mul_le_mul h4 h4 hy0 (by positivity)
    _ = c * r ^ 2 := by rw [← hq2]; ring
private theorem le_of_le_mul_sqrt_self {c x S : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hS : 0 ≤ S)
    (h : S ≤ x * Real.sqrt (c * S)) : S ≤ c * x ^ 2 := by
  have h1 := le_of_div_le_mul_sqrt (a := 1) (c := c) (r := x) (Z := S) (G := c * S) one_pos hc hx hS
    (by simp) (by simpa using h)
  exact h1
private theorem sum_le_of_chain {a c R Z Gq Hq Vq Mq S : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hR : 0 ≤ R)
    (hZ : Z ≤ c * R) (hGq : Gq ≤ c * (Z / a ^ 2)) (hVq : Vq ≤ c * Gq) (hHq : Hq ≤ c * Gq)
    (hMq : Mq ≤ 2 * R + 2 * Vq) (hS : S ≤ c * Mq) :
    Hq + Z / a ^ 2 + S + Mq ≤
      (c ^ 3 / a ^ 2 + c / a ^ 2 + (c + 1) * (2 + 2 * (c ^ 3 / a ^ 2))) * R := by
  have ha2 : 0 < a ^ 2 := by positivity
  set w := R / a ^ 2 with hw
  have hRw : R = w * a ^ 2 := by rw [hw]; field_simp
  have h1 : Z / a ^ 2 ≤ c * w := by
    rw [hw, div_le_iff₀ ha2]
    calc Z ≤ c * R := hZ
      _ = _ := by field_simp
  have h2 : Gq ≤ c ^ 2 * w := by
    calc Gq ≤ c * (Z / a ^ 2) := hGq
      _ ≤ c * (c * w) := mul_le_mul_of_nonneg_left h1 hc
      _ = _ := by ring
  have h3 : Vq ≤ c ^ 3 * w := by
    calc Vq ≤ c * Gq := hVq
      _ ≤ c * (c ^ 2 * w) := mul_le_mul_of_nonneg_left h2 hc
      _ = _ := by ring
  have h4 : Hq ≤ c ^ 3 * w := by
    calc Hq ≤ c * Gq := hHq
      _ ≤ c * (c ^ 2 * w) := mul_le_mul_of_nonneg_left h2 hc
      _ = _ := by ring
  have h5 : Mq ≤ 2 * R + 2 * (c ^ 3 * w) := by linarith
  have h6 : S ≤ c * (2 * R + 2 * (c ^ 3 * w)) :=
    hS.trans (mul_le_mul_of_nonneg_left h5 hc)
  have e : (c ^ 3 / a ^ 2 + c / a ^ 2 + (c + 1) * (2 + 2 * (c ^ 3 / a ^ 2))) * R =
      c ^ 3 * w + c * w + (c + 1) * (2 * R + 2 * (c ^ 3 * w)) := by
    rw [hw]
    field_simp
  rw [e]
  nlinarith
theorem firstVariationNearResponse_holds (hF : MinimizerFirstVariation)
    (hB : FirstVariationMapsBounded) (hc : PauliCoordsOrthonormal)
    (hm : ResponseMaps.ResponseMapsHold)
    (hr : TorusResponseRelations.statement) (hp : FaceSums.FacesAndPairings) :
    FirstVariationNearResponse := by
  intro a ha L hLs k hk
  obtain ⟨c, hc0, hb⟩ := hB L hLs k hk
  refine ⟨c ^ 3 / a ^ 2 + c / a ^ 2 + (c + 1) * (2 + 2 * (c ^ 3 / a ^ 2)), by positivity, ?_⟩
  filter_upwards [hb, eventually_gt_atTop 0] with n hbn hn B t ht
  obtain ⟨hT, hG, hlin, hbd⟩ := hbn
  obtain ⟨hJ, hN, G, l, hGv, hμ, hA⟩ := (hF a ha L hLs k n hk hn B).2 t ht
  obtain ⟨hlinν, hlinh⟩ := hlin B G
  set μ := t.2.2 with hμdef
  set Tμ := linearConstraintAdjoint L n k μ with hTμ
  set ν₀ := periodicDefect L n k B with hν₀
  set νG := periodicDefect L n k G with hνG
  have hμ' : μ = ν₀ - νG := by
    apply Subtype.ext
    rw [hμ, hlinν]
  let Z : ℝ := ∑ i : Fin k, (edgeFormPairing (Tμ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)
    (Tμ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)).re
  have hlev : ∀ i : Fin k, (i : ℕ) + 1 ≤ k := fun i => i.2
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun i _ => normSq_nonneg hc hp hLs hn (hlev i) _
  let ξ₀ : LevelForms L n k := (0, t.1.2)
  have hsq0 : levelFormsNormSq ξ₀ = Z / a ^ 2 := by
    change levelFormsNormSq ((0, t.1.2) : LevelForms L n k) = _
    rw [levelFormsNormSq_mk, pairing_zero_right hc hp hLs hn (Nat.zero_le _), zero_add]
    have e : ∀ i : Fin k, (edgeFormPairing (t.1.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)
        (t.1.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)).re =
        (a⁻¹) ^ 2 * (edgeFormPairing (Tμ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)
          (Tμ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)).re := by
      intro i
      rw [hN i]
      exact normSq_smul hc hp hLs hn (hlev i) _ _
    simp only [e]
    rw [← Finset.mul_sum]
    change (a⁻¹) ^ 2 * Z = Z / a ^ 2
    field_simp
  have hpair0 : (edgeFormPairing (μ : Edge L n k k → ComplexMatrix2)
      (G : Edge L n k k → ComplexMatrix2)).re = Z / a := by
    have h1 := hT μ ξ₀
    have h2 : linearChain ξ₀ k = (G : Edge L n k k → ComplexMatrix2) := hGv.symm
    rw [h2] at h1
    rw [← h1]
    change (edgeFormPairing (Tμ.1 : Edge L n k 0 → ComplexMatrix2)
        ((0 : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2)).re +
      ∑ i : Fin k, (edgeFormPairing (Tμ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)
        (t.1.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)).re = _
    rw [pairing_zero_right hc hp hLs hn (Nat.zero_le _), zero_add]
    have e : ∀ i : Fin k, (edgeFormPairing (Tμ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)
        (t.1.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)).re =
        a⁻¹ * (edgeFormPairing (Tμ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)
          (Tμ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)).re := by
      intro i
      rw [hN i]
      exact pairing_smul_right hc hp hLs hn (hlev i) _ _ _
    simp only [e]
    rw [← Finset.mul_sum]
    change a⁻¹ * Z = Z / a
    field_simp
  obtain ⟨ι, _, Ψ, hΨ⟩ := exists_orthonormal_coords (k := k) hc hp hLs hn le_rfl
  have hcur : 0 ≤ (edgeFormPairing (νG : Edge L n k k → ComplexMatrix2)
      (G : Edge L n k k → ComplexMatrix2)).re := by
    rw [← curvatureNormSq_response_eq hm hr hLs hk hn G]
    exact curvatureNormSq_nonneg hp hLs hn _
  have hsplit : (edgeFormPairing (μ : Edge L n k k → ComplexMatrix2)
      (G : Edge L n k k → ComplexMatrix2)).re =
      (edgeFormPairing (ν₀ : Edge L n k k → ComplexMatrix2) (G : Edge L n k k → ComplexMatrix2)).re -
        (edgeFormPairing (νG : Edge L n k k → ComplexMatrix2)
          (G : Edge L n k k → ComplexMatrix2)).re := by
    rw [hΨ, hΨ, hΨ, hμ', map_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply]
    ring
  have hcs := pairing_le_sqrt_mul_sqrt hc hp hLs hn (le_refl k) ν₀ G
  have hZa : Z / a ≤ Real.sqrt (topFormNormSq ν₀) * Real.sqrt (topFormNormSq G) := by
    have : Z / a ≤ (edgeFormPairing (ν₀ : Edge L n k k → ComplexMatrix2)
        (G : Edge L n k k → ComplexMatrix2)).re := by
      linarith
    exact this.trans hcs
  obtain ⟨G₂, hG₂, hG₂b⟩ := hG ξ₀
  have hGG : G₂ = G := Subtype.ext (hG₂.trans hGv.symm)
  rw [hGG, hsq0] at hG₂b
  have hR0 : 0 ≤ topFormNormSq ν₀ := normSq_nonneg hc hp hLs hn (le_refl k) ν₀
  have hZb := le_of_div_le_mul_sqrt ha hc0 (Real.sqrt_nonneg _) hZ0 hG₂b hZa
  rw [Real.sq_sqrt hR0] at hZb
  have hMq : topFormNormSq μ ≤ 2 * topFormNormSq ν₀ + 2 * topFormNormSq νG := by
    simp only [topFormNormSq]
    rw [hΨ, hΨ, hΨ, hμ', map_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Pi.sub_apply]
    nlinarith [sq_nonneg (Ψ ν₀ i + Ψ νG i)]
  have hM0 : 0 ≤ topFormNormSq μ := normSq_nonneg hc hp hLs hn (le_refl k) μ
  obtain ⟨G₃, hG₃, hG₃b⟩ := hG Tμ
  have hS0 := levelFormsNormSq_nonneg hc hp hLs hn Tμ
  have hSeq : levelFormsNormSq Tμ = (edgeFormPairing (μ : Edge L n k k → ComplexMatrix2)
      (G₃ : Edge L n k k → ComplexMatrix2)).re := by
    have h1 := hT μ Tμ
    rw [← hG₃] at h1
    exact h1
  have hSle : levelFormsNormSq Tμ ≤
      Real.sqrt (topFormNormSq μ) * Real.sqrt (c * levelFormsNormSq Tμ) := by
    rw [hSeq]
    refine (pairing_le_sqrt_mul_sqrt hc hp hLs hn (le_refl k) μ G₃).trans ?_
    rw [← hSeq]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hG₃b) (Real.sqrt_nonneg _)
  have hSb := le_of_le_mul_sqrt_self hc0 (Real.sqrt_nonneg _) hS0 hSle
  rw [Real.sq_sqrt hM0] at hSb
  let A : edgeFormSpace L n k 0 := t.1.1 - (meshScaledResponse L n k B - meshScaledResponse L n k G)
  have hAv : (A : Edge L n k 0 → ComplexMatrix2) =
      vertexCoboundary (l : Vertex L n k 0 → ComplexMatrix2) := by
    have h1 : (t.1.1 : Edge L n k 0 → ComplexMatrix2) =
        ((meshScaledResponse L n k B - meshScaledResponse L n k G : edgeFormSpace L n k 0) :
          Edge L n k 0 → ComplexMatrix2) + vertexCoboundary (l : Vertex L n k 0 → ComplexMatrix2) := by
      rw [hA, hlinh]
    change (t.1.1 : Edge L n k 0 → ComplexMatrix2) -
      ((meshScaledResponse L n k B - meshScaledResponse L n k G : edgeFormSpace L n k 0) :
        Edge L n k 0 → ComplexMatrix2) = _
    rw [h1]
    abel
  refine ⟨l, A, ((-meshScaledResponse L n k G, t.1.2), Tμ, μ), hAv, ?_, ?_⟩
  · refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
    · change t.1.1 = meshScaledResponse L n k B + A + -meshScaledResponse L n k G
      simp only [A]
      abel
    · change t.1.2 = 0 + 0 + t.1.2
      simp
    · change t.2.1 = 0 + 0 + Tμ
      simp [hJ, hTμ, hμdef]
    · change t.2.2 = 0 + 0 + μ
      simp [hμdef]
  · have hsum : tripleNormSq (((-meshScaledResponse L n k G, t.1.2), Tμ, μ) : LevelTriple L n k) =
        levelFormsNormSq ((meshScaledResponse L n k G, 0) : LevelForms L n k) + Z / a ^ 2 +
          levelFormsNormSq Tμ + topFormNormSq μ := by
      change levelFormsNormSq ((-meshScaledResponse L n k G, t.1.2) : LevelForms L n k) +
        levelFormsNormSq Tμ + topFormNormSq μ = _
      rw [← hsq0]
      change levelFormsNormSq ((-meshScaledResponse L n k G, t.1.2) : LevelForms L n k) +
        levelFormsNormSq Tμ + topFormNormSq μ =
        levelFormsNormSq ((meshScaledResponse L n k G, 0) : LevelForms L n k) +
          levelFormsNormSq ((0, t.1.2) : LevelForms L n k) + levelFormsNormSq Tμ + topFormNormSq μ
      have hz : ∑ i : Fin k, (edgeFormPairing
          (((0 : (i : Fin k) → edgeFormSpace L n k ((i : ℕ) + 1)) i :
            edgeFormSpace L n k ((i : ℕ) + 1)) : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)
          (((0 : (i : Fin k) → edgeFormSpace L n k ((i : ℕ) + 1)) i :
            edgeFormSpace L n k ((i : ℕ) + 1)) : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)).re = 0 :=
        Finset.sum_eq_zero fun i _ => pairing_zero_right hc hp hLs hn (hlev i) _
      have h1 : levelFormsNormSq ((-meshScaledResponse L n k G, t.1.2) : LevelForms L n k) =
          (edgeFormPairing (meshScaledResponse L n k G : Edge L n k 0 → ComplexMatrix2)
            (meshScaledResponse L n k G : Edge L n k 0 → ComplexMatrix2)).re +
            ∑ i : Fin k, (edgeFormPairing (t.1.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)
              (t.1.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)).re := by
        rw [levelFormsNormSq_mk, normSq_neg hc hp hLs hn (Nat.zero_le _)]
      have h2 : levelFormsNormSq ((meshScaledResponse L n k G, 0) : LevelForms L n k) =
          (edgeFormPairing (meshScaledResponse L n k G : Edge L n k 0 → ComplexMatrix2)
            (meshScaledResponse L n k G : Edge L n k 0 → ComplexMatrix2)).re := by
        rw [levelFormsNormSq_mk, hz, add_zero]
      have h3 : levelFormsNormSq ((0, t.1.2) : LevelForms L n k) =
          ∑ i : Fin k, (edgeFormPairing (t.1.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)
            (t.1.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)).re := by
        rw [levelFormsNormSq_mk, pairing_zero_right hc hp hLs hn (Nat.zero_le _), zero_add]
      rw [h1, h2, h3]
    rw [hsum]
    exact sum_le_of_chain ha hc0 hR0 hZb hG₂b (hbd G).1 (hbd G).2 hMq hSb
end YangMills.Construction.RunningCouplingSlope.FirstVariationNearResponseProof
end

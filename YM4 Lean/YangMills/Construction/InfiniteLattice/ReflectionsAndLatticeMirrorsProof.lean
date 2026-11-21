import YangMills.Construction.InfiniteLattice.DataOfADiagonalPictureProof
import YangMills.Construction.InfiniteLattice.ExpansionsMeetTheConditionsOfTheReconstructionProof
import YangMills.Construction.InfiniteLattice.LatticeMirrorsAndTwoFormsOfReflectionPositivityProof
import YangMills.Construction.InfiniteLattice.ReconstructionAtALatticeMirrorProof
import YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
import YangMills.Construction.InfiniteLattice.RulesForObservablesIsometriesAndMirrorsProof
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction.LatticeConventions.MirrorReflections
open YangMills.Construction.InfiniteLattice (LatticeMirror ReflectionClass latticeSubgroup)
theorem euclidDot_comm (u v : Point) : euclidDot u v = euclidDot v u := by apply _root_.YangMills.Construction.LatticeConventions.ObservableRules.euclidDot_comm <;> assumption
theorem euclidDot_add_left (u v x : Point) :
    euclidDot (u + v) x = euclidDot u x + euclidDot v x := by apply _root_.YangMills.Construction.LatticeConventions.LatticeMirrorsAndReflectionPositivity.euclidDot_add_left <;> assumption
theorem euclidDot_sub_left (u v x : Point) :
    euclidDot (u - v) x = euclidDot u x - euclidDot v x := by apply _root_.YangMills.Construction.LatticeConventions.MirrorExpansionsProof.euclidDot_sub_left <;> assumption
theorem euclidDot_neg_left (u x : Point) : euclidDot (-u) x = -euclidDot u x := by
  simp [euclidDot]
theorem euclidDot_smul_left (t : ℝ) (u x : Point) : euclidDot (t • u) x = t * euclidDot u x := by apply _root_.YangMills.Construction.LatticeConventions.ObservableRules.euclidDot_smul_left <;> assumption
theorem euclidDot_add_right (x u v : Point) :
    euclidDot x (u + v) = euclidDot x u + euclidDot x v := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.euclidDot_add <;> assumption
theorem euclidDot_sub_right (x u v : Point) :
    euclidDot x (u - v) = euclidDot x u - euclidDot x v := by apply _root_.YangMills.Construction.LatticeConventions.ObservableRules.euclidDot_sub_right <;> assumption
theorem euclidDot_neg_right (x u : Point) : euclidDot x (-u) = -euclidDot x u := by
  rw [euclidDot_comm, euclidDot_neg_left, euclidDot_comm]
theorem euclidDot_smul_right (t : ℝ) (x u : Point) : euclidDot x (t • u) = t * euclidDot x u := by apply _root_.YangMills.Construction.LatticeConventions.MirrorExpansionsProof.euclidDot_smul_right <;> assumption
theorem basisVector_self (μ : Direction) : basisVector μ μ = 1 := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.basisVector_apply_self <;> assumption
theorem basisVector_of_ne {μ ν : Direction} (h : ν ≠ μ) : basisVector μ ν = 0 := by
  simp [basisVector, h]
theorem euclidDot_basisVector_left (μ : Direction) (x : Point) :
    euclidDot (basisVector μ) x = x μ := by
  simp [euclidDot, basisVector, Pi.single_apply]
theorem euclidDot_basisVector_self (μ : Direction) :
    euclidDot (basisVector μ) (basisVector μ) = 1 := by
  rw [euclidDot_basisVector_left, basisVector_self]
theorem euclidDot_self_basis_add {μ lam : Direction} (h : μ ≠ lam) :
    euclidDot (basisVector μ + basisVector lam) (basisVector μ + basisVector lam) = 2 := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.euclidDot_self_basis_add <;> assumption
theorem euclidDot_self_basis_sub {μ lam : Direction} (h : μ ≠ lam) :
    euclidDot (basisVector μ - basisVector lam) (basisVector μ - basisVector lam) = 2 := by apply _root_.YangMills.Construction.LatticeConventions.MirrorExpansionsProof.euclidDot_sub_basis_self <;> assumption
theorem euclidNorm_sq (x : Point) : euclidNorm x ^ 2 = euclidDot x x := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.euclidNorm_sq_eq_selfDot <;> assumption
theorem normal_trichotomy (Q : NormalHyperplane) :
    (∃ μ, Q.normal = basisVector μ) ∨
      (∃ μ lam, μ ≠ lam ∧ Q.normal = basisVector μ + basisVector lam) ∨
      ∃ μ lam, μ ≠ lam ∧ Q.normal = basisVector μ - basisVector lam := by
  rcases Q.normal_valid with ⟨μ, h⟩ | ⟨μ, lam, hne, h | h⟩
  · exact Or.inl ⟨μ, h⟩
  · exact Or.inr (Or.inl ⟨μ, lam, hne, h⟩)
  · exact Or.inr (Or.inr ⟨μ, lam, hne, h⟩)
theorem euclidDot_normal_self_ne_zero (Q : NormalHyperplane) : euclidDot Q.normal Q.normal ≠ 0 := by apply _root_.YangMills.Construction.LatticeConventions.ObservableRules.euclidDot_normal_self_ne_zero <;> assumption
theorem not_axial_and_faceDiagonal {n : Point} (h : IsAxialNormal n)
    (h' : IsFaceDiagonalNormal n) : False := by
  obtain ⟨μ, h⟩ := h
  have h1 : euclidDot n n = 1 := by rw [h, euclidDot_basisVector_self]
  obtain ⟨ν, lam, hne, h' | h'⟩ := h'
  · rw [h', euclidDot_self_basis_add hne] at h1; norm_num at h1
  · rw [h', euclidDot_self_basis_sub hne] at h1; norm_num at h1
theorem isLatticeMirror_iff_of_axial {Q : NormalHyperplane} {a : ℝ}
    (h : IsAxialNormal Q.normal) :
    Q.IsLatticeMirror a ↔ ∃ q : ℤ, Q.level = (q : ℝ) * (a / 2) :=
  ⟨fun hQ => hQ.1 h, fun hq => ⟨fun _ => hq, fun h' => (not_axial_and_faceDiagonal h h').elim⟩⟩
theorem isLatticeMirror_iff_of_faceDiagonal {Q : NormalHyperplane} {a : ℝ}
    (h : IsFaceDiagonalNormal Q.normal) :
    Q.IsLatticeMirror a ↔ ∃ q : ℤ, Q.level = (q : ℝ) * a :=
  ⟨fun hQ => hQ.2 h, fun hq => ⟨fun h' => (not_axial_and_faceDiagonal h' h).elim, fun _ => hq⟩⟩
theorem normal_apply_trichotomy (Q : NormalHyperplane) (κ : Direction) :
    Q.normal κ = 0 ∨ Q.normal κ = 1 ∨ Q.normal κ = -1 := by
  rcases normal_trichotomy Q with ⟨μ, h⟩ | ⟨μ, lam, hne, h⟩ | ⟨μ, lam, hne, h⟩ <;> rw [h]
  · by_cases h1 : κ = μ
    · subst h1; simp [basisVector_self]
    · simp [basisVector_of_ne h1]
  · by_cases h1 : κ = μ
    · subst h1; simp [basisVector_self, basisVector_of_ne hne]
    · by_cases h2 : κ = lam
      · subst h2; simp [basisVector_self, basisVector_of_ne h1]
      · simp [basisVector_of_ne h1, basisVector_of_ne h2]
  · by_cases h1 : κ = μ
    · subst h1; simp [basisVector_self, basisVector_of_ne hne]
    · by_cases h2 : κ = lam
      · subst h2; simp [basisVector_self, basisVector_of_ne h1]
      · simp [basisVector_of_ne h1, basisVector_of_ne h2]
theorem exists_normal_apply_eq_one (Q : NormalHyperplane) : ∃ κ, Q.normal κ = 1 := by
  rcases normal_trichotomy Q with ⟨μ, h⟩ | ⟨μ, lam, hne, h⟩ | ⟨μ, lam, hne, h⟩ <;> rw [h] <;>
    refine ⟨μ, ?_⟩
  · exact basisVector_self μ
  · simp [basisVector_self, basisVector_of_ne hne]
  · simp [basisVector_self, basisVector_of_ne hne]
theorem basisVector_nonneg (μ κ : Direction) : 0 ≤ basisVector μ κ := by
  by_cases h : κ = μ
  · subst h; rw [basisVector_self]; norm_num
  · rw [basisVector_of_ne h]
theorem reflect_apply (Q : NormalHyperplane) (x : Point) :
    Q.reflect x =
      x - (2 * (euclidDot Q.normal x - Q.level) / euclidDot Q.normal Q.normal) • Q.normal := by
  simp only [NormalHyperplane.reflect, euclidNorm_sq]
theorem reflect_apply_coord (Q : NormalHyperplane) (x : Point) (ν : Direction) :
    Q.reflect x ν =
      x ν - (2 * (euclidDot Q.normal x - Q.level) / euclidDot Q.normal Q.normal) * Q.normal ν := by
  rw [reflect_apply]
  rfl
theorem reflectionLinear_apply (Q : NormalHyperplane) (w : Point) :
    Q.reflectionLinear w =
      w - (2 * (euclidDot Q.normal Q.normal)⁻¹ * euclidDot Q.normal w) • Q.normal := by
  rw [← euclidNorm_sq]
  rfl
theorem euclidDot_normal_reflect (Q : NormalHyperplane) (x : Point) :
    euclidDot Q.normal (Q.reflect x) = 2 * Q.level - euclidDot Q.normal x := by
  have hN := euclidDot_normal_self_ne_zero Q
  rw [reflect_apply, euclidDot_sub_right, euclidDot_smul_right]
  field_simp
  ring
theorem reflect_reflect (Q : NormalHyperplane) (x : Point) :
    Q.reflect (Q.reflect x) = x := by
  have hN := euclidDot_normal_self_ne_zero Q
  have h := euclidDot_normal_reflect Q x
  rw [reflect_apply Q (Q.reflect x), h]
  nth_rewrite 1 [reflect_apply Q x]
  rw [sub_sub, ← add_smul]
  have : 2 * (euclidDot Q.normal x - Q.level) / euclidDot Q.normal Q.normal +
      2 * (2 * Q.level - euclidDot Q.normal x - Q.level) / euclidDot Q.normal Q.normal = 0 := by
    field_simp
    ring
  rw [this]
  simp
theorem reflect_add (Q : NormalHyperplane) (x v : Point) :
    Q.reflect (x + v) = Q.reflect x + Q.reflectionLinear v := by
  have hN := euclidDot_normal_self_ne_zero Q
  rw [reflect_apply, reflect_apply, reflectionLinear_apply, euclidDot_add_right]
  have : 2 * (euclidDot Q.normal x + euclidDot Q.normal v - Q.level) / euclidDot Q.normal Q.normal =
      2 * (euclidDot Q.normal x - Q.level) / euclidDot Q.normal Q.normal +
        2 * (euclidDot Q.normal Q.normal)⁻¹ * euclidDot Q.normal v := by
    field_simp
    ring
  rw [this, add_smul]
  abel
theorem euclidDot_reflectionLinear (Q : NormalHyperplane) (w : Point) :
    euclidDot (Q.reflectionLinear w) (Q.reflectionLinear w) = euclidDot w w := by
  have hN := euclidDot_normal_self_ne_zero Q
  rw [reflectionLinear_apply]
  simp only [euclidDot_sub_left, euclidDot_sub_right, euclidDot_smul_left, euclidDot_smul_right,
    euclidDot_comm w Q.normal]
  field_simp
  ring
theorem euclidNorm_reflect_sub (Q : NormalHyperplane) (x y : Point) :
    euclidNorm (Q.reflect x - Q.reflect y) = euclidNorm (x - y) := by
  have h : Q.reflect x = Q.reflect y + Q.reflectionLinear (x - y) := by
    rw [← reflect_add, add_sub_cancel]
  have h' : Q.reflect x - Q.reflect y = Q.reflectionLinear (x - y) := by
    rw [h, add_sub_cancel_left]
  rw [h', euclidNorm, euclidNorm, euclidDot_reflectionLinear]
theorem reflectFixesAndSwaps (Q : NormalHyperplane) : ReflectFixesAndSwaps Q := by
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · have hx' : euclidDot Q.normal x = Q.level := hx
    rw [reflect_apply, hx']
    simp
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : Q.level ≤ euclidDot Q.normal x := hx
      change euclidDot Q.normal (Q.reflect x) ≤ Q.level
      rw [euclidDot_normal_reflect]
      linarith
    · intro hy
      have hy' : euclidDot Q.normal y ≤ Q.level := hy
      refine ⟨Q.reflect y, ?_, reflect_reflect Q y⟩
      change Q.level ≤ euclidDot Q.normal (Q.reflect y)
      rw [euclidDot_normal_reflect]
      linarith
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : euclidDot Q.normal x ≤ Q.level := hx
      change Q.level ≤ euclidDot Q.normal (Q.reflect x)
      rw [euclidDot_normal_reflect]
      linarith
    · intro hy
      have hy' : Q.level ≤ euclidDot Q.normal y := hy
      refine ⟨Q.reflect y, ?_, reflect_reflect Q y⟩
      change euclidDot Q.normal (Q.reflect y) ≤ Q.level
      rw [euclidDot_normal_reflect]
      linarith
theorem linearNegatesNormal (Q : NormalHyperplane) : LinearNegatesNormal Q := by
  have hN := euclidDot_normal_self_ne_zero Q
  refine ⟨?_, fun w hw => ?_⟩
  · rw [reflectionLinear_apply]
    have : 2 * (euclidDot Q.normal Q.normal)⁻¹ * euclidDot Q.normal Q.normal = 2 := by
      field_simp
    rw [this, two_smul]
    abel
  · rw [reflectionLinear_apply, hw]
    simp
theorem actsOnOneAxis {Q : NormalHyperplane} {μ : Direction} (h : Q.normal = basisVector μ) :
    ActsOnOneAxis Q μ := by
  intro x
  refine ⟨?_, fun ν hν => ?_⟩
  · rw [reflect_apply_coord, h, euclidDot_basisVector_self, euclidDot_basisVector_left,
      basisVector_self]
    ring
  · rw [reflect_apply_coord, h, basisVector_of_ne hν]
    ring
theorem actsOnSumAxes {Q : NormalHyperplane} {μ lam : Direction} (hne : μ ≠ lam)
    (h : Q.normal = basisVector μ + basisVector lam) : ActsOnSumAxes Q μ lam := by
  intro x
  have hd : euclidDot (basisVector μ + basisVector lam) x = x μ + x lam := by
    rw [euclidDot_add_left, euclidDot_basisVector_left, euclidDot_basisVector_left]
  refine ⟨?_, ?_, fun ν h1 h2 => ?_⟩
  · rw [reflect_apply_coord, h, euclidDot_self_basis_add hne, hd]
    simp only [Pi.add_apply, basisVector_self, basisVector_of_ne hne]
    ring
  · rw [reflect_apply_coord, h, euclidDot_self_basis_add hne, hd]
    simp only [Pi.add_apply, basisVector_self, basisVector_of_ne hne.symm]
    ring
  · rw [reflect_apply_coord, h]
    simp only [Pi.add_apply, basisVector_of_ne h1, basisVector_of_ne h2]
    ring
theorem actsOnDiffAxes {Q : NormalHyperplane} {μ lam : Direction} (hne : μ ≠ lam)
    (h : Q.normal = basisVector μ - basisVector lam) : ActsOnDiffAxes Q μ lam := by
  intro x
  have hd : euclidDot (basisVector μ - basisVector lam) x = x μ - x lam := by
    rw [euclidDot_sub_left, euclidDot_basisVector_left, euclidDot_basisVector_left]
  refine ⟨?_, ?_, fun ν h1 h2 => ?_⟩
  · rw [reflect_apply_coord, h, euclidDot_self_basis_sub hne, hd]
    simp only [Pi.sub_apply, basisVector_self, basisVector_of_ne hne]
    ring
  · rw [reflect_apply_coord, h, euclidDot_self_basis_sub hne, hd]
    simp only [Pi.sub_apply, basisVector_self, basisVector_of_ne hne.symm]
    ring
  · rw [reflect_apply_coord, h]
    simp only [Pi.sub_apply, basisVector_of_ne h1, basisVector_of_ne h2]
    ring
theorem axisAction (Q : NormalHyperplane) : AxisAction Q :=
  fun _ _ hne => ⟨actsOnOneAxis, actsOnSumAxes hne, actsOnDiffAxes hne⟩
theorem preservesLatticeIff (a : Spacing) (Q : NormalHyperplane) :
    PreservesLatticeIff a Q := by
  constructor
  · intro h
    have h0 : Q.reflect 0 ∈ (latticeSubgroup (a : ℝ) : Set Point) := by
      rw [← h]
      exact ⟨0, (latticeSubgroup (a : ℝ)).zero_mem, rfl⟩
    obtain ⟨p, hp⟩ := h0
    refine ⟨?_, ?_⟩
    · rintro ⟨μ, hμ⟩
      refine ⟨p μ, ?_⟩
      have h1 := (actsOnOneAxis hμ 0).1
      have h2 := hp μ
      rw [h1] at h2
      simp only [Pi.zero_apply, sub_zero] at h2
      linarith
    · rintro ⟨μ, lam, hne, hμ | hμ⟩
      · refine ⟨p μ, ?_⟩
        have h1 := (actsOnSumAxes hne hμ 0).1
        have h2 := hp μ
        rw [h1] at h2
        simpa using h2
      · refine ⟨p μ, ?_⟩
        have h1 := (actsOnDiffAxes hne hμ 0).1
        have h2 := hp μ
        rw [h1] at h2
        simpa using h2
  · intro hQ
    exact (NormalHyperplane.reflectSymmetry hQ).image_eq
theorem isIsometricInvolution (a : Spacing) (Q : NormalHyperplane) :
    IsIsometricInvolution a Q :=
  ⟨euclidNorm_reflect_sub Q, funext (reflect_reflect Q), reflect_add Q, fun _ => rfl⟩
theorem linearEigenvectors (Q : NormalHyperplane) : LinearEigenvectors Q := by
  have hN := euclidDot_normal_self_ne_zero Q
  have hn : Q.normal ≠ 0 := by
    intro h0
    apply hN
    rw [h0]
    simp [euclidDot]
  intro v
  rw [euclidNorm_sq]
  have hs : (2 * (euclidDot Q.normal Q.normal)⁻¹ * euclidDot Q.normal v) =
      2 * ((euclidDot Q.normal Q.normal)⁻¹ * euclidDot Q.normal v) := by ring
  constructor
  · rw [reflectionLinear_apply, hs]
    set t := (euclidDot Q.normal Q.normal)⁻¹ * euclidDot Q.normal v with ht
    constructor
    · intro h
      funext κ
      have h1 := congrFun h κ
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at h1 ⊢
      linarith
    · intro h
      funext κ
      have h1 := congrFun h κ
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at h1 ⊢
      linarith
  · rw [reflectionLinear_apply]
    constructor
    · intro h
      have h1 : (2 * (euclidDot Q.normal Q.normal)⁻¹ * euclidDot Q.normal v) • Q.normal = 0 := by
        have := sub_eq_self.mp h
        exact this
      rcases smul_eq_zero.mp h1 with h2 | h2
      · have h3 : (euclidDot Q.normal Q.normal)⁻¹ ≠ 0 := inv_ne_zero hN
        rcases mul_eq_zero.mp h2 with h4 | h4
        · exact absurd h4 (mul_ne_zero two_ne_zero h3)
        · exact h4
      · exact absurd h2 hn
    · intro h
      rw [h]
      simp
theorem normal_level_proportional {Q Q' : NormalHyperplane} (h : Q'.carrier = Q.carrier) :
    ∃ t : ℝ, Q'.normal = t • Q.normal ∧ Q'.level = t * Q.level := by
  have hN := euclidDot_normal_self_ne_zero Q
  have hx0 : euclidDot Q.normal ((Q.level / euclidDot Q.normal Q.normal) • Q.normal) = Q.level := by
    rw [euclidDot_smul_right]
    field_simp
  have mem : ∀ x, euclidDot Q.normal x = Q.level → euclidDot Q'.normal x = Q'.level := by
    intro x hx
    exact show x ∈ Q'.carrier from by
      rw [h]
      exact hx
  have orth : ∀ w, euclidDot Q.normal w = 0 → euclidDot Q'.normal w = 0 := by
    intro w hw
    have h1 := mem (((Q.level / euclidDot Q.normal Q.normal) • Q.normal) + w)
      (by rw [euclidDot_add_right, hx0, hw, add_zero])
    have h2 := mem _ hx0
    rw [euclidDot_add_right, h2] at h1
    linarith
  refine ⟨euclidDot Q'.normal Q.normal / euclidDot Q.normal Q.normal, ?_, ?_⟩
  · funext κ
    have hw : euclidDot Q.normal
        (euclidDot Q.normal Q.normal • basisVector κ - Q.normal κ • Q.normal) = 0 := by
      rw [euclidDot_sub_right, euclidDot_smul_right, euclidDot_smul_right,
        euclidDot_comm Q.normal (basisVector κ), euclidDot_basisVector_left]
      ring
    have h1 := orth _ hw
    rw [euclidDot_sub_right, euclidDot_smul_right, euclidDot_smul_right,
      euclidDot_comm Q'.normal (basisVector κ), euclidDot_basisVector_left] at h1
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith
  · have h2 := mem _ hx0
    rw [euclidDot_smul_right] at h2
    rw [← h2]
    field_simp
theorem eq_or_eq_neg_of_carrier_eq {Q Q' : NormalHyperplane} (h : Q'.carrier = Q.carrier) :
    (Q'.normal = Q.normal ∧ Q'.level = Q.level) ∨
      (Q'.normal = -Q.normal ∧ Q'.level = -Q.level) := by
  obtain ⟨t, hn, hc⟩ := normal_level_proportional h
  obtain ⟨κ, hκ⟩ := exists_normal_apply_eq_one Q
  have ht : Q'.normal κ = t := by
    rw [hn]
    simp [hκ]
  rcases normal_apply_trichotomy Q' κ with h0 | h1 | h2
  · exfalso
    have ht0 : t = 0 := by rw [← ht, h0]
    obtain ⟨κ', hκ'⟩ := exists_normal_apply_eq_one Q'
    rw [hn, ht0] at hκ'
    simp at hκ'
  · have ht1 : t = 1 := by rw [← ht, h1]
    left
    rw [hn, hc, ht1]
    simp
  · have ht1 : t = -1 := by rw [← ht, h2]
    right
    rw [hn, hc, ht1]
    simp
theorem diff_of_normal_eq_neg {Q Q' : NormalHyperplane} (h : Q'.normal = -Q.normal) :
    ∃ μ lam : Direction, μ ≠ lam ∧ Q.normal = basisVector μ - basisVector lam ∧
      Q'.normal = basisVector lam - basisVector μ := by
  obtain ⟨κ, hκ⟩ := exists_normal_apply_eq_one Q'
  rw [h] at hκ
  rcases normal_trichotomy Q with ⟨μ, h1⟩ | ⟨μ, lam, hne, h1⟩ | ⟨μ, lam, hne, h1⟩
  · exfalso
    rw [h1] at hκ
    have h2 := basisVector_nonneg μ κ
    simp only [Pi.neg_apply] at hκ
    linarith
  · exfalso
    rw [h1] at hκ
    have h2 := basisVector_nonneg μ κ
    have h3 := basisVector_nonneg lam κ
    simp only [Pi.neg_apply, Pi.add_apply] at hκ
    linarith
  · exact ⟨μ, lam, hne, h1, by rw [h, h1, neg_sub]⟩
theorem carrier_eq_of_neg {Q Q' : NormalHyperplane} (hn : Q'.normal = -Q.normal)
    (hc : Q'.level = -Q.level) : Q'.carrier = Q.carrier := by
  ext x
  change euclidDot Q'.normal x = Q'.level ↔ euclidDot Q.normal x = Q.level
  rw [hn, hc, euclidDot_neg_left, neg_inj]
theorem euclidDot_neg_neg (n : Point) : euclidDot (-n) (-n) = euclidDot n n := by
  rw [euclidDot_neg_left, euclidDot_neg_right, neg_neg]
theorem reflect_eq_of_neg {Q Q' : NormalHyperplane} (hn : Q'.normal = -Q.normal)
    (hc : Q'.level = -Q.level) : Q'.reflect = Q.reflect := by
  funext x
  rw [reflect_apply, reflect_apply, hn, hc, euclidDot_neg_neg, euclidDot_neg_left]
  have h : 2 * (-euclidDot Q.normal x - -Q.level) / euclidDot Q.normal Q.normal =
      -(2 * (euclidDot Q.normal x - Q.level) / euclidDot Q.normal Q.normal) := by
    ring
  rw [h, neg_smul_neg]
theorem reflectionLinear_eq_of_neg {Q Q' : NormalHyperplane} (hn : Q'.normal = -Q.normal) :
    Q'.reflectionLinear = Q.reflectionLinear := by
  refine LinearMap.ext fun w => ?_
  rw [reflectionLinear_apply, reflectionLinear_apply, hn, euclidDot_neg_neg, euclidDot_neg_left]
  have h : 2 * (euclidDot Q.normal Q.normal)⁻¹ * -euclidDot Q.normal w =
      -(2 * (euclidDot Q.normal Q.normal)⁻¹ * euclidDot Q.normal w) := by
    ring
  rw [h, neg_smul_neg]
theorem samePlaneTwoNormals (a : Spacing) (Q Q' : NormalHyperplane) :
    SamePlaneTwoNormals a Q Q' := by
  intro hne
  have key : Q'.carrier = Q.carrier → Q'.normal = -Q.normal ∧ Q'.level = -Q.level := by
    intro h
    rcases eq_or_eq_neg_of_carrier_eq h with ⟨h1, h2⟩ | h1
    · exact absurd (by rw [h1, h2]) hne
    · exact h1
  refine ⟨⟨fun h => ?_, ?_⟩, fun h => ?_⟩
  · obtain ⟨hn, hc⟩ := key h
    obtain ⟨μ, lam, hml, h1, h2⟩ := diff_of_normal_eq_neg hn
    exact ⟨μ, lam, hml, h1, h2, hc⟩
  · rintro ⟨μ, lam, _, h1, h2, hc⟩
    exact carrier_eq_of_neg (by rw [h1, h2, neg_sub]) hc
  · obtain ⟨hn, hc⟩ := key h
    obtain ⟨μ, lam, hml, h1, h2⟩ := diff_of_normal_eq_neg hn
    have d1 : IsFaceDiagonalNormal Q.normal := ⟨μ, lam, hml, Or.inr h1⟩
    have d2 : IsFaceDiagonalNormal Q'.normal := ⟨lam, μ, hml.symm, Or.inr h2⟩
    refine ⟨reflect_eq_of_neg hn hc, reflectionLinear_eq_of_neg hn, ?_, ?_, ?_⟩
    · rw [isLatticeMirror_iff_of_faceDiagonal d1, isLatticeMirror_iff_of_faceDiagonal d2, hc]
      constructor
      · rintro ⟨q, hq⟩
        exact ⟨-q, by push_cast; linarith⟩
      · rintro ⟨q, hq⟩
        exact ⟨-q, by push_cast; linarith⟩
    · ext x
      change Q'.level ≤ euclidDot Q'.normal x ↔ euclidDot Q.normal x ≤ Q.level
      rw [hn, hc, euclidDot_neg_left, neg_le_neg_iff]
    · ext x
      change Q.level ≤ euclidDot Q.normal x ↔ euclidDot Q'.normal x ≤ Q'.level
      rw [hn, hc, euclidDot_neg_left, neg_le_neg_iff]
theorem intCast_single_eq_basisVector (μ κ : Fin 4) :
    (((Pi.single μ (1 : ℤ) : Fin 4 → ℤ) κ : ℤ) : ℝ) = basisVector μ κ := by
  by_cases h : κ = μ
  · subst h
    simp [basisVector]
  · simp [basisVector, h]
theorem realNormal_axial (μ : Direction) :
    (ReflectionClass.axial μ).realNormal = basisVector μ := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.realNormal_axial <;> assumption
theorem realNormal_diagonal_apply (μ ν : Direction) (lt : μ < ν) (s : ℤˣ) (κ : Direction) :
    (ReflectionClass.diagonal μ ν lt s).realNormal κ =
      basisVector μ κ + ((s : ℤ) : ℝ) * basisVector ν κ := by
  change (((Pi.single μ (1 : ℤ) + (s : ℤ) • Pi.single ν (1 : ℤ) : Fin 4 → ℤ) κ : ℤ) : ℝ) = _
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul,
    intCast_single_eq_basisVector, intCast_single_eq_basisVector]
theorem realNormal_diagonal_one (μ ν : Direction) (lt : μ < ν) :
    (ReflectionClass.diagonal μ ν lt 1).realNormal = basisVector μ + basisVector ν := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.realNormal_diagonal_one <;> assumption
theorem realNormal_diagonal_neg_one (μ ν : Direction) (lt : μ < ν) :
    (ReflectionClass.diagonal μ ν lt (-1)).realNormal = basisVector μ - basisVector ν := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.realNormal_diagonal_neg_one <;> assumption
theorem realNormal_diagonal_first (μ ν : Direction) (lt : μ < ν) (s : ℤˣ) :
    (ReflectionClass.diagonal μ ν lt s).realNormal μ = 1 := by
  rw [realNormal_diagonal_apply, basisVector_self, basisVector_of_ne lt.ne]
  simp
theorem realNormal_diagonal_second (μ ν : Direction) (lt : μ < ν) (s : ℤˣ) :
    (ReflectionClass.diagonal μ ν lt s).realNormal ν = ((s : ℤ) : ℝ) := by
  rw [realNormal_diagonal_apply, basisVector_self, basisVector_of_ne lt.ne']
  simp
theorem realNormal_diagonal_of_ne {μ ν κ : Direction} (lt : μ < ν) (s : ℤˣ) (h1 : κ ≠ μ)
    (h2 : κ ≠ ν) : (ReflectionClass.diagonal μ ν lt s).realNormal κ = 0 := by
  rw [realNormal_diagonal_apply, basisVector_of_ne h1, basisVector_of_ne h2]
  simp
theorem unitCast_ne_zero (s : ℤˣ) : ((s : ℤ) : ℝ) ≠ 0 := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> norm_num
theorem eq_of_realNormal_eq_smul {F F' : ReflectionClass} {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (h : ∀ κ, F.realNormal κ = ε * F'.realNormal κ) : F = F' := by
  have hε0 : ε ≠ 0 := by
    rcases hε with rfl | rfl <;> norm_num
  cases F with
  | axial μ =>
    cases F' with
    | axial ν =>
      by_cases hμ : μ = ν
      · rw [hμ]
      · exfalso
        have h1 := h μ
        rw [realNormal_axial, realNormal_axial, basisVector_self, basisVector_of_ne hμ] at h1
        norm_num at h1
    | diagonal μ' ν' lt s =>
      exfalso
      by_cases hm : μ' = μ
      · subst hm
        have h1 := h ν'
        rw [realNormal_axial, basisVector_of_ne lt.ne', realNormal_diagonal_second] at h1
        exact mul_ne_zero hε0 (unitCast_ne_zero s) h1.symm
      · have h1 := h μ'
        rw [realNormal_axial, basisVector_of_ne hm, realNormal_diagonal_first] at h1
        exact hε0 (by simpa using h1.symm)
  | diagonal μ ν lt s =>
    cases F' with
    | axial ν' =>
      exfalso
      by_cases hm : μ = ν'
      · subst hm
        have h1 := h ν
        rw [realNormal_axial, basisVector_of_ne lt.ne', realNormal_diagonal_second] at h1
        exact unitCast_ne_zero s (by simp at h1)
      · have h1 := h μ
        rw [realNormal_axial, basisVector_of_ne hm, realNormal_diagonal_first] at h1
        norm_num at h1
    | diagonal μ' ν' lt' s' =>
      have hμ : μ = μ' := by
        rcases lt_trichotomy μ μ' with h1 | h1 | h1
        · exfalso
          have h2 := h μ
          rw [realNormal_diagonal_first,
            realNormal_diagonal_of_ne lt' s' h1.ne (h1.trans lt').ne] at h2
          norm_num at h2
        · exact h1
        · exfalso
          have h2 := h μ'
          rw [realNormal_diagonal_first,
            realNormal_diagonal_of_ne lt s h1.ne (h1.trans lt).ne] at h2
          exact hε0 (by simpa using h2.symm)
      subst hμ
      have hε1 : ε = 1 := by
        have h2 := h μ
        rw [realNormal_diagonal_first, realNormal_diagonal_first] at h2
        linarith
      subst hε1
      have hν : ν = ν' := by
        by_contra hne
        have h2 := h ν
        rw [realNormal_diagonal_second, realNormal_diagonal_of_ne lt' s' lt.ne' hne] at h2
        exact unitCast_ne_zero s (by simp at h2)
      subst hν
      have h2 := h ν
      rw [realNormal_diagonal_second, realNormal_diagonal_second, one_mul] at h2
      have h3 : s = s' := Units.ext (by exact_mod_cast h2)
      rw [h3]
def reflectionClassEquiv :
    ReflectionClass ≃ Fin 4 ⊕ ({p : Fin 4 × Fin 4 // p.1 < p.2} × ℤˣ) where
  toFun
    | .axial μ => Sum.inl μ
    | .diagonal μ ν lt s => Sum.inr (⟨(μ, ν), lt⟩, s)
  invFun
    | Sum.inl μ => .axial μ
    | Sum.inr (⟨(μ, ν), lt⟩, s) => .diagonal μ ν lt s
  left_inv := by
    rintro (_ | _) <;> rfl
  right_inv := by
    rintro (_ | ⟨⟨⟨_, _⟩, _⟩, _⟩) <;> rfl
theorem card_reflectionClass : Nat.card ReflectionClass = 16 := by
  have h6 : Fintype.card {p : Fin 4 × Fin 4 // p.1 < p.2} = 6 := by decide
  rw [Nat.card_congr reflectionClassEquiv, Nat.card_sum, Nat.card_prod, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h6, Fintype.card_units_int,
    Fintype.card_fin]
theorem exists_latticeMirror {a : ℝ} {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror a) :
    ∃ P : LatticeMirror a, P.plane = Q.carrier := by
  rcases normal_trichotomy Q with ⟨μ, h⟩ | ⟨μ, lam, hne, h⟩ | ⟨μ, lam, hne, h⟩
  · refine ⟨⟨.axial μ, Q.level, hQ.1 ⟨μ, h⟩⟩, ?_⟩
    ext x
    change (ReflectionClass.axial μ).realNormal ⬝ᵥ x = Q.level ↔ euclidDot Q.normal x = Q.level
    rw [realNormal_axial, h]
    exact Iff.rfl
  · have hc := hQ.2 ⟨μ, lam, hne, Or.inl h⟩
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · refine ⟨⟨.diagonal μ lam hlt 1, Q.level, hc⟩, ?_⟩
      ext x
      change (ReflectionClass.diagonal μ lam hlt 1).realNormal ⬝ᵥ x = Q.level ↔
        euclidDot Q.normal x = Q.level
      rw [realNormal_diagonal_one, h]
      exact Iff.rfl
    · refine ⟨⟨.diagonal lam μ hlt 1, Q.level, hc⟩, ?_⟩
      ext x
      change (ReflectionClass.diagonal lam μ hlt 1).realNormal ⬝ᵥ x = Q.level ↔
        euclidDot Q.normal x = Q.level
      rw [realNormal_diagonal_one, h, add_comm (basisVector lam)]
      exact Iff.rfl
  · have hc := hQ.2 ⟨μ, lam, hne, Or.inr h⟩
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · refine ⟨⟨.diagonal μ lam hlt (-1), Q.level, hc⟩, ?_⟩
      ext x
      change (ReflectionClass.diagonal μ lam hlt (-1)).realNormal ⬝ᵥ x = Q.level ↔
        euclidDot Q.normal x = Q.level
      rw [realNormal_diagonal_neg_one, h]
      exact Iff.rfl
    · obtain ⟨q, hq⟩ := hc
      refine ⟨⟨.diagonal lam μ hlt (-1), -Q.level, ⟨-q, by rw [hq]; push_cast; ring⟩⟩, ?_⟩
      ext x
      change (ReflectionClass.diagonal lam μ hlt (-1)).realNormal ⬝ᵥ x = -Q.level ↔
        euclidDot Q.normal x = Q.level
      rw [realNormal_diagonal_neg_one, h]
      change euclidDot (basisVector lam - basisVector μ) x = -Q.level ↔
        euclidDot (basisVector μ - basisVector lam) x = Q.level
      rw [euclidDot_sub_left, euclidDot_sub_left]
      constructor <;> intro h' <;> linarith
theorem exists_normalHyperplane {a : ℝ} (P : LatticeMirror a) :
    ∃ Q : NormalHyperplane, Q.IsLatticeMirror a ∧ Q.carrier = P.plane ∧
      Q.normal = P.cls.realNormal := by
  obtain ⟨F, c, hc⟩ := P
  cases F with
  | axial μ =>
    refine ⟨NormalHyperplane.axial μ c, ?_, ?_, (realNormal_axial μ).symm⟩
    · exact (isLatticeMirror_iff_of_axial (Q := NormalHyperplane.axial μ c)
        ⟨μ, rfl⟩).2 hc
    · ext x
      change euclidDot (basisVector μ) x = c ↔ (ReflectionClass.axial μ).realNormal ⬝ᵥ x = c
      rw [realNormal_axial]
      exact Iff.rfl
  | diagonal μ ν lt s =>
    rcases Int.units_eq_one_or s with rfl | rfl
    · refine ⟨sumPlane μ ν lt.ne c, ?_, ?_, (realNormal_diagonal_one μ ν lt).symm⟩
      · exact (isLatticeMirror_iff_of_faceDiagonal (Q := sumPlane μ ν lt.ne c)
          ⟨μ, ν, lt.ne, Or.inl rfl⟩).2 hc
      · ext x
        change euclidDot (basisVector μ + basisVector ν) x = c ↔
          (ReflectionClass.diagonal μ ν lt 1).realNormal ⬝ᵥ x = c
        rw [realNormal_diagonal_one]
        exact Iff.rfl
    · refine ⟨diffPlane μ ν lt.ne c, ?_, ?_, (realNormal_diagonal_neg_one μ ν lt).symm⟩
      · exact (isLatticeMirror_iff_of_faceDiagonal (Q := diffPlane μ ν lt.ne c)
          ⟨μ, ν, lt.ne, Or.inr rfl⟩).2 hc
      · ext x
        change euclidDot (basisVector μ - basisVector ν) x = c ↔
          (ReflectionClass.diagonal μ ν lt (-1)).realNormal ⬝ᵥ x = c
        rw [realNormal_diagonal_neg_one]
        exact Iff.rfl
theorem mirrorsClassified (a : Spacing) : MirrorsClassified a := by
  refine ⟨card_reflectionClass, ?_, ?_⟩
  · ext S
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      obtain ⟨P, hP⟩ := exists_latticeMirror hQ
      exact ⟨P.cls, P, rfl, hP⟩
    · rintro ⟨F, P, -, rfl⟩
      obtain ⟨Q, hQ, hp, -⟩ := exists_normalHyperplane P
      exact ⟨Q, hQ, hp⟩
  · intro Q hQ
    obtain ⟨P, hP⟩ := exists_latticeMirror hQ
    refine ⟨P.cls, ⟨P, rfl, hP⟩, ?_⟩
    rintro F ⟨P', hF, hP'⟩
    have hF' : P'.cls = F := hF
    obtain ⟨Q₁, -, hp₁, hn₁⟩ := exists_normalHyperplane P
    obtain ⟨Q₂, -, hp₂, hn₂⟩ := exists_normalHyperplane P'
    have hpts : Q₂.carrier = Q₁.carrier := by
      rw [hp₁, hp₂, hP, hP']
    rw [← hF']
    rcases eq_or_eq_neg_of_carrier_eq hpts with ⟨h1, -⟩ | ⟨h1, -⟩
    · refine eq_of_realNormal_eq_smul (ε := 1) (Or.inl rfl) fun κ => ?_
      rw [← hn₁, ← hn₂, h1, one_mul]
    · refine eq_of_realNormal_eq_smul (ε := -1) (Or.inr rfl) fun κ => ?_
      rw [← hn₁, ← hn₂, h1]
      simp
theorem diagonalPlanesAreMirrors (a : Spacing) : DiagonalPlanesAreMirrors a := by
  intro μ lam h
  refine ⟨⟨fun _ => ⟨0, ?_⟩, fun _ => ⟨0, ?_⟩⟩, ⟨fun _ => ⟨0, ?_⟩, fun _ => ⟨0, ?_⟩⟩⟩ <;>
    simp [sumPlane, diffPlane]
theorem diagonalPlaneUnitNormal : DiagonalPlaneUnitNormal := by
  intro j c
  have hne : timeAxis ≠ j.toDirection := by
    have hj : j.toDirection ∈ Set.range SpatialDirection.toDirection := ⟨j, rfl⟩
    rw [range_toDirection] at hj
    exact fun h => hj (Set.mem_singleton_iff.mpr h.symm)
  have hnorm : euclidNorm (basisVector timeAxis + basisVector j.toDirection) = Real.sqrt 2 := by
    rw [euclidNorm, euclidDot_self_basis_add hne, Real.sqrt_eq_rpow]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  ext x
  simp only [Set.mem_ofPred_eq, normalize, euclidDot_smul_left, euclidDot_add_left,
    euclidDot_basisVector_left, hnorm]
  rw [inv_mul_eq_div, div_left_inj' hs]
theorem mirrorReflections : MirrorReflectionsStatement := fun a =>
  ⟨fun Q => ⟨reflectFixesAndSwaps Q, linearNegatesNormal Q, axisAction Q,
      preservesLatticeIff a Q⟩,
    mirrorsClassified a, diagonalPlanesAreMirrors a, diagonalPlaneUnitNormal,
    fun Q => ⟨isIsometricInvolution a Q, linearEigenvectors Q⟩, samePlaneTwoNormals a⟩
end YangMills.Construction.LatticeConventions.MirrorReflections
end

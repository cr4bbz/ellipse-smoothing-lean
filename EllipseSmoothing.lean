import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ellipse smoothing

An axiom-free algebraic core for lifting a scalar control law to an ellipse.

The main distinction is between:

* the geometric trace, which is always the same ellipse; and
* the control law, which determines how the ellipse is traversed.

The triangular control law is proved admissible on the fundamental interval.
The smoothed odd-harmonic series is defined exactly.  Summability, positivity
of its normalizing denominator, and the global unit bound are proved on the
closed smoothing interval.  Endpoint identification and regularity remain
explicit future obligations rather than postulated axioms.
-/

namespace EllipseSmoothing

open scoped BigOperators

noncomputable section

/-- Centre and semiaxes of an axis-aligned ellipse. -/
structure Ellipse where
  cx : ℝ
  cy : ℝ
  a : ℝ
  b : ℝ

/-- Division-free ellipse equation.  For nonzero semiaxes this is equivalent
to the usual normalized equation. -/
def OnEllipse (E : Ellipse) (p : ℝ × ℝ) : Prop :=
  E.b ^ 2 * (p.1 - E.cx) ^ 2 + E.a ^ 2 * (p.2 - E.cy) ^ 2 =
    E.a ^ 2 * E.b ^ 2

/-- Lift a horizontal control value `g ∈ [-1,1]` to one of the two ellipse
branches.  The branch parameter is intended to be `+1` or `-1`. -/
def ellipseLift (E : Ellipse) (g branch : ℝ) : ℝ × ℝ :=
  (E.cx + E.a * g,
   E.cy + E.b * branch * Real.sqrt (1 - g ^ 2))

/-- The geometric invariant: every admissible scalar control value lifts to
the same ellipse, independently of how that control value was generated. -/
theorem ellipseLift_onEllipse
    (E : Ellipse) {g branch : ℝ}
    (hg : g ^ 2 ≤ 1) (hbranch : branch ^ 2 = 1) :
    OnEllipse E (ellipseLift E g branch) := by
  have hnonneg : 0 ≤ 1 - g ^ 2 := by linarith
  have hsqrt : (Real.sqrt (1 - g ^ 2)) ^ 2 = 1 - g ^ 2 := by
    simpa using Real.sq_sqrt hnonneg
  unfold OnEllipse ellipseLift
  dsimp only
  calc
    E.b ^ 2 * (E.cx + E.a * g - E.cx) ^ 2 +
          E.a ^ 2 * (E.cy + E.b * branch * Real.sqrt (1 - g ^ 2) - E.cy) ^ 2 =
        E.a ^ 2 * E.b ^ 2 *
          (g ^ 2 + branch ^ 2 * (Real.sqrt (1 - g ^ 2)) ^ 2) := by ring
    _ = E.a ^ 2 * E.b ^ 2 := by rw [hbranch, hsqrt]; ring

/-- A control law contains precisely the boundedness required by the lift. -/
structure ControlLaw (G : ℝ → ℝ) : Prop where
  sq_le_one : ∀ θ, G θ ^ 2 ≤ 1

/-- Alternating upper/lower branch. At a zero of `sin θ` the square-root term
vanishes for endpoint-preserving controls, so the branch choice is immaterial. -/
def branchSign (θ : ℝ) : ℝ :=
  if 0 ≤ Real.sin θ then 1 else -1

@[simp]
theorem branchSign_sq (θ : ℝ) : branchSign θ ^ 2 = 1 := by
  unfold branchSign
  split <;> norm_num

/-- Parametric path induced by a control function. -/
def controlledPath (E : Ellipse) (G : ℝ → ℝ) (θ : ℝ) : ℝ × ℝ :=
  ellipseLift E (G θ) (branchSign θ)

/-- Any admissible control law traces the ellipse exactly. -/
theorem controlledPath_onEllipse
    (E : Ellipse) (G : ℝ → ℝ) (hG : ControlLaw G) (θ : ℝ) :
    OnEllipse E (controlledPath E G θ) := by
  exact ellipseLift_onEllipse E (hG.sq_le_one θ) (branchSign_sq θ)

/-! ## The atomic triangular control -/

/-- Fundamental falling branch, with normalized time `u ∈ [0,1]`. -/
def triangleControl (u : ℝ) : ℝ :=
  1 - 2 * u

@[simp] theorem triangleControl_zero : triangleControl 0 = 1 := by
  simp [triangleControl]

@[simp] theorem triangleControl_one : triangleControl 1 = -1 := by
  norm_num [triangleControl]

/-- The falling linear branch never leaves the admissible interval. -/
theorem triangleControl_sq_le_one {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    triangleControl u ^ 2 ≤ 1 := by
  have hproduct : 0 ≤ u * (1 - u) :=
    mul_nonneg h0 (sub_nonneg.mpr h1)
  unfold triangleControl
  nlinarith

/-- Both halves of the atomic traversal lie on the same ellipse. -/
theorem triangleLift_onEllipse
    (E : Ellipse) {u branch : ℝ}
    (h0 : 0 ≤ u) (h1 : u ≤ 1) (hbranch : branch ^ 2 = 1) :
    OnEllipse E (ellipseLift E (triangleControl u) branch) := by
  exact ellipseLift_onEllipse E (triangleControl_sq_le_one h0 h1) hbranch

/-! ## Smoothed odd-harmonic control -/

/-- The `(2k+1)`-st odd harmonic. -/
def oddHarmonic (k : ℕ) : ℕ :=
  2 * k + 1

/-- Weight used by the normalized smoothing formula.  At `λ = 0` all odd
harmonics retain their triangular-wave weights.  At `λ = 1` only the first
harmonic survives. -/
def smoothingWeight (lam : ℝ) (k : ℕ) : ℝ :=
  (1 - lam) ^ (oddHarmonic k ^ 2 - 1) /
    (oddHarmonic k : ℝ) ^ 2

/-- Denominator of the normalized infinite control series. -/
def smoothDenominator (lam : ℝ) : ℝ :=
  ∑' k : ℕ, smoothingWeight lam k

/-- Numerator of the normalized infinite control series. -/
def smoothNumerator (lam θ : ℝ) : ℝ :=
  ∑' k : ℕ,
    smoothingWeight lam k * Real.cos ((oddHarmonic k : ℝ) * θ)

/-- The exact smoothing formula from the model. -/
def smoothControl (lam θ : ℝ) : ℝ :=
  smoothNumerator lam θ / smoothDenominator lam

/-! ## Gate 2: analytic admissibility of the smoothed control -/

/-- Odd harmonics form an injective subsequence of the natural numbers. -/
theorem oddHarmonic_injective : Function.Injective oddHarmonic := by
  intro k m h
  unfold oddHarmonic at h
  omega

/-- The square-reciprocal majorant along odd harmonics is summable. -/
theorem summable_oddHarmonic_inv_sq :
    Summable (fun k : ℕ => 1 / (oddHarmonic k : ℝ) ^ 2) := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  simpa [Function.comp_def] using hp.comp_injective oddHarmonic_injective

/-- In the smoothing interval every harmonic weight is nonnegative. -/
theorem smoothingWeight_nonneg
    {lam : ℝ} (_hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (k : ℕ) :
    0 ≤ smoothingWeight lam k := by
  have hbase : 0 ≤ 1 - lam := by linarith
  unfold smoothingWeight
  positivity

/-- Every smoothing weight is dominated by its triangular-wave coefficient. -/
theorem smoothingWeight_le_majorant
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (k : ℕ) :
    smoothingWeight lam k ≤ 1 / (oddHarmonic k : ℝ) ^ 2 := by
  have hbase0 : 0 ≤ 1 - lam := by linarith
  have hbase1 : 1 - lam ≤ 1 := by linarith
  have hpow : (1 - lam) ^ (oddHarmonic k ^ 2 - 1) ≤ 1 :=
    pow_le_one₀ hbase0 hbase1
  unfold smoothingWeight
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hpow (by positivity)

/-- The denominator series converges throughout the closed smoothing interval. -/
theorem summable_smoothingWeight
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    Summable (smoothingWeight lam) := by
  refine Summable.of_norm_bounded summable_oddHarmonic_inv_sq ?_
  intro k
  have hw := smoothingWeight_nonneg hlam0 hlam1 k
  simpa [Real.norm_eq_abs, abs_of_nonneg hw] using
    smoothingWeight_le_majorant hlam0 hlam1 k

@[simp]
theorem smoothingWeight_zero_index (lam : ℝ) : smoothingWeight lam 0 = 1 := by
  norm_num [smoothingWeight, oddHarmonic]

/-- The normalizing denominator is not merely nonzero but at least one. -/
theorem one_le_smoothDenominator
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    1 ≤ smoothDenominator lam := by
  have hsum := summable_smoothingWeight hlam0 hlam1
  have hterm : smoothingWeight lam 0 ≤ ∑' k : ℕ, smoothingWeight lam k :=
    hsum.le_tsum 0 (fun k _ => smoothingWeight_nonneg hlam0 hlam1 k)
  simpa [smoothDenominator] using hterm

/-- Positivity makes normalization by the denominator legitimate. -/
theorem smoothDenominator_pos
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    0 < smoothDenominator lam := by
  linarith [one_le_smoothDenominator hlam0 hlam1]

/-- Multiplying the weights by cosine preserves absolute summability. -/
theorem summable_smoothNumerator
    {lam θ : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    Summable (fun k : ℕ =>
      smoothingWeight lam k * Real.cos ((oddHarmonic k : ℝ) * θ)) := by
  have hweights := summable_smoothingWeight hlam0 hlam1
  refine Summable.of_norm_bounded hweights ?_
  intro k
  have hw := smoothingWeight_nonneg hlam0 hlam1 k
  have hcos := Real.abs_cos_le_one ((oddHarmonic k : ℝ) * θ)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
  nlinarith [mul_nonneg hw (sub_nonneg.mpr hcos)]

/-- The numerator is bounded in absolute value by the denominator. -/
theorem abs_smoothNumerator_le_denominator
    {lam θ : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    |smoothNumerator lam θ| ≤ smoothDenominator lam := by
  have hweights := summable_smoothingWeight hlam0 hlam1
  have hbound : ∀ k : ℕ,
      ‖smoothingWeight lam k * Real.cos ((oddHarmonic k : ℝ) * θ)‖ ≤
        smoothingWeight lam k := by
    intro k
    have hw := smoothingWeight_nonneg hlam0 hlam1 k
    have hcos := Real.abs_cos_le_one ((oddHarmonic k : ℝ) * θ)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    nlinarith [mul_nonneg hw (sub_nonneg.mpr hcos)]
  simpa [smoothNumerator, smoothDenominator, Real.norm_eq_abs] using
    tsum_of_norm_bounded hweights.hasSum hbound

/-- The normalized smoothed control remains in the closed unit interval. -/
theorem abs_smoothControl_le_one
    {lam θ : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    |smoothControl lam θ| ≤ 1 := by
  have hden := smoothDenominator_pos hlam0 hlam1
  have hnum := abs_smoothNumerator_le_denominator (θ := θ) hlam0 hlam1
  rw [smoothControl, abs_div, abs_of_pos hden]
  exact (div_le_one hden).2 hnum

/-- Squared form of admissibility, matching the contract of `ellipseLift`. -/
theorem smoothControl_sq_le_one
    {lam θ : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    smoothControl lam θ ^ 2 ≤ 1 := by
  have habs := abs_smoothControl_le_one (θ := θ) hlam0 hlam1
  have hprod :
      0 ≤ |smoothControl lam θ| * (1 - |smoothControl lam θ|) :=
    mul_nonneg (abs_nonneg _) (sub_nonneg.mpr habs)
  rw [← sq_abs]
  nlinarith

/-- The corresponding smoothed ellipse traversal. -/
def smoothedPath (E : Ellipse) (lam θ : ℝ) : ℝ × ℝ :=
  controlledPath E (smoothControl lam) θ

/-- Once the analytic bound is discharged, the smoothed series inherits the
ellipse invariant for free.  This theorem isolates the remaining analysis from
the already completed algebraic geometry. -/
theorem smoothedPath_onEllipse
    (E : Ellipse) (lam θ : ℝ)
    (hbound : smoothControl lam θ ^ 2 ≤ 1) :
    OnEllipse E (smoothedPath E lam θ) := by
  unfold smoothedPath controlledPath
  exact ellipseLift_onEllipse E hbound (branchSign_sq θ)

/-- Gate 2 closes the analytic precondition: every parameter in the smoothing
interval produces a point on the same ellipse. -/
theorem smoothedPath_onEllipse_of_mem_Icc
    (E : Ellipse) {lam θ : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    OnEllipse E (smoothedPath E lam θ) := by
  exact smoothedPath_onEllipse E lam θ
    (smoothControl_sq_le_one hlam0 hlam1)

/-! ## Explicit audit statements -/

#check ellipseLift_onEllipse
#check controlledPath_onEllipse
#check triangleLift_onEllipse
#check smoothedPath_onEllipse
#check summable_smoothingWeight
#check smoothDenominator_pos
#check smoothControl_sq_le_one
#check smoothedPath_onEllipse_of_mem_Icc

end

end EllipseSmoothing

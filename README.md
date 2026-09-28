# Ellipse smoothing in Lean 4

This project formalizes the structural claim behind the model:

> Changing the control law changes the traversal, not the ellipse invariant.

## What is already proved

- a division-free ellipse invariant;
- the generic square-root lift from any value `g` with `g² ≤ 1`;
- independence from the upper/lower branch;
- admissibility and endpoints of the normalized triangular branch;
- inheritance of the ellipse invariant by any bounded control law;
- the exact infinite odd-harmonic smoothing formula;
- summability and nonnegativity of its weights for `0 ≤ λ ≤ 1`;
- the lower bound `1 ≤ smoothDenominator λ` and hence positivity;
- the global estimate `|smoothControl λ θ| ≤ 1`;
- the ellipse invariant for every smoothed path with `0 ≤ λ ≤ 1`.

No project-specific axioms or `sorry` declarations are used.

## Remaining analytic obligations

Gate 2 closes summability, normalization, and global admissibility. The next
gate should identify the endpoint laws and establish regularity:

1. `smoothControl 0 θ` equals the periodic triangle wave;
2. `smoothControl 1 θ = cos θ`;
3. smoothness for `0 < λ` and the finite endpoint-speed formula.

The theorem `smoothedPath_onEllipse_of_mem_Icc` now performs the complete
transfer from the analytic bound to the already-proved geometric invariant.

## Local build

Clang is sufficient as the native compiler dependency. In PowerShell:

```powershell
lake update
lake exe cache get
lake build
```

To inspect the theorem dependencies in a temporary Lean file:

```lean
import EllipseSmoothing

#print axioms EllipseSmoothing.ellipseLift_onEllipse
#print axioms EllipseSmoothing.triangleLift_onEllipse
#print axioms EllipseSmoothing.smoothControl_sq_le_one
#print axioms EllipseSmoothing.smoothedPath_onEllipse_of_mem_Icc
```

The project targets Lean `v4.30.0` and the matching mathlib tag.

## Paper

The accompanying modular LaTeX paper is located in [`paper/`](paper/). It can
be rendered on Windows with:

```powershell
.\paper\render.ps1
```

Each export receives a filename derived from the current Git tag or commit.
GitHub Actions additionally produces a versioned PDF artifact on every push and
pull request.

/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

R1 — definitions for PSLQ-class integer-relation detection.

References:
* H. R. P. Ferguson, D. H. Bailey, S. Arno, "Analysis of PSLQ, an integer
  relation finding algorithm", Math. Comp. 68 (1999) — with J. Borwein and
  P. Lisoněk's analysis of the same period ("Analysis of PSLQ").
* J. Chen, D. Stehlé, G. Villard, "A new view on HJLS and PSLQ: sums and
  projections of lattices" (ISSAC 2013): PSLQ and HJLS are equivalent up to
  scaling; the HJLS normalization admits exact rational arithmetic, which is
  the form we formalize. Textbook PSLQ's `H` matrix has irrational (square
  root) entries even on rational input; the CSV/HJLS normalization replaces
  them by rational Gram–Schmidt data.
* "Integer relation detection for empirical data" line (error-controlled PSLQ)
  for the empirical-input theorem, the point of this tier.
-/
import Mathlib

namespace DiscoveryKernels.R1

/-- `m` is an integer relation for the vector `x`: `m ≠ 0` and `∑ mᵢ xᵢ = 0`. -/
def IsIntRelation {K : Type*} [Field K] {n : ℕ} (x : Fin n → K) (m : Fin n → ℤ) : Prop :=
  m ≠ 0 ∧ ∑ i, (m i : K) * x i = 0

end DiscoveryKernels.R1

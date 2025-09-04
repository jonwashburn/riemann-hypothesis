#!/usr/bin/env bash
set -euo pipefail
echo "==> Updating deps"
lake update
echo "==> Building"
lake build
echo "==> Scanning for holes/axioms"
if grep -RnE '\bsorry\b|\badmit\b|^\s*axiom\b' rh | grep -v 'no sorry' ; then echo 'Found holes/axioms'; exit 1; fi
echo "==> Checking theorems"
grep -R theorem RH rh/Proof/Main.lean >/dev/null
grep -R no_offcritical_zeros_from_schur rh/RS/SchurGlobalization.lean >/dev/null
grep -R ZetaNoZerosOnRe1FromSchur rh/RS/SchurGlobalization.lean >/dev/null
grep -R zeta_nonzero_re_eq_one rh/academic_framework/EulerProductMathlib.lean >/dev/null
echo "OK"

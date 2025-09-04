// Lean compiler output
// Module: rh.academic_framework.DiagonalFredholm
// Imports: Init rh.academic_framework.DiagonalFredholm.Operator rh.academic_framework.DiagonalFredholm.ProductLemmas rh.academic_framework.DiagonalFredholm.Determinant rh.academic_framework.DiagonalFredholm.Comprehensive
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_rh_academic__framework_DiagonalFredholm_Operator(uint8_t builtin, lean_object*);
lean_object* initialize_rh_academic__framework_DiagonalFredholm_ProductLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_rh_academic__framework_DiagonalFredholm_Determinant(uint8_t builtin, lean_object*);
lean_object* initialize_rh_academic__framework_DiagonalFredholm_Comprehensive(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rh_academic__framework_DiagonalFredholm(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_academic__framework_DiagonalFredholm_Operator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_academic__framework_DiagonalFredholm_ProductLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_academic__framework_DiagonalFredholm_Determinant(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_academic__framework_DiagonalFredholm_Comprehensive(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

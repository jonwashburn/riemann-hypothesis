// Lean compiler output
// Module: rh.academic_framework.GammaBounds
// Imports: Init Mathlib.Data.Complex.Basic Mathlib.Analysis.Complex.Liouville Mathlib.Analysis.SpecialFunctions.Complex.Log Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
lean_object* l_Nat_cast___at_Real_instNatCast___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_RH_AcademicFramework_GammaBounds_cauchyHPrimeBoundConstant___boxed(lean_object*);
static lean_object* l_RH_AcademicFramework_GammaBounds_cauchyHPrimeBoundConstant___closed__1;
LEAN_EXPORT lean_object* l_RH_AcademicFramework_GammaBounds_cauchyHPrimeBoundConstant(lean_object*);
static lean_object* _init_l_RH_AcademicFramework_GammaBounds_cauchyHPrimeBoundConstant___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(16u);
x_2 = l_Nat_cast___at_Real_instNatCast___spec__2(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_RH_AcademicFramework_GammaBounds_cauchyHPrimeBoundConstant(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RH_AcademicFramework_GammaBounds_cauchyHPrimeBoundConstant___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_RH_AcademicFramework_GammaBounds_cauchyHPrimeBoundConstant___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RH_AcademicFramework_GammaBounds_cauchyHPrimeBoundConstant(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Complex_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_Liouville(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Complex_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Gamma_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rh_academic__framework_GammaBounds(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Complex_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_Liouville(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Complex_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Gamma_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_RH_AcademicFramework_GammaBounds_cauchyHPrimeBoundConstant___closed__1 = _init_l_RH_AcademicFramework_GammaBounds_cauchyHPrimeBoundConstant___closed__1();
lean_mark_persistent(l_RH_AcademicFramework_GammaBounds_cauchyHPrimeBoundConstant___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

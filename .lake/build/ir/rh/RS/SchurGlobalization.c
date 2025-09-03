// Lean compiler output
// Module: rh.RS.SchurGlobalization
// Imports: Init Mathlib.Analysis.Analytic.Basic Mathlib.Analysis.Complex.AbsMax Mathlib.Analysis.Complex.CauchyIntegral Mathlib.Topology.Basic Mathlib.NumberTheory.LSeries.RiemannZeta Mathlib.Tactic Mathlib.Topology.Instances.Complex Mathlib.Topology.MetricSpace.Basic
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
LEAN_EXPORT lean_object* l_Rect__u03a9;
LEAN_EXPORT lean_object* l_RH_RS_bridge__of__localAssignment___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RH_RS_bridge__of__localAssignment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RH_RS__u03a9;
static lean_object* _init_l_RH_RS__u03a9() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_RH_RS_bridge__of__localAssignment(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_RH_RS_bridge__of__localAssignment___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RH_RS_bridge__of__localAssignment(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Rect__u03a9() {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Analytic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_AbsMax(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_CauchyIntegral(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_NumberTheory_LSeries_RiemannZeta(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Instances_Complex(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_MetricSpace_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rh_RS_SchurGlobalization(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Analytic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_AbsMax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_CauchyIntegral(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_NumberTheory_LSeries_RiemannZeta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Instances_Complex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_MetricSpace_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_RH_RS__u03a9 = _init_l_RH_RS__u03a9();
l_Rect__u03a9 = _init_l_Rect__u03a9();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

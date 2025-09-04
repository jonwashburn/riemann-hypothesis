// Lean compiler output
// Module: rh.academic_framework.Core
// Imports: Init Mathlib.Analysis.InnerProductSpace.l2Space Mathlib.Data.Nat.Prime.Basic Mathlib.Analysis.SpecialFunctions.Pow.Complex Mathlib.Analysis.SpecialFunctions.Exp Mathlib.NumberTheory.LSeries.RiemannZeta
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
LEAN_EXPORT lean_object* l_AcademicRH_instDecidableEqPrimeIndex___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_AcademicRH_PrimeIndex_equivPrimes;
LEAN_EXPORT lean_object* l_AcademicRH_PrimeIndex_equivPrimes___elambda__1(lean_object*);
static lean_object* l_AcademicRH_PrimeIndex_equivPrimes___closed__1;
LEAN_EXPORT uint8_t l___private_rh_academic__framework_Core_0__AcademicRH_decEqPrimeIndex____x40_rh_academic__framework_Core___hyg_20_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_AcademicRH_PrimeIndex_instCoeOutNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_AcademicRH_PrimeIndex_equivPrimes___elambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_AcademicRH_PrimeIndex_instCoeOutNat(lean_object*);
LEAN_EXPORT uint8_t l_AcademicRH_instDecidableEqPrimeIndex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_rh_academic__framework_Core_0__AcademicRH_decEqPrimeIndex____x40_rh_academic__framework_Core___hyg_20____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_AcademicRH_PrimeIndex_equivPrimes___elambda__2___boxed(lean_object*);
static lean_object* l_AcademicRH_PrimeIndex_equivPrimes___closed__2;
static lean_object* l_AcademicRH_PrimeIndex_equivPrimes___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_AcademicRH_PrimeIndex_equivPrimes___elambda__2(lean_object*);
LEAN_EXPORT uint8_t l___private_rh_academic__framework_Core_0__AcademicRH_decEqPrimeIndex____x40_rh_academic__framework_Core___hyg_20_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_rh_academic__framework_Core_0__AcademicRH_decEqPrimeIndex____x40_rh_academic__framework_Core___hyg_20____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_rh_academic__framework_Core_0__AcademicRH_decEqPrimeIndex____x40_rh_academic__framework_Core___hyg_20_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_AcademicRH_instDecidableEqPrimeIndex(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_AcademicRH_instDecidableEqPrimeIndex___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AcademicRH_instDecidableEqPrimeIndex(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_AcademicRH_PrimeIndex_instCoeOutNat(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_AcademicRH_PrimeIndex_instCoeOutNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_AcademicRH_PrimeIndex_instCoeOutNat(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_AcademicRH_PrimeIndex_equivPrimes___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_AcademicRH_PrimeIndex_equivPrimes___elambda__2(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_AcademicRH_PrimeIndex_equivPrimes___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_AcademicRH_PrimeIndex_equivPrimes___elambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_AcademicRH_PrimeIndex_equivPrimes___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_AcademicRH_PrimeIndex_equivPrimes___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_AcademicRH_PrimeIndex_equivPrimes___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_AcademicRH_PrimeIndex_equivPrimes___closed__1;
x_2 = l_AcademicRH_PrimeIndex_equivPrimes___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_AcademicRH_PrimeIndex_equivPrimes() {
_start:
{
lean_object* x_1; 
x_1 = l_AcademicRH_PrimeIndex_equivPrimes___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_AcademicRH_PrimeIndex_equivPrimes___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_AcademicRH_PrimeIndex_equivPrimes___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_AcademicRH_PrimeIndex_equivPrimes___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_AcademicRH_PrimeIndex_equivPrimes___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_InnerProductSpace_l2Space(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Prime_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Pow_Complex(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Exp(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_NumberTheory_LSeries_RiemannZeta(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rh_academic__framework_Core(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_InnerProductSpace_l2Space(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Prime_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Pow_Complex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Exp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_NumberTheory_LSeries_RiemannZeta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_AcademicRH_PrimeIndex_equivPrimes___closed__1 = _init_l_AcademicRH_PrimeIndex_equivPrimes___closed__1();
lean_mark_persistent(l_AcademicRH_PrimeIndex_equivPrimes___closed__1);
l_AcademicRH_PrimeIndex_equivPrimes___closed__2 = _init_l_AcademicRH_PrimeIndex_equivPrimes___closed__2();
lean_mark_persistent(l_AcademicRH_PrimeIndex_equivPrimes___closed__2);
l_AcademicRH_PrimeIndex_equivPrimes___closed__3 = _init_l_AcademicRH_PrimeIndex_equivPrimes___closed__3();
lean_mark_persistent(l_AcademicRH_PrimeIndex_equivPrimes___closed__3);
l_AcademicRH_PrimeIndex_equivPrimes = _init_l_AcademicRH_PrimeIndex_equivPrimes();
lean_mark_persistent(l_AcademicRH_PrimeIndex_equivPrimes);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

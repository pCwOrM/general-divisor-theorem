// Lean compiler output
// Module: GeneralDivisorTheorem
// Imports: Init Mathlib.Data.Nat.Basic Mathlib.Data.Nat.GCD.Basic Mathlib.Data.Nat.Factors Mathlib.Data.Rat.Lemmas Mathlib.Data.Nat.Totient Mathlib.NumberTheory.ArithmeticFunction Mathlib.Data.ZMod.Basic Mathlib.Tactic.Linarith Mathlib.Tactic.LinearCombination Mathlib.Tactic.Ring Mathlib.Tactic.FieldSimp Mathlib.Tactic.NormNum
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
lean_object* lean_nat_gcd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_d__param(lean_object*, lean_object*);
lean_object* l_Nat_cast___at_Rat_instOfNat___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_T__min___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_rad(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_R__param(lean_object*, lean_object*);
lean_object* l_Nat_totient(lean_object*);
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_rad___boxed(lean_object*);
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_R__param___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_C__factor(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
lean_object* l_Finset_prod___at_Nat_factorizationEquiv___elambda__1___spec__2(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* l_Nat_primeFactors(lean_object*);
static lean_object* l_GeneralDivisorTheorem_rad___closed__1;
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_T__min(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_d__param___boxed(lean_object*, lean_object*);
static lean_object* l_GeneralDivisorTheorem_C__factor___closed__1;
static lean_object* _init_l_GeneralDivisorTheorem_rad___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_rad(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Nat_primeFactors(x_1);
x_5 = l_GeneralDivisorTheorem_rad___closed__1;
x_6 = l_Finset_prod___at_Nat_factorizationEquiv___elambda__1___spec__2(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(0u);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_rad___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_GeneralDivisorTheorem_rad(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_d__param(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_nat_gcd(x_2, x_1);
x_4 = l_GeneralDivisorTheorem_rad(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_d__param___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_GeneralDivisorTheorem_d__param(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_R__param(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_GeneralDivisorTheorem_d__param(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_GeneralDivisorTheorem_rad(x_1);
x_7 = lean_nat_div(x_6, x_3);
lean_dec(x_3);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(0u);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_R__param___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_GeneralDivisorTheorem_R__param(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_T__min(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_GeneralDivisorTheorem_R__param(x_1, x_2);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_T__min___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_GeneralDivisorTheorem_T__min(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_GeneralDivisorTheorem_C__factor___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_cast___at_Rat_instOfNat___spec__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_GeneralDivisorTheorem_C__factor(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
x_2 = l_Nat_totient(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Nat_cast___at_Rat_instOfNat___spec__1(x_1);
x_6 = l_Nat_cast___at_Rat_instOfNat___spec__1(x_2);
x_7 = l_Rat_div(x_5, x_6);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_GeneralDivisorTheorem_C__factor___closed__1;
return x_8;
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_GCD_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Factors(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Rat_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Totient(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_NumberTheory_ArithmeticFunction(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_ZMod_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_Linarith(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_LinearCombination(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_Ring(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_FieldSimp(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_NormNum(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GeneralDivisorTheorem(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_GCD_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Factors(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Rat_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Totient(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_NumberTheory_ArithmeticFunction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_ZMod_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_Linarith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_LinearCombination(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_Ring(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_FieldSimp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_NormNum(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_GeneralDivisorTheorem_rad___closed__1 = _init_l_GeneralDivisorTheorem_rad___closed__1();
lean_mark_persistent(l_GeneralDivisorTheorem_rad___closed__1);
l_GeneralDivisorTheorem_C__factor___closed__1 = _init_l_GeneralDivisorTheorem_C__factor___closed__1();
lean_mark_persistent(l_GeneralDivisorTheorem_C__factor___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

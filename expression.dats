#define ATS_DYNLOADFLAG 0

staload "expression.sats"

#include "share/atspre_staload.hats"

// I don't know what I'm missing here:
// staload "prelude/DATS/integer.dats"
// staload "prelude/DATS/string.dats"
// staload "prelude/DATS/strptr.dats"
// staload "prelude/DATS/list_vt.dats"

implement expression_new() = list_vt_nil()

implement expression_copy(exp) =
	let
		implement list_vt_copylin$copy<Strptr1>(s) = strptr1_copy(s)
	in
		list_vt_copylin<Strptr1>(exp)
	end

implement expression_equal(ex1, ex2) =
	case+ (ex1, ex2) of
	| (list_vt_nil(), list_vt_nil()) => true
	| (list_vt_cons(e1, es1), list_vt_cons(e2, es2)) =>
		if compare_strptr_strptr(e1, e2) = 0 then
			true
		else
			expression_equal(es1, es2)
	| (_, _) => false

implement expression_print(exp) =
	case+ exp of
	| list_vt_cons(s, es) => (
		print_strptr(s);
		print(" ");
		expression_print(es)
	)
	| list_vt_nil() => ()

implement expression_free(exp)=
	let
		implement list_vt_freelin$clear<Strptr1>(s) = strptr_free(s)
	in
		list_vt_freelin<Strptr1>(exp)
	end
